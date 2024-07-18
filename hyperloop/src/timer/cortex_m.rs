//! Monotonic timer based on SysTick and cycle counter
//!
//! Based on <https://github.com/rtic-rs/dwt-systick-monotonic/blob/b8ad6d29d731a04cf974a74c9138b1a5aaa9ecdd/src/lib.rs>

use core::cell::{Cell, RefCell};

use cortex_m::{
    interrupt::Mutex,
    peripheral::{syst::SystClkSource, DCB, DWT, SYST},
};

use crate::timer::HardwareTimer;

pub type Instant<const DENOM: u32> = fugit::Instant<u64, 1, DENOM>;
pub type Duration<const DENOM: u32> = fugit::Duration<u64, 1, DENOM>;

/// Monotonic timer based on SysTick and cycle counter
pub struct SysTickTimer<const TIMER_HZ: u32> {
    ticks: Mutex<Cell<u64>>,
    systick: Mutex<RefCell<SYST>>,
}

impl<const TIMER_HZ: u32> SysTickTimer<TIMER_HZ> {
    pub fn new(dcb: &mut DCB, mut dwt: DWT, mut systick: SYST, sysclk: u32) -> Self {
        assert!(TIMER_HZ == sysclk);

        dcb.enable_trace();
        DWT::unlock();
        assert!(DWT::has_cycle_counter());

        dwt.enable_cycle_counter();
        dwt.set_cycle_count(0);

        systick.set_clock_source(SystClkSource::Core);

        Self {
            ticks: Mutex::new(Cell::new(0)),
            systick: Mutex::new(RefCell::new(systick)),
        }
    }
}

impl<const TIMER_HZ: u32> HardwareTimer for SysTickTimer<TIMER_HZ> {
    type Instant = Instant<TIMER_HZ>;
    type Duration = Duration<TIMER_HZ>;

    fn start(&self) {
        self.set_alarm(None);

        cortex_m::interrupt::free(|cs| {
            let mut systick = self.systick.borrow(cs).borrow_mut();

            systick.set_clock_source(SystClkSource::Core);

            systick.enable_counter();
            systick.enable_interrupt();
        });
    }

    fn now(&self) -> Self::Instant {
        let old = cortex_m::interrupt::free(|cs| self.ticks.borrow(cs).get());

        let mut high = (old >> 32) as u32;
        let low = old as u32;
        let now = DWT::cycle_count();

        // Detect CYCCNT overflow
        if now < low {
            high = high.wrapping_add(1);
        }

        let new = cortex_m::interrupt::free(|cs| {
            let ticks = self.ticks.borrow(cs);

            ticks.replace(((high as u64) << 32) | (now as u64));
            ticks.get()
        });

        Self::Instant::from_ticks(new)
    }

    fn set_alarm(&self, expiration: Option<Self::Instant>) {
        let max = 0xff_ffff;

        let ticks = expiration
            // Get duration between now and expiration, set to
            // zero if already expired
            .and_then(|expiration| {
                expiration
                    .checked_duration_since(self.now())
                    .or_else(|| Some(Self::Duration::from_ticks(0)))
            })
            // Try to convert duration to ticks
            .and_then(|duration| duration.ticks().try_into().ok())
            // If no expiration provided, or duration to long to fit
            // ticks in u32, set ticks to max value
            .unwrap_or(max)
            // If duration is zero, set to 1 because 0 has special
            // meaning in systick reload register
            .max(1)
            // Make sure ticks is not bigger than max
            .min(max);

        cortex_m::interrupt::free(|cs| {
            let mut systick = self.systick.borrow(cs).borrow_mut();

            systick.set_reload(ticks);
            systick.clear_current();
        });
    }

    fn wait_for_alarm(&self) {
        cortex_m::asm::wfi();
    }
}
