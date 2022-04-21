#![no_std]
#![no_main]
#![feature(type_alias_impl_trait)]

use core::{cell::Cell, pin::Pin};

use panic_probe as _;

use cortex_m::interrupt::Mutex;
use cortex_m_rt::{entry, exception};
use hyperloop::{
    static_executor, task,
    timer::cortex_m::{Duration, SysTickTimer},
    timer::TimerQueue,
};
use stm32f1xx_hal::{
    device::Peripherals,
    gpio::{ErasedPin, Output},
    prelude::*,
};

use defmt_rtt as _;

const SYSCLK_FREQ_HZ: u32 = 8_000_000;

type Timer = hyperloop::timer::Timer<SysTickTimer<SYSCLK_FREQ_HZ>>;

static G_TIMER_QUEUE: Mutex<Cell<Option<Pin<&TimerQueue<SysTickTimer<SYSCLK_FREQ_HZ>>>>>> =
    Mutex::new(Cell::new(None));

/// Systick exception handler
#[exception]
fn SysTick() {
    static mut TIMER_QUEUE: Option<Pin<&TimerQueue<SysTickTimer<SYSCLK_FREQ_HZ>>>> = None;

    let timer_queue = TIMER_QUEUE.get_or_insert_with(|| {
        cortex_m::interrupt::free(|cs| G_TIMER_QUEUE.borrow(cs).take().unwrap())
    });

    timer_queue.interrupt_handler();
}

/// Simple task that blinks toggles LED every second
#[task(priority = 1)]
async fn blinky(timer: Timer, mut led: ErasedPin<Output>) {
    // Use periodic for even 1 second period
    let mut periodic = timer.periodic(Duration::secs(1));

    loop {
        defmt::println!("Time: {}", timer.now().duration_since_epoch().to_micros());

        // Toggle led and wait till next period
        led.toggle();
        periodic.wait().await;
    }
}

#[entry]
fn main() -> ! {
    let mut cp = cortex_m::Peripherals::take().unwrap();
    let dp = Peripherals::take().unwrap();

    // Configure PC13 pin to blink LED
    let mut gpioc = dp.GPIOC.split();
    let mut led = gpioc.pc13.into_push_pull_output(&mut gpioc.crh).erase();
    led.set_high(); // Turn off

    // Set up systick timer
    let timer_queue = {
        static mut TIMER_QUEUE: Option<TimerQueue<SysTickTimer<SYSCLK_FREQ_HZ>>> = None;

        unsafe {
            TIMER_QUEUE = Some(TimerQueue::new(SysTickTimer::new(
                &mut cp.DCB,
                cp.DWT,
                cp.SYST,
                SYSCLK_FREQ_HZ,
            )));
        }

        let timer_queue =
            unsafe { Pin::new_unchecked(TIMER_QUEUE.as_ref().unwrap_or_else(|| unreachable!())) };

        cortex_m::interrupt::free(|cs| {
            G_TIMER_QUEUE.borrow(cs).replace(Some(timer_queue));
        });

        timer_queue
    };

    // Create executor with blinky task
    let mut executor = static_executor!(blinky(timer_queue.get_timer(), led).unwrap());

    loop {
        timer_queue.wake_tasks();
        executor.poll_tasks();

        // Commented out `wait_for_alarm()` because `wfi` prevents
        // debugger from connecting, see
        // https://github.com/probe-rs/probe-rs/issues/350#issuecomment-740550519
        // for a fix

        // timer_queue.wait_for_alarm();
    }
}
