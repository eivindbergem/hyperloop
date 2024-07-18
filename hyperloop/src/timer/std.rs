//! Standard library based [`HardwareTimer`]
//!
//! Implementation of [`HardwareTimer`] using Rust standard
//! library. This is mostly useful for testing code in pure software.

use std::{sync::Mutex, time::Instant};

use crate::timer::HardwareTimer;

/// Standard library based [`HardwareTimer`]
pub struct StdTimer {
    alarm: Mutex<Option<Instant>>,
}

impl StdTimer {
    pub fn new() -> Self {
        Self {
            alarm: Mutex::new(None),
        }
    }
}

impl Default for StdTimer {
    fn default() -> Self {
        Self::new()
    }
}

impl HardwareTimer for StdTimer {
    type Instant = std::time::Instant;
    type Duration = std::time::Duration;

    fn start(&self) {}

    fn now(&self) -> Self::Instant {
        Self::Instant::now()
    }

    fn set_alarm(&self, expires: Option<Self::Instant>) {
        *self.alarm.lock().unwrap() = expires;
    }

    fn wait_for_alarm(&self) {
        if let Some(alarm) = self.alarm.lock().unwrap().as_ref() {
            if let Some(delay) = alarm.checked_duration_since(Instant::now()) {
                std::thread::sleep(delay);
            }
        }
    }
}
