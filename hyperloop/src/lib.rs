//! Hyperloop is a priority based async runtime targetting embedded
//! systems.
//!
//! Features:
//! - Static allocation
//! - Priority based scheduling of async tasks
//! - Fixed capacity executor
//! - No critical sections, uses atomics for concurrent access
//! - Unsafe code tested with miri, concurrency tested with loom
//!
//! # Example
//! ```ignore
//! /// Simple task that blinks toggles LED every second
//! #[task(priority = 1)]
//! async fn blinky(timer: Timer, mut led: OutputPin) {
//!     // Use periodic for even 1 second period
//!     let mut periodic = timer.periodic(Duration::secs(1));
//!     loop {
//!         // Toggle led and wait till next period
//!         led.toggle();
//!         periodic.wait().await;
//!     }
//! }
//!
//! fn main() {
//!     let timer_queue = [...];
//!     let led = [...];
//!
//!     // Create executor with blinky task
//!     let mut executor = static_executor!(blinky(timer_queue.get_timer(), led).unwrap());
//!
//!     // Start the timer
//!     timer_queue.start_timer();
//!
//!     loop {
//!         timer_queue.wake_tasks();
//!         executor.poll_tasks();
//!
//!         timer_queue.wait_for_alarm();
//!     }
//! }
//! ```
//!
//! See the `examples/` directory for complete examples.

#![cfg_attr(not(any(test, feature = "std")), no_std)]
#![cfg_attr(feature = "nightly", feature(doc_cfg))]

mod common;

pub mod executor;
pub mod task;
pub mod timer;

#[cfg(feature = "macros")]
pub use hyperloop_macros::*;
