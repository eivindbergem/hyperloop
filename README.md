![Pipeline](https://github.com/rustne-kretser/hyperloop/actions/workflows/rust.yml/badge.svg)
[![Crates.io](https://img.shields.io/crates/v/hyperloop.svg)](https://crates.io/crates/hyperloop)
[![API reference](https://docs.rs/hyperloop/badge.svg)](https://docs.rs/hyperloop/)

# Hyperloop – the new superloop

Hyperloop is a priority based async runtime targetting embedded
systems.

Features:
- Static allocation
- Priority based scheduling of async tasks
- No critical sections, uses atomics for concurrent access
- Unsafe code tested with miri, concurrency tested with loom

## Example
```rust
/// Simple task that blinks toggles LED every second
#[task(priority = 1)]
async fn blinky(timer: Timer, mut led: OutputPin) {
    // Use periodic for even 1 second period
    let mut periodic = timer.periodic(Duration::secs(1));
    loop {
        // Toggle led and wait till next period
        led.toggle();
        periodic.wait().await;
    }
}

fn main() {
    let timer_queue = [...];
    let led = [...];

    // Create executor with blinky task
    let mut executor = static_executor!(blinky(timer_queue.get_timer(), led).unwrap());

    // Start the timer
    timer_queue.start_timer();

    loop {
        timer_queue.wake_tasks();
        executor.poll_tasks();

        timer_queue.wait_for_alarm();
    }
}
```

See the `examples/` directory for complete examples.

For more details, see [docs](https://docs.rs/hyperloop/).

## Minimum supported Rust version (MSRV)

Requires nightly for macros.

## Usage

Add this to your Cargo.toml:

```toml
[dependencies]
hyperloop = "0.1.0"
```

## License

MPL-2.0

## FAQ

### Why async? Can't we just use plain old stackful tasks?

Async tasks have a minimal memory footprint and are a good fit for
memory constrained microcontrollers. Tasks should be cheap and you
should be able to another task without having to worry much about
memory usage. Stackful tasks need a lot of memory for the stack,
especially if you need string formatting for logging. Stackful tasks
do allow for preemption, but it comes at a high price.

### How does Hyperloop differ from [Embassy](https://github.com/embassy-rs/embassy)

Embassy provides not only an executor, but a whole embedded async
ecosystem. Hyperloop is much more limited in scope. The main
difference between the Embassy exeutor and Hyperloop is that Hyperloop
uses priority based scheduling.
