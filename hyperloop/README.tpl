![Pipeline](https://github.com/rustne-kretser/hyperloop/actions/workflows/rust.yml/badge.svg)
[![Crates.io](https://img.shields.io/crates/v/hyperloop.svg)](https://crates.io/crates/hyperloop)
[![API reference](https://docs.rs/hyperloop/badge.svg)](https://docs.rs/hyperloop/)

# Hyperloop – the new superloop

{{readme}}

For more details, see [docs](https://docs.rs/hyperloop/).

## Minimum supported Rust version (MSRV)

Requires nightly for macros.

## Usage

Add this to your Cargo.toml:

```toml
[dependencies]
{{crate}} = "{{version}}"
```

## License

{{license}}

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
