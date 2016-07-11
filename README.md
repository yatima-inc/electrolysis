# electrolysis

[![Gitter](https://badges.gitter.im/Kha/electrolysis.svg)](https://gitter.im/Kha/electrolysis?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)

## About

A tool for formally verifying Rust programs by transpiling them into definitions in the [Lean](http://leanprover.github.io/) theorem prover. [Presentation at Oregon Programming Languages Summer School](presentation/presentation.pdf)

## Installation

Because electrolysis uses `rustc`'s unstable private API, you need a nightly compiler. Because the API is _highly_ unstable, you need a very specific nightly version, for which you should use [rustup.rs](https://www.rustup.rs/). After installing `rustup`, you can build this project by executing
```
electrolysis$ rustup override add $(cat rust-nightly-version)
electrolysis$ cargo run core
```
This will build the project and export all code from the `core` crate necessary for `binary_search` (see also [thys/core/config.toml](thys/core/config.toml)) into [thys/core/generated.lean](thys/core/generated.lean) (this file already exists in case you just want to examine the correctness proof).
