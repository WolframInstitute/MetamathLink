#!/bin/sh
# MetamathLink's library for this platform: `cargo wl build` (cargo-wl, from WolframResearch/wolfram-rust-library)
# compiles the crate in MetamathLink/Libs/metamath_link and writes the library with its generated loader, Functions.wl,
# into MetamathLink/Binaries/metamath_link-<SystemID>/, which Kernel/Library.wl gets. Its Rust tests run first.
set -e
cd "$(dirname "$0")/../MetamathLink/Libs/metamath_link"
command -v cargo-wl > /dev/null || cargo install cargo-wl --locked
cargo test --release --lib
cargo wl build --release
