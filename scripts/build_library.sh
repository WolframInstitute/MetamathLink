#!/bin/sh
# MetamathLink's library: `cargo wl build` (cargo-wl, from WolframResearch/wolfram-rust-library) compiles the crate in
# MetamathLink/Libs/metamath_link and writes the library with its generated loader, Functions.wl, into
# MetamathLink/Binaries/metamath_link-<SystemID>/, which Kernel/Library.wl gets. Its Rust tests run first.
#
#     sh scripts/build_library.sh          this platform
#     sh scripts/build_library.sh --all    the five platforms a release carries
#
# --all cross-compiles from a Mac, as TuringMachine does: the Rust targets of each platform (rustup target add) and the
# linkers .cargo/config.toml names, x86_64- and aarch64-unknown-linux-gnu-gcc and x86_64-w64-mingw32-gcc.
set -e
cd "$(dirname "$0")/../MetamathLink/Libs/metamath_link"
command -v cargo-wl > /dev/null || cargo install cargo-wl --locked
cargo test --release --lib
cargo wl build --release
if [ "$1" = "--all" ]; then
	for system_id in MacOSX-ARM64 MacOSX-x86-64 Linux-x86-64 Linux-ARM64 Windows-x86-64; do
		cargo wl build --release --system-id "$system_id"
	done
fi
