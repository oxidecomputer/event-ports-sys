#!/bin/bash
#:
#: name = "build"
#: variety = "basic"
#: target = "helios-2.0"
#: rust_toolchain = "stable"

set -o errexit
set -o pipefail
set -o xtrace

pfexec pkg install clang-15

cargo --version
rustc --version

banner "check"
cargo fmt -- --check
cargo clippy --all-targets -- --deny warnings

banner "test"
cargo test --doc

banner "build"
cargo build
