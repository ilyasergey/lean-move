#!/usr/bin/env bash
# Self-contained, deterministic corroboration of the paper's Section 6 numbers.
#
# This uses the SMALL sample bundled in this repository (sample.zip) — no dataset
# download is required. run.sh reproduces the FULL result but needs the entire
# ~13-16 GB sui-packages dataset (fetched from its public source) and hours of
# compute; this script instead times both reference-safety analyses on ~15,000
# framework functions in a few minutes, so the paper's headline ratio (regex
# ≈ 2.2x the deployed checker, tens of microseconds per function) can be checked
# quickly.
#
# Determinism: sample.zip is fixed bytes committed to the repo; the Rust
# toolchain is pinned by rust-toolchain.toml; and the Sui verifier revision under
# test is pinned in reference-safety-bench/Cargo.toml. Only the absolute timings
# vary with hardware.
#
# Provenance of sample.zip (see README.md, "What is shipped"): the 1,889 compiled
# `.mv` modules of the on-chain Move/Sui framework packages published at address
# 0x00, extracted from the public MystenLabs/sui-packages dataset at commit
# a2fa397e63496de98bba78333d6f896a1cd06bb0 (path packages/mainnet/0x00).
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BENCH_DIR="$SCRIPT_DIR/reference-safety-bench"
MANIFEST="$BENCH_DIR/Cargo.toml"
SAMPLE_ZIP="$SCRIPT_DIR/sample.zip"
SAMPLE_DIR="$SCRIPT_DIR/sample-data"          # gitignored extraction target
SAMPLE_PATH="packages/mainnet/0x00"

echo "== Section 6 corroboration (self-contained; bundled sample) =="

# 1. Toolchain check (version is pinned by rust-toolchain.toml; rustup installs it).
if ! command -v cargo >/dev/null 2>&1; then
  echo "ERROR: cargo/rustc not found. Install Rust from https://rustup.rs" >&2
  echo "       (rust-toolchain.toml pins the exact version; rustup fetches it)." >&2
  exit 1
fi

# 2. Extract the bundled sample FRESH (from scratch); nothing is downloaded.
#    Any previous extraction is discarded so every run starts from a clean state.
echo "Extracting bundled sample ($(basename "$SAMPLE_ZIP")) from scratch..."
rm -rf "$SAMPLE_DIR"
mkdir -p "$SAMPLE_DIR"
unzip -q "$SAMPLE_ZIP" -d "$SAMPLE_DIR"
n_mv=$(find "$SAMPLE_DIR/$SAMPLE_PATH" -name '*.mv' | wc -l | tr -d ' ')
echo "Sample: $n_mv compiled .mv modules"

# 3. Build (release; toolchain pinned by rust-toolchain.toml, Sui rev by Cargo.toml).
echo "Building (release)..."
cargo build --release --manifest-path "$MANIFEST"

# 4. Run (jobs=1 for the most accurate absolute timings).
BIN="$BENCH_DIR/target/release/reference-safety-bench"
echo
"$BIN" "$SAMPLE_DIR/$SAMPLE_PATH" --jobs 1

cat <<'EOF'

-- How to read this --
Expected: ratio mean(new)/mean(old) of roughly ~2x (the paper reports 2.2x over
the full corpus of 2.9M functions), and a mean regex time of tens of microseconds
per function. Exact values vary with hardware and with this framework-only
subsample (e.g. an Apple M2 gives ~2.03x and ~18 us/function). The complete
Section 6 figures require run.sh over the entire public dataset.
EOF
