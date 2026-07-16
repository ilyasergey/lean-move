#!/usr/bin/env bash
# Reproduce the borrow-checker performance numbers comparing the regex-based
# reference-safety checker against the deployed (graph-based) one.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BENCH_DIR="$SCRIPT_DIR/reference-safety-bench"
MANIFEST="$BENCH_DIR/Cargo.toml"

echo "== Reference-safety benchmark reproduction =="

# 1. Toolchain check (do not auto-install).
if ! command -v cargo >/dev/null 2>&1; then
  echo "ERROR: cargo/rustc not found. Install Rust from https://rustup.rs and retry." >&2
  echo "       (edition 2024 requires a recent stable Rust, >= 1.85.)" >&2
  exit 1
fi

# 2. Dataset location (env var wins; otherwise prompt, default $HOME/sui-packages).
if [ -n "${SUI_PACKAGES_DIR:-}" ] && [ -d "${SUI_PACKAGES_DIR}" ]; then
  echo "Using SUI_PACKAGES_DIR=$SUI_PACKAGES_DIR"
else
  default_dir="$HOME/sui-packages"
  printf "Path to sui-packages checkout [%s]: " "$default_dir"
  read -r reply
  SUI_PACKAGES_DIR="${reply:-$default_dir}"
  if [ ! -d "$SUI_PACKAGES_DIR" ]; then
    printf "%s does not exist. Clone MystenLabs/sui-packages there now? [y/N]: " "$SUI_PACKAGES_DIR"
    read -r yn
    case "$yn" in
      [Yy]*)
        echo "Cloning (shallow) into $SUI_PACKAGES_DIR ... this repository is large."
        git clone --depth 1 https://github.com/MystenLabs/sui-packages "$SUI_PACKAGES_DIR"
        ;;
      *)
        echo "Cannot proceed without the dataset. Exiting." >&2
        exit 1
        ;;
    esac
  fi
fi
echo "Tip: export SUI_PACKAGES_DIR=\"$SUI_PACKAGES_DIR\" to skip this prompt next time."

# 3. Corpus choice.
echo
echo "Which corpus?"
echo "  [1] mainnet most used (fast)"
echo "  [2] all mainnet (full, slow)"
printf "Choice [1]: "
read -r corpus
case "${corpus:-1}" in
  2) TARGET="$SUI_PACKAGES_DIR/packages/mainnet" ;;
  *) TARGET="$SUI_PACKAGES_DIR/packages/mainnet_most_used" ;;
esac
if [ ! -d "$TARGET" ]; then
  echo "ERROR: expected corpus directory not found: $TARGET" >&2
  exit 1
fi
echo "Corpus: $TARGET"

# 4. Jobs (default 1; parallelism is opt-in).
if command -v nproc >/dev/null 2>&1; then
  ncpu="$(nproc)"
elif command -v sysctl >/dev/null 2>&1; then
  ncpu="$(sysctl -n hw.ncpu 2>/dev/null || echo '?')"
else
  ncpu="?"
fi
echo
echo "Parallel jobs. Default 1 gives the most accurate timings; more jobs will"
echo "be faster (depending on the system) faster but inflate the results."
printf "Jobs [1] (this machine reports %s CPUs): " "$ncpu"
read -r jobs
JOBS="${jobs:-1}"

# 5. Build (release only -- never debug).
echo
echo "Building (release)..."
cargo build --release --manifest-path "$MANIFEST"

# 6. Run.
BIN="$BENCH_DIR/target/release/reference-safety-bench"
echo
echo "Running: $BIN $TARGET --jobs $JOBS"
echo
"$BIN" "$TARGET" --jobs "$JOBS"
