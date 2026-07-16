# Borrow checker performance benchmark

Reproduces the wall-time performance of the new regex-based reference safety checker vs the deployed (graph-based) approach.

The tool times both reference safety analyses per Move function, in isolation, over the corpus of published Sui packages, and reports the ratio of the means plus richer statistics (median, p90/p95/p99, min, max, std dev, total).

## What it measures

For each non-native function it times:

- **old**: `move_bytecode_verifier::reference_safety::verify` (deployed, borrow graph based), and
- **new**: `move_bytecode_verifier::regex_reference_safety::verify` (regex based).

Both run back-to-back on the same thread per function. Timing uses nanosecond resolution internally and is reported in microseconds.

## What is shipped

This folder is self-contained. It contains:

- **The benchmarking tool** — a small Rust crate under `reference-safety-bench/`
  (`src/main.rs`, `bench.rs`, `stats.rs`), with its dependencies pinned in
  `Cargo.lock` and the Rust toolchain pinned in `rust-toolchain.toml`. The two
  reference safety analyses it times are **not** vendored here: they are pulled,
  at a pinned revision, from the public `MystenLabs/sui` repository (the `move-*`
  git dependencies in `reference-safety-bench/Cargo.toml`), which is where both
  the deployed (`reference_safety`) and the new (`regex_reference_safety`)
  checkers live. See [`IMPLEMENTATION.md`](IMPLEMENTATION.md) for a guide to that
  implementation — direct links to it online (pinned) and how it maps to the Lean
  artefact.
- **`run.sh`** — reproduces the full Section 6 result over the entire corpus.
- **`corroborate.sh`** — a quick, self-contained corroboration over the bundled
  sample.
- **`sample.zip` — the bundled sample** used by `corroborate.sh`:
  - **Size:** ~7 MB compressed (~18 MB extracted).
  - **Contents:** 1,889 compiled `.mv` modules — the bytecode the verifier
    actually consumes (~4.6 MB) — plus the 1,889 corresponding decompiled
    `.move` sources (~13 MB, shipped for human readability/documentation only;
    the tool ignores everything that is not `.mv`). Together they hold ~15,279
    non-native functions.
  - **How it was selected:** it is exactly the on-chain Move/Sui **framework**
    packages published at address `0x00` — the Move standard library and the Sui
    framework (`option`, `vector`, `string`, `coin`, `transfer`, …). This address
    is present and identical for every reader, is real production bytecode, and is
    large enough (~15k functions) for a stable ratio yet small enough to bundle.
    It is not cherry-picked for favourable timings — it is simply the first,
    foundational package group.
  - **Provenance / how to re-derive the exact bytes** (without this bundle), from
    the public dataset at a pinned commit:
    ```sh
    git init sample && cd sample
    git remote add origin https://github.com/MystenLabs/sui-packages
    git fetch --filter=tree:0 --depth 1 origin a2fa397e63496de98bba78333d6f896a1cd06bb0
    git sparse-checkout init --no-cone
    git sparse-checkout set packages/mainnet/0x00
    git checkout FETCH_HEAD
    ```

**Not shipped:** the full ~13–16 GB corpus of all published Sui packages —
`run.sh` fetches it from its public source on demand; it is never stored here.

## Requirements

- A Rust toolchain. The exact version is pinned by `rust-toolchain.toml`
  (edition 2024 needs Rust ≥ 1.85); `rustup` reads that file and installs the
  pinned toolchain automatically. Install `rustup` via https://rustup.rs.
- Network access on first build, to fetch the pinned Sui crates (both scripts).
- For the **full** run (`run.sh`) only: the `MystenLabs/sui-packages` dataset,
  fetched from its public source — roughly **13–16 GB** (as of 15 July 2026). The
  small sample corroboration (`corroborate.sh`) needs **no** dataset download; it
  uses the bundled `sample.zip`.

## Run

```sh
./run.sh
```

The script will:

1. check for `cargo`/`rustc`
2. locate the dataset. It uses `$SUI_PACKAGES_DIR` if set, otherwise prompts for a directory (default `$HOME/sui-packages`) and offers to shallow-clone `MystenLabs/sui-packages`
3. ask which corpus to run: **mainnet most used** (`packages/mainnet_most_used`, fast) or **all mainnet** (`packages/mainnet`, full/slow)
4. ask for the number of parallel jobs (default 1)
5. build (in **release**) and run.

You can also run the tool directly (it has exactly two settings):

```sh
cargo build --release --manifest-path reference-safety-bench/Cargo.toml
./reference-safety-bench/target/release/reference-safety-bench <TARGET_DIR> --jobs <N>
```

## Deterministic small sample corroboration

The full run above needs the entire ~13–16 GB dataset and hours of compute. For a
quick, **self-contained** check that needs **no dataset download**:

```sh
./corroborate.sh
```

It extracts the bundled `sample.zip` (see “What is shipped”), builds the tool,
and times both analyses over the ~15,000 framework functions, printing the same
statistics as `run.sh`. Everything is deterministic: `sample.zip` is fixed bytes
committed to the repo, the Rust toolchain is pinned by `rust-toolchain.toml`, and
the Sui verifier revision under test is pinned in
`reference-safety-bench/Cargo.toml`. Only the absolute timings vary with hardware.

On an Apple M2 the sample gives a ratio of **≈2.0×** and a mean regex time of
**≈18 µs/function**, corroborating the paper's full corpus figures of **2.2×**
and **≈30 µs** (the subsample is framework-only and the hardware is not an
M1 Max, so the absolute microseconds are lower). Exact numbers vary by hardware;
the complete figures require `./run.sh` over the whole dataset.

## Dataset notes

`packages/mainnet_most_used/` entries are symlinks into `packages/mainnet/`.

The corpus contains only packages the deployed bytecode verifier accepts, which includes the deployed (graph-based) approach. The regex-based approach is strictly more expressive. As such, both analyses should accept every function.

The **full** dataset is not stored in this repository: `run.sh` fetches it from
its public source (`MystenLabs/sui-packages`) on demand, into a gitignored
directory. `corroborate.sh` uses the small bundled `sample.zip` and downloads no
dataset at all. Version-controlled here are only the tool sources, the pinned
`Cargo.lock` and `rust-toolchain.toml`, the scripts, and `sample.zip`.
