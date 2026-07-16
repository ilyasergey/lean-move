//! Times the old (graph-based) vs new (regex-based) reference-safety analyses
//! for every function in a corpus of compiled Move modules, and reports the
//! ratio plus summary statistics.

use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};

use clap::Parser;
use rayon::prelude::*;
use walkdir::WalkDir;

use move_binary_format::CompiledModule;
use move_vm_config::verifier::VerifierConfig;

mod bench;
mod stats;
use stats::Summary;

#[derive(Parser)]
#[command(
    name = "reference-safety-bench",
    about = "Time old (graph) vs new (regex) reference-safety per Move function"
)]
struct Args {
    /// Directory searched recursively for compiled Move modules (.mv).
    target_dir: PathBuf,

    /// Number of parallel jobs. Default 1 gives the most accurate absolute
    /// timings; more jobs are faster but can inflate absolute microseconds.
    #[arg(short = 'j', long = "jobs", default_value_t = 1)]
    jobs: usize,
}

fn main() -> anyhow::Result<()> {
    // Debug builds (debug assertions on, no optimization) produce meaningless
    // timings. debug_assert! compiles to nothing in release, so this only fires
    // when someone runs the debug build.
    debug_assert!(
        false,
        "reference-safety-bench must be built in release mode \
         (cargo build --release); debug builds produce meaningless timings"
    );

    let args = Args::parse();
    anyhow::ensure!(args.jobs >= 1, "--jobs must be >= 1");

    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(args.jobs)
        .build()?;

    eprintln!("Scanning {} for .mv files...", args.target_dir.display());
    // mainnet_most_used entries are symlinks into mainnet, so follow them.
    let files: Vec<PathBuf> = WalkDir::new(&args.target_dir)
        .follow_links(true)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.file_type().is_file())
        .map(|e| e.into_path())
        .filter(|p| p.extension().map(|x| x == "mv").unwrap_or(false))
        .collect();
    anyhow::ensure!(
        !files.is_empty(),
        "no .mv files found under {}",
        args.target_dir.display()
    );
    eprintln!(
        "Found {} module files. Running with {} job(s)...",
        files.len(),
        args.jobs
    );

    let config = VerifierConfig::default();
    let read_errors = AtomicUsize::new(0);
    let done = AtomicUsize::new(0);
    let nfiles = files.len();

    // Per function: (old_nanos, new_nanos, old_ok, new_ok).
    let results: Vec<(u64, u64, bool, bool)> = pool.install(|| {
        files
            .par_iter()
            .flat_map_iter(|path| {
                let n = done.fetch_add(1, Ordering::Relaxed) + 1;
                if n % 20_000 == 0 {
                    eprintln!("  {}/{} modules", n, nfiles);
                }
                let module = match std::fs::read(path)
                    .ok()
                    .and_then(|bytes| CompiledModule::deserialize_with_defaults(&bytes).ok())
                {
                    Some(m) => m,
                    None => {
                        read_errors.fetch_add(1, Ordering::Relaxed);
                        return Vec::new().into_iter();
                    }
                };
                bench::time_reference_safety(&config, &module)
                    .into_iter()
                    .map(|t| (t.old_nanos as u64, t.new_nanos as u64, t.old_ok, t.new_ok))
                    .collect::<Vec<_>>()
                    .into_iter()
            })
            .collect()
    });

    let mut old_ns: Vec<u64> = Vec::with_capacity(results.len());
    let mut new_ns: Vec<u64> = Vec::with_capacity(results.len());
    let mut old_failures = 0usize;
    let mut new_failure_reported = false;
    for &(o, n, old_ok, new_ok) in &results {
        if !new_ok {
            if !new_failure_reported {
                eprintln!(
                    "INTERNAL ERROR: regex-based analysis should accept every function in the corpus"
                );
                new_failure_reported = true;
            }
            continue;
        }
        if !old_ok {
            old_failures += 1;
            continue;
        }
        old_ns.push(o);
        new_ns.push(n);
    }

    assert_eq!(old_ns.len(), new_ns.len());
    let old = Summary::from_nanos(&mut old_ns);
    let new = Summary::from_nanos(&mut new_ns);
    print_report(nfiles, read_errors.into_inner(), &old, &new, old_failures);
    Ok(())
}

fn print_report(
    nfiles: usize,
    read_errors: usize,
    old: &Summary,
    new: &Summary,
    old_failures: usize,
) {
    println!();
    println!(
        "== Reference-safety timing: {} functions across {} modules ({} unreadable) ==",
        old.count, nfiles, read_errors
    );
    println!();
    println!("{:<14}{:>18}{:>18}", "", "old (graph)", "new (regex)");
    let row = |label: &str, a: f64, b: f64| {
        println!("{:<14}{:>18.3}{:>18.3}", label, a, b);
    };
    println!("{:<14}{:>18}{:>18}", "count", old.count, new.count);
    row("total (μs)", old.total_us, new.total_us);
    row("p90 (μs)", old.p90_us, new.p90_us);
    row("p95 (μs)", old.p95_us, new.p95_us);
    row("p99 (μs)", old.p99_us, new.p99_us);
    row("min (μs)", old.min_us, new.min_us);
    row("max (μs)", old.max_us, new.max_us);
    row("stddev (μs)", old.stddev_us, new.stddev_us);
    row("median (μs)", old.median_us, new.median_us);
    row("mean (μs)", old.mean_us, new.mean_us);
    println!();

    let ratio = if old.mean_us > 0.0 {
        new.mean_us / old.mean_us
    } else {
        f64::NAN
    };
    println!("Ratio mean(new)/mean(old) = {:.2}x", ratio);
    println!("Mean new (regex) per function = {:.1} μs", new.mean_us);
    if old_failures > 0 {
        println!(
            "WARNING: {} functions failed the old (graph-based) analysis. This likely means that \
            the corpus contains packages that were published after the old analysis was disabled \
            and replaced with the regex-based analysis. These functions are excluded from the \
            timing report above.",
            old_failures
        );
    }
}
