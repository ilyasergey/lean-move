//! Summary statistics for a set of per-function timings, reported in microseconds.

pub struct Summary {
    pub count: usize,
    pub mean_us: f64,
    pub median_us: f64,
    pub p90_us: f64,
    pub p95_us: f64,
    pub p99_us: f64,
    pub min_us: f64,
    pub max_us: f64,
    pub stddev_us: f64,
    pub total_us: f64,
}

impl Summary {
    /// Sorts `samples` (nanoseconds) in place and computes the summary in microseconds.
    pub fn from_nanos(samples: &mut [u64]) -> Self {
        let count = samples.len();
        if count == 0 {
            return Summary {
                count: 0,
                mean_us: 0.0,
                median_us: 0.0,
                p90_us: 0.0,
                p95_us: 0.0,
                p99_us: 0.0,
                min_us: 0.0,
                max_us: 0.0,
                stddev_us: 0.0,
                total_us: 0.0,
            };
        }
        samples.sort_unstable();
        let sum: u128 = samples.iter().map(|&x| x as u128).sum();
        let mean_ns = sum as f64 / count as f64;
        let variance = samples
            .iter()
            .map(|&x| {
                let d = x as f64 - mean_ns;
                d * d
            })
            .sum::<f64>()
            / count as f64;
        let stddev_ns = variance.sqrt();

        // Nearest-rank percentile over the sorted samples.
        let pct = |p: f64| -> f64 {
            let rank = ((p / 100.0) * count as f64).ceil() as usize;
            let idx = rank.saturating_sub(1).min(count - 1);
            samples[idx] as f64 / 1000.0
        };

        Summary {
            count,
            mean_us: mean_ns / 1000.0,
            median_us: pct(50.0),
            p90_us: pct(90.0),
            p95_us: pct(95.0),
            p99_us: pct(99.0),
            min_us: samples[0] as f64 / 1000.0,
            max_us: samples[count - 1] as f64 / 1000.0,
            stddev_us: stddev_ns / 1000.0,
            total_us: sum as f64 / 1000.0,
        }
    }
}
