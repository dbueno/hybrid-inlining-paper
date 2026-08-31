use hybrid_inlining_paper::analysis::run_hybrid;
use hybrid_inlining_paper::{families::*, figure1, figure5};

fn total(summary: &str) -> usize {
    summary.lines().filter_map(|l| l.split_once(" size: ")).filter_map(|(_, r)| r.trim().parse::<usize>().ok()).sum()
}

fn main() {
    for (name, prog, k) in [
        ("figure1", figure1::program(), 4),
        ("figure5", figure5::program(), 4),
        ("chain(16)", chain(16, 2), 18),
        ("fanin(32)", fanin(32, 3), 4),
        ("branching(7)", branching(7, 2), 9),
        ("targets(8)", targets(8), 1),
        ("wide(32,8)", wide(32, 8), 0),
        ("recursive_field", recursive_field(), 3),
        ("dead_receiver", dead_receiver(), 3),
    ] {
        let h = run_hybrid(&prog, k);
        let s = h.relation_sizes_summary();
        println!("{name:<16} all-relations={:<6} pending={:<5} resolve={:<4} points={:<6} edge={}",
                 total(&s), h.pending.len(), h.resolve.len(), h.points.len(), h.edge.len());
    }
}
