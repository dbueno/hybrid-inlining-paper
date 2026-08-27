use hybrid_inlining_poc::example::figure1;

fn main() {
    let mut prog = figure1();
    prog.run();
    println!("{}", prog.relation_sizes_summary());
}
