use test::Bencher;
use solver::Solution;

mod tools;
mod jnh01;
mod jnh02;
mod jnh03;
mod jnh12;

#[bench]
fn wikipedia(b: &mut Bencher) {
  let p = tools::load_problem("
p cnf 12 8
1 4 0
1 -3 -8 0
1 8 12 0
2 11 0
-7 -3 9 0
-7 8 -9 0
7 8 -10 0
7 10 -12");
    b.iter(|| ::solver::solve(
    	&p.expression,
    	p.varcount,
    	Solution::new(p.varcount)).unwrap())
}