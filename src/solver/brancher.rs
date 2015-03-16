use std::iter::FromIterator;
use collections::VecSet;
use solver::types::Var;
use solver::types::SolutionValue::{self, True, False};

/**
 * Defines a trait for picking which branches to use.
 */
pub trait Brancher {
    fn pick_branch(&self) -> Option<(Var, SolutionValue)>;
    fn is_empty(&self) -> bool;
    fn remove(&mut self, Var);
    fn insert(&mut self, Var);

    /**
     * Is the given variable sill in the set of possible branches?
     */
    fn contains(&self, Var) -> bool;

    /**
     * Prod a variable whenever its used in a learned clause.
     */
    fn ping(&mut self, Var);

    fn remove_all(&mut self, vars: &[Var]) {
        for v in vars.iter() {
            self.remove(*v);
        }
    }
}

// ----------------------------------------------------------------------------
// A naive, lowest-indexed-variable-first branching algorithm.
// ----------------------------------------------------------------------------

pub struct NaiveBrancher {
    vars: VecSet<Var>
}

impl NaiveBrancher {
    pub fn new(n: usize) -> NaiveBrancher {
        NaiveBrancher { vars: FromIterator::from_iter(1..n+1) }
    }
}

impl Brancher for NaiveBrancher {
    fn pick_branch(&self) -> Option<(Var, SolutionValue)> {
        match self.vars.iter().next() {
            None => None,
            Some(var) => Some((*var, False))
        }
    }

    fn is_empty(&self) -> bool {
        self.vars.is_empty()
    }

    fn contains(&self, var: Var) -> bool {
        self.vars.contains(&var)
    }

    fn remove(&mut self, v: Var) {
        println!("Removing {:?}", v);
        self.vars.remove(&v);
        println!("State is now {:?}", self.vars);
    }

    fn insert(&mut self, v: Var) {
        self.vars.insert(v);
    }

    fn ping(&mut self, _: Var) {}
}

#[test]
fn naive_brancher_returns_lowest_variable() {
    let mut b = NaiveBrancher::new(10);
    for i in (1..11) {
        let (var, val) = b.pick_branch().unwrap();
        assert_eq!(i, var);
        b.remove(i);
    }
}

#[test]
fn naive_brancher_always_returns_false() {
    let mut b = NaiveBrancher::new(10);
    for i in (1..11) {
        let (var, val) = b.pick_branch().unwrap();
        assert_eq!(False, val);
        b.remove(i);
    }
}

#[test]
fn naive_brancher_knows_its_contents() {
    let mut b = NaiveBrancher::new(10);
    assert!((1..11).all(|x| b.contains(x)));
    assert!(!b.contains(0));
    assert!(!b.contains(11));
}

#[test]
fn naive_brancher_knows_when_its_empty() {
    let mut b = NaiveBrancher::new(1);
    assert!(!b.is_empty());
    b.remove(1);
    assert!(b.is_empty());
}

#[test]
fn naive_brancher_returns_none_when_empty() {
    let mut b = NaiveBrancher::new(1);
    b.remove(1);
    assert!(b.pick_branch().is_none());
}