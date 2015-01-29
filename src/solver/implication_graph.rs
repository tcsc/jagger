use std::collections;
use std::collections::{HashMap};
use solver::types;
use solver::types::{Solution, SolutionValue, Expression, Var, VarSet};
use solver::types::Term::{self, Lit, Not};


// ----------------------------------------------------------------------------
// Implication graph implementation
// ----------------------------------------------------------------------------

pub struct ImplicationGraph {
    map: HashMap<Var, VarSet>
}

impl ImplicationGraph {
    pub fn new() -> ImplicationGraph {
        ImplicationGraph { map: HashMap::new() }
    }

    pub fn from(items: &[(Var, &[Var])]) -> ImplicationGraph {
        let mut g = ImplicationGraph::new();
        for &(var, roots) in items.iter() {
            for r in roots.iter() {
                g.add(var, *r);
            }
        }
        g
    }

    pub fn add(&mut self, v: Var, root: Var) {
        let mut insert_new = false;
        match self.map.get_mut(&v) {
            Some (s) => { s.insert(root); },
            None => { insert_new = true; }
        }

        if insert_new {
            let mut s = VarSet::new();
            s.insert(root);
            self.map.insert(v, s);
        }       
    }

    pub fn erase(&mut self, v: Var) {
        self.map.remove(&v);
    }

    pub fn add_from_clause(&mut self, v: Var, clause: &[Term]) {
        for t in clause.iter() {
            let root = t.var();
            if root != v { self.add(v, root); }
        }
    }

    pub fn get_roots(&self, v: Var) -> Vec<Var> {
        match self.map.get(&v) {
            Some (s) => s.iter().map(|v| *v).collect(),
            None => Vec::new()
        }
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    pub fn len(&self) -> usize {
        self.map.len()
    }
}

#[test]
fn implication_graph_duplicate_roots_are_not_added() {
    let mut g = ImplicationGraph::new();
    g.add(42, 1);
    g.add(42, 1);
    let x = g.get_roots(42);
    assert!(x.len() == 1);
    assert!(x.iter().any(|v| *v == 1));
}

#[test]
fn implication_graph_unset_roots_returns_empty_vec() {
    let mut g = ImplicationGraph::new();
    let x = g.get_roots(42);
    assert!(x.is_empty());
}

#[test]
fn implication_graph_setting_from_clause_doesnt_include_target() {
    let mut g = ImplicationGraph::new();
    g.add_from_clause(2, &[Lit(1), Lit(2), Lit(3)]);
    g.add_from_clause(2, &[Not(2), Lit(3), Lit(4)]);
    let x = g.get_roots(2);
    assert!(x.len() == 3);
    assert!(x.iter().any(|v| *v == 1));
    assert!(x.iter().any(|v| *v == 3));
    assert!(x.iter().any(|v| *v == 4));
}

#[test]
fn implication_graph_erase_erases() {
    let mut g = ImplicationGraph::new();
    g.add_from_clause(1, &[Lit(1), Lit(2), Lit(3)]);
    g.add_from_clause(2, &[Lit(1), Lit(2), Lit(3)]);
    g.add_from_clause(3, &[Not(2), Lit(3), Lit(4)]);

    g.erase(2);
    assert!(g.get_roots(2).is_empty());

    assert!(!g.get_roots(1).is_empty());
    assert!(!g.get_roots(3).is_empty());
}