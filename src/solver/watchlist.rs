/**
 * Implements the 2-literal watch list algorithm. Currently on hold because I
 * obviously don't understand the algorithm and the data structures required. 
 */

use std::collections::{HashMap};
use std::iter::{Iterator, FromIterator, repeat};
use std::vec;

use solver::types::{Var, Clause, ClauseId, Solution};
use solver::types::SolutionValue::{self, True, False, Unassigned};
use solver::types::Term::{self, Lit, Not};

/**
 * Keeps track of which variables are watched by what clauses. 
 */
pub struct Watchlist {
	// keeps track of terms in each clause are being watched   
	watches: Vec<(Var, Var)>,

	// maps variables to the clauses they appear in
	clauses_watching:  HashMap<Var, Vec<ClauseId>>
}

impl Watchlist {
	pub fn new<I: Iterator<Item=Clause>>(clauses: I, sln: &Solution) -> Watchlist {
		let mut watchlist = Watchlist { 
			watches: Vec::new(), 
		    clauses_watching: HashMap::new()
		};
		for (i, ref clause) in clauses.enumerate() {
			watchlist.add_clause(i, clause, sln);
		}
		watchlist
	} 

	/**
	 * Adds a clause to the watchlist and indexes it.
	 */
	pub fn add_clause(&mut self, id: ClauseId, clause: &Clause, sln: &Solution) {
		let len = clause.len();
		let v1 = pick_watch(clause, sln, None).unwrap_or(0);
		let v2 = pick_watch(clause, sln, Some(v1)).unwrap_or(0);
		if self.watches.len() <= id {
			self.watches.resize(id+1, (0,0));
		}
		self.watches[id] = (v1, v2);

		if v1 != 0 { record_watch(&mut self.clauses_watching, v1, id) }
		if v2 != 0 { record_watch(&mut self.clauses_watching, v2, id) }
	}

	/**
	 * Scans the watchlist for clauses that would be made unit by assigning
	 * the supplied variable.
	 */
	pub fn scan(&mut self, v: Var, clause: &[Clause], sln: &Solution) -> Vec<ClauseId> {
		let mut result = Vec::new();
		// match self.clauses_watching.get(&v) {
		// 	Some(watch_clauses) => {
		// 		for c in watch_clauses {
		// 			let other_watch = 
		// 				match self.watches[c] {
		// 					(Some(v), other) => other,
		// 					(other, Some(v)) => other,
		// 					_ => { panic!("This should not happen"); None }
		// 				};

		// 			// decide our watches 
		// 			let new_watch_pair = 
		// 				match pick_watch(clauses[c], sln, other_watch) {
		// 					None => {
		// 						// oops, we're down one unassigned var. Leave the watched
		// 						result.push(c);
		// 					},
		// 					Some(v) => {
		// 						(other_watch, v)
		// 					}
		// 				}
		// 			}
		// 		}
		// 	}
		// }
		result
	}
}

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

/**
 * Picks a watch variable. The watch variable selected may not be assigned a 
 * value, nor be the same variable as an existing watch.
 */
fn pick_watch(clause: &Clause, sln: &Solution, other_watch: Option<Var>) -> Option<Var> {
	let other = other_watch.unwrap_or(0);
	for (idx, t) in clause.terms().iter().enumerate() {
		let i = idx as isize;
		let v = t.var();
		if v == other { continue }
		if sln[v] == Unassigned {
			return Some(v)
		}
	}
	None
}

#[test]
fn unconstrained_pick_watch_picks_a_var() {
	let clause = Clause::from(&[Lit(1), Lit(2), Lit(3)]);
	let sln = Solution::new(3);
	let var = pick_watch(&clause, &sln, None).unwrap();
	assert!(var >= 1);
	assert!(var <= 3);
	}

#[test]
fn pick_watch_doesnt_pick_an_existing_watch_variable() {
	let clause = Clause::from(&[Lit(1), Lit(2), Lit(3)]);
	let sln = Solution::new(3);
	assert!(pick_watch(&clause, &sln, Some(1)).unwrap() != 1);
	assert!(pick_watch(&clause, &sln, Some(2)).unwrap() != 2);
	assert!(pick_watch(&clause, &sln, Some(3)).unwrap() != 3);
}

#[test]
fn pick_watch_wont_pick_an_assigned_variable() {
	let clause = Clause::from(&[Lit(1), Lit(2), Lit(3)]);
	let sln = Solution::from(3, &[(1,True), (2,Unassigned), (3,True)]);
	assert_eq!(pick_watch(&clause, &sln, None).unwrap(), 2);
}

#[test]
fn pick_watch_returns_none_when_all_vars_are_assigned() {
	let clause = Clause::from(&[Lit(1), Lit(2), Lit(3)]);
	let sln = Solution::from(3, &[(1,True), (2,True), (3,True)]);
	assert_eq!(pick_watch(&clause, &sln, None), None);
}

#[test]
fn pick_watch_doesnt_barf_on_a_single_term_expression() {
	let clause = Clause::from(&[Lit(1)]);
	let sln = Solution::new(3);
	assert_eq!(pick_watch(&clause, &sln, None).unwrap(), 1);
	assert_eq!(pick_watch(&clause, &sln, Some(1)), None);
}

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

/**
 * Records a watch-variable-to-clause mapping
 */
fn record_watch(map: &mut HashMap<Var, Vec<usize>>, v: Var, clause_id: usize) {
	let mut add = false;
	match map.get_mut(&v) {
		Some (clauses) => clauses.push(clause_id),
		None => add = true
	}

	if add {
		map.insert(v, vec!(clause_id));
	}
}

#[test]
fn record_watch_on_new_var_adds_entry() {
	// asserts that adding a mapping on a previously-unmapped var succeeds
	let mut map = HashMap::new();
	record_watch(&mut map, 7, 42);
	assert!(map.get(&7).unwrap().as_slice() == [42]);
}

#[test]
fn record_watch_on_existing_var_adds_entry() {
	// asserts that adding a mapping on a previously-unmapped var succeeds
	let mut map = HashMap::new();
	map.insert(7, vec![1, 2, 3, 4]);
	record_watch(&mut map, 7, 42);
	let mut v = map.get(&7).unwrap().clone();
	v.sort();
	assert!(v.as_slice() == [1, 2, 3, 4, 42]);
}