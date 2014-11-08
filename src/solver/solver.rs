use std::collections::{TrieMap, TrieSet};
use std::collections::trie::{Entries, Keys};
use std::fmt;
use log;
use solver::types::{SolutionValue, True, False, Unassigned};
use solver::types::{Term, Lit, Not};
use solver::types::{Solution, Expression, Var};

type VarSet = TrieSet;

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

#[deriving(Show, PartialEq)]
struct ImplicationMap(TrieMap<SolutionValue>);

impl ImplicationMap {
    fn new() -> ImplicationMap {
        ImplicationMap(TrieMap::new())
    }

    fn value_of(&self, v: Var) -> SolutionValue {
        let ImplicationMap(ref me) = *self;
        match me.find(&v) {
            None => Unassigned,
            Some(rval) => *rval 
        }
    }

    fn add(&mut self, var: Var, val: SolutionValue) {
        let ImplicationMap(ref mut me) = *self;
        me.insert(var, val);
    }

    fn is_empty(&self) -> bool {
        let ImplicationMap(ref me) = *self;
        me.is_empty()
    }

    fn iter<'a>(&'a self) -> Entries<'a, SolutionValue> {
        let ImplicationMap(ref me) = *self;
        me.iter()   
    }

    fn vars<'a>(&'a self) -> Keys<'a, SolutionValue> {
        let ImplicationMap(ref me) = *self;
        me.keys()
    }
}

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

/**
 * Chooses the next variable to assign from the set.
 */
fn pick_var(vars: &VarSet) -> uint {
    vars.iter().next().unwrap()
}

fn scan_unassigned_vars(varcount: uint, sln: &Solution) -> VarSet {
    let mut result = TrieSet::new();
    for v in range(1, varcount+1) {
        if !sln.is_assigned(v) { result.insert(v); }
    }
    result
}

fn next_val(v: SolutionValue) -> SolutionValue {
    match v { 
        Unassigned => False, 
        False => True, 
        _ => fail!("next_val was called with True") 
    }
}

#[test]
fn nextval_progresses_correctly() {
    assert!(next_val(Unassigned) == False);
    assert!(next_val(False) == True);      
}

#[test] 
#[should_fail]
fn nextval_fails_on_overrun() {
    next_val(True);
}

// ----------------------------------------------------------------------------
// Solve state tracking
// ----------------------------------------------------------------------------

#[deriving(Show)]
struct Decision {
    var: uint,
    value: SolutionValue,
    implications: Vec<Var>
}

struct DecisionStack {
    stack: Vec<Decision>
}

impl DecisionStack {
    fn new() -> DecisionStack { 
        DecisionStack { stack: Vec::new() } 
    }

    // fn new_with_unassigned(var: Var) -> DecisionStack {
    //     let mut s = DecisionStack::new();
    //     s.push_unassigned(var);
    //     s
    // }

    fn push(&mut self, 
            var: Var, 
            value: SolutionValue) {
        self.stack.push( Decision {
            var: var, 
            value: value, 
            implications: Vec::new()
        });
    }

    fn peek(&self) -> Option<&Decision> {
        self.stack.last()
    }

    fn mut_peek(&mut self) -> Option<&mut Decision> {
        self.stack.mut_last()
    }

    fn pop(&mut self) -> Option<Decision> {
        self.stack.pop()
    }
}

impl Collection for DecisionStack {
    fn len(&self) -> uint { self.stack.len() }
    fn is_empty(&self) -> bool { self.stack.is_empty() }
}

impl Index<uint, Decision> for DecisionStack {
    fn index<'a>(&'a self, index: &uint) -> &Decision {
        &self.stack[*index]
    }
}

impl fmt::Show for DecisionStack {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (i, s) in self.stack.iter().enumerate() {
            try!(write!(f, "{}: {}", i, s))
        }
        Ok(())
    }
}

// ----------------------------------------------------------------------------
// Implication graph implementation
// ----------------------------------------------------------------------------

struct ImplicationGraph {
    map: TrieMap<TrieSet>
}

impl ImplicationGraph {
    fn new() -> ImplicationGraph {
        ImplicationGraph { map: TrieMap::new() }
    }

    fn from(items: &[(Var, &[Var])]) -> ImplicationGraph {
        let mut g = ImplicationGraph::new();
        for &(var, roots) in items.iter() {
            for r in roots.iter() {
                g.add(var, *r);
            }
        }
        g
    }

    fn add(&mut self, v: Var, root: Var) {
        let mut insert_new = false;
        match self.map.find_mut(&v) {
            Some (s) => { s.insert(root); },
            None => { insert_new = true; }
        }

        if insert_new {
            let mut s = TrieSet::new();
            s.insert(root);
            self.map.insert(v, s);
        }       
    }

    fn erase(&mut self, v: Var) {
        self.map.remove(&v);
    }

    fn add_from_clause(&mut self, v: Var, clause: &[Term]) {
        for t in clause.iter() {
            let root = t.var();
            if root != v { self.add(v, root); }
        }
    }

    fn get_roots(&self, v: Var) -> Vec<Var> {
        match self.map.find(&v) {
            Some (s) => s.iter().collect(),
            None => Vec::new()
        }
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

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

fn learn_conflict_clause(v: Var, sln: &Solution, g: &ImplicationGraph) -> Vec<Term> {
    let mut clause = Vec::new();
    for r in g.get_roots(v).iter() {
        let term = match sln[*r] {
            True => Not(*r),
            False => Lit(*r),
            Unassigned => { fail!("This should never happen"); Lit(0) }
        };
        clause.push(term)
    }
    clause
}

#[config(test)]
fn mk_graph_test_exp() -> Expression {
    Expression::from(&[
        &[Lit(1), Lit(4)],
        &[Lit(1), Not(3), Not(8)],
        &[Lit(1), Lit(8), Lit(12)],
        &[Lit(2), Lit(11)],
        &[Not(7), Not(3), Lit(9)],
        &[Not(7), Lit(8), Not(9)],
        &[Lit(7), Lit(8), Not(10)],
        &[Lit(7), Lit(10), Not(12)] 
    ])
}

#[test]
fn learn_clause_finds_expected_clause() {
    let exp = mk_graph_test_exp();
    let sln = Solution::from(12, &[
        (1, False), (2, False), (3, True), (7, True), (8, False), (12, True)
    ]);

    let g = ImplicationGraph::from(&[
        ( 4, &[1]),
        ( 8, &[1]),
        ( 9, &[3, 7, 8]),
        (11, &[2]),
        (12, &[1, 8])
    ]);

    let clause = learn_conflict_clause(9, &sln, &g);
    assert!(clause.len() == 3)
    assert!(clause.iter().any(|t| *t == Not(3)), "Clause must contain ~3");
    assert!(clause.iter().any(|t| *t == Not(7)), "Clause must contain ~7");
    assert!(clause.iter().any(|t| *t == Lit(8)), "Clause must contain 8");
}

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

fn undo_decision(d: &Decision, sln: &mut Solution, vars: &mut VarSet) {
    for k in d.implications.iter() {
        sln.unset(*k);
        vars.insert(*k);
    }
}

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------


fn try_assignment(var: Var, val: SolutionValue, 
                  unassigned_vars: &mut VarSet,
                  exp: &Expression, 
                  sln: &mut Solution) -> PropagationResult {

    debug!("\tAttempting to set {} = {}", var, val);

    sln.set(var, val);
    unassigned_vars.remove(&var);

    match propagate(sln, var, val, exp) {
        // Yay - the assignment of var = val was valid. Time to update the 
        // bookkeeping. 
        Success (implications) => {
            // remove all variables that we assigned values to in this pass 
            // from the unassigned variables set.
            for k in implications.iter() {
                unassigned_vars.remove(k);
            }

            Success (implications)
        },

        // Any sort of failure - get set up for the next pass by pushing a copy of our 
        // original state with an updated value to try  
        rval @ _ => {
            debug!("Assignment failed.");
            sln.set(var, Unassigned);
            unassigned_vars.insert(var);
            rval
        }
    }
}

#[test]
fn trying_valid_assignment_on_new_var_succeeds() {
    let exp = Expression::from(&[
        &[Lit(2), Lit(3), Lit(4)],
        &[Not(1)],
        &[Lit(5), Lit(6)],
        &[Lit(2), Not(6)]
    ]);
    let mut vars : TrieSet = FromIterator::from_iter(
        range(1,6).filter(|x| *x != 5));
    let mut sln = Solution::new(6);

    assert!(try_assignment(5, False, &mut vars, &exp, &mut sln).is_success());
    assert!(sln[5] == False);
    assert!(!vars.contains(&5));
}

#[test]
fn trying_invalid_assignment_on_new_var_fails() {
    let exp = Expression::from(&[
        &[Lit(2), Lit(3), Lit(4)],
        &[Lit(1)],
        &[Lit(5), Lit(6)],
        &[Lit(2), Not(6)]
    ]);

    let mut vars : TrieSet = FromIterator::from_iter(range(1, 6));
    let expected_vars = vars.clone();
    let mut sln = Solution::new(6);

    assert!(try_assignment(1, False, &mut vars, &exp, &mut sln).is_failure());
    assert!(sln[1] == Unassigned);
    assert!(vars == expected_vars, "Got {}", vars);
}

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

enum SolverMove { Continue, Backtrack, Retry }

/**
 * The main solver routine. Horribly side-effecting, but only internally.
 */
pub fn solve(e: &Expression, 
             varcount: uint, 
             initial_sln: Solution) -> Option<Solution> {
    let mut unassigned_vars = scan_unassigned_vars(varcount, &initial_sln);
    let mut stack = DecisionStack::new();
    let mut sln = initial_sln.clone(); 
    let mut next_move = Continue;

    while !unassigned_vars.is_empty() {
        let (var, val) = match next_move {
            Continue => (pick_var(&mut unassigned_vars), False),
            Backtrack => {
                debug!("Attempting to backtrack");
                match stack.pop() {
                    None => {
                        debug!("No solution found");
                        return None
                    },
                    Some (d) =>  {
                        undo_decision(&d, &mut sln, &mut unassigned_vars);
                        if d.value == True { continue; };
                        next_move = Continue;
                        (d.var, next_val(d.value))
                    }
                }
            },
            Retry => { fail!("Shouldn't happen yet"); (0u, Unassigned) }
        };
    
        debug!("Stack depth: {}", stack.len());
        stack.push(var, val);

        match try_assignment(var, val, &mut unassigned_vars, e, &mut sln) {
            Success (implications) => {
                stack.mut_peek().unwrap().implications = implications;
                next_move = Continue;
            },
            EvaluatesToFalse | Contradiction (_) => {
                next_move = Backtrack;
            }
        }
    }

    Some(sln)
}

#[test]
fn solver_completes() {
    let exp = Expression::from(&[
        &[Lit(1), Lit(2), Lit(3), Lit(4)],
        &[Lit(1), Not(7)],
        &[Lit(3)],
        &[Not(2), Not(3)],
        &[Not(3), Lit(2), Lit(1)],
        &[Not(1), Lit(3)], 
        &[Not(2), Lit(7)],
        &[Not(4)],
    ]);

    match solve(&exp, 7, Solution::new(7)) {
        None => { fail!("Expression should be valid"); }
        Some(sln) => {
            debug!("Solution: {}", sln);

            assert!(range(1u, 8u).all(|x| sln[x] != Unassigned));
            assert!(exp.apply(&sln) == True);
            assert!(sln[1] == True); // this at least must be true

            match sln.get(2) {
                False => { 
                    assert!(sln[6] == False, "If 2 is false then 5 *must* be true");
                    assert!((sln[3] | sln[4]) == True, "If 2 is false then 3 | 4 *must* be true");
                }
                _ => {}
            }
        }
    }
}

#[test]
fn solver_detects_basic_contradiction() {
    let exp = Expression::from(&[
        &[Lit(1), Lit(2), Lit(3), Lit(4)],
        &[Lit(3)],
        &[Not(3)],
        &[Not(2), Not(3)],
        &[Not(3), Lit(2), Lit(1)],
        &[Not(1), Lit(3)], 
        &[Not(2), Lit(7)],
        &[Not(4)],
    ]);

    match solve(&exp, 7, Solution::new(7)) {
        None => { }
        Some(_) => { 
            fail!("Expression contains a contradiction, so shouldn't succeed.")
        }
    }
}

#[deriving(PartialEq, Eq, Show)]
enum ClauseAnalysis {
    IsTrue, IsFalse, IsUnit (Term), IsIndeterminate
}

fn analyse_clause(clause: &[Term], sln: &Solution) -> ClauseAnalysis {
    let mut value = False;
    let mut unassigned_terms = Vec::with_capacity(clause.len());

    // walk each term in the Clause and try to evaluate it.
    for term in clause.iter() {
        let t = term.value(sln);
        value = value | t;

        if t == Unassigned {
            unassigned_terms.push(term);
        }

        if value == True {
            break;
        }
    }

    match value {
        True => IsTrue,
        False => IsFalse,
        Unassigned => {
            assert!(unassigned_terms.len() > 0);

            if unassigned_terms.len() == 1 {
                IsUnit(*unassigned_terms[0])
            }
            else {
                IsIndeterminate
            }
        }
    }
}

#[test]
fn analysis_detects_single_term_unit_clause() {
    let sln = Solution::new(4);
    let rval = analyse_clause(&[Lit(1)], &sln);
    assert!(rval == IsUnit(Lit(1)));
}

#[test]
fn analysis_detects_unit_clause() {
    let sln = Solution::from(4, &[(1, False), (2, False), (4, False)]);
    let rval = analyse_clause(&[Lit(1), Lit(2), Lit(3), Lit(4)], &sln);
    assert!(rval == IsUnit(Lit(3)));
}

#[test]
fn analysis_detects_true_clause() {
    let sln = Solution::from(4, &[(3, True)]);
    let rval = analyse_clause(&[Lit(1), Lit(2), Lit(3), Lit(4)], &sln);
    assert!(rval == IsTrue);
}

#[test]
fn analysis_detects_false_clause() {
    let sln = Solution::from(4, &[(2, False), (3, False)]);
    let rval = analyse_clause(&[Lit(2), Lit(3)], &sln);
    assert!(rval == IsFalse);
}


#[test]
fn analysis_detects_indeterminate_clause() {
    let sln = Solution::from(4, &[(2, False), (3, False)]);
    let rval = analyse_clause(&[Lit(1), Lit(2), Lit(3), Lit(4)], &sln);
    assert!(rval == IsIndeterminate);
}

#[deriving(Show)]
enum PropagationResult {
    EvaluatesToFalse,

    /**
     * 
     */
    Contradiction (uint),

    /**
     * (implications) where
     *
     *   implications - A vector containing the variables set by the propagation
     */
    Success (Vec<Var>)
}

impl PropagationResult {
    fn is_success(&self) -> bool {
        match *self {
            Success (_) => true,
            _ => false
        }
    }

    fn is_failure(&self) -> bool {
        !self.is_success()
    }
}

/**
 *
 */
fn propagate(sln: &mut Solution, seed_var: Var, seed_val: SolutionValue, e: &Expression) -> PropagationResult {
    let mut implications = ImplicationMap::new();
    let mut queue : Vec<(Var, SolutionValue)> = Vec::new();
    queue.push((seed_var, seed_val));
    implications.add(seed_var, seed_val);

    while !queue.is_empty() {
        let (var, val) = queue.pop().unwrap();

        debug!("\tChecking implications of setting {} = {}", var, val)

        sln.set(var, val);

        for clause in e.clauses_containing(var) {
            match analyse_clause(clause, sln) {
                IsUnit (term) => {
                    debug!("\t\tFound unit clause {}, term of interest is {}", clause, term)
                    let v = term.var();

                    // deduce value
                    let deduced_value = match term {
                        Lit (_) => True,
                        Not (_) => False
                    };

                    debug!("\t\tDeduced that {} = {}", v, deduced_value);

                    // check for a contradiction - have we aleady deduced that 
                    // this variable must have a different value?
                    debug!("\t\tExisting implication for {} is {}", v, implications.value_of(v));
                    match implications.value_of(v) {
                        Unassigned => { 
                            queue.push((v, deduced_value));
                            implications.add(v, deduced_value);
                        },

                        x if x != deduced_value => { 
                            debug!("\t\tDetected contradiction on {}!", v);
                            sln.unset_all(implications.vars());
                            return Contradiction(v) 
                        },

                        _ => { /* value is consistent, all is well */ }
                    }
                },

                IsTrue => { 
                    debug!("\t\tClause {} is TRUE", clause);
                },

                IsFalse => {
                    // oh, dear. All variables in the term have values and the
                    // clause evaluates to false. Bail out and let the caller 
                    // know that this can't possibly be the right answer.
                    debug!("\t\tClause {} evaluates to false. Ooops.", clause); 
                    sln.unset_all(implications.vars());
                    return EvaluatesToFalse
                },

                IsIndeterminate => { 
                    debug!("\t\tClause {} is still indeterminate", clause);
                }
            }
        }
    }

    Success (implications.vars().collect())
}

#[test]
fn propagation_deduces_true_value() {
    let exp = Expression::from(&[&[Lit(1), Lit(2), Lit(3), Lit(4)]]);
    let mut sln = Solution::from(4, &[(1, False), (2, False)]);
    match propagate(&mut sln, 4, False, &exp) {
        Success (mut implications) => {
            implications.sort();
            assert!(implications.as_slice() == &[3u, 4u], 
                    "Expected [3, 4], got {}", implications);
        },
        other => {
            fail!("Unexpected propagation result: {}", other)
        }
    }
}

#[test]
fn propagation_deduces_false_value() {
    let exp = Expression::from(&[&[Lit(1), Lit(2), Not(3), Lit(4)]]);
    let mut sln = Solution::from(4, &[(1, False), (2, False)]);
    match propagate(&mut sln, 4, False, &exp) {
        Success (mut implications) => {
            implications.sort();
            assert!(implications.as_slice() == &[3u, 4u], 
                    "Expected [3, 4], got {}", implications);
        },
        other => {
            fail!("Unexpected propagation result: {}", other)
        }
    }
}

#[test]
fn propagation_detects_contradictions() {
    let exp = Expression::from(&[
        &[Lit(1), Lit(2), Lit(3)],
        &[Lit(1), Lit(2), Not(3)],
    ]);

    let mut sln = Solution::from(3, &[(1, False)]);
    
    match propagate(&mut sln, 2, False, &exp) {
        Contradiction (n) => assert!(n == 3, "Expected a contractiction of variable #3"),
        other => fail!("Unexpected result from propagate(): {}", other)
    }

    assert!(sln[1] == False, "Expected False, got {}", sln[1]);
    assert!(sln[2] == Unassigned, "Expected Unassigned, got {}", sln[2]);
    assert!(sln[3] == Unassigned, "Expected Unassigned, got {}", sln[3]);
}

#[test]
fn propagation_detects_evaluation_to_false() {
    let exp = Expression::from(&[
        &[Lit(1), Lit(2), Lit(3)],
        &[Lit(1), Lit(2), Not(4)],
    ]);

    let mut sln = Solution::from(4, &[(1, False), (2, False)]);

    match propagate(&mut sln, 3, False, &exp) {
        EvaluatesToFalse => {},
        other => fail!("Unexpected result from propagate(): {}", other)
    }
}
