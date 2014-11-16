use std::collections::{TrieMap, TrieSet};
use std::collections::trie::{Entries, Keys};
use std::iter::{range_step};
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

impl Collection for ImplicationGraph {
    fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    fn len(&self) -> uint {
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

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

fn learn_conflict_clause(v: Var, sln: &Solution, g: &ImplicationGraph) -> Vec<Term> {
    let mut clause = Vec::new();
    for r in g.get_roots(v).iter() {
        let term = match sln[*r] {
            True => Not(*r),
            False => Lit(*r),
            Unassigned => {
                let all_roots : Vec<uint> = g.get_roots(v); 
                fail!("This should never happen (r: {}, all: {})", r, all_roots); Lit(0) }
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


fn try_assignment(var: Var, 
                  val: SolutionValue, 
                  state: &mut SolveState,
                  exp: &Expression) -> PropagationResult {

    debug!("\tAttempting to set {} = {}", var, val);

    let sln = &mut state.solution;
    let vars = &mut state.unassigned_vars;
    let g = &mut state.implications;
    
    sln.set(var, val);
    vars.remove(&var);

    debug!("Solution: {}", sln);
    debug!("Unset Vars: {}", vars);

    match propagate(sln, var, val, exp, g) {
        // Yay - the assignment of var = val was valid. Time to update the 
        // bookkeeping. 
        Success (implications) => {
            // remove all variables that we assigned values to in this pass 
            // from the unassigned variables set.
            for k in implications.iter() { vars.remove(k); }
            Success (implications)
        },

        // Any sort of failure - get set up for the next pass by pushing a copy of our 
        // original state with an updated value to try  
        rval @ _ => {
            debug!("Assignment failed.");
            sln.unset(var);
            vars.insert(var);
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
    let mut state = SolveState { 
        unassigned_vars: FromIterator::from_iter(range(1,6).filter(|x| *x != 5)),
        solution: Solution::new(6),
        implications: ImplicationGraph::new(),
        stack: DecisionStack::new()
    };

    assert!(try_assignment(5, False, &mut state, &exp).is_success());
    assert!(state.solution[5] == False);
    assert!(!state.unassigned_vars.contains(&5));
}

#[test]
fn trying_invalid_assignment_on_new_var_fails() {
    let exp = Expression::from(&[
        &[Lit(2), Lit(3), Lit(4)],
        &[Lit(1)],
        &[Lit(5), Lit(6)],
        &[Lit(2), Not(6)]
    ]);

    let mut state = SolveState::new(6);
    let expected_vars = state.unassigned_vars.clone();

    assert!(try_assignment(1, False, &mut state, &exp).is_failure());
    assert!(state.solution[1] == Unassigned);
    assert!(state.unassigned_vars == expected_vars,
            "Got {}", state.unassigned_vars);
}

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

enum SolverMove { Continue, Backtrack, Retry (Var, SolutionValue) }

struct SolveState {
    unassigned_vars: VarSet,
    implications: ImplicationGraph,
    solution: Solution,
    stack: DecisionStack
}

impl SolveState {
    fn new(varcount: uint) -> SolveState {
        SolveState {
            unassigned_vars: FromIterator::from_iter(range(1, varcount+1)),
            implications: ImplicationGraph::new(),
            solution: Solution::new(varcount),
            stack: DecisionStack::new()
        }
    }

    fn has_unassigned_vars(&self) -> bool {
        !self.unassigned_vars.is_empty()
    }

    fn undo_decision(&mut self, d: &Decision) {
        debug!("Undoing {} = {}, ", d.var, d.value);
        for k in d.implications.iter() {
            debug!("Unsetting {}", k);
            self.solution.unset(*k);
            self.unassigned_vars.insert(*k);
            self.implications.erase(*k);
        }
    }

    /**
     * Unwinds the state stack until all decisions affecting the variables in
     * the supplied set have been undone. Fails hard if the unwinding tries to 
     * go past the end of the stack.
     */
    fn unwind(&mut self, mut vars: VarSet) -> (Var, SolutionValue) {
        debug!("Unwinding for: {}", vars);
        loop {
            match self.pop() {
                None => fail!("Attempting to unwind an empty stack"),
                Some(d) => {
                    debug!("Implications of {} = {}: {}", d.var, d.value, d.implications);
                    self.undo_decision(&d);
                    for v in d.implications.iter() {
                        vars.remove(v);
                    }
                    if vars.is_empty() {
                        return (d.var, d.value)
                    }
                }
            }
        }
    }

    fn push(&mut self, var: Var, val: SolutionValue) {
        self.stack.push(var, val)
    }

    fn pop(&mut self) -> Option<Decision> {
        self.stack.pop()
    }

    fn mut_peek(&mut self) -> Option<&mut Decision> {
        self.stack.mut_peek()
    }
}

#[test]
fn stack_unwound_to_expected_point() {
    let mut state = SolveState {
        unassigned_vars: TrieSet::new(),
        implications: ImplicationGraph::new(),
        solution: Solution::new(10),
        stack: DecisionStack::new()
    };

    for x in range_step(1, 11, 2) {
        state.push(x, True);
        state.mut_peek().unwrap().implications = vec![x, x+1];
        state.solution.set(x, True);
        state.solution.set(x+1, False);
        state.implications.add(x+1, x);
    }

    let missing_vars : TrieSet = FromIterator::from_iter(
        [10u, 5u, 8u].iter().map(|x| *x));

    let (var, val) = state.unwind(missing_vars);
    assert!(var == 5);
    assert!(val == True);

    assert!(state.stack.len() == 2);
    
    let expected_vars : VarSet = FromIterator::from_iter(range(5u, 11u));
    assert!(state.unassigned_vars == expected_vars, 
            "Expected {}, got {}", expected_vars, state.unassigned_vars);

    assert!(range(1, 5).all(|n| state.solution[n] != Unassigned));
    assert!(range(5, 11).all(|n| state.solution[n] == Unassigned));
    assert!(range(5, 11).all(|n| state.implications.get_roots(n) == vec![]));

    assert!(state.stack.len() == 2);
}

/**
 * The main solver routine. Horribly side-effecting, but only internally.
 */
pub fn solve(exp: &Expression, 
             varcount: uint, 
             initial_sln: Solution) -> Option<Solution> {
    let mut state = SolveState::new(varcount);
    let mut next_move = Continue;
    let mut e = exp.clone();

    while state.has_unassigned_vars() {
        let (var, val) = match next_move {
            Continue => (pick_var(&mut state.unassigned_vars), False),
            Backtrack => {
                debug!("Attempting to backtrack");
                match state.pop() {
                    None => {
                        debug!("No solution found");
                        return None
                    },
                    Some (d) =>  {
                        state.undo_decision(&d);
                        if d.value == True { continue; };
                        (d.var, next_val(d.value))
                    }
                }
            },
            Retry (x, v) => (x, v) 
        };
    
        debug!("Stack depth: {}", state.stack.len());
        state.push(var, val);

        match try_assignment(var, val, &mut state, &e) {
            Success (implications) => {
                match state.mut_peek() {
                    Some(d) => d.implications = implications,
                    None => fail!("Empty decision stack")
                }
                next_move = Continue;
            },

            Contradiction (new_clauses, missing_vars) => {
                for c in new_clauses.iter() {
                    e.add(c.as_slice());
                }
                let (var_p, val_p) = state.unwind(missing_vars);
                next_move = Retry(var_p, val_p);
            },

            EvaluatesToFalse => {
                next_move = Backtrack;
            }
        }
    }

    Some(state.solution)
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

            println!("+++ {}, {}", sln, range(1u, 8u).all(|x| {
                println!(">>> sln[{}] == {} (!= Unassigned? {}) ",
                         x, sln[x], sln[x] != Unassigned); 
                sln[x] != Unassigned
            }));

            assert!(range(1u, 8u).all(|x| sln[x] != Unassigned), 
                    "Expected all values to be assigned, got {} instead", 
                    sln);

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
     * Contradiction detected during propagation. Returns both the conflict 
     * expression and the variables that need to be reset before a retry can 
     * occur. (We need the reamaining ones returned as some of the terms in 
     * the conflict expression may have already been reset by cleanup code in 
     * the propagation routine.)
     */
    Contradiction (Vec<Vec<Term>>, VarSet),

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
fn propagate(sln: &mut Solution, 
             seed_var: Var, 
             seed_val: SolutionValue, 
             e: &Expression,
             g: &mut ImplicationGraph) -> PropagationResult {

    let mut implications = ImplicationMap::new();
    let mut queue : Vec<(Var, SolutionValue)> = Vec::new();
    let mut conflicts = TrieSet::new();
    let mut conflict_clauses : Vec<Vec<Term>> = Vec::new(); 
    let mut clause_vars = TrieSet::new();

    queue.push((seed_var, seed_val));
    implications.add(seed_var, seed_val);

    while !queue.is_empty() {
        let (var, val) = queue.pop().unwrap();
        if conflicts.contains(&var) {
            continue;
        }

        debug!("\tChecking implications of setting {} = {}", var, val)

        sln.set(var, val);

        for clause in e.clauses_containing(var) {
            match analyse_clause(clause, sln) {
                IsUnit (term) => {
                    debug!("\t\tFound unit clause {}, term of interest is {}", clause, term)
                    let v = term.var();

                    if conflicts.contains(&v) {
                        continue;
                    }

                    // deduce value
                    let deduced_value = match term {
                        Lit (_) => True,
                        Not (_) => False
                    };

                    debug!("\t\tDeduced that {} = {}", v, deduced_value);
                    g.add_from_clause(v, clause);

                    // check for a contradiction - have we aleady deduced that 
                    // this variable must have a different value?
                    debug!("\t\tExisting implication for {} is {} (Unassigned -> None)", 
                           v, implications.value_of(v));

                    match implications.value_of(v) {
                        Unassigned => { 
                            queue.push((v, deduced_value));
                            implications.add(v, deduced_value);
                        },

                        x if x != deduced_value => { 
                            debug!("\t\tDetected contradiction on {}!", v);

                            let conflict_clause = learn_conflict_clause(v, sln, g);
                            debug!("\t\tLearned {}", conflict_clause);
                            
                            sln.unset(v);

                            clause_vars.extend(
                                conflict_clause.iter().map(|t| t.var()));
                            conflict_clauses.push(conflict_clause);
                            conflicts.insert(v);
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
                    for v in implications.vars() {
                        sln.unset(v);
                        g.erase(v);
                    }
                    return EvaluatesToFalse
                },

                IsIndeterminate => { 
                    debug!("\t\tClause {} is still indeterminate", clause);
                }
            }
        }
    }

    if conflict_clauses.is_empty() {
        Success (implications.vars().collect())
    }
    else {
        for v in implications.vars() {
            sln.unset(v);
            g.erase(v);
            clause_vars.remove(&v);
        }
        Contradiction(conflict_clauses, clause_vars)
    }
}

#[test]
fn propagation_deduces_true_value() {
    let exp = Expression::from(&[&[Lit(1), Lit(2), Lit(3), Lit(4)]]);
    let mut sln = Solution::from(4, &[(1, False), (2, False)]);
    let mut g = ImplicationGraph::new();
    match propagate(&mut sln, 4, False, &exp, &mut g) {
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
    let mut g = ImplicationGraph::new();
    match propagate(&mut sln, 4, False, &exp, &mut g) {
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
    let mut g = ImplicationGraph::new();
    
    match propagate(&mut sln, 2, False, &exp, &mut g) {
        Contradiction (mut c, mut vs) => {
            c.sort();
            assert!(c.as_slice() == &[vec![Lit(1), Lit(2)]], 
                    "Expected a conflic clause like [1, 2], got {}", 
                    c);
        },
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
    let mut g = ImplicationGraph::new();

    match propagate(&mut sln, 3, False, &exp, &mut g) {
        EvaluatesToFalse => {},
        other => fail!("Unexpected result from propagate(): {}", other)
    }

    assert!(g.is_empty());
}
