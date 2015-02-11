use std::collections::{HashMap, HashSet, BTreeSet};
use std::collections::hash_map::{Keys, Values, Iter};
use std::iter::{FromIterator, range_step};
use std::ops::{Index, IndexMut};
use std::fmt;
use log;

use solver::types::{Solution, SolutionValue, Expression, Var, VarSet, Clause, Term};
use solver::types::SolutionValue::{Unassigned, True, False};
use solver::types::Term::{Lit, Not};
use solver::implication_graph::{ImplicationGraph, dump_graph};

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

#[derive(Show, PartialEq)]
struct ImplicationMap(HashMap<Var, SolutionValue>);

impl ImplicationMap {
    fn new() -> ImplicationMap {
        ImplicationMap(HashMap::new())
    }

    fn value_of(&self, v: Var) -> SolutionValue {
        let ImplicationMap(ref me) = *self;
        match me.get(&v) {
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

    fn iter<'a>(&'a self) -> Iter<'a, Var, SolutionValue> {
        let ImplicationMap(ref me) = *self;
        me.iter()   
    }

    fn vars<'a>(&'a self) -> Keys<'a, Var, SolutionValue> {
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
fn pick_var(vars: &VarSet) -> Var {
    *vars.iter().next().unwrap()
}

fn scan_unassigned_vars(varcount: usize, sln: &Solution) -> VarSet {
    let mut result = VarSet::new();
    for v in range(1, varcount+1) {
        if !sln.is_assigned(v) { result.insert(v); }
    }
    result
}

fn next_val(v: SolutionValue) -> SolutionValue {
    match v { 
        Unassigned => False, 
        False => True, 
        _ => panic!("next_val was called with True") 
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

#[derive(Show)]
struct Decision {
    var: Var,
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
        match self.stack.len() {
            0 => None,
            n => Some(&mut self.stack[n-1])
        }
    }

    fn pop(&mut self) -> Option<Decision> {
        self.stack.pop()
    }

    fn len(&self) -> usize { self.stack.len() }
    fn is_empty(&self) -> bool { self.stack.is_empty() }
}

impl Index<usize> for DecisionStack {
    type Output = Decision;
    fn index<'a>(&'a self, index: &usize) -> &'a Decision {
        &self.stack[*index]
    }
}

impl fmt::Show for DecisionStack {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (i, s) in self.stack.iter().enumerate() {
            try!(write!(f, "{:?}: {:?}", i, s))
        }
        Ok(())
    }
}

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

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


// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------


fn try_assignment(var: Var, 
                  val: SolutionValue, 
                  state: &mut SolveState,
                  exp: &Expression) -> PropagationResult {

    debug!("\tAttempting to set {:?} = {:?}", var, val);

    let sln = &mut state.solution;
    let vars = &mut state.unassigned_vars;
    let g = &mut state.implications;
    
    sln.set(var, val);
    vars.remove(&var);

//    debug!("Solution: {:?}", sln);
//    debug!("Unset Vars: {:?}", vars);

    match propagate(sln, state.stack.len()+1, var, val, exp, g) {
        // Yay - the assignment of var = val was valid. Time to update the 
        // bookkeeping. 
        PropagationResult::Success (implications) => {
            // remove all variables that we assigned values to in this pass 
            // from the unassigned variables set.
            for k in implications.iter() { vars.remove(k); }
            PropagationResult::Success (implications)
        },

        // Any sort of failure - get set up for the next pass by pushing a copy of our 
        // original state with an updated value to try  
        rval @ _ => {
            debug!("Assignment failed: {:?}. Cleaning up.", rval);
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
            "Got {:?}", state.unassigned_vars);
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
    fn new(varcount: usize) -> SolveState {
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
        debug!("Undoing {:?} = {:?}, ", d.var, d.value);
        for k in d.implications.iter() {
            debug!("Unsetting {:?}", k);
            let k_val = self.solution[*k];
            self.solution.unset(*k);
            self.unassigned_vars.insert(*k);
            self.implications.remove(*k, k_val);
        }
    }

    /**
     * Unwinds the state stack until all decisions affecting the variables in
     * the supplied set have been undone. Fails hard if the unwinding tries to 
     * go past the end of the stack.
     */
    fn unwind(&mut self, mut vars: VarSet) -> (Var, SolutionValue) {
        debug!("Unwinding for: {:?}", vars);
        loop {
            match self.pop() {
                None => panic!("Attempting to unwind an empty stack"),
                Some(d) => {
                    debug!("Implications of {:?} = {:?}: {:?}", d.var, d.value, d.implications);
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
    use solver::implication_graph;

    let mut state = SolveState {
        unassigned_vars: VarSet::new(),
        implications: ImplicationGraph::new(),
        solution: Solution::new(10),
        stack: DecisionStack::new()
    };

    // Create a 
    for (level, x) in range_step(1, 11, 2).enumerate() {
        state.push(x, True);
        state.mut_peek().unwrap().implications = vec![x, x+1];
        state.solution.set(x, True);
        state.solution.set(x+1, False);
        state.implications.insert(level, x, True, &[]);
        state.implications.insert(level, x+1, False, &[(x,True)]);
    }

//    implication_graph::dump_graph("stack_unwind.dot", &state.implications);

    // roll back the decision stack such that all of the supplied variables 
    // are unset.
    let missing_vars : VarSet = FromIterator::from_iter(
        [10us, 5us, 8us].iter().map(|x| *x));

    // check that the unwind returns the last decision variable it unset 
    // during the rollback
    let (var, val) = state.unwind(missing_vars);
    assert!(var == 5);
    assert!(val == True);

    // Check that the decision stack is now the size we expect from a 
    // post-rollback stack
    assert!(state.stack.len() == 2);
    
    // assert that all variables prior to the rollback point are still 
    // assigned 
    assert!(range(1, 5).all(|n| state.solution[n] != Unassigned));

    // assert that all variables after the rollback point have been unassigned 
    // and their implications have been deleted
    assert!(range(5, 11).all(|n| state.solution[n] == Unassigned));
    assert!(range(5, 11).all(|n| !state.implications.has(n)));

    assert!(4 == state.implications.len(), 
        "Expected a 4-element implication graph, got {:?}", 
        state.implications.len());
}

/**
 * The main solver routine. Horribly side-effecting, but only internally.
 */
pub fn solve(exp: &Expression, 
             varcount: usize, 
             initial_sln: Solution) -> Option<Solution> {
    let mut state = SolveState::new(varcount);
    let mut next_move = SolverMove::Continue;
    let mut e = exp.clone();

    while state.has_unassigned_vars() {
        let (var, val) = match next_move {
            SolverMove::Continue => (pick_var(&mut state.unassigned_vars), False),
            SolverMove::Backtrack => {
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
            SolverMove::Retry (x, v) => (x, v) 
        };
    
        debug!("Stack depth: {:?}", state.stack.len());
        state.push(var, val);

        match try_assignment(var, val, &mut state, &e) {
            PropagationResult::Success (implications) => {
                match state.mut_peek() {
                    Some(d) => d.implications = implications,
                    None => panic!("Empty decision stack")
                }
                next_move = SolverMove::Continue;
            },

            PropagationResult::Contradiction (new_clauses, missing_vars) => {
                for c in new_clauses.iter().map(|x| x.clone()) {
                    e.add_clause(c);
                }
                let (var_p, val_p) = state.unwind(missing_vars);
                next_move = SolverMove::Retry(var_p, val_p);
            },

            PropagationResult::EvaluatesToFalse => {
                next_move = SolverMove::Backtrack;
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
        None => { panic!("Expression should be valid"); }
        Some(sln) => {
            debug!("Solution: {:?}", sln);

            println!("+++ {:?}, {:?}", sln, range(1us, 8us).all(|x| {
                println!(">>> sln[{:?}] == {:?} (!= Unassigned? {:?}) ",
                         x, sln[x], sln[x] != Unassigned); 
                sln[x] != Unassigned
            }));

            assert!(range(1us, 8us).all(|x| sln[x] != Unassigned), 
                    "Expected all values to be assigned, got {:?} instead", 
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
            panic!("Expression contains a contradiction, so shouldn't succeed.")
        }
    }
}

#[derive(PartialEq, Eq, Show, Clone)]
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
        True => ClauseAnalysis::IsTrue,
        False => ClauseAnalysis::IsFalse,
        Unassigned => {
            assert!(unassigned_terms.len() > 0);

            if unassigned_terms.len() == 1 {
                ClauseAnalysis::IsUnit(unassigned_terms[0].clone())
            }
            else {
                ClauseAnalysis::IsIndeterminate
            }
        }
    }
}

#[test]
fn analysis_detects_single_term_unit_clause() {
    let sln = Solution::new(4);
    let rval = analyse_clause(&[Lit(1)], &sln);
    assert!(rval == ClauseAnalysis::IsUnit(Lit(1)));
}

#[test]
fn analysis_detects_unit_clause() {
    let sln = Solution::from(4, &[(1, False), (2, False), (4, False)]);
    let rval = analyse_clause(&[Lit(1), Lit(2), Lit(3), Lit(4)], &sln);
    assert!(rval == ClauseAnalysis::IsUnit(Lit(3)));
}

#[test]
fn analysis_detects_true_clause() {
    let sln = Solution::from(4, &[(3, True)]);
    let rval = analyse_clause(&[Lit(1), Lit(2), Lit(3), Lit(4)], &sln);
    assert!(rval == ClauseAnalysis::IsTrue);
}

#[test]
fn analysis_detects_false_clause() {
    let sln = Solution::from(4, &[(2, False), (3, False)]);
    let rval = analyse_clause(&[Lit(2), Lit(3)], &sln);
    assert!(rval == ClauseAnalysis::IsFalse);
}


#[test]
fn analysis_detects_indeterminate_clause() {
    let sln = Solution::from(4, &[(2, False), (3, False)]);
    let rval = analyse_clause(&[Lit(1), Lit(2), Lit(3), Lit(4)], &sln);
    assert!(rval == ClauseAnalysis::IsIndeterminate);
}

#[derive(Show)]
enum PropagationResult {
    EvaluatesToFalse,

    /**
     * Contradiction detected during propagation. Returns both the conflict 
     * expressions and the variables that need to be reset before a retry can 
     * occur. (We need the reamaining ones returned as some of the terms in 
     * the conflict expression may have already been reset by cleanup code in 
     * the propagation routine.)
     */
    Contradiction (Vec<Clause>, VarSet),

    /**
     * The propagation succeded, and has returned the deduced implications.
     */
    Success (Vec<Var>)
}

impl PropagationResult {
    fn is_success(&self) -> bool {
        match *self {
            PropagationResult::Success (_) => true,
            _ => false
        }
    }

    fn is_failure(&self) -> bool {
        !self.is_success()
    }
}

static mut dump_idx : usize = 0us;

unsafe fn get_dump_idx() -> usize {
    let r = dump_idx;
    dump_idx = dump_idx + 1;
    r
}

/**
 * Propagates the logical consequences of the current solution.
 */
fn propagate(sln: &mut Solution,
             level: usize,
             seed_var: Var, 
             seed_val: SolutionValue, 
             e: &Expression,
             g: &mut ImplicationGraph) -> PropagationResult {

    let mut implications = ImplicationMap::new();
    let mut queue : Vec<(Var, SolutionValue)> = Vec::new();
    let mut conflicts = VarSet::new();
    let mut conflict_clauses : Vec<Clause> = Vec::new(); 
    let mut clause_vars = VarSet::new();

    queue.push((seed_var, seed_val));
    implications.add(seed_var, seed_val);
    g.insert(level, seed_var, seed_val, &[]);

    while !queue.is_empty() {
        let (var, val) = queue.pop().unwrap();
        if conflicts.contains(&var) {
            continue;
        }

        debug!("\tChecking implications of setting {:?} = {:?}", var, val);

        sln.set(var, val);

        for clause in e.clauses_containing(var) {
            match analyse_clause(clause, sln) {
                ClauseAnalysis::IsUnit (term) => {
                    debug!("\t\tFound unit clause {:?}, term of interest is {:?}", clause, term);
                    let v = term.var();

                    if conflicts.contains(&v) {
                        continue;
                    }

                    // deduce value
                    let deduced_value = match term {
                        Lit (_) => True,
                        Not (_) => False
                    };

                    debug!("\t\tDeduced that {:?} = {:?}", v, deduced_value);
                    let roots : Vec<(Var, SolutionValue)> = 
                        clause.iter()
                              .map(|&t| t.var())
                              .filter(|&term_var| term_var != v)
                              .map(|v| (v, sln[v]))
                              .collect();

                    g.insert(level, v, deduced_value, roots.as_slice());
                    // TODO: fixme

                    // check for a contradiction - have we aleady deduced that 
                    // this variable must have a different value?
//                  debug!("\t\tExisting implication for {:?} is {:?} (Unassigned == None)", 
//                         v, implications.value_of(v));

                    match implications.value_of(v) {
                        SolutionValue::Unassigned => { 
                            queue.push((v, deduced_value));
                            implications.add(v, deduced_value);
                        },

                        x => {
                            if x != deduced_value {
                                debug!("\t\tDetected contradiction on {:?}!", v);

                            unsafe {
                                let filename = format!("{:016x}.dot", get_dump_idx());
                                debug!("Dumping graph to: {:?}", filename);
                                dump_graph(&filename, g);
                            }

                                let conflict_clause = g.learn_conflict_clause(v, (seed_var, seed_val));
                                debug!("\t\tLearned {:?}", conflict_clause);
                                
                                sln.unset(v);

                                clause_vars.extend(
                                    conflict_clause.iter().map(|t| t.var()));
                                conflict_clauses.push(conflict_clause);
                                conflicts.insert(v);
                            }
                        }
                    }
                },

                ClauseAnalysis::IsTrue => { 
                    //debug!("\t\tClause {:?} is TRUE", clause);
                },

                ClauseAnalysis::IsFalse => {
                    // oh, dear. All variables in the term have values and the
                    // clause evaluates to false. Bail out and let the caller 
                    // know that this can't possibly be the right answer.
                    println!("\t\tClause {:?} evaluates to false. Ooops.", clause);
                    println!("\t\tCleaning up {:?}", implications);
                    for v in implications.vars() {
                        let val = sln[*v];
                        sln.unset(*v);
                        g.remove(*v, val);
                    }
                    return PropagationResult::EvaluatesToFalse
                },

                ClauseAnalysis::IsIndeterminate => { 
                    //debug!("\t\tClause {:?} is still indeterminate", clause);
                }
            }
        }
    }

    if conflict_clauses.is_empty() {
        debug!("Propagation success");
        PropagationResult::Success (implications.vars().map(|v| *v).collect())
    }
    else {
        debug!("Contradiction, cleaning up...");
        for v in implications.vars() {
            let val = sln[*v];
            sln.unset(*v);
            g.remove(*v, val);
            clause_vars.remove(v);
        }
        PropagationResult::Contradiction(conflict_clauses, clause_vars)
    }
}

#[test]
fn propagation_deduces_true_value() {
    let exp = Expression::from(&[&[Lit(1), Lit(2), Lit(3), Lit(4)]]);
    let mut sln = Solution::from(4, &[(1, False), (2, False)]);
    let mut g = ImplicationGraph::new();
    match propagate(&mut sln, 1, 4, False, &exp, &mut g) {
        PropagationResult::Success (mut implications) => {
            implications.sort();
            assert!(implications.as_slice() == [3us, 4us], 
                    "Expected [3, 4], got {:?}", implications);
        },
        other => {
            panic!("Unexpected propagation result: {:?}", other)
        }
    }
}

#[test]
fn propagation_deduces_false_value() {
    let exp = Expression::from(&[&[Lit(1), Lit(2), Not(3), Lit(4)]]);
    let mut sln = Solution::from(4, &[(1, False), (2, False)]);
    let mut g = ImplicationGraph::new();
    match propagate(&mut sln, 1, 4, False, &exp, &mut g) {
        PropagationResult::Success (mut implications) => {
            implications.sort();
            assert!(implications.as_slice() == [3us, 4us], 
                    "Expected [3, 4], got {:?}", implications);
        },
        other => {
            panic!("Unexpected propagation result: {:?}", other)
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
    let mut g = ImplicationGraph::from(&[
        (1, (1, False), &[])
    ]);
    
    match propagate(&mut sln, g.len()+1, 2, False, &exp, &mut g) {
        PropagationResult::Contradiction (mut c, mut vs) => {
            let expected = vec!(Lit(1), Lit(2));
            assert!(c.len() == 1, "Expected a single-element list");
            let mut clause : Vec<Term> = c[0].iter().map(|&x|x).collect();
            clause.sort();
            assert!(clause == expected, 
                    "Expected a conflict clause like {0:?}, got {1:?}", 
                    expected, clause);
        },
        other => panic!("Unexpected result from propagate(): {:?}", other)
    }

    assert!(sln[1] == False, "Expected False, got {:?}", sln[1]);
    assert!(sln[2] == Unassigned, "Expected Unassigned, got {:?}", sln[2]);
    assert!(sln[3] == Unassigned, "Expected Unassigned, got {:?}", sln[3]);
}

#[test]
fn propagation_detects_evaluation_to_false() {
    let exp = Expression::from(&[
        &[Lit(1), Lit(2), Lit(3)],
        &[Lit(1), Lit(2), Not(4)],
    ]);

    let mut sln = Solution::from(4, &[(1, False), (2, False)]);
    let mut g = ImplicationGraph::from(&[
        (1, (1, False), &[]),
        (2, (2, False), &[])
    ]);

    match propagate(&mut sln, g.len()+1, 3, False, &exp, &mut g) {
        PropagationResult::EvaluatesToFalse => {},
        other => panic!("Unexpected result from propagate(): {:?}", other)
    }

    println!("Graph: {:?}", g);

    assert!(g.len() == 2);
    assert!(g.has(1));
    assert!(g.has(2));
}
