use std::collections::{TreeMap, BitvSet};
use std::fmt;
use std::rc::Rc;
use std::slice;
use std::vec;

use pkg;
use pkg::{Package, Gte, Lt, Lte, Eq, Any};

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

#[deriving(PartialEq, Eq, Show)]
enum SolutionValue { Unassigned, True, False }

impl SolutionValue {
    fn from_bool(val: bool) -> SolutionValue {
        match val {
            true => True,
            false => False
        }
    }

    fn as_bool(&self) -> bool {
        match *self {
            Unassigned => fail!("Expected True or False"),
            True => true,
            False => false
        }
    }
}

impl BitOr<SolutionValue, SolutionValue> for SolutionValue {
    fn bitor(&self, rhs: &SolutionValue) -> SolutionValue {
        if (*self == Unassigned) || (*rhs == Unassigned) {
            Unassigned
        }
        else {
            if (self.as_bool() | rhs.as_bool()) {
               True 
            }
            else {
                False
            }
        }
    }
}

#[test]
fn unassigned_solution_value_propagates_through_or() {
    assert!((Unassigned | True) == Unassigned);
    assert!((Unassigned | False) == Unassigned);
    assert!((True | Unassigned) == Unassigned);
    assert!((False | Unassigned) == Unassigned);
}

#[test]
fn oring_assigned_solution_values_behaves_like_boolean() {
    assert!((True | True) == True);
    assert!((True | False) == True);
    assert!((False | True) == True);
    assert!((False | False) == False);
}

impl Not<SolutionValue> for SolutionValue {
    fn not(&self) -> SolutionValue {
        match *self {
            Unassigned => Unassigned,
            True => False,
            False => True
        }
    }
}

#[test]
fn not_unassigned_solution_value_is_unassigned() {
    assert!(!Unassigned == Unassigned)
}

#[test]
fn not_assigned_solution_behaves_like_boolean() {
    assert!(!True == False);
    assert!(!False == True);
}

/**
 * A variable-to-value mapping.
 */
#[deriving(PartialEq, Clone, Show)]
struct Solution (TreeMap<uint, bool>);

impl Solution {
    /**
     * Creates an empty solution
     */
    fn new() -> Solution { Solution(TreeMap::new()) }

    /**
     * Creates a solution from predefined values encoded as a (variable, value) pair
     */
    fn from(values: &[(uint, SolutionValue)]) -> Solution {
        let mut s = Solution::new();
        for &(var, val) in values.iter() {
            s.set(var, val)
        }
        s
    }

    /**
     * Sets a value in the solution
     */
    fn set(&mut self, var: uint, val: SolutionValue) {
        let Solution(ref mut map) = *self;
        match val {
            Unassigned => map.remove(&var),
            _ => map.insert(var, val.as_bool())
        };
    }

    /**
     * Fetches a value in the solution
     */
    fn get(&self, var: uint) -> SolutionValue {
        let Solution(ref map) = *self;
        match map.find(&var) {
            Some(val) => SolutionValue::from_bool(*val),
            None => Unassigned
        }
    }
}

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

#[deriving(Clone)]
enum Term { Lit(uint), Not(uint) }

impl Term {
    fn var(&self) -> uint {
        match *self {
            Lit(v) => v,
            Not(v) => v
        }
    }

    fn value(&self, s: &Solution) -> SolutionValue {
        match s.get(self.var()) {
            Unassigned => Unassigned,
            val => match *self { Lit (_) => val, Not (_) => !val }
        } 
    }
}

impl PartialEq for Term {
    fn eq(&self, other: &Term) -> bool {
        match *self {
            Lit(x) => match *other { Lit(y) => x == y, _ => false },
            Not(x) => match *other { Not(y) => x == y, _ => false }
        }
    }
}

impl Eq for Term {}

impl fmt::Show for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Lit(x) => write!(f, "{}", x),
            Not(x) => write!(f, "not {}", x)
        }
    }
}

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

struct Rule(Vec<Term>); 

#[deriving(Clone)]
impl Rule {
    fn new() -> Rule {
        Rule(vec![])
    }

    fn from(terms: &[Term]) -> Rule {
        let mut r = Rule::new();
        for t in terms.iter() {
            r.add(*t)
        };
        r
    }

    fn add(&mut self, t: Term) {
        let Rule(ref mut r) = *self;
        r.push(t.clone())
    }

    fn terms<'a>(&'a self) -> slice::Items<'a, Term> {
        let Rule(ref r) = *self;
        r.iter()   
    }

    fn len(&self) -> uint {
        let Rule(ref r) = *self;
        r.len()
    }
}

impl FromIterator<Term> for Rule {
    fn from_iter<T: Iterator<Term>>(mut terms: T) -> Rule {
        let mut r = Rule::new();
        for t in terms {
            r.add(t.clone())
        }
        r
    }
}

impl PartialEq for Rule {
    fn eq(&self, other: &Rule) -> bool {
        let Rule(ref me) = *self;
        let Rule(ref it) = *other;
        me == it
    }
}

impl fmt::Show for Rule {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let Rule(ref terms) = *self;
        terms.fmt(f)
    }
}

type RuleRef = Rc<Rule>;

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

/**
 * An expression consisting of multiple rules that are ANDed together. The 
 * clauses are reference counted so that they can appear in multiple iterations
 * of the expression as it gets progressively simplified during solving. 
 */
 #[deriving(Show)]
struct Expression(Vec<RuleRef>);

impl Expression {
    fn new() -> Expression { Expression(vec![]) }

    fn from(rules: &[&[Term]]) -> Expression {
        let mut e = Expression::new();
        for r in rules.iter() {
            e.add( Rule::from(*r) );
        }
        e
    }

    fn iter<'a>(&'a self) -> slice::Items<'a, Rc<Rule>> //-> Items<Rc<Rule>> 
    {
        let Expression(ref v) = *self;
        v.iter()
    }

    fn len(&self) -> uint {
        let Expression(ref v) = *self;
        v.len()
    }

    fn add(&mut self, rule: Rule) {
        let Expression(ref mut v) = *self;
        v.push(Rc::new(rule));
    }

    fn add_ref(&mut self, rule: &Rc<Rule>) {
        let Expression(ref mut v) = *self;
        v.push(rule.clone())
    }
}

impl PartialEq for Expression {
    fn eq(&self, other: &Expression) -> bool {
        let Expression(ref me) = *self;
        let Expression(ref it) = *other;
        me == it
    }    
}

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

enum SolverError {
    NoVariableFor (String, uint)
}

impl fmt::Show for SolverError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            NoVariableFor (ref name, ordinal) => {
                write!(f, "{}, #{:u}", name, ordinal)
            }
        }
    }
}

type SolverResult<T> = Result<T, SolverError>;

fn no_var_for<T>(pkg: &Package) -> SolverResult<T> {
    Err(NoVariableFor(String::from_str(pkg.name()), pkg.ordinal()))
}

/**
 *
 */
struct Solver<'a> {
    pkgvars: TreeMap<&'a pkg::Package, uint>,
    pkgdb: &'a pkg::PkgDb
}

impl<'a> Solver<'a> {
	fn new(packages: &'a pkg::PkgDb) -> Solver<'a> {
		let mut s = Solver{ pkgvars: TreeMap::new(), pkgdb: packages };
        for (n, p) in packages.iter().enumerate() {
            s.pkgvars.insert(p, n);
        }
        s
	}

    /**
     * Generates a rule descrbing a mutual exclusion
     */
    fn make_conflict_rule(&self, a: &Package, b: &Package) -> SolverResult<Rule> {
        let va = Not(try!(self.pkg_var(a)));
        let vb = Not(try!(self.pkg_var(b)));
        Ok(Rule(vec![va, vb]))
    }

    fn pkg_vars(&self, name: &str, exp: pkg::VersionExpression) -> SolverResult<Vec<uint>> {
        let mut pkgs : Vec<uint> = vec![];
        for pkg in self.pkgdb.select(name, exp).iter() {
            let pkgvar = try!(self.pkg_var(*pkg));
            pkgs.push(pkgvar);
        }
        Ok(pkgs)
    }

    fn apply_system_rules(&mut self) {

    }

    /**
     * Looks up the variable that represents a given package in the solver. 
     * Returns None if no such variable exists.
     */
    fn find_pkg_var(&'a self, pkg: &'a pkg::Package) -> Option<uint> {
        match self.pkgvars.find(&pkg) {
            Some(n) => Some(*n),
            None => None
        }
    }

    fn pkg_var(&'a self, pkg: &'a pkg::Package) -> SolverResult<uint> {
        match self.find_pkg_var(pkg) {
            None => no_var_for(pkg),
            Some(n) => Ok(n)
        }  
    }
}

impl<'a> fmt::Show for Solver<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (key, value) in self.pkgvars.iter() {
            try!(writeln!(f, "{}: {:p}: {}", key, *key, value));
        }
        writeln!(f, "")
    }    
}

/**
 * Constructs a set of rules that say only one package with the supplied 
 * name may be installed. For example, should you have a repo with packages 
 * A1, A2 & A3, then this function should return the ruleset of 
 *  (~A1 | ~A2) & (~A1 | ~A3) & (~A2 | ~A3)
 */
fn make_unique_install_clauses(s: &Solver, name: &str) -> SolverResult<Vec<Rule>> {
    let mut result = vec![];
    let mut visited = BitvSet::new();
    let pkgs = try!(s.pkg_vars(name, Any));

    for a in pkgs.iter() {
        for b in pkgs.iter() {
            if *a == *b { 
                continue;
            }

            if visited.contains(b) { 
                continue;
            }

            result.push( Rule(vec![Not(*a), Not(*b)]) );
        }
        visited.insert(*a);
    }
    Ok(result)
}

#[test]
fn unique_package_install_rules_are_created_correctly() {
    // asserts that the rules stating that only one version of a package may be
    // installed are created as we expect (i.e., if packages A1, A2 and A3
    // exist, then we want to have rules like (~A1 | ~A2) & (~A2 | ~A3) & (~A1 | ~A3)

    let db = &mk_test_db();
    let s = Solver::new(db);
    let actual = make_unique_install_clauses(&s, "alpha").unwrap();
    let pkgs = db.select("alpha", Any);

    for a in pkgs.iter() {
        for b in pkgs.iter() {
            if a != b {
                // assert that we can find a clause that says (~a | ~b) or 
                // (~b | ~a)
                assert!( actual.iter().find(|r| {
                    let fwd = s.make_conflict_rule(*a, *b).unwrap();
                    let rev = s.make_conflict_rule(*b, *a).unwrap();

                    (*r).eq(&fwd) || (*r).eq(&rev)
                }).is_some())
            }
        }
    }

    // assert that there are the number of clauses that we would expect
    let n = (pkgs.len()-1) * pkgs.len() / 2;
    assert!(actual.len() == n);
}

/**
 * Generates a list of conflicts
 */
fn make_conflicts_clauses(s: &Solver, pkg: &pkg::Package, exp: &pkg::PkgExp) -> SolverResult<Vec<Rule>> {
    let pkgvar = try!(s.pkg_var(pkg));
    let mut result = Vec::new();

    for conflict in s.pkgdb.select_exp(exp).iter() {
        let conflict_var = try!(s.pkg_var(*conflict));
        result.push( Rule(vec![Not(pkgvar), Not(conflict_var)]) ) 
    }
    Ok(result)
}

#[test]
fn package_conflict_rules_are_generated_correctly() {
    let db = &mk_test_db();

    // find the package that we want to test
    let pkg = match db.select("gamma", Eq(5)).as_slice() {
        [p] => p,
        _ => {
            assert!(false, "Expected exactly one package returned from select");
            return
        }
    };

    let s = Solver::new(db);
    let pkgvar = s.pkg_var(pkg).unwrap();
    let expected : Vec<Rule> = db.select("alpha", Lte(2))
                                 .iter()
                                 .map(|p| { 
                                    Rule( vec![Not(pkgvar), Not(s.pkg_var(*p).unwrap())] )
                                 })
                                 .collect();

    match make_conflicts_clauses(&s, pkg, &pkg.conflicts()[0]) {
        Ok (actual) => {
            println!("actual: {}", actual);
            println!("expected: {}", expected);
            assert!(actual == expected);
        },
        Err (reason) => {
            assert!(false, "Failed with {}", reason)
        }
    }
}

/**
 * Generates rules that specify that a version of the installed packages must 
 * stay installed. Installed packages can be upgraded but not uninstalled.
 */
fn make_installed_package_upgrade_rules(s: &Solver) -> SolverResult<Vec<RuleRef>> {
    let mut result = Vec::new();
    for pkg in s.pkgdb.installed_packages().iter() {
        let valid_pkgs = s.pkgdb.select(pkg.name(), Gte(pkg.ordinal()));
        let mut rule = Rule::new();
        for p in valid_pkgs.iter() {
            rule.add(Lit(try!(s.pkg_var(*p))))
        }
        result.push(Rc::new(rule));
    }
    Ok(result)
}

#[test]
fn installed_packages_must_be_installed_or_upgraded() {
    // asserts that the rules stating that a package's dependencies  

    let db = &mk_test_db();
    let s = Solver::new(db);

    let mk_test_rule = |name, ord| -> Rule {
        FromIterator::from_iter(
            db.select(name, Gte(ord))
              .iter()
              .map(|p| s.pkg_var(*p).unwrap())
              .map(|v| Lit(v)))
    };

    let find_rule = |a: &Rule, b: &Rule| -> bool {
        let Rule(ref r1) = *a;
        let Rule(ref r2) = *b;
        r1 == r2
    };

    match make_installed_package_upgrade_rules(&s) {
        Ok (rules) => {
            assert!(rules.len() == 2, "Expected 2 rules, got {}", rules.len());

            let r1 = mk_test_rule("alpha", 1);
            let r2 = mk_test_rule("beta", 4);

            assert!(rules.iter()
                         .find(|x| find_rule(x.deref(), &r1))
                         .is_some(), 
                    "Couldn't find rule {}", r1);

            assert!(rules.iter()
                         .find(|x| find_rule(x.deref(), &r2))
                         .is_some(), 
                    "Couldn't find rule {}", r2);

        },
        Err (reason) => {
            fail!("failed with {}", reason)
        }
    }
}

/**
 * Automatically deselects all packages older than any installed packages.
 */
fn deny_installed_package_downgrades(s: &Solver,sln: &Solution) -> SolverResult<Solution> {
    let mut result = sln.clone(); 
    for pkg in s.pkgdb.installed_packages().iter() {
        let invalid_pkgs = s.pkgdb.select(pkg.name(), Lt(pkg.ordinal()));
        for invalid_pkg in invalid_pkgs.iter() {
            let ivar = try!(s.pkg_var(*invalid_pkg));
            result.set(ivar, False);
        }
    };
    Ok (result)
}

#[test]
fn installed_package_downgrades_are_disabled() {
    // asserts that the variables that indicate an installed package downgrade 
    // have been set to false by the appropriate function.
    let db = &mk_test_db();
    let solver = Solver::new(db);
    let sln = deny_installed_package_downgrades(&solver, &Solution::new()).unwrap();

    println!("Pkgs: {}", solver.pkgvars);
    println!("Soln: {}", sln);

    for pkg in db.installed_packages().iter() {
        let pvar = solver.pkg_var(*pkg).unwrap();
        assert!(sln.get(pvar) == Unassigned);

        for p in db.iter() {
            let v = solver.pkg_var(p).unwrap();
            if p.name() == pkg.name() {
                if p.ordinal() < pkg.ordinal() {
                    assert!(sln.get(v) == False)
                }
                else {
                    assert!(sln.get(v) == Unassigned)
                }
            }
        }
    }
}

/**
 * Generates a rule requiring that at least one of the packages specified 
 * by the package expression must be installed for the root package is 
 * installed. For example, given package A depends on package B, 
 * versions 2-4, this method will generate a rule like
 *
 *    (~A | B2 | B3 | B4)
 *
 * This rule basically states that either A is not installed, or package A 
 * AND any of B2, B3, B4 are installed. We rely on the clauses generated by 
 * the unique install rule to make sure *only one* of them is installed in 
 * the end.
 */
fn make_requires_clause(s: &Solver, pkg: &pkg::Package, exp: &pkg::PkgExp) -> SolverResult<Rule> {
    let mut result = Vec::new();
    let pkgvar = try!(s.pkg_var(pkg));
    result.push(Not(pkgvar));
    for dep in s.pkgdb.select_exp(exp).iter() {
        let v = try!(s.pkg_var(*dep));
        result.push(Lit(v))
    }
    Ok(Rule(result))
}


#[test]
fn package_requirement_rules_are_created_correctly() {
    // asserts that the rules stating that a package's dependencies  
    let db = &mk_test_db();

    // find the package that we want to test
    let pkg = match db.select("gamma", Eq(5)).as_slice() {
        [p] => p,
        _ => {
            assert!(false, "Expected exactly one package returned from select");
            return
        }
    };

    let s = Solver::new(db);

    let mut expected = vec![ match s.pkg_var(pkg) {
        Err(reason) => { assert!(false, "Failed with {}", reason); return },
        Ok(var) => Not(var)
    }];
    match s.pkg_vars("beta", Gte(5)) {
        Err(reason) => assert!(false, "Failed with {0}", reason),
        Ok(vars) => expected.extend(vars.iter().map(|x| Lit(*x)))
    };

    match make_requires_clause(&s, pkg, &pkg.requires()[0]) {
        Ok (actual) => {
            println!("actual: {}", actual);
            println!("expected: {}", expected);
            assert!(actual == Rule(expected));
        },
        Err (reason) => {
            assert!(false, "Failed with {}", reason)
        }
    }
}

fn solve(e: &Expression, s: &Solution) {
    let mut exp = e.clone();
    let mut sln = s.clone();

    // do assignment
    loop {
        match propagate(&sln, exp) {
            Success (new_exp, deduced_values) => {
            },

            Contradiction (_) => {
            },

            EvaluatesToFalse => {
            }
        }
    }
}

#[deriving(Show)]
enum PropagationResult {
    EvaluatesToFalse,

    /**
     * 
     */
    Contradiction (uint),

    /**
     * (new_exp, deduced_values) where
     *
     *   new_exp - An abbbreviated version of the input expression, where all
     *             rules proven to be true have been removed.
     *
     *   deduced_values - A dictionary of the values deduced from this 
     *                    propagation pass.
     */
    Success (Expression, Solution)
}

fn propagate(sln: &Solution, e: &Expression) -> PropagationResult {
    let mut new_exp = Expression::new();
    let mut deduced_values = Solution::new();
        
    for rule in e.iter() {
        let mut value = False;
        let mut unassigned_terms = Vec::with_capacity(rule.len());

        // walk each term in the rule and try to evaluate it.
        for term in rule.terms() {
            match term.value(sln) {
                Unassigned => { unassigned_terms.push(term) },
                v => { value = value | v; }
            }

            if value == True { break }
        }

        // decide what to do based on out evaluation attempt above
        match value {
            True => {
                // At least one term in the rule evaluates to true, meaning 
                // that the entire rule does. This in turn means that the 
                // entire rule can be removed from the expression and so reduce
                // the search space for the next time around. 

                // Watch us explicitly not copy the rule into the output 
                // expression.
            },

            False => {
                match unassigned_terms.len() {
                    // oh, dear. All variables in the term have values and the
                    // rule evaluates to false. Bail out and let the caller 
                    // know that this can't possibly be the right answer.
                    0 => { return EvaluatesToFalse },

                    // We have a 'unit' rule (i.e. all terms bar one are 
                    // false). We can infer a value for the remaining value and
                    // propagate that.
                    1 => {
                        let term = *unassigned_terms.get(0);
                        let var = term.var();

                        // deduce value
                        let deduced_value = match *term {
                            Lit (_) => True,
                            Not (_) => False
                        };

                        // check for a contradiction
                        match deduced_values.get(var) {
                            Unassigned => { deduced_values.set(var, deduced_value) },
                            x if (x != deduced_value) => { return Contradiction(var) }
                            _ => { /* value is consistent, all is well */ }
                        }
                    },

                    // We have multiple unassigned variables in the rule; not 
                    // much we can do here except wait for more letters in the 
                    // crossword.
                    _ => {}
                };

                // copy the rule into the output expression
                new_exp.add_ref(rule);
            },

            Unassigned => { 
                fail!("Rule evaluates to unassigned. This should have been expressly forbidden."); 
            }
        }
    }

    Success (new_exp, deduced_values)
}

#[test]
fn propagation_eliminates_true_rules() {
    let exp = Expression::from(&[
        &[Lit(2), Lit(3), Lit(4)],
        &[Not(1)],
        &[Lit(5), Lit(6)],
        &[Lit(2), Not(6)]
    ]);

    let sln = Solution::from(&[(1, False), (2, False), (5, True)]);
    match propagate(&sln, &exp) {
        Success (new_exp, _) => {
            let expected = Expression::from(&[
                &[Lit(2), Lit(3), Lit(4)],
                &[Lit(2), Not(6)]
            ]);
            assert!(new_exp == expected, "Expected {}, got {}", expected, new_exp);
        },
        other => {
            fail!("Unexpected propagation result")
        }
    }
}

#[test]
fn propagation_deduces_true_value() {
    let exp = Expression::from(&[&[Lit(1), Lit(2), Lit(3), Lit(4)]]);
    let sln = Solution::from(&[(1, False), (2, False), (4, False)]);
    match propagate(&sln, &exp) {
        Success (new_exp, deduced_values) => {
            assert!(exp == new_exp, "Expected {}, got {}", exp, new_exp);
            assert!(deduced_values == Solution::from(&[(3, True)]))
        },
        other => {
            fail!("Unexpected propagation result")
        }
    }
}

#[test]
fn propagation_deduces_false_value() {
    let exp = Expression::from(&[&[Lit(1), Lit(2), Not(3), Lit(4)]]);
    let sln = Solution::from(&[(1, False), (2, False), (4, False)]);
    match propagate(&sln, &exp) {
        Success (new_exp, deduced_values) => {
            assert!(exp == new_exp, "Expected {}, got {}", exp, new_exp);
            assert!(deduced_values == Solution::from(&[(3, False)]))
        },
        other => {
            fail!("Unexpected propagation result")
        }
    }
}

#[test]
fn propagation_detects_contradictions() {
    let exp = Expression::from(&[
        &[Lit(1), Lit(2), Lit(3)],
        &[Lit(1), Lit(2), Not(3)],
    ]);

    let sln = Solution::from(&[(1, False), (2, False)]);

    match propagate(&sln, &exp) {
        Contradiction (n) => assert!(n == 3, "Expected a contractiction of variable #3"),
        other => fail!("Unexpected result from propagate(): {}", other)
    }
}

#[test]
fn propagation_detects_evaluation_to_false() {
    let exp = Expression::from(&[
        &[Lit(1), Lit(2), Lit(3)],
        &[Lit(1), Lit(2), Not(4)],
    ]);

    let sln = Solution::from(&[(1, False), (2, False), (3, False)]);

    match propagate(&sln, &exp) {
        EvaluatesToFalse => {},
        other => fail!("Unexpected result from propagate(): {}", other)
    }
}

#[cfg(test)]
fn mk_test_db() -> pkg::PkgDb {
    // b0  b1  b2  b3  b4* b5  b6  b7  b8  b9
    //  |   |   |   |   |   |   |   |   |   |
    // >=  >=  >=  >=  >=  >=  >=  >=  >=  >=
    //  |   |   |   |   |   |   |   |   |   |
    // g0  g1  g2  g3  g4  g5  g6  g7  g8  g9
    //  | /     | /     | /     | /     | /
    //  <=      <=      <=      <=      <=
    //  |       |       |       |       |
    // a0      a1*     a2      a3      a4

    let mut db = pkg::PkgDb::new();
    db.add_packages(Vec::from_fn(5, |n| { 
        let state = if n == 1 { pkg::Installed } else { pkg::Available };
        pkg::Package::new("alpha", n, state)
    }).as_slice());
    
    db.add_packages(Vec::from_fn(10, |n| {
        let state = if n == 4 { pkg::Installed } else { pkg::Available };
        pkg::Package::new("beta", n, state)
    }).as_slice());
    
    db.add_packages(Vec::from_fn(10, |n| { 
        let mut p = pkg::Package::new("gamma", n, pkg::Available);
        p.add_requirement("beta", Gte(n));
        p.add_conflict("alpha", Lte(n / 2));
        p
    }).as_slice());


    return db
}