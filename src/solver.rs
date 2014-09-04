use std::collections::{TreeMap, BitvSet};
use std::fmt;

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

enum Literal { Lit(uint), Not(uint) }

impl PartialEq for Literal {
    fn eq(&self, other: &Literal) -> bool {
        match *self {
            Lit(x) => match *other { Lit(y) => x == y, _ => false },
            Not(x) => match *other { Not(y) => x == y, _ => false }
        }
    }
}

impl Eq for Literal {}

impl fmt::Show for Literal {
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

struct Rule(Vec<Literal>); 

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

    /**
     * Generates a list of conflicts
     */
    fn make_conflicts_clauses(&self, pkg: &pkg::Package, exp: &pkg::PkgExp) -> SolverResult<Vec<Rule>> {
        let pkgvar = try!(self.pkg_var(pkg));
        let mut result = Vec::new();

        for conflict in self.pkgdb.select_exp(exp).iter() {
            let conflict_var = try!(self.pkg_var(*conflict));
            result.push( Rule(vec![Not(pkgvar), Not(conflict_var)]) ) 
        }
        Ok(result)
    }

    fn pkg_vars(&self, name: &str, exp: pkg::VersionExpression) -> SolverResult<Vec<uint>> {
        let mut pkgs : Vec<uint> = vec![];
        for pkg in self.pkgdb.select(name, exp).iter() {
            let pkgvar = try!(self.pkg_var(*pkg));
            pkgs.push(pkgvar);
        }
        Ok(pkgs)
    }

    /**
     * Constructs a set of rules that say only one package with the supplied 
     * name may be installed. For example, should you have a repo with packages 
     * A1, A2 & A3, then this function should return the ruleset of 
     *  (~A1 | ~A2) & (~A1 | ~A3) & (~A2 | ~A3)
     */
    fn make_unique_install_clauses(&self, name: &str) -> SolverResult<Vec<Rule>> {
        let mut result = vec![];
        let mut visited = BitvSet::new();
        let pkgs = try!(self.pkg_vars(name, Any));

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

#[cfg(test)]
fn mk_test_db() -> pkg::PkgDb {
    // b0  b1  b2  b3  b4  b5  b6  b7  b8  b9
    //  |   |   |   |   |   |   |   |   |   |
    // >=  >=  >=  >=  >=  >=  >=  >=  >=  >=
    //  |   |   |   |   |   |   |   |   |   |
    // g0  g1  g2  g3  g4  g5  g6  g7  g8  g9
    //  | /     | /     | /     | /     | /
    //  <=      <=      <=      <=      <=
    //  |       |       |       |       |
    // a0      a1      a2      a3      a4

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

    match s.make_conflicts_clauses(pkg, &pkg.conflicts()[0]) {
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

#[test]
fn unique_package_install_rules_are_created_correctly() {
    // asserts that the rules stating that only one version of a package may be
    // installed are created as we expect (i.e., if packages A1, A2 and A3
    // exist, then we want to have rules like (~A1 | ~A2) & (~A2 | ~A3) & (~A1 | ~A3)

    let db = &mk_test_db();
    let s = Solver::new(db);
    let actual = s.make_unique_install_clauses("alpha").unwrap();
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