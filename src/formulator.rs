use std::collections::{HashMap, BitvSet};
use std::fmt;
use std::iter::FromIterator;
use solver::{Term, Clause, Solution, SolutionValue, Var};
use solver::Term::*;
use solver::SolutionValue::{True, False, Unassigned};

use pkg::*;

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

enum FormulatorError {
    NoVariableFor (String, Ordinal)
}

impl fmt::Debug for FormulatorError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FormulatorError::NoVariableFor (ref name, ordinal) => {
                write!(f, "{0}, #{1}", name, ordinal)
            }
        }
    }
}

type FormulatorResult<T> = Result<T, FormulatorError>;

fn no_var_for<T>(pkg: &Package) -> FormulatorResult<T> {
    let s = String::from_str(pkg.name());
    Err(FormulatorError::NoVariableFor(s, pkg.ordinal()))
}

/**
 *
 */
struct Solver<'a> {
    pkgvars: HashMap<&'a Package, Var>,
    pkgdb: &'a PkgDb
}

impl<'a> Solver<'a> {
	fn new(packages: &'a PkgDb) -> Solver<'a> {
		let mut s = Solver{ pkgvars: HashMap::new(), pkgdb: packages };
        for (n, p) in packages.iter().enumerate() {
            s.pkgvars.insert(p, n);
        }
        s
	}

    /**
     * Generates a Clause descrbing a mutual exclusion
     */
    fn make_conflict_clause(&self, a: &Package, b: &Package) -> FormulatorResult<Clause> {
        let va = Term::Not(try!(self.pkg_var(a)));
        let vb = Term::Not(try!(self.pkg_var(b)));
        Ok( Clause::from(&[va, vb]) )
    }

    fn pkg_vars(&self, name: &str, exp: VersionExpression) -> FormulatorResult<Vec<Var>> {
        let mut pkgs : Vec<Var> = vec![];
        for pkg in self.pkgdb.select(name, exp).iter() {
            let pkgvar = try!(self.pkg_var(*pkg));
            pkgs.push(pkgvar);
        }
        Ok(pkgs)
    }

    fn apply_system_clauses(&mut self) {

    }

    /**
     * Looks up the variable that represents a given package in the solver.
     * Returns None if no such variable exists.
     */
    fn find_pkg_var(&'a self, pkg: &'a Package) -> Option<Var> {
        match self.pkgvars.get(&pkg) {
            Some(n) => Some(*n),
            None => None
        }
    }

    fn pkg_var(&'a self, pkg: &'a Package) -> FormulatorResult<Var> {
        match self.find_pkg_var(pkg) {
            None => no_var_for(pkg),
            Some(n) => Ok(n)
        }
    }
}

impl<'a> fmt::Debug for Solver<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (key, value) in self.pkgvars.iter() {
            try!(writeln!(f, "{:?}: {:p}: {}", key, *key, value));
        }
        writeln!(f, "")
    }
}

/**
 * Constructs a set of Clauses that say only one package with the supplied
 * name may be installed. For example, should you have a repo with packages
 * A1, A2 & A3, then this function should return the set of
 *  (~A1 | ~A2) & (~A1 | ~A3) & (~A2 | ~A3)
 */
fn make_unique_install_clauses(s: &Solver, name: &str) -> FormulatorResult<Vec<Clause>> {
    let mut result = vec![];
    let mut visited = BitvSet::new();
    let pkgs = try!(s.pkg_vars(name, VersionExpression::Any));

    for a in pkgs.iter() {
        for b in pkgs.iter() {
            if *a == *b {
                continue;
            }

            if visited.contains(b) {
                continue;
            }

            result.push( Clause::from(&[Term::Not(*a), Term::Not(*b)]) );
        }
        visited.insert(*a);
    }
    Ok(result)
}

#[test]
fn unique_package_install_clauses_are_created_correctly() {
    // asserts that the Clauses stating that only one version of a package may be
    // installed are created as we expect (i.e., if packages A1, A2 and A3
    // exist, then we want to have Clauses like (~A1 | ~A2) & (~A2 | ~A3) & (~A1 | ~A3)

    let db = &mk_test_db();
    let s = Solver::new(db);
    let actual = make_unique_install_clauses(&s, "alpha").unwrap();
    let pkgs = db.select("alpha", VersionExpression::Any);

    for a in pkgs.iter() {
        for b in pkgs.iter() {
            if a != b {
                // assert that we can find a clause that says (~a | ~b) or
                // (~b | ~a)
                assert!( actual.iter().find(|r| {
                    let fwd = s.make_conflict_clause(*a, *b).unwrap();
                    let rev = s.make_conflict_clause(*b, *a).unwrap();

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
fn make_conflicts_clauses(s: &Solver, pkg: &Package, exp: &PkgExp) -> FormulatorResult<Vec<Clause>> {
    let pkgvar = try!(s.pkg_var(pkg));
    let mut result = Vec::new();

    for conflict in s.pkgdb.select_exp(exp).iter() {
        let conflict_var = try!(s.pkg_var(*conflict));
        result.push( Clause::from(&[Term::Not(pkgvar), Term::Not(conflict_var)]) )
    }
    Ok(result)
}

#[test]
fn package_conflict_clauses_are_generated_correctly() {
    let db = &mk_test_db();

    // find the package that we want to test
    let pkg = match &db.select("gamma", eq(5))[] {
        [p] => p,
        _ => {
            assert!(false, "Expected exactly one package returned from select");
            return
        }
    };

    let s = Solver::new(db);
    let pkgvar = s.pkg_var(pkg).unwrap();
    let expected : Vec<Clause>
        = db.select("alpha", lte(2))
            .iter()
            .map(|p| Clause::from( &[Not(pkgvar), Not(s.pkg_var(*p).unwrap())] )  )
            .collect();

    match make_conflicts_clauses(&s, pkg, &pkg.conflicts()[0]) {
        Ok (actual) => {
            assert!(actual == expected, "expected {:?}, got {:?}", expected, actual);
        },
        Err (reason) => {
            assert!(false, "Failed with {0:?}", reason)
        }
    }
}

/**
 * Generates Clauses that specify that a version of the installed packages must
 * stay installed. Installed packages can be upgraded but not uninstalled.
 */
fn make_installed_package_upgrade_clauses(s: &Solver) -> FormulatorResult<Vec<Clause>> {
    let mut result = Vec::new();
    for pkg in s.pkgdb.installed_packages().iter() {
        let valid_pkgs = s.pkgdb.select(pkg.name(), gte(pkg.ordinal()));
        let mut terms : Vec<Term> = Vec::new();
        for p in valid_pkgs.iter() {
            terms.push(Term::Lit(try!(s.pkg_var(*p))))
        }
        result.push( Clause::from(&terms[]) );
    }
    Ok(result)
}

#[test]
fn installed_packages_must_be_installed_or_upgraded() {
    // asserts that the Clauses stating that a package's dependencies

    let db = &mk_test_db();
    let s = Solver::new(db);

    let mk_test_clause = |&: name: &str, ord: Ordinal| -> Clause {
        FromIterator::from_iter(
            db.select(name, gte(ord))
              .iter()
              .map(|p| s.pkg_var(*p).unwrap())
              .map(|v| Term::Lit(v)))
    };

    let find_clause = |&: a: &Clause, b: &Clause| -> bool {
        *a == *b
    };

    match make_installed_package_upgrade_clauses(&s) {
        Ok (clauses) => {
            assert!(clauses.len() == 2, "Expected 2 Clauses, got {0:?}", clauses.len());

            let r1 = mk_test_clause("alpha", 1);
            let r2 = mk_test_clause("beta", 4);

            assert!(clauses.iter()
                           .find(|x| find_clause(*x, &r1))
                           .is_some(),
                    "Couldn't find Clause {0:?}", r1);

            assert!(clauses.iter()
                           .find(|x| find_clause(*x, &r2))
                           .is_some(),
                    "Couldn't find Clause {0:?}", r2);

        },
        Err (reason) => {
            panic!("failed with {0:?}", reason)
        }
    }
}

/**
 * Automatically deselects all packages older than any installed packages.
 */
fn deny_installed_package_downgrades(s: &Solver,sln: &Solution) -> FormulatorResult<Solution> {
    let mut result = sln.clone();
    for pkg in s.pkgdb.installed_packages().iter() {
        let invalid_pkgs = s.pkgdb.select(pkg.name(), lt(pkg.ordinal()));
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
    let sln = deny_installed_package_downgrades(&solver, &Solution::new(100)).unwrap();

    debug!("Pkgs: {0:?}", solver.pkgvars);
    debug!("Soln: {0:?}", sln);

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
 * Generates a Clause requiring that at least one of the packages specified
 * by the package expression must be installed for the root package is
 * installed. For example, given package A depends on package B,
 * versions 2-4, this method will generate a Clause like
 *
 *    (~A | B2 | B3 | B4)
 *
 * This Clause basically states that either A is not installed, or package A
 * AND any of B2, B3, B4 are installed. We rely on the clauses generated by
 * the unique install Clause to make sure *only one* of them is installed in
 * the end.
 */
fn make_requires_clause(s: &Solver, pkg: &Package, exp: &PkgExp) -> FormulatorResult<Clause> {
    let mut result = Vec::new();
    let pkgvar = try!(s.pkg_var(pkg));
    result.push(Term::Not(pkgvar));
    for dep in s.pkgdb.select_exp(exp).iter() {
        let v = try!(s.pkg_var(*dep));
        result.push(Term::Lit(v))
    }
    Ok( Clause::from(&result[]) )
}

#[test]
fn package_requirement_clauses_are_created_correctly() {
    // asserts that the clauses stating that a package's dependencies
    let db = &mk_test_db();

    // find the package that we want to test
    let pkg = match &db.select("gamma", eq(5))[] {
        [p] => p,
        _ => {
            assert!(false, "Expected exactly one package returned from select");
            return
        }
    };

    let s = Solver::new(db);

    let mut expected = vec![ match s.pkg_var(pkg) {
        Err(reason) => { assert!(false, "Failed with {0:?}", reason); return },
        Ok(var) => Term::Not(var)
    }];
    match s.pkg_vars("beta", gte(5)) {
        Err(reason) => assert!(false, "Failed with {0:?}", reason),
        Ok(vars) => expected.extend(vars.iter().map(|x| Term::Lit(*x)))
    };

    match make_requires_clause(&s, pkg, &pkg.requires()[0]) {
        Ok (actual) => {
            let e = Clause::from(&expected[]);
            assert!(actual == e, "Expected: {0:?}, got {1:?}", e, actual);
        },
        Err (reason) => {
            assert!(false, "Failed with {0:?}", reason)
        }
    }
}

#[cfg(test)]
fn pkg_vec<F>(n: usize, f: F) -> Vec<Package> where
    F: FnMut(usize) -> Package
{
    FromIterator::from_iter(range(0, n).map(f))
}

#[cfg(test)]
fn mk_test_db() -> PkgDb {
    // b0  b1  b2  b3  b4* b5  b6  b7  b8  b9
    //  |   |   |   |   |   |   |   |   |   |
    // >=  >=  >=  >=  >=  >=  >=  >=  >=  >=
    //  |   |   |   |   |   |   |   |   |   |
    // g0  g1  g2  g3  g4  g5  g6  g7  g8  g9
    //  | /     | /     | /     | /     | /
    //  <=      <=      <=      <=      <=
    //  |       |       |       |       |
    // a0      a1*     a2      a3      a4

    let mut db = PkgDb::new();
    db.add_packages(&pkg_vec(5, |n| {
        let state = if n == 1 { State::Installed } else { State::Available };
        Package::new("alpha", n, state)
    })[]);

    db.add_packages(&pkg_vec(10, |n| {
        let state = if n == 4 { State::Installed } else { State::Available };
        Package::new("beta", n, state)
    })[]);

    db.add_packages(&pkg_vec(10, |n| {
        let mut p = Package::new("gamma", n, State::Available);
        p.add_requirement("beta", gte(n));
        p.add_conflict("alpha", lte(n / 2));
        p
    })[]);


    return db
}