use std::collections::{TreeMap, BitvSet};
use std::fmt;
use pkg;
use pkg::{Package, Gte, Lte, Eq, Any};

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

enum Variable { Unassigned, True, False }

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

    fn make_requires_clause(&self, pkg: &pkg::Package, exp: &pkg::PkgExp) -> Rule {
        let mut result = Vec::new();
        result.push(Not(self.pkg_var(pkg).unwrap()));
        for dep in self.pkgdb.select_exp(exp).iter() {
            result.push(Lit(self.pkg_var(*dep).unwrap()))
        }
        Rule(result)
    }

    fn make_conflict_rule(&self, a: &Package, b: &Package) -> Rule {
        let va = self.pkg_var(a).unwrap();
        let vb = self.pkg_var(b).unwrap();
        Rule(vec![ Not(va), Not(vb) ])
    }

    /**
     * Generates a list of conflicts
     */
    fn make_conflicts_clauses(&self, pkg: &pkg::Package, exp: &pkg::PkgExp) -> Vec<Rule> {
        let pkgvar = self.pkg_var(pkg).unwrap();
        self.pkgdb.select_exp(exp)
                  .iter()
                  .map(|p| { self.make_conflict_rule(pkg, *p) })
                  .collect()
    }

    /**
     * Constructs a set of rules that say only one package with the supplied 
     * name may be installed. For example, should you have a repo with packages 
     * A1, A2 & A3, then this function should return the ruleset of 
     *  (~A1 | ~A2) & (~A1 | ~A3) & (~A2 | ~A3)
     */
    fn make_unique_install_clauses(&self, name: &str) -> Vec<Rule> {
        let mut result = vec![];
        let pkgs : Vec<uint> = self.pkgdb.select(name, Any)
                                   .iter()
                                   .map(|x| self.pkg_var(*x).unwrap())
                                   .collect();
        let mut visited = BitvSet::new();

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
        result
    }


    fn pkg_var(&'a self, pkg: &'a pkg::Package) -> Option<uint> {
        match self.pkgvars.find(&pkg) {
            Some(n) => Some(*n),
            None => None
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

#[cfg(test)]
fn mk_test_db() -> pkg::PkgDb {
    let mut db = pkg::PkgDb::new();
    db.add_packages(Vec::from_fn(5, |n| pkg::Package::new("alpha", n, pkg::Available)).as_slice());
    db.add_packages(Vec::from_fn(10, |n| pkg::Package::new("beta", n, pkg::Available)).as_slice());
    db.add_packages(Vec::from_fn(10, |n| { 
        let mut p = pkg::Package::new("gamma", n, pkg::Available);
        p.add_requirement("beta", Gte(n));
        p.add_conflict("alpha", Lte(n / 2));
        p
    }).as_slice());
    return db
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
    let actual = s.make_requires_clause(pkg, &pkg.requires()[0]);
    let mut expected = vec![ Not(s.pkg_var(pkg).unwrap()) ];
    expected.extend(db.select("beta", Gte(5))
                      .iter()
                      .map(|p| Lit(s.pkg_var(*p).unwrap())));

    println!("actual: {}", actual)
    println!("expected: {}", expected)

    assert!(actual == Rule(expected));
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
    let actual = s.make_conflicts_clauses(pkg, &pkg.conflicts()[0]);
    let expected : Vec<Rule> = db.select("alpha", Lte(2))
                                 .iter()
                                 .map(|p| { 
                                    Rule( vec![Not(pkgvar), Not(s.pkg_var(*p).unwrap())] )
                                 })
                                 .collect();

    println!("actual: {}", actual);
    println!("expected: {}", expected);

    assert!(actual == expected);
}

#[test]
fn unique_package_install_rules_are_created_correctly() {
    // asserts that the rules stating that only one version of a package may be
    // installed are created as we expect (i.e., if packages A1, A2 and A3
    // exist, then we want to have rules like (~A1 | ~A2) & (~A2 | ~A3) & (~A1 | ~A3)
    let db = &mk_test_db();
    let s = Solver::new(db);
    let actual = s.make_unique_install_clauses("alpha");
    let mut pkgs = db.select("alpha", Any);

    for a in pkgs.iter() {
        for b in pkgs.iter() {
            if a != b {
                assert!( actual.iter().find(|r| {
                    (*r).eq(&s.make_conflict_rule(*a, *b)) || 
                    (*r).eq(&s.make_conflict_rule(*b, *a))
                }).is_some())
            }
        }
    }
    
    let n = ((pkgs.len()-1) * pkgs.len() / 2);
    assert!(actual.len() == n);
}

#[test]
fn installed_package_upgrade_rules_are_created_correctly() {
    // asserts that the rules stating that an installed package may 
    // be upgraded (but not downgraded) are created as we expect.
    let db = &mk_test_db();
    for pkg in db.installed_packages().iter() {

    }
}