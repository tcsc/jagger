use std::collections::{TreeMap};
use package::{VersionExpression, Package, PkgDb, PkgQuery, PkgExp, Eq, Gte, Lte};
use std::fmt;

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
    pkgvars: TreeMap<&'a Package, uint>,
    pkgdb: &'a PkgDb
}

impl<'a> Solver<'a> {
	fn new(packages: &'a PkgDb) -> Solver<'a> {
		let mut s = Solver{ pkgvars: TreeMap::new(), pkgdb: packages };
        for (n, p) in packages.iter().enumerate() {
            s.pkgvars.insert(p, n);
        }
        s
	}

    fn make_requires_clause(&self, pkg: &Package, exp: &PkgExp) -> Rule {
        let mut result = Vec::new();
        result.push(Not(self.pkg_var(pkg).unwrap()));
        for dep in self.pkgdb.select_exp(exp).iter() {
            result.push(Lit(self.pkg_var(*dep).unwrap()))
        }
        Rule(result)
    }

    fn make_conflicts_clauses(&self, pkg: &Package, exp: &PkgExp) -> Vec<Rule> {
        let pkgvar = self.pkg_var(pkg).unwrap();
        self.pkgdb.select_exp(exp)
                  .iter()
                  .map(|p| { Rule( vec![
                    Not(pkgvar), 
                    Not(self.pkg_var(*p).unwrap())
                  ]) })
                  .collect()
    }

    fn pkg_var(&'a self, pkg: &'a Package) -> Option<uint> {
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
fn mk_test_db() -> PkgDb {
    let mut db = PkgDb::new();
    db.add_packages(Vec::from_fn(5, |n| Package::new("alpha", n)).as_slice());
    db.add_packages(Vec::from_fn(10, |n| Package::new("beta", n)).as_slice());
    db.add_packages(Vec::from_fn(10, |n| { 
        let mut p = Package::new("gamma", n);
        p.add_requirement("beta", Gte(n));
        p.add_conflict("alpha", Lte(n / 2));
        p
    }).as_slice());
    return db
}

#[test]
fn generate_requires_clause() {
    let db = &mk_test_db();

    // find the package that we want to test
    let pkg = match db.select("gamma", Eq(5)).as_slice() {
        [p] => p,
        x => {
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
fn generate_conflicts_clause() {
    let db = &mk_test_db();

    // find the package that we want to test
    let pkg = match db.select("gamma", Eq(5)).as_slice() {
        [p] => p,
        x => {
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