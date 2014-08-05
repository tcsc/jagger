use std::collections::{TreeMap};
use std::vec;
use std::fmt;

#[deriving(Show, Clone)]
enum VersionExpression {
    Any,
    Eq (int),
    Gt (int),
    Gte (int),
    Lt (int),
    Lte (int),
    And (Box<VersionExpression>, Box<VersionExpression>),
    Or (Box<VersionExpression>, Box<VersionExpression>),
}

impl VersionExpression {
    fn matches(&self, ver: int) -> bool {
        match *self {
            Any => true,
            Eq(n) => n == ver,
            Gt(n) => ver > n,
            Gte(n) => ver >= n,
            Lt(n) => ver < n,
            Lte(n) => ver <= n,
            And(ref a, ref b) => a.matches(ver) && b.matches(ver),
            Or(ref a, ref b) => a.matches(ver) || b.matches(ver)
        }
    }
}

impl PartialEq for VersionExpression {
    fn eq(&self, other: &VersionExpression) -> bool {
        match *self {
            Any => match *other { Any => true, _ => false },
            Eq(n) => match *other { Eq(x) => n == x, _ => false },
            Gt(n) => match *other { Gt(x) => n == x, _ => false },
            Gte(n) => match *other { Gte(x) => n == x, _ => false },
            Lt(n) => match *other { Lt(x) => n == x, _ => false },
            Lte(n) => match *other { Lte(x) => n == x, _ => false },
            And(ref a, ref b) => a.eq(b),
            Or(ref a, ref b) => a.eq(b)
        }
    }
}

impl Eq for VersionExpression {}

#[test]
fn version_expression_any()  {
    let v = Any;
    assert!(v.matches(7));
    assert!(v.matches(42));
    assert!(v.matches(48));
}


#[test]
fn version_expression_eq()  {
    let v = Eq(42);
    assert!(!v.matches(7));
    assert!(v.matches(42));
    assert!(!v.matches(48));
}

#[test]
fn version_expression_gt()  {
    let v = Gt(42);
    assert!(!v.matches(7));
    assert!(!v.matches(42));
    assert!(v.matches(48));
}

#[test]
fn version_expression_gte()  {
    let v = Gte(42);
    assert!(!v.matches(7));
    assert!(v.matches(42));
    assert!(v.matches(48));
}

#[test]
fn version_expression_lt()  {
    let v = Lt(42);
    assert!(v.matches(7));
    assert!(!v.matches(42));
    assert!(!v.matches(48));
}

#[test]
fn version_expression_lte()  {
    let v = Lte(42);
    assert!(v.matches(7));
    assert!(v.matches(42));
    assert!(!v.matches(48));
}

#[test]
fn version_expression_boolean_and()  {
    let v = And(box Gt(42), box Lt(44)); 
    assert!(v.matches(43));
    assert!(!v.matches(41));
    assert!(!v.matches(42));
    assert!(!v.matches(44));
    assert!(!v.matches(45));
}

#[test]
fn version_expression_boolean_or()  {
    let v = Or(box Eq(1), box Eq(163)); 
    assert!(v.matches(1));
    assert!(!v.matches(2));

    assert!(!v.matches(162));
    assert!(v.matches(163));
    assert!(!v.matches(164));
}

/**
 * A package name and the version of that package required.
 */
#[deriving(Clone, Eq)]
struct PkgReq {
    name: String,
    restriction: VersionExpression 
}

impl PartialEq for PkgReq {
    fn eq(&self, other: &PkgReq) -> bool {
        self.name == other.name && self.restriction == other.restriction
    }
}

/**
 * The metadata for a given package at a given version.
 */
struct Package {
    /**
     *
     */
    name: String,

    /** 
     * The ordinal version (i.e. the index of this package in an ordered list 
     * of all known versions of this package) of a package. Using this value 
     * rather than a package format-specific version identifier means that the 
     * solver doesn't have care about the specifics of versioning in a given 
     * package format. 
     */
    ordinal: int,

    requires: Vec<PkgReq>,
    conflicts: Vec<PkgReq> 
}

impl Package {
    fn new(name: &str, ordinal: int) -> Package {
        Package { 
            name: String::from_str(name),
            ordinal: ordinal,
            requires: Vec::new(),
            conflicts: Vec::new() 
        }
    }

    /**
     * Checks to see if this package meets the requirements of a given PkgReq. 
     */
    fn matches(&self, cond: &VersionExpression) -> bool {
        cond.matches(self.ordinal)
    }
}

impl PartialEq for Package {
    fn eq(&self, other: &Package) -> bool {
        if self.name != other.name { return false };
        if self.ordinal != other.ordinal { return false };
        if self.requires.as_slice() != other.requires.as_slice() { return false };
        if self.conflicts.as_slice() != other.conflicts.as_slice() { return false };
        true 
    }
}

impl Clone for Package {
    fn clone(&self) -> Package {
        Package {
            name: self.name.clone(),
            ordinal: self.ordinal,
            requires: self.requires.clone(),
            conflicts: self.requires.clone()
        }
    }
}

impl fmt::Show for Package {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} #{}", self.name, self.ordinal)
    }
}

// ----------------------------------------------------------------------------
// PkgDb - the package metadata database
// ----------------------------------------------------------------------------

type PkgVec = Vec<Package>;
type PkgMap = TreeMap<String, PkgVec>;

/**
 * The store for (and ultimate owner of) all the package objects. 
 */
struct PkgDb {
    packages: PkgMap   
}

impl PkgDb {
    /**
     * Constructs a new, empty, package database.
     */
    fn new() -> PkgDb {
        PkgDb { packages: TreeMap::new() }
    }

    /**
     * Adds packages to the database. The versions vector is assumed to be 
     * stored in ascending version order.
     */
    fn add_packages(& mut self, name: &str, versions: &[Package]) {
        self.packages.insert(String::from_str(name), Vec::from_slice(versions));
    } 

    /**
     * Selects a set of packages that match a given name and version 
     * expression.
     */
    fn select<'a>(& 'a self, name: &str, cond: &VersionExpression) -> Vec<&'a Package> {
        let n = String::from_str(name);
        match self.packages.find(&n) {
            Some (ref v) => {
                v.iter()
                 .filter(|p| p.matches(cond))
                 .collect()
            },
            None => Vec::new()
        }
    }
}

#[test]
fn pkgdb_select_non_existant_package_name_returns_empty_vector() {
    let db = PkgDb::new();
    assert!(db.select("nonesuch", &Any).as_slice() == [])
}

#[test]
fn pkgdb_empty_select_returns_empty_vector() {
    let mut db = PkgDb::new();
    db.add_packages("alpha", Vec::from_fn(5, |n| Package::new("alpha", n as int)).as_slice());
    assert!(db.select("nonesuch", &Gt(10)).as_slice() == [])
}

#[test]
fn pkgdb_select_returns_expected_packages() {
    let mut db = PkgDb::new();
    db.add_packages("alpha", Vec::from_fn(5, |n| Package::new("alpha", n as int)).as_slice());
    db.add_packages("beta", Vec::from_fn(10, |n| Package::new("beta", n as int)).as_slice());

    let data = Vec::from_fn(4, |n| Package::new("beta", (n as int) + 6));
    let expected : Vec<&Package> = data.iter().map(|p| p).collect();
    let actual = db.select("beta", &Gte(6));

    println!("expected: {}", expected);
    println!("actual: {}", actual);

    assert!(expected.as_slice() == actual.as_slice());
}
