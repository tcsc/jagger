use std::cmp;
use std::cmp::Ordering;
use std::fmt;
use std::iter::FromIterator;
use self::VersionExpression::*;

pub type Ordinal = usize; 

#[derive(Clone, Hash)]
pub enum VersionExpression {
    Any,
    Eq (Ordinal),
    Gt (Ordinal),
    Gte (Ordinal),
    Lt (Ordinal),
    Lte (Ordinal),
    And (Box<VersionExpression>, Box<VersionExpression>),
    Or (Box<VersionExpression>, Box<VersionExpression>),
}

pub fn eq(n: Ordinal) -> VersionExpression { VersionExpression::Eq(n) }
pub fn gt(n: Ordinal) -> VersionExpression { VersionExpression::Gt(n) }
pub fn gte(n: Ordinal) -> VersionExpression { VersionExpression::Gte(n) }
pub fn lt(n: Ordinal) -> VersionExpression { VersionExpression::Lt(n) }
pub fn lte(n: Ordinal) -> VersionExpression { VersionExpression::Lte(n) }

pub fn and(a: VersionExpression, b: VersionExpression) -> VersionExpression { 
    VersionExpression::And(box a, box b) 
}

pub fn or(a: VersionExpression, b: VersionExpression) -> VersionExpression { 
    VersionExpression::Or(box a, box b)
}

impl VersionExpression {
    fn matches(&self, ver: Ordinal) -> bool {
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

impl fmt::Show for VersionExpression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Any => write!(f, "any"),
            Eq(n) => write!(f, "= {:?}", n),
            Gt(n) => write!(f, "> {:?}", n),
            Gte(n) => write!(f, ">= {:?}", n),
            Lt(n) => write!(f, "< {:?}", n),
            Lte(n) => write!(f, "<= {:?}", n),
            And(ref a, ref b) => write!(f, "{:?} && {:?}", a, b),
            Or(ref a, ref b) => write!(f, "{:?} || {:?}", a, b)
        }
    }
}

impl cmp::Eq for VersionExpression {

}

#[test]
fn version_expression_any()  {
    let v = VersionExpression::Any;
    assert!(v.matches(7));
    assert!(v.matches(42));
    assert!(v.matches(48));
}


#[test]
fn version_expression_eq()  {
    let v = eq(42);
    assert!(!v.matches(7));
    assert!(v.matches(42));
    assert!(!v.matches(48));
}

#[test]
fn version_expression_gt()  {
    let v = gt(42);
    assert!(!v.matches(7));
    assert!(!v.matches(42));
    assert!(v.matches(48));
}

#[test]
fn version_expression_gte()  {
    let v = gte(42);
    assert!(!v.matches(7));
    assert!(v.matches(42));
    assert!(v.matches(48));
}

#[test]
fn version_expression_lt()  {
    let v = lt(42);
    assert!(v.matches(7));
    assert!(!v.matches(42));
    assert!(!v.matches(48));
}

#[test]
fn version_expression_lte()  {
    let v = lte(42);
    assert!(v.matches(7));
    assert!(v.matches(42));
    assert!(!v.matches(48));
}

#[test]
fn version_expression_boolean_and()  {
    let v = and(gt(42), lt(44)); 
    assert!(v.matches(43));
    assert!(!v.matches(41));
    assert!(!v.matches(42));
    assert!(!v.matches(44));
    assert!(!v.matches(45));
}

#[test]
fn version_expression_boolean_or()  {
    let v = or(eq(1), eq(163)); 
    assert!(v.matches(1));
    assert!(!v.matches(2));

    assert!(!v.matches(162));
    assert!(v.matches(163));
    assert!(!v.matches(164));
}

/**
 * A package name and the version of that package required.
 */
#[derive(Clone, Eq, Hash)]
pub struct PkgExp {
    name: String,
    version: VersionExpression 
}

impl PkgExp {
    pub fn new(name: &str, version: VersionExpression) -> PkgExp {
        PkgExp { 
            name: String::from_str(name),
            version: version
        }
    }
}

impl PartialEq for PkgExp {
    fn eq(&self, other: &PkgExp) -> bool {
        self.name == other.name && self.version == other.version
    }
}

impl fmt::Show for PkgExp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?} {:?}", self.name, self.version)
    }
}

// ----------------------------------------------------------------------------
// Package - An abstract representation of a package
// ----------------------------------------------------------------------------

#[derive(Show, Eq, PartialEq, Hash, Clone)]
pub enum State {
    Installed,
    Available,
}

/**
 * The metadata for a given package at a given version.
 */
 #[derive(Hash)]
pub struct Package {
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
    ordinal: Ordinal,

    state: State,

    requires: Vec<PkgExp>,
    conflicts: Vec<PkgExp> 
}

impl Package {
    pub fn new_installed(name: &str, ordinal: Ordinal) -> Package {
        Package::new(name, ordinal, State::Installed)
    }

    pub fn new_available(name: &str, ordinal: Ordinal) -> Package {
        Package::new(name, ordinal, State::Available)
    }

    pub fn new(name: &str, ordinal: Ordinal, state: State) -> Package {
        Package { 
            name: String::from_str(name),
            ordinal: ordinal,
            state: state,
            requires: Vec::new(),
            conflicts: Vec::new() 
        }
    }

    /**
     * Adds a requirement to the 
     */
    pub fn add_requirement(&mut self, name: &str, ver: VersionExpression) {
        self.requires.push(PkgExp::new(name, ver));
    }

    /**
     *
     */
    pub fn requires<'a>(&'a self) -> &'a [PkgExp] {
        self.requires.as_slice()
    }

    pub fn add_conflict(&mut self, name: &str, ver: VersionExpression) {
        self.conflicts.push(PkgExp::new(name, ver));
    }

    pub fn conflicts<'a>(&'a self) -> &'a [PkgExp] {
        self.conflicts.as_slice()
    }

    /**
     * Checks to see if this package meets the requirements of a given package 
     * expression. 
     */
    pub fn matches(&self, exp: &PkgExp) -> bool {
        (self.name == exp.name) && exp.version.matches(self.ordinal)
    }

    pub fn name<'a>(&'a self) -> &'a str { self.name.as_slice() }

    pub fn ordinal(&self) -> Ordinal { self.ordinal }
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

impl cmp::Eq for Package {}

impl PartialOrd for Package {
    fn partial_cmp(&self, other: &Package) -> Option<cmp::Ordering> {
        match self.name.cmp(&other.name) {
            Ordering::Equal => Some(self.ordinal.cmp(&other.ordinal)),
            rval => Some(rval)
        }
    }
}

impl Ord for Package {
    fn cmp(&self, other: &Package) -> Ordering {
        if self.name < other.name {
            Ordering::Less
        }
        else if self.name > other.name {
            Ordering::Greater
        } 
        else {
            match self.ordinal {
                n if n < other.ordinal => Ordering::Less,
                n if n > other.ordinal => Ordering::Greater,
                _ => Ordering::Equal
            }
        }
    }
}

impl Clone for Package {
    fn clone(&self) -> Package {
        Package {
            name: self.name.clone(),
            ordinal: self.ordinal,
            state: self.state.clone(),
            requires: self.requires.clone(),
            conflicts: self.conflicts.clone()
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

/**
 * The store for (and ultimate owner of) all the package objects. 
 */
pub struct PkgDb {
    packages: Vec<Package>   
}

impl PkgDb {
    /**
     * Constructs a new, empty, package database.
     */
    pub fn new() -> PkgDb {
        PkgDb { packages: Vec::new() }
    }

    /**
     * Adds packages to the database.
     */
    pub fn add_packages(& mut self, packages: &[Package]) {
        self.packages.push_all(packages);
    }

    pub fn iter<'a>(&'a self) -> ::std::slice::Iter<'a, Package> {
        self.packages.iter()
    }

    pub fn select<'a>(&'a self, name: &str, ver: VersionExpression) -> Vec<&'a Package> {
        self.select_exp(&PkgExp::new(name, ver))
    }

    pub fn installed_packages<'a>(&'a self) -> Vec<&'a Package> {
        self.packages
            .iter()
            .filter(|p| p.state == State::Installed)
            .collect()
    }

    /**
     * Selects a set of packages that match a given name and version 
     * expression.
     */
    pub fn select_exp<'a>(&'a self, spec: &PkgExp) -> Vec<&'a Package> {
        self.packages.iter()
                     .filter(|p| p.matches(spec))
                     .collect()
    } 
}


#[test]
fn pkgdb_select_non_existant_package_name_returns_empty_vector() {
    let db = PkgDb::new();
    assert!(db.select("nonesuch", VersionExpression::Any).is_empty())
}

#[cfg(test)]
fn pkg_vec<F>(n: usize, f: F) -> Vec<Package> where 
    F: FnMut(usize) -> Package 
{
    FromIterator::from_iter(range(0, n).map(f))
}

#[test]
fn pkgdb_empty_select_returns_empty_vector() {
    let mut db = PkgDb::new();
    db.add_packages(pkg_vec(5, |n| {
        Package::new("alpha", n, State::Available)
    }).as_slice());
    assert!(db.select("nonesuch", gt(10)).is_empty())
}

#[test]
fn pkgdb_select_returns_expected_packages() {
    let mut db = PkgDb::new();
    db.add_packages(pkg_vec(5, |n| { 
        Package::new("alpha", n, State::Available)
    }).as_slice());
    db.add_packages(pkg_vec(10, |n| {
        Package::new("beta", n, State::Available)
    }).as_slice());

    let data = pkg_vec(4, |n| Package::new_available("beta", n + 6));
    let expected : Vec<&Package> = data.iter().map(|p| p).collect();
    let actual = db.select("beta", gte(6));

    assert!(expected.as_slice() == actual.as_slice(), 
            "expected: {:?}, got: {:?}", expected, actual);
}
