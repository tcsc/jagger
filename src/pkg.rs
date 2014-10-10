use std::cmp;
use std::fmt;

#[deriving(Clone)]
pub enum VersionExpression {
    Any,
    Eq (uint),
    Gt (uint),
    Gte (uint),
    Lt (uint),
    Lte (uint),
    And (Box<VersionExpression>, Box<VersionExpression>),
    Or (Box<VersionExpression>, Box<VersionExpression>),
}

impl VersionExpression {
    fn matches(&self, ver: uint) -> bool {
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
            Eq(n) => write!(f, "= {}", n),
            Gt(n) => write!(f, "> {}", n),
            Gte(n) => write!(f, ">= {}", n),
            Lt(n) => write!(f, "< {}", n),
            Lte(n) => write!(f, "<= {}", n),
            And(ref a, ref b) => write!(f, "{} && {}", a, b),
            Or(ref a, ref b) => write!(f, "{} || {}", a, b)
        }
    }
}

impl cmp::Eq for VersionExpression {

}

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
        write!(f, "{} {}", self.name, self.version)
    }
}

// ----------------------------------------------------------------------------
// Package - An abstract representation of a package
// ----------------------------------------------------------------------------

#[deriving(Show, Eq, PartialEq)]
pub enum State {
    Installed,
    Available,
}

/**
 * The metadata for a given package at a given version.
 */
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
    ordinal: uint,

    state: State,

    requires: Vec<PkgExp>,
    conflicts: Vec<PkgExp> 
}

impl Package {
    pub fn new_installed(name: &str, ordinal: uint) -> Package {
        Package::new(name, ordinal, Installed)
    }

    pub fn new_available(name: &str, ordinal: uint) -> Package {
        Package::new(name, ordinal, Available)
    }

    pub fn new(name: &str, ordinal: uint, state: State) -> Package {
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

    pub fn ordinal(&self) -> uint { self.ordinal }
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
    fn partial_cmp(&self, other: &Package) -> Option<Ordering> {
        match self.name.cmp(&other.name) {
            Equal => Some(self.ordinal.cmp(&other.ordinal)),
            rval => Some(rval)
        }
    }
}

impl Ord for Package {
    fn cmp(&self, other: &Package) -> Ordering {
        if self.name < other.name {
            Less
        }
        else if self.name > other.name {
            Greater
        } 
        else {
            match self.ordinal {
                n if n < other.ordinal => Less,
                n if n > other.ordinal => Greater,
                _ => Equal
            }
        }
    }
}

impl Clone for Package {
    fn clone(&self) -> Package {
        Package {
            name: self.name.clone(),
            ordinal: self.ordinal,
            state: self.state,
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

    pub fn iter<'a>(&'a self) -> ::std::slice::Items<'a, Package> {
        self.packages.iter()
    }

    pub fn select<'a>(&'a self, name: &str, ver: VersionExpression) -> Vec<&'a Package> {
        self.select_exp(&PkgExp::new(name, ver))
    }

    pub fn installed_packages<'a>(&'a self) -> Vec<&'a Package> {
        self.packages
            .iter()
            .filter(|p| p.state == Installed)
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
    assert!(db.select("nonesuch", Any).as_slice() == [])
}

#[test]
fn pkgdb_empty_select_returns_empty_vector() {
    let mut db = PkgDb::new();
    db.add_packages(Vec::from_fn(5, |n| {
        Package::new("alpha", n, Available)
    }).as_slice());
    assert!(db.select("nonesuch", Gt(10)).as_slice() == [])
}

#[test]
fn pkgdb_select_returns_expected_packages() {
    let mut db = PkgDb::new();
    db.add_packages(Vec::from_fn(5, |n| { 
        Package::new("alpha", n, Available)
    }).as_slice());
    db.add_packages(Vec::from_fn(10, |n| {
        Package::new("beta", n, Available)
    }).as_slice());

    let data = Vec::from_fn(4, |n| Package::new_available("beta", n + 6));
    let expected : Vec<&Package> = data.iter().map(|p| p).collect();
    let actual = db.select("beta", Gte(6));

    assert!(expected.as_slice() == actual.as_slice(), 
            "expected: {}, got: {}", expected, actual);
}
