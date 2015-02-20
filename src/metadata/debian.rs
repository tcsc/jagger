
use self::System::*;
use self::Vendor::*;
use self::Cpu::*;
use std::str::FromStr;
use std::cmp;
use std::cmp::Ordering::*;

#[derive(PartialEq, Eq, Debug)]
pub enum ArchError {
    UnknownAlias (String),
    InvalidArchitecture (String),
    InvalidSystem (String),
    InvalidVendor (String),
    InvalidCpu (String)
}

pub type ArchResult<T> = Result<T, ArchError>;

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum System {
    AnySystem,
    Linux,
    Windows,
    Darwin,
    CustomSystem (String)
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Vendor {
    AnyVendor,
    NamedVendor (String)
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Cpu {
    AnyCpu,
    I386,
    AMD64,
    CustomCpu (String)
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Architecture {
    system: System,
    vendor: Vendor,
    cpu: Cpu
}

impl Architecture {
    pub fn is_compatible_with(&self, other: &Architecture) -> bool {
        let compatible_system = self.system == AnySystem ||
                                other.system == AnySystem ||
                                self.system == other.system;
        let compatible_vendor = self.vendor == AnyVendor ||
                                other.vendor == AnyVendor ||
                                self.vendor == other.vendor;
        let compatible_cpu = self.cpu == AnyCpu ||
                             other.cpu == AnyCpu ||
                             self.cpu == other.cpu;

        compatible_system && compatible_vendor && compatible_cpu
    }
}

#[test]
fn identical_architectures_are_compatible() {
    let a = Architecture {system: Windows, vendor: AnyVendor, cpu: I386};
    let b = a.clone();
    assert!(a.is_compatible_with(&b));
    assert!(b.is_compatible_with(&a));
}

fn parse_alias(a: &str) -> ArchResult<Architecture> {
    match a {
        "any" => Ok(Architecture{ system: AnySystem, vendor: AnyVendor, cpu: AnyCpu }),
        "win32" => Ok(Architecture{ system: Windows, vendor: AnyVendor, cpu: I386 }),
        "win64" => Ok(Architecture{ system: Windows, vendor: AnyVendor, cpu: AMD64 }),
        _ => Err(ArchError::UnknownAlias(String::from_str(a)))
    }
}

fn parse_system(a: &str) -> ArchResult<System> {
    match a {
        "any" => Ok(AnySystem),
        "mswindows"  => Ok(Windows),
        "linux" => Ok(Linux),
        "darwin" => Ok(Darwin),
        "" => Err(ArchError::InvalidSystem(String::from_str(a))),
        _ => Ok(CustomSystem(String::from_str(a)))
    }
}

fn parse_cpu(a: &str) -> ArchResult<Cpu> {
    match a {
        "any" => Ok(AnyCpu),
        "i386" => Ok(I386),
        "amd64" => Ok(AMD64),
        "" => Err(ArchError::InvalidCpu(String::from_str(a))), // invalid
        _ => Ok(CustomCpu(String::from_str(a)))
    }
}

#[test]
fn empty_cpu_is_an_error() {
    assert!(parse_cpu("") == Err(ArchError::InvalidCpu(String::from_str(""))))
}

#[test]
fn any_cpu_is_a_special_case() {
    assert!(parse_cpu("any") == Ok(AnyCpu))
}

fn parse_vendor(a: &str) -> ArchResult<Vendor> {
    match a {
        "any" => Ok(AnyVendor),
        "" => Err(ArchError::InvalidVendor(String::from_str(a))), // Invalid
        v => Ok(NamedVendor(String::from_str(v)))
    }
}

#[test]
fn empty_vendor_is_an_error() {
    assert!(parse_vendor("") == Err(ArchError::InvalidVendor(String::from_str(""))));
}

#[test]
// make sure the vendor "any" resolves to AnyVendor (as opposed to Vendor("any"))
fn any_vendor_is_a_special_case() {
    let result = parse_vendor("any");
    assert!(result.is_ok());
    assert!(result == Ok(AnyVendor));
}

/**
 * Parses a string describing an archtecture into an architecture struct.
 */
fn parse_arch(a: &str) -> ArchResult<Architecture> {
    if a == "" {
        Err(ArchError::InvalidArchitecture(String::from_str(a)))
    }
    else {
        let part_strings : Vec<&str> = a.split('-').collect();
        let parts = &part_strings[];
        match parts.len() {
            1 => parse_alias(parts[0]),
            n @ 2 ... 3 => {
                let system = try!(parse_system(parts[0]));
                let cpu = try!(parse_cpu(parts[parts.len()-1]));
                let vendor_name = if n == 2 { "any" } else { parts[1] };
                let vendor = try!(parse_vendor(vendor_name));
                Ok( Architecture {system: system, vendor: vendor, cpu: cpu} )
            }

            _ => Err(ArchError::InvalidArchitecture(String::from_str(a)))
        }
    }
}

#[test]
fn parse_any() {
    let expected = Architecture { system: AnySystem,
                                  vendor: AnyVendor,
                                  cpu: AnyCpu };
    assert!(parse_arch("any") == Ok(expected));
}

#[test]
fn empty_string_is_invalid_architecture() {
    let arch = parse_arch("");
    assert!(arch == Err(ArchError::InvalidArchitecture(String::from_str(""))));
}

#[test]
fn too_many_parts_makes_an_architecture_invalid() {
    let text = "mswindows-somevendor-somerubish-i386";
    let arch = parse_arch(text);
    assert!(arch == Err(ArchError::InvalidArchitecture(String::from_str(text))));
}

#[test]
fn parse_windows_no_vendor() {
    let expected = Architecture { system: Windows,
                                  vendor: AnyVendor,
                                  cpu: I386 };
    let result = parse_arch("mswindows-i386");
    assert!(result.is_ok());
    assert!(result == Ok(expected));
}

#[test]
fn parse_windows_with_vendor() {
    let expected = Architecture {
        system: Windows,
        vendor: NamedVendor(String::from_str("somevendor")),
        cpu: I386
    };
    let result = parse_arch("mswindows-somevendor-i386");
    assert!(result.is_ok());
    assert!(result == Ok(expected));
}

#[test]
fn parse_windows_64() {
    let expected = Architecture {
        system: Windows,
        vendor: AnyVendor,
        cpu: AMD64
    };
    let result = parse_arch("mswindows-amd64");
    assert!(result.is_ok());
    assert!(result == Ok(expected));
}

#[test]
fn empty_system_is_an_error() {
    let a = parse_arch("-i386");
    assert!(a == Err(ArchError::InvalidSystem(String::from_str(""))));
}

// ------------------------------------------------------------------------
// Version
// ------------------------------------------------------------------------

#[derive(PartialEq, Eq, Debug, Clone)]
struct VersionChunk {
    prefix: String,
    number: isize
}

impl VersionChunk {
    fn new(prefix: &str, number: isize) -> VersionChunk {
        VersionChunk { prefix: String::from_str(prefix),
                       number: number }
    }
}

/// A package version consisting of an "upstream version" (the version of
/// the software being packaged) and the "package revision" which is the
/// version of the enclosing package.

#[derive(Eq, Debug, Clone)]
pub struct Version {
    epoch: isize,
    chunks: Vec<VersionChunk>,
    revision: String
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum VersionError {
    InvalidVersion (String),
    InvalidEpoch (String),
    InvalidPackageVersion (String)
}

impl VersionError {
    fn invalid(s: &str) -> VersionError {
        VersionError::InvalidVersion (String::from_str(s))
    }
    fn epoch(s: &str) -> VersionError {
        VersionError::InvalidEpoch(s.to_string())
    }
}

pub type VerResult<T> = Result<T, VersionError>;

/***
 * Extracts and parses the epoch value from a version string.
 *
 * On success, extract_epoch returns a pair containing the epoch integer and a
 * slice containing the remainder of the supplied string. A version with no
 * epoch is assumed to have epoch 0.
 *
 * On failure it will return a VersionError.
 *
 * For example,
 * ```
 * assert!(extract_epoch("42:1.2") == Ok((42, "1.2")));
 * assert!(extract_epoch("1.2") == Ok((0, "1.2")));
 * ```
 */
fn extract_epoch<'a>(s: &'a str) -> VerResult<(isize, &'a str)> {
    match s.find(':') {
        None => Ok((0, s)),
        Some(n) => {
            let text = s.slice_to(n);
            let epoch = match FromStr::from_str(text) {
                Ok(e) => e,
                Err(_) => return Err(VersionError::epoch(text))
            };
            let remainder = s.slice_from(n+1);
            Ok((epoch, remainder))
        }
    }
}

#[test]
fn no_epoch_returns_zero() {
    assert!(extract_epoch("42:12345") == Ok((42, "12345")));
}

#[test]
fn multiple_colons_is_not_an_error() {
    assert!(extract_epoch("1:2:3") == Ok((1, "2:3")));
}

#[test]
fn empty_epoch_is_an_error() {
    assert!(extract_epoch(":1") == Err(VersionError::epoch("")));
}

#[test]
fn non_integer_epoch_is_an_error() {
    let expected = Err(VersionError::epoch("narf"));
    let actual = extract_epoch("narf:2:3");
    assert!(expected == actual, "Expected: {:?}, got {:?}", expected, actual);
}

/**
 * Extracts the upstream version from a buffer, assuming any epoch text has
 * already been removed.
 */
fn extract_upstream<'a>(s: &'a str) -> Option<(&'a str, &'a str)> {
    match s.rfind('-') {
        Some(n) if n == s.len() - 1 => None,
        Some(n) => Some((s.slice_to(n), s.slice_from(n+1))),
        None => Some((s, ""))
    }
}

#[test]
fn no_seperator_in_upstream_version_returns_whole_string() {
    let expected = Some(("a.b.c.d", ""));
    let actual = extract_upstream("a.b.c.d");
    assert!(actual == expected,"Expected: {:?}, got: {:?}", expected, actual);
}

#[test]
fn trailing_revision_separator_reports_error_but_does_not_crash() {
    let expected = None;
    let actual = extract_upstream("a.b.c.d-");
    assert!(actual == expected, "expected: {:?}, got: {:?}", expected, actual);
}

/**
 * Parses the upstream version into a form that's easier to use with the debian
 * version sorting algorithm.
 */
fn parse_upstream(s: &str) -> VerResult<Vec<VersionChunk>> {
    let mut result = vec![];
    let mut text = s;
    while text.len() > 0 {
        // grab all leading nondigit characters
        let p = text.find(|&: c:char| c.is_digit(10)).unwrap_or(text.len());
        let prefix = text.slice_to(p);
        text = text.slice_from(p);

        debug!("p: {:?}, prefix: \"{:?}\", text: {:?}", p, prefix, text);

        // grab all leading digit chars
        let d = text.find(|&: c:char| !c.is_digit(10)).unwrap_or(text.len());
        let digits = text.slice_to(d);
        text = text.slice_from(d);

        debug!("d: {:?}, digits: \"{:?}\", text: {:?}", d, digits, text);

        let suffix : isize = FromStr::from_str(digits).unwrap_or(0);
        result.push(VersionChunk::new(prefix, suffix))
    }
    Ok(result)
}

#[test]
fn upstream_versions_with_trailing_chars_are_ok() {
    let expected = Ok(vec![VersionChunk::new("alpha.", 1), VersionChunk::new(".bravo", 0)]);
    let actual = parse_upstream("alpha.1.bravo");
    assert!(expected == actual, "expected: {:?}, got {:?}", expected, actual);
}

impl Version {
    // Attempts to parse a debian-style package version string.
    //
    // The version string contains an "upstream version" number and a
    // "package version" number, separated by a string.
    pub fn parse(v: &str) -> VerResult<Version> {
        let (epoch, text) = try!(extract_epoch(v));
        let (upstream, revision) = match extract_upstream(text) {
            Some((u, r)) => (u, r),
            None => return Err(VersionError::invalid(v))
        };

        let chunks = try!(parse_upstream(upstream));

        Ok(Version { epoch: epoch, chunks: chunks, revision: String::from_str(revision) })
    }
}

/**
 * Implements the debian version string comparison algorithm. This is basically
 * the normal ascii ordering, except that a tilde will sort before any other
 * character, living or dead.
 */
fn debian_cmp(a: &str, b: &str) -> cmp::Ordering {

    for (ca, cb) in a.chars().zip(b.chars()) {
        if ca != cb {
            if ca == '~' { return Less };
            if cb == '~' { return Greater };
            return if ca < cb { Less } else { Greater };
        }
    }

    // if we get to here we have exhausted at least one string. If we have
    // exhausted both strings, then the strings are equal. If not, then the
    // shorter string should always go first

    match (a.len() as isize) - (b.len() as isize) {
        n if n < 0 => Less,
        n if n > 0 => Greater,
        _ => Equal
    }
}

#[test]
fn debian_cmp_prefers_tildes() {
    assert!(debian_cmp("abcd~f", "abcdef") == Less);
    assert!(debian_cmp("abcdef", "abcd~f") == Greater);
}

#[test]
fn debian_cmp_lets_shorter_strings_go_first() {
    assert!(debian_cmp("abc", "abcdef") == Less);
    assert!(debian_cmp("abcdef", "abc") == Greater);
}

#[test]
fn debian_cmp_doesnt_crash_on_an_empty_string() {
    assert!(debian_cmp("", "abcdef") == Less);
    assert!(debian_cmp("abcdef", "") == Greater);
}

#[test]
fn debian_cmp_recognises_equal_strings() {
    assert!(debian_cmp("abcdef", "abcdef") == Equal);
    assert!(debian_cmp("abcdef", "abcdef") == Equal);
}

impl PartialEq<Version> for Version {
    fn eq(&self, other: &Version) -> bool {
        match self.partial_cmp(other) {
            Some(Equal) => true,
            Some(_) => false,
            None => {
                panic!("This should never, ever happen.");
                false
            }
        }
    }
}

impl PartialOrd for Version {
    fn partial_cmp(&self, other: &Version) -> Option<cmp::Ordering> {
        match self.epoch.cmp(&other.epoch) {
            Equal => {
                // compare the chunks left-to-right, as far as we can
                let mut chunks = self.chunks.iter().zip(other.chunks.iter());
                for (ref s, ref o) in chunks {
                    match debian_cmp(&s.prefix[], &o.prefix[]) {
                        Equal => {
                            match s.number.cmp(&o.number) {
                                Equal => {},
                                rval => return Some(rval)
                            }
                        },
                        rval => return Some(rval)
                    }
                };

                // If we get to here, then the chunks are the same up to the
                // point that at least one of the upstream version chunks is
                // exhausted. It's possible that one string of chunks is
                // longer, and the longer one should be considered larger
                // (e.g. 1.2.3 vs 1.2.3.4).
                match (self.chunks.len() as isize) - (other.chunks.len() as isize) {
                    n if n < 0 => return Some(Less),
                    n if n > 0 => return Some(Greater),
                    _ => {
                        // If both chunk strings are the same length, then
                        // compare the package revision and return that
                        let rval = debian_cmp(&self.revision[], &other.revision[]);
                        return Some(rval);
                    }
                }
            },
            rval => return Some(rval)
        }
    }
}

#[test]
fn dotted_decimal_versions_are_valid() {
    let expected = Ok(Version {
        epoch: 0,
        chunks: vec![ VersionChunk::new("",  1),
                      VersionChunk::new(".", 2),
                      VersionChunk::new(".", 3),
                      VersionChunk::new(".", 4)],
        revision: String::from_str("5")
    });
    let actual = Version::parse("1.2.3.4-5");
    assert!(expected == actual, "Expected: {:?}, got: {:?}", expected, actual);
}

#[test]
fn lexical_versions_are_valid() {
    let expected = Ok(Version {
        epoch: 0,
        chunks: vec![ VersionChunk::new("someversion", 0) ],
        revision: String::from_str("1")
    });
    let actual = Version::parse("someversion-1");
    assert!(expected == actual, "Expected: {:?}, got: {:?}", expected, actual);
}

#[test]
fn versions_are_comparable() {
    let a = Version { epoch: 0,
                      chunks: vec![ VersionChunk::new("",  1),
                                    VersionChunk::new(".", 2),
                                    VersionChunk::new(".", 3),
                                    VersionChunk::new(".", 4)],
                      revision: String::from_str("")
    };

    let b = Version { epoch: 0,
                      chunks: vec![ VersionChunk::new("",  1),
                                    VersionChunk::new(".", 2),
                                    VersionChunk::new(".", 3),
                                    VersionChunk::new(".", 5)],
                      revision: String::from_str("")
    };

    assert!(a < b);
    assert!(a != b);
    assert!(b > a);
}

#[test]
fn epochs_are_compared_first() {
    let a = Version {
        epoch: 1,
        chunks: vec![VersionChunk::new("a", 1)],
        revision: String::from_str("")
    };
    let b = Version {
        epoch: 2,
        chunks: vec![VersionChunk::new("a", 1)],
        revision: String::from_str("")
    };
    assert!(a < b);
    assert!(a != b);
    assert!(b > a);
}

#[test]
fn upstream_versions_chunk_prefixes_are_compared() {
    let a = Version {
        epoch: 0,
        chunks: vec![VersionChunk::new("a", 1)],
        revision: String::from_str("")
    };
    let b = Version {
        epoch: 0, chunks:
        vec![VersionChunk::new("b", 1)],
        revision: String::from_str("")
    };
    assert!(a < b);
    assert!(a != b);
    assert!(b > a);
}

#[test]
fn upstream_versions_chunk_numbers_are_compared() {
    let a = Version {epoch: 0, chunks: vec![VersionChunk::new("a", 1)], revision: String::from_str("")};
    let b = Version {epoch: 0, chunks: vec![VersionChunk::new("a", 2)], revision: String::from_str("")};
    assert!(a < b);
    assert!(b > a);
}

#[test]
fn upstream_version_superstring_wins() {
    let a = Version {epoch: 0, chunks: vec![VersionChunk::new("a", 1)], revision: String::from_str("")};
    let b = Version {
        epoch: 0,
        chunks: vec![
            VersionChunk::new("a", 1),
            VersionChunk::new("b", 2)
        ],
        revision: String::from_str("")
    };
    assert!(a < b);
    assert!(b > a);
}

#[test]
fn package_revision_breaks_ties() {
    let a = Version {epoch: 0, chunks: vec![VersionChunk::new("a", 1)], revision: String::from_str("1")};
    let b = Version {epoch: 0, chunks: vec![VersionChunk::new("a", 1)], revision: String::from_str("2")};
    assert!(a < b);
    assert!(b > a);
}

#[test]
fn tildes_sort_before_anything_else() {
    let a = Version {epoch: 0, chunks: vec![VersionChunk::new("~", 1)], revision: String::from_str("")};
    let b = Version {epoch: 0, chunks: vec![VersionChunk::new("a", 1)], revision: String::from_str("")};
    assert!(a < b);
    assert!(b > a);
}