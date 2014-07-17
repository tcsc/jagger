//use std::string;

mod architecture {

    #[deriving(PartialEq, Show)]
    enum Error { 
        UnknownAlias (String),
        InvalidArchitecture (String),
        InvalidSystem (String),
        InvalidVendor (String),
        InvalidCpu (String)
    }

   #[deriving(PartialEq, Show)]
   enum System {
        AnySystem,
        Linux,
        Windows,
        Darwin,
        CustomSystem (String)
    }

    #[deriving(PartialEq, Show)]
    enum Vendor {
        AnyVendor,
        Vendor (String)
    }

    #[deriving(PartialEq, Show)]
    enum Cpu {
        AnyCpu,
        I386,
        AMD64,
        CustomCpu (String)
    }

    #[deriving(PartialEq, Show)]
    struct Architecture {
        system: System,
        vendor: Vendor,
        cpu: Cpu
    }

    fn parse_alias(a: &str) -> Result<Architecture, Error> {
        match a {
            "any" => Ok(Architecture{ system: AnySystem, vendor: AnyVendor, cpu: AnyCpu }),
            "win32" => Ok(Architecture{ system: Windows, vendor: AnyVendor, cpu: I386 }),
            "win64" => Ok(Architecture{ system: Windows, vendor: AnyVendor, cpu: AMD64 }),
            _ => Err(UnknownAlias(String::from_str(a)))
        }
    }

    fn parse_system(a: &str) -> Result<System, Error> {
        match a {
            "any" => Ok(AnySystem),
            "mswindows"  => Ok(Windows),
            "linux" => Ok(Linux),
            "darwin" => Ok(Darwin),
            "" => Err(InvalidSystem(String::from_str(a))),
            _ => Ok(CustomSystem(String::from_str(a)))
        }
    }

    fn parse_cpu(a: &str) -> Result<Cpu, Error> {
        match a {
            "any" => Ok(AnyCpu),
            "i386" => Ok(I386),
            "amd64" => Ok(AMD64),
            "" => Err(InvalidCpu(String::from_str(a))), // invalid
            _ => Ok(CustomCpu(String::from_str(a)))
        }
    }

    #[test]
    fn empty_cpu_is_an_error() {
        assert!(parse_cpu("") == Err(InvalidCpu(String::from_str(""))))
    }

    #[test]
    fn any_cpu_is_a_special_case() {
        assert!(parse_cpu("any") == Ok(AnyCpu))
    }

    fn parse_vendor(a: &str) -> Result<Vendor, Error> {
        match a {
            "any" => Ok(AnyVendor),
            "" => Err(InvalidVendor(String::from_str(a))), // Invalid
            v => Ok(Vendor(String::from_str(v)))
        }
    }

    #[test]
    fn empty_vendor_is_an_error() {
        assert!(parse_vendor("") == Err(InvalidVendor(String::from_str(""))));
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
    fn parse_arch(a: &str) -> Result<Architecture, Error> {
        if a == "" { 
            Err(InvalidArchitecture(String::from_str(a)))
        }
        else {
            let part_strings : Vec<&str> = a.split('-').collect();
            let parts = part_strings.as_slice();
            match parts.len() {
                1 => parse_alias(parts[0]),
                n @ 2 .. 3 => {
                    let system = try!(parse_system(parts[0]));
                    let cpu = try!(parse_cpu(parts[parts.len()-1]));
                    let vendor_name = if n == 2 { "any" } else { parts[1] };
                    let vendor = try!(parse_vendor(vendor_name));
                    Ok( Architecture {system: system, vendor: vendor, cpu: cpu} )
                }

                _ => Err(InvalidArchitecture(String::from_str(a)))
            }
        }
    }

    #[test]
    fn parse_any() {
        let expected = Architecture { system: AnySystem, vendor: AnyVendor, cpu: AnyCpu };
        assert!(parse_arch("any") == Ok(expected));
    }

    #[test]
    fn empty_string_is_invalid_architecture() {
        let arch = parse_arch("");
        assert!(arch == Err(InvalidArchitecture(String::from_str(""))));
    }

    #[test]
    fn too_many_parts_makes_an_architecture_invalid() {
        let text = "mswindows-somevendor-somerubish-i386";
        let arch = parse_arch(text);
        print!("arch: {}\n", arch);
        assert!(arch == Err(InvalidArchitecture(String::from_str(text))));
    }

    #[test]
    fn parse_windows_no_vendor() {
        let expected = Architecture {system: Windows, vendor: AnyVendor, cpu: I386};
        let result = parse_arch("mswindows-i386");
        assert!(result.is_ok());
        assert!(result == Ok(expected));      
    }

    #[test]
    fn parse_windows_with_vendor() {
        let expected = Architecture {
            system: Windows, 
            vendor: Vendor(String::from_str("somevendor")), 
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
        assert!(a == Err(InvalidSystem(String::from_str(""))));
    }
}

mod version {

}

fn main() {

}