use vstd::prelude::*;

verus! {

#[macro_export]
macro_rules! vprint {
    ($($arg:tt)*) => {
        #[cfg(not(verus_only))]
        {
        use $crate::print::*;
        let s = format!($($arg)*);
        print(&s)
    }
        #[cfg(verus_only)]
        {
        }
    };
}

#[macro_export]
macro_rules! veprint {
    ($($arg:tt)*) => {
        #[cfg(not(verus_only))]
        {
        use $crate::print::*;
        let s = format!($($arg)*);
        eprint(&s)
    }
        #[cfg(verus_only)]
        {
        }
    };
}

#[macro_export]
macro_rules! vprintln {
    ($($arg:tt)*) => {
        #[cfg(not(verus_only))]
        {
        use $crate::print::*;
        let s = format!($($arg)*);
        println(&s)
        }
        #[cfg(verus_only)]
        {
        }
    };
}

#[macro_export]
macro_rules! veprintln {
    ($($arg:tt)*) => {
        #[cfg(not(verus_only))]
        {
        use $crate::print::*;
        let s = format!($($arg)*);
        eprintln(&s)
        }
        #[cfg(verus_only)]
        {
        }
    };
}

#[verifier::external_body]
pub fn print(s: &str) {
    print!("{s}");
}

#[verifier::external_body]
pub fn eprint(s: &str) {
    eprint!("{s}");
}

#[verifier::external_body]
pub fn println(s: &str) {
    println!("{s}");
}

#[verifier::external_body]
pub fn eprintln(s: &str) {
    eprintln!("{s}");
}

// ExFmtArguments/the `std::fmt::format` spec used to be declared here, but
// vstd::std_specs::fmt now provides both natively (as ExArguments and the
// `alloc::fmt::format` spec), so declaring them again here is a duplicate specification error.
} // verus!
