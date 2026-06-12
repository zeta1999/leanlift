//! Machine-integer types and function signatures (the v1 scope: kernels over
//! fixed-width integers, shape `f(a,b,c,…) -> r`). This is what lets the oracle
//! emit a correctly-typed C++ call for any arity/width instead of assuming
//! `(u64,…)->u64`.

/// An unsigned machine integer type. (Signed/float widths are a later step.)
/// `U8`/`U16` are supported by the oracle codegen but not yet exercised by a
/// built-in example.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[allow(dead_code)]
pub enum IntType {
    U8,
    U16,
    U32,
    U64,
}

impl IntType {
    pub fn bits(self) -> u32 {
        match self {
            IntType::U8 => 8,
            IntType::U16 => 16,
            IntType::U32 => 32,
            IntType::U64 => 64,
        }
    }

    /// The Aeneas `Std.U*` type name (for the extracted-model runner/proof).
    pub fn aeneas_name(self) -> &'static str {
        match self {
            IntType::U8 => "Std.U8",
            IntType::U16 => "Std.U16",
            IntType::U32 => "Std.U32",
            IntType::U64 => "Std.U64",
        }
    }

    /// The C/C++ fixed-width type name used in the generated oracle runner.
    pub fn c_name(self) -> &'static str {
        match self {
            IntType::U8 => "uint8_t",
            IntType::U16 => "uint16_t",
            IntType::U32 => "uint32_t",
            IntType::U64 => "uint64_t",
        }
    }

    /// The Go fixed-width type name.
    pub fn go_name(self) -> &'static str {
        match self {
            IntType::U8 => "uint8",
            IntType::U16 => "uint16",
            IntType::U32 => "uint32",
            IntType::U64 => "uint64",
        }
    }

    /// The Solidity fixed-width type name.
    pub fn sol_name(self) -> &'static str {
        match self {
            IntType::U8 => "uint8",
            IntType::U16 => "uint16",
            IntType::U32 => "uint32",
            IntType::U64 => "uint64",
        }
    }
}

/// A function signature: ordered argument types and a single return type.
#[derive(Clone, Debug)]
pub struct Signature {
    pub args: Vec<IntType>,
    pub ret: IntType,
}

impl Signature {
    pub fn arity(&self) -> usize {
        self.args.len()
    }
}
