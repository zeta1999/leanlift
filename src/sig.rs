//! Machine value types and function signatures. The v1 scope was fixed-width
//! **integer** kernels, shape `f(a,b,c,…) -> r`; this now also admits **float**
//! kernels (f32/f64). A `Ty` is either an `IntType` (checked-integer path) or a
//! `FloatType` (the bit-exact IEEE-754 differential path — `double`/`float` in
//! C++ vs Lean's native binary64/32 `Float`, compared by bit pattern).

/// An unsigned machine integer type. (Signed widths are a later step.)
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

/// An IEEE-754 binary floating-point type. The differential oracle treats a
/// float value as its **bit pattern** (a `uint32_t`/`uint64_t` carrier), so the
/// whole vector/join-key/compare machinery is reused unchanged: C++ `double` and
/// Lean's native `Float` agree bit-for-bit on `+ - * / sqrt` under
/// `-ffp-contract=off` (verified on arm64), and a NaN payload is canonicalized.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[allow(dead_code)]
pub enum FloatType {
    F32,
    F64,
}

impl FloatType {
    pub fn bits(self) -> u32 {
        match self {
            FloatType::F32 => 32,
            FloatType::F64 => 64,
        }
    }

    /// The C/C++ floating type used in the kernel ABI.
    pub fn c_name(self) -> &'static str {
        match self {
            FloatType::F32 => "float",
            FloatType::F64 => "double",
        }
    }

    /// The unsigned C carrier the bit pattern travels in (`memcpy` target).
    pub fn carrier_c(self) -> &'static str {
        match self {
            FloatType::F32 => "uint32_t",
            FloatType::F64 => "uint64_t",
        }
    }
}

/// A machine value type: an integer (checked-arithmetic path) or a float
/// (bit-exact IEEE-754 differential path).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Ty {
    Int(IntType),
    Float(FloatType),
}

impl Ty {
    pub fn bits(self) -> u32 {
        match self {
            Ty::Int(t) => t.bits(),
            Ty::Float(f) => f.bits(),
        }
    }

    pub fn c_name(self) -> &'static str {
        match self {
            Ty::Int(t) => t.c_name(),
            Ty::Float(f) => f.c_name(),
        }
    }

    pub fn is_float(self) -> bool {
        matches!(self, Ty::Float(_))
    }

    pub fn float(self) -> Option<FloatType> {
        match self {
            Ty::Float(f) => Some(f),
            Ty::Int(_) => None,
        }
    }

    // The integer-only backends (Aeneas/Go/Solidity) never carry a float
    // argument — those paths are integer kernels only.
    pub fn aeneas_name(self) -> &'static str {
        match self {
            Ty::Int(t) => t.aeneas_name(),
            Ty::Float(_) => unreachable!("float types do not go through the Aeneas backend"),
        }
    }
    pub fn go_name(self) -> &'static str {
        match self {
            Ty::Int(t) => t.go_name(),
            Ty::Float(_) => unreachable!("float types do not go through the Go oracle"),
        }
    }
    pub fn sol_name(self) -> &'static str {
        match self {
            Ty::Int(t) => t.sol_name(),
            Ty::Float(_) => unreachable!("float types do not go through the Solidity oracle"),
        }
    }
}

/// A function signature: ordered argument types and a single return type.
#[derive(Clone, Debug)]
pub struct Signature {
    pub args: Vec<Ty>,
    pub ret: Ty,
}

impl Signature {
    pub fn arity(&self) -> usize {
        self.args.len()
    }

    /// A float kernel — its values travel as IEEE bit patterns and are compared
    /// bit-exactly (with NaN canonicalization), not through the checked-`Res`
    /// integer monad. All our float kernels are uniformly typed, so the return
    /// type discriminates the path.
    pub fn is_float(&self) -> bool {
        self.ret.is_float()
    }

    /// The float type of a float signature (panics if integer).
    pub fn float_ty(&self) -> FloatType {
        self.ret.float().expect("float_ty on an integer signature")
    }
}
