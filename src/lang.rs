//! Source languages the engine can lift from. Each pairs with an oracle strategy
//! (§6): C++/Go compile to native code and run; Solidity executes on an EVM.

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Lang {
    Cpp,
    Go,
    Solidity,
}

impl Lang {
    /// Human name, also used as the Markdown fence tag in LLM prompts.
    pub fn fence(self) -> &'static str {
        match self {
            Lang::Cpp => "cpp",
            Lang::Go => "go",
            Lang::Solidity => "solidity",
        }
    }
}
