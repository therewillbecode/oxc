#[cfg(feature = "full")]
mod compiler;

#[cfg(feature = "full")]
pub use compiler::{Compiler, CompilerInterface};

pub mod allocator {
    //! Memory arena allocator used by all other submodules.
    //!
    //! See the [`oxc_allocator` module-level documentation](oxc_allocator) for more information.
    #[doc(inline)]
    pub use oxc_allocator::*;
}

pub mod ast {
    #[doc(inline)]
    pub use oxc_ast::*;
}

#[cfg(feature = "ast_visit")]
pub mod ast_visit {
    #[doc(inline)]
    pub use oxc_ast_visit::*;
}

pub mod diagnostics {
    //! Error data types and utilities for handling/reporting them.
    //!
    //! See the [`oxc_diagnostics` module-level documentation](oxc_diagnostics) for more information.
    #[doc(inline)]
    pub use oxc_diagnostics::*;
}

pub mod parser {
    //! JavaScript/TypeScript parser.
    //!
    //! See the [`oxc_parser` module-level documentation](oxc_parser) for more information.
    #[doc(inline)]
    pub use oxc_parser::*;
}

#[cfg(feature = "regular_expression")]
pub mod regular_expression {
    #[doc(inline)]
    pub use oxc_regular_expression::*;
}

pub mod span {
    //! Source text Span and string types.
    //!
    //! See the [`oxc_span` module-level documentation](oxc_span) for more information.
    #[doc(inline)]
    pub use oxc_span::*;
}

pub mod syntax {
    //! Common code for JavaScript Syntax
    //!
    //! See the [`oxc_syntax` module-level documentation](oxc_syntax) for more information.
    #[doc(inline)]
    pub use oxc_syntax::*;
}

#[cfg(feature = "semantic")]
pub mod semantic {
    //! Semantic analysis of a JavaScript/TypeScript program.
    //!
    //! See the [`oxc_semantic` module-level documentation](oxc_semantic) for more information.
    #[doc(inline)]
    pub use oxc_semantic::*;
}

#[cfg(feature = "transformer")]
pub mod transformer {
    //! Transformer/Transpiler
    //!
    //! See the [`oxc_transformer` module-level documentation](oxc_transformer) for more
    //! information.
    #[doc(inline)]
    pub use oxc_transformer::*;
}

#[cfg(feature = "transformer")]
pub mod transformer_plugins {
    //! Transformer/Transpiler
    //!
    //! See the [`oxc_transformer_plugins` module-level documentation](oxc_transformer_plugins) for more
    //! information.
    #[doc(inline)]
    pub use oxc_transformer_plugins::*;
}

#[cfg(feature = "minifier")]
pub mod minifier {
    //! Source code minifier.
    //!
    //! See the [`oxc_minifier` module-level documentation](oxc_minifier) for more information.
    #[doc(inline)]
    pub use oxc_minifier::*;
}

#[cfg(feature = "mangler")]
pub mod mangler {
    #[doc(inline)]
    pub use oxc_mangler::*;
}

#[cfg(feature = "codegen")]
pub mod codegen {
    //! AST code printer
    //!
    //! See the [`oxc_codegen` module-level documentation](oxc_codegen) for more information.
    #[doc(inline)]
    pub use oxc_codegen::*;
}

#[cfg(feature = "isolated_declarations")]
pub mod isolated_declarations {
    //! `.d.ts` emit for Isolated Declarations.
    //!
    //! See the [`oxc_isolated_declarations` module-level documentation](oxc_isolated_declarations)
    //! for more information.
    #[doc(inline)]
    pub use oxc_isolated_declarations::*;
}

#[cfg(feature = "cfg")]
pub mod cfg {
    #[doc(inline)]
    pub use oxc_cfg::*;
}
