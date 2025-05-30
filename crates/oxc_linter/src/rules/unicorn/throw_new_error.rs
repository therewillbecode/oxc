use oxc_ast::{AstKind, ast::Expression};
use oxc_diagnostics::OxcDiagnostic;
use oxc_macros::declare_oxc_lint;
use oxc_span::Span;

use crate::{
    AstNode,
    ast_util::{outermost_paren, outermost_paren_parent},
    context::LintContext,
    rule::Rule,
};

fn throw_new_error_diagnostic(span: Span) -> OxcDiagnostic {
    OxcDiagnostic::warn("Require `new` when throwing an error.")
        .with_help("Using `new` ensures the error is correctly initialized.")
        .with_label(span)
}

#[derive(Debug, Default, Clone)]
pub struct ThrowNewError;

declare_oxc_lint!(
    /// ### What it does
    ///
    /// This rule makes sure you always use `new` when throwing an error.
    ///
    /// ### Why is this bad?
    ///
    /// In JavaScript, omitting `new` (e.g., `throw Error('message')`) is allowed,
    /// but it does not properly initialize the error object. This can lead to missing
    /// stack traces or incorrect prototype chains. Using `new` makes the intent clear,
    /// ensures consistent behavior, and helps avoid subtle bugs.
    ///
    /// ### Examples
    ///
    /// Examples of **incorrect** code for this rule:
    /// ```javascript
    /// throw Error('🦄');
    /// throw TypeError('unicorn');
    /// throw lib.TypeError('unicorn');
    /// ```
    ///
    /// Examples of **correct** code for this rule:
    /// ```javascript
    /// throw new Error('🦄');
    /// throw new TypeError('unicorn');
    /// throw new lib.TypeError('unicorn');
    /// ```
    ThrowNewError,
    unicorn,
    style,
    fix
);

impl Rule for ThrowNewError {
    fn run<'a>(&self, node: &AstNode<'a>, ctx: &LintContext<'a>) {
        let AstKind::CallExpression(call_expr) = node.kind() else {
            return;
        };

        let Some(outermost_paren_node) = outermost_paren_parent(node, ctx) else {
            return;
        };

        let AstKind::ThrowStatement(_) = outermost_paren(outermost_paren_node, ctx).kind() else {
            return;
        };

        let name = match call_expr.callee.without_parentheses() {
            Expression::Identifier(v) => v.name,
            Expression::StaticMemberExpression(v) => v.property.name,
            _ => return,
        };

        if name.len() >= 5 && name.as_bytes()[0].is_ascii_uppercase() && name.ends_with("Error") {
            ctx.diagnostic_with_fix(throw_new_error_diagnostic(call_expr.span), |fixer| {
                fixer.insert_text_before_range(call_expr.span, "new ")
            });
        }
    }
}

#[test]
fn test() {
    use crate::tester::Tester;

    let pass = vec![
        ("throw new Error()", None),
        ("new Error()", None),
        ("throw new TypeError()", None),
        ("throw new EvalError()", None),
        ("throw new RangeError()", None),
        ("throw new ReferenceError()", None),
        ("throw new SyntaxError()", None),
        ("throw new URIError()", None),
        ("throw new CustomError()", None),
        ("throw new FooBarBazError()", None),
        ("throw new ABCError()", None),
        ("throw getError()", None),
        ("throw CustomError", None),
        ("throw getErrorConstructor()()", None),
        ("throw lib[Error]()", None),
        ("throw lib[\"Error\"]()", None),
        ("throw lib.getError()", None),
    ];

    let fail = vec![
        ("throw Error()", None),
        ("throw (Error)()", None),
        ("throw lib.Error()", None),
        ("throw lib.mod.Error()", None),
        ("throw lib[mod].Error()", None),
        ("throw (lib.mod).Error()", None),
        ("throw Error('foo')", None),
        ("throw CustomError('foo')", None),
        ("throw FooBarBazError('foo')", None),
        ("throw ABCError('foo')", None),
        ("throw Abc3Error('foo')", None),
        ("throw TypeError()", None),
        ("throw EvalError()", None),
        ("throw RangeError()", None),
        ("throw ReferenceError()", None),
        ("throw SyntaxError()", None),
        ("throw URIError()", None),
        ("throw (( URIError() ))", None),
        ("throw (( URIError ))()", None),
        ("throw getGlobalThis().Error()", None),
        ("throw utils.getGlobalThis().Error()", None),
        ("throw (( getGlobalThis().Error ))()", None),
    ];

    let fix = vec![
        ("throw Error()", "throw new Error()"),
        ("throw (( getGlobalThis().Error ))()", "throw new (( getGlobalThis().Error ))()"),
    ];

    Tester::new(ThrowNewError::NAME, ThrowNewError::PLUGIN, pass, fail)
        .expect_fix(fix)
        .test_and_snapshot();
}
