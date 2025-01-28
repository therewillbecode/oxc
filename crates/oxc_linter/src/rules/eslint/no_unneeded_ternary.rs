use oxc_ast::ast::{BooleanLiteral, ConditionalExpression, Expression};
use oxc_ast::AstKind;
use oxc_diagnostics::OxcDiagnostic;
use oxc_ecmascript::ToJsString;
use oxc_macros::declare_oxc_lint;
use oxc_span::Span;

use crate::{
    context::LintContext,
    fixer::{RuleFix, RuleFixer},
    rule::Rule,
    AstNode,
};

fn no_unneeded_ternary_diagnostic<'a>(span: Span) -> OxcDiagnostic {
    // See <https://oxc.rs/docs/contribute/linter/adding-rules.html#diagnostics> for details
    OxcDiagnostic::warn("Should be an imperative statement about what is wrong")
        .with_help("Should be a command-like statement that tells the user how to fix the issue")
        .with_label(span)
}

#[derive(Debug, Default, Clone)]
pub struct NoUnneededTernary;

declare_oxc_lint!(
    /// ### What it does
    ///
    /// This rule disallow ternary operators when simpler alternatives exist.
    ///
    /// It’s a common mistake in JavaScript to use a conditional expression to
    /// select between two Boolean values instead of using ! to convert the test
    /// to a Boolean.
    ///
    /// ### Why is this bad?
    ///
    /// Adds unnecessary complexity to conditional expressions.
    ///
    /// ### Examples
    ///
    /// Examples of **incorrect** code for this rule:
    ///
    /// ```js
    /// var isYes = answer === 1 ? true : false;
    /// ```
    ///
    /// ```js
    /// var isNo = answer === 1 ? false : true;
    /// ```
    ///
    /// ```js
    /// foo(bar ? bar : 1);
    /// ```
    ///
    /// Examples of **correct** code for this rule:
    ///
    /// ```js
    /// var isYes = answer === 1;
    /// ```
    ///
    /// ```js
    /// var isNo = answer !== 1;
    /// ```
    ///
    /// ```js
    /// foo(bar || 1);
    /// ```
    NoUnneededTernary,
    eslint,
    style,
    fix  // TODO: describe fix capabilities. Remove if no fix can be done,
             // keep at 'pending' if you think one could be added but don't know how.
             // Options are 'fix', 'fix_dangerous', 'suggestion', and 'conditional_fix_suggestion'
);

#[derive(Debug, Clone)]
enum UnneededTernary {
    TrueFalse, // test ? true : false
    FalseTrue, // test ? false : true
}

// Todo - need to add call to  expr.without_parentheses()
// to cover cases liek (true) : ((false))
/// For `test ? cons : alt` do we have a redundant ternary?
fn is_ternary_unneeded<'a>(node: &ConditionalExpression<'a>) -> Option<UnneededTernary> {
    match (node.consequent.get_inner_expression(), node.alternate.get_inner_expression()) {
        (Expression::BooleanLiteral(expr_cons), Expression::BooleanLiteral(expr_alt)) => {
            println!("{} {}", (*expr_cons).value, (*expr_alt).value);

            match ((*expr_cons).value, (*expr_alt).value) {
                (true, false) => Some(UnneededTernary::TrueFalse),
                (false, true) => Some(UnneededTernary::FalseTrue),
                (_, _) => None,
            }
        }
        (_, _) => None,
    }
}

impl Rule for NoUnneededTernary {
    fn run<'a>(&self, node: &AstNode<'a>, ctx: &LintContext<'a>) {
        if let AstKind::ConditionalExpression(node) = node.kind() {
            //            println!("{}", is_ternary_unneeded(node).is_some());
            if let Some(UnneededTernary::TrueFalse) = is_ternary_unneeded(node) {
                ctx.diagnostic_with_fix(no_unneeded_ternary_diagnostic(node.span), |fixer| {
                    //  Replace `test ? true : false` with just `test`.
                    fixer.replace_with(node, &node.test)
                })
            }
        }
    }
}

#[test]
fn test() {
    use crate::tester::Tester;

    let pass = vec![
        ("config.newIsCap = config.newIsCap !== false", None),
        ("var a = x === 2 ? 'Yes' : 'No';", None),
        ("var a = x === 2 ? true : 'No';", None),
        ("var a = x === 2 ? 'Yes' : false;", None),
        ("var a = x === 2 ? 'true' : 'false';", None),
        ("var a = foo ? foo : bar;", None),
        ("var value = 'a';var canSet = true;var result = value || (canSet ? 'unset' : 'can not set')", None),
        ("var a = foo ? bar : foo;", None),
        ("foo ? bar : foo;", None),
        ("var a = f(x ? x : 1)", None),
        ("f(x ? x : 1);", None),
        ("foo ? foo : bar;", None),
        ("var a = foo ? 'Yes' : foo;", None),
        ("var a = foo ? 'Yes' : foo;", Some(serde_json::json!([{ "defaultAssignment": false }]))),
        ("var a = foo ? bar : foo;", Some(serde_json::json!([{ "defaultAssignment": false }]))),
        ("foo ? bar : foo;", Some(serde_json::json!([{ "defaultAssignment": false }])))
    ];

    let fail = vec![
        ("var a = x === 2 ? true : false;", None),
        ("var a = x >= 2 ? true : false;", None),
        // ("var a = x ? true : false;", None),
        // ("var a = x === 1 ? false : true;", None),
        // ("var a = x != 1 ? false : true;", None),
        // ("var a = foo() ? false : true;", None),
        // ("var a = !foo() ? false : true;", None),
        // ("var a = foo + bar ? false : true;", None),
        // ("var a = x instanceof foo ? false : true;", None),
        // ("var a = foo ? false : false;", None),
        // ("var a = foo() ? false : false;", None),
        // ("var a = x instanceof foo ? true : false;", None),
        // ("var a = !foo ? true : false;", None),
        // (
        //     "
        //		                var value = 'a'
        //		                var canSet = true
        //		                var result = value ? value : canSet ? 'unset' : 'can not set'
        //    ",
        //     Some(serde_json::json!([{ "defaultAssignment": false }])),
        // ),
        // (
        //     "foo ? foo : (bar ? baz : qux)",
        //     Some(serde_json::json!([{ "defaultAssignment": false }])),
        // ),
        // (
        //     "function* fn() { foo ? foo : yield bar }",
        //     Some(serde_json::json!([{ "defaultAssignment": false }])),
        // ), // { "ecmaVersion": 6 },
        // ("var a = foo ? foo : 'No';", Some(serde_json::json!([{ "defaultAssignment": false }]))),
        // (
        //     "var a = ((foo)) ? (((((foo))))) : ((((((((((((((bar))))))))))))));",
        //     Some(serde_json::json!([{ "defaultAssignment": false }])),
        // ),
        // ("var a = b ? b : c => c;", Some(serde_json::json!([{ "defaultAssignment": false }]))), // { "ecmaVersion": 2015 },
        // ("var a = b ? b : c = 0;", Some(serde_json::json!([{ "defaultAssignment": false }]))), // { "ecmaVersion": 2015 },
        // ("var a = b ? b : (c => c);", Some(serde_json::json!([{ "defaultAssignment": false }]))), // { "ecmaVersion": 2015 },
        // ("var a = b ? b : (c = 0);", Some(serde_json::json!([{ "defaultAssignment": false }]))), // { "ecmaVersion": 2015 },
        // ("var a = b ? b : (c) => (c);", Some(serde_json::json!([{ "defaultAssignment": false }]))), // { "ecmaVersion": 2015 },
        // (
        //     "var a = b ? b : c, d; // this is ((b ? b : c), (d))",
        //     Some(serde_json::json!([{ "defaultAssignment": false }])),
        // ), // { "ecmaVersion": 2015 },
        // ("var a = b ? b : (c, d);", Some(serde_json::json!([{ "defaultAssignment": false }]))), // { "ecmaVersion": 2015 },
        // ("f(x ? x : 1);", Some(serde_json::json!([{ "defaultAssignment": false }]))),
        // ("x ? x : 1;", Some(serde_json::json!([{ "defaultAssignment": false }]))),
        // ("var a = foo ? foo : bar;", Some(serde_json::json!([{ "defaultAssignment": false }]))),
        // ("var a = foo ? foo : a ?? b;", Some(serde_json::json!([{ "defaultAssignment": false }]))), // { "ecmaVersion": 2020 },
        // ("foo as any ? false : true", None), // {                "parser": require(parser("typescript-parsers/unneeded-ternary-1")),                "ecmaVersion": 6            },
        // ("foo ? foo : bar as any", Some(serde_json::json!([{ "defaultAssignment": false }]))), // {                "parser": require(parser("typescript-parsers/unneeded-ternary-2")),                "ecmaVersion": 6            }
    ];

    let fix = vec![
        ("var a = x === 2 ? true : false;", "var a = x === 2;", None),
        //   ("var a = x >= 2 ? true : false;", "var a = x >= 2;", None),
        //   ("var a = x ? true : false;", "var a = !!x;", None),
        //   ("var a = x === 1 ? false : true;", "var a = x !== 1;", None),
        //   ("var a = x != 1 ? false : true;", "var a = x == 1;", None),
        //   ("var a = foo() ? false : true;", "var a = !foo();", None),
        //   ("var a = !foo() ? false : true;", "var a = !!foo();", None),
        //   ("var a = foo + bar ? false : true;", "var a = !(foo + bar);", None),
        //   ("var a = x instanceof foo ? false : true;", "var a = !(x instanceof foo);", None),
        //   ("var a = foo ? false : false;", "var a = false;", None),
        //   ("var a = x instanceof foo ? true : false;", "var a = x instanceof foo;", None),
        //   ("var a = !foo ? true : false;", "var a = !foo;", None),
        //   (
        //       "
        //		                var value = 'a'
        //		                var canSet = true
        //		                var result = value ? value : canSet ? 'unset' : 'can not set'
        //		            ",
        //       "
        //		                var value = 'a'
        //		                var canSet = true
        //		                var result = value || (canSet ? 'unset' : 'can not set')
        //		            ",
        //       Some(serde_json::json!([{ "defaultAssignment": false }])),
        //   ),
        //   (
        //       "foo ? foo : (bar ? baz : qux)",
        //       "foo || (bar ? baz : qux)",
        //       Some(serde_json::json!([{ "defaultAssignment": false }])),
        //   ),
        //   (
        //       "function* fn() { foo ? foo : yield bar }",
        //       "function* fn() { foo || (yield bar) }",
        //       Some(serde_json::json!([{ "defaultAssignment": false }])),
        //   ),
        //   (
        //       "var a = foo ? foo : 'No';",
        //       "var a = foo || 'No';",
        //       Some(serde_json::json!([{ "defaultAssignment": false }])),
        //   ),
        //   (
        //       "var a = ((foo)) ? (((((foo))))) : ((((((((((((((bar))))))))))))));",
        //       "var a = ((foo)) || ((((((((((((((bar))))))))))))));",
        //       Some(serde_json::json!([{ "defaultAssignment": false }])),
        //   ),
        //   (
        //       "var a = b ? b : c => c;",
        //       "var a = b || (c => c);",
        //       Some(serde_json::json!([{ "defaultAssignment": false }])),
        //   ),
        //   (
        //       "var a = b ? b : c = 0;",
        //       "var a = b || (c = 0);",
        //       Some(serde_json::json!([{ "defaultAssignment": false }])),
        //   ),
        //   (
        //       "var a = b ? b : (c => c);",
        //       "var a = b || (c => c);",
        //       Some(serde_json::json!([{ "defaultAssignment": false }])),
        //   ),
        //   (
        //       "var a = b ? b : (c = 0);",
        //       "var a = b || (c = 0);",
        //       Some(serde_json::json!([{ "defaultAssignment": false }])),
        //   ),
        //   (
        //       "var a = b ? b : (c) => (c);",
        //       "var a = b || ((c) => (c));",
        //       Some(serde_json::json!([{ "defaultAssignment": false }])),
        //   ),
        //   (
        //       "var a = b ? b : c, d; // this is ((b ? b : c), (d))",
        //       "var a = b || c, d; // this is ((b ? b : c), (d))",
        //       Some(serde_json::json!([{ "defaultAssignment": false }])),
        //   ),
        //   (
        //       "var a = b ? b : (c, d);",
        //       "var a = b || (c, d);",
        //       Some(serde_json::json!([{ "defaultAssignment": false }])),
        //   ),
        //   ("f(x ? x : 1);", "f(x || 1);", Some(serde_json::json!([{ "defaultAssignment": false }]))),
        //   ("x ? x : 1;", "x || 1;", Some(serde_json::json!([{ "defaultAssignment": false }]))),
        //   (
        //       "var a = foo ? foo : bar;",
        //       "var a = foo || bar;",
        //       Some(serde_json::json!([{ "defaultAssignment": false }])),
        //   ),
        //   (
        //       "var a = foo ? foo : a ?? b;",
        //       "var a = foo || (a ?? b);",
        //       Some(serde_json::json!([{ "defaultAssignment": false }])),
        //   ),
        //   ("foo as any ? false : true", "!(foo as any)", None),
        //   (
        //       "foo ? foo : bar as any",
        //       "foo || (bar as any)",
        //       Some(serde_json::json!([{ "defaultAssignment": false }])),
        //   ),
    ];
    Tester::new(NoUnneededTernary::NAME, NoUnneededTernary::PLUGIN, pass, fail)
        .expect_fix(fix)
        .test_and_snapshot();
}
