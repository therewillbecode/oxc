use oxc_diagnostics::OxcDiagnostic;
use oxc_macros::declare_oxc_lint;
use oxc_span::Span;

use crate::{
    context::LintContext,
    fixer::{RuleFix, RuleFixer},
    rule::Rule,
    AstNode,
};

fn no_lonely_if_diagnostic(span: Span) -> OxcDiagnostic {
    // See <https://oxc.rs/docs/contribute/linter/adding-rules.html#diagnostics> for details
    OxcDiagnostic::warn("Should be an imperative statement about what is wrong")
        .with_help("Should be a command-like statement that tells the user how to fix the issue")
        .with_label(span)
}

#[derive(Debug, Default, Clone)]
pub struct NoLonelyIf;

declare_oxc_lint!(
    /// ### What it does
    ///
    ///
    /// ### Why is this bad?
    ///
    ///
    /// ### Examples
    ///
    /// Examples of **incorrect** code for this rule:
    /// ```js
    /// FIXME: Tests will fail if examples are missing or syntactically incorrect.
    /// ```
    ///
    /// Examples of **correct** code for this rule:
    /// ```js
    /// FIXME: Tests will fail if examples are missing or syntactically incorrect.
    /// ```
    NoLonelyIf,
    eslint,
    nursery, // TODO: change category to `correctness`, `suspicious`, `pedantic`, `perf`, `restriction`, or `style`
             // See <https://oxc.rs/docs/contribute/linter.html#rule-category> for details

    pending  // TODO: describe fix capabilities. Remove if no fix can be done,
             // keep at 'pending' if you think one could be added but don't know how.
             // Options are 'fix', 'fix_dangerous', 'suggestion', and 'conditional_fix_suggestion'
);

impl Rule for NoLonelyIf {
    fn run<'a>(&self, node: &AstNode<'a>, ctx: &LintContext<'a>) {}
}

#[test]
fn test() {
    use crate::tester::Tester;

    let pass = vec![
        "if (a) {;} else if (b) {;}",
        "if (a) {;} else { if (b) {;} ; }",
        "if (a) if (a) {} else { if (b) {} } else {}",
    ];

    let fail = vec![
        "if (a) {;} else { if (b) {;} }",
        "if (foo) {} else { if (bar) baz(); }",
        "if (foo) {} else { if (bar) baz() } qux();",
        "if (foo) {} else { if (bar) baz(); } qux();",
    ];

    let fix = vec![
        ("if (a) {;} else { if (b) {;} }", "if (a) {;} else if (b) {;}", None),
        ("if (foo) {} else { if (bar) baz(); }", "if (foo) {} else if (bar) baz();", None),
        (
            "if (foo) {} else { if (bar) baz(); } qux();",
            "if (foo) {} else if (bar) baz(); qux();",
            None,
        ),
    ];
    Tester::new(NoLonelyIf::NAME, NoLonelyIf::PLUGIN, pass, fail)
        .expect_fix(fix)
        .test_and_snapshot();
}
