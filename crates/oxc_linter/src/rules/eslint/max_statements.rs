use oxc_diagnostics::OxcDiagnostic;
use oxc_macros::declare_oxc_lint;
use oxc_span::Span;
use serde_json::Value;
use  oxc_ast::AstKind;

use crate::{
    AstNode,
    context::LintContext,
    rule::Rule,
};

fn max_statements_diagnostic(span: Span) -> OxcDiagnostic {
    // See <https://oxc.rs/docs/contribute/linter/adding-rules.html#diagnostics> for details
    OxcDiagnostic::warn("Should be an imperative statement about what is wrong")
        .with_help("Should be a command-like statement that tells the user how to fix the issue")
        .with_label(span)
}

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
    MaxStatements,
    eslint,
    pedantic
);

#[derive(Debug, Default, Clone)]
pub struct MaxStatements(Box<MaxStatementsConfig>);

#[derive(Debug, Clone)]
pub struct MaxStatementsConfig {
    pub max: usize,
    pub ignore_top_level_functions: bool,
}

impl Default for MaxStatementsConfig {
    fn default() -> Self {
        Self { max: 10, ignore_top_level_functions: false }
    }
}

impl Rule for MaxStatements {
    fn from_configuration(value: serde_json::Value) -> Self {
        let config = value.get(0);
        if let Some(max) = config
            .and_then(Value::as_number)
            .and_then(serde_json::Number::as_u64)
            .and_then(|v| usize::try_from(v).ok())
        {
            Self(Box::new(MaxStatementsConfig { max, ignore_top_level_functions: false }))
        } else {
            let default_max = 10;
            let max = value
                .get(0)
                .and_then(|config| config.get("max"))
                .and_then(serde_json::Value::as_number)
                .and_then(serde_json::Number::as_u64)
                .map_or(default_max, |v| usize::try_from(v).unwrap_or(default_max));

            let ignore_top_level_functions = value
                .get(0)
                .and_then(|config| config.get("ignoreTopLevelFunctions"))
                .and_then(serde_json::Value::as_bool)
                .unwrap_or(false);

            Self(Box::new(MaxStatementsConfig { max, ignore_top_level_functions }))
        }
    }

    fn run<'a>(&self, node: &AstNode<'a>, ctx: &LintContext<'a>) {
        match &node.kind() {
            AstKind::FunctionBody(b) => {
                let config: &MaxStatementsConfig = &self.0;

                let Some(f) : Option< &AstNode<'a>> = ctx.nodes().parent_node(node.node_id) else {
                    return;
                };

                match f {

AstKind::Function(func) => {

}
                }


//let func_decl = ctx.symbols().get_declaration(func_ident);
// let is_top_level: bool = ctx.scopes().get_flags(func_decl.scope_id()).is_top();

                 println!("is top level {is_top_level:?}, scope id {0:?}", node);
                if config.ignore_top_level_functions && is_top_level {
                    return;
                }

                println!("statements {0:?}, but max is {1:?}", b.statements.len(), self.0.max);

                if b.statements.len() > self.0.max {
                    println!("awoooooo");
                    ctx.diagnostic(max_statements_diagnostic(b.span))
                }
            }
            _ => {}
        }
    }
}

#[test]
fn test() {
    use crate::tester::Tester;

    let pass = vec![
        (
            "function foo() { var bar = 1; function qux () { var noCount = 2; } return 3; }",
            Some(serde_json::json!([3])),
        ),
        (
            "function foo() { var bar = 1; if (true) { for (;;) { var qux = null; } } else { quxx(); } return 3; }",
            Some(serde_json::json!([6])),
        ),
        (
            "function foo() { var x = 5; function bar() { var y = 6; } bar(); z = 10; baz(); }",
            Some(serde_json::json!([5])),
        ),
        (
            "function foo() { var a; var b; var c; var x; var y; var z; bar(); baz(); qux(); quxx(); }",
            None,
        ),
//(
//    "(function() { var bar = 1; return function () { return 42; }; })()",
//    Some(serde_json::json!([1, { "ignoreTopLevelFunctions": true }])),
//),
        (
            "function foo() { var bar = 1; var baz = 2; }",
            Some(serde_json::json!([1, { "ignoreTopLevelFunctions": true }])),
        ),
        (
            "define(['foo', 'qux'], function(foo, qux) { var bar = 1; var baz = 2; })",
            Some(serde_json::json!([1, { "ignoreTopLevelFunctions": true }])),
        ),
        (
            "var foo = { thing: function() { var bar = 1; var baz = 2; } }",
            Some(serde_json::json!([2])),
        ),
        ("var foo = { thing() { var bar = 1; var baz = 2; } }", Some(serde_json::json!([2]))), // { "ecmaVersion": 6 },
        ("var foo = { ['thing']() { var bar = 1; var baz = 2; } }", Some(serde_json::json!([2]))), // { "ecmaVersion": 6 },
        ("var foo = { thing: () => { var bar = 1; var baz = 2; } }", Some(serde_json::json!([2]))), // { "ecmaVersion": 6 },
        (
            "var foo = { thing: function() { var bar = 1; var baz = 2; } }",
            Some(serde_json::json!([{ "max": 2 }])),
        ),
        (
            "class C { static { one; two; three; { four; five; six; } } }",
            Some(serde_json::json!([2])),
        ), // { "ecmaVersion": 2022 },
        (
            "function foo() { class C { static { one; two; three; { four; five; six; } } } }",
            Some(serde_json::json!([2])),
        ), // { "ecmaVersion": 2022 },
        (
            "class C { static { one; two; three; function foo() { 1; 2; } four; five; six; } }",
            Some(serde_json::json!([2])),
        ), // { "ecmaVersion": 2022 },
        (
            "class C { static { { one; two; three; function foo() { 1; 2; } four; five; six; } } }",
            Some(serde_json::json!([2])),
        ), // { "ecmaVersion": 2022 },
        (
            "function top_level() { 1; /* 2 */ class C { static { one; two; three; { four; five; six; } } } 3;}",
            Some(serde_json::json!([2, { "ignoreTopLevelFunctions": true }])),
        ), // { "ecmaVersion": 2022 },
        (
            "function top_level() { 1; 2; } class C { static { one; two; three; { four; five; six; } } }",
            Some(serde_json::json!([1, { "ignoreTopLevelFunctions": true }])),
        ), // { "ecmaVersion": 2022 },
        (
            "class C { static { one; two; three; { four; five; six; } } } function top_level() { 1; 2; } ",
            Some(serde_json::json!([1, { "ignoreTopLevelFunctions": true }])),
        ), // { "ecmaVersion": 2022 },
        (
            "function foo() { let one; let two = class { static { let three; let four; let five; if (six) { let seven; let eight; let nine; } } }; }",
            Some(serde_json::json!([2])),
        ), // { "ecmaVersion": 2022 }
    ];
    // let _pass = vec![];

    let fail = vec![
        ("function foo() { var bar = 1; var baz = 2; var qux = 3; }", Some(serde_json::json!([2]))),
        (
            "var foo = () => { var bar = 1; var baz = 2; var qux = 3; };",
            Some(serde_json::json!([2])),
        ), // { "ecmaVersion": 6 },
        (
            "var foo = function() { var bar = 1; var baz = 2; var qux = 3; };",
            Some(serde_json::json!([2])),
        ),
        (
            "function foo() { var bar = 1; if (true) { while (false) { var qux = null; } } return 3; }",
            Some(serde_json::json!([4])),
        ),
        (
            "function foo() { var bar = 1; if (true) { for (;;) { var qux = null; } } return 3; }",
            Some(serde_json::json!([4])),
        ),
        (
            "function foo() { var bar = 1; if (true) { for (;;) { var qux = null; } } else { quxx(); } return 3; }",
            Some(serde_json::json!([5])),
        ),
        (
            "function foo() { var x = 5; function bar() { var y = 6; } bar(); z = 10; baz(); }",
            Some(serde_json::json!([3])),
        ),
        (
            "function foo() { var x = 5; function bar() { var y = 6; } bar(); z = 10; baz(); }",
            Some(serde_json::json!([4])),
        ),
        (
            ";(function() { var bar = 1; return function () { var z; return 42; }; })()",
            Some(serde_json::json!([1, { "ignoreTopLevelFunctions": true }])),
        ),
        (
            ";(function() { var bar = 1; var baz = 2; })(); (function() { var bar = 1; var baz = 2; })()",
            Some(serde_json::json!([1, { "ignoreTopLevelFunctions": true }])),
        ),
        (
            "define(['foo', 'qux'], function(foo, qux) { var bar = 1; var baz = 2; return function () { var z; return 42; }; })",
            Some(serde_json::json!([1, { "ignoreTopLevelFunctions": true }])),
        ),
        (
            "function foo() { var a; var b; var c; var x; var y; var z; bar(); baz(); qux(); quxx(); foo(); }",
            None,
        ),
        (
            "var foo = { thing: function() { var bar = 1; var baz = 2; var baz2; } }",
            Some(serde_json::json!([2])),
        ),
        (
            "var foo = { thing() { var bar = 1; var baz = 2; var baz2; } }",
            Some(serde_json::json!([2])),
        ), // { "ecmaVersion": 6 },
        (
            "var foo = { thing: () => { var bar = 1; var baz = 2; var baz2; } }",
            Some(serde_json::json!([2])),
        ), // { "ecmaVersion": 6 },
        (
            "var foo = { thing: function() { var bar = 1; var baz = 2; var baz2; } }",
            Some(serde_json::json!([{ "max": 2 }])),
        ),
        ("function foo() { 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; }", Some(serde_json::json!([{}]))),
        ("function foo() { 1; }", Some(serde_json::json!([{ "max": 0 }]))),
        (
            "function foo() { foo_1; /* foo_ 2 */ class C { static { one; two; three; four; { five; six; seven; eight; } } } foo_3 }",
            Some(serde_json::json!([2])),
        ), // { "ecmaVersion": 2022 },
        (
            "class C { static { one; two; three; four; function not_top_level() { 1; 2; 3; } five; six; seven; eight; } }",
            Some(serde_json::json!([2, { "ignoreTopLevelFunctions": true }])),
        ), // { "ecmaVersion": 2022 },
        (
            "class C { static { { one; two; three; four; function not_top_level() { 1; 2; 3; } five; six; seven; eight; } } }",
            Some(serde_json::json!([2, { "ignoreTopLevelFunctions": true }])),
        ), // { "ecmaVersion": 2022 },
        (
            "class C { static { { one; two; three; four; } function not_top_level() { 1; 2; 3; } { five; six; seven; eight; } } }",
            Some(serde_json::json!([2, { "ignoreTopLevelFunctions": true }])),
        ), // { "ecmaVersion": 2022 }
    ];

    Tester::new(MaxStatements::NAME, MaxStatements::PLUGIN, pass, fail).test_and_snapshot();
}
