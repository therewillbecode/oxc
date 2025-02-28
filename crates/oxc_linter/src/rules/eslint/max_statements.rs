use oxc_ast::AstKind;
use oxc_ast::ast::Function;
use oxc_diagnostics::OxcDiagnostic;
use oxc_macros::declare_oxc_lint;
use oxc_semantic::{ScopeId, Semantic};
use oxc_span::{GetSpan, Span};
use serde_json::Value;

use crate::{AstNode, ast_util::{iter_outer_expressions, outermost_paren_parent}, context::LintContext, rule::Rule};

fn max_statements_diagnostic(span: Span, count: usize, max: usize) -> OxcDiagnostic {
    OxcDiagnostic::warn(format!(
        "Function has too many statements ({count:?}). Maximum allowed is {max:?}."
    ))
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

/*
/// Iterate over parent nodes and see if callee contains span of the node.
fn is_iife<'a>(node: &AstNode<'a>, ctx: &LintContext, semantic: &Semantic<'a>) -> bool {
    let Some(AstKind::CallExpression(call)) = iter_outer_expressions(semantic, node.id()).next()
    else {
        return false;
    };
    call.callee.span().contains_inclusive(node.span())
}
 */

/// Returns true if the closed enclosing function body for this function is declared at the top
/// level scope.
///
/// do we? We call this recursively until there is no enclosing parent function around the
/// function declaration.
fn func_declared_top_level<'a>(ctx: &LintContext<'a>, func: &Function) -> bool {
    // could be faster when func.is_declaration() == true to just use func.scope_id and not get the declaration

    let decl_scope_id = if let Some(ident) = &func.id {

        // function with an identifier so go to declaration
        let symbols = ctx.semantic().symbols();
        println!("1111111111111");

        let func_decl_symbol_id = symbols.get_declaration(ident.symbol_id());
        ctx.nodes().get_node(func_decl_symbol_id).scope_id()
    } else {
        println!("2222222 {func:?}");

        // Anonymous function so just use the scope id of this node which declares the function binding
        func.scope_id()
    };

//if let Some(top_level_reference) =
  //      resolve_global_binding(ident, decl_scope_id, ctx)

    ctx.scopes().get_flags(decl_scope_id).is_top()

    //todo NEED TO CALL THIS RECURSEIVELY ON EACH FUNCTION BODY CONTAINING THIS ONE
}

impl Rule for MaxStatements {
    fn from_configuration(value: serde_json::Value) -> Self {
        let default_max = 10;

        println!("config {value:?}");

        let max_statements =
        // option is just a usize like 8.
   value
            .get(0)
            .and_then(Value::as_number)
            .and_then(serde_json::Number::as_u64)
            .and_then(|v| usize::try_from(v).ok())
            .unwrap_or(default_max);

        let Some(vec_config) = value.as_array() else {
            return Self(Box::new(MaxStatementsConfig {
                max: max_statements,
                ignore_top_level_functions: false,
            }));
        };

        let ignore_top_level_functions = vec_config
            .get(1)
            .and_then(|config| config.get("ignoreTopLevelFunctions"))
            .and_then(serde_json::Value::as_bool)
            .unwrap_or(false);

        println!("ignore con {ignore_top_level_functions:?}");
        Self(Box::new(MaxStatementsConfig { max: max_statements, ignore_top_level_functions }))
    }

    fn run<'a>(&self, node: &AstNode<'a>, ctx: &LintContext<'a>) {
        match &node.kind() {
            AstKind::FunctionBody(b) => {
                let config: &MaxStatementsConfig = &self.0;

                let Some(f): Option<&AstNode<'a>> = ctx.nodes().parent_node(node.id()) else {
                    return;
                };

                match f.kind() {
                    AstKind::Function(func) => {
                        if config.ignore_top_level_functions {
//println!("1111");
//if is_iife(node, ctx, ctx.semantic()) {
//println!("IIFE");
//println!("IIFE");
//} else {
//println!("not IIFE");
//}

                            if func_declared_top_level(ctx, func) {
                                return;
                            }
                        }
                        let top_level: bool = func_declared_top_level(ctx, func);
                        println!(
                            "is top {0:?}, config ignore top level: {1:?}",
                            top_level, config.ignore_top_level_functions
                        );

                        println!(
                            "statements {0:?}, but max is {1:?}",
                            b.statements.len(),
                            self.0.max
                        );

                        let count = b.statements.len();
                        let max = self.0.max;
                        if count > max {
                            println!("awoooooo");
                            ctx.diagnostic(max_statements_diagnostic(b.span, count, max))
                        }
                    }
                    _ => {}
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
        //(
        //    "function foo() { var bar = 1; function qux () { var noCount = 2; } return 3; }",
        //    Some(serde_json::json!([3])),
        //),
        //(
        //    "function foo() { var bar = 1; if (true) { for (;;) { var qux = null; } } else { quxx(); } return 3; }",
        //    Some(serde_json::json!([6])),
        //),
        //(
        //    "function foo() { var x = 5; function bar() { var y = 6; } bar(); z = 10; baz(); }",
        //    Some(serde_json::json!([5])),
        //),
        //(
        //    "function foo() { var a; var b; var c; var x; var y; var z; bar(); baz(); qux(); quxx(); }",
        //    None,
        //),
        (
            "(function() { var bar = 1; return function () { return 42; }; })()",
            Some(serde_json::json!([1, { "ignoreTopLevelFunctions": true }])),
        ),
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
