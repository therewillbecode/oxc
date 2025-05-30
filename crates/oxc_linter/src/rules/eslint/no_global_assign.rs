use oxc_diagnostics::OxcDiagnostic;
use oxc_macros::declare_oxc_lint;
use oxc_span::{CompactStr, Span};

use crate::{config::GlobalValue, context::LintContext, rule::Rule};

fn no_global_assign_diagnostic(global_name: &str, span: Span) -> OxcDiagnostic {
    OxcDiagnostic::warn(format!("Read-only global '{global_name}' should not be modified."))
        .with_label(span.label(format!("Read-only global '{global_name}' should not be modified.")))
}

#[derive(Debug, Default, Clone)]
pub struct NoGlobalAssign(Box<NoGlobalAssignConfig>);

#[derive(Debug, Default, Clone)]
pub struct NoGlobalAssignConfig {
    excludes: Vec<CompactStr>,
}

impl std::ops::Deref for NoGlobalAssign {
    type Target = NoGlobalAssignConfig;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

declare_oxc_lint!(
    /// ### What it does
    ///
    /// Disallow modifications to read-only global variables.
    ///
    /// ### Why is this bad?
    ///
    /// In almost all cases, you don’t want to assign a value to these global variables as doing so could result in losing access to important functionality.
    ///
    /// ### Examples
    ///
    /// Examples of **incorrect** code for this rule:
    /// ```javascript
    /// Object = null
    /// ```
    NoGlobalAssign,
    eslint,
    correctness
);

impl Rule for NoGlobalAssign {
    fn from_configuration(value: serde_json::Value) -> Self {
        let obj = value.get(0);

        Self(Box::new(NoGlobalAssignConfig {
            excludes: obj
                .and_then(|v| v.get("exceptions"))
                .and_then(serde_json::Value::as_array)
                .unwrap_or(&vec![])
                .iter()
                .map(serde_json::Value::as_str)
                .filter(Option::is_some)
                .map(|x| x.unwrap().into())
                .collect::<Vec<CompactStr>>(),
        }))
    }

    fn run_once(&self, ctx: &LintContext) {
        let symbol_table = ctx.scoping();
        for (name, reference_id_list) in ctx.scoping().root_unresolved_references() {
            for &reference_id in reference_id_list {
                let reference = symbol_table.get_reference(reference_id);
                if reference.is_write()
                    && !self.excludes.iter().any(|n| n == name)
                    && ctx
                        .get_global_variable_value(name)
                        .is_some_and(|global| global == GlobalValue::Readonly)
                {
                    ctx.diagnostic(no_global_assign_diagnostic(
                        name,
                        ctx.semantic().reference_span(reference),
                    ));
                }
            }
        }
    }
}

#[test]
fn test() {
    use crate::tester::Tester;

    let pass = vec![
        ("string='1';", None, None),
        ("var string;", None, None),
        ("Object = 0;", Some(serde_json::json!([{ "exceptions": ["Object"] }])), None),
        ("top = 0;", None, None),
        (
            "onload = 0;",
            None,
            Some(serde_json::json!({
                "env": {
                    "browser": true
                }
            })),
        ),
        ("require = 0;", None, None),
        ("window[parseInt('42', 10)] = 99;", None, None),
        (
            "a = 1",
            None,
            Some(serde_json::json!({
                "globals": {
                    "a": true
                }
            })),
        ),
        // ("/*global a:true*/ a = 1", None),
    ];

    let fail = vec![
        ("String = 'hello world';", None, None),
        ("String++;", None, None),
        ("({Object = 0, String = 0} = {});", None, None),
        (
            "top = 0;",
            None,
            Some(serde_json::json!({
                "env": {
                    "browser": true
                }
            })),
        ),
        (
            "require = 0;",
            None,
            Some(serde_json::json!({
                "env": {
                    "node": true
                }
            })),
        ),
        ("function f() { Object = 1; }", None, None),
        (
            "a = 1",
            None,
            Some(serde_json::json!({
                "globals": {
                    "a": false
                }
            })),
        ),
        // ("/*global b:false*/ function f() { b = 1; }", None),
        // ("/*global b:false*/ function f() { b++; }", None),
        // ("/*global b*/ b = 1;", None),
        ("Array = 1;", None, None),
    ];

    Tester::new(NoGlobalAssign::NAME, NoGlobalAssign::PLUGIN, pass, fail).test_and_snapshot();
}
