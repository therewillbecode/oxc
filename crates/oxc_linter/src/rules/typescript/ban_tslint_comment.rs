use lazy_regex::{Lazy, Regex, lazy_regex};
use oxc_diagnostics::OxcDiagnostic;
use oxc_macros::declare_oxc_lint;
use oxc_span::Span;

use crate::{context::LintContext, rule::Rule};

fn ban_tslint_comment_diagnostic(tslint_comment: &str, span: Span) -> OxcDiagnostic {
    OxcDiagnostic::warn(format!("tslint comment detected: \"{tslint_comment}\"")).with_label(span)
}

#[derive(Debug, Default, Clone)]
pub struct BanTslintComment;

declare_oxc_lint!(
    /// ### What it does
    ///
    /// This rule disallows `tslint:<rule-flag>` comments
    ///
    /// ### Why is this bad?
    ///
    /// Useful when migrating from TSLint to ESLint. Once TSLint has been
    /// removed, this rule helps locate TSLint annotations
    ///
    /// ### Examples
    ///
    /// Examples of **incorrect** code for this rule:
    /// ```ts
    /// // tslint:disable-next-line
    /// someCode();
    /// ```
    ///
    /// Examples of **correct** code for this rule:
    /// ```ts
    /// someCode();
    /// ```
    BanTslintComment,
    typescript,
    style,
    fix
);

static ENABLE_DISABLE_REGEX: Lazy<Regex> =
    lazy_regex!(r"^\s*tslint:(enable|disable)(?:-(line|next-line))?(:|\s|$)");

impl Rule for BanTslintComment {
    fn run_once(&self, ctx: &LintContext) {
        let comments = ctx.comments();
        for comment in comments {
            let raw = ctx.source_range(comment.content_span());
            if ENABLE_DISABLE_REGEX.is_match(raw) {
                let comment_span = get_full_comment(ctx, comment.span);
                ctx.diagnostic_with_fix(
                    ban_tslint_comment_diagnostic(raw.trim(), comment_span),
                    |fixer| fixer.delete_range(comment_span),
                );
            }
        }
    }
}

fn get_full_comment(ctx: &LintContext, span: Span) -> Span {
    let mut span = span;

    let source_size = u32::try_from(ctx.source_text().len()).unwrap();
    let tokens = ctx.source_range(Span::new(span.end, source_size));

    // Take into account new line at the end of the comment
    if matches!(tokens.chars().next(), Some('\n')) {
        span.end += 1;
    }

    span
}

#[test]
fn test() {
    use crate::tester::Tester;

    let pass = vec![
        r"let a: readonly any[] = [];",
        r"let a = new Array();",
        r"// some other comment",
        r"// TODO: this is a comment that mentions tslint",
        r"/* another comment that mentions tslint */",
        r"someCode(); // This is a comment that just happens to mention tslint",
    ];

    let fail = vec![
        r"/* tslint:disable */",
        r"/* tslint:enable */",
        r"/* tslint:disable:rule1 rule2 rule3... */",
        r"/* tslint:enable:rule1 rule2 rule3... */",
        r"// tslint:disable-next-line",
        r"someCode(); // tslint:disable-line",
        r"// tslint:disable-next-line:rule1 rule2 rule3...",
        r"const woah = doSomeStuff();
        // tslint:disable-line
        console.log(woah);
        ",
    ];

    let fix = vec![
        (
            r"const woah = doSomeStuff();
        // tslint:disable-line
        console.log(woah);",
            r"const woah = doSomeStuff();
                console.log(woah);",
            None,
        ),
        (
            r"const woah = doSomeStuff();
        /* tslint:disable-line */
        console.log(woah);",
            r"const woah = doSomeStuff();
                console.log(woah);",
            None,
        ),
        (r"/* tslint:disable-line */", r"", None),
        // Issue: <https://github.com/oxc-project/oxc/issues/8090>
        (r"/*tslint:disable*/É", r"É", None),
    ];

    Tester::new(BanTslintComment::NAME, BanTslintComment::PLUGIN, pass, fail)
        .expect_fix(fix)
        .test_and_snapshot();
}
