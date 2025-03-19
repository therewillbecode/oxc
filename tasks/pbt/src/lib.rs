use oxc_ast::{NONE, ast::*};
use oxc_ecmascript::side_effects::MayHaveSideEffects;
use oxc_span::{ContentEq, GetSpan};
use oxc_syntax::es_target::ESTarget;

#[cfg(test)]
mod test {
    use oxc_allocator::{Allocator, Box, IntoIn, Vec};
    use oxc_ast::ast::{BooleanLiteral, Expression, LogicalExpression, LogicalOperator};
    use oxc_codegen::{CodeGenerator, CodegenOptions};
    use oxc_span::Span;
    use oxc_syntax::es_target::ESTarget;
    use proptest::prelude::*;

    fn bool_lit_strat (alloc: &Allocator) -> impl Strategy<Value = Expression<'static>> {
        (proptest::bool::weighted(0.5)).prop_map(move |x| {
            let b = BooleanLiteral { span: Span::empty(0), value: x };
            //let alloc = Allocator::default();
            Expression::BooleanLiteral(Box::new_in(b, &alloc))
        })
    }

    fn logical_expr_strat(alloc: &Allocator) -> impl Strategy<Value = Expression<'_>> {
        (
            prop_oneof![Just(LogicalOperator::Or), Just(LogicalOperator::And),],
            bool_lit_strat(alloc),
            bool_lit_strat(alloc),
        )
            .prop_map(|(op, l, r)| {
                // let lb = BooleanLiteral { span: Span::empty(0), value: x };
                // let rb = BooleanLiteral { span: Span::empty(0), value: y };
                let left: Expression = l;
                let right: Expression = r;
                let operator: LogicalOperator = op;
                let span: Span = Span::empty(0);
                let a = LogicalExpression { left, right, operator, span };

                Expression::LogicalExpression(Box::new_in(a, alloc))
            })
    }

    fn nested_logical_expr_strat(
        alloc: &'static Allocator,
    ) -> impl Strategy<Value = Expression<'static>> {
        let leaf = prop_oneof![bool_lit_strat(alloc)];
        leaf.prop_recursive(
            4,  // 3 levels deep
            20, // Shoot for maximum size of 16 nodes
            4,  // We put up to 3 items per collection
            move |inner| {
                (logical_expr_strat(alloc), inner).prop_map(move |(logical_exp, inner_exp)| {
                    Expression::LogicalExpression(Box::new_in(
                        LogicalExpression {
                            left: logical_exp,
                            right: inner_exp,
                            operator: LogicalOperator::Or,
                            span: Span::empty(0),
                        },
                        alloc,
                    ))
                })
            },
        )
    }

    /*

    fn nested_logical_expr_strat() -> impl Strategy<Value = Json> {
        let leaf = prop_oneof![
            bool_lit_strat(),
            any::<bool>().prop_map(Json::Bool),
            any::<f64>().prop_map(Json::Number),
            ".*".prop_map(Json::String),
        ];
        leaf.prop_recursive(
          8, // 8 levels deep
          256, // Shoot for maximum size of 256 nodes
          10, // We put up to 10 items per collection
          |inner| prop_oneof![
              // Take the inner strategy and make the two recursive cases.
              prop::collection::vec(inner.clone(), 0..10)
                  .prop_map(Json::Array),
              prop::collection::hash_map(".*", inner, 0..10)
                  .prop_map(Json::Map),
          ])
    }
     */
    static ALLOC: std::sync::LazyLock<oxc_allocator::Allocator> =
        std::sync::LazyLock::new(|| Allocator::default());

    // test that AST -> codegen -> AST roundtrips
    proptest! {
            #[test]
            fn doesnt_crash(cond in nested_logical_expr_strat(&ALLOC)) {

              //  let alloc = Allocator::new(); // ugh no

                //let ad = a.
                //let mut program = ret.program;
                let mut codegen = CodeGenerator::new();
                codegen.print_expression(&cond);
                let s: String = codegen.into_source_text();
    println!("{}", s);

           assert_eq!(s.as_str(), s.as_str() );//"false || false");
            }
        }

//    test that AST -> codegen -> lint --fix - > Always parses
//    proptest! {
//            #[test]
//            fn doesnt_crash(cond in nested_logical_expr_strat(&ALLOC)) {
//
//            }
//        }
//
//
//    test that AST -> codegen -> Minifier - > Always parses
//    proptest! {
//            #[test]
//            fn doesnt_crash(cond in nested_logical_expr_strat(&ALLOC)) {
//
//            }
//        }
//
//     test that AST -> codegen -> prettier - > Always parses
//    proptest! {
//            #[test]
//            fn doesnt_crash(cond in nested_logical_expr_strat(&ALLOC)) {
//
//            }
//        }
//

}
