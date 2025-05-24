use oxc_span::{ContentEq, GetSpan};

#[cfg(test)]
mod test {
    use oxc_allocator::{Allocator, Box, IntoIn, Vec};
    use oxc_ast::ast::{BooleanLiteral, Expression, LogicalExpression, LogicalOperator};
    use oxc_codegen::{Codegen, CodegenOptions};

    use oxc_span::Span;
    use oxc_syntax::es_target::ESTarget;
    use proptest::prelude::*;

    fn bool_lit_strat(alloc: &Allocator) -> impl Strategy<Value = Expression<'static>> {
        (proptest::bool::weighted(0.5)).prop_map(move |x| {
            let b = BooleanLiteral { span: Span::empty(0), value: x };
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

    static ALLOC: std::sync::LazyLock<oxc_allocator::Allocator> =
        std::sync::LazyLock::new(|| Allocator::default());

    // test that AST -> codegen -> AST roundtrips
    proptest! {
            #[test]
            fn ast_logical_expr_rndtrips(inital_logic_exp in nested_logical_expr_strat(&ALLOC)) {

                // AST -> Source Text
                let mut codegen = Codegen::new();
                codegen.print_expression(&inital_logic_exp);

                let original_source_text: String = codegen.into_source_text();


    println!("{}", original_source_text);

           // Source Text -> AST
            let  parseOpt = oxc_parser::ParseOptions::default();
                let parsed_ast = oxc_parser::Parser::new(&ALLOC, &original_source_text, oxc_ast::ast::SourceType::ts())
               .with_options(parseOpt)
               .parse();

        // get the only single expression in the parsed AST so we can compare
        // against the original we generated with proptest
           let fst_ast_statement = parsed_ast.program.body.first().unwrap();
           let expr_stat: &Box<'_,oxc_ast::ast::ExpressionStatement> = match fst_ast_statement {
               oxc_ast::ast::Statement::ExpressionStatement(expr_statement)=>
                 expr_statement,
             _ => panic!("Unexpected, shoould only be a single expression statement")
           };


           //  if show_ast {
            //   println!("AST:");
          //     println!("{parsed_ast_program:#?}");
               //}

               // AST -> SourceText -> Ast -> SourceTxt2, the SourceTxt2 should be unchanged.

               let rnd_tripped_logic_exp: &Expression<'_> = &expr_stat.expression;

               let mut codegen_two = Codegen::new();
                      codegen_two.print_expression(rnd_tripped_logic_exp);
                let roundtripped_source_text: String = codegen_two.into_source_text();
                 assert_eq!(original_source_text.as_str(), roundtripped_source_text.as_str());
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

    // Parser
    //
    // Ensuring AST for TypeScript types is aligned with the standard "TS-ESLint" to ensure
    // tool interopability.
    //
    // https://github.com/oxc-project/oxc/issues/9705
    //
    // // test roundtripping from our AST to back again produces the same ast
    // test that AST -> codegen -> Parse with TS-ESLINT -> Print with TS-ESLINT -> codegen -> BackTo Our AST
}
