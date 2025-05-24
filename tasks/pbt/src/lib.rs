use oxc_span::{ContentEq, GetSpan};

#[cfg(test)]
mod test {
    use oxc_allocator::{Allocator, Box, IntoIn, Vec};
    use oxc_ast::ast::{
        BooleanLiteral, ConditionalExpression, Expression, ExpressionStatement, LogicalExpression,
        LogicalOperator, ParenthesizedExpression, Program, Statement, TSAsExpression,
        TSBooleanKeyword, TSType, TSTypeLiteral, UnaryExpression, UnaryOperator,
    };
    use oxc_codegen::{Codegen, CodegenOptions, Context, Gen};

    use oxc_mangler::MangleOptions;
    use oxc_minifier::{CompressOptions, Minifier, MinifierOptions};
    use oxc_parser::Parser;
    use oxc_span::{ContentEq, SourceType};

    use oxc_span::Span;
    use oxc_syntax::es_target::ESTarget;
    use proptest::prelude::*;
    use std::process::Command;

    use std::fs::File;
    use std::io::Result;
    use std::io::prelude::*;

    fn write_file(file_path: &str, contents: &str) -> Result<()> {
        let mut file = File::create(file_path)?;
        file.write_all(contents.as_bytes())
    }

    fn bool_lit_strat(alloc: &Allocator) -> impl Strategy<Value = Expression<'static>> {
        (proptest::bool::weighted(0.5), proptest::bool::weighted(0.15)).prop_map(
            move |(x, cast_as)| {
                let b = BooleanLiteral { span: Span::empty(0), value: x };

                if cast_as {
                    let inner = Expression::BooleanLiteral(Box::new_in(b, &alloc));
                    let a = TSAsExpression {
                        expression: inner,
                        span: Span::empty(0),
                        type_annotation: TSType::TSBooleanKeyword(Box::new_in(
                            TSBooleanKeyword { span: Span::empty(0) },
                            &alloc,
                        )),
                    };
                    Expression::TSAsExpression(Box::new_in(a, &alloc))
                } else {
                    Expression::BooleanLiteral(Box::new_in(b, &alloc))
                }
            },
        )
    }

    fn logical_expr_strat(alloc: &Allocator) -> impl Strategy<Value = Expression<'_>> {
        (
            prop_oneof![Just(LogicalOperator::Or), Just(LogicalOperator::And)],
            bool_lit_strat(alloc),
            bool_lit_strat(alloc),
            proptest::bool::weighted(0.65),
        )
            .prop_map(|(op, l, r, is_negated)| {
                let left: Expression = l;
                let right: Expression = r;
                let operator: LogicalOperator = op;
                let span: Span = Span::empty(0);
                let a = LogicalExpression { left, right, operator, span };

                if !is_negated {
                    Expression::LogicalExpression(Box::new_in(a, alloc))
                } else {
                    Expression::UnaryExpression(Box::new_in(
                        UnaryExpression {
                            span: Span::empty(0),
                            operator: UnaryOperator::LogicalNot,
                            argument: Expression::LogicalExpression(Box::new_in(a, alloc)),
                        },
                        alloc,
                    ))
                }
            })
    }

    fn nested_logical_expr_strat(
        alloc: &'static Allocator,
    ) -> impl Strategy<Value = Expression<'static>> {
        let leaf = prop_oneof![bool_lit_strat(alloc)];
        let is_negated = proptest::bool::weighted(0.25);
        let is_and = proptest::bool::weighted(0.50);

        leaf.prop_recursive(
            40, // 3 levels deep
            30, // Shoot for maximum size of 16 nodes
            2,  // We put up to 3 items per collection
            move |inner| {
                (logical_expr_strat(alloc), is_negated, is_and, inner).prop_map(
                    move |(logical_exp, is_negated, is_and, inner_exp)| {
                        let operator =
                            if is_and { LogicalOperator::And } else { LogicalOperator::Or };

                        Expression::LogicalExpression(Box::new_in(
                            LogicalExpression {
                                left: logical_exp,
                                right: inner_exp,
                                operator,
                                span: Span::empty(0),
                            },
                            alloc,
                        ))
                    },
                )
            },
        )
    }

    fn conditional_expr(alloc: &'static Allocator) -> impl Strategy<Value = Expression<'static>> {
        (
            prop_oneof![bool_lit_strat(alloc), nested_logical_expr_strat(alloc)],
            prop_oneof![bool_lit_strat(alloc), nested_logical_expr_strat(alloc)],
            prop_oneof![bool_lit_strat(alloc), nested_logical_expr_strat(alloc)],
        )
            .prop_map(|(l, r, t)| {
                let test: Expression = t;
                let alternate: Expression = l;
                let consequent: Expression = r;
                let span: Span = Span::empty(0);
                let cond = ConditionalExpression { test, alternate, consequent, span };

                Expression::ConditionalExpression(Box::new_in(cond, alloc))
            })
    }

    fn gen_expr_statement(alloc: &'static Allocator) -> impl Strategy<Value = Statement<'static>> {
        (prop_oneof![conditional_expr(alloc)]).prop_map(|expr| {
            let ex = ExpressionStatement { span: Span::empty(0), expression: expr };
            Statement::ExpressionStatement(Box::new_in(ex, alloc))
        })
    }

    fn gen_program(alloc: &'static Allocator) -> impl Strategy<Value = Program<'static>> {
        (prop_oneof![gen_expr_statement(alloc)]).prop_map(|expr| {
            let mut body: Vec<'_, Statement> = Vec::new_in(&ALLOC);

            body.push(expr);

            let init_program: Program = Program {
                span: Span::empty(0),
                comments: Vec::new_in(&ALLOC),
                directives: Vec::new_in(&ALLOC),
                body: body.into_in(&ALLOC),
                hashbang: None,
                source_text: "",
                source_type: oxc_ast::ast::SourceType::ts(),
                scope_id: Default::default(),
            };

            return init_program;
        })
    }

    // test that AST -> codegen ->  fmt -> parse doesnt crash
    proptest! {
            #[test]
            fn ast_expr_code_gen_fmts_parses_again(inital_logic_exp in conditional_expr(&ALLOC)) {

                // AST -> Source Text
                let mut codegen = Codegen::new();
                //   codegen.print_str("return ");

                codegen.print_expression(&inital_logic_exp);


                let original_source_text: String = codegen.into_source_text();


    println!("{}", original_source_text);

           // Source Text -> AST -> Fmt -> Fmted Source Text
            let  parseOpt = oxc_parser::ParseOptions::default();
                let parsed_ast = oxc_parser::Parser::new(&ALLOC, &original_source_text, oxc_ast::ast::SourceType::ts())
               .with_options(parseOpt)
               .parse();

            let fmt_options = oxc_formatter::FormatOptions::default();
             let fmted_src =
             oxc_formatter::Formatter::new(&ALLOC, fmt_options).build(&parsed_ast.program);

             println!("{fmted_src}");


             // should not crash when parsing the fmted source text again
              let parsed_fmted_ast = oxc_parser::Parser::new(&ALLOC, &fmted_src, oxc_ast::ast::SourceType::ts())
             .with_options(parseOpt)
             .parse();

            }
        }

    static ALLOC: std::sync::LazyLock<oxc_allocator::Allocator> =
        std::sync::LazyLock::new(|| Allocator::default());

    // test that AST -> codegen -> AST roundtrips
    proptest! {
            #[test]
            fn ast_logical_expr_rndtrips(mut original_program in gen_program(&ALLOC)) {


                // AST -> Source Text
                let mut codegen = Codegen::new();
                //      codegen.print_str("return ");
                original_program.r#gen(&mut codegen, Context::default());
                //codegen.r#gen(&prog);

                let original_source_text: String = codegen.into_source_text();
                  original_program.source_text =original_source_text.as_str();

    println!("{}", original_source_text);

           // Source Text -> AST
            let  parseOpt = oxc_parser::ParseOptions::default();
                let parsed_ast = oxc_parser::Parser::new(&ALLOC, &original_source_text, oxc_ast::ast::SourceType::ts())
               .with_options(parseOpt)
               .parse();

            let fmt_options = oxc_formatter::FormatOptions::default();
             let fmted_round_tripped_src =
             oxc_formatter::Formatter::new(&ALLOC, fmt_options).build(&parsed_ast.program);

             println!("{fmted_round_tripped_src}");

             // should not crash when parsing the minified source text again
             let  parseOpt = oxc_parser::ParseOptions::default();
             let rnd_tripped_ast = oxc_parser::Parser::new(&ALLOC, &fmted_round_tripped_src, oxc_ast::ast::SourceType::ts())
             .with_options(parseOpt)
             .parse();
             let rnd_trip_program: Program = rnd_tripped_ast.program;
             println!("AST1: {original_program:#?}");
             println!("AST2: {rnd_trip_program:#?}");

               assert!(original_program.content_eq(&rnd_trip_program));
             /*
        // get the only single expression in the parsed AST so we can compare
        // against the original we generated with proptest
           let fst_ast_statement = parsed_ast.program.body.first().unwrap();
           let expr_stat: &Box<'_,oxc_ast::ast::ExpressionStatement> = match fst_ast_statement {
               oxc_ast::ast::Statement::ExpressionStatement(expr_statement)=>
                 expr_statement,
             _ => panic!("Unexpected, shoould only be a single expression statement")
           };


           //  if show_ast {
          //     println!("{parsed_ast_program:#?}");
               //}

               // AST -> SourceText -> Ast -> SourceTxt2, the SourceTxt2 should be unchanged.

               let rnd_tripped_logic_exp: &Expression<'_> = &expr_stat.expression;

               let mut codegen_two = Codegen::new();
                      codegen_two.print_expression(rnd_tripped_logic_exp);
                let roundtripped_source_text: String = codegen_two.into_source_text();
                 assert_eq!(original_source_text.as_str(), roundtripped_source_text.as_str());
            */
                 }
        }

    //    test that AST -> codegen -> lint apply "safe" fixes - > Always parses without crash
    proptest! {
                #[test]
                fn ast_logical_expr_lint_fix_parses_again(inital_logic_exp in conditional_expr(&ALLOC)) {

                    // AST -> Source Text
                    let mut codegen = Codegen::new();
                    codegen.print_expression(&inital_logic_exp);

                    let original_source_text: String = codegen.into_source_text();


        println!("{}", original_source_text);

    write_file("pbt.ts", &original_source_text).expect("failed to write file");

        let output = Command::new("oxlint")
                             .args(["pbt.ts", "--fix-suggestions"])
                           //  .arg("-A all")
                           // .arg
                             .output()
                             .expect("failed to execute process");

        println!("status: {}", output.status);
        println!("stdout: {}", String::from_utf8_lossy(&output.stdout));

        let fixed_src =  std::fs::read_to_string("pbt.ts").expect("failed to read fixed src");
               // Source Text -> AST -> Fmt -> Fmted Source Text
          /*
               let  parseOpt = oxc_parser::ParseOptions::default();
                    let parsed_ast = oxc_parser::Parser::new(&ALLOC, &original_source_text, oxc_ast::ast::SourceType::ts())
                   .with_options(parseOpt)
                   .parse();

                let fmt_options = oxc_linter::FormatOptions::default();
                 let fmted_src =
                 oxc_formatter::Formatter::new(&ALLOC, fmt_options).build(&parsed_ast.program);
    */
              //   println!("{fmted_src}");

                 // should not crash when parsing the fixed source text again
                 let  parseOpt = oxc_parser::ParseOptions::default();
                 let parsed_fixed_src = oxc_parser::Parser::new(&ALLOC, &fixed_src, oxc_ast::ast::SourceType::ts())
                 .with_options(parseOpt)
                 .parse();


                 println!("{:?}",fixed_src)
                }
            }

    fn minify(
        allocator: &Allocator,
        source_text: &str,
        source_type: SourceType,
        mangle: bool,
        nospace: bool,
    ) -> String {
        let ret = Parser::new(allocator, source_text, source_type).parse();
        let mut program = ret.program;
        let options = MinifierOptions {
            mangle: mangle.then(MangleOptions::default),
            compress: Some(CompressOptions::default()),
        };
        let ret = Minifier::new(options).build(allocator, &mut program);
        Codegen::new()
            .with_options(CodegenOptions {
                minify: nospace,
                comments: false,
                annotation_comments: false,
                legal_comments: oxc_codegen::LegalComment::Eof,
                ..CodegenOptions::default()
            })
            .with_scoping(ret.scoping)
            .build(&program)
            .code
    }

    //  AST -> Minifier -> Source Txt -> Parses without crash
    proptest! {
            #[test]
            fn ast_expr_code_gen_minify_parses_again(inital_logic_exp in conditional_expr(&ALLOC)) {

                // AST -> Source Text
                let mut codegen = Codegen::new();
                //codegen.print_str("return ");
                codegen.print_expression(&inital_logic_exp);

                let original_source_text: String = codegen.into_source_text();


    println!("{}", original_source_text);



            let minified_src = minify(&ALLOC, &original_source_text, oxc_ast::ast::SourceType::ts(), true, true);

             println!("minified: {}, original: {}", minified_src, original_source_text);


             // should not crash when parsing the minified source text again
             let  parseOpt = oxc_parser::ParseOptions::default();
             let parsed_fmted_ast = oxc_parser::Parser::new(&ALLOC, &minified_src, oxc_ast::ast::SourceType::ts())
             .with_options(parseOpt)
             .parse();
             let mut program = parsed_fmted_ast.program;
             // println!("pro {program:#?}");



            }
        }
}
