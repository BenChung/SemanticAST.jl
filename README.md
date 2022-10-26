# SemanticAST

SemanticAST.jl aims to provide a unified view of Julia's AST by reproducing much of the logic that the [lowering](https://docs.julialang.org/en/v1/devdocs/eval/#dev-parsing) phase does.
Many of the more structural errors that Julia produces (for example how a toplevel `::Int` declaration begets `syntax: invalid "::" syntax`) are not actually produced by the parser
but instead by a later lowering phase. In effect, lowering (in conjunction with macro expansion) defines all of the Julia AST forms that can be successfully compiled to executable runtime code.
If it can be lowered, it will at least *attempt* to execute. 

`Expr` ASTs are notoriously annoying to deal with to the point that packages like
[ExprTools](https://github.com/invenia/ExprTools.jl) are widely used to analyze what's actually there. `Expr`s will come in all sorts of wild and wonderful forms and having a library
to deal with all of the possible cases is a great help. However, ExprTools only goes so far: it solely provides a consistent representation of function definitions. SemanticAST aims to
go further. 

SemanticAST aims to extend this sort of "rationalization" to all of Julia's syntax; it provides a single set of AST definitions that explicitly declare every parameter and are descriptive
about what their fields mean. Moreover, SemanticAST's types try to be complete --- that is, you can use the type of a field in a SemanticAST struct to determine precisely what any possible
member might be. Additionally, by sitting on top of JuliaSyntax, SemanticAST provides detailed source location information both in the output AST and in the lowering-equivalent error messages
that SemanticAST produces The objective, then, is to eliminate the surprise inherent to working with Julia's AST forms, allowing easier development of static analysis tooling for Julia.

The implementation strategy for SemanticAST is to bring together lowering, parts of toplevel evaluation, and parts of the Julia runtime itself to identify as many errors as early as possible.
Ideally, SemanticAST will accept any program that is "runnable" by Julia, even if it might encounter a dynamic error. Errors produced by SemanticAST aim to parallel errors produced by Julia
itself as it goes to compile a given `Expr` to IR, as well as parts of evaluation of that IR.

## Limitation: Macros

At present SemanticAST tries to cover much of "basic" Julia - but there's a major fly in the ointment: macros.

Macros are challenging for the SemanticAST approach because they can accept non-standard Julia `Expr`s and then both
produce unusual `Expr` forms as well as use a wide range of forms not otherwise produced by parsing. As SemanticAST sits
on top of JuliaSyntax and only understands JuliaSyntax `SyntaxNode`s it cannot practically run macros directly as while a 
`SyntaxNode` can be converted to an `Expr` vice versa is not possible without loss of information. Thus, at present,
macro invocations are simply replaced with a placeholder. There's limited hardcoded support for a small list of built-in macros
but no more.

Similarly, support for quoting is as of now more or less nonexistent. 

# Use

SemanticAST's entry points are through the `expand_forms` and `expand_toplevel` functions; given a 
`JuliaSyntax.SyntaxNode` and a `ExpandCtx` they will attempt to unpack a `SyntaxNode` into a `SemanticAST.Expression` and `SemanticAST.ToplevelStmts`, respectively. 
Note that SemanticAST AST forms all contain a `location` field that's implicitly inserted by the `@ast_node` and `@ast_data` macros that is of type `SemanticAST.SourcePosition`.
