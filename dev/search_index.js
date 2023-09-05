var documenterSearchIndex = {"docs":
[{"location":"interface/","page":"Public interface","title":"Public interface","text":"SemanticAST parses a SyntaxNode as provided by JuliaSyntax into its internal ASTNode structures for use by downstream analyses. This process is performed by one of two methods: expand_forms and expand_toplevel.","category":"page"},{"location":"interface/","page":"Public interface","title":"Public interface","text":"CurrentModule = SemanticAST","category":"page"},{"location":"interface/","page":"Public interface","title":"Public interface","text":"expand_forms\nexpand_toplevel\nExpandCtx\nErrorReporting\nExceptionErrorReporting\nSilentErrorReporting\nMacroContext\nDefaultMacroContext","category":"page"},{"location":"interface/#SemanticAST.expand_forms","page":"Public interface","title":"SemanticAST.expand_forms","text":"expand_forms(ast::JuliaSyntax.SyntaxNode, ctx::ExpandCtx)\n\nExpands an expression (such as a method body) from a SyntaxNode to an Expression with respect to a ExpandCtx. See expand_toplevel for more discussion.\n\n\n\n\n\n","category":"function"},{"location":"interface/#SemanticAST.expand_toplevel","page":"Public interface","title":"SemanticAST.expand_toplevel","text":"expand_toplevel(ast::JuliaSyntax.SyntaxNode)::ToplevelStmts\nexpand_toplevel(ast::JuliaSyntax.SyntaxNode, ctx::ExpandCtx)::ToplevelStmts\n\nTakes a SyntaxNode representing an entire file and lowers it to a ToplevelStmts.\n\nToplevel vs. expression can be thought of generally as \"where would it make sense for a module or using statement to exist?\". As an example, the contents of a file are usually at the top level as is the arugment to an eval call. In constrast, a method body will not be at the top level as neither module nor using statements are valid inside of it.\n\nFor most use cases this is the reccomended entry point. Use expand_forms if you need to expand a specific expression.\n\n\n\n\n\n","category":"function"},{"location":"interface/#SemanticAST.ExpandCtx","page":"Public interface","title":"SemanticAST.ExpandCtx","text":"ExpandCtx(is_toplevel::Bool=false, is_loop::Bool= false; macro_context=DefaultMacroContext(), error_context=ExceptionErrorReporting())\n\nThe context in which to perform expansion from SyntaxNodes to ASTNodes.\n\nis_toplevel: is the analyzed expression at the top level or not?\nis_loop: is the expression in a loop or not (used for determining if break or continue are valid)?\nmacro_context: The context with which to expand macros. See the discussion in readme.\nerror_context: The error reporting context. By default, two are provided (ExceptionErrorReporting and SilentErrorReporting), with exceptions being the default.\n\n\n\n\n\n","category":"type"},{"location":"interface/#SemanticAST.ErrorReporting","page":"Public interface","title":"SemanticAST.ErrorReporting","text":"The error reporting mode to use\n\n\n\n\n\n","category":"type"},{"location":"interface/#SemanticAST.ExceptionErrorReporting","page":"Public interface","title":"SemanticAST.ExceptionErrorReporting","text":"Create an ASTException when an issue is encountered and continue with the fallback.\n\n\n\n\n\n","category":"type"},{"location":"interface/#SemanticAST.SilentErrorReporting","page":"Public interface","title":"SemanticAST.SilentErrorReporting","text":"Do nothing when an issue is encountered and continue with the fallback.\n\n\n\n\n\n","category":"type"},{"location":"interface/#SemanticAST.MacroContext","page":"Public interface","title":"SemanticAST.MacroContext","text":"The abstract type for macro expansion contexts.\n\nThere are two macro extension points in the analyzer: resolve_toplevel_macro(ast::SyntaxNode, ::MacroContext, ::Val{Symbol}, args::Vector{SyntaxNode}, ctx::ExpandCtx)::ToplevelStmts and resolve_macro(ast, ::MacroContext, ::Val{Symbol}, args, ctx)::Expression. Both share the same signature:\n\nast: The SyntaxNode root of the macro invocation.\nMacroContext: The context with which to resolve macros in. Implement a new MacroContext by implementing resolve_toplevel_macro and resolve_macro that accept it; the provided one is DefaultMacroContext.\nVal{Symbol}: The macro's name (in Val form).\nargs: The SyntaxNodes that represent the arguments to the macro.\nctx: The expansion context inside which the analysis is being done.\n\nThey differ in that resolve_toplevel_macro returns a TopLevelStmts (a statement that can only exist at the top level), while resolve_macro returns an Expression. An example of how to write a macro analyzer can be seen in the default implementation for @inline and @noinline:\n\nresolve_macro(ast, ::DefaultMacroContext, ::Union{Val{Symbol(\"@inline\")}, Val{Symbol(\"@noinline\")}, Val{Symbol(\"@inbounds\")}}, args, ctx) = expand_forms(args[1], ctx)\n\nFrom the perspective of the default analyzer @inline and @noinline are no-ops, so analysis continues by simply calling back into expand_forms on the first argument.\n\n\n\n\n\n","category":"type"},{"location":"interface/#SemanticAST.DefaultMacroContext","page":"Public interface","title":"SemanticAST.DefaultMacroContext","text":"The default macro analysis context.\n\nCurrently implements top-level support for:\n\n* @doc\n* @inline, @noinline\n* @assume_effects, @constprop\n\nExpression-level support is provided for:\n\n* @doc\n* @inline, @noinline\n* @eval\n* @generated\n* @assume_effects\n\n\n\n\n\n","category":"type"},{"location":"#SemanticAST","page":"SemanticAST","title":"SemanticAST","text":"","category":"section"},{"location":"","page":"SemanticAST","title":"SemanticAST","text":"SemanticAST.jl aims to provide a unified view of Julia's AST by reproducing much of the logic that the lowering phase does. Many of the more structural errors that Julia produces (for example how a toplevel ::Int declaration begets syntax: invalid \"::\" syntax) are not actually produced by the parser but instead by a later lowering phase. In effect, lowering (in conjunction with macro expansion) defines all of the Julia AST forms that can be successfully compiled to executable runtime code. If it can be lowered, it will at least attempt to execute.","category":"page"},{"location":"","page":"SemanticAST","title":"SemanticAST","text":"Expr ASTs are notoriously annoying to deal with to the point that packages like ExprTools are widely used to analyze what's actually there. Exprs will come in all sorts of wild and wonderful forms and having a library to deal with all of the possible cases is a great help. However, ExprTools only goes so far: it solely provides a consistent representation of function definitions. SemanticAST aims to go further.","category":"page"},{"location":"","page":"SemanticAST","title":"SemanticAST","text":"SemanticAST aims to extend this sort of \"rationalization\" to all of Julia's syntax; it provides a single set of AST definitions that explicitly declare every parameter and are descriptive about what their fields mean. Moreover, SemanticAST's types try to be complete –- that is, you can use the type of a field in a SemanticAST struct to determine precisely what any possible member might be. Additionally, by sitting on top of JuliaSyntax, SemanticAST provides detailed source location information both in the output AST and in the lowering-equivalent error messages that SemanticAST produces The objective, then, is to eliminate the surprise inherent to working with Julia's AST forms, allowing easier development of static analysis tooling for Julia.","category":"page"},{"location":"","page":"SemanticAST","title":"SemanticAST","text":"The implementation strategy for SemanticAST is to bring together lowering, parts of toplevel evaluation, and parts of the Julia runtime itself to identify as many errors as early as possible. Ideally, SemanticAST will accept any program that is \"runnable\" by Julia, even if it might encounter a dynamic error. Errors produced by SemanticAST aim to parallel errors produced by Julia itself as it goes to compile a given Expr to IR, as well as parts of evaluation of that IR.","category":"page"},{"location":"","page":"SemanticAST","title":"SemanticAST","text":"","category":"page"},{"location":"#Use","page":"SemanticAST","title":"Use","text":"","category":"section"},{"location":"","page":"SemanticAST","title":"SemanticAST","text":"SemanticAST's entry points are through the expand_forms and expand_toplevel functions; given a JuliaSyntax.SyntaxNode and a ExpandCtx they will attempt to unpack a SyntaxNode into a SemanticAST.Expression and SemanticAST.ToplevelStmts, respectively. Note that SemanticAST AST forms all contain a location field that's implicitly inserted by the @ast_node and @ast_data macros that is of type SemanticAST.SourcePosition.","category":"page"},{"location":"","page":"SemanticAST","title":"SemanticAST","text":"As an example, suppose we wanted to analyze the program hello_world.jl that looked like","category":"page"},{"location":"","page":"SemanticAST","title":"SemanticAST","text":"function hello_world()\n    println(\"hello world!\")\nend","category":"page"},{"location":"","page":"SemanticAST","title":"SemanticAST","text":"the complete analysis program would look like:","category":"page"},{"location":"","page":"SemanticAST","title":"SemanticAST","text":"using JuliaSyntax, SemanticAST\n\nfilename = \"hello_world.jl\"\nsource_tree = parsestmt(SyntaxNode, read(filename, String), filename=filename)\nsemantic_tree = expand_toplevel(source_tree)","category":"page"},{"location":"","page":"SemanticAST","title":"SemanticAST","text":"that's it!","category":"page"},{"location":"#Limitation:-Macros","page":"SemanticAST","title":"Limitation: Macros","text":"","category":"section"},{"location":"","page":"SemanticAST","title":"SemanticAST","text":"At present SemanticAST tries to cover much of \"basic\" Julia - but there's a major fly in the ointment: macros.","category":"page"},{"location":"","page":"SemanticAST","title":"SemanticAST","text":"Macros are challenging for the SemanticAST approach because they can accept non-standard Julia Exprs and then both produce unusual Expr forms as well as use a wide range of forms not otherwise produced by parsing. As SemanticAST sits on top of JuliaSyntax and only understands JuliaSyntax SyntaxNodes it cannot practically run macros directly as while a SyntaxNode can be converted to an Expr vice versa is not possible without loss of information. Thus, at present, macro invocations are simply replaced with a placeholder. There's limited hardcoded support for a small list of built-in macros and an extension mechanism, but no more.","category":"page"},{"location":"#Limitation:-Quoting","page":"SemanticAST","title":"Limitation: Quoting","text":"","category":"section"},{"location":"","page":"SemanticAST","title":"SemanticAST","text":"While SemanticAST will not choke on quotes, it won't interpret them intelligently. Quotes are seen as a big blob of Expr, including unquotes.","category":"page"},{"location":"#State","page":"SemanticAST","title":"State","text":"","category":"section"},{"location":"","page":"SemanticAST","title":"SemanticAST","text":"SemanticAST is part of the implementation of my thesis on typing Julia and its current implementation was designed specifically to fit the needs of a type system. As a result, it is missing a number of features that might be interesting. Two that I think would be interesting are:","category":"page"},{"location":"","page":"SemanticAST","title":"SemanticAST","text":"The ability to analyze normal Exprs and not only JuliaSyntax nodes. This could be accomplished by extending the custom patterns to support Exprs, and would allow SemanticAST to be used after macro expansion (or as part of normal Julia macro implementations) when combined with\nSupport for semantic forms that don't result from parsing. My goal was to support parser output but macros are allowed to use a larger Expr language. As a result, analyzing post-expansion Exprs is not possible.","category":"page"}]
}