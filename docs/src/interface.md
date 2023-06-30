SemanticAST parses a `SyntaxNode` as provided by JuliaSyntax into its internal `ASTNode` structures for use by downstream analyses. This process is performed by one of two methods: `expand_forms` and `expand_toplevel`.

```@meta
CurrentModule = SemanticAST
```

```@docs
expand_forms
expand_toplevel
ExpandCtx
ErrorReporting
ExceptionErrorReporting
SilentErrorReporting
MacroContext
DefaultMacroContext
```
