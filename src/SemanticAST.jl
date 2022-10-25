module SemanticAST
using MLStyle
using MLStyle.AbstractPatterns
using MLStyle.AbstractPatterns.BasicPatterns
import JuliaSyntax: @K_str, @KSet_str
using JuliaSyntax

const SN = JuliaSyntax.SyntaxNode
const SH = JuliaSyntax.SyntaxHead

include("util.jl")
include("ast_defns.jl")
include("mlstyle_helpers.jl")
include("analyzer.jl")

export expand_forms, expand_toplevel, ExpandCtx

end
