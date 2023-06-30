using Documenter, SemanticAST

makedocs(sitename="SemanticAST",
pages = [
    "index.md",
    "Public interface" => "interface.md",
])
deploydocs(
    repo = "github.com/BenChung/SemanticAST.jl.git"
)
