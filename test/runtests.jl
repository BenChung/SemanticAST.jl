using SemanticAST
import SemanticAST: just_argslist, flatten_where_expr, analyze_typevar, ASTException
using Test
import JuliaSyntax
import JuliaSyntax: @K_str, @KSet_str

const SN = JuliaSyntax.SyntaxNode
const SH = JuliaSyntax.SyntaxHead
childof = JuliaSyntax.child
kindof(ex) = JuliaSyntax.kind(JuliaSyntax.head(ex))

@testset "visit" begin
	y = 0
	enter = (x) -> y = 1
	exit = (x) -> begin @test y == 1; y = 2 end
	SemanticAST.visit(enter, exit, SemanticAST.StringInterpolate([], nothing))
	@test y == 2
end

af1 = JuliaSyntax.parseall(SN, "function () end")
af2 = JuliaSyntax.parseall(SN, "function (x) end")
af3 = JuliaSyntax.parseall(SN, "function (x,y) end")
af4 = JuliaSyntax.parseall(SN, "function (x,y) where T end")
nf1 = JuliaSyntax.parseall(SN, "function f() end")
nf2 = JuliaSyntax.parseall(SN, "function f(x) end")
nf3 = JuliaSyntax.parseall(SN, "function f(x, y) end")
nf4 = JuliaSyntax.parseall(SN, "function f(x, y) where T end")

@testset "just_argslist" begin
	@test just_argslist(childof(af1, 1))
	@test just_argslist(childof(af2, 1))
	@test just_argslist(childof(af3, 1))
	@test just_argslist(childof(af4, 1))
	@test !just_argslist(childof(nf1, 1))
	@test !just_argslist(childof(nf2, 1))
	@test !just_argslist(childof(nf3, 1))
	@test !just_argslist(childof(nf4, 1))
end

wex1 = JuliaSyntax.parseall(SN, "x where T")
wex2 = JuliaSyntax.parseall(SN, "x where T where S")
wex3 = JuliaSyntax.parseall(SN, "x where T <: I")
wex4 = JuliaSyntax.parseall(SN, "x where T <: I where I")
wex5 = JuliaSyntax.parseall(SN, "x where {T, V}")
@testset "flatten_where_expr" begin
	ctx = ExpandCtx(true, false)
	@test sprint(show, flatten_where_expr(childof(wex1, 1), ctx)) == "(x, Any[T])"
	@test sprint(show, flatten_where_expr(childof(wex2, 1), ctx)) == "(x, Any[S, T])"
	@test sprint(show, flatten_where_expr(childof(wex3, 1), ctx)) == "(x, Any[(<: T I)])"
	@test sprint(show, flatten_where_expr(childof(wex4, 1), ctx)) == "(x, Any[I, (<: T I)])"
	@test sprint(show, flatten_where_expr(childof(wex5, 1), ctx)) == "(x, Any[T, V])"
end

atv1 = JuliaSyntax.parseall(SN, "A <: B")
atv2 = JuliaSyntax.parseall(SN, "A >: B")
atv3 = JuliaSyntax.parseall(SN, "A <: B <: C")
atv4 = JuliaSyntax.parseall(SN, "A >: B >: C")
atv5 = JuliaSyntax.parseall(SN, "A + 2 <: B")
@testset "analyze_typevar" begin
	@test string(analyze_typevar(childof(atv1, 1), ExpandCtx())) == "TyVar(:A, Variable(:B), nothing)"
	@test string(analyze_typevar(childof(atv2, 1), ExpandCtx())) == "TyVar(:A, nothing, Variable(:B))"
	@test string(analyze_typevar(childof(atv3, 1), ExpandCtx())) == "TyVar(:B, Variable(:C), Variable(:A))"
	@test_throws ASTException analyze_typevar(childof(atv4, 1), ExpandCtx())
	@test_throws ASTException analyze_typevar(childof(atv5, 1), ExpandCtx())
end
struct ErrorResult end
expr_tests() = [
	:function => [
		"function foo() end" => "FunctionDef(ResolvedName([:foo]), [], [], [], nothing, Block([]))",
		"function foo(a) end" => "FunctionDef(ResolvedName([:foo]), [FnArg(IdentifierAssignment(:a), nothing, nothing)], [], [], nothing, Block([]))",
        "function foo(::Int) end" => "FunctionDef(ResolvedName([:foo]), [FnArg(nothing, nothing, Variable(:Int))], [], [], nothing, Block([]))",
		"function foo(a::Int) end" => "FunctionDef(ResolvedName([:foo]), [FnArg(IdentifierAssignment(:a), nothing, Variable(:Int))], [], [], nothing, Block([]))",
		"function foo(a::Int, b::Int) end" => "FunctionDef(ResolvedName([:foo]), [FnArg(IdentifierAssignment(:a), nothing, Variable(:Int)), FnArg(IdentifierAssignment(:b), nothing, Variable(:Int))], [], [], nothing, Block([]))",
		"function foo(a::Int, b::Int, c=2) end" => "FunctionDef(ResolvedName([:foo]), [FnArg(IdentifierAssignment(:a), nothing, Variable(:Int)), FnArg(IdentifierAssignment(:b), nothing, Variable(:Int)), FnArg(IdentifierAssignment(:c), Literal(2), nothing)], [], [], nothing, Block([]))",
		"function foo(a::Int, b::Int, c=2, d::Int) end" => ErrorResult(),
		"function foo(; c) end" => "FunctionDef(ResolvedName([:foo]), [], [KwArg(:c, nothing, nothing, false)], [], nothing, Block([]))",
		"function foo(; c=2) end" => "FunctionDef(ResolvedName([:foo]), [], [KwArg(:c, nothing, Literal(2), false)], [], nothing, Block([]))",
		"function foo(; c::Int=2) end" => "FunctionDef(ResolvedName([:foo]), [], [KwArg(:c, Variable(:Int), Literal(2), false)], [], nothing, Block([]))",
		"function foo(a; c::Int=2) end" => "FunctionDef(ResolvedName([:foo]), [FnArg(IdentifierAssignment(:a), nothing, nothing)], [KwArg(:c, Variable(:Int), Literal(2), false)], [], nothing, Block([]))",
		"function foo(a; c::Int) end" => "FunctionDef(ResolvedName([:foo]), [FnArg(IdentifierAssignment(:a), nothing, nothing)], [KwArg(:c, Variable(:Int), nothing, false)], [], nothing, Block([]))",
		"function foo(a; c::Int, d) end" => "FunctionDef(ResolvedName([:foo]), [FnArg(IdentifierAssignment(:a), nothing, nothing)], [KwArg(:c, Variable(:Int), nothing, false), KwArg(:d, nothing, nothing, false)], [], nothing, Block([]))",
		"function foo((a,b), c) end" => "FunctionDef(ResolvedName([:foo]), [FnArg(TupleAssignment([IdentifierAssignment(:a), IdentifierAssignment(:b)]), nothing, nothing), FnArg(IdentifierAssignment(:c), nothing, nothing)], [], [], nothing, Block([]))",
		"function foo((a,b)...) end" => "FunctionDef(ResolvedName([:foo]), [FnArg(VarargAssignment(TupleAssignment([IdentifierAssignment(:a), IdentifierAssignment(:b)])), nothing, nothing)], [], [], nothing, Block([]))",
		"function foo(a, b..., c) end" => ErrorResult(),
		"function foo(; (a,b)::Tuple{Int, Int} = (1, 2)) end" => ErrorResult(),
		"function foo(; (a,b)) end" => ErrorResult(),
		"function foo((;a,b)) end" => "FunctionDef(ResolvedName([:foo]), [FnArg(NamedTupleAssignment([IdentifierAssignment(:a), IdentifierAssignment(:b)]), nothing, nothing)], [], [], nothing, Block([]))",
		"function foo((;a=2,b)) end" => ErrorResult(),
		"function foo((;a,b)::Int) end" => "FunctionDef(ResolvedName([:foo]), [FnArg(NamedTupleAssignment([IdentifierAssignment(:a), IdentifierAssignment(:b)]), nothing, Variable(:Int))], [], [], nothing, Block([]))",
		"function foo() :: Int end" => "FunctionDef(ResolvedName([:foo]), [], [], [], Variable(:Int), Block([]))",
		"function foo() :: Int where T end" => "FunctionDef(ResolvedName([:foo]), [], [], [TyVar(:T, nothing, nothing)], Variable(:Int), Block([]))",
		"function foo() :: Int where {T, V} end" => "FunctionDef(ResolvedName([:foo]), [], [], [TyVar(:T, nothing, nothing), TyVar(:V, nothing, nothing)], Variable(:Int), Block([]))",
		"function foo() :: Int where {T <: V, V} end" => "FunctionDef(ResolvedName([:foo]), [], [], [TyVar(:T, Variable(:V), nothing), TyVar(:V, nothing, nothing)], Variable(:Int), Block([]))",
		"function foo() :: Int where {T} where V end" => "FunctionDef(ResolvedName([:foo]), [], [], [TyVar(:V, nothing, nothing), TyVar(:T, nothing, nothing)], Variable(:Int), Block([]))",
		"function foo() :: Int where {T} where {U, V} end" => "FunctionDef(ResolvedName([:foo]), [], [], [TyVar(:U, nothing, nothing), TyVar(:V, nothing, nothing), TyVar(:T, nothing, nothing)], Variable(:Int), Block([]))",
		"function foo()::T where T end" => "FunctionDef(ResolvedName([:foo]), [], [], [TyVar(:T, nothing, nothing)], Variable(:T), Block([]))",
		"function foo() where {T} where {U, V} end" => "FunctionDef(ResolvedName([:foo]), [], [], [TyVar(:U, nothing, nothing), TyVar(:V, nothing, nothing), TyVar(:T, nothing, nothing)], nothing, Block([]))",
		"function foo() where Int <: T <: Float32 end" => "FunctionDef(ResolvedName([:foo]), [], [], [TyVar(:T, Variable(:Float32), Variable(:Int))], nothing, Block([]))",
		"function foo()::T where Int <: T <: Float32 end" => "FunctionDef(ResolvedName([:foo]), [], [], [TyVar(:T, Variable(:Float32), Variable(:Int))], Variable(:T), Block([]))",
		"evalpoly(x::T, p::T)::T where T<:Number = 2" => "Assignment(FunctionAssignment(ResolvedName([:evalpoly]), [FnArg(IdentifierAssignment(:x), nothing, Variable(:T)), FnArg(IdentifierAssignment(:p), nothing, Variable(:T))], [], [TyVar(:T, Variable(:Number), nothing)], Variable(:T)), Literal(2))",
		"function foo(a) where {T} where {U, V} end" => "FunctionDef(ResolvedName([:foo]), [FnArg(IdentifierAssignment(:a), nothing, nothing)], [], [TyVar(:U, nothing, nothing), TyVar(:V, nothing, nothing), TyVar(:T, nothing, nothing)], nothing, Block([]))",
		"function foo(a; b::T) where {T} where {U, V} end" => "FunctionDef(ResolvedName([:foo]), [FnArg(IdentifierAssignment(:a), nothing, nothing)], [KwArg(:b, Variable(:T), nothing, false)], [TyVar(:U, nothing, nothing), TyVar(:V, nothing, nothing), TyVar(:T, nothing, nothing)], nothing, Block([]))",
		"function foo(a, a) end" => ErrorResult(),
		"function foo(a::Int, a::Int) end" => ErrorResult(),
		"function foo((a,b), b::Int) end" => "FunctionDef(ResolvedName([:foo]), [FnArg(TupleAssignment([IdentifierAssignment(:a), IdentifierAssignment(:b)]), nothing, nothing), FnArg(IdentifierAssignment(:b), nothing, Variable(:Int))], [], [], nothing, Block([]))",
		"function foo(; a=1, a=2) end" => ErrorResult(),
		"function foo(a; a=1) end" => ErrorResult(),
		"function foo() where {T, T} end" => ErrorResult(),
		"function foo() where T where T end" => ErrorResult(),
		"function foo(T) where T end" => ErrorResult(),
		"function () end" => "FunctionDef(AnonFuncName(), [], [], [], nothing, Block([]))",
		"function (a) end" => "FunctionDef(AnonFuncName(), [FnArg(IdentifierAssignment(:a), nothing, nothing)], [], [], nothing, Block([]))",
		"function (a::Int) end" => "FunctionDef(AnonFuncName(), [FnArg(IdentifierAssignment(:a), nothing, Variable(:Int))], [], [], nothing, Block([]))",
		"function (a::Int, b::Int) end" => "FunctionDef(AnonFuncName(), [FnArg(IdentifierAssignment(:a), nothing, Variable(:Int)), FnArg(IdentifierAssignment(:b), nothing, Variable(:Int))], [], [], nothing, Block([]))",
		"function (a::Int, b::Int, c=2) end" => "FunctionDef(AnonFuncName(), [FnArg(IdentifierAssignment(:a), nothing, Variable(:Int)), FnArg(IdentifierAssignment(:b), nothing, Variable(:Int)), FnArg(IdentifierAssignment(:c), Literal(2), nothing)], [], [], nothing, Block([]))",
		"function (a::Int, b::Int, c=2, d::Int) end" => ErrorResult(),
		"function foo end" => "FunctionDef(ResolvedName([:foo]), [], [], [], nothing, nothing)",
		"function (::Type{T})(x) end" => "FunctionDef(DeclName(nothing, CallCurly(Variable(:Type), [Variable(:T)])), [FnArg(IdentifierAssignment(:x), nothing, nothing)], [], [], nothing, Block([]))",
		"function A.f()   end" => "FunctionDef(ResolvedName([:A, :f]), [], [], [], nothing, Block([]))",
		"function f{T}() end" => "FunctionDef(TypeFuncName(Variable(:f), [Variable(:T)]), [], [], [], nothing, Block([]))",
		"function f()::T    end" => "FunctionDef(ResolvedName([:f]), [], [], [], Variable(:T), Block([]))",
		"function f()::g(T) end" => "FunctionDef(ResolvedName([:f]), [], [], [], FunCall(Variable(:g), [PositionalArg(Variable(:T))], []), Block([]))",
		"(2+2)(x,y) = x" => ErrorResult(),
		"function foo() where 2+T end" => ErrorResult(),
		"function foo((x::Int, y)::String) end" => ErrorResult(),
		"function foo(;x ; y) end" => ErrorResult(),
		"function foo(;(x,y)...) end" => ErrorResult(),
		"function foo{; a}() end" => ErrorResult(),
		"function foo{a=y}() end" => ErrorResult(),
        "function foo(a::b = 9) end" => "FunctionDef(ResolvedName([:foo]), [FnArg(IdentifierAssignment(:a), Literal(9), Variable(:b))], [], [], nothing, Block([]))",
        "function foo(a::b = 9, b::c = 17) end" => "FunctionDef(ResolvedName([:foo]), [FnArg(IdentifierAssignment(:a), Literal(9), Variable(:b)), FnArg(IdentifierAssignment(:b), Literal(17), Variable(:c))], [], [], nothing, Block([]))",
        "function -(a, b) end" => "FunctionDef(ResolvedName([:-]), [FnArg(IdentifierAssignment(:a), nothing, nothing), FnArg(IdentifierAssignment(:b), nothing, nothing)], [], [], nothing, Block([]))",
        "function .-(a, b) end" => ErrorResult(),
		"function \$x(a, b) end" => ErrorResult(),
        "function f(;x...) end" => "FunctionDef(ResolvedName([:f]), [], [KwArg(:x, nothing, nothing, true)], [], nothing, Block([]))",
        "function f(a, b, c...) end" =>  "FunctionDef(ResolvedName([:f]), [FnArg(IdentifierAssignment(:a), nothing, nothing), FnArg(IdentifierAssignment(:b), nothing, nothing), FnArg(VarargAssignment(IdentifierAssignment(:c)), nothing, nothing)], [], [], nothing, Block([]))"
	],
	:macro => [
		"macro foo end" => "MacroDef(ResolvedName([:foo]), [], [], nothing, nothing)",
		"macro foo.bar() end" => ErrorResult(),
		"macro foo{2}() end" => ErrorResult(),
		"macro foo() end" => "MacroDef(ResolvedName([:foo]), [], [], nothing, Block([]))",
		"macro foo(a) end" => "MacroDef(ResolvedName([:foo]), [FnArg(IdentifierAssignment(:a), nothing, nothing)], [], nothing, Block([]))",
		"macro foo(a::Int) end" => "MacroDef(ResolvedName([:foo]), [FnArg(IdentifierAssignment(:a), nothing, Variable(:Int))], [], nothing, Block([]))",
		"macro foo(a::Int, b::Int) end" => "MacroDef(ResolvedName([:foo]), [FnArg(IdentifierAssignment(:a), nothing, Variable(:Int)), FnArg(IdentifierAssignment(:b), nothing, Variable(:Int))], [], nothing, Block([]))",
		"macro foo(a::Int, b::Int, c=2) end" => "MacroDef(ResolvedName([:foo]), [FnArg(IdentifierAssignment(:a), nothing, Variable(:Int)), FnArg(IdentifierAssignment(:b), nothing, Variable(:Int)), FnArg(IdentifierAssignment(:c), Literal(2), nothing)], [], nothing, Block([]))",
		"macro foo(a::Int, b::Int, c=2, d::Int) end" => ErrorResult(),
		"macro foo(; x) end" => ErrorResult()
	],
	:weirdwhere => [
		"where = 3" => "Assignment(IdentifierAssignment(:where), Literal(3))",
		"func(where) = 12" => "Assignment(FunctionAssignment(ResolvedName([:func]), [FnArg(IdentifierAssignment(:where), nothing, nothing)], [], [], nothing), Literal(12))",
		"func(where::Int) = 12" => "Assignment(FunctionAssignment(ResolvedName([:func]), [FnArg(IdentifierAssignment(:where), nothing, Variable(:Int))], [], [], nothing), Literal(12))"
	],
	:try => [
		"try \n x \n catch e \n y \n finally \n z end" => "TryCatch(Block([Variable(:x)]), :e, Block([Variable(:y)]), nothing, Block([Variable(:z)]))",
		"try \n x \n catch e \n y \n else z finally \n w end" => "TryCatch(Block([Variable(:x)]), :e, Block([Variable(:y)]), Block([Variable(:z)]), Block([Variable(:w)]))",
		"try x catch end" => "TryCatch(Block([Variable(:x)]), nothing, Block([]), nothing, nothing)",
		"try x catch ; y end" => "TryCatch(Block([Variable(:x)]), nothing, Block([Variable(:y)]), nothing, nothing)",
		"try x catch \n y end" => "TryCatch(Block([Variable(:x)]), nothing, Block([Variable(:y)]), nothing, nothing)",
		"try x catch e y end" => "TryCatch(Block([Variable(:x)]), :e, Block([Variable(:y)]), nothing, nothing)",
		"try x finally y end" => "TryCatch(Block([Variable(:x)]), nothing, nothing, nothing, Block([Variable(:y)]))",
		"try catch ; else end" => "TryCatch(Block([]), nothing, Block([]), Block([]), nothing)"
	],
	:curly => [
		"a{;a}" => ErrorResult(),
		"a{a=2}" => ErrorResult(),
		"a{}" => "CallCurly(Variable(:a), [])",
		"a{b}" => "CallCurly(Variable(:a), [Variable(:b)])",
		"a{<:T}" => "CallCurly(Variable(:a), [TyVar(nothing, Variable(:T), nothing)])",
		"a{>:T}" => "CallCurly(Variable(:a), [TyVar(nothing, nothing, Variable(:T))])"
	],
	:(.) => [
		"a.f" => "GetProperty(Variable(:a), :f)",
		"a.\"f\"" => "GetProperty(Variable(:a), Literal(\"f\"))",
		"a.(f)" => "FunCall(Broadcast(Variable(:a)), [PositionalArg(Variable(:f))], [])",
		"a.(f, x=9, z)" => "FunCall(Broadcast(Variable(:a)), [PositionalArg(Variable(:f)), PositionalArg(Variable(:z))], [KeywordArg(:x, Literal(9))])",
		"a.(f.(x))" => "FunCall(Broadcast(Variable(:a)), [PositionalArg(FunCall(Broadcast(Variable(:f)), [PositionalArg(Variable(:x))], []))], [])",
		"a.(2 .+ 2)" => "FunCall(Broadcast(Variable(:a)), [PositionalArg(FunCall(Broadcast(Variable(:+)), [PositionalArg(Literal(2)), PositionalArg(Literal(2))], []))], [])",
		"a .&& b" => "FunCall(Broadcast(Variable(:&&)), [PositionalArg(Variable(:a)), PositionalArg(Variable(:b))], [])",
		"a .|| b" => "FunCall(Broadcast(Variable(:||)), [PositionalArg(Variable(:a)), PositionalArg(Variable(:b))], [])",
		"a .= b" => "BroadcastAssignment(Variable(:a), Variable(:b))",
		"a[5] .= b" => "BroadcastAssignment(GetIndex(Variable(:a), [PositionalArg(Literal(5))]), Variable(:b))",
		"a[5, 6] .= b" => "BroadcastAssignment(GetIndex(Variable(:a), [PositionalArg(Literal(5)), PositionalArg(Literal(6))]), Variable(:b))",
		"x+y .= y" => "BroadcastAssignment(FunCall(Variable(:+), [PositionalArg(Variable(:x)), PositionalArg(Variable(:y))], []), Variable(:y))",
		"x+y .+= y" => "BroadcastUpdate(:+=, FunCall(Variable(:+), [PositionalArg(Variable(:x)), PositionalArg(Variable(:y))], []), Variable(:y))",
		".!f" => "FunCall(Broadcast(Variable(:!)), [PositionalArg(Variable(:f))], [])"
	],
	:call => [
		"a(x)" => "FunCall(Variable(:a), [PositionalArg(Variable(:x))], [])",
		"a(x,y)" => "FunCall(Variable(:a), [PositionalArg(Variable(:x)), PositionalArg(Variable(:y))], [])",
		"a(x,y; y=2, z=3)" => "FunCall(Variable(:a), [PositionalArg(Variable(:x)), PositionalArg(Variable(:y))], [KeywordArg(:y, Literal(2)), KeywordArg(:z, Literal(3))])",
		"a(x, y...; z=9)" => "FunCall(Variable(:a), [PositionalArg(Variable(:x)), SplatArg(Variable(:y))], [KeywordArg(:z, Literal(9))])",
		"a - b - c" => "FunCall(Variable(:-), [PositionalArg(FunCall(Variable(:-), [PositionalArg(Variable(:a)), PositionalArg(Variable(:b))], [])), PositionalArg(Variable(:c))], [])",
		"a + b + c" => "FunCall(Variable(:+), [PositionalArg(Variable(:a)), PositionalArg(Variable(:b)), PositionalArg(Variable(:c))], [])",
		"a + b .+ c" => "FunCall(Broadcast(Variable(:+)), [PositionalArg(FunCall(Variable(:+), [PositionalArg(Variable(:a)), PositionalArg(Variable(:b))], [])), PositionalArg(Variable(:c))], [])",
		"[x +y]" => "HCat(nothing, [Variable(:x), FunCall(Variable(:+), [PositionalArg(Variable(:y))], [])])",
		"[x+y +z]" => "HCat(nothing, [FunCall(Variable(:+), [PositionalArg(Variable(:x)), PositionalArg(Variable(:y))], []), FunCall(Variable(:+), [PositionalArg(Variable(:z))], [])])",
		"[x +₁y]" => "Vect([FunCall(Variable(:+₁), [PositionalArg(Variable(:x)), PositionalArg(Variable(:y))], [])])",
		"[x+y+z]" => "Vect([FunCall(Variable(:+), [PositionalArg(Variable(:x)), PositionalArg(Variable(:y)), PositionalArg(Variable(:z))], [])])",
		"[x+y + z]" => "Vect([FunCall(Variable(:+), [PositionalArg(Variable(:x)), PositionalArg(Variable(:y)), PositionalArg(Variable(:z))], [])])",
		"a +₁ b +₁ c" => "FunCall(Variable(:+₁), [PositionalArg(FunCall(Variable(:+₁), [PositionalArg(Variable(:a)), PositionalArg(Variable(:b))], [])), PositionalArg(Variable(:c))], [])",
		"a .+ b .+ c" => "FunCall(Broadcast(Variable(:+)), [PositionalArg(FunCall(Broadcast(Variable(:+)), [PositionalArg(Variable(:a)), PositionalArg(Variable(:b))], [])), PositionalArg(Variable(:c))], [])",
		"f(a).g(b)" => "FunCall(GetProperty(FunCall(Variable(:f), [PositionalArg(Variable(:a))], []), :g), [PositionalArg(Variable(:b))], [])",
		"foo(;x ; y)" => ErrorResult(),
        "f(;x...)" => "FunCall(Variable(:f), [], [SplatArg(Variable(:x))])",
        "+(x=1)" => "FunCall(Variable(:+), [PositionalArg(Assignment(IdentifierAssignment(:x), Literal(1)))], [])"
	],
	:unionall => [
		"A where B" => "WhereType(Variable(:A), [TyVar(:B, nothing, nothing)])",
		"A where {}" => "WhereType(Variable(:A), [])",
		"A where B where C" => "WhereType(WhereType(Variable(:A), [TyVar(:B, nothing, nothing)]), [TyVar(:C, nothing, nothing)])",
		"A where B<:C" => "WhereType(Variable(:A), [TyVar(:B, Variable(:C), nothing)])",
		"A where Z<:W<:X" => "WhereType(Variable(:A), [TyVar(:W, Variable(:X), Variable(:Z))])",
		"A where {Z<:W<:X, K}" => "WhereType(Variable(:A), [TyVar(:W, Variable(:X), Variable(:Z)), TyVar(:K, nothing, nothing)])"
	],
	:const => [
		"const a = 1" => "Declaration([VarDecl(IdentifierAssignment(:a), Literal(1), DECL_CONST)])",
		"const a::Int = 1" => "Declaration([VarDecl(TypedAssignment(IdentifierAssignment(:a), Variable(:Int)), Literal(1), DECL_CONST)])"
	],
	:local => [
		"local a" => "Declaration([VarDecl(IdentifierAssignment(:a), nothing, DECL_LOCAL)])",
		"local a::Int" => "Declaration([VarDecl(TypedAssignment(IdentifierAssignment(:a), Variable(:Int)), nothing, DECL_LOCAL)])",
		"local a::Int, (b=4), c::String" => "Declaration([VarDecl(TypedAssignment(IdentifierAssignment(:a), Variable(:Int)), nothing, DECL_LOCAL), VarDecl(IdentifierAssignment(:b), Literal(4), DECL_LOCAL), VarDecl(TypedAssignment(IdentifierAssignment(:c), Variable(:String)), nothing, DECL_LOCAL)])"
	],
	:global => [
		"global a" => "Declaration([VarDecl(IdentifierAssignment(:a), nothing, DECL_GLOBAL)])",
		"global a::Int" => "Declaration([VarDecl(TypedAssignment(IdentifierAssignment(:a), Variable(:Int)), nothing, DECL_GLOBAL)])",
		"global a::Int, (b=4), c::String" => "Declaration([VarDecl(TypedAssignment(IdentifierAssignment(:a), Variable(:Int)), nothing, DECL_GLOBAL), VarDecl(IdentifierAssignment(:b), Literal(4), DECL_GLOBAL), VarDecl(TypedAssignment(IdentifierAssignment(:c), Variable(:String)), nothing, DECL_GLOBAL)])"
	],
	:(=) => [
		"a = 2" => "Assignment(IdentifierAssignment(:a), Literal(2))",
		"a = b = 2" => "Assignment(IdentifierAssignment(:a), Assignment(IdentifierAssignment(:b), Literal(2)))",
		"a.b = 2" => "Assignment(FieldAssignment(Variable(:a), :b), Literal(2))",
		"a.b.c = 5" => "Assignment(FieldAssignment(GetProperty(Variable(:a), :b), :c), Literal(5))",
		"a.b[3] = 9" => "Assignment(RefAssignment(GetProperty(Variable(:a), :b), [PositionalArg(Literal(3))], []), Literal(9))",
		"a.b[3, 4] = 9" => "Assignment(RefAssignment(GetProperty(Variable(:a), :b), [PositionalArg(Literal(3)), PositionalArg(Literal(4))], []), Literal(9))",
		"a.b[3; x = 0] = 9" => ErrorResult(),
		"a.b[3 9] = 9" => ErrorResult(),
		"(a.b, c) = 2" => "Assignment(TupleAssignment([FieldAssignment(Variable(:a), :b), IdentifierAssignment(:c)]), Literal(2))",
		"y :: Int = 3" => "Assignment(TypedAssignment(IdentifierAssignment(:y), Variable(:Int)), Literal(3))",
		"{ faulty } = 9" => ErrorResult(),
		"(x..., y..., z) = (1,2)" => ErrorResult(),
		"[a; b] = 2" => ErrorResult(),
		"[a b] = 2" => ErrorResult(),
		"[a ;; b] = 2" => ErrorResult(),
        "f() = 3" => "Assignment(FunctionAssignment(ResolvedName([:f]), [], [], [], nothing), Literal(3))",
        "f(x) = x" => "Assignment(FunctionAssignment(ResolvedName([:f]), [FnArg(IdentifierAssignment(:x), nothing, nothing)], [], [], nothing), Variable(:x))",
		"f(x)::Int = x" => "Assignment(FunctionAssignment(ResolvedName([:f]), [FnArg(IdentifierAssignment(:x), nothing, nothing)], [], [], Variable(:Int)), Variable(:x))",
        "f(x::T) where T = x" => "Assignment(FunctionAssignment(ResolvedName([:f]), [FnArg(IdentifierAssignment(:x), nothing, Variable(:T))], [], [TyVar(:T, nothing, nothing)], nothing), Variable(:x))",
        "f(x::T) where T <: V = x" => "Assignment(FunctionAssignment(ResolvedName([:f]), [FnArg(IdentifierAssignment(:x), nothing, Variable(:T))], [], [TyVar(:T, Variable(:V), nothing)], nothing), Variable(:x))",
		"f()::T where T = x" => "Assignment(FunctionAssignment(ResolvedName([:f]), [], [], [TyVar(:T, nothing, nothing)], Variable(:T)), Variable(:x))",
        "x{y} = 2" => "Assignment(UnionAllAssignment(IdentifierAssignment(:x), [TyVar(:y, nothing, nothing)]), Literal(2))",
        "x{} = 2" => ErrorResult()
	],
	:comparison => [
		"a < b < c" => "Comparison(Variable(:a), [Variable(:<) => Variable(:b), Variable(:<) => Variable(:c)])",
		"a <= b < c" => "Comparison(Variable(:a), [Variable(:<=) => Variable(:b), Variable(:<) => Variable(:c)])",
		"a <: b <: c" => "Comparison(Variable(:a), [Variable(:<:) => Variable(:b), Variable(:<:) => Variable(:c)])",
		"a .< b == c" => "Comparison(Variable(:a), [Broadcast(Variable(:<)) => Variable(:b), Variable(:(==)) => Variable(:c)])"
	],
	:ref => [
		"x[2]" => "GetIndex(Variable(:x), [PositionalArg(Literal(2))])",
		"x[2,3]" => "GetIndex(Variable(:x), [PositionalArg(Literal(2)), PositionalArg(Literal(3))])",
		"x[2,x=3; z=9]" => ErrorResult(),
		"x[2,z...; y=0]" => ErrorResult(),
        "x[y=3]" => "GetIndex(Variable(:x), [PositionalArg(Assignment(IdentifierAssignment(:y), Literal(3)))])"
	],
	:do => [
		"f() do ; end" => "DoStatement(FunCall(Variable(:f), [], []), [], Block([]))",
		"f() do ; body end" => "DoStatement(FunCall(Variable(:f), [], []), [], Block([Variable(:body)]))",
		"f() do x, y; body end" => "DoStatement(FunCall(Variable(:f), [], []), [FnArg(IdentifierAssignment(:x), nothing, nothing), FnArg(IdentifierAssignment(:y), nothing, nothing)], Block([Variable(:body)]))",
		"f(x) do y body end" => "DoStatement(FunCall(Variable(:f), [PositionalArg(Variable(:x))], []), [FnArg(IdentifierAssignment(:y), nothing, nothing)], Block([Variable(:body)]))"
	],
	:tuple => [
		"(1,2,3)" => "TupleExpr([Literal(1), Literal(2), Literal(3)])",
		"(a=1, b=2)" => "NamedTupleExpr([NamedValue(:a, Literal(1)), NamedValue(:b, Literal(2))])",
		"(a=1, b=2; c=3)" => ErrorResult(),
		"(a=1, )" => "NamedTupleExpr([NamedValue(:a, Literal(1))])",
		"(;a=2, b=2)" => "NamedTupleExpr([NamedValue(:a, Literal(2)), NamedValue(:b, Literal(2))])",
		"(2=3, a=9)" => ErrorResult(),
		"((x+y) => 3, b=3)" => "NamedTupleExpr([ComputedNamedValue(FunCall(Variable(:+), [PositionalArg(Variable(:x)), PositionalArg(Variable(:y))], []), Literal(3)), NamedValue(:b, Literal(3))])",
		"(;x, y)" => "NamedTupleExpr([NamedValue(:x, Variable(:x)), NamedValue(:y, Variable(:y))])",
		"(;x.x, x.y)" => "NamedTupleExpr([NamedValue(:x, GetProperty(Variable(:x), :x)), NamedValue(:y, GetProperty(Variable(:x), :y))])",
        "(x..., )" => "TupleExpr([Splat(Variable(:x))])",
        "(x=y, z...)" => "NamedTupleExpr([NamedValue(:x, Variable(:y)), SplattedNamedValue(Variable(:z))])"
	],
	:string => [
		"\"hello \$world today\"" => "StringInterpolate([\"hello \", Variable(:world), \" today\"])",
		"\"hello \$(\"inner \$string here \$bar\") today\"" => "StringInterpolate([\"hello \", StringInterpolate([\"inner \", Variable(:string), \" here \", Variable(:bar)]), \" today\"])"
	],
	:(::) => [
		"::Int" => ErrorResult(),
		"a::Int" => "TypeAssert(Variable(:a), Variable(:Int))",
		"(a,b)::Tuple{Int, Int}" => "TypeAssert(TupleExpr([Variable(:a), Variable(:b)]), CallCurly(Variable(:Tuple), [Variable(:Int), Variable(:Int)]))"
	],
	:if => [
		"if a; b end" => "IfStmt([IfClause(Variable(:a), Block([Variable(:b)]))])",
		"if a; end" => "IfStmt([IfClause(Variable(:a), Block([]))])",
		"if a; b else c end" => "IfStmt([IfClause(Variable(:a), Block([Variable(:b)])), IfClause(nothing, Block([Variable(:c)]))])",
		"if a; b elseif c; d end" => "IfStmt([IfClause(Variable(:a), Block([Variable(:b)])), IfClause(Variable(:c), Block([Variable(:d)]))])",
		"if a; b elseif c; d else f end" => "IfStmt([IfClause(Variable(:a), Block([Variable(:b)])), IfClause(Variable(:c), Block([Variable(:d)])), IfClause(nothing, Block([Variable(:f)]))])"
	],
	:while => [
		"while true end" => "WhileStmt(Literal(true), Block([]))",
		"while true 2+3 end" => "WhileStmt(Literal(true), Block([FunCall(Variable(:+), [PositionalArg(Literal(2)), PositionalArg(Literal(3))], [])]))",
	],
	:break => [
		"break" => ErrorResult(),
		"while true; break end" => "WhileStmt(Literal(true), Block([BreakStmt()]))",
		"for i=1:10; break end" => "ForStmt([IdentifierAssignment(:i) => FunCall(Variable(:(:)), [PositionalArg(Literal(1)), PositionalArg(Literal(10))], [])], Block([BreakStmt()]))",
		"for i=1:10; if true break end end" => "ForStmt([IdentifierAssignment(:i) => FunCall(Variable(:(:)), [PositionalArg(Literal(1)), PositionalArg(Literal(10))], [])], Block([IfStmt([IfClause(Literal(true), Block([BreakStmt()]))])]))",
        "while break; 2 end" => "WhileStmt(BreakStmt(), Block([Literal(2)]))",
        "for i in [break;] 2 end" => "ForStmt([IdentifierAssignment(:i) => VCat(nothing, [BreakStmt()])], Block([Literal(2)]))"
	],
	:iterators => [
		"1:10" => "FunCall(Variable(:(:)), [PositionalArg(Literal(1)), PositionalArg(Literal(10))], [])",
		"1:10:5" => "FunCall(Variable(:(:)), [PositionalArg(Literal(1)), PositionalArg(Literal(10)), PositionalArg(Literal(5))], [])",
	],
	:continue => [
		"continue" => ErrorResult()
		"while true; continue end" => "WhileStmt(Literal(true), Block([ContinueStmt()]))"
	],
	:for => [
		"for x in y; end" => "ForStmt([IdentifierAssignment(:x) => Variable(:y)], Block([]))",
		"for x in y; w end" => "ForStmt([IdentifierAssignment(:x) => Variable(:y)], Block([Variable(:w)]))",
		"for x in y, z in l; w end" => "ForStmt([IdentifierAssignment(:x) => Variable(:y), IdentifierAssignment(:z) => Variable(:l)], Block([Variable(:w)]))",
		"for outer x in y; w end" => "ForStmt([OuterIdentifierAssignment(:x) => Variable(:y)], Block([Variable(:w)]))",
		"for outer x in y, z in l; w end" => "ForStmt([OuterIdentifierAssignment(:x) => Variable(:y), IdentifierAssignment(:z) => Variable(:l)], Block([Variable(:w)]))"
	],
	:update => [  
		"x += y" => "Update(:+=, IdentifierAssignment(:x), Variable(:y))",
		"x %= y" => "Update(:%=, IdentifierAssignment(:x), Variable(:y))",
		"x \$= y" => "Update(:\$=, IdentifierAssignment(:x), Variable(:y))",
		"x ≕ y" => "Update(:≕, IdentifierAssignment(:x), Variable(:y))",
		"x ⩴ y" => "Update(:⩴, IdentifierAssignment(:x), Variable(:y))",
		"(x, y) += z" => "Update(:+=, TupleAssignment([IdentifierAssignment(:x), IdentifierAssignment(:y)]), Variable(:z))",
		"x .+= y" => "BroadcastUpdate(:+=, Variable(:x), Variable(:y))",
		"(x, y) .+= z" => "BroadcastUpdate(:+=, TupleExpr([Variable(:x), Variable(:y)]), Variable(:z))",
		"x.y += z" => "Update(:+=, FieldAssignment(Variable(:x), :y), Variable(:z))"
	],
	:vect => [
		"[1,2,3]" => "Vect([Literal(1), Literal(2), Literal(3)])",
		"[1,2,x...]" => "Vect([Literal(1), Literal(2), Splat(Variable(:x))])",
		"[1,2,x...,5]" => "Vect([Literal(1), Literal(2), Splat(Variable(:x)), Literal(5)])",
		"[a=1, 2]" => ErrorResult(),
		"[1, 2; 3]" => ErrorResult(),
		"[1, 2; x=y]" => ErrorResult()
	],
	:vcat => [
		"[1 2;4 5]" => "VCat(nothing, [Row([Literal(1), Literal(2)]), Row([Literal(4), Literal(5)])])",
		"[1 2;4 x=5]" => ErrorResult(),
		"[1 2;4 x...]" => "VCat(nothing, [Row([Literal(1), Literal(2)]), Row([Literal(4), Splat(Variable(:x))])])"
	],
	:hcat => [
		"[1 2 3]" => "HCat(nothing, [Literal(1), Literal(2), Literal(3)])",
		"[1 2 x...]" => "HCat(nothing, [Literal(1), Literal(2), Splat(Variable(:x))])",
		"[1 2 x... 5]" => "HCat(nothing, [Literal(1), Literal(2), Splat(Variable(:x)), Literal(5)])",
		"[a=1 2]" => ErrorResult(),
		"[1 2; x=y]" => ErrorResult()
	],
	:ncat => [
		"[1 ;; 2 ;; 3]" => "NCat(nothing, 2, [Literal(1), Literal(2), Literal(3)])",
		"[1 ;; 2 ;; 3 ; x = 5]" => ErrorResult(),
		"[1 ;; 2 ;; 3 ; x...]" => ErrorResult(),
		"[1 ; 2 ;; 3 ; 4 ;; 5 ; 6]" => "NCat(nothing, 2, [NRow(1, [Literal(1), Literal(2)]), NRow(1, [Literal(3), Literal(4)]), NRow(1, [Literal(5), Literal(6)])])",
		"[1 ; 2 ;; 3 ; 4 ;;; 5 ; 6 ;; 7 ; 8 ;;; 9 ; 10 ;; 11 ; 12]" => "NCat(nothing, 3, [NRow(2, [NRow(1, [Literal(1), Literal(2)]), NRow(1, [Literal(3), Literal(4)])]), NRow(2, [NRow(1, [Literal(5), Literal(6)]), NRow(1, [Literal(7), Literal(8)])]), NRow(2, [NRow(1, [Literal(9), Literal(10)]), NRow(1, [Literal(11), Literal(12)])])])"
	],
	:typed_vcat => [
		"x[1 2;4 5]" => "VCat(Variable(:x), [Row([Literal(1), Literal(2)]), Row([Literal(4), Literal(5)])])"
	],
	:typed_hcat => [
		"x[1 2 3]" => "HCat(Variable(:x), [Literal(1), Literal(2), Literal(3)])"
	],
	:typed_ncat => [
		"x[1 ;; 2 ;; 3]" => "NCat(Variable(:x), 2, [Literal(1), Literal(2), Literal(3)])"
	],
    :comprehension => [
        "[x for x in y]" => "Comprehension(nothing, Generator(Variable(:x), [IterEq(IdentifierAssignment(:x), Variable(:y))]))",
        "[x for x in y if z]" => "Comprehension(nothing, Generator(Variable(:x), [Filter([IterEq(IdentifierAssignment(:x), Variable(:y))], Variable(:z))]))",
        "Int[x for x in z, w in l]" =>  "Comprehension(Variable(:Int), Generator(Variable(:x), [Cartesian([IterEq(IdentifierAssignment(:x), Variable(:z)), IterEq(IdentifierAssignment(:w), Variable(:l))])]))"
    ],
	:generator => [
		"(return x for x in y)" => ErrorResult(),
		"(x for a in as)" => "Generator(Variable(:x), [IterEq(IdentifierAssignment(:a), Variable(:as))])",
		"(x for a = as for b = bs if cond1 for c = cs if cond2)" => "Generator(Variable(:x), [IterEq(IdentifierAssignment(:a), Variable(:as)), Filter([IterEq(IdentifierAssignment(:b), Variable(:bs))], Variable(:cond1)), Filter([IterEq(IdentifierAssignment(:c), Variable(:cs))], Variable(:cond2))])",
		"(x for a = as if begin cond2 end)" => "Generator(Variable(:x), [Filter([IterEq(IdentifierAssignment(:a), Variable(:as))], Block([Variable(:cond2)]))])",
		"(a for x in xs if cond)" => "Generator(Variable(:a), [Filter([IterEq(IdentifierAssignment(:x), Variable(:xs))], Variable(:cond))])",
		"(xy for x in xs for y in ys)" => "Generator(Variable(:xy), [IterEq(IdentifierAssignment(:x), Variable(:xs)), IterEq(IdentifierAssignment(:y), Variable(:ys))])",
		"(xy for x in xs, y in ys)" => "Generator(Variable(:xy), [Cartesian([IterEq(IdentifierAssignment(:x), Variable(:xs)), IterEq(IdentifierAssignment(:y), Variable(:ys))])])",
		"(xy for x in xs for y in ys for z in zs)" => "Generator(Variable(:xy), [IterEq(IdentifierAssignment(:x), Variable(:xs)), IterEq(IdentifierAssignment(:y), Variable(:ys)), IterEq(IdentifierAssignment(:z), Variable(:zs))])",
		"(x for x in xs, y in ys if w)" => "Generator(Variable(:x), [Filter([Cartesian([IterEq(IdentifierAssignment(:x), Variable(:xs)), IterEq(IdentifierAssignment(:y), Variable(:ys))])], Variable(:w))])",
	],
	:struct => [
		"struct Foo end" => ErrorResult()
	],
	:abstract => [
		"abstract type Foo end" => ErrorResult()
	],
	:primitive => [
		"primitive type A 32 end" => ErrorResult()
	],
	:import => [
		"import Foo" => ErrorResult()
	],
	:using => [
		"using Foo" => ErrorResult()
	],
	:export => [
		"export foo" => ErrorResult()
	],
	:module => [
		"module Foo end" => ErrorResult()
	],
	:let => [
		"let x = y; z end" => "LetBinding(Union{Symbol, Pair{<:LValue, <:Expression}}[IdentifierAssignment(:x) => Variable(:y)], Block([Variable(:z)]))",
		"let ; z end" => "LetBinding(Union{Symbol, Pair{<:LValue, <:Expression}}[], Block([Variable(:z)]))",
		"let 2+2; 34 end" => ErrorResult(),
		"let x() = 3; x() end" => "LetBinding(Union{Symbol, Pair{<:LValue, <:Expression}}[FunctionAssignment(ResolvedName([:x]), [], [], [], nothing) => Literal(3)], Block([FunCall(Variable(:x), [], [])]))",
		"let x; 2 end" => "LetBinding(Union{Symbol, Pair{<:LValue, <:Expression}}[:x], Block([Literal(2)]))",
		"let (x, y) = 2; 2 end" => "LetBinding(Union{Symbol, Pair{<:LValue, <:Expression}}[TupleAssignment([IdentifierAssignment(:x), IdentifierAssignment(:y)]) => Literal(2)], Block([Literal(2)]))",
		"let x::Real = 2; x end" => "LetBinding(Union{Symbol, Pair{<:LValue, <:Expression}}[TypedAssignment(IdentifierAssignment(:x), Variable(:Real)) => Literal(2)], Block([Variable(:x)]))",
	],
    :docstring => [
        """
        \"\"\"
        Foo Bar Baz
        \"\"\"
        function x() end
        """ => "MacroExpansion(Docstring(StringInterpolate([\"Foo Bar Baz\\n\"]), FunctionDef(ResolvedName([:x]), [], [], [], nothing, Block([]))))"
    ],
    :boolops => [
        "a && b" => "FunCall(Variable(:&&), [PositionalArg(Variable(:a)), PositionalArg(Variable(:b))], [])",
		"x && (y = w)" => "FunCall(Variable(:&&), [PositionalArg(Variable(:x)), PositionalArg(Assignment(IdentifierAssignment(:y), Variable(:w)))], [])",
        "a || b" => "FunCall(Variable(:||), [PositionalArg(Variable(:a)), PositionalArg(Variable(:b))], [])"
    ],
    :? => [
        "x ? y : z" => "Ternary(Variable(:x), Variable(:y), Variable(:z))"
    ],
    :return => [
        "return" => "ReturnStmt(nothing)",
        "return 2" => "ReturnStmt(Literal(2))"
    ],
    :literals => [
        "true" => "Literal(true)",
        "false" => "Literal(false)",
        "'c'" => "Literal('c')",
        "3" => "Literal(3)",
    ],
    :typerel => [
        "x <: y" => "FunCall(Variable(:<:), [PositionalArg(Variable(:x)), PositionalArg(Variable(:y))], [])",
        "x >: y" => "FunCall(Variable(:>:), [PositionalArg(Variable(:x)), PositionalArg(Variable(:y))], [])"
    ],
    :transpose => [
        "x'" => "FunCall(Variable(Symbol(\"'\")), [PositionalArg(Variable(:x))], [])"
    ],
    :juxtapose => [
        "2x" => "FunCall(Variable(:*), [PositionalArg(Literal(2)), PositionalArg(Variable(:x))], [])",
        "2x + 2y" => "FunCall(Variable(:+), [PositionalArg(FunCall(Variable(:*), [PositionalArg(Literal(2)), PositionalArg(Variable(:x))], [])), PositionalArg(FunCall(Variable(:*), [PositionalArg(Literal(2)), PositionalArg(Variable(:y))], []))], [])"
    ],
    :literal => [
        "2" => "Literal(2)",
        "2.0" => "Literal(2.0)",
        "0b1010" => "Literal(0x0a)",
        "0x10" => "Literal(0x10)",
        "0o10" => "Literal(0x08)",
        "2.f0" => "Literal(2.0f0)",
        "'h'" => "Literal('h')",
        #"`h`" => "FunCall(Variable(:*), [PositionalArg(Literal(2)), PositionalArg(Variable(:x))], [])" TODO
    ]
]

toplevel_tests() = [
	:struct => [
		"struct Foo end" => "StructDefStmt(:Foo, Symbol[], nothing, [], [])",
		"struct Foo <: Bar end" => "StructDefStmt(:Foo, Symbol[], Variable(:Bar), [], [])",
		"struct Foo{X} <: Bar end" => "StructDefStmt(:Foo, [:X], Variable(:Bar), [], [])",
		"struct Foo{X} <: Bar{X} end" => "StructDefStmt(:Foo, [:X], CallCurly(Variable(:Bar), [Variable(:X)]), [], [])",
		"struct Foo{X<:Int} <: Bar{X} end" => "StructDefStmt(:Foo, [:X], CallCurly(Variable(:Bar), [Variable(:X)]), [], [])",
		"struct Foo{X, Y} <: Baz{Y} end" => "StructDefStmt(:Foo, [:X, :Y], CallCurly(Variable(:Baz), [Variable(:Y)]), [], [])",
		"struct Foo x end" => "StructDefStmt(:Foo, Symbol[], nothing, [StructField(:x, nothing, FIELD_NONE)], [])",
		"struct Foo x; y end" => "StructDefStmt(:Foo, Symbol[], nothing, [StructField(:x, nothing, FIELD_NONE), StructField(:y, nothing, FIELD_NONE)], [])",
		"struct Foo x::Int end" => "StructDefStmt(:Foo, Symbol[], nothing, [StructField(:x, Variable(:Int), FIELD_NONE)], [])",
		"struct Foo x::Int; y::String end" => "StructDefStmt(:Foo, Symbol[], nothing, [StructField(:x, Variable(:Int), FIELD_NONE), StructField(:y, Variable(:String), FIELD_NONE)], [])",
		"struct Foo const x::Int end" => ErrorResult(),
		"struct Foo x=3 end" => ErrorResult(),
		"mutable struct Foo x::Int; const y::String end" => "StructDefStmt(:Foo, Symbol[], nothing, [StructField(:x, Variable(:Int), FIELD_NONE), StructField(:y, Variable(:String), FIELD_CONST)], [])"
	],
	:abstract => [
		"abstract type Foo end" => "AbstractDefStmt(:Foo, Symbol[], nothing)",
		"abstract type Foo <: Bar end" => "AbstractDefStmt(:Foo, Symbol[], Variable(:Bar))",
		"abstract type Foo{X} <: Bar end" => "AbstractDefStmt(:Foo, [:X], Variable(:Bar))",
		"abstract type Foo{X} <: Bar{X} end" => "AbstractDefStmt(:Foo, [:X], CallCurly(Variable(:Bar), [Variable(:X)]))",
		"abstract type Foo{X<:Int} <: Bar{X} end" => "AbstractDefStmt(:Foo, [:X], CallCurly(Variable(:Bar), [Variable(:X)]))",
		"abstract type Foo{X, Y} <: Baz{Y} end" => "AbstractDefStmt(:Foo, [:X, :Y], CallCurly(Variable(:Baz), [Variable(:Y)]))",
		"abstract type A end" => "AbstractDefStmt(:A, Symbol[], nothing)",
		"abstract type A ; end" => "AbstractDefStmt(:A, Symbol[], nothing)",
		"abstract type A <: B end" => "AbstractDefStmt(:A, Symbol[], Variable(:B))",
		"abstract type A <: B{T,S} end" => "AbstractDefStmt(:A, Symbol[], CallCurly(Variable(:B), [Variable(:T), Variable(:S)]))",
		"abstract type A < B end" => ErrorResult()
	],
	:primitive => [
		"primitive type A 32 end" => "PrimitiveDefStmt(:A, Symbol[], nothing, Literal(32))",
		"primitive type A 32 ; end" => "PrimitiveDefStmt(:A, Symbol[], nothing, Literal(32))",
		"primitive type A <: B \n 8 \n end" => "PrimitiveDefStmt(:A, Symbol[], Variable(:B), Literal(8))"
	],
	:import => [
		"import Foo" => "ImportStmt([Dep(ImportId(:Foo))])",
		"import Foo: bar" => "SourceImportStmt(ImportId(:Foo), [Dep(ImportId(:bar))])",
		"import Foo.bar: baz" => "SourceImportStmt(ImportField(ImportId(:Foo), :bar), [Dep(ImportId(:baz))])",
		"import Foo.bar" => "ImportStmt([Dep(ImportField(ImportId(:Foo), :bar))])",
		"import Foo: baz, bing" => "SourceImportStmt(ImportId(:Foo), [Dep(ImportId(:baz)), Dep(ImportId(:bing))])",
		"import ..Foo" => "ImportStmt([Dep(ImportField(ImportRelative(2), :Foo))])",
		"import ..Foo, ..Baz" => "ImportStmt([Dep(ImportField(ImportRelative(2), :Foo)), Dep(ImportField(ImportRelative(2), :Baz))])",
		"import ..Foo: Baz" => "SourceImportStmt(ImportField(ImportRelative(2), :Foo), [Dep(ImportId(:Baz))])",
		"import Foo: baz as Bar, b.bar" => "SourceImportStmt(ImportId(:Foo), [AliasDep(ImportId(:baz), :Bar), Dep(ImportField(ImportId(:b), :bar))])",
		"import Foo as Bar" => "ImportStmt([AliasDep(ImportId(:Foo), :Bar)])",
		"import Foo as Bar, Bar as Baz" => "ImportStmt([AliasDep(ImportId(:Foo), :Bar), AliasDep(ImportId(:Bar), :Baz)])",
		"import Foo.Bar + 2" => ErrorResult(),
        "import Foo.@baz" => "ImportStmt([Dep(ImportField(ImportId(:Foo), Symbol(\"@baz\")))])",
        "import Foo: @baz" => "SourceImportStmt(ImportId(:Foo), [Dep(ImportId(Symbol(\"@baz\")))])",
        "import Foo.Bar: @baz" => "SourceImportStmt(ImportField(ImportId(:Foo), :Bar), [Dep(ImportId(Symbol(\"@baz\")))])",
		"import Foo: ..Bar" => ErrorResult(),
		"import Foo: ..Bar as Baz" => ErrorResult()
	],
	:using => [
		"using Foo" => "UsingStmt([ImportId(:Foo)])",
		"using Foo, Bar" => "UsingStmt([ImportId(:Foo), ImportId(:Bar)])",
		"using Foo, ..Bar" => "UsingStmt([ImportId(:Foo), ImportField(ImportRelative(2), :Bar)])",
		"using Foo: bar" => "SourceUsingStmt(ImportId(:Foo), [Dep(ImportId(:bar))])",
		"using Foo.bar: baz" => "SourceUsingStmt(ImportField(ImportId(:Foo), :bar), [Dep(ImportId(:baz))])",
		"using Foo.bar" => "UsingStmt([ImportField(ImportId(:Foo), :bar)])",
		"using Foo: baz, bing" => "SourceUsingStmt(ImportId(:Foo), [Dep(ImportId(:baz)), Dep(ImportId(:bing))])",
		"using ..Foo" => "UsingStmt([ImportField(ImportRelative(2), :Foo)])",
		"using Foo: baz as Bar, b.bar" => "SourceUsingStmt(ImportId(:Foo), [AliasDep(ImportId(:baz), :Bar), Dep(ImportField(ImportId(:b), :bar))])",
		"using Foo: ..Bar" => ErrorResult(),
		"using Foo: ..Bar as Baz" => ErrorResult(),
		"using ..Foo, ..Bar" => "UsingStmt([ImportField(ImportRelative(2), :Foo), ImportField(ImportRelative(2), :Bar)])"
	],
	:export => [
		"export foo" => "ExportStmt([:foo])",
		"export foo, bar, baz" => "ExportStmt([:foo, :bar, :baz])"
	],
	:module => [
		"module Foo end" => "ModuleStmt(true, :Foo, [])",
		"module Foo module Bar end end" => "ModuleStmt(true, :Foo, [ModuleStmt(true, :Bar, [])])",
		"function f() module Foo module Bar end end end" => ErrorResult(),
        "baremodule Foo end" => "ModuleStmt(false, :Foo, [])"
	],
	:inline => [
		"@inline function foobarbaz() end" => "ExprStmt(FunctionDef(ResolvedName([:foobarbaz]), [], [], [], nothing, Block([])))"
		"function foo() @inline function bar() end end" => "ExprStmt(FunctionDef(ResolvedName([:foo]), [], [], [], nothing, Block([FunctionDef(ResolvedName([:bar]), [], [], [], nothing, Block([]))])))"
	],
	:noinline => [
		"@noinline function foobarbaz() end" => "ExprStmt(FunctionDef(ResolvedName([:foobarbaz]), [], [], [], nothing, Block([])))"
		"function foo() @noinline function bar() end end" => "ExprStmt(FunctionDef(ResolvedName([:foo]), [], [], [], nothing, Block([FunctionDef(ResolvedName([:bar]), [], [], [], nothing, Block([]))])))"
	],
	:other_macros => [
		"@assume_effects :consistent function foobarbaz() end" => "ExprStmt(FunctionDef(ResolvedName([:foobarbaz]), [], [], [], nothing, Block([])))"
		"if @generated; 2 else 3 end" => "ExprStmt(IfStmt([IfClause(Literal(true), Block([Literal(2)])), IfClause(nothing, Block([Literal(3)]))]))"
	],
    :docstring => [
        """
        \"\"\"
        Foo Bar Baz
        \"\"\"
        function x() end
        """ => "MacroExpansionStmt(Docstring(StringInterpolate([\"Foo Bar Baz\\n\"]), ExprStmt(FunctionDef(ResolvedName([:x]), [], [], [], nothing, Block([])))))",
        """
        \"\"\"
        ...
        \"\"\"
        const a = 1
        """ => "MacroExpansionStmt(Docstring(StringInterpolate([\"...\\n\"]), ExprStmt(Declaration([VarDecl(IdentifierAssignment(:a), Literal(1), DECL_CONST)]))))",
        """
        \"\"\"
        ...
        \"\"\"
        global a = 1
        """ => "MacroExpansionStmt(Docstring(StringInterpolate([\"...\\n\"]), ExprStmt(Declaration([VarDecl(IdentifierAssignment(:a), Literal(1), DECL_GLOBAL)]))))",
        """
        \"\"\"
        ...
        \"\"\"
        baremodule M end
        """ => "MacroExpansionStmt(Docstring(StringInterpolate([\"...\\n\"]), ModuleStmt(false, :M, [])))",
        """
        \"\"\"
        ...
        \"\"\"
        module M end
        """ => "MacroExpansionStmt(Docstring(StringInterpolate([\"...\\n\"]), ModuleStmt(true, :M, [])))",
        """
        \"\"\"
        ...
        \"\"\"
        abstract type T1 end
        """ => "MacroExpansionStmt(Docstring(StringInterpolate([\"...\\n\"]), AbstractDefStmt(:T1, Symbol[], nothing)))",
        """
        \"\"\"
        ...
        \"\"\"
        mutable struct T2 end
        """ => "MacroExpansionStmt(Docstring(StringInterpolate([\"...\\n\"]), StructDefStmt(:T2, Symbol[], nothing, [], [])))",
        """
        \"\"\"
        ...
        \"\"\"
        struct T3 end
        """ => "MacroExpansionStmt(Docstring(StringInterpolate([\"...\\n\"]), StructDefStmt(:T3, Symbol[], nothing, [], [])))",
        """
        \"\"\"
        ...
        \"\"\"
        macro m(x) end
        """ => "MacroExpansionStmt(Docstring(StringInterpolate([\"...\\n\"]), ExprStmt(MacroDef(ResolvedName([:m]), [FnArg(IdentifierAssignment(:x), nothing, nothing)], [], nothing, Block([])))))",
        """
        \"\"\"
        ...
        \"\"\"
        f(x) = x
        """ => "MacroExpansionStmt(Docstring(StringInterpolate([\"...\\n\"]), ExprStmt(Assignment(FunctionAssignment(ResolvedName([:f]), [FnArg(IdentifierAssignment(:x), nothing, nothing)], [], [], nothing), Variable(:x)))))",
        """
        \"\"\"
        ...
        \"\"\"
        function f(x)
            x
        end
        """ => "MacroExpansionStmt(Docstring(StringInterpolate([\"...\\n\"]), ExprStmt(FunctionDef(ResolvedName([:f]), [FnArg(IdentifierAssignment(:x), nothing, nothing)], [], [], nothing, Block([Variable(:x)])))))",
        """
        \"\"\"
        ...
        \"\"\"
        f(x)
        """ => "MacroExpansionStmt(CallDocstring(StringInterpolate([\"...\\n\"]), ResolvedName([:f]), [FnArg(IdentifierAssignment(:x), nothing, nothing)], [], [], nothing))",
        """
        \"\"\"
        ...
        \"\"\"
        function f end
        """ => "MacroExpansionStmt(Docstring(StringInterpolate([\"...\\n\"]), ExprStmt(FunctionDef(ResolvedName([:f]), [], [], [], nothing, nothing))))",
        """
        \"\"\"
        ... \$testme end
        \"\"\"
        function f end
        """ => "MacroExpansionStmt(Docstring(StringInterpolate([\"... \", Variable(:testme), \" end\\n\"]), ExprStmt(FunctionDef(ResolvedName([:f]), [], [], [], nothing, nothing))))",
        """
        \"\"\"
        ... \$testme end
        \"\"\"
        foo(bar::baz)::bing
        """ => "MacroExpansionStmt(CallDocstring(StringInterpolate([\"... \", Variable(:testme), \" end\\n\"]), ResolvedName([:foo]), [FnArg(IdentifierAssignment(:bar), nothing, Variable(:baz))], [], [], Variable(:bing)))",
        """
        \"\"\"
        ... \$testme end
        \"\"\"
        foo(bar::baz)::bing where Bar
        """ => "MacroExpansionStmt(CallDocstring(StringInterpolate([\"... \", Variable(:testme), \" end\\n\"]), ResolvedName([:foo]), [FnArg(IdentifierAssignment(:bar), nothing, Variable(:baz))], [], [], WhereType(Variable(:bing), [TyVar(:Bar, nothing, nothing)])))",
        """
        \"\"\"
        ... testme end
        \"\"\"
        foo(bar; baz::Int = 2)
        """ => "MacroExpansionStmt(CallDocstring(StringInterpolate([\"... testme end\\n\"]), ResolvedName([:foo]), [FnArg(IdentifierAssignment(:bar), nothing, nothing)], [KwArg(:baz, Variable(:Int), Literal(2), false)], [], nothing))",
        """
        \"\"\"
        ... testme end
        \"\"\"
        foo(bar; baz::Int = 2)::Int
        """ => "MacroExpansionStmt(CallDocstring(StringInterpolate([\"... testme end\\n\"]), ResolvedName([:foo]), [FnArg(IdentifierAssignment(:bar), nothing, nothing)], [KwArg(:baz, Variable(:Int), Literal(2), false)], [], Variable(:Int)))"
    ]
]

@testset "Statement tests" begin
	@testset "$head" for (head, test_specs) in toplevel_tests()
		@testset "$input" for (input, output) in test_specs
			if output isa ErrorResult
				@test_throws ASTException expand_toplevel(childof(JuliaSyntax.parseall(SN, input), 1), ExpandCtx(true, false))
			else
				@test string(expand_toplevel(childof(JuliaSyntax.parseall(SN, input), 1), ExpandCtx(true, false))) == output
			end
		end
	end
end
@testset "Expression tests" begin
	@testset "$head" for (head, test_specs) in expr_tests()
		@testset "$input" for (input, output) in test_specs
			if output isa ErrorResult
				@test_throws ASTException expand_forms(childof(JuliaSyntax.parseall(SN, input), 1), ExpandCtx(true, false))
				@test string(expand_forms(childof(JuliaSyntax.parseall(SN, input), 1), ExpandCtx(true, false; error_context=SemanticAST.SilentErrorReporting()))) != nothing
			else
				ast = expand_forms(childof(JuliaSyntax.parseall(SN, input), 1), ExpandCtx(true, false))
				SemanticAST.visit((x) -> nothing, y->nothing, ast)
				@test string(ast) == output
			end
		end
	end
end
