
abstract type ASTNode end
abstract type Expression <: ASTNode end

struct SourcePosition 
	basenode::JuliaSyntax.SyntaxNode
end
Base.show(io::IO, pos::SourcePosition) = begin print(io, "SourcePosition") end

@ast_node struct TyVar <: ASTNode
	name::Union{Symbol, Nothing}
	ub::Any
	lb::Any
end
export TyVar

abstract type LValue <: ASTNode end
@ast_node struct FnArg <: ASTNode
	binding::Union{LValue, Nothing}
	default_value::Union{ASTNode, Nothing}
    type::Union{Expression, Nothing}
end
export FnArg, LValue

struct KwArg <: ASTNode
	name::Symbol
	type::Union{ASTNode, Nothing}
	default_value::Union{ASTNode, Nothing}
	is_vararg::Bool
	location::Union{SourcePosition, Nothing}
	KwArg(name, type, default_value, basenode, is_vararg = false) = new(name, type, default_value, is_vararg, isnothing(basenode) ? nothing : SourcePosition(basenode))
end
@as_record KwArg
Base.:(==)(a::KwArg, b::KwArg) = a.name == b.name && a.type == b.type && a.default_value == b.default_value && a.is_vararg == b.is_vararg
export KwArg

@enum FieldAttributes FIELD_NONE=0 FIELD_CONST=1
Base.show(io::IO, d::FieldAttributes) = print(io, d)
Base.:(|)(a::FieldAttributes, b::FieldAttributes) = FieldAttributes(Int(a) | Int(b))
@ast_node struct StructField <: ASTNode 
	name::Symbol
	type::Union{Expression, Nothing}
	attributes::FieldAttributes
end
export StructField, FieldAttributes

Base.:(==)(a::StructField, b::StructField) = a.name == b.name && a.type == b.type && a.attributes == b.attributes

@ast_data CallArg <: ASTNode begin 
	PositionalArg(body::Expression)
	KeywordArg(name::Symbol, value::Expression)
	SplatArg(body::Union{Expression, Nothing})
end
export CallArg, PositionalArg, KeywordArg, SplatArg

const PositionalArgs = Union{PositionalArg, SplatArg}
export PositionalArgs

@enum DeclAttributes DECL_NONE=0 DECL_CONST=1 DECL_LOCAL=2 DECL_GLOBAL=4
Base.show(io::IO, d::DeclAttributes) = print(io, d)
@ast_node struct VarDecl <: ASTNode
	binding::LValue
	value::Union{Expression, Nothing}
	flags::DeclAttributes
end
export VarDecl

@ast_data NamedTupleBody <: ASTNode begin
	NamedValue(name::Symbol, value::Expression)
	ComputedNamedValue(name::Expression, value::Expression)
    SplattedNamedValue(splat::Expression)
end
export NamedTupleBody, NamedValue, ComputedNamedValue, SplattedNamedValue

@ast_node struct IfClause <: ASTNode
	cond::Union{Expression, Nothing}
	body::Expression
end
export IfClause

@ast_data Rows <: ASTNode begin 
	Splat(body::Expression)
	Row(elems::Vector{Union{Expression, Splat}})
	NRow(dim::Int, elems::Vector{Union{NRow, Expression}})
end
export Rows, Splat, Row, NRow

@ast_data Iterspec <: ASTNode begin 
	IterEq(lhs::LValue, rhs::Expression)
	Filter(inner::Vector{Iterspec}, cond::Expression)
end
export Iterspec, IterEq, Filter

@ast_data ImportPath <: ASTNode begin
	ImportField(source::ImportPath, name::Symbol)
	ImportId(name::Symbol)
	ImportRelative(levels::Int)
end
export ImportPath, ImportField, ImportId, ImportRelative

@ast_data DepClause <: ASTNode begin
	Dep(path::ImportPath)
	AliasDep(path::ImportPath, alias::Symbol)
end
export DepClause, Dep, AliasDep

@ast_data FunctionName <: ASTNode begin 
	ResolvedName(path::Vector{Symbol})
	DeclName(binding::Union{LValue, Nothing}, typ::Expression)
	TypeFuncName(receiver::Expression, args::Vector{Union{Expression, TyVar}})
	AnonFuncName()
end
export FunctionName, ResolvedName, DeclName, TypeFuncName, AnonFuncName

@ast_data ToplevelStmts <: ASTNode begin 
	StructDefStmt(name::Symbol, params::Vector{Symbol}, super::Union{Expression, Nothing}, fields::Vector{StructField}, cstrs::Vector{Expression})
	AbstractDefStmt(name::Symbol, params::Vector{Symbol}, super::Union{Expression, Nothing})
	PrimitiveDefStmt(name::Symbol, params::Vector{Symbol}, super::Union{Expression, Nothing}, size::Expression)
	UsingStmt(mods::Vector{ImportPath})
	ImportStmt(mods::Vector{DepClause})
	SourceUsingStmt(sourcemod::ImportPath, stmts::Vector{DepClause})
	SourceImportStmt(sourcemod::ImportPath, stmts::Vector{DepClause})
	ExportStmt(syms::Vector{Symbol})
	ModuleStmt(std_imports::Bool, name::Symbol, body::Vector{ToplevelStmts})
	ExprStmt(expr::Expression)
	ToplevelStmt(exprs::Vector{ToplevelStmts})
    MacroExpansionStmt(value::Any)
end
export ToplevelStmts, StructDefStmt, AbstractDefStmt, PrimitiveDefStmt, UsingStmt, ImportStmt, SourceUsingStmt, SourceImportStmt, ExportStmt, ModuleStmt, ExprStmt, ToplevelStmt, MacroExpansionStmt

@ast_data Expression <: ASTNode begin
	Literal(expr::Any)
	Variable(name::Symbol)
	FunctionDef(name::FunctionName, arguments::Vector{FnArg}, kw_args::Vector{KwArg}, sparams::Vector{TyVar}, rett::Union{Expression, Nothing}, body::Union{Expression, Nothing})
	MacroDef(name::ResolvedName, arguments::Vector{FnArg}, sparams::Vector{TyVar}, rett::Union{Expression, Nothing}, body::Union{Expression, Nothing})
	Block(exprs::Vector{Expression})
	LetBinding(bindings::Vector{Union{Pair{<:LValue, <:Expression}, Symbol}}, body::Expression)
	TryCatch(body::Expression, catch_var::Union{Symbol, Nothing}, catch_body::Union{Expression, Nothing}, else_body::Union{Expression, Nothing}, finally_body::Union{Expression, Nothing})
	CallCurly(receiver::Expression, args::Vector{Union{Expression, TyVar}})
	Comparison(first::Expression, clauses::Vector{Pair{Expression, Expression}})
	Broadcast(op::Expression)
	FunCall(receiver::Expression, pos_args::Vector{PositionalArgs}, kw_args::Vector{Union{KeywordArg, SplatArg}})
	GetIndex(arr::Expression, arguments::Vector{PositionalArgs})
	GetProperty(rec::Expression, prop::Union{Symbol, Literal})
	Assignment(lhs::LValue, rhs::Expression)
	Update(op::Symbol, lhs::LValue, rhs::Expression, dotted::Bool)
	WhereType(type::Expression, vars::Vector{TyVar})
	Declaration(vars::Vector{VarDecl})
	DoStatement(func::Expression, arguments::Vector{FnArg}, body::Expression)
	TupleExpr(exprs::Vector{Union{Expression, Splat}})
	NamedTupleExpr(exprs::Vector{NamedTupleBody})
	StringInterpolate(components::Vector{Union{String, Expression}})
	TypeAssert(val::Expression, typ::Expression)
	IfStmt(clauses::Vector{IfClause})
	WhileStmt(cond::Expression, body::Expression)
	BreakStmt()
	ContinueStmt()
    ReturnStmt(retval::Union{Expression, Nothing})
	ForStmt(iters::Vector{Pair{LValue, Expression}}, body::Expression)
	Vect(elems::Vector{Union{Expression, Splat}})
	HCat(type::Union{Expression, Nothing}, elems::Vector{Union{Expression, Splat}})
	VCat(type::Union{Expression, Nothing}, rows::Vector{Union{Row, Expression, Splat}})
	NCat(type::Union{Expression, Nothing}, dim::Int, rows::Vector{Union{NRow, Expression}})
	Generator(flatten::Bool, expr::Expression, iterators::Vector{Iterspec})
	Comprehension(type::Union{Expression, Nothing}, gen::Generator)
	Quote(ast::JuliaSyntax.SyntaxNode)
    MacroExpansion(value::Any)
    Ternary(cond::Expression, then::Expression, els::Expression)
end
export Expression, Literal, Variable, FunctionDef, MacroDef, Block, LetBinding, TryCatch, CallCurly, Comparison, Broadcast, FunCall, GetIndex, GetProperty, Assignment, Update, WhereType, Declaration, DoStatement, TupleExpr, NamedTupleExpr, StringInterpolate, TypeAssert, IfStmt, WhileStmt, BreakStmt, ContinueStmt, ReturnStmt, ForStmt, Vect, HCat, VCat, NCat, Generator, Comprehension, Quote, MacroExpansion, Ternary

@ast_data LValueImpl <: LValue begin 
	IdentifierAssignment(id::Symbol)
	OuterIdentifierAssignment(id::Symbol)
	FieldAssignment(obj::Expression, name::Symbol)
	TupleAssignment(params::Vector{LValue})
	RefAssignment(arr::Expression, arguments::Vector{PositionalArgs}, kwargs::Vector{KeywordArg})
	VarargAssignment(tgt::Union{Nothing, LValue})
	TypedAssignment(lhs::LValue, type::Expression)
	NamedTupleAssignment(params::Vector{Union{IdentifierAssignment, TypedAssignment}})
	FunctionAssignment(name::FunctionName, args_stmts::Vector{FnArg}, kwargs_stmts::Vector{KwArg}, sparams::Vector{TyVar}, rett::Union{Expression, Nothing})
	BroadcastAssignment(lhs::LValue)
    UnionAllAssignment(name::LValue, tyargs::Vector{TyVar})
end
export LValueImpl, IdentifierAssignment, OuterIdentifierAssignment, FieldAssignment, TupleAssignment, RefAssignment, VarargAssignment, TypedAssignment, NamedTupleAssignment, FunctionAssignment, BroadcastAssignment, UnionAllAssignment

@generated function Base.show(io::IO, a::T) where T<:Union{Expression, VarDecl, NamedTupleBody, IfClause, Rows, Iterspec, ImportPath, DepClause, FunctionName, ToplevelStmts, LValueImpl, CallArg, FnArg, TyVar, KwArg, StructField}
	outbody = []
	fldnames = filter(x -> x != :location, fieldnames(T))
	for fld in fldnames[1:end-1]
		push!(outbody, :(show(io, a.$fld)))
		push!(outbody, :(print(io, ", ")))
	end
	if length(fldnames) > 0
		push!(outbody, :(show(io, a.$(fldnames[end]))))
	end
	return quote
		print(io, string(nameof(T)))
		print(io, "(")
		$(outbody...)
		print(io, ")")
	end
end

const ASTNodes = Union{Expression, VarDecl, NamedTupleBody, IfClause, Rows, Iterspec, ImportPath, DepClause, FunctionName, ToplevelStmts, LValueImpl, CallArg, FnArg, TyVar, LValue, KwArg, StructField}
function Base.show(io::IO, v::Vector{T}) where T<:Union{ASTNodes, Tuple{Vararg{ASTNodes}}, Pair{X, Y} where {X<:ASTNodes,Y<:ASTNodes}, Union{String, Y} where Y <: ASTNodes}
	print(io, "[")
	for el in v[1:end-1]
		show(io, el)
		print(io, ", ")
	end
	if length(v) > 0
		show(io, v[end])
	end
	print(io, "]")
end

function Base.show(io::IO, (l, r)::Pair{N1, N2}) where {N1 <: ASTNodes, N2 <: ASTNodes}
	show(io, l)
	print(io, " => ")
	show(io, r)
end

@generated function Base.:(==)(a::T, b::T) where T<:Union{Expression, VarDecl, NamedTupleBody, IfClause, Rows, Iterspec, ImportPath, DepClause, FunctionName, ToplevelStmts, LValueImpl, CallArg, FnArg}
	if length(fieldnames(T)) == 0 
		return true
	end
	return :(Base.:(&)($(map(x->:(a.$x == b.$x), filter(x->x != :location, fieldnames(T)))...)))
end
