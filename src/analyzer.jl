"The error reporting mode to use"
abstract type ErrorReporting end

"Create an ASTException when an issue is encountered and continue with the fallback."
struct ExceptionErrorReporting <: ErrorReporting end
"Do nothing when an issue is encountered and continue with the fallback."
struct SilentErrorReporting <: ErrorReporting end

"""
The abstract type for macro expansion contexts.

There are two macro extension points in the analyzer: `resolve_toplevel_macro(ast::SyntaxNode, ::MacroContext, ::Val{Symbol}, args::Vector{SyntaxNode}, ctx::ExpandCtx)::ToplevelStmts` and `resolve_macro(ast, ::MacroContext, ::Val{Symbol}, args, ctx)::Expression`.
Both share the same signature:

* `ast`: The SyntaxNode root of the macro invocation.
* `MacroContext`: The context with which to resolve macros in. Implement a new `MacroContext` by implementing `resolve_toplevel_macro` and `resolve_macro` that accept it; the provided one is `DefaultMacroContext`.
* `Val{Symbol}`: The macro's name (in `Val` form).
* `args`: The SyntaxNodes that represent the arguments to the macro.
* `ctx`: The expansion context inside which the analysis is being done.

They differ in that `resolve_toplevel_macro` returns a `TopLevelStmts` (a statement that can only exist at the top level), while `resolve_macro` returns an `Expression`. An example of how to write a macro analyzer
can be seen in the default implementation for `@inline` and `@noinline`:

```
resolve_macro(ast, ::DefaultMacroContext, ::Union{Val{Symbol("@inline")}, Val{Symbol("@noinline")}, Val{Symbol("@inbounds")}}, args, ctx) = expand_forms(args[1], ctx)
```

From the perspective of the default analyzer `@inline` and `@noinline` are no-ops, so analysis continues by simply calling back into `expand_forms` on the first
argument.

"""
abstract type MacroContext end

"""
The default macro analysis context.

Currently implements top-level support for:

	* @doc
	* @inline, @noinline
	* @assume_effects, @constprop

Expression-level support is provided for:

	* @doc
	* @inline, @noinline
	* @eval
	* @generated
	* @assume_effects
"""
struct DefaultMacroContext <: MacroContext end

"""
	ExpandCtx(is_toplevel::Bool=false, is_loop::Bool= false; macro_context=DefaultMacroContext(), error_context=ExceptionErrorReporting())

The context in which to perform expansion from SyntaxNodes to ASTNodes.

* `is_toplevel`: is the analyzed expression at the top level or not?
* `is_loop`: is the expression in a loop or not (used for determining if `break` or `continue` are valid)?
* `macro_context`: The context with which to expand macros. See the discussion in readme.
* `error_context`: The error reporting context. By default, two are provided ([ExceptionErrorReporting](@ref) and [SilentErrorReporting](@ref)), with exceptions being the default.
"""
struct ExpandCtx{ER <: ErrorReporting, MC <: MacroContext}
	is_toplevel::Bool
	is_loop::Bool
	macro_context::MC
	error_context::ER
	ExpandCtx(is_toplevel::Bool=false, is_loop::Bool=false;
		 macro_context::MC=DefaultMacroContext(), error_context::ER=ExceptionErrorReporting()) where {ER, MC} =
		new{ER, MC}(is_toplevel, is_loop, macro_context, error_context)
	ExpandCtx(base::ExpandCtx{ER, MC};
		is_toplevel::Union{Bool, Nothing}=nothing,
		is_loop::Union{Bool, Nothing}=nothing)  where {ER, MC}= new{ER, MC}(
			isnothing(is_toplevel) ? false : is_toplevel,
			isnothing(is_loop) ? base.is_loop : is_loop,
            base.macro_context, base.error_context)
end

handle_error(context::ExpandCtx, node::JuliaSyntax.SyntaxNode, reporting::ExceptionErrorReporting, message::String, continuation::Union{Function, Nothing}) = throw(ASTException(node, message))
handle_error(context::ExpandCtx, node::JuliaSyntax.SyntaxNode, reporting::SilentErrorReporting, message::String, continuation::Union{Function, Nothing}) = if !isnothing(continuation) continuation() else nothing end

isdecl(ast) = @match ast begin
	SN(SH(K"::", _), _) => true
	_ => false
end
isassignment(ast) = @match ast begin
	SN(SH(K"=", _), _) => true
	_ => false
end
iskwarg(ast) = @match ast begin
	SN(SH(K"=", _), _) => true
	_ => false
end
identifier_name(ast) = @match ast begin
	SN(SH(K"Identifier", _), _) => ast
	_ => nothing
end
eventually_call = @λ begin
	SN(SH(K"call", _), _) => true
	SN(SH(K"where", _), [name, _...]) => eventually_call(name)
	SN(SH(K"::", _), [name, _]) => eventually_call(name)
	_ => false
end

isdotop_named(ast) = let idname = identifier_name(ast); !isnothing(idname) && JuliaSyntax.is_dotted(JuliaSyntax.head(idname)) end
check_dotop(ctx, ast) =
	if isdotop_named(ast)
		handle_error(ctx, ast, ctx.error_context, "Invalid function name", nothing)
	else
		@match ast begin
			SN(SH(K".", _), [rec, name]) => check_dotop(ctx, name)
			SN(SH(K"quote" || K"break", _), [body]) => check_dotop(ctx, body)
			_ => nothing
		end;
		ast
	end


kindof(ex) = JuliaSyntax.kind(JuliaSyntax.head(ex))
childof = JuliaSyntax.child
just_argslist(args) = kindof(args[1]) ∈ KSet"tuple block ..." || (kindof(args[1]) == K"where" && just_argslist(args[1]))

function flatten_where_expr(ex)
	vars = Any[]
	if kindof(ex) != K"where"
		throw(ASTException(ex, "Invalid expression (internal error: flattening non-where)")) # using direct throw due to fatal error
	end
	while kindof(ex) == K"where"
		@match ex begin
			SN(SH(K"where", _), [body, SN(SH(K"braces", _), [current_vars...])]) => begin
				push!.((vars, ), current_vars)
				ex = body
			end
			SN(SH(K"where", _), [body, var]) => begin
				push!(vars, var)
				ex = body
			end
			_ => ex
		end
	end
	return (ex, vars)
end

function analyze_typevar(ex, ctx)
	check_sym(s) = (kindof(s) == K"Identifier" ? Expr(s) : handle_error(ctx, s, ctx.error_context, "Invalid type variable (non-symbol)", () -> TyVar(gensym(), nothing, nothing, ex)))
	@match ex begin
		ex && GuardBy(isatom) => TyVar(check_sym(ex), nothing, nothing, ex)
		SN(SH(K"Identifier", _), _) => TyVar(check_sym(ex), nothing, nothing, ex)
		SN(SH(K"comparison", _), [a, SN(SH(K"<:", _), _), b, SN(SH(K"<:", _), _), c]) => TyVar(check_sym(b), expand_forms(c, ctx), expand_forms(a, ctx), ex)
		SN(SH(K"<:", _), [a, b]) => TyVar(check_sym(a), expand_forms(b, ctx), nothing, ex)
		SN(SH(K">:", _), [a, b]) => TyVar(check_sym(a), nothing, expand_forms(b, ctx), ex)
		_ => handle_error(ctx, ex, ctx.error_context, "invalid variable expression in \"where\"", () -> TyVar(gensym(), nothing, nothing, ex))
	end
end

analyze_tuple_assignment(expr, ctx) = @match expr begin
	SN(SH(K"Identifier", _), _) && name => IdentifierAssignment(Expr(name), expr)
	SN(SH(K"::", _), [name, type]) => TypedAssignment(IdentifierAssignment(Expr(name)), expand_forms(type, ctx), expr)
	_ => handle_error(ctx, expr, ctx.error_context, "invalid assignment location", () -> IdentifierAssignment(gensym(), expr))
end

unquote = @λ begin
	SN(SH(K"quote", _), [body]) => Expr(body)
end
analyze_lvalue(expr, ctx; is_for=false) = @match expr begin
	SN(SH(K"Identifier", _), _) && id =>
		if Expr(id) ∈ [:ccall, :global]
			handle_error(ctx, expr, ctx.error_context, "invalid assignment location", () -> IdentifierAssignment(gensym(), expr))
		else
			IdentifierAssignment(Expr(id), expr)
		end
	SN(SH(K".", _), [a,b]) => FieldAssignment(expand_forms(a, ctx), unquote(b), expr)
	SN(SH(K"tuple", _), [_, args..., SN(SH(K"parameters", _), _)]) => handle_error(ctx, expr, ctx.error_context, "invalid assignment location", () -> IdentifierAssignment(gensym(), expr))
	SN(SH(K"tuple", _), [SN(SH(K"parameters", _), params)]) =>
		NamedTupleAssignment(map(x -> analyze_tuple_assignment(x, ctx), params), expr)
	SN(SH(K"tuple", _), [args...]) => begin
			has_varargs = false
			assignment_args = LValue[]
			for arg in args
				@match arg begin
					SN(SH(K"...", _), body) => begin
						if has_varargs
							push!(assignment_args, handle_error(ctx, arg, ctx.error_context, "multiple \"...\" on lhs of assignment", () -> IdentifierAssignment(gensym(), expr)))
						end
						has_varargs = true
						push!(assignment_args, VarargAssignment(length(body) > 0 ? analyze_lvalue(body[1], ctx) : nothing, arg))
					end
					arg => push!(assignment_args, analyze_lvalue(arg, ctx))
				end
			end
			TupleAssignment(assignment_args, expr)
		end
	SN(SH(K"typed_hcat", _), _) => handle_error(ctx, expr, ctx.error_context, "invalid spacing in left side of indexed assignment", () -> IdentifierAssignment(gensym(), expr))
	SN(SH(K"typed_vcat" || K"typed_ncat", _), _) => handle_error(ctx, expr, ctx.error_context, "unexpected \";\" in left side of indexed assignment", () -> IdentifierAssignment(gensym(), expr))
	SN(SH(K"ref", _), [a, idxs...]) => RefAssignment(expand_forms(a, ctx), split_arguments(idxs, ctx)..., expr)
	SN(SH(K"::", _), [typ]) => handle_error(ctx, expr, ctx.error_context, "invalid assignment location", () -> IdentifierAssignment(gensym(), expr))
	SN(SH(K"::", _), [call && GuardBy(eventually_call), T]) && funspec => FunctionAssignment(expand_function_name(funspec, ctx)..., expr)
	SN(SH(K"::", _), [x, T]) => TypedAssignment(analyze_lvalue(x, ctx), expand_forms(T, ctx), expr)
	SN(SH(K"vcat" || K"ncat", _), _) => handle_error(ctx, expr, ctx.error_context, "use \"(a, b) = ...\" to assign multiple values", () -> IdentifierAssignment(gensym(), expr))
	SN(SH(K"call" || K"where", _), _) && name => FunctionAssignment(expand_function_name(name, ctx)..., expr)
    SN(SH(K"curly", _), [name, tyargs...]) => length(tyargs) == 0 ? handle_error(ctx, expr, ctx.error_context, "empty type parameter list", () -> analyze_lvalue(name, ctx)) : UnionAllAssignment(analyze_lvalue(name, ctx), analyze_typevar.(tyargs, (ctx, )), expr)
	SN(SH(K"outer", _), [SN(SH(K"Identifier", _), _) && id]) =>
		if is_for
			OuterIdentifierAssignment(Expr(id), expr)
		else
			handle_error(ctx, expr, ctx.error_context, "no outer local variable declaration exists", () -> IdentifierAssignment(Expr(id), expr))
		end
	_ => handle_error(ctx, expr, ctx.error_context, "invalid assignment location", () -> IdentifierAssignment(gensym(), expr))
end

expr_contains_p(pred, expr, filter = x -> true) =
	filter(expr) && (pred(expr) || @match expr begin
		SN(SH(K"quote", _), _) => false
		SN(_, args) => any(expr_contains_p.(pred, args, filter))
		e => throw("unhandled $e")
	end)

isparam = @λ begin SN(SH(K"parameters", _), _) => true; _ => false end
contains_destructuring = @λ begin
	SN(SH(K"::" || K"=", _), _) => true
	_ => false
end
is_return = @λ begin
	SN(SH(K"return", _), _) => true
	_ => false
end
contains_return(e) = expr_contains_p(is_return, e)
check_recursive_assignment(expr) =
	if expr_contains_p(contains_destructuring, expr)
		false
	else
		true
	end
analyze_argument(expr, is_kw, ctx) = @match (expr, is_kw) begin
	(SN(SH(K"tuple", _), _), false) => (FnArg(analyze_lvalue(expr, ctx), nothing, nothing, expr), false)
	(SN(SH(K"::", _), [binding, typ]), false) => check_recursive_assignment(binding) ?
		(FnArg(analyze_lvalue(binding, ctx), nothing, expand_forms(typ, ctx), expr), false) :
		(handle_error(ctx, expr, ctx.error_context, "invalid recursive destructuring syntax", () -> FnArg(IdentifierAssignment(gensym(), expr), nothing, expand_forms(typ, ctx), expr)), false)
	(SN(SH(K"::", _), [typ]), false) => (FnArg(nothing, nothing, expand_forms(typ, ctx), expr), false)
	(SN(SH(K"=", _), [head, default]), is_kw) => (let (base, _) = analyze_argument(head, false, ctx); FnArg(base.binding, expand_forms(default, ctx), base.type, expr) end, true)
	(SN(SH(K"...", _), [bound]), false) => (FnArg(VarargAssignment(analyze_lvalue(bound, ctx), expr), nothing, nothing, expr), false)
	(SN(SH(K"...", _), []), false) => (FnArg(VarargAssignment(nothing, expr), nothing, nothing, expr), false)
	(_, false) => (FnArg(analyze_lvalue(expr, ctx), nothing, nothing, expr), false)
	(_, true) => (handle_error(ctx, expr, ctx.error_context, "optional positional arguments must occur at end", () -> first(analyze_argument(expr, false, ctx))), true)
	(_, _) => (handle_error(ctx, expr, ctx.error_context, "invalid argument syntax", () -> FnArg(IdentifierAssignment(gensym(), expr), nothing, nothing, expr)), is_kw)
end
analyze_kwargs(expr, ctx) = @match expr begin
	SN(SH(K"parameters", _), _) => handle_error(ctx, expr, ctx.error_context, "more than one semicolon in argument list", () -> KwArg(gensym(), nothing, nothing, expr))
	SN(SH(K"=", _), [SN(SH(K"::", _), [SN(SH(K"Identifier", _), ) && name, type]), body]) => begin
		KwArg(Expr(name), expand_forms(type, ctx), expand_forms(body, ctx), expr)
	end
	SN(SH(K"=", _), [SN(SH(K"Identifier", _), _) && name, body]) => KwArg(Expr(name), nothing, expand_forms(body, ctx), expr)
	SN(SH(K"...", _), [SN(SH(K"Identifier", _), _) && name]) => KwArg(Expr(name), nothing, nothing, expr, true)
	SN(SH(K"=", _), [SN(SH(K"::", _), [name, type]), body]) => handle_error(ctx, expr, ctx.error_context, "is not a valid function argument name", () -> KwArg(gensym(), expand_forms(type, ctx), expand_forms(body, ctx), expr))
	SN(SH(K"=", _), [name, body]) => handle_error(ctx, expr, ctx.error_context, "is not a valid function argument name", () -> KwArg(Expr(name), nothing, expand_forms(body, ctx), expr))
	SN(SH(K"...", _), [name]) => handle_error(ctx, expr, ctx.error_context, "is not a valid function argument name", () -> KwArg(gensym(), nothing, nothing, expr))
	SN(SH(K"Identifier", _), _) && ident => KwArg(Expr(ident), nothing, nothing, expr)
	SN(SH(K"::", _), [SN(SH(K"Identifier", _), _) && ident, type]) => KwArg(Expr(ident), expand_forms(type, ctx), nothing, expr)
	other => handle_error(ctx, expr, ctx.error_context, "invalid keyword argument syntax", () -> KwArg(gensym(), nothing, nothing, expr))
end

hasduplicates(array) = length(unique(array)) != length(array)

unpack_fn_name(e, ctx) = @match e begin
	SN(SH(K".", _), [rec, SN(SH(K"quote", _), [field && SN(SH(K"Identifier", _), _)])]) => push!(unpack_fn_name(rec, ctx), Expr(field))
	SN(SH(K"Identifier", _), _) && name => [Expr(name)]
	expr => handle_error(ctx, expr, ctx.error_context, "invalid function name", () -> [gensym()])
end

parse_func_name(ctx, receiver, args, e) = TypeFuncName(expand_forms(receiver, ctx), [let param = extract_implicit_whereparam(arg, ctx); isnothing(param) ? expand_forms(arg, ctx) : param end for arg in args], e)
resolve_function_name(e, ctx) = @match e begin
	SN(SH(K"Identifier", _), _) && name => ResolvedName([Expr(name)], e) # symbols are valid
	SN(SH(K".", _), _) && e => ResolvedName(unpack_fn_name(e, ctx), e)
	SN(SH(K"::", _), [name, type]) => DeclName(analyze_lvalue(name, ctx), expand_forms(type, ctx), e)
	SN(SH(K"::", _), [type]) => DeclName(nothing, expand_forms(type, ctx), e)
    SN(SH(K"curly", _), [receiver, args..., SN(SH(K"parameters", _), _)]) => handle_error(ctx, e, ctx.error_context, "unexpected semicolon", () -> parse_func_name(ctx, receiver, args, e))
    SN(SH(K"curly", _), [receiver, args...]) =>
		if any(iskwarg, args)
			handle_error(ctx, e, ctx.error_context, "unexpected semicolon", () -> parse_func_name(ctx, receiver, filter(a -> !iskwarg(a), args), e))
		else
			parse_func_name(ctx, receiver, args, e)
		end
    SN(GuardBy(JuliaSyntax.is_operator) && GuardBy((!) ∘ JuliaSyntax.is_dotted), _) && name => ResolvedName([Expr(name)], e) # so are non-dotted operators
	nothing => AnonFuncName(e)
	_ => handle_error(ctx, e, ctx.error_context, "invalid function name", () -> ResolvedName([gensym()], e))
end

function analyze_call(call, name, args, raw_typevars, rett, ctx; is_macro=false)
	sparams = analyze_typevar.(raw_typevars, (ctx, ))
	# todo: nospecialize
	is_kw = false
	args_stmts = [
		begin
			(result, is_kw) = analyze_argument(expr, is_kw, ctx)
			result
		end for expr in filter((!) ∘ isparam, args)]
	params = filter(isparam, args)
	kwargs_stmts = []
	if length(params) == 1
		kwargs_stmts = @match params[1] begin
			SN(SH(K"parameters", _), [params...]) =>
				if !is_macro
					map(x -> analyze_kwargs(x, ctx), params)
				else
					map(x -> handle_error(ctx, x, ctx.error_context, "macros cannot accept keyword arguments", () -> analyze_kwargs(x, ctx)), params)
				end
		end
	elseif length(params) > 1
		handle_error(ctx, call, ctx.error_context, "more than one semicolon in argument list", nothing)
    end
	if !isnothing(name)
		if is_macro
			@match name begin
				SN(SH(K"Identifier", _), _) => nothing
				_ => handle_error(ctx, call, ctx.error_context, "invalid macro definition", nothing)
			end
		end
		name = check_dotop(ctx, name)
	end
	varargs_indices = findall(arg -> arg.binding isa VarargAssignment, args_stmts)
	if !isempty(varargs_indices) && last(varargs_indices) != length(args_stmts)
		handle_error(ctx, call, ctx.error_context, "invalid \"...\" on non-final argument", nothing)
	end
	get_fnarg_name = @λ begin
		FnArg(IdentifierAssignment(name, _) || TypedAssignment(IdentifierAssignment(name, _), _, _,), _, _, _) => [name]
		expr => begin [] end
	end
	argnames = vcat(collect(Iterators.flatten(map(get_fnarg_name, args_stmts))), map(x -> x.name, kwargs_stmts))
	staticnames = map(x -> x.name, sparams)
	if !isempty(argnames) && hasduplicates(argnames)
		handle_error(ctx, call, ctx.error_context, "function argument name not unique", nothing)
	elseif !isempty(staticnames) && hasduplicates(staticnames)
		handle_error(ctx, call, ctx.error_context, "function static parameter names not unique", nothing)
	elseif !isempty(argnames) && !isempty(staticnames) && (argnames ⊆ staticnames || staticnames ⊆ argnames)
		handle_error(ctx, call, ctx.error_context, "function argument and static parameter names must be distinct", nothing)
	end
	return resolve_function_name(name, ctx), args_stmts, kwargs_stmts, sparams, (isnothing(rett) ? nothing : expand_forms(rett, ctx))
end

function destructure_function_head(name)
	(name, raw_typevars) = @match name begin
		SN(SH(K"::", _), [nexpr, SN(SH(K"where", _), _) && clause]) => begin
			return (nexpr, flatten_where_expr(clause)...)
		end
		SN(SH(K"where", _), _) => flatten_where_expr(name)
		_ => (name, [])
	end # this control flow is very cursed sorry
	rett, name = @match name begin
	    SN(SH(K"::", _), [true_name, typ]) => (typ, true_name)
	    _ => (nothing, name) # todo return a valid thingie
	end
	return name, rett, raw_typevars
end

function expand_function_name(name, ctx; is_macro = false)
	orig_expr = name
	name, rett, raw_typevars = destructure_function_head(name)
	return @match name begin
		SN(SH(K"call", _), [name, args...]) =>  analyze_call(orig_expr, name, args, raw_typevars, rett, ctx; is_macro = is_macro)
		SN(SH(K"tuple", _), [args...]) =>  analyze_call(orig_expr, nothing, args, raw_typevars, rett, ctx; is_macro=is_macro)
		SN(SH(K"Identifier", _), _) =>  (ResolvedName([Expr(name)], name), [], KwArg[], TyVar[], nothing)
		_ => (handle_error(ctx, orig_expr, ctx.error_context, "invalid assignment location name $name", () -> ResolvedName([gensym()], orig_expr)), [], KwArg[], TyVar[], nothing)
	end
end
function expand_anon_function(spec, ctx)
	orig_expr = spec
	spec, rett, raw_typevars = destructure_function_head(spec)
	return @match spec begin
		SN(SH(K"tuple", _), [args...]) =>  analyze_call(orig_expr, nothing, args, raw_typevars, rett, ctx)
		SN(SH(K"Identifier", _), _) && arg =>  analyze_call(orig_expr, nothing, [arg], raw_typevars, rett, ctx)
		_ => (handle_error(ctx, orig_expr, ctx.error_context, "invalid assignment location name $name", () -> ResolvedName([gensym()], orig_expr)), [], KwArg[], TyVar[], nothing)
	end
end
function analyze_let_eq(expr)
	return @match expr begin
		FunctionAssignment(ResolvedName([_], _), _, _, _, _, _) && fun => fun
		FunctionAssignment(name, a, b, c, d, e) && fun => handle_error(ctx, name.location.basenode, ctx.error_context, "invalid let syntax", () -> FunctionAssignment(ResolvedName(gensym, name.location.basenode), a, b, c, d, e))
		TupleAssignment(_, _) && tup => tup
		IdentifierAssignment(_, _) && id => id
		TypedAssignment(_, _, _) && ty => ty
		_ => handle_error(ctx, expr.location.basenode, ctx.error_context, "invalid let syntax", () -> IdentifierAssignment(gensym(), expr.location.basenode))
	end
end
analyze_let_binding(expr, ctx) = @match expr begin
	SN(SH(K"Identifier", _), _) && ident => Expr(ident)
	SN(SH(K"=", _), [a, b]) => (analyze_let_eq(analyze_lvalue(a, ctx))) => expand_forms(b, ctx)
	_ => begin handle_error(ctx, expr, ctx.error_context, "invalid let syntax", nothing); nothing end
end
function expand_macro_name(name, ctx)
	name, args_stmts, kwargs_stmts, sparams, rett = expand_function_name(name, ctx; is_macro = true)
	return name, args_stmts, sparams, rett
end

eventually_decl(expr) = @match expr begin
	SN(SH(K"Identifier", _), _) => true
	SN(SH(K"::" || K"const" || K"=", _), [name, _...]) => eventually_decl(name)
	_ => false
end

analyze_type_sig = @λ begin
	SN(SH(K"Identifier", _), _) && name => (name, [], nothing)
	SN(SH(K"curly", _), [SN(SH(K"Identifier", _), _) && name, params...]) => (name, params, nothing)
	SN(SH(K"<:", _), [SN(SH(K"Identifier", _), _) && name, super]) => (name, [], super)
	SN(SH(K"<:", _), [SN(SH(K"curly", _), [SN(SH(K"Identifier", _), _) && name, params...]), super]) => (name, params, super)
	_ && invalid => nothing
end

node_to_bool = @λ begin
	SN(SH(K"true",_), _) => true
	SN(SH(K"false",_), _) => false
	expr => throw(ASTException(expr, "boolean used in non-boolean context")) # left due to being a fatal internal error
end

unpack_attrs(expr, attrs, mutable, ctx) = @match (expr, mutable) begin
	(SN(SH(K"=", _), [lhs && GuardBy(eventually_decl), value]), _) => handle_error(ctx, expr, ctx.error_context, "operator = inside type definition is reserved", () -> StructField(gensym(), nothing, [], expr))
	(SN(SH(K"::", _), [SN(SH(K"Identifier", _), _) && name, typ]), _) => StructField(Expr(name), expand_forms(typ, ctx), attrs, expr)
	(SN(SH(K"Identifier", _), _) && name, _) => StructField(Expr(name), nothing, attrs, expr)
	(SN(SH(K"const", _), [ex]), true) => unpack_attrs(ex, attrs | FIELD_CONST, mutable, ctx)
	(SN(SH(K"const", _), [ex]), false) => handle_error(ctx, expr, ctx.error_context, "invalid field attribute const for immutable struct", nothing)
	_ => throw("invalid field attribute")
end
quoted = @λ begin
	SN(SH(K"quote", _), _) => true
	_ => false
end
effect_free = @λ begin
	SN(SH(K"true" || K"false", _), _) => true
	SN(SH(K".", _), [SH(SN(K"Identifier", _), _), _]) => true # sym-dot?
	GuardBy(quoted) => true
	_ => false
end
is_string = @λ begin
	SN(SH(K"string" || K"String", _), _) => true
	_ => false
end

unzip(a) = map(x->getfield.(a, x), fieldnames(eltype(a)))
decompose_decl(e) = @match e begin
	SN(SH(K"::", _), [name, typ]) => (name, typ)
	ex => (ex, nothing)
end
flatten_blocks(e) = @match e begin
	SN(SH(K"block", _), [contents...]) => vcat((flatten_blocks.(contents))...)
	expr => [expr]
end

function expand_struct_def(expr, mut, sig, fields, ctx)
	analyzed = analyze_type_sig(sig)
	if isnothing(analyzed)
		handle_error(ctx, expr, ctx.error_context, "invalid type signature", nothing)
		return StructDefStmt(gensym(), [], nothing, [], [], expr)
	else
		name, params, super = analyzed
	end
	bounds = analyze_typevar.(params, (ctx, ))
	params = getfield.(bounds, :name)
	fields = flatten_blocks(fields)
	fieldspecs = map(fld -> unpack_attrs(fld, FIELD_NONE, mut, ctx), filter(eventually_decl, fields))
	defs = filter((!) ∘ eventually_decl, fields)
	defs = filter(d -> !(effect_free(d) || is_string(d)), defs)
	cstrs = expand_forms.(defs, (ctx, )) # need to eventually do some transformations here?
	return StructDefStmt(Expr(name), params, isnothing(super) ? nothing : expand_forms(super, ctx), fieldspecs, cstrs, expr)
end

function expand_abstract_def(expr, sig, ctx)
	analyzed = analyze_type_sig(sig)
	if isnothing(analyzed)
		handle_error(ctx, expr, ctx.error_context, "invalid type signature", nothing)
		return AbstractDefStmt(gensym(), [], nothing, expr)
	else
		name, params, super = analyzed
	end
	bounds = analyze_typevar.(params, (ctx, ))
	params = getfield.(bounds, :name)
	return AbstractDefStmt(Expr(name), params, isnothing(super) ? nothing : expand_forms(super, ctx), expr)
end

function expand_primitive_def(expr, sig, size, ctx)
	analyzed = analyze_type_sig(sig)
	if isnothing(analyzed)
		handle_error(ctx, expr, ctx.error_context, "invalid type signature", nothing)
		return PrimitiveDefStmt(gensym(), [], nothing, Literal(0, expr), expr)
	else
		name, params, super = analyzed
	end
	bounds = analyze_typevar.(params)
	params = getfield.(bounds, :name)
	return PrimitiveDefStmt(Expr(name), params, isnothing(super) ? nothing : expand_forms(super, ctx), expand_forms(size, ctx), expr)
end

extract_implicit_whereparam(expr, ctx) = @match expr begin
	SN(SH(K"<:", _), [bound]) => TyVar(nothing, expand_forms(bound, ctx), nothing, expr)
	SN(SH(K">:", _), [bound]) => TyVar(nothing, nothing, expand_forms(bound, ctx), expr)
	_ => nothing
end
isatom(ast) = @match ast begin
    SH(K"Float" || K"Integer" || K"String" || K"Char" || K"true" || K"false", _) => true
    _ => false
end
ifnotfalse(ast, then) = @match ast begin
	SN(SH(K"false",_ ), _) => nothing
	_ => then(ast)
end

analyze_kw_param(expr, ctx) = @match expr begin
	SN(SH(K"parameters", _), [params...]) => handle_error(ctx, expr, ctx.error_context, "more than one semicolon in argument list", () -> KeywordArg(gensym(), nothing, expr))
	SN(SH(K"=", _), [name && SN(SH(K"Identifier", _), _), value]) => KeywordArg(Expr(name), expand_forms(value, ctx), expr)
	SN(SH(K"Identifier", _), _) && name => KeywordArg(Expr(name), expand_forms(name, ctx), expr)
	SN(SH(K".", _), [_, SN(SH(K"quote", _), [field && SN(SH(K"Identifier", _), _)])]) => KeywordArg(Expr(field), expand_forms(expr, ctx), expr)
    SN(SH(K"...", _), [splat]) => SplatArg(expand_forms(splat, ctx), expr)
	_ => throw("inexhaustive $expr")
end
analyze_kw_call(params, ctx) = map(x -> analyze_kw_param(x, ctx), params)
function split_arguments(args, ctx; down=expand_forms)
	pos_args = []; kw_args = []
    has_parameters = false
	for arg in args
		@match arg begin
			SN(SH(K"parameters", _), [params...]) =>
                if !has_parameters
                    append!(kw_args, analyze_kw_call(params, ctx))
                    has_parameters = true
                else
					handle_error(ctx, arg, ctx.error_context, "more than one semicolon in argument list", nothing)
                end
			SN(SH(K"=", _), [SN(SH(K"Identifier", _), _) && name, value]) => push!(kw_args, KeywordArg(Expr(name), down(value, ctx), arg))
			SN(SH(K"...", _), [arg]) => push!(pos_args, SplatArg(down(arg, ctx), arg))
			expr => push!(pos_args, PositionalArg(down(expr, ctx), arg))
		end
	end
	return pos_args, kw_args
end
function split_op_arguments(args, ctx; down=expand_forms)
	pos_args = []; kw_args = []
	for arg in args
		push!(pos_args, PositionalArg(down(arg, ctx), arg))
	end
	return pos_args, kw_args
end

expand_broadcast(e) = dot_to_fuse(e)

convert_decltype = @λ begin
	K"const" => DECL_CONST
	K"local" => DECL_LOCAL
	K"global" => DECL_GLOBAL
end
expand_declaration(decltype, expr, ctx) = @match expr begin
	SN(SH(K"Identifier", _), _) =>
		if decltype != DECL_CONST
			VarDecl(IdentifierAssignment(Expr(expr), expr), nothing, decltype, expr)
		else
			handle_error(ctx, expr, ctx.error_context, "expected assignment after \"const\"", () -> VarDecl(IdentifierAssignment(Expr(expr), expr), nothing, DECL_NONE, expr))
		end
	SN(SH(K"::", _), _) => VarDecl(analyze_lvalue(expr, ctx), nothing, decltype, expr)
	SN(SH(GuardBy(JuliaSyntax.is_prec_assignment), _), [lhs, rhs]) => VarDecl(analyze_lvalue(lhs, ctx), expand_forms(rhs, ctx), decltype, expr)
end
expand_named_tuple_arg(expr, ctx) = @match expr begin
	SN(SH(K"=", _), [SN(SH(K"Identifier", _), _) && name, rhs]) => NamedValue(Expr(name), expand_forms(rhs, ctx), expr)
	SN(SH(K"=", _), [lhs, rhs]) => handle_error(ctx, expr, ctx.error_context, "invalid name", () -> NamedValue(gensym(), expand_forms(rhs, ctx), expr))
	SN(SH(K"Identifier", _), _) && name => NamedValue(Expr(name), expand_forms(name, ctx), expr)
	SN(SH(K".", _), [rec, SN(SH(K"quote", _), [field && SN(SH(K"Identifier", _), _)])]) && ast => NamedValue(Expr(field), expand_forms(ast, ctx), expr)
	SN(SH(K"call", GuardBy(JuliaSyntax.is_infix_op_call)), [lhs, SN(SH(K"=>", _), _), rhs]) => ComputedNamedValue(expand_forms(lhs, ctx), expand_forms(rhs, ctx), expr)
    SN(SH(K"...", _), [splat]) => SplattedNamedValue(expand_forms(splat, ctx), expr)
	expr => begin handle_error(ctx, expr, ctx.error_context, "invalid named tuple argument", nothing); nothing end
end
function expand_named_tuple(args, ctx)
	tupleargs = []
	for arg in args
		expanded = expand_named_tuple_arg(arg, ctx)
		if !isnothing(expanded)
			push!(tupleargs, expanded)
		end
	end
	return tupleargs
end

string_interpoland(expr, ctx) = @match expr begin
	SN(SH(K"String", _), _) && str => Expr(str)
	other => expand_forms(other, ctx)
end

expand_if_clause(expr, clauses, ctx) = @match clauses begin
	[cond, then, SN(SH(K"elseif", _), elsif)] => pushfirst!(expand_if_clause(expr, elsif, ctx), IfClause(expand_forms(cond, ctx), expand_forms(then, ctx), expr))
	[cond, then, els] => [IfClause(expand_forms(cond, ctx), expand_forms(then, ctx), expr), IfClause(nothing, expand_forms(els, ctx), expr)]
	[cond, then] => [IfClause(expand_forms(cond, ctx), expand_forms(then, ctx), expr)]
end
expand_if(expr, params, ctx) = IfStmt(expand_if_clause(expr, params, ctx), expr)

analyze_iterspec(expr, ctx) = @match expr begin
	SN(SH(K"=", _), [var, iter]) => analyze_lvalue(var, ctx; is_for=true) => expand_forms(iter, ctx)
end

is_update(kw) = kw ∈ KSet"+= -= *= /= //= \= ^= ÷= |= &= ⊻= <<= >>= >>>="

expand_hcat_arg(expr, ctx) = @match expr begin
	GuardBy(isassignment) => begin handle_error(ctx, expr, ctx.error_context, "misplaced assignment statement", nothing); nothing end
	GuardBy(isparam) => begin handle_error(ctx, expr, ctx.error_context, "unexpected semicolon in array expression", nothing); nothing end
	SN(SH(K"...", _), [body]) => Splat(expand_forms(body, ctx), expr)
	e => expand_forms(e, ctx)
end

expand_row(el, toplevel, ctx) = @match el begin
	GuardBy(isassignment) => begin handle_error(ctx, el, ctx.error_context, "misplaced assignment statement", nothing); nothing end
	GuardBy(isparam) => begin handle_error(ctx, el, ctx.error_context, "unexpected semicolon in array expression", nothing); nothing end
	SN(SH(K"row", _), elems) => toplevel ?
		Row(filter((!) ∘ isnothing, expand_row.(elems, false, (ctx, ))), el) :
	    begin handle_error(ctx, el, ctx.error_context, "nested rows not supported", nothing); nothing end
	SN(SH(K"...", _), [body]) => Splat(expand_forms(body, ctx), el)
	e => expand_forms(e, ctx)
end

expand_nrow(expr, ctx) = @match expr begin
	GuardBy(isassignment) => begin handle_error(ctx, expr, ctx.error_context, "misplaced assignment statement", nothing); nothing end
	GuardBy(isparam) => begin handle_error(ctx, expr, ctx.error_context, "unexpected semicolon in array expression", nothing); nothing end
	SN(SH(K"nrow", flgs), elems) => NRow(JuliaSyntax.numeric_flags(flgs), filter((!) ∘ isnothing, expand_nrow.(elems, (ctx, ))), expr)
	SN(SH(K"...", _), body) => begin handle_error(ctx, expr, ctx.error_context, "Splatting ... in an hvncat with multiple dimensions is not supported", nothing); nothing end
	e => expand_forms(e, ctx)
end

expand_iterator(expr, ctx)::Iterspec = @match expr begin
	SN(SH(K"cartesian_iterator", _), iters) => Cartesian(expand_iterator.(iters, (ctx, )), expr)
	SN(SH(K"=", _), [lhs, rhs]) => IterEq(analyze_lvalue(lhs, ctx), expand_forms(rhs, ctx), expr)
	SN(SH(K"filter", _), [iters..., cond]) => Filter(expand_iterator.(iters, (ctx,)), expand_forms(cond, ctx), expr)
end
expand_generator(expr, ctx)::Expression = @match expr begin
	SN(SH(K"generator", _), [expr, iters...]) => Generator(expand_forms(expr, ctx), Iterspec[expand_iterator(iter, ctx) for iter in iters], expr)
end

expand_import_source(ctx, expr) = @match expr begin
	SN(SH(K"importpath", _), path) => expand_import_path(ctx,path)
end
expand_import_clause(ctx, expr; allow_relative=true) = @match expr begin
	SN(SH(K"importpath", _), path) => Dep(expand_import_path(ctx, path; allow_relative=allow_relative), expr)
	SN(SH(K"as", _), [SN(SH(K"importpath", _), path), SN(SH(K"Identifier", _), _) && alias]) => AliasDep(expand_import_path(ctx, path; allow_relative=allow_relative), Expr(alias), expr)
end

function expand_import_path(ctx, src_path; allow_relative=true)
	path = nothing
	for path_el in src_path
		path = @match (path_el, path) begin
			(SN(SH(K"Identifier" || K"MacroName", _), _) && id, nothing) => ImportId(Expr(id), path_el)
			(SN(SH(K"Identifier" || K"MacroName", _), _) && id, path) => ImportField(path, Expr(id), path_el)
			(SN(SH(K".", _), _), nothing) => allow_relative ? ImportRelative(1, path_el) : handle_error(ctx, path_el, ctx.error_context, "invalid path: \".\" in identifier path", () -> ImportRelative(1, path_el))
			(SN(SH(K".", _), _), ImportRelative(lvl, _)) => allow_relative ? ImportRelative(lvl+1, path_el) : handle_error(ctx, path_el, ctx.error_context, "invalid path: \".\" in identifier path", () -> ImportRelative(lvl+1, path_el))
			(SN(SH(K".", _), _), _) => handle_error(ctx, path_el, ctx.error_context, "invalid path: \".\" in identifier path", () -> ImportRelative(1, path_el))
			(_, _) => handle_error(ctx, path_el, ctx.error_context, "invalid path", () -> ImportRelative(1, path_el))
		end
	end
	return path
end

expand_tuple_arg(expr, ctx) = @match expr begin
    SN(SH(K"...", _), [ex]) => Splat(expand_forms(ex, ctx), expr)
    _ => expand_forms(expr, ctx)
end

@data Docstrings begin
    Docstring(doc::Expression, defn::Union{Expression, ToplevelStmts})
    CallDocstring(doc::Expression, name::FunctionName, arguments::Vector{FnArg}, kw_args::Vector{KwArg}, sparams::Vector{TyVar}, rett::Union{Expression, Nothing})
end

expand_docstring(expand, args, ast, ctx) = @match args begin
    [docs, SN(SH(K"::", _), [SN(SH(K"call" || K"where", _), _) && fn, typ])] => let (name, args, kwargs, sparams, rett) = expand_function_name(fn,ctx); CallDocstring(expand_forms(docs, ctx), name, args, kwargs, sparams, expand_forms(typ, ctx)) end
    [docs, SN(SH(K"call" || K"where", _), _) && fn] => CallDocstring(expand_forms(docs, ctx), expand_function_name(fn, ctx)...)
    [docs, inner_ast] => Docstring(expand_forms(docs, ctx), expand(inner_ast, ctx))
end


resolve_toplevel_macro(ast, ::DefaultMacroContext, ::Val{Symbol("@doc")}, args, ctx) = MacroExpansionStmt(expand_docstring(expand_toplevel, args, ast, ctx), ast)
resolve_toplevel_macro(ast, ::DefaultMacroContext, ::Union{Val{Symbol("@inline")}, Val{Symbol("@noinline")}}, args, ctx) = expand_toplevel(args[1], ctx)
resolve_toplevel_macro(ast, ::DefaultMacroContext, ::Union{Val{Symbol("@assume_effects")}, Val{Symbol("@constprop")}}, args, ctx) = expand_toplevel(args[2], ctx)
resolve_toplevel_macro(ast, ::DefaultMacroContext, ::Val{mc}, args, ctx) where mc = handle_error(ctx, ast, ctx.error_context, "Unrecognized macro $mc $(typeof(mc))", () -> MacroExpansionStmt(Literal(:unknown, ast), ast))

resolve_macro(ast, ::DefaultMacroContext, ::Val{Symbol("@doc")}, args, ctx) = MacroExpansion(expand_docstring(expand_forms, args, ast, ctx), ast)
resolve_macro(ast, ::DefaultMacroContext, ::Union{Val{Symbol("@inline")}, Val{Symbol("@noinline")}, Val{Symbol("@inbounds")}}, args, ctx) = expand_forms(args[1], ctx)
resolve_macro(ast, ::DefaultMacroContext, ::Val{Symbol("@eval")}, args, ctx) = Literal(:(), ast)
resolve_macro(ast, ::DefaultMacroContext, ::Val{Symbol("@horner")}, args, ctx) = FunCall(Variable(:evalpoly, ast), PositionalArg.([expand_forms(args[1], ctx), TupleExpr(expand_forms.(args[2:end], (ctx, )), ast)], (ast, )), Vector{Union{KeywordArg, SplatArg}}[], ast)
resolve_macro(ast, ::DefaultMacroContext, ::Val{Symbol("@generated")}, args, ctx) = Literal(true, ast)
resolve_macro(ast, ::DefaultMacroContext, ::Val{Symbol("@assume_effects")}, args, ctx) = expand_forms(args[2], ctx)
resolve_macro(ast, ::DefaultMacroContext, ::Val{mc}, args, ctx) where mc = handle_error(ctx, ast, ctx.error_context, "Unrecognized macro $mc", () -> MacroExpansion(Literal(:unknown, ast), ast))

next_ctx(head, ctx) = ExpandCtx(ctx)

"""
	expand_toplevel(ast::JuliaSyntax.SyntaxNode)::ToplevelStmts
	expand_toplevel(ast::JuliaSyntax.SyntaxNode, ctx::ExpandCtx)::ToplevelStmts

Takes a SyntaxNode representing an entire file and lowers it to a [ToplevelStmts](@ref).

Toplevel vs. expression can be thought of generally as "where would it make sense for a
`module` or `using` statement to exist?". As an example, the contents of a file are usually
at the top level as is the arugment to an `eval` call. In constrast, a method body will not be
at the top level as neither module nor using statements are valid inside of it.

For most use cases this is the reccomended entry point. Use `expand_forms` if you need to expand
a specific expression.
"""
expand_toplevel(ast::JuliaSyntax.SyntaxNode) = expand_toplevel(ast, ExpandCtx(true, false))
expand_toplevel(ast::JuliaSyntax.SyntaxNode, ctx::ExpandCtx) = @match ast begin
    SN(SH(K"using", _), [SN(SH(K":", _), [mod, terms...])]) => SourceUsingStmt(expand_import_source(ctx, mod), expand_import_clause.((ctx,), terms; allow_relative=false), ast)
    SN(SH(K"using", _), [terms...]) => UsingStmt(expand_import_source.((ctx,), terms), ast)
    SN(SH(K"import", _), [SN(SH(K":", _), [mod, terms...])]) => SourceImportStmt(expand_import_source(ctx, mod), expand_import_clause.((ctx,), terms; allow_relative=false), ast)
    SN(SH(K"import", _), [terms...]) => ImportStmt(expand_import_clause.((ctx,), terms), ast)
    SN(SH(K"export", _), syms) => ExportStmt(Expr.(syms), ast)
    SN(SH(K"module", flags), [name, SN(SH(K"block", _), stmts)]) => ModuleStmt(!JuliaSyntax.has_flags(flags, JuliaSyntax.BARE_MODULE_FLAG), Expr(name), expand_toplevel.(stmts, (ctx, )), ast)
    SN(SH(K"abstract", _), [sig]) => expand_abstract_def(ast, sig, ctx)
    SN(SH(K"struct", flags), [sig, fields]) => expand_struct_def(ast, JuliaSyntax.has_flags(flags, JuliaSyntax.MUTABLE_FLAG), sig, fields, ctx)
    SN(SH(K"primitive", _), [sig, size]) => expand_primitive_def(ast, sig, size, ctx)
    SN(SH(K"toplevel", _), exprs) => ToplevelStmt(expand_toplevel.(exprs, (ctx, )), ast)
    SN(SH(K"doc", _), [args...]) => resolve_toplevel_macro(ast, ctx.macro_context, Val{Symbol("@doc")}(), args, ctx)
    SN(SH(K"macrocall", _), [name, args...]) => resolve_toplevel_macro(ast, ctx.macro_context, Val{Symbol(name)}(), args, ctx)
	expr => ExprStmt(expand_forms(expr, JuliaSyntax.head(expr), JuliaSyntax.children(expr), ExpandCtx(ctx; is_toplevel = true)), ast)
end
expand_curly_internal(receiver, ctx, args, ast) =
	CallCurly(expand_forms(receiver, ctx), [let param = extract_implicit_whereparam(arg, ctx); isnothing(param) ? expand_forms(arg, ctx) : param end for arg in args], ast)
expand_curly(receiver, ctx, args, ast) =
	any(iskwarg, args) ?
		handle_error(ctx, ast, ctx.error_context, "misplaced assignment statement", () -> expand_curly_internal(receiver, ctx, filter((!) ∘ isnothing, args), ast)) :
		expand_curly_internal(receiver, ctx, args, ast)

expand_vect(ctx, ast, elems) = any(isassignment, elems) ?
	handle_error(ctx, ast, ctx.error_context, "misplaced assignment statement", () -> Vect(filter((!) ∘ isnothing, expand_hcat_arg.(filter((!) ∘ isnothing, elems), (ctx, ))), ast)) :
	Vect(filter((!) ∘ isnothing, expand_hcat_arg.(elems, (ctx, ))), ast)

function expand_try_catch(ctx, block, clauses, ast)
	expanded_block = expand_forms(block, ctx)

	catch_var = nothing
	catch_body = nothing
	else_body = nothing
	finally_body = nothing
	for clause in clauses
		@match clause begin
			SN(SH(K"catch", _), [SN(SH(K"false", _), _), body]) => begin catch_body = expand_forms(body, ctx) end
			SN(SH(K"catch", _), [var, body]) => begin catch_var = Expr(var); catch_body = expand_forms(body, ctx) end
			SN(SH(K"else", _), [body]) => begin else_body = expand_forms(body, ctx) end
			SN(SH(K"finally", _), [body]) => begin finally_body = expand_forms(body, ctx) end
		end
	end
	TryCatch(expanded_block, catch_var, catch_body, else_body, finally_body, ast)
end

"""
	expand_forms(ast::JuliaSyntax.SyntaxNode, ctx::ExpandCtx)

Expands an expression (such as a method body) from a SyntaxNode to an Expression with respect to a [ExpandCtx](@ref). See [expand_toplevel](@ref) for
more discussion.
"""
expand_forms(ast::JuliaSyntax.SyntaxNode, ctx::ExpandCtx) = expand_forms(ast, JuliaSyntax.head(ast), JuliaSyntax.children(ast), next_ctx(JuliaSyntax.head(ast), ctx))
expand_forms(ast, head, children, ctx) = @match (head, children) begin
	(SH(K"Float" || K"Integer" || K"String" || K"Char" || K"char" || K"true" || K"false" || K"HexInt", _), _) => Literal(Expr(ast), ast)
    (SH(K"quote",_), _) => Quote(ast, ast) # need to port bits of macroexpansion into this
    (SH(K"function", _), [name, body]) => FunctionDef(expand_function_name(name, ctx)..., expand_forms(body, ctx), ast)
    (SH(K"function", _), [name]) => FunctionDef(expand_function_name(name, ctx)..., nothing, ast)
    (SH(K"->", _), [name, body]) => FunctionDef(expand_anon_function(name, ctx)..., expand_forms(body, ctx), ast)
    (SH(K"let", _), [SN(SH(K"block", _), bindings), body]) => LetBinding(filter((!) ∘ isnothing, analyze_let_binding.(bindings, (ctx, ))), expand_forms(body, ctx), ast)
    (SH(K"let", _), [binding, body]) => LetBinding(filter((!) ∘ isnothing,[analyze_let_binding(binding, ctx)]), expand_forms(body, ctx), ast)
    (SH(K"macro", _), [SN(SH(K"call", _), _) && name, body]) => @match expand_macro_name(name, ctx) begin
		(ResolvedName(nm, _) && name, args_stmts, sparams, rett) => MacroDef(name, args_stmts, sparams, rett, expand_forms(body, ctx), ast)
		(nm, args_stmts, sparams, rett) => handle_error(ctx, nm.location.basenode, ctx.error_context, "Invalid macro name", () -> MacroDef(ResolvedName([gensym()], ast), args_stmts, sparams, rett, expand_forms(body, ctx), ast))
	end
    (SH(K"macro", _), [SN(SH(K"Identifier", _), _) && name]) => MacroDef(expand_macro_name(name, ctx)..., nothing, ast)
    (SH(K"macro", _), _) => handle_error(ctx, ast, ctx.error_context, "invalid macro definition", () -> MacroDef(ResolvedName([gensym()], ast), nothing, ast))
    (SH(K"try", _), [block, clauses...]) => expand_try_catch(ctx, block, clauses, ast)
    (SH(K"block", _), stmts) => Block(expand_forms.(stmts, (ctx, )), ast)
    (SH(K".", _), [op]) => Broadcast(expand_forms(op, ctx), ast)
	(SH(K".", _), [f, SN(SH(K"quote", _), [x && SN(SH(K"Identifier", _), _)])]) => GetProperty(expand_forms(f, ctx), Expr(x), ast)
	(SH(K".", _), [f, SN(SH(K"quote", _), [x]) && lit]) => GetProperty(expand_forms(f, ctx), Literal(Expr(x), lit), ast)
	(SH(K".", _), [f, SN(SH(K"tuple", _), args)]) => FunCall(Broadcast(expand_forms(f, ctx), ast), split_arguments(args, ctx)..., ast)
	(SH(K"comparison", _), [initial, args...]) => Comparison(expand_forms(initial, ctx), map((op, value) -> expand_forms(op, ctx) => expand_forms(value, ctx), args[1:2:end], args[2:2:end]), ast)
	(SH(K"&&", _ && GuardBy(JuliaSyntax.is_dotted)), [l, r]) => FunCall(Broadcast(Variable(:(&&), ast), ast), split_op_arguments([l, r], ctx)..., ast)
	(SH(K"||", _ && GuardBy(JuliaSyntax.is_dotted)), [l, r]) => FunCall(Broadcast(Variable(:(||), ast), ast), split_op_arguments([l, r], ctx)..., ast)
    (SH(K"=", _ && GuardBy(JuliaSyntax.is_dotted)), [lhs, rhs]) => BroadcastAssignment(expand_forms(lhs, ctx), expand_forms(rhs, ctx), ast)
    (SH(K"<:", _), [a,b]) => FunCall(Variable(:(<:), ast), split_arguments([a, b], ctx)..., ast)
    (SH(K">:", _), [a,b]) => FunCall(Variable(:(>:), ast), split_arguments([a, b], ctx)..., ast)
    (SH(K"-->", _), _) => FunCall(Variable(:(-->)), split_arguments([a, b], ctx)..., ast)
    (SH(K"where", _), [typ, SN(SH(K"braces", _), vars)]) => WhereType(expand_forms(typ, ctx), analyze_typevar.(vars, (ctx, )), ast)
    (SH(K"where", _), [typ, var]) => WhereType(expand_forms(typ, ctx), [analyze_typevar(var, ctx)], ast)
    (SH((K"const" || K"local" || K"global") && decltype, _), decls) => Declaration(expand_declaration.(convert_decltype(decltype), decls, (ctx, )), ast)
    (SH(K"=", _), [lhs, rhs]) => Assignment(analyze_lvalue(lhs, ctx), expand_forms(rhs, ctx), ast)
    (SH(K"ref", _), [arr, idxes..., SN(SH(K"parameters", _), _)]) => handle_error(ctx, ast, ctx.error_context, "unexpected semicolon in array expression", () -> GetIndex(expand_forms(arr, ctx), map(el->PositionalArg(expand_forms(el, ctx), el), idxes), ast))
    (SH(K"ref", _), [arr, idxes...]) => GetIndex(expand_forms(arr, ctx), map(el->PositionalArg(expand_forms(el, ctx), el), idxes), ast)
    (SH(K"curly", _), [receiver, args..., SN(SH(K"parameters", _), _)]) => handle_error(ctx, ast, ctx.error_context, "unexpected semicolon", () -> expand_curly(receiver, ctx, args, ast))
    (SH(K"curly", _), [receiver, args...]) => expand_curly(receiver, ctx, args, ast)
	(SH(K"call", GuardBy(JuliaSyntax.is_infix_op_call)), [arg1, f, arg2...]) && call => FunCall(expand_forms(f, ctx), split_op_arguments([arg1; arg2], ctx)..., ast) # todo Global method definition needs to be placed at the toplevel
    (SH(K"call", GuardBy(JuliaSyntax.is_postfix_op_call)), [arg, f]) => FunCall(expand_forms(f, ctx), split_op_arguments([arg], ctx)..., ast)
    (SH(K"call", GuardBy(JuliaSyntax.is_prefix_op_call)), [f, arg]) => FunCall(expand_forms(f, ctx), [PositionalArg(expand_forms(arg, ctx), ast)], [], ast)
	(SH(K"call", _), [f, args...]) => FunCall(expand_forms(f, ctx), split_arguments(args, ctx)..., ast)
	(SH(K"dotcall", GuardBy(JuliaSyntax.is_infix_op_call)), [arg1, f, arg2...]) => FunCall(Broadcast(expand_forms(f, ctx), ast), split_op_arguments([arg1; arg2], ctx)..., ast)
	(SH(K"dotcall", GuardBy(JuliaSyntax.is_postfix_op_call)), [arg, f]) => FunCall(Broadcast(expand_forms(f, ctx), ast), split_op_arguments([arg], ctx)..., ast)
	(SH(K"dotcall", GuardBy(JuliaSyntax.is_prefix_op_call)), [f, arg]) => FunCall(Broadcast(expand_forms(f, ctx), ast), [PositionalArg(expand_forms(arg, ctx), ast)], ast)
	(SH(K"dotcall", _), [f, args...]) => FunCall(Broadcast(expand_forms(f, ctx), ast), split_arguments(args, ctx)..., ast)
    (SH(K"do", _), [call, args, body]) =>
		let
			(_, args, _, _, _) = expand_anon_function(args, ctx);
			DoStatement(expand_forms(call, ctx), args, expand_forms(body, ctx), ast)
		end
	(SH(K"tuple", _), [arg1, args..., SN(SH(K"parameters", _), _)]) => handle_error(ctx, ast, ctx.error_context, "unexpected semicolon in tuple", () -> TupleExpr(expand_tuple_arg.([arg1; args], (ctx, )), ast))
	(SH(K"tuple", _), [SN(SH(K"parameters", _), params)]) => NamedTupleExpr(expand_named_tuple(params, ctx), ast)
	(SH(K"tuple", _), args) => any(isassignment, args) ? NamedTupleExpr(expand_named_tuple(args, ctx), ast) : TupleExpr(expand_tuple_arg.(args, (ctx, )), ast)
    (SH(K"braces", _), _) => handle_error(ctx, ast, ctx.error_context, "{ } vector syntax is discontinued", () -> Literal(nothing, ast))
    (SH(K"bracescat", _), _) => handle_error(ctx, ast, ctx.error_context, "{ } matrix syntax is discontinued", () -> Literal(nothing, ast))
    (SH(K"string", _), args) => StringInterpolate(string_interpoland.(args, (ctx, )), ast)
    (SH(K"::", _), [exp]) => handle_error(ctx, ast, ctx.error_context, "invalid \"::\" syntax", () -> expand_forms(exp, ctx))
    (SH(K"::", _), [val, typ]) => TypeAssert(expand_forms(val, ctx), expand_forms(typ, ctx), ast)
    (SH(K"if", _), params) => expand_if(ast, params, ctx)
    (SH(K"while", _), [cond, body]) => let ictx = ExpandCtx(ctx; is_loop=true); WhileStmt(expand_forms(cond, ictx), expand_forms(body, ictx), ast) end
    (SH(K"break", _), _) => if ctx.is_loop BreakStmt(ast) else handle_error(ctx, ast, ctx.error_context, "break or continue outside loop", () -> Literal(nothing, ast)) end
    (SH(K"continue", _), _) => if ctx.is_loop ContinueStmt(ast) else handle_error(ctx, ast, ctx.error_context, "break or continue outside loop", () -> Literal(nothing, ast)) end
    (SH(K"return", _), []) => ReturnStmt(nothing, ast)
    (SH(K"return", _), [val]) => ReturnStmt(expand_forms(val, ctx), ast)
    (SH(K"for", _), [SN(SH(K"=", _), _) && iterspec, body]) => let ictx = ExpandCtx(ctx; is_loop=true); ForStmt(Pair{LValue, Expression}[analyze_iterspec(iterspec, ictx)], expand_forms(body, ictx), ast) end
    (SH(K"for", _), [SN(SH(K"cartesian_iterator", _), iterspecs), body]) => let ictx = ExpandCtx(ctx; is_loop=true); ForStmt(Pair{LValue, Expression}[analyze_iterspec(iterspec, ictx) for iterspec in iterspecs], expand_forms(body, ictx), ast) end
    (SH(K"&&", _), [l, r]) => FunCall(Variable(:(&&), ast), split_op_arguments([l, r], ctx)..., ast)
    (SH(K"||", _), [l, r]) => FunCall(Variable(:(||), ast), split_op_arguments([l, r], ctx)..., ast)
    (SH(upd && GuardBy(is_update), _ && GuardBy(JuliaSyntax.is_dotted)), [lhs, rhs]) => BroadcastUpdate(Symbol(upd), expand_forms(lhs,ctx), expand_forms(rhs, ctx), ast)
    (SH(upd && GuardBy(is_update), _), [lhs, rhs]) => Update(Symbol(upd), analyze_lvalue(lhs, ctx), expand_forms(rhs, ctx), ast)
    (SH(K"$", _), _) => handle_error(ctx, ast, ctx.error_context, "\"\$\" expression outside quote", () -> Literal(nothing, ast))
    (SH(K"...", _), _) => handle_error(ctx, ast, ctx.error_context, "\"...\" expression outside call", () -> Literal(nothing, ast))
    (SH(K"vect", _), [elems..., SN(SH(K"parameters", _), _)]) => handle_error(ctx, ast, ctx.error_context, "unexpected semicolon in array expression", () -> expand_vect(ctx, ast, elems))
    (SH(K"vect", _), elems) => expand_vect(ctx, ast, elems)
    (SH(K"hcat", _), elems && GuardBy(x -> any(isassignment, x))) => handle_error(ctx, ast, ctx.error_context, "misplaced assignment statement", () -> HCat(nothing, filter((!) ∘ isnothing, expand_hcat_arg.(filter((!) ∘ isassignment, elems), (ctx, ))), ast))
	(SH(K"hcat", _), elems) => HCat(nothing, filter((!) ∘ isnothing, expand_hcat_arg.(elems, (ctx, ))), ast)
    (SH(K"typed_hcat", _), elems && GuardBy(x -> any(isassignment, x))) => handle_error(ctx, ast, ctx.error_context, "misplaced assignment statement", () -> HCat(expand_forms(type, ctx), filter((!) ∘ isnothing, expand_hcat_arg.(filter((!) ∘ isassignment, elems), (ctx, ))), ast))
	(SH(K"typed_hcat", _), [type, elems...]) => HCat(expand_forms(type, ctx), filter((!) ∘ isnothing, expand_hcat_arg.(elems, (ctx, ))), ast)
    (SH(K"vcat", _), params) => VCat(nothing, filter((!) ∘ isnothing, expand_row.(params, true, (ctx, ))), ast)
    (SH(K"typed_vcat", _), [type, params...]) => VCat(expand_forms(type, ctx), filter((!) ∘ isnothing, expand_row.(params, true, (ctx, ))), ast)
    (SH(K"ncat", flags), elems) => NCat(nothing, JuliaSyntax.numeric_flags(flags), filter((!) ∘ isnothing, expand_nrow.(elems, (ctx, ))), ast)
    (SH(K"typed_ncat", flags), [type, elems...]) => NCat(expand_forms(type, ctx), JuliaSyntax.numeric_flags(flags), filter((!) ∘ isnothing, expand_nrow.(elems, (ctx, ))), ast)
    (SH(K"generator", _), elems && GuardBy(x -> any(contains_return, x))) => handle_error(ctx, ast, ctx.error_context, "\"return\" not allowed inside comprehension or generator", () -> expand_generator(ast, ctx))
    (SH((K"generator" || K"cartesian_iterator") && head, _), [expr, iters...]) => expand_generator(ast, ctx)
    (SH(K"comprehension", _), [generator]) => Comprehension(nothing, expand_generator(generator, ctx), ast)
    (SH(K"typed_comprehension", _), [type, generator]) => Comprehension(expand_forms(type, ctx), expand_generator(generator, ctx), ast)
	(SH(K"Identifier", _), _) => Variable(Expr(ast), ast)
	(SH(K"doc", _), [args...]) => resolve_macro(ast, ctx.macro_context, Val{Symbol(Symbol("@doc"))}(), args, ctx)
	(SH(K"macrocall", _), [mcro, args...]) => resolve_macro(ast, ctx.macro_context, Val{Symbol(mcro)}(), args, ctx)
    (SH(K"?", _), [cond, then, els]) => Ternary(expand_forms(cond, ctx), expand_forms(then, ctx), expand_forms(els, ctx), ast)
	(SH(K"using" || K"import" || K"export" || K"module" || K"abstract" || K"struct" || K"primitive", _), _) => handle_error(ctx, ast, ctx.error_context, "must be at top level", () -> Literal(nothing, ast))
	(SH(op && GuardBy(JuliaSyntax.is_operator), _ && GuardBy(JuliaSyntax.is_dotted)), _) => Broadcast(Variable(Symbol(string(op)), ast), ast)
	(SH(GuardBy(JuliaSyntax.is_operator), _), _) => try Variable(Expr(ast), ast) catch e println(ast); rethrow(e) end
    (head, args) => throw("Unimplemented $head")
end
