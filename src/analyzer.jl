
isdecl(ast) = @match ast begin 
	SN(SH(K"::", _), _) => true
	_ => false
end
isassignment(ast) = @match ast begin 
	SN(SH(K"=", _), _) => true
	_ => false
end
iskwarg(ast) = @match ast begin 
	SN(SH(K"kw", _), _) => true
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
check_dotop(ast) = 
	if isdotop_named(ast) 
		throw(ASTException(ast, "Invalid function name"))
	else 
		@match ast begin 
			SN(SH(K".", _), [rec, name]) => check_dotop(name)
			SN(SH(K"quote" || K"break", _), [body]) => check_dotop(body)
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
		throw("Invalid expression (internal error: flattening non-where)")
	end
	while kindof(ex) == K"where"
		@match ex begin 
			SN(SH(K"where", _), [body, current_vars...]) => begin 
				push!.((vars, ), current_vars)
				ex = body
			end
			_ => ex
		end
	end
	return (ex, vars)
end

function analyze_typevar(ex, ctx)
	check_sym(s) = (kindof(s) == K"Identifier" ? Expr(s) : throw(ASTException(s, "Invalid type variable (non-symbol)")))
	@match ex begin 
		ex && GuardBy(isatom) => TyVar(check_sym(s), nothing, nothing, ex)
		SN(SH(K"Identifier", _), _) => TyVar(check_sym(ex), nothing, nothing, ex)
		SN(SH(K"comparison", _), [a, SN(SH(K"<:", _), _), b, SN(SH(K"<:", _), _), c]) => TyVar(check_sym(b), expand_forms(c, ctx), expand_forms(a, ctx), ex)
		SN(SH(K"<:", _), [a, b]) => TyVar(check_sym(a), expand_forms(b, ctx), nothing, ex)
		SN(SH(K">:", _), [a, b]) => TyVar(check_sym(a), nothing, expand_forms(b, ctx), ex)
		_ => throw(ASTException(ex, "invalid variable expression in \"where\""))
	end
end

analyze_tuple_assignment(expr, ctx) = @match expr begin 
	SN(SH(K"Identifier", _), _) && name => IdentifierAssignment(Expr(name), expr)
	SN(SH(K"::", _), [name, type]) => TypedAssignment(IdentifierAssignment(Expr(name)), expand_forms(type, ctx), expr)
	_ => throw(ASTException(expr, "invalid assignment location"))
end

unquote = @λ begin 
	SN(SH(K"quote", _), [body]) => Expr(body)
end
analyze_lvalue(expr, ctx; is_for=false) = @match expr begin 
	SN(SH(K"Identifier", _), _) && id => 
		if Expr(id) ∈ [:ccall, :global]
			throw(ASTException(expr, "invalid assignment location"))
		else 
			IdentifierAssignment(Expr(id), expr)
		end
	SN(SH(K".", _), [a,b]) => FieldAssignment(expand_forms(a, ctx), unquote(b), expr)
	SN(SH(K"tuple", _), [_, args..., SN(SH(K"parameters", _), _)]) => throw(ASTException(expr, "invalid assignment location"))
	SN(SH(K"tuple", _), [SN(SH(K"parameters", _), params)]) => 
		NamedTupleAssignment(map(x -> analyze_tuple_assignment(x, ctx), params), expr)
	SN(SH(K"tuple", _), [args...]) => begin
			has_varargs = false
			TupleAssignment([@match arg begin 
				SN(SH(K"...", _), body) => begin 
					if has_varargs
						throw(ASTException(expr, "multiple \"...\" on lhs of assignment"))
					end
					has_varargs = true
					VarargAssignment(length(body) > 0 ? analyze_lvalue(body[1], ctx) : nothing, arg)
				end
				arg => analyze_lvalue(arg, ctx)
			end for arg in args], expr)
		end
	SN(SH(K"typed_hcat", _), _) => throw(ASTException(expr, "invalid spacing in left side of indexed assignment"))
	SN(SH(K"typed_vcat" || K"typed_ncat", _), _) => throw(ASTException(expr, "unexpected \";\" in left side of indexed assignment"))
	SN(SH(K"ref", _), [a, idxs...]) => RefAssignment(expand_forms(a, ctx), split_arguments(idxs, ctx)..., expr)
	SN(SH(K"::", _), [typ]) => throw(ASTException(expr, "invalid assignment location"))
	SN(SH(K"::", _), [call && GuardBy(eventually_call), T]) && funspec => FunctionAssignment(expand_function_name(funspec, ctx)..., expr)
	SN(SH(K"::", _), [x, T]) => TypedAssignment(analyze_lvalue(x, ctx), expand_forms(T, ctx), expr)
	SN(SH(K"vcat" || K"ncat", _), _) => throw(ASTException(expr, "use \"(a, b) = ...\" to assign multiple values"))
	SN(SH(K"call" || K"where", _), _) && name => FunctionAssignment(expand_function_name(name, ctx)..., expr)
	SN(SH(K"outer", _), [SN(SH(K"Identifier", _), _) && id]) =>  
		if is_for 
			OuterIdentifierAssignment(Expr(id), expr) 
		else 
			throw(ASTException(expr, "no outer local variable declaration exists for"))
		end
	_ => throw(ASTException(expr, "invalid assignment location"))
end

expr_contains_p(pred, expr, filter = x -> true) =
	filter(expr) && (pred(expr) || @match expr begin 
		SN(SH(K"quote", _), _) => false
		SN(_, args) => any(expr_contains_p.(pred, args, filter))
		e => throw("unhandled $e")
	end)

isparam = @λ begin SN(SH(K"parameters", _), _) => true; _ => false end
contains_destructuring = @λ begin 
	SN(SH(K"::" || K"=" || K"kw", _), _) => true
	_ => false 
end
is_return = @λ begin 
	SN(SH(K"return", _), _) => true
	_ => false 
end
contains_return(e) = expr_contains_p(is_return, e)
check_recursive_assignment(expr) = 
	if expr_contains_p(contains_destructuring, expr)
		throw(ASTException(expr, "invalid argument destructuring syntax $expr"))
	else 
		true
	end
analyze_argument(expr, is_kw, ctx) = @match (expr, is_kw) begin
	(SN(SH(K"tuple", _), _), false) => (FnArg(analyze_lvalue(expr, ctx), nothing, nothing, expr), false)
	(SN(SH(K"::", _), [binding && GuardBy(check_recursive_assignment), typ]), false) => (FnArg(analyze_lvalue(binding, ctx), nothing, expand_forms(typ, ctx), expr), false)
	(SN(SH(K"::", _), [typ]), false) => (FnArg(nothing, nothing, expand_forms(typ, ctx), expr), false)
	(SN(SH(K"kw", _), [head, default]), is_kw) => (let (base, _) = analyze_argument(head, is_kw, ctx); FnArg(base.binding, expand_forms(default, ctx), base.type, expr) end, true)
	(SN(SH(K"...", _), [bound]), false) => (FnArg(VarargAssignment(analyze_lvalue(bound, ctx), expr), nothing, nothing, expr), false)
	(SN(SH(K"...", _), []), false) => (FnArg(VarargAssignment(nothing, expr), nothing, nothing, expr), false)
	(_, false) => (FnArg(analyze_lvalue(expr, ctx), nothing, nothing, expr), false)
	(_, true) => throw(ASTException(expr, "optional positional arguments must occur at end"))
	(_, _) => throw("invalid argument syntax $expr $is_kw")
end
analyze_kwargs(expr, ctx) = @match expr begin 
	SN(SH(K"parameters", _), _) => throw(ASTException(expr, "more than one semicolon in argument list"))
	SN(SH(K"kw", _), [SN(SH(K"::", _), [SN(SH(K"Identifier", _), ) && name, type]), body]) => begin
		KwArg(Expr(name), expand_forms(type, ctx), expand_forms(body, ctx), expr)
	end
	SN(SH(K"kw", _), [SN(SH(K"Identifier", _), _) && name, body]) => KwArg(Expr(name), nothing, expand_forms(body, ctx), expr)
	SN(SH(K"...", _), [SN(SH(K"Identifier", _), _) && name]) => KwArg(Expr(name), nothing, nothing, expr; is_vararg=true)
	SN(SH(K"kw", _), [SN(SH(K"::", _), [name, type]), body]) => throw(ASTException(expr, "is not a valid function argument name"))
	SN(SH(K"kw", _), [name, body]) => throw(ASTException(expr, "is not a valid function argument name"))
	SN(SH(K"...", _), [name]) => throw(ASTException(expr, "is not a valid function argument name"))
	SN(SH(K"Identifier", _), _) && ident => KwArg(Expr(ident), nothing, nothing, expr)
	SN(SH(K"::", _), [SN(SH(K"Identifier", _), _) && ident, type]) => KwArg(Expr(ident), expand_forms(type, ctx), nothing, expr)
	other => throw(ASTException(expr, "invalid keyword argument syntax $other"))
end

hasduplicates(array) = length(unique(array)) != length(array)

unpack_fn_name = @λ begin 
SN(SH(K".", _), [rec, SN(SH(K"quote", _), [field && SN(SH(K"Identifier", _), _)])]) => push!(unpack_fn_name(rec), Expr(field))
SN(SH(K"Identifier", _), _) && name => [Expr(name)]
end

resolve_function_name(e, ctx) = @match e begin 
	SN(SH(K"Identifier", _), _) && name => ResolvedName([Expr(name)], e) # symbols are valid
	SN(SH(K".", _), _) && e => ResolvedName(unpack_fn_name(e), e)
	SN(SH(K"::", _), [name, type]) => DeclName(analyze_lvalue(name, ctx), expand_forms(type, ctx), e)
	SN(SH(K"::", _), [type]) => DeclName(nothing, expand_forms(type, ctx), e)
    SN(SH(K"curly", _), [_, _..., SN(SH(K"parameters", _), _)]) => throw(ASTException(e, "unexpected semicolon"))
    SN(SH(K"curly", _), [receiver, args...]) =>
		if any(iskwarg, args) 
			throw(ASTException(e,"misplaced assignment statement"))
		else 
			TypeFuncName(expand_forms(receiver, ctx), [let param = extract_implicit_whereparam(arg, ctx); isnothing(param) ? expand_forms(arg, ctx) : param end for arg in args], e)
		end
	nothing => AnonFuncName(e)
	_ => throw(ASTException(e, "invalid function name"))
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
					throw(ASTException(call, "macros cannot accept keyword arguments"))
				end
		end
	end #>=1 forbidden by parsing
	if !isnothing(name)
		if is_macro
			@match name begin
				SN(SH(K"Identifier", _), _) => nothing
				_ => throw(ASTException(call, "invalid macro definition"))
			end
		end
		name = check_dotop(name)
	end
	varargs_indices = findall(arg -> arg.binding isa VarargAssignment, args_stmts)
	if !isempty(varargs_indices) && last(varargs_indices) != length(varargs_indices)
		throw(ASTException(call, "invalid \"...\" on non-final argument"))
	end
	get_fnarg_name = @λ begin 
		FnArg(IdentifierAssignment(name, _) || TypedAssignment(IdentifierAssignment(name, _), _, _,), _, _, _) => [name]
		expr => begin [] end
	end
	argnames = vcat(collect(Iterators.flatten(map(get_fnarg_name, args_stmts))), map(x -> x.name, kwargs_stmts))
	staticnames = map(x -> x.name, sparams)
	if !isempty(argnames) && hasduplicates(argnames)
		throw(ASTException(call, "function argument name not unique"))
	elseif !isempty(staticnames) && hasduplicates(staticnames)
		throw(ASTException(call, "function static parameter names not unique"))
	elseif !isempty(argnames) && !isempty(staticnames) && (argnames ⊆ staticnames || staticnames ⊆ argnames)
		throw(ASTException(call, "function argument and static parameter names must be distinct"))
	end
	return resolve_function_name(name, ctx), args_stmts, kwargs_stmts, sparams, (isnothing(rett) ? nothing : expand_forms(rett, ctx))
end

function destructure_function_head(name)
	raw_typevars = []
	if kindof(name) == K"where"
		(name, vars) = flatten_where_expr(name)
		@match name begin 
			SN(SH(K"call" || K"::" || K"tuple", _), _) => nothing
			_ => throw(ASTException(name, "Invalid assignment location")) # I don't think that this should happen from parsed code?
		end
		raw_typevars = vars
	end
	decl, rett, name = @match name begin
	    SN(SH(K"::", _), [true_name, typ]) => (true, typ, true_name)
	    _ => (false, nothing, name) # todo return a valid thingie
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
		_ => throw(ASTException(orig_expr, "invalid assignment location name $name in $orig_expr"))
	end
end
function expand_anon_function(spec, ctx)
	orig_expr = spec
	spec, rett, raw_typevars = destructure_function_head(spec)
	return @match spec begin
		SN(SH(K"tuple", _), [args...]) =>  analyze_call(orig_expr, nothing, args, raw_typevars, rett, ctx)
		SN(SH(K"Identifier", _), _) && arg =>  analyze_call(orig_expr, nothing, [arg], raw_typevars, rett, ctx)
		_ => throw(ASTException(orig_expr, "invalid assignment location name $name"))
	end
end
function analyze_let_eq(expr) 
	return @match expr begin
		FunctionAssignment(ResolvedName([_], _), _, _, _, _, _) && fun => fun
		FunctionAssignment(name, _, _, _, _, _) => throw(ASTException(name.location.basenode, "invalid let syntax"))
		TupleAssignment(_, _) && tup => tup
		IdentifierAssignment(_, _) && id => id
		_ => throw(ASTException(expr, "invalid let syntax"))
	end
end
analyze_let_binding(expr, ctx) = @match expr begin 
	SN(SH(K"Identifier", _), _) && ident => Expr(ident)
	SN(SH(K"=", _), [a, b]) => (analyze_let_eq(analyze_lvalue(a, ctx))) => expand_forms(b, ctx)
	_ => throw(ASTException(expr, "invalid let syntax"))
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
	_ && invalid => throw(ASTException(invalid, "invalid type signature"))
end

node_to_bool = @λ begin 
	SN(SH(K"true",_), _) => true
	SN(SH(K"false",_), _) => false
	expr => throw(ASTException(expr, "boolean used in non-boolean context"))
end

unpack_attrs(expr, attrs, mutable, ctx) = @match (expr, mutable) begin 
	(SN(SH(K"=", _), [lhs && GuardBy(eventually_decl), value]), _) => throw(ASTException(expr, "inside type definition is reserved"))
	(SN(SH(K"::", _), [SN(SH(K"Identifier", _), _) && name, typ]), _) => StructField(Expr(name), expand_forms(typ, ctx), attrs, expr)
	(SN(SH(K"Identifier", _), _) && name, _) => StructField(Expr(name), nothing, attrs, expr)
	(SN(SH(K"const", _), [ex]), true) => unpack_attrs(ex, attrs | FIELD_CONST, mutable, ctx)
	(SN(SH(K"const", _), [ex]), false) => throw(ASTException(expr, "invalid field attribute const for immutable struct"))
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
	name, params, super = analyze_type_sig(sig)
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
	name, params, super = analyze_type_sig(sig)
	bounds = analyze_typevar.(params, (ctx, ))
	params = getfield.(bounds, :name)
	return AbstractDefStmt(Expr(name), params, isnothing(super) ? nothing : expand_forms(super, ctx), expr)
end

function expand_primitive_def(expr, sig, size, ctx)
	name, params, super = analyze_type_sig(sig)
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
	SN(SH(K"parameters", _), [params...]) => throw(ASTException(expr, "more than one semicolon in argument list"))
	SN(SH(K"=" || K"kw", _), [name && SN(SH(K"Identifier", _), _), value]) => KeywordArg(Expr(name), expand_forms(value, ctx), expr)
	SN(SH(K"Identifier", _), _) && name => KeywordArg(Expr(name), expand_forms(name, ctx), expr)
	SN(SH(K".", _), [_, SN(SH(K"quote", _), [field && SN(SH(K"Identifier", _), _)])]) => KeywordArg(Expr(field), expand_forms(expr, ctx), expr)
	_ => throw("inexhaustive $expr")
end
analyze_kw_call(params, ctx) = map(x -> analyze_kw_param(x, ctx), params)
function split_arguments(args, ctx; down=expand_forms)
	pos_args = []; kw_args = []
	for arg in args 
		@match arg begin 
			SN(SH(K"parameters", _), [params...]) => append!(kw_args, analyze_kw_call(params, ctx))
			SN(SH(K"kw", _), [SN(SH(K"Identifier", _), _) && name, value]) => push!(kw_args, KeywordArg(Expr(name), down(value, ctx), arg))
			SN(SH(K"...", _), [arg]) => push!(pos_args, SplatArg(down(arg, ctx), arg))
			expr => push!(pos_args, PositionalArg(down(expr, ctx), arg))
		end
	end
	return pos_args, kw_args
end

#=
partially_expand_ref = @λ begin 
	SN(SH(K"ref", _), [arr, idxes]) => GetIndex(expand_forms(arr), split_arguments(idxes)...)
end
commented out b/c it's not a complete match
=# 
function ref_to_view(e, ctx)
	@match e begin 
		SN(SH(K"ref", _), [arr, idxes...]) => GetIndex(expand_forms(arr, ctx), split_arguments(idxes, ctx)...)
		SN(SH(K".", _), [l, r]) => GetProperty(expand_forms(arr, ctx), Literal(Expr(r)))
		_ => expand_forms(e, ctx)
	end
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
			throw(ASTException(expr, "expected assignment after \"const\""))
		end
	SN(SH(K"::", _), _) => VarDecl(analyze_lvalue(expr, ctx), nothing, decltype, expr)
	SN(SH(GuardBy(JuliaSyntax.is_prec_assignment), _), [lhs, rhs]) => VarDecl(analyze_lvalue(lhs, ctx), expand_forms(rhs, ctx), decltype, expr)
end
expand_named_tuple_arg(expr, ctx) = @match expr begin 
	SN(SH(K"kw" || K"=", _), [SN(SH(K"Identifier", _), _) && name, rhs]) => NamedValue(Expr(name), expand_forms(rhs, ctx), expr)
	SN(SH(K"kw" || K"=", _), [lhs, rhs]) => throw(ASTException(expr, "invalid name"))
	SN(SH(K"Identifier", _), _) && name => NamedValue(Expr(name), expand_forms(name, ctx), expr)
	SN(SH(K".", _), [rec, SN(SH(K"quote", _), [field && SN(SH(K"Identifier", _), _)])]) && ast => NamedValue(Expr(field), expand_forms(ast, ctx), expr)
	SN(SH(K"call", GuardBy(JuliaSyntax.is_infix)), [lhs, SN(SH(K"=>", _), _), rhs]) => ComputedNamedValue(expand_forms(lhs, ctx), expand_forms(rhs, ctx), expr)
    SN(SH(K"...", _), [splat]) => SplattedNamedValue(expand_forms(splat, ctx), expr)
	expr => throw("invalid $expr")
end
expand_named_tuple(args, ctx) = expand_named_tuple_arg.(args, (ctx, ))

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
	GuardBy(isassignment) => throw(ASTException(expr, "misplaced assignment statement"))
	GuardBy(isparam) => throw(ASTException(expr, "unexpected semicolon in array expression"))
	SN(SH(K"...", _), [body]) => Splat(expand_forms(body, ctx), expr)
	e => expand_forms(e, ctx)
end

expand_row(el, toplevel, ctx) = @match el begin
	GuardBy(isassignment) => throw(ASTException(el, "misplaced assignment statement"))
	GuardBy(isparam) => throw(ASTException(el, "unexpected semicolon in array expression"))
	SN(SH(K"row", _), elems) => if toplevel Row(expand_row.(elems, false, (ctx, )), el) else throw(ASTException(el, "nested rows not supported")) end
	SN(SH(K"...", _), [body]) => Splat(expand_forms(body, ctx), el)
	e => expand_forms(e, ctx)
end

expand_nrow(expr, ctx) = @match expr begin
	GuardBy(isassignment) => throw(ASTException(expr, "misplaced assignment statement"))
	GuardBy(isparam) => throw(ASTException(expr, "unexpected semicolon in array expression"))
	SN(SH(K"nrow", flgs), elems) => NRow(JuliaSyntax.numeric_flags(flgs), expand_nrow.(elems, (ctx, )), expr)
	SN(SH(K"...", _), body) => throw(ASTException(expr, "Splatting ... in an hvncat with multiple dimensions is not supported"))
	e => expand_forms(e, ctx)
end

expand_vcat(params, ctx) = VCat(expand_row.(params, true, ctx))
expand_iterator(expr, ctx)::Iterspec = @match expr begin 
	SN(SH(K"=", _), [lhs, rhs]) => IterEq(analyze_lvalue(lhs, ctx), expand_forms(rhs, ctx), expr)
	SN(SH(K"filter", _), [iters..., cond]) => Filter(expand_iterator.(iters, (ctx,)), expand_forms(cond, ctx), expr)
end
expand_generator(expr, ctx)::Expression = @match expr begin 
	SN(SH((K"generator" || K"flatten") && head, _), [expr, iters...]) => Generator(head == K"flatten", expand_forms(expr, ctx), Iterspec[expand_iterator(iter, ctx) for iter in iters], expr)
end

expand_import_source = @λ begin 
	SN(SH(K".", _), path) => expand_import_path(path)
end
expand_import_clause(expr) = @match expr begin 
	SN(SH(K".", _), path) => Dep(expand_import_path(path), expr)
	SN(SH(K"as", _), [SN(SH(K".", _), path), SN(SH(K"Identifier", _), _) && alias]) => AliasDep(expand_import_path(path), Expr(alias), expr)
end

function expand_import_path(src_path)
	path = nothing
	for path_el in src_path 
		path = @match (path_el, path) begin
			(SN(SH(K"Identifier" || K"MacroName", _), _) && id, nothing) => ImportId(Expr(id), path_el)
			(SN(SH(K"Identifier" || K"MacroName", _), _) && id, path) => ImportField(path, Expr(id), path_el)
			(SN(SH(K".", _), _), nothing) => ImportRelative(1, path_el)
			(SN(SH(K".", _), _), ImportRelative(lvl, _)) => ImportRelative(lvl+1, path_el)
			(SN(SH(K".", _), _), _) => throw(ASTException(src_path, "invalid path: \".\" in identifier path"))
			(_, _) => throw(ASTException(path_el, "invalid path"))
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

resolve_toplevel_macro(ast, macroname, args, ctx) = @match macroname begin
    SN(SH(K"core_@doc", _), _) => MacroExpansionStmt(expand_docstring(expand_toplevel, args, ast, ctx), ast)
    _ => MacroExpansionStmt(Literal(:placeholder, ast), ast)
end
resolve_macro(ast, macroname, args, ctx) = @match macroname begin
    SN(SH(K"core_@doc", _), _) => MacroExpansion(expand_docstring(expand_forms, args, ast, ctx), ast)
    _ => MacroExpansion(Literal(:placeholder, ast), ast)
end

struct ExpandCtx 
	is_toplevel::Bool
	is_loop::Bool
	in_module::Bool
    macro_resolver::Function
    toplevel_macro_resolver::Function
	ExpandCtx(is_toplevel::Bool=false, is_loop::Bool=false; in_module=false, macroresolver=resolve_macro, tlresolver=resolve_toplevel_macro) = new(is_toplevel, is_loop, in_module, macroresolver, tlresolver)
	ExpandCtx(base; 
		is_toplevel::Union{Bool, Nothing}=nothing, 
		is_loop::Union{Bool, Nothing}=nothing,
		in_module::Union{Bool, Nothing}=nothing) = new(
			isnothing(is_toplevel) ? false : is_toplevel, 
			isnothing(is_loop) ? base.is_loop : is_loop,
			isnothing(in_module) ? false : in_module,
            base.macro_resolver, base.toplevel_macro_resolver)
end

next_ctx(head, ctx) = ExpandCtx(ctx)

function handle_macrocall(mcro, ast)
	return Literal(:placeholder, mcro)
end

expand_toplevel(ast::JuliaSyntax.SyntaxNode, ctx::ExpandCtx) = @match ast begin 
    SN(SH(K"using", _), [SN(SH(K":", _), [mod, terms...])]) => SourceUsingStmt(expand_import_source(mod), expand_import_clause.(terms), ast)
    SN(SH(K"using", _), [terms...]) => UsingStmt(expand_import_source.(terms), ast)
    SN(SH(K"import", _), [SN(SH(K":", _), [mod, terms...])]) => SourceImportStmt(expand_import_source(mod), expand_import_clause.(terms), ast)
    SN(SH(K"import", _), [terms...]) => ImportStmt(expand_import_clause.(terms), ast)
    SN(SH(K"export", _), syms) => ExportStmt(Expr.(syms), ast)
    SN(SH(K"module", _), [stdimports, name, SN(SH(K"block", _), stmts)]) => ModuleStmt(Expr(stdimports), Expr(name), expand_toplevel.(stmts, (ctx, )), ast)
    SN(SH(K"abstract", _), [sig]) => expand_abstract_def(ast, sig, ctx)
    SN(SH(K"struct", _), [mut, sig, fields]) => expand_struct_def(ast, node_to_bool(mut), sig, fields, ctx)
    SN(SH(K"primitive", _), [sig, size]) => expand_primitive_def(ast, sig, size, ctx)
    SN(SH(K"toplevel", _), exprs) => ToplevelStmt(expand_toplevel.(exprs, (ctx, )), ast)
    SN(SH(K"macrocall", _), [name, args...]) => ctx.toplevel_macro_resolver(ast, name, args, ctx)
	expr => ExprStmt(expand_forms(expr, JuliaSyntax.head(expr), JuliaSyntax.children(expr), ExpandCtx(ctx; is_toplevel = true)), ast)
end

expand_forms(ast::JuliaSyntax.SyntaxNode, ctx::ExpandCtx) = expand_forms(ast, JuliaSyntax.head(ast), JuliaSyntax.children(ast), next_ctx(JuliaSyntax.head(ast), ctx))
expand_forms(ast, head, children, ctx) = @match (head, children) begin
	(SH(K"Float" || K"Integer" || K"String" || K"Char" || K"true" || K"false", _), _) => Literal(Expr(ast), ast)
    (SH(K"quote",_), _) => Quote(ast, ast) # need to port bits of macroexpansion into this
    (SH(K"function", _), [name, body]) => FunctionDef(expand_function_name(name, ctx)..., expand_forms(body, ctx), ast)
    (SH(K"function", _), [name]) => FunctionDef(expand_function_name(name, ctx)..., nothing, ast)
    (SH(K"->", _), [name, body]) => FunctionDef(expand_anon_function(name, ctx)..., expand_forms(body, ctx), ast)
    (SH(K"let", _), [SN(SH(K"block", _), bindings), body]) => LetBinding(analyze_let_binding.(bindings, (ctx, )), expand_forms(body, ctx), ast)
    (SH(K"let", _), [binding, body]) => LetBinding([analyze_let_binding(binding, ctx)], expand_forms(body, ctx), ast)
    (SH(K"macro", _), [SN(SH(K"call", _), _) && name, body]) => MacroDef(expand_macro_name(name, ctx)..., expand_forms(body, ctx), ast)
    (SH(K"macro", _), [SN(SH(K"Identifier", _), _) && name]) => MacroDef(expand_macro_name(name, ctx)..., nothing, ast)
    (SH(K"macro", _), _) => throw(ASTException(ast, "invalid macro definition"))
    (SH(K"try", _ && GuardBy(x->JuliaSyntax.has_flags(x, JuliaSyntax.TRY_CATCH_AFTER_FINALLY_FLAG))), 
		[block, SN(SH(K"false", _), _), SN(SH(K"false", _), _), else_block, finally_block, catch_var, catch_block]) => TryCatch(expand_forms(block, ctx), ifnotfalse(catch_var, x->Expr(x)), ifnotfalse(catch_block, x -> expand_forms(x, ctx)), ifnotfalse(else_block, x -> expand_forms(x, ctx)), ifnotfalse(finally_block, x -> expand_forms(x, ctx)), ast)
    (SH(K"try", _), [block, catch_var, catch_block, else_block, finally_block]) => TryCatch(expand_forms(block, ctx), ifnotfalse(catch_var, x->Expr(x)), ifnotfalse(catch_block, x -> expand_forms(x, ctx)), ifnotfalse(else_block, x -> expand_forms(x, ctx)), ifnotfalse(finally_block, x -> expand_forms(x, ctx)), ast)
    (SH(K"block", _), stmts) => Block(expand_forms.(stmts, (ctx, )), ast)
    (SH(K".", _), [op]) => Broadcast(expand_forms(op, ctx), ast)
	(SH(K".", _), [f, SN(SH(K"quote", _), [x && SN(SH(K"Identifier", _), _)])]) => GetProperty(expand_forms(f, ctx), Expr(x), ast)
	(SH(K".", _), [f, SN(SH(K"quote", _), [x]) && lit]) => GetProperty(expand_forms(f, ctx), Literal(Expr(x), lit), ast)
	(SH(K".", _), [f, SN(SH(K"tuple", _), args)]) => FunCall(Broadcast(expand_forms(f, ctx), ast), split_arguments(args, ctx)..., ast)
	(SH(K"comparison", _), [initial, args...]) => Comparison(expand_forms(initial, ctx), map((op, value) -> expand_forms(op, ctx) => expand_forms(value, ctx), args[1:2:end], args[2:2:end]), ast)
	(SH(K"&&", _ && GuardBy(JuliaSyntax.is_dotted)), [l, r]) => FunCall(Broadcast(Variable(:(&&), ast), ast), split_arguments([l, r], ctx)..., ast)
	(SH(K"||", _ && GuardBy(JuliaSyntax.is_dotted)), [l, r]) => FunCall(Broadcast(Variable(:(||), ast), ast), split_arguments([l, r], ctx)..., ast)
    (SH(K"=", _ && GuardBy(JuliaSyntax.is_dotted)), [lhs, rhs]) => Assignment(BroadcastAssignment(analyze_lvalue(lhs, ctx), ast), expand_forms(rhs, ctx), ast)
    (SH(K"<:", _), [a,b]) => FunCall(Variable(:(<:)), split_arguments([a, b], ctx)..., ast)
    (SH(K">:", _), [a,b]) => FunCall(Variable(:(>:)), split_arguments([a, b], ctx)..., ast)
    (SH(K"-->", _), _) => FunCall(Variable(:(-->)), split_arguments([a, b], ctx)..., ast)
    (SH(K"where", _), [typ, vars...]) => WhereType(expand_forms(typ, ctx), analyze_typevar.(vars, (ctx, )), ast)
    (SH((K"const" || K"local" || K"global") && decltype, _), decls) => Declaration(expand_declaration.(convert_decltype(decltype), decls, (ctx, )), ast)
    (SH(K"=", _), [lhs, rhs]) => Assignment(analyze_lvalue(lhs, ctx), expand_forms(rhs, ctx), ast)
    (SH(K"ref", _), [arr, idxes...]) => GetIndex(expand_forms(arr, ctx), split_arguments(idxes, ctx)..., ast)
    (SH(K"curly", _), [_, _..., SN(SH(K"parameters", _), _)]) => throw(ASTException(ast, "unexpected semicolon"))
    (SH(K"curly", _), [receiver, args...]) =>
		if any(iskwarg, args) 
			throw(ASTException(ast, "misplaced assignment statement"))
		else 
			CallCurly(expand_forms(receiver, ctx), [let param = extract_implicit_whereparam(arg, ctx); isnothing(param) ? expand_forms(arg, ctx) : param end for arg in args], ast)
		end
	(SH(K"call", GuardBy(JuliaSyntax.is_infix)), [arg1, f, arg2]) => FunCall(expand_forms(f, ctx), split_arguments([arg1, arg2], ctx)..., ast) # todo Global method definition needs to be placed at the toplevel
	(SH(K"call", _), [f, args...]) => FunCall(expand_forms(f, ctx), split_arguments(args, ctx)..., ast)
	(SH(K"call", _), [SN(SH(K".", _), [op]), args]) => FunCall(Broadcast(expand_forms(op, ctx)), split_arguments(args, ctx)..., ast)
    (SH(K"do", _), [call, args, body]) => 
		let 
			(_, args, _, _, _) = expand_anon_function(args, ctx);
			DoStatement(expand_forms(call, ctx), args, expand_forms(body, ctx), ast)
		end
	(SH(K"tuple", _), [arg1, args..., SN(SH(K"parameters", _), _)]) => throw(ASTException(ast, "unexpected semicolon in tuple"))
	(SH(K"tuple", _), [SN(SH(K"parameters", _), params)]) => NamedTupleExpr(expand_named_tuple(params, ctx), ast)
	(SH(K"tuple", _), args) => any(isassignment, args) ? NamedTupleExpr(expand_named_tuple(args, ctx), ast) : TupleExpr(expand_tuple_arg.(args, (ctx, )), ast)
    (SH(K"braces", _), _) => throw(ASTException(ast, "{ } vector syntax is discontinued"))
    (SH(K"bracescat", _), _) => throw(ASTException(ast, "{ } matrix syntax is discontinued"))
    (SH(K"string", _), args) => StringInterpolate(string_interpoland.(args, (ctx, )), ast)
    (SH(K"::", _), [_]) => throw(ASTException(ast, "invalid \"::\" syntax"))
    (SH(K"::", _), [val, typ]) => TypeAssert(expand_forms(val, ctx), expand_forms(typ, ctx), ast)
    (SH(K"if", _), params) => expand_if(ast, params, ctx)
    (SH(K"while", _), [cond, body]) => let ictx = ExpandCtx(ctx; is_loop=true); WhileStmt(expand_forms(cond, ictx), expand_forms(body, ictx), ast) end
    (SH(K"break", _), _) => if ctx.is_loop BreakStmt(ast) else throw(ASTException(ast, "break or continue outside loop")) end
    (SH(K"continue", _), _) => if ctx.is_loop ContinueStmt(ast) else throw(ASTException(ast, "break or continue outside loop")) end
    (SH(K"return", _), [SN(SH(K"nothing", _), _)]) => ReturnStmt(nothing, ast)
    (SH(K"return", _), [val]) => ReturnStmt(expand_forms(val, ctx), ast)
    (SH(K"for", _), [SN(SH(K"=", _), _) && iterspec, body]) => let ictx = ExpandCtx(ctx; is_loop=true); ForStmt(Pair{LValue, Expression}[analyze_iterspec(iterspec, ictx)], expand_forms(body, ctx), ast) end
    (SH(K"for", _), [SN(SH(K"block", _), iterspecs), body]) => let ictx = ExpandCtx(ctx; is_loop=true); ForStmt(Pair{LValue, Expression}[analyze_iterspec(iterspec, ictx) for iterspec in iterspecs], expand_forms(body, ictx), ast) end
    (SH(K"&&", _), [l, r]) => FunCall(Variable(:(&&), ast), split_arguments([l, r], ctx)..., ast)
    (SH(K"||", _), [l, r]) => FunCall(Variable(:(||), ast), split_arguments([l, r], ctx)..., ast)
    (SH(K"&", _), _) => throw(ASTException(ast, "invalid syntax"))
    (SH(upd && GuardBy(is_update), _ && GuardBy(JuliaSyntax.is_dotted)), [lhs, rhs]) => Update(Symbol(upd), analyze_lvalue(lhs,ctx), expand_forms(rhs, ctx), true, ast)
    (SH(upd && GuardBy(is_update), _), [lhs, rhs]) => Update(Symbol(upd), analyze_lvalue(lhs, ctx), expand_forms(rhs, ctx), false, ast)
    (SH(K"$", _), _) => throw(ASTException(ast, "\"\$\" expression outside quote"))
    (SH(K"...", _), _) => throw(ASTException(ast, "\"...\" expression outside call"))
    (SH(K"vect", _), [_..., SN(SH(K"parameters", _), _)]) => throw(ASTException(ast, "unexpected semicolon in array expression"))
    (SH(K"vect", _), elems) => any(isassignment, elems) ? throw(ASTException(ast, "misplaced assignment statement")) : Vect(expand_hcat_arg.(elems, (ctx, )), ast)
    (SH(K"hcat" || K"typed_hcat", _), elems && GuardBy(x -> any(isassignment, x))) => throw(ASTException(ast, "misplaced assignment statement")) 
	(SH(K"hcat", _), elems) => HCat(nothing, expand_hcat_arg.(elems, (ctx, )), ast)
	(SH(K"typed_hcat", _), [type, elems...]) => HCat(expand_forms(type, ctx), expand_hcat_arg.(elems, (ctx, )), ast)
    (SH(K"vcat", _), params) => VCat(nothing, expand_row.(params, true, (ctx, )), ast)
    (SH(K"typed_vcat", _), [type, params...]) => VCat(expand_forms(type, ctx), expand_row.(params, true, (ctx, )), ast)
    (SH(K"ncat", flags), elems) => NCat(nothing, JuliaSyntax.numeric_flags(flags), expand_nrow.(elems, (ctx, )), ast)
    (SH(K"typed_ncat", flags), [type, elems...]) => NCat(expand_forms(type, ctx), JuliaSyntax.numeric_flags(flags), expand_nrow.(elems, (ctx, )), ast)
    (SH(K"generator", _), elems && GuardBy(x -> any(contains_return, x))) => throw(ASTException(ast, "\"return\" not allowed inside comprehension or generator"))
    (SH((K"generator" || K"flatten") && head, _), [expr, iters...]) => expand_generator(ast, ctx)
    (SH(K"comprehension", _), [generator]) => Comprehension(expand_generator(generator, ctx), ast)
    (SH(K"typed_comprehension", _), [type, generator]) => Comprehension(expand_forms(type, ctx), expand_generator(generator, ctx), ast)
	(SH(K"Identifier", _), _) => Variable(Expr(ast), ast)
	(SH(K"macrocall", _), [mcro, args...]) => ctx.macro_resolver(ast, mcro, args, ctx)
    (SH(K"?", _), [cond, then, els]) => Ternary(expand_forms(cond, ctx), expand_forms(then, ctx), expand_forms(els, ctx), ast)
	(SH(K"using" || K"import" || K"export" || K"module" || K"abstract" || K"struct" || K"primitive", _), _) => throw(ASTException(ast, "must be at top level"))
	(SH(op && GuardBy(JuliaSyntax.is_operator), _ && GuardBy(JuliaSyntax.is_dotted)), _) => Broadcast(Variable(Symbol(string(op)), ast), ast)
	(SH(GuardBy(JuliaSyntax.is_operator), _), _) => Variable(Expr(ast), ast)
    (head, args) => throw("Unimplemented $head")
end
