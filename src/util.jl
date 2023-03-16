struct ASTException <: Exception 
	source_node::JuliaSyntax.SyntaxNode
	reason::String
end

first_byte(e::ASTException) = e.source_node.position
last_byte(e::ASTException) = e.source_node.position + JuliaSyntax.span(e.source_node) - 1
global ast_id::Int = 0
function make_id()
	old = ast_id
	ast_id += 1
	return ast_id
end

# stolen from JuliaSyntax in most part
function Base.show(io::IO, exception::ASTException)
    source = exception.source_node.source
    color,prefix = (:light_red, "Error")
    line, col = JuliaSyntax.source_location(source, first_byte(exception))
    linecol = "$line:$col"
    filename = source.filename
    if !isnothing(filename)
        locstr = "$filename:$linecol"
        if get(io, :color, false)
            # Also add hyperlinks in color terminals
            url = "file://$(abspath(filename))#$linecol"
            locstr = "\e]8;;$url\e\\$locstr\e]8;;\e\\"
        end
    else
        locstr = "line $linecol"
    end
    print(io, prefix, ": ")
    printstyled(io, exception.reason, color=color)
    printstyled(io, "\n", "@ $locstr", color=:light_black)
    print(io, "\n")

    p = first_byte(exception)
    q = last_byte(exception)
    text = JuliaSyntax.sourcetext(source)
    if q < p || (p == q && source[p] == '\n')
        # An empty or invisible range!  We expand it symmetrically to make it
        # visible.
        p = max(firstindex(text), prevind(text, p))
        q = min(lastindex(text), nextind(text, q))
    end

    # p and q mark the start and end of the diagnostic range. For context,
    # buffer these out to the surrouding lines.
    a,b = JuliaSyntax.source_line_range(source, p, context_lines_before=2, context_lines_after=1)
    c,d = JuliaSyntax.source_line_range(source, q, context_lines_before=1, context_lines_after=2)

    hicol = (100,40,40)

    # TODO: show line numbers on left

    print(io, source[a:prevind(text, p)])
    # There's two situations, either
    if b >= c
        # The diagnostic range is compact and we show the whole thing
        # a...............
        # .....p...q......
        # ...............b
        JuliaSyntax._printstyled(io, source[p:q]; bgcolor=hicol)
    else
        # Or large and we trucate the code to show only the region around the
        # start and end of the error.
        # a...............
        # .....p..........
        # ...............b
        # (snip)
        # c...............
        # .....q..........
        # ...............d
        JuliaSyntax._printstyled(io, source[p:b]; bgcolor=hicol)
        println(io, "…")
        JuliaSyntax._printstyled(io, source[c:q]; bgcolor=hicol)
    end
    print(io, source[nextind(text,q):d])
    println(io)
end

macro ast_data(name, body)
	@assert body isa Expr && body.head == :block
	outbody = []
	supertype = nothing
	@match name begin 
		:($sname <: $_) => begin supertype = sname end
		_ => nothing
	end
	for elem in body.args
		@match elem begin 
			:($casename($(params...))) => begin
				push!(outbody, :(@ast_node struct $casename <: $supertype; $(params...) end))
				visit_body = []
				for param in params 
					@match param begin
						:($fldname::$fldtype) && fldspec => begin
							push!(visit_body, :(visit(enter, exit, arg.$fldname)))
						end
					end
				end
			end
			lnn :: LineNumberNode => push!(outbody, lnn)
		end
	end
	return quote 
		abstract type $name end
		$(outbody...)
	end
end

macro ast_node(defn)
	@match defn begin 
		:(struct $prop <: $super; $(fields...); end) => begin
			output_body = []
			hash_body = []
			eq_body = []
			init_fields = []
			for field in fields
				@match field begin 
					:($fldname::$fldtype) && fldspec => begin 
						if fldname != :location
							push!(init_fields, fldname => fldtype)
						else
							throw("Location specified explicitly; ast node locations are implicit!")
						end
						push!(output_body, fldspec)
						push!(hash_body, :(h = hash(node.$fldname, h)))
						push!(eq_body, :(self.$fldname == other.$fldname))
					end
					_::LineNumberNode => nothing
				end
			end
			eq_check = foldl((exp, el) -> :($exp && $el), eq_body; init = :(self.location == other.location))

			out = quote
				struct $prop <: $super; 
					$(output_body...); 
					location::Union{$SemanticAST.SourcePosition, Nothing};
					$prop($((:($argname) for (argname, argtype) in init_fields)...), basenode::Union{$JuliaSyntax.SyntaxNode, Nothing}) = 
						new($((argname for (argname, argtype) in init_fields)...), isnothing(basenode) ? nothing : $SemanticAST.SourcePosition(basenode)) 
				end;
				function $(esc(:visit))(enter, exit, arg::$(esc(prop))) enter(arg); $((:(visit(enter, exit, arg.$argname)) for (argname, argtype) in init_fields)...); exit(arg) end
				function Base.hash(node::$(esc(prop)), h::UInt) 
					$(hash_body...)
					h = hash(node.location, h)
					return h
				end
				Base.:(==)(self::$(esc(prop)), other::$(esc(prop))) = $eq_check
				$MLStyle.@as_record $(esc(prop))
			end
			return out
		end
	end
end

visit(enter, exit, elems::Vector{T}) where T = for elem in elems visit(enter, exit,elem) end
visit(enter, exit, elem::Pair{T, U}) where {T, U} = begin visit(enter, exit, elem[1]); visit(enter, exit, elem[2]) end
visit(enter, exit, alt) = begin enter(alt); exit(alt) end