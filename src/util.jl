struct ASTException <: Exception 
	source_node::JuliaSyntax.SyntaxNode
	reason::String
end

first_byte(e::ASTException) = e.source_node.position
last_byte(e::ASTException) = e.source_node.position + JuliaSyntax.span(e.source_node) - 1

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
			:($casename($(params...))) => push!(outbody, :(@ast_node struct $casename <: $supertype; $(params...) end))
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
					end
					_::LineNumberNode => nothing
				end
			end

			out = quote
				struct $prop <: $super; 
					$(output_body...); 
					location::Union{$SemanticAST.SourcePosition, Nothing};
					$prop($((:($argname) for (argname, argtype) in init_fields)...), basenode::Union{$JuliaSyntax.SyntaxNode, Nothing}) = 
						new($((argname for (argname, argtype) in init_fields)...), isnothing(basenode) ? nothing : $SemanticAST.SourcePosition(basenode)) 
				end;
				$MLStyle.@as_record $(esc(prop))
			end
			return out
		end
	end
end
