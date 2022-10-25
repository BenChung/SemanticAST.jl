struct ASTException <: Exception 
	source_node::JuliaSyntax.SyntaxNode
	reason::String
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
