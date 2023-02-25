
function MLStyle.pattern_uncall(::Type{JuliaSyntax.SyntaxNode}, self, type_params, type_args, args)
	t = JuliaSyntax.SyntaxNode
    tcons(_...) = t
    comp = PComp("$t", tcons;)
    function extract(sub::Any, i::Int, ::Any, ::Any)
    	if i == 1
    		return :(JuliaSyntax.head($sub))
    	elseif i == 2
    		return :(JuliaSyntax.children($sub)) 
    	end
    end
    return decons(comp, extract, map(self, args))
end

function MLStyle.pattern_uncall(::Type{JuliaSyntax.SyntaxHead}, self, type_params, type_args, args)
	t = JuliaSyntax.SyntaxHead
    tcons(_...) = t
    comp = PComp("$t", tcons;)
    function extract(sub::Any, i::Int, ::Any, ::Any)
    	if i == 1
    		return :($sub.kind)
    	elseif i == 2
    		return :($sub.flags)
    	end
    end
    return decons(comp, extract, map(self, args))
end


struct SyntaxFlags
	flags::JuliaSyntax.RawFlags
end

flag_assignment = Dict{Symbol, UInt16}(
	:TRIVIA => JuliaSyntax.TRIVIA_FLAG,
	:INFIX => JuliaSyntax.INFIX_FLAG,
	:DOTOP => JuliaSyntax.DOTOP_FLAG,
	:TRIPLE_STRING => JuliaSyntax.TRIPLE_STRING_FLAG,
	:RAW_STRING => JuliaSyntax.RAW_STRING_FLAG,
	:SUFFIXED => JuliaSyntax.SUFFIXED_FLAG
)
@active InfixHead(x) begin
    return JuliaSyntax.is_infix(x)
end
@active DottedHead(x) begin
    return JuliaSyntax.is_dotted(x)
end
function MLStyle.pattern_uncall(::Type{SyntaxFlags}, self, type_params, type_args, args)
	if any((!).(haskey.((flag_assignment,), args)))
		throw("invalid flag in $args")
	end
	flag_match = reduce(|, getindex.((flag_assignment,), args); init=0)
end
