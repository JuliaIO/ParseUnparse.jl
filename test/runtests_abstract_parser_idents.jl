using ParseUnparse.ContextFreeGrammarUtil
using ParseUnparse.SymbolGraphs
using ParseUnparse.AbstractParserIdents
using Test

struct ParserIdent <: AbstractParserIdent end

function AbstractParserIdents.get_lexer(::ParserIdent)
    function lexer(iterator)
        function f(c::Char)
            (nothing, c)
        end
        Iterators.map(f, iterator)
    end
end

function AbstractParserIdents.get_token_grammar(::ParserIdent)
    start_symbol = 'A'
    rules = (
        ('A' => Set(([],))),
    )
    (start_symbol, Dict{Char, Set{Vector{Char}}}(rules))
end

function AbstractParserIdents.get_token_parser(id::ParserIdent)
    (start_symbol, grammar) = get_token_grammar(id)
    tables = make_parsing_table_strong_ll_1(grammar, start_symbol)
    StrongLL1TableDrivenParser{Union{}, Nothing}(start_symbol, tables...)
end

@testset "`AbstractParserIdents`" begin
    @test let p = get_parser(ParserIdent())
        (tree, err) = @inferred p("")
        isempty(err) && (tree isa SymbolGraphRooted)
    end
end
