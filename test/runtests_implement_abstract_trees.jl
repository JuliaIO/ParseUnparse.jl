using ParseUnparse.ContextFreeGrammarUtil
using ParseUnparse.SymbolGraphs
using Test
using AbstractTrees: AbstractTrees

const dyck_language_parser = let
    only_nonterminal = 'A' => Set(([], ['(', 'A', ')', 'A']))
    grammar = Dict{Char, Set{Vector{Char}}}(only_nonterminal)
    start_symbol = only(keys(grammar))
    parsing_tables = make_parsing_table_strong_ll_1(grammar, start_symbol)
    StrongLL1TableDrivenParser{Union{}, Nothing}(start_symbol, parsing_tables...)
end

struct LanguageExampleString
    string::String
    leaves::Vector{Char}
    preorder::Vector{Char}
    postorder::Vector{Char}
end

const dyck_language_examples = LanguageExampleString[
    LanguageExampleString("", ['A'], ['A'], ['A']),
    LanguageExampleString("()", ['(', 'A', ')', 'A'], ['A', '(', 'A', ')', 'A'], ['(', 'A', ')', 'A', 'A']),
    LanguageExampleString("()()", ['(', 'A', ')', '(', 'A', ')', 'A'], ['A', '(', 'A', ')', 'A', '(', 'A', ')', 'A'], ['(', 'A', ')', '(', 'A', ')', 'A', 'A', 'A']),
    LanguageExampleString("(())", ['(', '(', 'A', ')', 'A', ')', 'A'], ['A', '(', 'A', '(', 'A', ')', 'A', ')', 'A'], ['(', '(', 'A', ')', 'A', 'A', ')', 'A', 'A']),
]

function string_to_toks(s::String)
    function f(kind::Char)
        (nothing, kind)
    end
    Iterators.map(f, s)
end

function get_root_symbol_kind(tree)
    root_symbol_kind(tree.graph)
end

@testset "implement the AbstractTrees interface" begin
    @testset "example_string: $(example.string)" for example ∈ dyck_language_examples
        @test let toks = string_to_toks(example.string)
            (tree, _) = SymbolGraphs.parse(dyck_language_parser, toks)
            example.leaves == @inferred collect(Char, Iterators.map(get_root_symbol_kind, AbstractTrees.Leaves(graph_as_tree(tree))))
        end
        @test let toks = string_to_toks(example.string)
            (tree, _) = SymbolGraphs.parse(dyck_language_parser, toks)
            example.preorder == @inferred collect(Char, Iterators.map(get_root_symbol_kind, AbstractTrees.PreOrderDFS(graph_as_tree(tree))))
        end
        @test let toks = string_to_toks(example.string)
            (tree, _) = SymbolGraphs.parse(dyck_language_parser, toks)
            example.postorder == @inferred collect(Char, Iterators.map(get_root_symbol_kind, AbstractTrees.PostOrderDFS(graph_as_tree(tree))))
        end
    end
end
