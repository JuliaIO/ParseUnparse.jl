using ParseUnparse.Optionals
using ParseUnparse.SymbolGraphs
using Test

const ParsingTableDefault = Dict{Tuple{K, K}, Vector{K}} where {K}
const ParsingTableDefaultEndMarker = Dict{K, Vector{K}} where {K}

const languages = Dict{String, Dict{String, Vector{String}}}(
    "set containing only the empty string" => Dict(
        "included_examples" => [
            "",
        ],
        "excluded_examples" => [
            "t", "tt", "ttt", "tttt",
        ],
    ),
    "set containing only the length-one string" => Dict(
        "included_examples" => [
            "t",
        ],
        "excluded_examples" => [
            "", "tt", "ttt", "tttt",
        ],
    ),
    "set of nonempty strings" => Dict(
        "included_examples" => [
            "t", "tt", "ttt", "tttt",
        ],
        "excluded_examples" => [
            "",
        ],
    ),
    "set of strings of even length" => Dict(
        "included_examples" => [
            "", "tt", "tttt", "tttttt",
        ],
        "excluded_examples" => [
            "t", "ttt", "ttttt",
        ],
    ),
    "Dyck language" => Dict(
        "included_examples" => [
            "",
            "()",
            "(())", "()()",
            "((()))", "(()())", "(())()", "()(())", "()()()",
            "(((())))", "((()()))", "((())())", "(()(()))", "(()()())", "((()))()", "()((()))", "(()())()", "()(()())", "()(())()", "(())()()", "()()(())", "()()()()",
        ],
        "excluded_examples" => [
            "(", ")",
            ")(", "((", "))",
            ")))", "))(", ")()", ")((", "())", "()(", "(()", "(((",
        ],
    ),
)

const strong_ll_1_parser_data = Dict(  # https://mdaines.github.io/grammophone
    "set containing only the empty string" => [
        (;
            start_symbol = 'A',
            table = ParsingTableDefault{Char}(
            ),
            table_end_marker = ParsingTableDefaultEndMarker{Char}(
                'A' => [],
            ),
        ),
        (;
            start_symbol = 'A',
            table = ParsingTableDefault{Char}(
            ),
            table_end_marker = ParsingTableDefaultEndMarker{Char}(
                'A' => ['B'],
                'B' => []
            ),
        ),
    ],
    "set containing only the length-one string" => [
        (;
            start_symbol = 'A',
            table = ParsingTableDefault{Char}(
                ('A', 't') => ['t'],
            ),
            table_end_marker = ParsingTableDefaultEndMarker{Char}(
            ),
        ),
        (;
            start_symbol = 'A',
            table = ParsingTableDefault{Char}(
                ('A', 't') => ['B'],
                ('B', 't') => ['t'],
            ),
            table_end_marker = ParsingTableDefaultEndMarker{Char}(
            ),
        ),
    ],
    "set of nonempty strings" => [
        (;
            start_symbol = 'A',
            table = ParsingTableDefault{Char}(
                ('A', 't') => ['t', 'B'],
                ('B', 't') => ['t', 'B'],
            ),
            table_end_marker = ParsingTableDefaultEndMarker{Char}(
                'B' => [],
            ),
        ),
    ],
    "set of strings of even length" => [
        (;
            start_symbol = 'A',
            table = ParsingTableDefault{Char}(
                ('A', 't') => ['t', 't', 'A'],
            ),
            table_end_marker = ParsingTableDefaultEndMarker{Char}(
                'A' => [],
            ),
        ),
        (;
            start_symbol = 'A',
            table = ParsingTableDefault{Char}(
                ('A', 't') => ['B'],
                ('B', 't') => ['t', 't', 'A'],
            ),
            table_end_marker = ParsingTableDefaultEndMarker{Char}(
                'A' => [],
            ),
        ),
        (;
            start_symbol = 'A',
            table = ParsingTableDefault{Char}(
                ('A', 't') => ['B'],
                ('B', 't') => ['t', 't', 'B'],
            ),
            table_end_marker = ParsingTableDefaultEndMarker{Char}(
                'A' => ['B'],
                'B' => []
            ),
        ),
    ],
    "Dyck language" => [
        (;
            start_symbol = 'A',
            table = ParsingTableDefault{Char}(
                ('A', '(') => ['(', 'A', ')', 'A'],
                ('A', ')') => [],
            ),
            table_end_marker = ParsingTableDefaultEndMarker{Char}(
                'A' => [],
            ),
        ),
        (;
            start_symbol = 'A',
            table = ParsingTableDefault{Char}(
                ('B', '(') => ['(', 'A', ')', 'A'],
                ('A', '(') => ['B'],
                ('A', ')') => [],
            ),
            table_end_marker = ParsingTableDefaultEndMarker{Char}(
                'A' => [],
            ),
        ),
        (;
            start_symbol = 'A',
            table = ParsingTableDefault{Char}(
                ('B', '(') => ['(', 'B', ')', 'B'],
                ('A', '(') => ['B'],
                ('B', ')') => [],
            ),
            table_end_marker = ParsingTableDefaultEndMarker{Char}(
                'A' => ['B'],
                'B' => [],
            ),
        ),
    ],
)

@testset "`SymbolGraphs`" begin
    @testset "basic" begin
        @test (@inferred SymbolGraphNodeIdentity()) isa SymbolGraphNodeIdentity
        @test @inferred SymbolGraphNodeIdentity() != SymbolGraphNodeIdentity()
        @test (@inferred make_node_vec()) isa AbstractVector{SymbolGraphNodeIdentity}
        @test (@inferred make_node_vec(SymbolGraphNodeIdentity())) isa AbstractVector{SymbolGraphNodeIdentity}
        @test make_node_vec() === make_node_vec()
        @test (@inferred SymbolGraphRootless{Int, String}()) isa SymbolGraphRootless{Int, String}
        @test let graph = SymbolGraphRootless{Int, String}(), root = SymbolGraphNodeIdentity()
            (@inferred SymbolGraphRooted(root, graph)) isa SymbolGraphRooted{Int, String}
        end
        @test let graph = SymbolGraphRootless{Int, String}(), root = SymbolGraphNodeIdentity()
            graph.node_to_grammar_symbol_kind[root] = 3
            rooted = SymbolGraphRooted(root, graph)
            3 === @inferred root_symbol_kind(rooted)
        end
        @test let graph = SymbolGraphRootless{Int, String}()
            root = new_terminal_symbol!(graph.node_to_grammar_symbol_kind, graph.terminal_node_to_token, 3, "three")
            rooted = SymbolGraphRooted(root, graph)
            "three" == (@inferred root_token(rooted))::String
        end
        @test let graph = SymbolGraphRootless{Int, String}()
            root = new_terminal_symbol!(graph.node_to_grammar_symbol_kind, graph.terminal_node_to_token, 3, "three")
            rooted = SymbolGraphRooted(root, graph)
            isempty(collect(Any, @inferred root_children(rooted)))
        end
        @test let graph = SymbolGraphRootless{Int, String}()
            root = new_terminal_symbol!(graph.node_to_grammar_symbol_kind, graph.terminal_node_to_token, 3, "three")
            rooted = SymbolGraphRooted(root, graph)
            @inferred root_is_terminal(rooted)
        end
        @test let graph = SymbolGraphRootless{Int, String}()
            root = new_terminal_symbol!(graph.node_to_grammar_symbol_kind, graph.terminal_node_to_token, 3, "three")
            rooted = SymbolGraphRooted(root, graph)
            @inferred root_is_childless(rooted)
        end
    end
    @testset "parsing" begin
        function string_to_toks(s::String)
            function f(kind::Char)
                (nothing, kind)
            end
            Iterators.map(f, s)
        end
        for Debug ∈ (Union{}, Nothing)
            for language_key ∈ keys(languages)
                included = languages[language_key]["included_examples"]
                excluded = languages[language_key]["excluded_examples"]
                for parser_data ∈ strong_ll_1_parser_data[language_key]
                    parser = (@inferred StrongLL1TableDrivenParser{Debug, Nothing}(parser_data.start_symbol, parser_data.table, parser_data.table_end_marker))::StrongLL1TableDrivenParser{Debug, Nothing}
                    @test (@inferred SymbolGraphs.parse(parser, string_to_toks(first(included)))) isa Tuple{SymbolGraphRooted{Char, Nothing}, Optional{Tuple{SymbolGraphNodeIdentity, Optional{Tuple{Nothing, Char}}}}}
                    for s ∈ included  # parse-unparse
                        @test let (tree, _) = SymbolGraphs.parse(parser, string_to_toks(s))
                            function f(io::IO)
                                function g(::Any, kind::Char)
                                    print(io, kind)
                                end
                                SymbolGraphs.unparse(g, tree)
                            end
                            s == (@inferred sprint(f))::AbstractString
                        end
                    end
                    for s ∈ included
                        @test isempty(SymbolGraphs.parse(parser, string_to_toks(s))[2])
                    end
                    for s ∈ excluded
                        @test !isempty(SymbolGraphs.parse(parser, string_to_toks(s))[2])
                    end
                end
            end
        end
    end
end
