using ParseUnparse
using ParseUnparse.Common.ContextFreeGrammarUtil
using Test

@testset "`ContextFreeGrammarUtil`" begin
    @testset "trivial" begin
        empty_language_grammar_clean = Dict{Char, Set{Vector{Char}}}()
        empty_language_grammar_loop = Dict{Char, Set{Vector{Char}}}(('S' => Set((['S'],)),))
        empty_language_grammar_unreachable = Dict{Char, Set{Vector{Char}}}(('A' => Set((['0'],)),))
        singleton_language_grammar_clean = Dict{Char, Set{Vector{Char}}}(('S' => Set((['0'],)),))
        singleton_language_grammar_unreachable = Dict{Char, Set{Vector{Char}}}(('S' => Set((['0'],)), 'A' => Set((['0'],))))
        even_paired_language_grammar_clean = Dict{Char, Set{Vector{Char}}}(('S' => Set(([], ['0', 'S', '1'])),))
        empty_language_tables = (Dict{Tuple{Char, Char}, Vector{Char}}(), Dict{Char, Vector{Char}}())
        singleton_language_tables = (Dict{Tuple{Char, Char}, Vector{Char}}((('S', '0') => ['0'],)), Dict{Char, Vector{Char}}())
        even_paired_language_tables = (Dict{Tuple{Char, Char}, Vector{Char}}(((('S', '0') => ['0', 'S', '1']), (('S', '1') => []))), Dict{Char, Vector{Char}}((('S' => []),)))
        @test empty_language_grammar_clean == @inferred cleaned_up_grammar_copy(empty_language_grammar_clean, 'S')
        @test empty_language_grammar_clean == @inferred cleaned_up_grammar_copy(empty_language_grammar_loop, 'S')
        @test empty_language_grammar_clean == @inferred cleaned_up_grammar_copy(empty_language_grammar_unreachable, 'S')
        @test singleton_language_grammar_clean == @inferred cleaned_up_grammar_copy(singleton_language_grammar_clean, 'S')
        @test singleton_language_grammar_clean == @inferred cleaned_up_grammar_copy(singleton_language_grammar_unreachable, 'S')
        @test even_paired_language_grammar_clean == @inferred cleaned_up_grammar_copy(even_paired_language_grammar_clean, 'S')
        @test singleton_language_grammar_unreachable == @inferred copy_with_deduplicated_rules_identity(singleton_language_grammar_unreachable)
        @test let dedup = copy_with_deduplicated_rules_identity(singleton_language_grammar_unreachable)
            (a, b) = Iterators.map(only, values(dedup))
            a::AbstractVector{Char} === b::AbstractVector{Char}
        end
        @test isempty(@inferred first_sets(empty_language_grammar_clean))
        @test Set((['0'],)) == only(values(@inferred first_sets(singleton_language_grammar_clean)))
        @test Set((['0'], [])) == only(values(@inferred first_sets(even_paired_language_grammar_clean)))
        @test let fir = first_sets(empty_language_grammar_clean)
            all(isempty, values(@inferred follow_sets(empty_language_grammar_clean, fir)))
        end
        @test let fir = first_sets(singleton_language_grammar_clean)
            all(isempty, values(@inferred follow_sets(singleton_language_grammar_clean, fir)))
        end
        @test let fir = first_sets(even_paired_language_grammar_clean)
            Set(('1',)) == only(values(@inferred follow_sets(even_paired_language_grammar_clean, fir)))
        end
        @test let fir = first_sets(empty_language_grammar_clean)
            isempty(@inferred endable_set(empty_language_grammar_clean, fir, 'S'))
        end
        @test let fir = first_sets(singleton_language_grammar_clean)
            'S' === only(@inferred endable_set(singleton_language_grammar_clean, fir, 'S'))
        end
        @test let fir = first_sets(even_paired_language_grammar_clean)
            'S' === only(@inferred endable_set(even_paired_language_grammar_clean, fir, 'S'))
        end
        @test empty_language_tables == @inferred make_parsing_table_strong_ll_1(empty_language_grammar_clean, 'S')
        @test empty_language_tables == @inferred make_parsing_table_strong_ll_1(empty_language_grammar_loop, 'S')
        @test empty_language_tables == @inferred make_parsing_table_strong_ll_1(empty_language_grammar_unreachable, 'S')
        @test singleton_language_tables == @inferred make_parsing_table_strong_ll_1(singleton_language_grammar_clean, 'S')
        @test singleton_language_tables == @inferred make_parsing_table_strong_ll_1(singleton_language_grammar_unreachable, 'S')
        @test even_paired_language_tables == @inferred make_parsing_table_strong_ll_1(even_paired_language_grammar_clean, 'S')
    end
end
