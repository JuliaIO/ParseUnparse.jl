module TestOptionals
    include("runtests_optionals.jl")
end

module TestContextFreeGrammarUtil
    include("runtests_context_free_grammar_util.jl")
end

module TestSymbolGraphs
    include("runtests_symbol_graphs.jl")
end

module TestImplementAbstractTrees
    include("runtests_implement_abstract_trees.jl")
end

module TestAbstractParserIdents
    include("runtests_abstract_parser_idents.jl")
end

module TestKindConstruction
    include("runtests_kind_construction.jl")
end

module TestLexingUtil
    include("runtests_lexing_util.jl")
end

module TestAqua
    include("runtests_aqua.jl")
end
