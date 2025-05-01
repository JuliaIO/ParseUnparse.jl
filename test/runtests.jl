using ParseUnparse
using Test
using Aqua: Aqua

@testset "ParseUnparse.jl" begin
    @testset "Code quality (Aqua.jl)" begin
        Aqua.test_all(ParseUnparse)
    end
end

module TestOptionals
    include("runtests_optionals.jl")
end

module TestSymbolGraphs
    include("runtests_symbol_graphs.jl")
end
