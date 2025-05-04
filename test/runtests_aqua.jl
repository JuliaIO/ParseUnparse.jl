using ParseUnparse
using Test
using Aqua: Aqua

@testset "Aqua.jl" begin
    Aqua.test_all(ParseUnparse)
end
