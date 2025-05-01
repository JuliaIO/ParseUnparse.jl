using ParseUnparse
using Test
using Aqua

@testset "ParseUnparse.jl" begin
    @testset "Code quality (Aqua.jl)" begin
        Aqua.test_all(ParseUnparse)
    end
    # Write your tests here.
end
