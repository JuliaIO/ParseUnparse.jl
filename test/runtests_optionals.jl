using ParseUnparse.Optionals
using Test

@testset "`Optionals`" begin
    @test Optional <: AbstractVector
    @test Optional{String} <: AbstractVector{String}
    @test Optional{Int} <: AbstractVector{Int}
    @test (@inferred Optional{Int}()) isa Optional{Int}
    @test (@inferred Optional{Integer}()) isa Optional{Integer}
    @test (@inferred Optional(3)) isa Optional{Int}
    @test [] == (@inferred Optional{Int}()) == @inferred Optional{Float32}()
    @test [3] == (@inferred Optional(3)) == @inferred Optional(3.0)
    @test @inferred isempty(Optional{Float32}())
    @test !(@inferred isempty(Optional(3)))
    @test iszero(@inferred length(Optional{Float32}()))
    @test isone(@inferred length(Optional(3)))
    @test (@inferred Optional{Float32}(3)) isa Optional{Float32}
    @test [] == collect(Int, Optional{Number}())
    @test [3] == collect(Float32, Optional(3))
    @test_throws BoundsError Optional(3.0)[2]
    @test_throws BoundsError Optional{Int}()[1]
end
