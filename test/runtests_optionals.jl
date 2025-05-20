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
    @test (@inferred convert(Optional, Float32[])) isa Optional{Float32}
    @test isempty(convert(Optional, Float32[]))
    @test Optional(3) === convert(Optional, [3])
    @test (@inferred convert(Optional{Float64}, Float32[])) isa Optional{Float64}
    @test isempty(convert(Optional{Float64}, Float32[]))
    @test Optional(3.0) === convert(Optional{Float64}, [3])
    @test_throws ArgumentError convert(Optional, [3, 7])
    @test_throws ArgumentError convert(Optional{Float64}, [3, 7])
end
