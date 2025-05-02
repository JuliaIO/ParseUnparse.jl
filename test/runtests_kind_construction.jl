using ParseUnparse.KindConstruction
using Test

@testset "`KindConstruction`" begin
    @test_throws ArgumentError let construct = Returns(7)
        kind_to_name = Dict{Int, String}()
        name_to_kind = Dict{String, Int}()
        construct_kind!(construct, kind_to_name, name_to_kind, "")
    end
    @test let construct = Returns(7)
        kind_to_name = Dict{Int, String}()
        name_to_kind = Dict{String, Int}()
        a = 7 === @inferred construct_kind!(construct, kind_to_name, name_to_kind, "seven")
        b = (7 => "seven") == only(kind_to_name)
        c = ("seven" => 7) == only(name_to_kind)
        a && b && c
    end
    @test_throws ArgumentError let construct = Returns(7)
        kind_to_name = Dict{Int, String}()
        name_to_kind = Dict{String, Int}()
        construct_kind!(construct, kind_to_name, name_to_kind, "seven")
        construct_kind!(construct, kind_to_name, name_to_kind, "seven")
    end
end
