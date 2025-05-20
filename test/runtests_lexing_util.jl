using ParseUnparse.LexingUtil
using Test

@testset "`LexingUtil`" begin
    @test let extra = nothing, t = token_iterator_state_init(Char, extra)
        !t.is_done
    end
    @test let extra = nothing, t = token_iterator_state_init(Char, extra)
        extra === t.extra
    end
    @test let extra = nothing, t = token_iterator_state_init(Char, extra)
        () === lexer_state_new(t.opaque, extra, "")
    end
    @test let extra = nothing, t = token_iterator_state_init(Char, extra)
        ls = only(lexer_state_new(t.opaque, extra, "a"))
        'a' === only(@inferred lexer_state_peek!(ls))
    end
    @test let extra = nothing, t = token_iterator_state_init(Char, extra)
        ls = only(lexer_state_new(t.opaque, extra, "a"))
        a = only(lexer_state_peek!(ls))
        a === only(@inferred lexer_state_consume!(ls))
    end
    @test let extra = nothing, t = token_iterator_state_init(Char, extra)
        ls = only(lexer_state_new(t.opaque, extra, "a"))
        lexer_state_consume!(ls)
        isempty(lexer_state_consume!(ls))
    end
    @test let extra = nothing, t = token_iterator_state_init(Char, extra)
        ls = only(lexer_state_new(t.opaque, extra, "a"))
        des = lexer_state_destroy!(ls)
        "" == String(des.token_source)
    end
    @test let extra = nothing, t = token_iterator_state_init(Char, extra)
        it = "ab"
        ls1 = only(lexer_state_new(t.opaque, extra, it))
        des = lexer_state_destroy!(ls1)
        ls2 = only(lexer_state_new(des.opaque, lexer_state_get_extra(ls1), it))
        lexer_state_consume!(ls2)
        'b' === only(@inferred lexer_state_consume!(ls2))
    end
    @test let extra = nothing, t = token_iterator_state_init(Char, extra)
        ls = only(lexer_state_new(t.opaque, extra, "a"))
        Int64(0) === @inferred lexer_state_get_consumed_character_count(ls)
    end
    @test let extra = nothing, t = token_iterator_state_init(Char, extra)
        ls = only(lexer_state_new(t.opaque, extra, "a"))
        lexer_state_consume!(ls)
        Int64(1) === @inferred lexer_state_get_consumed_character_count(ls)
    end
    @test () === lexer_state_simple_new("")
    @test let (ls,) = lexer_state_simple_new("a")
        'a' === only(@inferred lexer_state_peek!(ls))
    end
end
