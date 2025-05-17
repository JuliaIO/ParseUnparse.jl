# ParseUnparse

[![Build Status](https://github.com/JuliaIO/ParseUnparse.jl/actions/workflows/CI.yml/badge.svg?branch=main)](https://github.com/JuliaIO/ParseUnparse.jl/actions/workflows/CI.yml?query=branch%3Amain)
[![Coverage](https://codecov.io/gh/JuliaIO/ParseUnparse.jl/branch/main/graph/badge.svg)](https://codecov.io/gh/JuliaIO/ParseUnparse.jl)
[![Package version](https://juliahub.com/docs/General/ParseUnparse/stable/version.svg)](https://juliahub.com/ui/Packages/General/ParseUnparse)
[![Package dependencies](https://juliahub.com/docs/General/ParseUnparse/stable/deps.svg)](https://juliahub.com/ui/Packages/General/ParseUnparse?t=2)
[![PkgEval](https://JuliaCI.github.io/NanosoldierReports/pkgeval_badges/P/ParseUnparse.svg)](https://JuliaCI.github.io/NanosoldierReports/pkgeval_badges/P/ParseUnparse.html)
[![Aqua](https://raw.githubusercontent.com/JuliaTesting/Aqua.jl/master/badge.svg)](https://github.com/JuliaTesting/Aqua.jl)

Given a context-free grammar, parse input data to get a parse tree. Supports unparsing, with perfect roundtripping, depending on the implementation for the specific format.

The parse tree type implements the [AbstractTrees](https://github.com/JuliaCollections/AbstractTrees.jl) interface.

Some dependent packages:

* Implementations for specific formats:

    * JSON: [ParseUnparseJSON](https://github.com/JuliaIO/ParseUnparseJSON.jl)

    * WKT-CRS: [ParseUnparseWKTCRS](https://github.com/JuliaIO/ParseUnparseWKTCRS.jl)

## Usage example: a parser for the *Dyck language*

The *Dyck language* is the set of balanced strings of parentheses. Example words in the Dyck language: `()`, `(())`, `()()`, `()(())`. Here's how to get a parser for the Dyck language:

```julia
using ParseUnparse.ContextFreeGrammarUtil
using ParseUnparse.SymbolGraphs
using ParseUnparse.AbstractParserIdents

struct DyckParserId <: AbstractParserIdent end  # necessary so the Dyck language could be dispatched on

function AbstractParserIdents.get_lexer(::DyckParserId)  # trivial tokenizer
    function lexer(iterator)
        function f(c::Char)
            (nothing, c)  # `c` is the grammar symbol kind in this case
        end
        Iterators.map(f, iterator)
    end
end

function AbstractParserIdents.get_token_grammar(::DyckParserId)  # an LL(1) grammar for the Dyck language, with a single nonterminal and two production rules
    start_symbol = 'S'
    rules = (
        ('S' => Set(([], ['(', 'S', ')', 'S']))),
    )
    (start_symbol, Dict{Char, Set{Vector{Char}}}(rules))
end

function AbstractParserIdents.get_token_parser(id::DyckParserId)  # strong-LL(1) parser
    (start_symbol, grammar) = get_token_grammar(id)
    tables = make_parsing_table_strong_ll_1(grammar, start_symbol)
    NoDebug = Nothing  # disable debugging
    Token = Nothing  # our tokenizer is trivial
    StrongLL1TableDrivenParser{NoDebug, Token}(start_symbol, tables...)
end
```

While this simple example uses a trivial lexer/tokenizer, in practice the lexer would:

* Do actual tokenization, coalescing certain input symbols into tokens (terminal symbols of the grammar).

* Include source/debugging info, such as on the position of the token within the complete input source.

Regarding the expression `'S' => Set(([], ['(', 'S', ')', 'S']))` above, it defines the production rules of our context-free grammar for the Dyck language. Try the same grammar out in Grammophone, a grammar playground on the Web:

* https://mdaines.github.io/grammophone/?s=UyAtPiB8IGxlZnQgUyByaWdodCBTIC4=

The input in this case is an iterator with `Char` elements. Such as a `String`. Try the parser out in the REPL:

```julia-repl
julia> parser = get_parser(DyckParserId());

julia> (tree, error_status) = parser("");

julia> isempty(error_status)  # the parser accepts the empty string
true

julia> (tree, error_status) = parser("())");

julia> isempty(error_status)  # the parser rejects the unbalanced string
false

julia> using AbstractTrees: print_tree  # let's see the parse tree!

julia> function print_tree_map(io::IO, tree)
           kind = root_symbol_kind(tree)
           if root_is_terminal(tree)
               show(io, (kind, root_token(tree)))  # a terminal symbol may have extra info (although it's just `nothing` in this example)
           else
               show(io, kind)  # a nonterminal symbol just has its symbol kind
           end
       end
print_tree_map (generic function with 1 method)

julia> print_tree(print_tree_map, stdout, parser("(()())")[1]; maxdepth = 100)
'S'
├─ ('(', nothing)
├─ 'S'
│  ├─ ('(', nothing)
│  ├─ 'S'
│  ├─ (')', nothing)
│  └─ 'S'
│     ├─ ('(', nothing)
│     ├─ 'S'
│     ├─ (')', nothing)
│     └─ 'S'
├─ (')', nothing)
└─ 'S'
```
