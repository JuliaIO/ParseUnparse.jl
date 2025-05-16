# ParseUnparse

[![Build Status](https://github.com/nsajko/ParseUnparse.jl/actions/workflows/CI.yml/badge.svg?branch=main)](https://github.com/nsajko/ParseUnparse.jl/actions/workflows/CI.yml?query=branch%3Amain)
[![Package version](https://juliahub.com/docs/General/ParseUnparse/stable/version.svg)](https://juliahub.com/ui/Packages/General/ParseUnparse)
[![Package dependencies](https://juliahub.com/docs/General/ParseUnparse/stable/deps.svg)](https://juliahub.com/ui/Packages/General/ParseUnparse?t=2)
[![Coverage](https://codecov.io/gh/nsajko/ParseUnparse.jl/branch/main/graph/badge.svg)](https://codecov.io/gh/nsajko/ParseUnparse.jl)
[![PkgEval](https://JuliaCI.github.io/NanosoldierReports/pkgeval_badges/P/ParseUnparse.svg)](https://JuliaCI.github.io/NanosoldierReports/pkgeval_badges/P/ParseUnparse.html)
[![Aqua](https://raw.githubusercontent.com/JuliaTesting/Aqua.jl/master/badge.svg)](https://github.com/JuliaTesting/Aqua.jl)

Given a context-free grammar, parse input data to get a parse tree. Supports unparsing, with perfect roundtripping, depending on the implementation for the specific format.

Some dependent packages:

* Implementations for specific format:

    * JSON: [ParseUnparseJSON](https://github.com/nsajko/ParseUnparseJSON.jl)

    * WKT-CRS: [ParseUnparseWKTCRS](https://github.com/nsajko/ParseUnparseWKTCRS.jl)
