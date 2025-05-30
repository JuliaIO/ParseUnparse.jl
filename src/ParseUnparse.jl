module ParseUnparse
    export ContextFreeGrammarUtil, SymbolGraphs, AbstractParserIdents, KindConstruction, LexingUtil
    module Optionals
        export Optional
        struct Optional{P} <: AbstractVector{P}
            defined::Bool
            v::P
            function Optional{P}() where {P}
                new{P}(false)
            end
            function Optional{P}(v) where {P}
                new{P}(true, v)
            end
        end
        function Optional(v)
            Optional{typeof(v)}(v)
        end
        function is_not_empty(o::Optional)
            getfield(o, 1)
        end
        function Base.isempty(o::Optional)
            !is_not_empty(o)
        end
        function Base.size(o::Optional)
            len = Int(is_not_empty(o))
            (len,)
        end
        function Base.IndexStyle(::Type{<:Optional})
            IndexLinear()
        end
        function Base.getindex(o::Optional, i::Integer)
            if isempty(o) || !isone(i)
                throw(BoundsError(o, i))
            end
            getfield(o, 2)
        end
        function Base.iterate(o::Optional)
            if is_not_empty(o)
                (o[1], nothing)
            else
                nothing
            end
        end
        function Base.iterate(::Optional, ::Any)
            nothing
        end
        function convert_from_other_vector_eltype(::Type{Optional{T}}, ::Type) where {T}
            T
        end
        function convert_from_other_vector_eltype(::Type{Optional}, ::Type{T}) where {T}
            T
        end
        function convert_from_other_vector(::Type{O}, vec::AbstractVector) where {O <: Optional}
            if 1 < length(vec)
                throw(ArgumentError("got vector with more than one element, too long"))
            end
            T = convert_from_other_vector_eltype(O, eltype(vec))
            Op = Optional{T}
            if isempty(vec)
                Op()
            else
                Op(only(vec))
            end
        end
        function Base.convert(::Type{Optional{T}}, vec::AbstractVector) where {T}
            convert_from_other_vector(Optional{T}, vec)
        end
        function Base.convert(::Type{Optional}, vec::AbstractVector)
            convert_from_other_vector(Optional, vec)
        end
    end
    """
        ContextFreeGrammarUtil::Module

    Functionality for analysing context-free grammars (CFG), and creating parsing tables from grammars.
    """
    module ContextFreeGrammarUtil
        export
            cleaned_up_grammar_copy,
            first_sets, follow_sets, endable_set,
            make_parsing_table_strong_ll_1
        using ..Optionals
        """
            ContextFreeGrammar::Type{<:AbstractDict}

        CFG productions.
        """
        const ContextFreeGrammar = AbstractDict{
            GrammarSymbolKind,  # left-hand side of a grammar rule: nonterminal symbol
            RightHandSides,  # the right-hand sides corresponding to the left-hand side
        } where {
            GrammarSymbolKind,
            RightHandSides <: AbstractSet{<:AbstractVector{GrammarSymbolKind}},
        }
        const CFGFollowSets = AbstractDict{
            GrammarSymbolKind,  # nonterminal symbol
            FollowSet,  # terminal symbols
        } where {
            GrammarSymbolKind,
            FollowSet <: AbstractSet{GrammarSymbolKind},
        }
        const CFGFirstSets = AbstractDict{
            GrammarSymbolKind,  # nonterminal symbol
            FirstSet,  # strings of terminal symbols of length less than or equal to one
        } where {
            GrammarSymbolKind,
            FirstSet <: AbstractSet{Optional{GrammarSymbolKind}},
        }
        const Vec = (@isdefined Memory) ? Memory : Vector  # performance optimization: use `Memory` when available!
        function copy_with_only_productive_rules!(
            dst::ContextFreeGrammar{GrammarSymbolKind},
            src::ContextFreeGrammar{GrammarSymbolKind},
        ) where {GrammarSymbolKind}
            modified = false
            nonterminal_symbols = keys(src)
            function is_immediately_productive(sym::GrammarSymbolKind)
                is_terminal = sym ∉ nonterminal_symbols
                is_terminal || sym ∈ keys(dst)
            end
            # Mark as productive each rule all of whose RHS members are productive.
            for nonterminal ∈ nonterminal_symbols
                for sentential_form ∈ src[nonterminal]
                    if all(is_immediately_productive, sentential_form)
                        # this rule is productive
                        if nonterminal ∉ keys(dst)
                            dst[nonterminal] = Set{Vec{GrammarSymbolKind}}()
                        end
                        let rules = dst[nonterminal]
                            if sentential_form ∉ rules
                                push!(rules, sentential_form)
                                modified = true
                            end
                        end
                    end
                end
            end
            modified
        end
        function copy_with_only_productive_rules(grammar::ContextFreeGrammar{GrammarSymbolKind}) where {GrammarSymbolKind}
            # Everything except terminal symbols and ϵ-rules is initially assumed to be nonproductive.
            ret = Dict{GrammarSymbolKind, Set{Vec{GrammarSymbolKind}}}()
            while copy_with_only_productive_rules!(ret, grammar) end
            ret
        end
        function copy_with_only_reachable_nonterminals!(
            reachable_nonterminals::AbstractSet{GrammarSymbolKind},
            grammar::ContextFreeGrammar{GrammarSymbolKind},
        ) where {GrammarSymbolKind}
            reachable_nonterminals_next = copy(reachable_nonterminals)
            nonterminal_symbols = keys(grammar)
            # Mark as reachable each nonterminal appearing on the RHS of a rule where the LHS is reachable.
            for reachable_nonterminal ∈ reachable_nonterminals
                for sentential_form ∈ grammar[reachable_nonterminal]
                    for sym ∈ sentential_form
                        if sym ∈ nonterminal_symbols
                            push!(reachable_nonterminals_next, sym)
                        end
                    end
                end
            end
            modified = reachable_nonterminals != reachable_nonterminals_next
            union!(reachable_nonterminals, reachable_nonterminals_next)
            modified
        end
        function copy_with_only_reachable_nonterminals(
            grammar::ContextFreeGrammar{GrammarSymbolKind},
            start_symbol::GrammarSymbolKind,
        ) where {GrammarSymbolKind}
            reachable_nonterminals = Set{GrammarSymbolKind}()
            nonterminal_symbols = keys(grammar)
            if start_symbol ∈ nonterminal_symbols
                # Start by marking the start symbol as reachable. All other symbols are initially assumed to be unreachable.
                push!(reachable_nonterminals, start_symbol)
                while copy_with_only_reachable_nonterminals!(reachable_nonterminals, grammar) end
            end
            ret = Dict{GrammarSymbolKind, Set{Vec{GrammarSymbolKind}}}()
            function f(sym::GrammarSymbolKind)
                ret[sym] = copy(grammar[sym])
            end
            foreach(f, reachable_nonterminals)
            ret
        end
        """
            cleaned_up_grammar_copy(grammar, start_symbol)

        Return a cleaned-up copy of the given CFG, where all nonterminals are reachable from the start symbol and all rules are productive.
        """
        function cleaned_up_grammar_copy(
            grammar::ContextFreeGrammar{GrammarSymbolKind},
            start_symbol::GrammarSymbolKind,
        ) where {GrammarSymbolKind}
            copy_with_only_reachable_nonterminals(copy_with_only_productive_rules(grammar), start_symbol)
        end
        """
            copy_with_deduplicated_rules_identity(grammar)

        Return a copy of the given grammar with some deduplication. Meant as a performance optimization, to decrease memory usage and improve cache locality.
        """
        function copy_with_deduplicated_rules_identity(grammar::ContextFreeGrammar{GrammarSymbolKind}) where {GrammarSymbolKind}
            right_hand_sides = Dict{Vec{GrammarSymbolKind}, Nothing}()  # https://discourse.julialang.org/t/get-an-equal-element-of-a-set-get-an-equal-key-of-a-dictionary/128779
            for (_, rules) ∈ grammar
                for rhs ∈ rules
                    right_hand_sides[copy(rhs)] = nothing
                end
            end
            ret = Dict{GrammarSymbolKind, Set{Vec{GrammarSymbolKind}}}()
            nonterminal_symbols = keys(grammar)
            function ini(sym::GrammarSymbolKind)
                ret[sym] = Set{Vec{GrammarSymbolKind}}()
            end
            foreach(ini, nonterminal_symbols)
            for (lhs, rules) ∈ grammar
                for rhs ∈ rules
                    dedup = getkey(right_hand_sides, rhs, nothing)
                    push!(ret[lhs], dedup)
                end
            end
            ret
        end
        function first_set(
            firsts::CFGFirstSets{GrammarSymbolKind},
            sentential_form::AbstractVector{GrammarSymbolKind},
        ) where {GrammarSymbolKind}
            nonterminal_symbols = keys(firsts)
            ϵ = Optional{GrammarSymbolKind}()
            ret = push!(Set{Optional{GrammarSymbolKind}}(), ϵ)
            for sym ∈ sentential_form
                if ϵ ∉ ret
                    break
                end
                delete!(ret, ϵ)
                if sym ∈ nonterminal_symbols
                    # `sym` is not terminal
                    union!(ret, firsts[sym])
                else
                    # `sym` is terminal
                    push!(ret, Optional{GrammarSymbolKind}(sym))
                end
            end
            ret
        end
        function first_sets!(
            firsts::CFGFirstSets{GrammarSymbolKind},
            rule::AbstractVector{GrammarSymbolKind},  # RHS
            nonterminal_symbol::GrammarSymbolKind,    # LHS
        ) where {GrammarSymbolKind}
            fir = firsts[nonterminal_symbol]
            fir_next = first_set(firsts, rule)
            modified = fir_next ⊈ fir
            union!(fir, fir_next)
            modified
        end
        function first_sets!(
            firsts::CFGFirstSets{GrammarSymbolKind},
            grammar::ContextFreeGrammar{GrammarSymbolKind},
            nonterminal_symbol::GrammarSymbolKind,
        ) where {GrammarSymbolKind}
            modified = false
            sentential_forms = grammar[nonterminal_symbol]
            for rule ∈ sentential_forms
                modified |= first_sets!(firsts, rule, nonterminal_symbol)
            end
            modified
        end
        function first_sets!(
            firsts::CFGFirstSets{GrammarSymbolKind},
            grammar::ContextFreeGrammar{GrammarSymbolKind},
        ) where {GrammarSymbolKind}
            modified = false
            nonterminal_symbols = keys(grammar)
            for nonterminal ∈ nonterminal_symbols
                modified |= first_sets!(firsts, grammar, nonterminal)
            end
            modified
        end
        function first_sets(grammar::ContextFreeGrammar{GrammarSymbolKind}) where {GrammarSymbolKind}
            ret = Dict{GrammarSymbolKind, Set{Optional{GrammarSymbolKind}}}()
            function ini(sym::GrammarSymbolKind)
                ret[sym] = Set{Optional{GrammarSymbolKind}}()
            end
            nonterminal_symbols = keys(grammar)
            # Start by initializing the sets as empty.
            foreach(ini, nonterminal_symbols)
            while first_sets!(ret, grammar) end
            ret
        end
        function endable_set!(
            endables::AbstractSet{GrammarSymbolKind},
            grammar::ContextFreeGrammar{GrammarSymbolKind},
            firsts::CFGFirstSets{GrammarSymbolKind},
        ) where {GrammarSymbolKind}
            endables_next = copy(endables)
            nonterminal_symbols = keys(grammar)
            ϵ = Optional{GrammarSymbolKind}()
            for endable ∈ endables
                for rule ∈ grammar[endable]
                    for sym ∈ Iterators.reverse(rule)
                        sym_is_nonterminal = sym ∈ nonterminal_symbols
                        if sym_is_nonterminal
                            push!(endables_next, sym)
                        end
                        is_nullable = sym_is_nonterminal && (ϵ ∈ firsts[sym])
                        if !is_nullable
                            break
                        end
                    end
                end
            end
            modified = endables != endables_next
            union!(endables, endables_next)
            modified
        end
        function endable_set(
            grammar::ContextFreeGrammar{GrammarSymbolKind},
            firsts::CFGFirstSets{GrammarSymbolKind},
            start_symbol::GrammarSymbolKind,
        ) where {GrammarSymbolKind}
            ret = Set{GrammarSymbolKind}()
            nonterminal_symbols = keys(grammar)
            if start_symbol ∈ nonterminal_symbols
                # Start by marking the start symbol as endable. All other symbols are initially assumed not to be endable.
                push!(ret, start_symbol)
                while endable_set!(ret, grammar, firsts) end
            end
            ret
        end
        function new_follow_sets(grammar::ContextFreeGrammar{GrammarSymbolKind}) where {GrammarSymbolKind}
            ret = Dict{GrammarSymbolKind, Set{GrammarSymbolKind}}()
            function ini(sym::GrammarSymbolKind)
                ret[sym] = Set{Optional{GrammarSymbolKind}}()
            end
            nonterminal_symbols = keys(grammar)
            # Start by initializing the sets as empty.
            foreach(ini, nonterminal_symbols)
            ret
        end
        function follow_sets!(
            follows::CFGFollowSets{GrammarSymbolKind},
            firsts::CFGFirstSets{GrammarSymbolKind},
            grammar::ContextFreeGrammar{GrammarSymbolKind},
        ) where {GrammarSymbolKind}
            follows_next = new_follow_sets(grammar)
            function ini(sym::GrammarSymbolKind)
                union!(follows_next[sym], follows[sym])
            end
            nonterminal_symbols = keys(grammar)
            # Start by copying the FOLLOW sets.
            foreach(ini, nonterminal_symbols)
            ϵ = Optional{GrammarSymbolKind}()
            for nonterminal_symbol ∈ nonterminal_symbols
                for rule ∈ grammar[nonterminal_symbol]
                    for i ∈ eachindex(rule)
                        sym = rule[i]
                        if sym ∈ nonterminal_symbols
                            let fol = follows_next[sym]
                                rest = @view rule[(i + 1):end]
                                fir = first_set(firsts, rest)
                                # add all terminal symbols from FIRST(rest) to FOLLOW(sym)
                                for s ∈ fir
                                    if !isempty(s)
                                        push!(fol, only(s))
                                    end
                                end
                                # if rest derives ϵ, add all symbols from FOLLOW(nonterminal_symbol) to FOLLOW(sym)
                                if ϵ ∈ fir
                                    union!(fol, follows_next[nonterminal_symbol])
                                end
                            end
                        end
                    end
                end
            end
            modified = follows != follows_next
            function upd(sym::GrammarSymbolKind)
                union!(follows[sym], follows_next[sym])
            end
            foreach(upd, nonterminal_symbols)
            modified
        end
        function follow_sets(
            grammar::ContextFreeGrammar{GrammarSymbolKind},
            firsts::CFGFirstSets{GrammarSymbolKind},
        ) where {GrammarSymbolKind}
            ret = new_follow_sets(grammar)
            while follow_sets!(ret, firsts, grammar) end
            ret
        end
        function make_parsing_table_strong_ll_1_impl_3(
            grammar::ContextFreeGrammar{GrammarSymbolKind},
            firsts::CFGFirstSets{GrammarSymbolKind},
            follows::CFGFollowSets{GrammarSymbolKind},
            endables::AbstractSet{GrammarSymbolKind},
        ) where {GrammarSymbolKind}
            table = Dict{Tuple{GrammarSymbolKind, GrammarSymbolKind}, Vec{GrammarSymbolKind}}()
            table_end_marker = Dict{GrammarSymbolKind, Vec{GrammarSymbolKind}}()
            function add_checked!(tab::AbstractDict, key, rhs::AbstractVector{GrammarSymbolKind})
                if haskey(tab, key) && (rhs !== tab[key])
                    throw(ArgumentError("conflict detected, grammar not LL(1)"))
                end
                tab[key] = rhs
            end
            function add_entry!(key::Tuple{GrammarSymbolKind, GrammarSymbolKind}, rhs::AbstractVector{GrammarSymbolKind})
                add_checked!(table, key, rhs)
            end
            function add_entry_end_marker!(key::GrammarSymbolKind, rhs::AbstractVector{GrammarSymbolKind})
                add_checked!(table_end_marker, key, rhs)
            end
            ϵ = Optional{GrammarSymbolKind}()
            for (lhs, rules) ∈ grammar
                fol = follows[lhs]
                lhs_is_endable = lhs ∈ endables
                for rhs ∈ rules
                    fir = first_set(firsts, rhs)
                    for s ∈ fir
                        if !isempty(s)
                            add_entry!((lhs, only(s)), rhs)
                        end
                    end
                    if ϵ ∈ fir
                        for sym ∈ fol
                            add_entry!((lhs, sym), rhs)
                        end
                        if lhs_is_endable
                            add_entry_end_marker!(lhs, rhs)
                        end
                    end
                end
            end
            (table, table_end_marker)
        end
        function make_parsing_table_strong_ll_1_impl_2(
            grammar::ContextFreeGrammar{GrammarSymbolKind},
            firsts::CFGFirstSets{GrammarSymbolKind},
            start_symbol::GrammarSymbolKind
        ) where {GrammarSymbolKind}
            fol = follow_sets(grammar, firsts)
            en = endable_set(grammar, firsts, start_symbol)
            make_parsing_table_strong_ll_1_impl_3(grammar, firsts, fol, en)
        end
        function make_parsing_table_strong_ll_1_impl_1(
            grammar::ContextFreeGrammar{GrammarSymbolKind},
            start_symbol::GrammarSymbolKind
        ) where {GrammarSymbolKind}
            fir = first_sets(grammar)
            make_parsing_table_strong_ll_1_impl_2(grammar, fir, start_symbol)
        end
        """
            make_parsing_table_strong_ll_1(grammar, start_symbol)

        Make a strong-LL(1) parsing table from an LL(1) grammar.
        """
        function make_parsing_table_strong_ll_1(
            grammar::ContextFreeGrammar{GrammarSymbolKind},
            start_symbol::GrammarSymbolKind
        ) where {GrammarSymbolKind}
            cleaned_grammar = copy_with_deduplicated_rules_identity(cleaned_up_grammar_copy(grammar, start_symbol))
            make_parsing_table_strong_ll_1_impl_1(cleaned_grammar, start_symbol)
        end
    end
    """
        SymbolGraphs::Module

    Parse-tree-related functionality.
    """
    module SymbolGraphs
        export
            parse, unparse,
            graph_as_tree,
            SymbolGraphNodeIdentity, make_node_vec,
            SymbolGraphRootless,
            SymbolGraphRooted,
            root_symbol_kind,
            root_is_terminal,
            root_is_childless,
            root_token,
            root_children,
            new_terminal_symbol!,
            StrongLL1TableDrivenParser,
            validate_symbol_graph
        using ..Optionals
        using AbstractTrees: AbstractTrees
        """
            SymbolGraphNodeIdentity()

        Return the identity of a new node of a symbol graph.
        """
        mutable struct SymbolGraphNodeIdentity end
        const Vec = ((@isdefined Memory) ? Memory : Vector){SymbolGraphNodeIdentity}  # performance optimization: use `Memory` when available!
        const empty_vector = Vec(undef, 0)  # used for allocation-free tree traversal and other optimizations
        function make_node_vec(elements::Vararg{SymbolGraphNodeIdentity})
            len = length(elements)
            if iszero(len)
                empty_vector
            else
                let vec = Vec(undef, len)
                    for i ∈ eachindex(elements)
                        vec[i] = elements[i]
                    end
                    vec
                end
            end::Vec
        end
        """
            SymbolGraphRootless{GrammarSymbolKind, Token}()::SymbolGraphRootless{GrammarSymbolKind, Token}

        Return a graph whose nodes are symbols of a context-free grammar.
        """
        struct SymbolGraphRootless{GrammarSymbolKind, Token}
            node_to_grammar_symbol_kind::Dict{SymbolGraphNodeIdentity, GrammarSymbolKind}
            nonterminal_node_to_children::Dict{SymbolGraphNodeIdentity, Vec}
            terminal_node_to_token::Dict{SymbolGraphNodeIdentity, Token}
            function SymbolGraphRootless{GrammarSymbolKind, Token}() where {GrammarSymbolKind, Token}
                kinds = Dict{SymbolGraphNodeIdentity, GrammarSymbolKind}()
                rules = Dict{SymbolGraphNodeIdentity, Vec}()
                tokens = Dict{SymbolGraphNodeIdentity, Token}()
                new{GrammarSymbolKind, Token}(kinds, rules, tokens)
            end
        end
        """
            SymbolGraphRooted(root::SymbolGraphNodeIdentity, graph::SymbolGraphRootless)::SymbolGraphRooted

        Return a graph whose nodes are symbols of a context-free grammar, with `root` as the root.

        Intended to be used as a parse tree or an abstract syntax tree.
        """
        struct SymbolGraphRooted{GrammarSymbolKind, Token}
            root::SymbolGraphNodeIdentity
            graph::SymbolGraphRootless{GrammarSymbolKind, Token}
            function SymbolGraphRooted(
                root::SymbolGraphNodeIdentity,
                graph::SymbolGraphRootless{GrammarSymbolKind, Token},
            ) where {GrammarSymbolKind, Token}
                new{GrammarSymbolKind, Token}(root, graph)
            end
        end
        """
            root_symbol_kind(::SymbolGraphRooted)

        Return the kind of the root node as a grammar symbol.
        """
        function root_symbol_kind(tree::SymbolGraphRooted)
            tree.graph.node_to_grammar_symbol_kind[tree.root]
        end
        """
            root_is_terminal(::SymbolGraphRooted)::Bool

        Predicate, tell if the (root) node of the parse tree is a terminal symbol.
        """
        function root_is_terminal(tree::SymbolGraphRooted)
            root = tree.root
            graph = tree.graph
            # invariant: `haskey(graph.terminal_node_to_token, root) === !haskey(graph.nonterminal_node_to_children, root)`
            haskey(graph.terminal_node_to_token, root)::Bool
        end
        """
            root_is_childless(::SymbolGraphRooted)::Bool

        Predicate, tell if the (root) node of the parse tree is a leaf node/childless.
        """
        function root_is_childless(tree::SymbolGraphRooted)
            root_is_terminal(tree) ||
                isempty(tree.graph.nonterminal_node_to_children[tree.root])
        end
        """
            root_token(::SymbolGraphRooted)

        Return the token of a terminal symbol.
        """
        function root_token(tree::SymbolGraphRooted)
            tree.graph.terminal_node_to_token[tree.root]
        end
        """
            root_children(::SymbolGraphRooted)

        Return an iterator of `SymbolGraphRooted` elements.
        """
        function root_children(tree::SymbolGraphRooted)
            graph = tree.graph
            grammar_rules = graph.nonterminal_node_to_children
            function f(root::SymbolGraphNodeIdentity)
                SymbolGraphRooted(root, graph)
            end
            children = if root_is_childless(tree)
                make_node_vec()
            else
                grammar_rules[tree.root]
            end
            Iterators.map(f, children)
        end
        """
            new_terminal_symbol!(kinds::Dict{SymbolGraphNodeIdentity}, tokens::Dict{SymbolGraphNodeIdentity}, kind, token)::SymbolGraphNodeIdentity

        Form a terminal symbol from `kind` and `token`, registering it with `kinds` and `tokens`, and returns the new symbol.
        """
        function new_terminal_symbol!(
            kinds::Dict{SymbolGraphNodeIdentity, GrammarSymbolKind},
            tokens::Dict{SymbolGraphNodeIdentity, Token},
            kind::GrammarSymbolKind,
            token::Token,
        ) where {GrammarSymbolKind, Token}
            terminal_symbol = SymbolGraphNodeIdentity()
            kinds[terminal_symbol] = kind
            tokens[terminal_symbol] = token
            terminal_symbol
        end
        """
            unparse(print_token, tree::SymbolGraphRooted)::Nothing

        Unparse `tree`, calling `print_token(token, kind)` for each token-kind pair corresponding to a terminal symbol.
        """
        function unparse(print_token::PrTok, tree::SymbolGraphRooted) where {PrTok}
            if root_is_terminal(tree)
                print_token(root_token(tree), root_symbol_kind(tree))
            else
                foreach(Base.Fix1(unparse, print_token), root_children(tree))
            end
            nothing
        end
        function validate_symbol_graph(tree::SymbolGraphRootless)
            kinds = tree.node_to_grammar_symbol_kind
            grammar_rules = tree.nonterminal_node_to_children
            tokens = tree.terminal_node_to_token
            symbols = keys(kinds)
            terminal_symbols = keys(tokens)
            nonterminal_symbols = keys(grammar_rules)
            if !isdisjoint(terminal_symbols, nonterminal_symbols)
                throw(ArgumentError("the set of terminal symbols and the set of nonterminal symbols should be disjoint"))
            end
            if symbols != union(terminal_symbols, nonterminal_symbols)
                throw(ArgumentError("the union of the set of terminal symbols and the set of nonterminal symbols should be equal to the set of all symbols"))
            end
            # TODO: check that the symbol graph is weakly connected
            # TODO: check that the symbol graph is a tree, or at least acyclic
            tree
        end
        """
            validate_symbol_graph(::SymbolGraphRooted)::SymbolGraphRooted

        Throw if the input is malformed, otherwise return the input unchanged.
        """
        function validate_symbol_graph(tree::SymbolGraphRooted)
            graph = validate_symbol_graph(tree.graph)
            # TODO: check that each symbol graph node (symbol) is reachable from the root
            SymbolGraphRooted(tree.root, graph)
        end
        """
            StrongLL1TableDrivenParser{Debug, Token}(
                start_symbol_kind::GrammarSymbolKind,
                table::AbstractDict{Tuple{GrammarSymbolKind, GrammarSymbolKind}, <:AbstractVector{GrammarSymbolKind}},
                table_end_marker::AbstractDict{GrammarSymbolKind, <:AbstractVector{GrammarSymbolKind}},
            ) where {Debug <: Nothing, Token, GrammarSymbolKind}

        Return a table driven strong-LL(1) parser. Use with [`parse`](@ref).

        Set `Debug` to `Nothing` to disable debugging, set it to `Union{}` to enable debugging, which may cause more eager throws in case, for example, the grammar is faulty. Meant to be used while developing a grammar.
        """
        struct StrongLL1TableDrivenParser{
            Debug <: Nothing,  # `Union{}` is "do debugging", `Nothing` is "no debugging"
            Token,
            GrammarSymbolKind,
            Table <: AbstractDict{Tuple{Vararg{GrammarSymbolKind,2}}, <:AbstractVector{GrammarSymbolKind}},
            TableEndMarker <: AbstractDict{GrammarSymbolKind, <:AbstractVector{GrammarSymbolKind}},
        }
            start_symbol_kind::GrammarSymbolKind
            table::Table
            table_end_marker::TableEndMarker
            function StrongLL1TableDrivenParser{Debug, Token}(
                start_symbol_kind::GrammarSymbolKind,
                table::AbstractDict{Tuple{Vararg{GrammarSymbolKind,2}}, <:AbstractVector{GrammarSymbolKind}},
                table_end_marker::AbstractDict{GrammarSymbolKind, <:AbstractVector{GrammarSymbolKind}},
            ) where {
                Debug <: Nothing, Token, GrammarSymbolKind,
            }
                new{Debug, Token, GrammarSymbolKind, typeof(table), typeof(table_end_marker)}(start_symbol_kind, table, table_end_marker)
            end
        end
        const debug_exception = ArgumentError("unexpected: debug")
        function debugging_is_enabled(::StrongLL1TableDrivenParser{Debug}) where {Debug <: Nothing}
            Debug <: Union{}
        end
        function parser_token_type(::(StrongLL1TableDrivenParser{Debug, Token} where {Debug <: Nothing})) where {Token}
            Token
        end
        function parser_grammar_symbol_kind_type(::(StrongLL1TableDrivenParser{Debug, Token, GrammarSymbolKind} where {Debug <: Nothing, Token})) where {GrammarSymbolKind}
            GrammarSymbolKind
        end
        function parse_strong_ll_1_table_driven_predict!(
            stack::Vector{SymbolGraphNodeIdentity},
            graph::SymbolGraphRootless{GrammarSymbolKind},
            stack_top_symbol::SymbolGraphNodeIdentity,
            rule::AbstractVector{GrammarSymbolKind},
            debug::Bool,
        ) where {GrammarSymbolKind}
            parse_tree_kinds = graph.node_to_grammar_symbol_kind
            parse_tree_grammar_rules = graph.nonterminal_node_to_children
            if debug && haskey(parse_tree_grammar_rules, stack_top_symbol)
                throw(debug_exception)
            end
            if debug && (!isempty(rule)) && (parse_tree_kinds[stack_top_symbol] == first(rule))
                throw(debug_exception)
            end
            len = length(rule)
            vec = Vec(undef, len)
            for i ∈ eachindex(rule, vec)
                id = SymbolGraphNodeIdentity()
                vec[i] = id
                parse_tree_kinds[id] = rule[i]
            end
            for id ∈ Iterators.reverse(vec)
                push!(stack, id)
            end
            parse_tree_grammar_rules[stack_top_symbol] = vec
            nothing
        end
        function parse_strong_ll_1_table_driven_end!(
            stack::Vector{SymbolGraphNodeIdentity},
            graph::SymbolGraphRootless{GrammarSymbolKind, Token},
            parsing_table::AbstractDict{GrammarSymbolKind, <:AbstractVector{GrammarSymbolKind}},
            debug::Bool,
        ) where {GrammarSymbolKind, Token}
            error_stack_symbol = nothing
            parse_tree_kinds = graph.node_to_grammar_symbol_kind
            while !isempty(stack)
                stack_top_symbol = pop!(stack)
                stack_top_symbol_kind = parse_tree_kinds[stack_top_symbol]
                # predict step (a match step is not possible)
                if !haskey(parsing_table, stack_top_symbol_kind)
                    # parsing error: unexpected end of input
                    error_stack_symbol = stack_top_symbol
                    break
                end
                rule = parsing_table[stack_top_symbol_kind]
                if debug && (!isempty(rule)) && (parse_tree_kinds[stack_top_symbol] ∈ rule)
                    throw(debug_exception)
                end
                parse_strong_ll_1_table_driven_predict!(stack, graph, stack_top_symbol, rule, debug)
            end
            error_status_inner_type = Optional{Tuple{Token, GrammarSymbolKind}}
            error_status_type = Optional{Tuple{SymbolGraphNodeIdentity, error_status_inner_type}}
            error_status = if error_stack_symbol === nothing
                error_status_type()
            else
                error_stack_symbol = error_stack_symbol::SymbolGraphNodeIdentity
                error_status_type((error_stack_symbol, error_status_inner_type()))
            end
            if debug && isempty(error_status) && !isempty(stack)
                throw(debug_exception)
            end
            error_status
        end
        function parse_strong_ll_1_table_driven_with_lookahead!(
            stack::Vector{SymbolGraphNodeIdentity},
            graph::SymbolGraphRootless{GrammarSymbolKind, Token},
            parsing_table::AbstractDict{Tuple{GrammarSymbolKind, GrammarSymbolKind}, <:AbstractVector{GrammarSymbolKind}},
            debug::Bool,
            parsing_table_end_marker::AbstractDict{GrammarSymbolKind, <:AbstractVector{GrammarSymbolKind}},
            lookahead::Token,
            lookahead_kind::GrammarSymbolKind,
            iter_state,
            tokens_and_kinds,
        ) where {GrammarSymbolKind, Token}
            error_status_inner_type = Optional{Tuple{Token, GrammarSymbolKind}}
            error_status_type = Optional{Tuple{SymbolGraphNodeIdentity, error_status_inner_type}}
            error_status = error_status_type()
            parse_tree_kinds = graph.node_to_grammar_symbol_kind
            parse_tree_tokens = graph.terminal_node_to_token
            if debug
                lookahead = lookahead::Token
                lookahead_kind = lookahead_kind::GrammarSymbolKind
            end
            while true
                stack_top_symbol = pop!(stack)
                stack_top_symbol_kind = parse_tree_kinds[stack_top_symbol]
                if lookahead_kind == stack_top_symbol_kind
                    # a match step
                    if debug && haskey(parse_tree_tokens, stack_top_symbol)
                        throw(debug_exception)
                    end
                    parse_tree_tokens[stack_top_symbol] = lookahead
                    let iter_lookahead_state = iterate(tokens_and_kinds, iter_state)
                        if iter_lookahead_state === nothing
                            # end of input
                            error_status = parse_strong_ll_1_table_driven_end!(stack, graph, parsing_table_end_marker, debug)
                            break
                        else
                            ((lookahead, lookahead_kind), iter_state) = iter_lookahead_state
                            if debug
                                lookahead = lookahead::Token
                                lookahead_kind = lookahead_kind::GrammarSymbolKind
                            end
                        end
                    end
                else
                    # a predict step
                    let parsing_table_key = (stack_top_symbol_kind, lookahead_kind)
                        if !haskey(parsing_table, parsing_table_key)
                            # parsing error: unexpected input symbol kind
                            error_status = error_status_type((stack_top_symbol, error_status_inner_type((lookahead, lookahead_kind))))
                            break
                        end
                        rule = parsing_table[parsing_table_key]
                        parse_strong_ll_1_table_driven_predict!(stack, graph, stack_top_symbol, rule, debug)
                    end
                end
                if isempty(stack)
                    # parsing error: trailing garbage
                    error_status = error_status_type((stack_top_symbol, error_status_inner_type((lookahead, lookahead_kind))))
                    break
                end
            end
            if debug && isempty(error_status) && !isempty(stack)
                throw(debug_exception)
            end
            error_status
        end
        """
            parse(parser, tokens_and_kinds)::Tuple{SymbolGraphRooted, AbstractVector}

        Parse `tokens_and_kinds` with the given parser. Return a (parse tree, error status) tuple.
        """
        function parse end
        function parse(parser::StrongLL1TableDrivenParser, tokens_and_kinds)
            debug = debugging_is_enabled(parser)
            Token = parser_token_type(parser)
            GrammarSymbolKind = parser_grammar_symbol_kind_type(parser)
            if debug
                Tuple{Token, GrammarSymbolKind}::Type{<:eltype(tokens_and_kinds)}
            end
            parsing_table = parser.table
            parsing_table_end_marker = parser.table_end_marker
            graph = SymbolGraphRootless{GrammarSymbolKind, Token}()
            parse_tree_kinds = graph.node_to_grammar_symbol_kind
            start_symbol_kind = parser.start_symbol_kind
            start_symbol = SymbolGraphNodeIdentity()
            parse_tree_kinds[start_symbol] = start_symbol_kind
            stack = [start_symbol]  # the end marker is implicitly always at the bottom of the stack (index zero, say)
            iter_initial = iterate(tokens_and_kinds)
            error_status = if iter_initial === nothing
                # empty input
                parse_strong_ll_1_table_driven_end!(stack, graph, parsing_table_end_marker, debug)
            else
                # nonempty input
                let (e, s) = iter_initial
                    parse_strong_ll_1_table_driven_with_lookahead!(stack, graph, parsing_table, debug, parsing_table_end_marker, e..., s, tokens_and_kinds)
                end
            end
            if debug && isempty(error_status) && !isempty(stack)
                throw(debug_exception)
            end
            ret = SymbolGraphRooted(start_symbol, graph)
            if debug && isempty(error_status)
                ret = validate_symbol_graph(ret)
            end
            (ret, error_status)
        end
        struct AsTree{Graph <: SymbolGraphRooted}
            graph::Graph
            function AsTree(graph::SymbolGraphRooted)
                new{typeof(graph)}(graph)
            end
        end
        """
            graph_as_tree(graph::SymbolGraphRooted)

        Wrap to assume the graph is a tree. The return type implements the AbstractTrees.jl interface.
        """
        function graph_as_tree(graph::SymbolGraphRooted)
            AsTree(graph)
        end
        function AbstractTrees.children(tree::AsTree)
            Iterators.map(graph_as_tree, root_children(tree.graph))
        end
    end
    """
        AbstractParserIdents::Module

    Interface for declaring a concrete parser implementation.
    """
    module AbstractParserIdents
        export AbstractParserIdent, get_lexer, get_token_grammar, get_token_parser, get_parser
        using ..SymbolGraphs: SymbolGraphs
        """
            AbstractParserIdent::DataType

        Abstract type for identifying a parser and related components. Add a subtype together with methods for [`get_lexer`](@ref), [`get_token_grammar`](@ref) and [`get_token_parser`](@ref).
        """
        abstract type AbstractParserIdent end
        """
            get_lexer(::AbstractParserIdent)

        Return a lexer, also known as a tokenizer.

        Add a method for a new subtype of [`AbstractParserIdent`](@ref).
        """
        function get_lexer end
        """
            get_token_grammar(::AbstractParserIdent)

        Return a context-free grammar, together with its start symbol. The tokens returned by the lexer are the terminal symbols of the grammar.

        Add a method for a new subtype of [`AbstractParserIdent`](@ref).
        """
        function get_token_grammar end
        """
            get_token_parser(::AbstractParserIdent)

        Return a high-level parser, operating on tokens returned by the lexer.

        Add a method for a new subtype of [`AbstractParserIdent`](@ref).
        """
        function get_token_parser end
        """
            get_parser(::AbstractParserIdent)

        Return a parser.

        Do not add any method.
        """
        function get_parser(id::AbstractParserIdent)
            p = get_token_parser(id)
            l = get_lexer(id)
            function parser_closure(iterator)
                SymbolGraphs.parse(p, l(iterator))
            end
        end
    end
    module KindConstruction
        export construct_kind!
        function construct_kind!(
            new::New,
            kind_to_name::AbstractDict{<:Any,<:AbstractString},
            name_to_kind::AbstractDict{<:AbstractString},
            name::AbstractString,
        ) where {New}
            if isempty(name)
                throw(ArgumentError("name is empty"))
            end
            if haskey(name_to_kind, name)
                throw(ArgumentError("name already exists"))
            end
            kind = new()
            kind_to_name[kind] = name
            name_to_kind[name] = kind
            kind
        end
    end
    module LexingUtil
        export TokenIteratorState, token_iterator_state_init, lexer_state_simple_new, lexer_state_new, lexer_state_get_extra, lexer_state_get_consumed_character_count, lexer_state_destroy!, lexer_state_peek!, lexer_state_consume!
        using ..Optionals
        const TokenIteratorStateOpaque = Tuple{
            Int64, IOBuffer, Optional{Character}, OptionalCharacterIteratorState,
        } where {Character, OptionalCharacterIteratorState <: Union{Tuple{}, Tuple{Optional}}}
        const TokenIteratorState = NamedTuple{
            (:is_done, :extra, :opaque), Tuple{Bool, Extra, TokenIteratorStateOpaque{Character, OptionalCharacterIteratorState}},
        } where {Extra, Character, OptionalCharacterIteratorState <: Union{Tuple{}, Tuple{Optional}}}
        function token_iterator_state_init_opaque(::Type{Character}) where {Character}
            (Int64(0), IOBuffer(; read = false), Optional{Character}(), ())
        end
        function token_iterator_state_init(::Type{Character}, extra) where {Character}
            opaque = token_iterator_state_init_opaque(Character)
            (;
                is_done = false,
                extra,
                opaque,
            )
        end
        mutable struct LexerStateSimple{Character, CharacterIterator, CharacterIteratorState}
            optional_most_recently_read_character::Optional{Character}
            const character_iterator::CharacterIterator
            """
            * If empty, the input is exhausted.

            * Assuming the character iterator state type stays the same after each iteration!
            """
            optional_character_iterator_state::Optional{CharacterIteratorState}
            function LexerStateSimple(oc::AbstractVector, it, os::AbstractVector)
                new{eltype(oc), typeof(it), eltype(os)}(oc, it, os)
            end
        end
        function lexer_state_simple_new(character_iterator)
            iter = iterate(character_iterator)
            if iter === nothing
                ()
            else
                ls = let (e, s) = iter
                    LexerStateSimple(Optional(e), character_iterator, Optional(s))
                end
                (ls,)
            end
        end
        mutable struct LexerState{Character, CharacterIterator, CharacterIteratorState, Extra}
            optional_most_recently_read_character::Optional{Character}
            const character_iterator::CharacterIterator
            """
            * If empty, the input is exhausted.

            * Assuming the character iterator state type stays the same after each iteration!
            """
            optional_character_iterator_state::Optional{CharacterIteratorState}
            read_character_count::Int64
            const buffer::IOBuffer
            const extra::Extra
            function LexerState(oc::Optional, it, os::Optional, rcc::Int64, buffer::IOBuffer, extra)
                new{eltype(oc), typeof(it), eltype(os), typeof(extra)}(oc, it, os, rcc, buffer, extra)
            end
        end
        function lexer_state_new(opaque::TokenIteratorStateOpaque, extra, character_iterator)
            (rcc, buffer, oc, ois) = opaque
            character_iterator_state = if ois === ()
                if !isempty(oc)
                    throw(ArgumentError("unexpected error"))
                end
                let it = iterate(character_iterator)
                    if it === nothing
                        return ()
                    end
                    let (c, s) = it
                        rcc += true
                        oc = typeof(oc)(c)
                        Optional(s)
                    end
                end
            else
                only(ois)
            end
            ls = LexerState(oc, character_iterator, character_iterator_state, rcc, buffer, extra)
            (ls,)
        end
        function lexer_state_get_extra(lexer_state::LexerState)
            lexer_state.extra
        end
        function lexer_state_is_empty(lexer_state::Union{LexerStateSimple, LexerState})
            isempty(lexer_state.optional_most_recently_read_character)
        end
        function lexer_state_destroy_most_recently_read_character!(lexer_state::Union{LexerStateSimple, LexerState})
            lexer_state.optional_most_recently_read_character = typeof(lexer_state.optional_most_recently_read_character)()
        end
        function lexer_state_advance!(lexer_state::Union{LexerStateSimple, LexerState})
            optional_state = lexer_state.optional_character_iterator_state
            C = typeof(lexer_state.optional_most_recently_read_character)
            S = typeof(optional_state)
            if !lexer_state_is_empty(lexer_state)
                throw(ArgumentError("refusing to overwrite data"))
            end
            if !isempty(optional_state)
                iter = iterate(lexer_state.character_iterator, only(optional_state))
                if iter === nothing
                    lexer_state_destroy_most_recently_read_character!(lexer_state)
                    lexer_state.optional_character_iterator_state = S()
                else
                    if lexer_state isa LexerState
                        lexer_state.read_character_count += true
                    end
                    let (c, s) = iter
                        lexer_state.optional_most_recently_read_character = C(c)
                        lexer_state.optional_character_iterator_state = S(s)
                    end
                end
            end
            nothing
        end
        function lexer_state_get_consumed_character_count(lexer_state::LexerState)
            rcc = lexer_state.read_character_count
            oc = lexer_state.optional_most_recently_read_character
            rcc - !isempty(oc)
        end
        function lexer_state_destroy!(lexer_state::LexerState)
            oc = lexer_state.optional_most_recently_read_character
            optional_state = lexer_state.optional_character_iterator_state
            rcc = lexer_state.read_character_count
            lexer_state_destroy_most_recently_read_character!(lexer_state)
            lexer_state.optional_character_iterator_state = typeof(optional_state)()
            buffer = lexer_state.buffer
            opaque = (rcc, buffer, oc, (optional_state,))
            token_source = take!(buffer)
            (; opaque, token_source)
        end
        function lexer_state_advance_if_possible!(lexer_state::Union{LexerStateSimple, LexerState})
            if lexer_state_is_empty(lexer_state)
                lexer_state_advance!(lexer_state)
                lexer_state_is_empty(lexer_state)
            else
                false
            end
        end
        function lexer_state_peek!(lexer_state::Union{LexerStateSimple, LexerState})
            lexer_state_advance_if_possible!(lexer_state)
            lexer_state.optional_most_recently_read_character
        end
        function lexer_state_consume!(lexer_state::Union{LexerStateSimple, LexerState})
            oc = lexer_state_peek!(lexer_state)
            if (lexer_state isa LexerState) && !isempty(oc)
                print(lexer_state.buffer, only(oc))
            end
            lexer_state_destroy_most_recently_read_character!(lexer_state)
            oc
        end
    end
end
