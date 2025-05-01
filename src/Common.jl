module Common
    module Optionals
        export Optional
        mutable struct Mutable{P}
            const v::P
        end
        struct Optional{P} <: AbstractVector{P}
            v::Mutable{P}
            function Optional{P}() where {P}
                new{P}()
            end
            function Optional{P}(v::P) where {P}
                m = Mutable(v)
                new{P}(m)
            end
        end
        function Optional(v)
            Optional{typeof(v)}(v)
        end
        function Base.propertynames(::Optional, ::Bool = false)
            ()
        end
        function Base.getproperty(::Optional, ::Symbol)
            throw(ArgumentError("no properties"))
        end
        function is_not_empty(o::Optional)
            isdefined(o, 1)
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
            sym = :v
            m = getfield(o, sym)
            getfield(m, sym)
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
    end
    module SymbolGraphs
        export
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
        """
            SymbolGraphNodeIdentity()

        Return the identity of a new node of a symbol graph.
        """
        mutable struct SymbolGraphNodeIdentity end
        const Vec = ((@isdefined Memory) ? Memory : Vector){SymbolGraphNodeIdentity}
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

        Return a graph whose nodes are symbols of a formal grammar.
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

        Return a graph whose nodes are symbols of a formal grammar, with `root` as the root.

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

        Returns the kind of the root node as a grammar symbol.
        """
        function root_symbol_kind(tree::SymbolGraphRooted)
            tree.graph.node_to_grammar_symbol_kind[tree.root]
        end
        """
            root_is_terminal(::SymbolGraphRooted)::Bool

        Predicate, tells if the (root) node of the parse tree is a terminal symbol.
        """
        function root_is_terminal(tree::SymbolGraphRooted)
            root = tree.root
            graph = tree.graph
            # invariant: `haskey(graph.terminal_node_to_token, root) === !haskey(graph.nonterminal_node_to_children, root)`
            haskey(graph.terminal_node_to_token, root)::Bool
        end
        """
            root_is_childless(::SymbolGraphRooted)::Bool

        Predicate, tells if the (root) node of the parse tree is a leaf node/childless.
        """
        function root_is_childless(tree::SymbolGraphRooted)
            root_is_terminal(tree) ||
                isempty(tree.graph.nonterminal_node_to_children[tree.root])
        end
        """
            root_token(::SymbolGraphRooted)

        Returns the token of a terminal symbol.
        """
        function root_token(tree::SymbolGraphRooted)
            tree.graph.terminal_node_to_token[tree.root]
        end
        """
            root_children(::SymbolGraphRooted)

        Returns an iterator of `SymbolGraphRooted` elements.
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

        Forms a terminal symbol from `kind` and `token`, registering it with `kinds` and `tokens`, and returns the new symbol.
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
            iter_initial::Tuple{Tuple{Token, GrammarSymbolKind}, Any},
            tokens_and_kinds,
        ) where {GrammarSymbolKind, Token}
            error_status_inner_type = Optional{Tuple{Token, GrammarSymbolKind}}
            error_status_type = Optional{Tuple{SymbolGraphNodeIdentity, error_status_inner_type}}
            error_status = error_status_type()
            parse_tree_kinds = graph.node_to_grammar_symbol_kind
            parse_tree_tokens = graph.terminal_node_to_token
            ((lookahead, lookahead_kind), iter_state) = iter_initial
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
                parse_strong_ll_1_table_driven_with_lookahead!(stack, graph, parsing_table, debug, parsing_table_end_marker, iter_initial, tokens_and_kinds)
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
    end
end
