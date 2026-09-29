# Owner: WP9 (DESIGN_NetworkEpiCore.md §A.2, §B.4, §B.7; work package in §G.2).
# Only WP9 edits this file. Triggered by Catalyst + Symbolics.
#
# Contents: contact_model(rn::Catalyst.ReactionSystem; susceptible, transmission, rates,
# population, merge_duplicates, name) (a method of the generics.jl stub),
# Catalyst.ReactionSystem(::ContactModel; κ, name, complete) (the syntax-level reverse map
# MA(c_κ P)) and Catalyst.ReactionSystem(::ReactionNetworkData; name, complete).
# NEC never re-exports Catalyst's `species`, `parameters`, `reactions`, `compose`, `equations` or
# `solve` (§A.2); they are qualified here as Catalyst.species etc.
#
# Rates. A Catalyst rate that is an arithmetic expression over RATE_OPS in parameters, numbers
# and the independent variable becomes a Symbol/Expr rate (`τ` → :τ, `(1-p)*σ` → :(σ * (1 - p)),
# `t` → :t), so the ContactModel of `@reaction_network` is the same object as the direct one and
# evaluates, hashes and simulates without Symbolics. Any other rate in parameters and time is
# kept symbolic (a `Symbolics.Num`), which the IR allows. Observables are expanded first; a rate
# that then involves species or any variable other than parameters and time is an error (§B.4
# step 0, §B.1). The system's independent variable is the IR's time t whatever its name: with
# `@ivs s`, `s` becomes the leaf :t of an Expr rate or the variable t of a symbolic one, never a
# constant parameter s (§J.4).
module NetworkEpiCoreCatalystExt

import NetworkEpiCore
import NetworkEpiCore: ContactModel, Contact, NodeTransition, Provenance, PerContact,
                       FrequencyDependent, DensityDependent, ReactionNetworkData, GeneralReaction,
                       SpeciesLabel
import Catalyst
import Symbolics

const NEC = NetworkEpiCore
const SU = Symbolics.SymbolicUtils
const MTKB = Catalyst.ModelingToolkitBase

# ---------------------------------------------------------------------------------------------
# Context: the species, parameters and independent variable of a reaction system
# ---------------------------------------------------------------------------------------------

_name(x) = Symbol(Symbolics.getname(x))
_issymbolic(x) = Symbolics.unwrap(x) isa SU.BasicSymbolic

# The canonical order of the arguments of sums and products, and the canonical printing, of
# NetworkEpiCoreSymbolicsExt (SymbolicUtils' own order changes between releases and sessions).
_SX() = Base.get_extension(NetworkEpiCore, :NetworkEpiCoreSymbolicsExt)
_canonical(x) = _SX()._canonical_string(x)

struct _Context
    species::Vector{Any}              # unwrapped species variables, in Catalyst order
    species_names::Vector{Symbol}
    species_by_name::Dict{Symbol,Any}
    params::Dict{Symbol,Any}          # parameter name => unwrapped parameter
    param_order::Vector{Symbol}
    iv::Any
    observed::Vector{Pair{Any,Any}}   # observable => its definition (unwrapped), `obs ~ expr`
    unknowns::Vector{Any}             # unwrapped unknowns (species and non-species variables)
end

function _context(rn)
    sps = Any[Symbolics.unwrap(s) for s in Catalyst.species(rn)]
    names = Symbol[_name(s) for s in sps]
    # an array parameter k stands for its elements, which Catalyst may list as well (k, k[2])
    ps = Any[]
    for p in Catalyst.parameters(rn)
        u = Symbolics.unwrap(p)
        a = _is_element(u) ? first(SU.arguments(u)) : u
        any(q -> isequal(q, a), ps) || push!(ps, a)
    end
    pnames = Symbol[_name(p) for p in ps]
    iv = Symbolics.unwrap(Catalyst.get_iv(rn))
    # everything below is keyed by name, so two variables with one name would be merged (E25)
    for (what, ns) in (("species", names), ("parameters", pnames))
        i = findfirst(j -> ns[j] in view(ns, 1:(j - 1)), eachindex(ns))
        i === nothing || throw(ArgumentError(
            "the ReactionSystem $(nameof(rn)) has two $(what) named $(ns[i]); a ContactModel " *
            "names its $(what) by Symbols, so the names must be distinct"))
    end
    # the IR reads the name t as time (§B.1), whatever the system's own independent variable is
    # called, so a parameter or species named t would be read as time (§J.4, E25). Catalyst
    # reserves t, but a system built with disable_forbidden_symbol_check = true may use it.
    for (what, ns) in (("species", names), ("parameter", pnames))
        :t in ns || continue
        ivtext = _name(iv) === :t ? "" : " (the independent variable $(_name(iv)) of the system " *
                                          "becomes t)"
        throw(ArgumentError(
            "the ReactionSystem $(nameof(rn)) has a $(what) named t, but a ContactModel reads t " *
            "as time$(ivtext); rename the $(what)"))
    end
    obs = Pair{Any,Any}[Symbolics.unwrap(eq.lhs) => Symbolics.unwrap(eq.rhs)
                        for eq in MTKB.observed(rn)]
    us = Any[Symbolics.unwrap(u) for u in MTKB.unknowns(rn)]
    return _Context(sps, names, Dict(zip(names, sps)), Dict(zip(pnames, ps)), pnames, iv, obs,
                    us)
end

# The IR's time (§B.1): a Symbol/Expr rate uses the leaf `:t`, and a symbolic rate a variable
# named t (NetworkEpiCoreSymbolicsExt detects time by that name). This is Catalyst's (and
# ModelingToolkit's) default independent variable, which the reverse maps use as well.
_ir_time() = Symbolics.unwrap(Catalyst.default_t())

# A symbolic rate of the reaction system in the IR's time: the system's own independent
# variable (`@ivs s`) is replaced by t. Kept as `s`, it would be read as a constant parameter, so
# `β*sin(ω*s)` would be frozen at a value of s (§J.4, E25).
function _in_ir_time(x, ctx::_Context)
    T = _ir_time()
    (_issymbolic(x) && !isequal(ctx.iv, T)) || return x
    any(v -> isequal(v, ctx.iv), _variables(x)) || return x
    return Symbolics.unwrap(Symbolics.substitute(Symbolics.unwrap(x), Dict{Any,Any}(ctx.iv => T)))
end

_is_species(ctx::_Context, v) = any(s -> isequal(s, v), ctx.species)

_is_array(v) = v isa SU.BasicSymbolic && SU.symtype(v) <: AbstractArray
_is_element(v) = v isa SU.BasicSymbolic && SU.iscall(v) && SU.operation(v) === getindex

# A scalar parameter of the reaction system. Array parameters and their elements `k[1]` are not
# parameters of a ContactModel, which names every rate parameter by a Symbol (§B.1): `k[1]` and
# `k[2]` both have the name k, so they are rejected rather than merged (E25).
_is_parameter(ctx::_Context, v) = !_is_array(v) && any(p -> isequal(p, v), values(ctx.params))

# The array parameter behind `v` (`k` for `k[1]` or `k` itself), or nothing.
function _array_parameter(ctx::_Context, v)
    a = _is_element(v) ? first(SU.arguments(v)) : v
    (_is_array(a) && any(p -> isequal(p, a), values(ctx.params))) || return nothing
    return a
end

# Scalar names for the elements of an array parameter, for messages: k1 k2 for k[1:2], K1_1 K1_2
# … for a matrix (row by row); at most four are listed.
function _scalar_names(a)
    nm = _name(a)
    idx = try
        [reverse(i) for i in vec(collect(Iterators.product(reverse(SU.shape(a))...)))]
    catch
        [(1,), (2,)]
    end
    names = String[string(nm, join(i, "_")) for i in idx[1:min(end, 4)]]
    return join(names, " ") * (length(idx) > 4 ? " …" : "")
end

# The variables of a symbolic rate, by name. Every variable must be a scalar symbol (a parameter
# or time) or, where `species` allows it, a species `X(t)` of a general rate law. An element
# `k[1]` of an array, an array, or a function of time such as `β(t)` has no Symbol name of its
# own, and two different variables with one name (β::Real and β::Int) would be merged by any map
# that goes through names, so each of these is an ArgumentError (E25).
function _named_variables(x, where; species = ())
    out = Pair{Symbol,Any}[]
    for v in _variables(x)
        n = if v isa SU.BasicSymbolic && SU.issym(v) && !_is_array(v)
            _name(v)
        elseif v isa SU.BasicSymbolic && SU.iscall(v) && SU.operation(v) isa SU.BasicSymbolic &&
               SU.issym(SU.operation(v)) && _name(v) in species
            _name(v)
        else
            nothing
        end
        if n === nothing
            what = _is_element(v) ?
                   "an element of the array $(first(SU.arguments(v))); use scalar parameters " *
                   "such as $(_scalar_names(first(SU.arguments(v))))" :
                   _is_array(v) ? "an array; use scalar parameters such as $(_scalar_names(v))" :
                   isempty(species) ?
                   "which is not a scalar parameter or time; a rate may depend on parameters " *
                   "(named by Symbols) and time only" :
                   "which is not a species, a scalar parameter or time"
            throw(ArgumentError("$(where) uses $(v), $(what)"))
        end
        i = findfirst(p -> first(p) === n, out)
        if i === nothing
            push!(out, n => v)
        elseif !isequal(last(out[i]), v)
            throw(ArgumentError("$(where) uses two different variables named $(n) " *
                                "($(repr(SU.symtype(last(out[i])))) and " *
                                "$(repr(SU.symtype(v)))); a rate names each parameter by a " *
                                "Symbol, so the names must be distinct"))
        end
    end
    return out
end

_observable_index(ctx::_Context, v) = findfirst(p -> isequal(first(p), v), ctx.observed)

function _has_species(ctx::_Context, x)
    _issymbolic(x) || return false
    return any(v -> _is_species(ctx, v), Symbolics.get_variables(Symbolics.unwrap(x)))
end

# ---------------------------------------------------------------------------------------------
# Symbolic expression → Real | Symbol | Expr over RATE_OPS
# ---------------------------------------------------------------------------------------------

# Thrown when a symbolic expression is not an arithmetic expression over RATE_OPS in numbers,
# parameters and time; the rate is then kept symbolic.
struct _NotArithmetic <: Exception
    what::String
end

function _const_value(v)
    v isa Real && !(v isa Bool) && return v
    throw(_NotArithmetic("the constant $(repr(v))"))
end

# `display = true` (for messages only) renders species as their names, puts numbers first, then
# the other factors, then the species in model order, and renders anything else by its string.
function _rate_expr(x, ctx::_Context; display::Bool = false)
    ex = _to_expr(Symbolics.unwrap(x), ctx, display)
    return _tidy(ex)
end

function _to_expr(x, ctx, display)
    if !(x isa SU.BasicSymbolic)
        x isa Real && return _const_value(x)
        throw(_NotArithmetic("the value $(repr(x))"))
    end
    SU.isconst(x) && return _const_value(SU.unwrap_const(x))
    if _is_species(ctx, x)
        display && return _name(x)
        throw(_NotArithmetic("the species $(_name(x))"))
    end
    if SU.issym(x)
        # the independent variable is the IR's time :t (messages keep the name as written)
        isequal(x, ctx.iv) && return display ? _name(x) : :t
        n = _name(x)
        (display || haskey(ctx.params, n)) && return n
        throw(_NotArithmetic("the variable $(n), which is not a parameter"))
    end
    SU.iscall(x) || throw(_NotArithmetic(_canonical(x)))
    op = SU.operation(x)
    args = _SX()._sorted_arguments(x)       # sums and products in the canonical order
    conv(a) = _to_expr(a, ctx, display)
    if op === (+)
        ts = Any[conv(a) for a in args]
        display && (ts = _display_sum_order(ts, args, ctx))
        return _sum_expr(ts)
    elseif op === (*)
        fs = Any[conv(a) for a in args]
        return _prod_expr(_factor_order(fs, args, ctx, display))
    elseif op === (/) && length(args) == 2
        return Expr(:call, :/, conv(args[1]), conv(args[2]))
    elseif op === (^) && length(args) == 2
        return Expr(:call, :^, conv(args[1]), conv(args[2]))
    elseif (op === exp || op === log) && length(args) == 1
        return Expr(:call, Symbol(op), conv(args[1]))
    elseif (op === min || op === max) && length(args) >= 2
        return Expr(:call, Symbol(op), Any[conv(a) for a in args]...)
    elseif op === sqrt && length(args) == 1
        return Expr(:call, :^, conv(args[1]), 0.5)
    elseif op === (-) && length(args) in (1, 2)
        return Expr(:call, :-, Any[conv(a) for a in args]...)
    end
    display && return Symbol(_display_string(x, ctx))
    throw(_NotArithmetic("the function $(op)"))
end

# SymbolicUtils stores the factors of a product in its own canonical order (`ε*τ2` comes back as
# [τ2, ε]). Factors are put back in a stable, readable order: numbers, then parameters and time
# by name (so `ε*τ2`, `p*σ` and `τ0*exp(-a*t)` read as written), then compound factors, and, in
# messages, any other variable by name (a non-species unknown or an observable: `β*V`, `β*M`)
# and the species last in model order (`β*S*I`).
_species_index(ctx, x) = something(findfirst(s -> isequal(s, x), ctx.species), 0)

function _factor_order(fs, args, ctx, display)
    function rank(i)
        fs[i] isa Real && return (0, "", i)
        a = args[i]
        display && _is_species(ctx, a) && return (4, "", _species_index(ctx, a))
        if fs[i] isa Symbol && a isa SU.BasicSymbolic && SU.issym(a) &&
           (isequal(a, ctx.iv) || haskey(ctx.params, _name(a)))
            return (1, string(fs[i]), i)
        end
        # only messages render other variables (`V(t)` as V) or unconverted terms as Symbols
        display && fs[i] isa Symbol && a isa SU.BasicSymbolic &&
            (SU.issym(a) || _is_variable_term(a)) && return (3, string(fs[i]), i)
        return (2, "", i)
    end
    return fs[sortperm(collect(eachindex(fs)); by = rank)]
end

# A dependent variable such as V(t) or an observable M(t) (not a species: those come first).
_is_variable_term(a) = a isa SU.BasicSymbolic && SU.iscall(a) &&
                       SU.operation(a) isa SU.BasicSymbolic && SU.issym(SU.operation(a))

# The terms of a sum in messages: numbers, terms without species, then terms with species in
# model order of their first species (`1 + a*I`, `S + I + R`).
function _display_sum_order(ts, args, ctx)
    function rank(i)
        ts[i] isa Real && return (0, i)
        sp = [v for v in _variables(args[i]) if _is_species(ctx, v)]
        isempty(sp) && return (1, i)
        return (2, minimum(_species_index(ctx, v) for v in sp))
    end
    return ts[sortperm(collect(eachindex(ts)); by = rank)]
end

function _prod_expr(fs)
    nums = [f for f in fs if f isa Real]
    rest = Any[f for f in fs if !(f isa Real)]
    c = isempty(nums) ? 1 : prod(nums)
    isempty(rest) && return c
    iszero(c) && return c
    isone(c) && return length(rest) == 1 ? rest[1] : Expr(:call, :*, rest...)
    return Expr(:call, :*, c, rest...)
end

# (is_negative, magnitude) of a term of a sum.
function _split_sign(t)
    t isa Real && return t < 0 ? (true, -t) : (false, t)
    if t isa Expr && t.head === :call
        t.args[1] === :- && length(t.args) == 2 && return (true, t.args[2])
        if t.args[1] === :* && t.args[2] isa Real && t.args[2] < 0
            c = -t.args[2]
            rest = t.args[3:end]
            isone(c) && return (true, length(rest) == 1 ? rest[1] : Expr(:call, :*, rest...))
            return (true, Expr(:call, :*, c, rest...))
        end
    end
    return (false, t)
end

function _sum_expr(terms)
    acc = nothing
    for t in terms
        if acc === nothing
            acc = t
            continue
        end
        neg, mag = _split_sign(t)
        if neg
            acc = Expr(:call, :-, acc, mag)
        elseif acc isa Expr && acc.head === :call && acc.args[1] === :+
            acc = Expr(:call, :+, acc.args[2:end]..., mag)
        else
            acc = Expr(:call, :+, acc, mag)
        end
    end
    return acc
end

# Rewrite leftover coefficients -1 as unary minus: (-1)*a*t → (-a)*t, (-1)*a → -a.
_tidy(x) = x
function _tidy(ex::Expr)
    args = Any[_tidy(a) for a in ex.args]
    if ex.head === :call && args[1] === :* && length(args) >= 3 && args[2] isa Real &&
       args[2] == -1
        rest = args[3:end]
        length(rest) == 1 && return Expr(:call, :-, rest[1])
        return Expr(:call, :*, Expr(:call, :-, rest[1]), rest[2:end]...)
    end
    return Expr(ex.head, args...)
end

# ---------------------------------------------------------------------------------------------
# Reaction strings (RN style, as in §B.7: "β, S + I --> E + R", "μ, ∅ --> S")
# ---------------------------------------------------------------------------------------------

# A symbolic expression printed for messages, with the species and other variables of the
# independent variable by their names (`I(t)` and `I(s)` as I; `sin(s)` stays `sin(s)`).
function _display_string(x, ctx)
    x = Symbolics.unwrap(x)
    _issymbolic(x) || return string(x)
    subs = Dict{Any,Any}(v => Symbolics.unwrap(Symbolics.variable(_name(v)))
                         for v in _variables(x) if _is_variable_term(v))
    isempty(subs) && return _canonical(x)
    return _canonical(Symbolics.substitute(x, subs))
end

function _rate_display(r, ctx)
    ex = try
        _rate_expr(r, ctx; display = true)
    catch err
        err isa _NotArithmetic || rethrow()
        return _display_string(r, ctx)
    end
    return NEC._rate_string(ex)
end

_side_string(side::Vector{Pair{Symbol,Int}}) =
    isempty(side) ? "∅" : join((n == 1 ? string(x) : string(n, x) for (x, n) in side), " + ")

function _raw_side_string(vars, stoich)
    isempty(vars) && return "∅"
    parts = String[]
    for (v, n) in zip(vars, stoich)
        nm = try
            string(_name(v))
        catch
            string(v)
        end
        push!(parts, isequal(n, 1) ? nm : string(n, nm))
    end
    return join(parts, " + ")
end

function _rx_string(rx, ctx)
    arrow = rx.only_use_rate ? " => " : " --> "
    return string(_rate_display(rx.rate, ctx), ", ",
                  _raw_side_string(rx.substrates, rx.substoich), arrow,
                  _raw_side_string(rx.products, rx.prodstoich))
end

# ---------------------------------------------------------------------------------------------
# Classification of one reaction (§B.4 steps 0, 2, 3)
# ---------------------------------------------------------------------------------------------

struct _Classified
    kind::Symbol                       # :contact | :transition | :noop
    index::Int
    recipient::Symbol                  # contact: s; transition: X
    infector::Symbol                   # contact: J; transition: unused (:∅)
    product::Union{Symbol,Nothing}     # contact: X; transition: Y or nothing
    rate::Any                          # unwrapped symbolic rate constant (or a number)
    reduced::Bool                      # a `=>` rate law reduced to its mass-action constant
    text::String                       # the reaction as written (for messages)
    observed::Vector{Symbol}           # observables expanded in the rate
    simplified::Bool                   # species in the rate cancel (it was simplified)
end

_Classified(kind, index, recipient, infector, product, rate, reduced, text) =
    _Classified(kind, index, recipient, infector, product, rate, reduced, text, Symbol[], false)

function _integer_stoich(n, k, rxs)
    n = Symbolics.unwrap(n)
    n isa SU.BasicSymbolic && SU.isconst(n) && (n = SU.unwrap_const(n))
    (n isa Real && isinteger(n) && n >= 1) && return Int(n)
    throw(ArgumentError("`$(rxs)`: the stoichiometry $(n) is not a positive integer " *
                        "(reaction $(k)); a ContactModel has unit-stoichiometry contacts and " *
                        "transitions only"))
end

function _side(vars, stoich, k, rxs)
    out = Pair{Symbol,Int}[]
    for (v, n) in zip(vars, stoich)
        v = Symbolics.unwrap(v)
        nm = _name(v)
        Catalyst.isspecies(v) || throw(ArgumentError(
            "`$(rxs)`: $(nm) is a constant species (a parameter); in a network model every " *
            "reactant is a node state, so declare $(nm) as a species (reaction $(k))"))
        Catalyst.isbc(v) && throw(ArgumentError(
            "`$(rxs)`: $(nm) is a boundary-condition species; in a network model every " *
            "reactant is a node state whose number changes only through the reactions " *
            "(reaction $(k))"))
        m = _integer_stoich(n, k, rxs)
        i = findfirst(p -> first(p) === nm, out)
        i === nothing ? push!(out, nm => m) : (out[i] = nm => last(out[i]) + m)
    end
    return out
end

_count(side) = sum(last, side; init = 0)
_multiset(side) = Dict{Symbol,Int}(side)

const _IR_TAIL = "the IR supports mass-action contacts and first-order transitions only"

function _rate_error(rxs, k, nsub, distinct, via = "")
    kind = (nsub == 2 && distinct) ? "non-bilinear incidence" :
           nsub == 1 ? "not a first-order transition" : "not mass action"
    return ArgumentError("rate law of `$(rxs)` depends on species ($(kind))$(via). Reaction " *
                         "$(k) has a species-dependent or non-mass-action rate law; $(_IR_TAIL).")
end

# Replace the observables in a rate by their definitions (`obs ~ expr` in `observed(rn)`),
# repeatedly, since a definition may use other observables. Returns the expanded rate and the
# observables used, in order of first use.
function _expand_observed(x, ctx::_Context, k, rxs)
    used = Any[]
    (isempty(ctx.observed) || !_issymbolic(x)) && return x, used
    for _ in 0:length(ctx.observed)
        subs = Dict{Any,Any}()
        for v in _variables(x)
            i = _observable_index(ctx, v)
            i === nothing && continue
            subs[v] = last(ctx.observed[i])
            any(u -> isequal(u, v), used) || push!(used, v)
        end
        isempty(subs) && return x, used
        x = Symbolics.unwrap(Symbolics.substitute(x, subs))
    end
    throw(ArgumentError("`$(rxs)`: the observables $(join(string.(used), ", ")) in the rate are " *
                        "defined in terms of one another (reaction $(k))"))
end

# "through the observable Ntot = S + I + R" (the definition fully expanded), for messages.
function _via_observed(used, ctx)
    isempty(used) && return ""
    defs = String[]
    for v in used
        rhs, _ = _expand_observed(last(ctx.observed[_observable_index(ctx, v)]), ctx, 0, "")
        push!(defs, string(_name(v), " = ", _rate_display(rhs, ctx)))
    end
    return string(" through the observable", length(defs) == 1 ? " " : "s ", join(defs, ", "))
end

# §B.1: a rate is species-free and may depend on parameters and time only. After the
# observables are expanded, every variable left must be a scalar parameter or the independent
# variable; anything else, such as a non-species unknown declared with @variables, would
# otherwise be stored as if it were a constant. An element k[1] of an array parameter is an
# error too: the IR names rate parameters by Symbols, and k[1] and k[2] would both become k.
function _check_rate_variables(x, ctx::_Context, k, rxs)
    for v in _variables(x)
        isequal(v, ctx.iv) && continue
        a = _array_parameter(ctx, v)
        if a !== nothing
            what = isequal(a, v) ? "the array parameter $(_name(a))" :
                   "$(v), an element of the array parameter $(_name(a))"
            throw(ArgumentError(
                "`$(rxs)`: the rate uses $(what) (reaction $(k)). A ContactModel names each " *
                "rate parameter by a Symbol and has scalar parameters only; declare scalar " *
                "parameters instead, for example @parameters $(_scalar_names(a))."))
        end
        # a time-dependent parameter (`@discretes β(t)`) is not a constant of the model
        _is_variable_term(v) && _is_parameter(ctx, v) && throw(ArgumentError(
            "`$(rxs)`: the rate uses the time-dependent parameter $(v) (reaction $(k)). The " *
            "parameters of a ContactModel are constants; write the time dependence into the " *
            "rate as an expression in the independent variable $(ctx.iv) (such as " *
            "β0*exp(-a*$(ctx.iv))), or use an intervention in NetworkOutbreaks."))
        _is_parameter(ctx, v) && continue
        what = any(u -> isequal(u, v), ctx.unknowns) ?
               "a non-species unknown of the reaction system" :
               "not a parameter of the reaction system"
        throw(ArgumentError(
            "`$(rxs)`: the rate depends on $(v), which is $(what) (reaction $(k)). A network " *
            "rate is species-free and may depend on parameters and the independent variable " *
            "$(ctx.iv) only; declare a constant with @parameters $(_name(v))."))
    end
    return nothing
end

# The species-free rate constant k of a reaction: `rx.rate` for `-->`, and L/∏A for `=>`
# (§B.4 step 0), with the observables of the rate expanded. A rate whose species cancel
# (`β*(I + 1) - β*I`) is species-free after expansion and simplification, and is replaced by
# that form (`simplified`); a rate that still involves species is an error.
function _rate_constant(rx, subs, ctx, k, rxs)
    L, used = _expand_observed(Symbolics.unwrap(rx.rate), ctx, k, rxs)
    nsub = _count(subs)
    distinct = length(subs) == nsub
    reduced = rx.only_use_rate
    if reduced
        P = prod((ctx.species_by_name[x]^n for (x, n) in subs); init = 1)
        L = Symbolics.unwrap(Symbolics.simplify(L / P))
    end
    simplified = false
    if _has_species(ctx, L)
        L2 = _species_free_form(L, ctx)
        L2 === nothing && throw(_rate_error(rxs, k, nsub, distinct, _via_observed(used, ctx)))
        L, simplified = L2, true
    end
    _check_rate_variables(L, ctx, k, rxs)
    return L, reduced, Symbol[_name(v) for v in used], simplified
end

# A species-free form of `x` by expansion, then simplification, or nothing.
function _species_free_form(x, ctx)
    for f in (Symbolics.expand, y -> Symbolics.simplify(Symbolics.expand(y)))
        y = try
            Symbolics.unwrap(f(x))
        catch
            continue
        end
        _has_species(ctx, y) || return y
    end
    return nothing
end

# Evidence for the orientation of a bimolecular reaction a + b → … that is not a contact, for
# the suggestion in its error message (which substrate is the recipient s and which the
# infector J): the declared susceptible species, the recipients and infectors of the reactions
# that are contacts by stoichiometry, and the species that some reaction produces (a net gain).
struct _Hints
    sus::Vector{Symbol}
    recipients::Set{Symbol}
    infectors::Set{Symbol}
    produced::Set{Symbol}
end

function _hints(rxs_all, ctx, sus)
    rec, inf, made = Set{Symbol}(), Set{Symbol}(), Set{Symbol}()
    for (k, rx) in enumerate(rxs_all)
        subs, prods = try
            _side(rx.substrates, rx.substoich, k, ""), _side(rx.products, rx.prodstoich, k, "")
        catch err
            err isa ArgumentError || rethrow()
            continue                   # its own classification reports it
        end
        A, B = _multiset(subs), _multiset(prods)
        for (x, n) in B
            n > get(A, x, 0) && push!(made, x)
        end
        (length(subs) == 2 && _count(subs) == 2) || continue
        a, b = first(subs[1]), first(subs[2])
        C = [x for x in (a, b) if get(B, x, 0) >= 1]
        length(C) == 1 || continue
        J = only(C)
        rest = copy(B)
        rest[J] -= 1
        filter!(p -> last(p) > 0, rest)
        (length(rest) == 1 && only(values(rest)) == 1) || continue
        push!(rec, J === a ? b : a)
        push!(inf, J)
    end
    return _Hints(sus, rec, inf, made)
end

# The orientation (s, J) of the substrates a, b of a non-contact: the first kind of evidence
# that tells them apart decides (a declared susceptible species is the recipient; then the roles
# in the contacts; then a species that no reaction produces is the recipient, one that some
# reaction produces the infector); without evidence, the first substrate is the recipient.
function _orientation(a, b, h::_Hints)
    for score in ((a in h.sus) - (b in h.sus),
                  (a in h.recipients) + (b in h.infectors) - (b in h.recipients) -
                  (a in h.infectors),
                  (b in h.produced) - (a in h.produced))
        score > 0 && return (a, b)
        score < 0 && return (b, a)
    end
    return (a, b)
end

function _classify(rx, k, ctx, hints::_Hints)
    rxs = _rx_string(rx, ctx)
    subs = _side(rx.substrates, rx.substoich, k, rxs)
    prods = _side(rx.products, rx.prodstoich, k, rxs)
    isempty(subs) && throw(ArgumentError(
        "`$(rxs)`: births change the node set; use Catalyst's own ODE for mass action."))
    if _multiset(subs) == _multiset(prods)
        return _Classified(:noop, k, first(first(subs)), :∅, nothing, rx.rate, false, rxs)
    end
    rate, reduced, obs, simp = _rate_constant(rx, subs, ctx, k, rxs)
    made(kind, s, J, X) = _Classified(kind, k, s, J, X, rate, reduced, rxs, obs, simp)
    nsub = _count(subs)
    if nsub == 1                                      # X → Y | ∅
        X = first(only(subs))
        np = _count(prods)
        np == 0 && return made(:transition, X, :∅, nothing)
        np == 1 && return made(:transition, X, :∅, first(only(prods)))
        throw(ArgumentError(
            "`$(rxs)`: splitting (one node becomes $(np) nodes); a node transition changes the " *
            "state of one node (X → Y or X → ∅), and births change the node set."))
    end
    if !(length(subs) == 2 && nsub == 2)
        throw(ArgumentError(
            "`$(rxs)`: higher order ($(_side_string(subs))); a network model has contacts " *
            "between two distinct nodes (s + J → X + J) and node transitions (X → Y | ∅) " *
            "only. Use Catalyst's own ODE for mass action."))
    end
    a, b = first(subs[1]), first(subs[2])
    B = _multiset(prods)
    C = [x for x in (a, b) if get(B, x, 0) >= 1]
    rs = _rate_display(rate, ctx)
    if length(C) == 1
        J = only(C)
        s = J === a ? b : a
        rest = copy(B)
        rest[J] -= 1
        filter!(p -> last(p) > 0, rest)
        if length(rest) == 1 && only(values(rest)) == 1
            return made(:contact, s, J, only(keys(rest)))
        elseif isempty(rest)
            throw(ArgumentError(
                "`$(rxs)`: the recipient $(s) disappears (its only product is the infector " *
                "$(J)); a contact s + J → X + J turns the recipient into another state X. Add " *
                "a removed state, for example `$(rs), $(s) + $(J) --> D + $(J)`."))
        else
            prod_text = _side_string([x => rest[x] for (x, _) in prods if haskey(rest, x)])
            throw(ArgumentError(
                "`$(rxs)`: not a pairwise contact: besides the infector $(J) it produces " *
                "$(prod_text) from the one recipient $(s); a contact s + J → X + J turns one " *
                "recipient into one node."))
        end
    elseif isempty(C)
        # the suggestion pairs the substrates with the products as written (a → first product)
        s, J = _orientation(a, b, hints)
        expanded = Symbol[x for (x, n) in prods for _ in 1:n]
        if length(expanded) == 2
            Xs, XJ = s === a ? (expanded[1], expanded[2]) : (expanded[2], expanded[1])
            throw(ArgumentError(
                "`$(rxs)`: the infector changes state on transmission; a network contact must " *
                "leave the infector unchanged. Split it into `$(rs), $(s) + $(J) --> $(Xs) + " *
                "$(J)` and a transition `$(J) --> $(XJ)`."))
        elseif length(expanded) == 1
            throw(ArgumentError(
                "`$(rxs)`: the infector is consumed on transmission; a network contact must " *
                "leave the infector unchanged. Write it as `$(rs), $(s) + $(J) --> " *
                "$(only(expanded)) + $(J)`, with any change of $(J) as a transition."))
        end
        throw(ArgumentError(
            "`$(rxs)`: not a pairwise contact: neither substrate survives, and a contact " *
            "s + J → X + J turns one recipient into one node and leaves the infector unchanged."))
    end
    throw(ArgumentError(
        "`$(rxs)`: not a pairwise contact: both substrates survive and new nodes appear " *
        "(births change the node set)."))
end

# ---------------------------------------------------------------------------------------------
# Reaction metadata and the `transmission` overrides (§B.4 step 1)
# ---------------------------------------------------------------------------------------------

_metadata(rx, key) = Catalyst.hasmetadata(rx, key) ? Catalyst.getmetadata(rx, key) : nothing

function _bool_metadata(rx, key, k, rxs)
    v = _metadata(rx, key)
    (v === nothing || v isa Bool) && return v
    throw(ArgumentError("`$(rxs)`: the metadata [$(key) = $(repr(v))] must be true or false " *
                        "(reaction $(k))"))
end

function _symbol_metadata(rx, key, k, rxs)
    v = _metadata(rx, key)
    v === nothing && return nothing
    (v isa Symbol || v isa AbstractString) && return Symbol(v)
    throw(ArgumentError("`$(rxs)`: the metadata [$(key) = $(repr(v))] must be a Symbol " *
                        "(reaction $(k))"))
end

function _symbols_metadata(rx, key, k, rxs)
    v = _metadata(rx, key)
    v === nothing && return Symbol[]
    (v isa Symbol || v isa AbstractString) && return [Symbol(v)]
    (v isa AbstractVector || v isa Tuple) && all(x -> x isa Union{Symbol,AbstractString}, v) &&
        return Symbol[Symbol(x) for x in v]
    throw(ArgumentError("`$(rxs)`: the metadata [$(key) = $(repr(v))] must be a Symbol or a " *
                        "vector of Symbols (reaction $(k))"))
end

# Contact flags per reaction (`nothing` when classification is by stoichiometry alone), and the
# provenance method.
function _transmission_flags(transmission, rxs_all, texts)
    n = length(rxs_all)
    if transmission === :stoichiometry
        return nothing, :stoichiometry
    elseif transmission === :metadata
        flags = Bool[something(_bool_metadata(rx, :contact, k, texts[k]), false)
                     for (k, rx) in enumerate(rxs_all)]
        return flags, :metadata
    elseif transmission isa AbstractVector{Bool}
        length(transmission) == n || throw(ArgumentError(
            "transmission: a Vector{Bool} needs one flag per reaction ($(n)); got " *
            "$(length(transmission))"))
        return collect(Bool, transmission), :predicate
    elseif transmission isa AbstractVector && all(x -> x isa Integer, transmission)
        bad = [i for i in transmission if !(1 <= i <= n)]
        isempty(bad) || throw(ArgumentError(
            "transmission: reaction indices $(join(bad, ", ")) are out of range 1:$(n)"))
        return Bool[k in transmission for k in 1:n], :predicate
    elseif transmission isa Symbol
        throw(ArgumentError("transmission = :$(transmission) is not supported; use " *
                            ":stoichiometry, :metadata, a predicate rx -> Bool, a Vector{Bool} " *
                            "or reaction indices"))
    end
    (n == 0 || applicable(transmission, first(rxs_all))) || throw(ArgumentError(
        "transmission must be :stoichiometry, :metadata, a predicate rx -> Bool, a " *
        "Vector{Bool} or reaction indices; got $(repr(transmission))"))
    flags = Bool[]
    for rx in rxs_all
        v = transmission(rx)
        v isa Bool || throw(ArgumentError(
            "transmission: the predicate must return true or false; got $(repr(v))"))
        push!(flags, v)
    end
    return flags, :predicate
end

function _check_flag(c::_Classified, flag, source)
    (flag === nothing || c.kind === :noop) && return nothing
    if flag && c.kind !== :contact
        throw(ArgumentError(
            "`$(c.text)` is marked as a contact ($(source)), but it is a node transition: a " *
            "contact s + J → X + J has two distinct substrates and a catalytic infector J. " *
            "Overrides disambiguate; they never change a reaction's stoichiometry (reaction " *
            "$(c.index))."))
    elseif !flag && c.kind === :contact
        throw(ArgumentError(
            "`$(c.text)` is marked as not a contact ($(source)), but its stoichiometry is that " *
            "of a contact s + J → X + J with the catalytic infector $(c.infector); the IR has " *
            "no bimolecular transitions, so mark it as a contact (reaction $(c.index))."))
    end
    return nothing
end

# ---------------------------------------------------------------------------------------------
# Rate conventions (§B.4 step 5, §B.6)
# ---------------------------------------------------------------------------------------------

const _RATES = (:per_contact, :frequency, :density)

function _check_population(population)
    population === nothing && return nothing
    population isa Symbol && return population
    (population isa Real && !(population isa Bool) && isfinite(population) && population > 0) &&
        return population
    throw(ArgumentError("population must be nothing, a parameter name (Symbol) or a positive " *
                        "number; got $(repr(population))"))
end

# f ≡ g: symbolically (expand and simplify the difference) or, when simplification cannot
# decide, by the evidence rule of vector_fields_equal (§J.3, `_probe_equal`).
function _identically_equal(f, g, what)
    d = try
        Symbolics.unwrap(Symbolics.simplify(Symbolics.expand(f - g)))
    catch
        nothing
    end
    x = d === nothing ? nothing : _numeric(d)
    (x !== nothing && iszero(x)) && return true
    return _probe_equal(f, g, what)
end

# The verdict of NetworkEpiCoreSymbolicsExt on f ≡ g (every variable a parameter, or time, by
# name): exact after folding, else seeded probes that must be evidence (every term of the
# difference that does not cancel is seen at a probe point, and the cancellation does not depend
# on the value of a non-analytic part such as max or ifelse). An undecided answer is an error that
# says why, never "equal" (and never "different": the caller's error would then misreport the
# rate's form). `what` names the comparison in that error.
function _probe_equal(f, g, what; probes = 8)
    SX = Base.get_extension(NetworkEpiCore, :NetworkEpiCoreSymbolicsExt)
    v = SX._expressions_verdict(f, g; probes)
    v.verdict === :undecided && throw(ArgumentError(
        "$(what): cannot decide whether $(_display_expr(f)) and $(_display_expr(g)) are equal " *
        "(the answer is unknown, not false): the difference " * SX._undecided_why(v.why, v.what, probes)))
    return v.verdict === :equal
end

_display_expr(x) = "`$(_canonical(x))`"

_substitute(x, vals) = _issymbolic(x) ? Symbolics.substitute(x, vals; fold = Val(true)) : x

function _numeric(v)
    v = Symbolics.unwrap(v)
    if v isa SU.BasicSymbolic
        SU.isconst(v) || return nothing
        v = SU.unwrap_const(v)
    end
    (v isa Real && !(v isa Bool)) || return nothing
    return Float64(v)
end

# In order of first appearance, with sums and products in the canonical order.
_variables(x) = _issymbolic(x) ? _SX()._variables(Symbolics.unwrap(x)) : Any[]

function _population_var(ctx, N, what)
    if haskey(ctx.params, N)
        _is_array(ctx.params[N]) && throw(ArgumentError(
            "$(what): population = :$(N) is an array parameter; the population size is a " *
            "scalar parameter or a number"))
        return ctx.params[N]
    end
    throw(ArgumentError("$(what): population = :$(N) is not a parameter of the reaction system " *
                        "(parameters: $(join(ctx.param_order, ", ")))"))
end

# k with rate ≡ k/N: rate·N must not depend on N.
function _frequency_constant(rate, N, ctx, c::_Classified)
    if N isa Real
        return _issymbolic(rate) ? Symbolics.unwrap(Symbolics.simplify(rate * N)) : rate * N
    end
    Nv = _population_var(ctx, N, "rates = :frequency")
    cand = Symbolics.unwrap(_substitute(rate, Dict(Nv => 1)))
    ok = _issymbolic(rate) && any(v -> isequal(v, Nv), _variables(rate)) &&
         _identically_equal(Symbolics.unwrap(rate * Nv), cand,
                            "`$(c.text)` (reaction $(c.index)), rates = :frequency, " *
                            "population = :$(N): is rate·$(N) independent of $(N)?")
    ok || throw(ArgumentError(
        "`$(c.text)`: with rates = :frequency, population = :$(N) a contact rate must have the " *
        "form k/$(N) with k independent of $(N) (β S I/N), but its rate is " *
        "$(_rate_display(rate, ctx)) (reaction $(c.index))"))
    return cand
end

# k with rate ≡ k·N (the fraction-scale mass-action rate of a DensityDependent(N) contact).
#
# In a hand-written system the rate must have that form (k = rate at N = 1), which catches a rate
# written in counts by mistake. A system written by Catalyst.ReactionSystem(cm), whose system
# metadata records the convention DensityDependent(N), has the rate β·N exactly, but Symbolics
# may have simplified the product (β/N of cm is written as (β/N)·N = β), so there k = rate/N.
function _density_constant(rate, N, ctx, c::_Classified, written::Bool)
    if N isa Real
        return _issymbolic(rate) ? Symbolics.unwrap(Symbolics.simplify(rate / N)) : rate / N
    end
    Nv = _population_var(ctx, N, "[rate_convention = :density]")
    cand = Symbolics.unwrap(_substitute(rate, Dict(Nv => 1)))
    ok = _issymbolic(rate) &&
         _identically_equal(rate, Symbolics.unwrap(cand * Nv),
                            "`$(c.text)` (reaction $(c.index)), [rate_convention = :density, " *
                            "population = :$(N)]: is the rate of the form β·$(N)?")
    ok && return cand
    written && return Symbolics.unwrap(Symbolics.simplify(rate / Nv))
    throw(ArgumentError(
        "`$(c.text)`: the metadata [rate_convention = :density, population = :$(N)] says that " *
        "the rate is the mass-action rate β·$(N) on population fractions, but " *
        "$(_rate_display(rate, ctx)) is not of that form (reaction $(c.index))"))
end

# The rate r of a DensityDependent(N) contact with a number N, read back exactly. The reverse map
# writes the mass-action rate r·N, rounded (0.1·3.0 = 0.30000000000000004, and rate/N then gives
# 0.10000000000000002), so it records r as the reaction metadata [ir_rate = r] too. r is used
# when it reproduces the rate of the reaction exactly, and so is never a different rate (an
# edited rate gives nothing, and rate/N is used).
function _stored_density_rate(rx, rate, N, ctx)
    N isa Real || return nothing
    r = _metadata(rx, :ir_rate)
    r === nothing && return nothing
    vars = Dict{Symbol,Any}(ctx.params)
    vars[:t] = ctx.iv
    w = try
        _to_symbolic(r, vars)
    catch err
        err isa ArgumentError || rethrow()
        return nothing
    end
    a, b = _numeric(w), _numeric(rate)
    same = (a !== nothing && b !== nothing) ? a * N == b :
           isequal(Symbolics.unwrap(w * N), Symbolics.unwrap(rate))
    same || return nothing
    return r isa Union{Real,Symbol,Expr} ? r : Symbolics.unwrap(w)
end

# Convention metadata written by `Catalyst.ReactionSystem(cm)`: (convention, population) or
# nothing, identical on every contact.
function _metadata_convention(rxs_all, contacts_cl, texts)
    found = nothing
    for (i, c) in enumerate(contacts_cl)
        rx = rxs_all[c.index]
        rc = _symbol_metadata(rx, :rate_convention, c.index, texts[c.index])
        pop = _metadata(rx, :population)
        pop isa AbstractString && (pop = Symbol(pop))
        rc === nothing && pop !== nothing && throw(ArgumentError(
            "`$(c.text)`: the metadata [population = …] needs [rate_convention = …] " *
            "(reaction $(c.index))"))
        this = rc === nothing ? nothing : (rc, pop)
        if rc !== nothing
            rc in _RATES || throw(ArgumentError(
                "`$(c.text)`: [rate_convention = :$(rc)] must be one of $(_RATES) " *
                "(reaction $(c.index))"))
            rc === :density && pop === nothing && throw(ArgumentError(
                "`$(c.text)`: [rate_convention = :density] needs [population = N] " *
                "(reaction $(c.index))"))
            rc === :density || pop === nothing || throw(ArgumentError(
                "`$(c.text)`: [rate_convention = :$(rc)] takes no [population = …]: the rate " *
                "of a reaction with convention metadata is its mass-action rate on population " *
                "fractions (β for :frequency); use rates = :frequency, population = :N for β/N " *
                "(reaction $(c.index))"))
            _check_population(pop)
        end
        if i == 1
            found = this
        elseif !isequal(this, found)
            throw(ArgumentError(
                "the contacts carry different [rate_convention = …, population = …] metadata " *
                "(`$(first(contacts_cl).text)` and `$(c.text)`); a ContactModel has one rate " *
                "convention"))
        end
    end
    return found
end

_mentions(k, name::Symbol) = any(v -> SU.issym(v) && _name(v) === name, _variables(k))

function _population_text(N)
    N isa Symbol && return ":$(N)"
    return string(N)
end

# Apply the convention to the contact rates; returns (rates, convention, assumptions). `written`
# is the convention in the system metadata of a system written by Catalyst.ReactionSystem(cm), or
# nothing: it is the convention of a model without contacts (whose reactions carry no convention
# metadata) unless the keywords set one, and it marks the density rates as exact.
function _apply_convention(contacts_cl, rxs_all, texts, rates, population, ctx, written)
    rates in _RATES || throw(ArgumentError("rates = $(repr(rates)) must be one of $(_RATES)"))
    population = _check_population(population)
    notes = String[]
    if isempty(contacts_cl) && written !== nothing && rates === :per_contact &&
       population === nothing
        written isa PerContact || push!(notes,
            "rate convention $(written) read from the system metadata written by " *
            "Catalyst.ReactionSystem(::ContactModel) (the model has no contacts)")
        return Any[], written, notes
    end
    md = isempty(contacts_cl) ? nothing : _metadata_convention(rxs_all, contacts_cl, texts)
    ks = Any[c.rate for c in contacts_cl]
    if md !== nothing
        conv_md, pop_md = md
        (rates === :per_contact || rates === conv_md) || throw(ArgumentError(
            "rates = :$(rates) contradicts the reaction metadata [rate_convention = " *
            ":$(conv_md)] of the contacts"))
        (population === nothing || isequal(population, pop_md)) || throw(ArgumentError(
            "population = $(repr(population)) contradicts the reaction metadata " *
            "[population = $(repr(pop_md))] of the contacts"))
        if conv_md === :per_contact
            return ks, PerContact(), notes
        elseif conv_md === :frequency
            push!(notes, "contact rates read from the reaction metadata " *
                         "[rate_convention = :frequency]: β of β S I/N on population fractions " *
                         "(FrequencyDependent)")
            return ks, FrequencyDependent(), notes
        else
            exact = written isa DensityDependent && isequal(written.N, pop_md)
            stored = Any[exact ? _stored_density_rate(rxs_all[c.index], k, pop_md, ctx) : nothing
                         for (k, c) in zip(ks, contacts_cl)]
            ks = Any[r === nothing ? _density_constant(k, pop_md, ctx, c, exact) : r
                     for (r, k, c) in zip(stored, ks, contacts_cl)]
            push!(notes, "contact rates read from the reaction metadata [rate_convention = " *
                         ":density, population = $(_population_text(pop_md))]: the rate is the " *
                         "mass-action rate β·N on population fractions, β stored " *
                         "(DensityDependent)")
            return ks, DensityDependent(pop_md), notes
        end
    end
    if rates === :per_contact
        wanted = population isa Symbol ? population : :N
        i = findfirst(k -> _mentions(k, wanted), ks)
        if i !== nothing
            @warn "rate $(_rate_display(ks[i], ctx)) looks frequency-dependent; pass " *
                  "rates = :frequency, population = :$(wanted)"
        elseif population !== nothing
            @warn "population = $(repr(population)) has no effect with rates = :per_contact " *
                  "(the contact rates are read as per-contact rates τ); pass rates = :frequency " *
                  "or rates = :density to use it"
        end
        return ks, PerContact(), notes
    elseif rates === :frequency
        if population === nothing
            i = findfirst(k -> _mentions(k, :N), ks)
            if i !== nothing
                r = _rate_display(ks[i], ctx)
                @warn "rate $(r) contains N, but rates = :frequency was given without a " *
                      "population, so $(r) itself is stored as the β of β S I/N; pass " *
                      "population = :N to read the rate as β/N and store β"
            end
            push!(notes, "contact rates read as frequency-dependent β of β S I/N on population " *
                         "fractions (rates = :frequency, no population parameter)")
            return ks, FrequencyDependent(), notes
        end
        ks = Any[_frequency_constant(k, population, ctx, c) for (k, c) in zip(ks, contacts_cl)]
        if population isa Symbol
            push!(notes, "contact rates read as frequency-dependent: rate = β/N with N = " *
                         "$(_population_text(population)); β stored (rates = :frequency)")
        else
            Nt = _population_text(population)
            push!(notes, "contact rates read as frequency-dependent with the number N = $(Nt): " *
                         "each rate is taken to be β/N and β = $(Nt)·rate is stored " *
                         "(rates = :frequency; the form of a rate cannot be checked against a " *
                         "number)")
        end
        return ks, FrequencyDependent(), notes
    else
        population === nothing && throw(ArgumentError(
            "rates = :density needs population = :N (the population size, a parameter name or " *
            "a number): density-dependent contacts are β S I in counts, τ = β N/⟨k⟩"))
        (population isa Symbol && haskey(ctx.params, population)) &&
            _population_var(ctx, population, "rates = :density")    # a scalar parameter
        push!(notes, "contact rates read as density-dependent β of β S I in counts, population " *
                     "N = $(_population_text(population)) (rates = :density)")
        return ks, DensityDependent(population), notes
    end
end

# ---------------------------------------------------------------------------------------------
# IR rates, parameters and defaults (§B.4 step 6)
# ---------------------------------------------------------------------------------------------

# A Symbol/Expr rate when the expression is arithmetic over RATE_OPS; otherwise a Num. Either
# way the system's independent variable becomes the IR's time: the leaf :t of an Expr, or the
# variable t (`_ir_time()`) of a Num, whatever the system calls it (§J.4).
function _ir_rate(x, ctx, notes, text)
    x = Symbolics.unwrap(x)
    x isa SU.BasicSymbolic || return x
    try
        return _rate_expr(x, ctx)
    catch err
        err isa _NotArithmetic || rethrow()
        push!(notes, "the rate of `$(text)` is kept symbolic ($(err.what) is not in RATE_OPS " *
                     "$(NEC.RATE_OPS))")
        return Symbolics.Num(_in_ir_time(x, ctx))
    end
end

# Parameter names of an IR rate (Symbol/Expr/number/Num), excluding time. The variables of a
# symbolic rate are scalar parameters and the IR's time t (checked by _check_rate_variables;
# _context rejects a parameter named t), so no two of them share a name; _named_variables makes
# sure of it. SymbolicUtils keeps the variables of an expression in an order of its own, which
# changes with the variables (`β*sin(ω*s)` and `β*sin(ω*t)` list β and ω in different orders), so
# the names of a symbolic rate are sorted, as the parameters of a product are in Expr rates.
function _ir_rate_names(r, ctx)
    r isa Symbolics.Num || return Symbol[NEC._parameter_name(p) for p in NEC.rate_parameters(r)]
    return sort!(Symbol[n for (n, v) in _named_variables(r, "the rate $(r)")
                        if !(n === :t || isequal(v, ctx.iv))]; by = string)
end

# Numeric parameter defaults by name, the species with initial values, the parameters whose
# defaults are not numbers, and the array parameters with defaults (no rate uses an array
# parameter, so these are not recorded).
function _defaults(rn, ctx)
    vals = Dict{Symbol,Float64}()
    pending = Dict{Symbol,Any}()
    sources = Any[MTKB.initial_conditions(rn)]
    isdefined(MTKB, :bindings) && push!(sources, MTKB.bindings(rn))
    species_ic = Symbol[]
    arrays = Symbol[]
    for src in sources, (key, v) in pairs(src)
        n = _name(key)
        if !haskey(ctx.params, n)
            _is_species(ctx, Symbolics.unwrap(key)) && push!(species_ic, n)
            continue
        end
        if _is_array(ctx.params[n])
            n in arrays || push!(arrays, n)
            continue
        end
        x = _numeric(v)
        x === nothing ? (pending[n] = Symbolics.unwrap(v)) : (vals[n] = x)
    end
    for n in ctx.param_order                        # fallback: the variable's own default
        (haskey(vals, n) || haskey(pending, n) || n in arrays) && continue
        d = Symbolics.getdefaultval(ctx.params[n], nothing)
        d === nothing && continue
        if _is_array(ctx.params[n])
            push!(arrays, n)
            continue
        end
        x = _numeric(d)
        x === nothing ? (pending[n] = Symbolics.unwrap(d)) : (vals[n] = x)
    end
    progress = true
    while progress && !isempty(pending)             # defaults given in terms of other defaults
        progress = false
        subs = Dict{Any,Any}(ctx.params[n] => v for (n, v) in vals)
        for (n, v) in collect(pending)
            x = _numeric(_substitute(v, subs))
            x === nothing && continue
            vals[n] = x
            delete!(pending, n)
            progress = true
        end
    end
    # (the sources are dictionaries: the species in model order, the arrays by name)
    unique!(species_ic)
    sort!(species_ic; by = n -> something(findfirst(==(n), ctx.species_names), typemax(Int)))
    return vals, species_ic, sort!(collect(keys(pending))), sort!(arrays)
end

function _unique_name(base::Symbol, used::Set{Symbol})
    name = base
    k = 1
    while name in used
        k += 1
        name = Symbol(base, :_, k)
    end
    push!(used, name)
    return name
end

# ---------------------------------------------------------------------------------------------
# contact_model(::ReactionSystem)
# ---------------------------------------------------------------------------------------------

"""
    contact_model(rn::Catalyst.ReactionSystem; susceptible = :infer,
                  transmission = :stoichiometry, rates = :per_contact, population = nothing,
                  merge_duplicates = false, name = nameof(rn)) -> ContactModel

Classify the reactions of a Catalyst reaction network as contacts `s + J → X + J` and node
transitions `X → Y | ∅` (DESIGN §B.4; loaded with Catalyst and Symbolics). Species names are
`Symbolics.getname` of the species, so the namespaced names of `compose`d systems (`pop1₊S`)
are kept.

For each reaction, with substrates A and products B (multisets):

- **Rate.** The rate must not involve species, and may depend on parameters and time only
  (§B.1). Observables in a rate are first replaced by their definitions, so `β/Ntot` with
  `Ntot ~ S + I + R` depends on species. A rate whose species cancel (`β*(I + 1) - β*I`) is
  replaced by its species-free form (`β`), with a note. A `=>` reaction (`only_use_rate`) must
  have a mass-action law L = k·∏A with a species-free k, which becomes the rate. Otherwise the
  `ArgumentError` reads "rate law of `β*S*I/(1 + a*I), S + I => E + I` depends on species
  (non-bilinear incidence)." A rate that uses any other variable, such as a non-species unknown
  declared with `@variables V(t)` or a time-dependent parameter `@discretes β(t)`, is an
  `ArgumentError` naming the reaction and the variable, since binding it to a constant would
  change the model. So is an element `k[1]` of an array parameter: a `ContactModel` names each
  rate parameter by a Symbol, and `k[1]` and `k[2]` would both be `k`; declare scalar
  parameters (`@parameters k1 k2`) instead.
- **Time.** The independent variable of the system is the time t of the model, whatever its
  name: in a network declared with `@ivs s`, the rate `β*sin(ω*s)` is the time-dependent rate
  `β*sin(ω*t)` (never a rate with a constant parameter `s`), exactly as if the network had been
  written in t. A parameter or species named `t` is therefore an `ArgumentError`, and so is a
  system with spatial independent variables (`@ivs t x`), since a `ContactModel` has no space.
- **Transition.** A = {X} and B = {Y} or ∅ give `NodeTransition(X, Y | nothing)`; X → Y + Z is
  an error (splitting).
- **Contact.** A = {a, b} (distinct, unit stoichiometry) with exactly one catalytic substrate J
  (B[J] ≥ 1) and B − {J} = {X} gives `Contact(s, J, X)`: `S + I --> 2I`, `S + I --> E + I`,
  tracing `S + D --> Q + D`, S-catalysed recovery `I + S --> R + S`. If no substrate survives
  (`S + I --> E + R`) the infector changes state, which is an error that suggests the split.
- **Errors** name the reaction: births `∅ --> S`, higher order (`2S + I --> …`), splitting,
  non-catalytic or non-pairwise contacts (`S + I --> 3I`), constant or boundary-condition
  species, parametric stoichiometry, non-reaction equations and events. The suggested split of
  a non-catalytic contact takes as the recipient the substrate that the other reactions show to
  be susceptible (declared susceptible, a recipient rather than an infector of the contacts, or
  never produced by a reaction), and otherwise the first substrate.
- **No-ops** (A = B, including X → X) are dropped with a warning.

The model is not required to be admissible for any back end here: each back end checks its own
admissibility (`show(cm)` prints the typing). Species are ordered as the IR orders them
(susceptible first, then first appearance reading `s + J → X + J` as s, X, J, so SEIR is S, E,
I, R as in `seir_model()`), followed by any species that takes part in no reaction; a system
written by `Catalyst.ReactionSystem(cm)` keeps the species order of `cm`. Species that carry
a [`SpeciesLabel`](@ref) as species metadata (as that reverse map writes them) keep their labels.

# Keywords

- `susceptible`: the susceptible set Σ (`:infer`: contact recipients that are never a contact
  product, §B.2), a Symbol or a vector. Reactions may also declare it with the metadata
  `[susceptible = :S]`.
- `transmission`: `:stoichiometry` (the default) classifies by stoichiometry and checks any
  `[contact = true/false]` metadata against it; `:metadata` makes the contacts exactly the
  reactions marked `[contact = true]`; a predicate `rx -> Bool`, a `Vector{Bool}` or reaction
  indices flag the contacts, with the calling convention of ReproductiveNumbers.jl. Overrides
  disambiguate; they never make an unrepresentable reaction representable, so a flag that
  contradicts the stoichiometry is an error, and with a predicate, vector or indices any
  `[contact = …]` metadata is checked as well. Note that the flags mark the *contacts*
  `s + J → X + J`, which is a consistency check, not the "new infection" flags of an NGM: a
  contact whose product is not infectious (tracing `S + D --> Q + D`, or `R1 + I2 --> I12 + I2`)
  must be flagged as a contact, and a reaction that creates an infected node without a contact
  (importation `η, S --> E`) must not.
- `rates` ([`RateConvention`](@ref)): `:per_contact` (the rate is the per-contact rate τ; a
  contact rate that contains a parameter named `N`, or `population`, gives a warning, and so does
  a `population` that no contact rate uses, since it has no effect here); `:frequency`
  (β S I/N: with `population = :N` the rate must be k/N and k is stored; with a number N the
  rate is taken to be β/N and N·rate is stored, which the provenance records; without
  `population` the rate is β on population fractions, with a warning if it contains `N`);
  `:density` (β S I in counts; needs `population`, recorded as `DensityDependent(population)`;
  the rate itself is β, so a population name need not be a parameter of `rn`: it becomes a
  parameter of the model, whose value is supplied when the model is lifted. `:frequency`, in
  contrast, reads the rate as k/N and so needs N to be a parameter of `rn`).
  The conversion to τ happens at lift time ([`per_contact_rates`](@ref)).
- `merge_duplicates = true` adds the rates of identical reactions; otherwise they are an error.

Contacts carry the layer of the metadata `[layer = :home]` (for a `MultiplexNetwork`). The
metadata `[rate_convention = :frequency]` or `[rate_convention = :density, population = N]`,
which `Catalyst.ReactionSystem(cm)` writes, fixes the convention: the rate is then the
mass-action rate on population fractions (β, respectively β·N, from which β is recovered), and
`rates` must be left at `:per_contact` or agree. The system metadata written by that reverse map
records the convention as well, which gives the convention of a model without contacts when
`rates` and `population` are left at their defaults.

Rates that are arithmetic over [`RATE_OPS`](@ref) in parameters, numbers and time become Symbol
or Expr rates (so `contact_model(rn)` and the direct `ContactModel` are the same object); other
species-free rates are kept symbolic. The rate parameters are in order of first appearance in
the rates (contacts, then transitions; §B.1, as for the direct constructor, with the parameters
of one symbolic rate by name), not in the order of `Catalyst.parameters(rn)`. Parameter defaults come from
`ModelingToolkitBase.initial_conditions` (and bindings), falling back to
`Symbolics.getdefaultval`. The provenance records the source `:catalyst`, the classification
method, every assumption and the reaction map.

```julia
sir = @reaction_network sir begin
    @parameters τ = 0.2 γ = 0.25
    τ, S + I --> 2I
    γ, I --> R
end
contact_model(sir)                      # isequivalent to sir_model()
seir = @reaction_network seir begin
    β / N, S + I --> E + I
    σ, E --> I
    γ, I --> R
end
contact_model(seir; rates = :frequency, population = :N)   # S + I → E + I at β, FrequencyDependent
```
"""
function NetworkEpiCore.contact_model(rn::Catalyst.ReactionSystem; susceptible = :infer,
                                      transmission = :stoichiometry, rates = :per_contact,
                                      population = nothing, merge_duplicates::Bool = false,
                                      name = nothing)
    ctx = _context(rn)
    _check_system(rn)
    rxs_all = Catalyst.reactions(rn)
    texts = String[_rx_string(rx, ctx) for rx in rxs_all]
    assumptions = String[]

    # the susceptible set declared by the user or by reaction metadata
    sus_md = Symbol[]
    for (k, rx) in enumerate(rxs_all), x in _symbols_metadata(rx, :susceptible, k, texts[k])
        x in ctx.species_names || throw(ArgumentError(
            "`$(texts[k])`: the metadata [susceptible = :$(x)] names $(x), which is not a " *
            "species (reaction $(k))"))
        x in sus_md || push!(sus_md, x)
    end
    sus_kw = susceptible === :infer ? nothing :
             susceptible isa Symbol ? [susceptible] :
             (susceptible isa AbstractVector && all(x -> x isa Symbol, susceptible)) ?
             collect(Symbol, susceptible) :
             throw(ArgumentError("susceptible must be :infer, a Symbol or a vector of Symbols; " *
                                 "got $(repr(susceptible))"))
    if sus_kw !== nothing && !isempty(sus_md) && Set(sus_kw) != Set(sus_md)
        throw(ArgumentError("susceptible = $(repr(sus_kw)) contradicts the reaction metadata " *
                            "[susceptible = …], which declares $(join(sus_md, ", "))"))
    end
    hints = _hints(rxs_all, ctx, something(sus_kw, sus_md))

    # classify
    cls = _Classified[_classify(rx, k, ctx, hints) for (k, rx) in enumerate(rxs_all)]
    flags, method = _transmission_flags(transmission, rxs_all, texts)
    source = transmission === :metadata ? "reaction metadata [contact = …]" :
             "transmission = …"
    # every flag, and any [contact = …] metadata besides a predicate's flags, is checked
    # against the stoichiometry, so flags and metadata can never disagree silently
    for c in cls
        flags === nothing || _check_flag(c, flags[c.index], source)
        if method !== :metadata
            md = _bool_metadata(rxs_all[c.index], :contact, c.index, c.text)
            _check_flag(c, md, "reaction metadata [contact = $(md)]")
        end
    end
    if method !== :stoichiometry
        by = method === :metadata ? "the reaction metadata [contact = true]" : "transmission = …"
        push!(assumptions, "contacts flagged by $(by) and checked against the stoichiometry")
    end
    for c in cls
        if c.kind === :noop
            @warn "reaction $(c.index) (`$(c.text)`) does nothing and is dropped"
            push!(assumptions, "dropped reaction $(c.index) (`$(c.text)`): it does nothing")
            continue
        end
        if !isempty(c.observed)
            one = length(c.observed) == 1
            push!(assumptions, "reaction $(c.index) (`$(c.text)`): the observable" *
                               "$(one ? "" : "s") $(join(c.observed, ", ")) in the rate " *
                               "replaced by $(one ? "its definition" : "their definitions")")
        end
        if c.reduced
            push!(assumptions, "reaction $(c.index) (`$(c.text)`): the rate law was reduced to " *
                               "its mass-action constant $(_rate_display(c.rate, ctx))")
        end
        if c.simplified
            push!(assumptions, "reaction $(c.index) (`$(c.text)`): the species in the rate " *
                               "cancel; the rate is $(_rate_display(c.rate, ctx))")
        end
    end

    # layers (contacts only)
    ccls = [c for c in cls if c.kind === :contact]
    tcls = [c for c in cls if c.kind === :transition]
    layers = Dict{Int,Symbol}()
    for c in cls
        c.kind === :noop && continue
        ℓ = _symbol_metadata(rxs_all[c.index], :layer, c.index, c.text)
        ℓ === nothing && continue
        c.kind === :contact || throw(ArgumentError(
            "`$(c.text)`: the metadata [layer = :$(ℓ)] applies to contacts only; a node " *
            "transition happens on every layer (reaction $(c.index))"))
        layers[c.index] = ℓ
        ℓ === :all || push!(assumptions, "reaction $(c.index) (`$(c.text)`) acts on the layer " *
                                         ":$(ℓ) (reaction metadata)")
    end

    # rate convention, then IR rates
    ks, conv, cnotes = _apply_convention(ccls, rxs_all, texts, rates, population, ctx,
                                         _convention_hint(rn))
    append!(assumptions, cnotes)
    used = Set{Symbol}()
    cs = Contact[]
    ts = NodeTransition[]
    for (c, k) in zip(ccls, ks)
        ℓ = get(layers, c.index, :all)
        base = ℓ === :all ? Symbol(c.recipient, :_, c.infector, :_to_, c.product) :
               Symbol(c.recipient, :_, c.infector, :_to_, c.product, :_, ℓ)
        push!(cs, Contact(c.recipient, c.infector, c.product, _ir_rate(k, ctx, assumptions, c.text),
                          ℓ, _unique_name(base, used)))
    end
    for c in tcls
        base = Symbol(c.recipient, :_to_, something(c.product, :∅))
        push!(ts, NodeTransition(c.recipient, c.product, _ir_rate(c.rate, ctx, assumptions, c.text),
                                 _unique_name(base, used)))
    end
    rmap = vcat(Int[c.index for c in ccls], Int[c.index for c in tcls])
    if _name(ctx.iv) !== :t && any(r -> NEC._uses_time(r.rate), Iterators.flatten((cs, ts)))
        push!(assumptions, "the independent variable $(_name(ctx.iv)) of the ReactionSystem is " *
                           "the time t of the model (the time-dependent rates use t)")
    end

    # species: the IR order of first appearance, then species no reaction touches, unless the
    # system carries the order written by Catalyst.ReactionSystem(cm)
    sp = NEC._infer_species(cs, ts)
    idle = [x for x in ctx.species_names if !(x in sp)]
    if !isempty(idle)
        verb = length(idle) == 1 ? "takes" : "take"
        push!(assumptions, "species $(join(idle, ", ")) $(verb) part in no reaction")
    end
    append!(sp, idle)
    hint = _species_order_hint(rn)
    if hint !== nothing && length(hint) == length(sp) && Set(hint) == Set(sp) && hint != sp
        sp = hint
        push!(assumptions, "species order read from the system metadata written by " *
                           "Catalyst.ReactionSystem(::ContactModel)")
    end
    labels = _species_labels(ctx)
    isempty(labels) || push!(assumptions,
        "species labels of $(join(sort!(collect(keys(labels))), ", ")) read from the species " *
        "metadata SpeciesLabel")

    # parameters (order of first appearance in the rates) and defaults
    params = Any[]
    for r in Iterators.flatten((cs, ts)), n in _ir_rate_names(r.rate, ctx)
        n in params || push!(params, n)
    end
    conv isa DensityDependent && conv.N isa Symbol && !(conv.N in params) && push!(params, conv.N)
    defaults, species_ic, unresolved, arrays = _defaults(rn, ctx)
    isempty(species_ic) || push!(assumptions,
        "the initial values of $(join(species_ic, ", ")) in the ReactionSystem are not used " *
        "(each back end seeds from a SeedSpec)")
    isempty(unresolved) || push!(assumptions,
        "the defaults of $(join(unresolved, ", ")) do not evaluate to numbers and are not recorded")
    isempty(arrays) || push!(assumptions,
        "the defaults of the array parameter$(length(arrays) == 1 ? "" : "s") " *
        "$(join(arrays, ", ")) are not recorded (no rate uses $(length(arrays) == 1 ? "it" : "them"), " *
        "and a ContactModel has scalar parameters only)")

    Σ = if sus_kw !== nothing
        sus_kw
    elseif !isempty(sus_md)
        push!(assumptions, "Sus declared by the reaction metadata [susceptible = …] = " *
                           "{$(join(sus_md, ", "))}")
        sus_md
    else
        :infer
    end
    mname = name === nothing ? Symbol(nameof(rn)) : Symbol(name)
    pv = Provenance(:catalyst; method, assumptions, reaction_map = rmap)
    return ContactModel(mname; contacts = cs, transitions = ts, species = sp, susceptible = Σ,
                        convention = conv, defaults, labels, rate_params = params,
                        provenance = pv, merge_duplicates)
end

# The key of the system metadata that records the species order of a ContactModel (§B.1: the
# order is significant for every back end), written by Catalyst.ReactionSystem(cm).
struct _SpeciesOrder end

# The key of the system metadata that records the rate convention of a ContactModel, written by
# Catalyst.ReactionSystem(cm): the reaction metadata [rate_convention = …] sits on the contacts,
# so a model without contacts keeps its convention only here.
struct _Convention end

function _convention_hint(rn)
    md = MTKB.get_metadata(rn)
    md isa AbstractDict || return nothing
    v = get(md, _Convention, nothing)
    return v isa NEC.RateConvention ? v : nothing
end

function _species_order_hint(rn)
    md = MTKB.get_metadata(rn)
    md isa AbstractDict || return nothing
    v = get(md, _SpeciesOrder, nothing)
    (v isa AbstractVector && all(x -> x isa Symbol, v)) || return nothing
    return collect(Symbol, v)
end

# SpeciesLabels carried as species metadata (the key is the type SpeciesLabel itself), so that
# stratified, staged and reinfection-counted models keep their labels through the round trip.
function _species_labels(ctx::_Context)
    labels = Dict{Symbol,SpeciesLabel}()
    for (x, s) in zip(ctx.species_names, ctx.species)
        l = Symbolics.getmetadata(s, SpeciesLabel, nothing)
        l isa SpeciesLabel && (labels[x] = l)
    end
    return labels
end

function _check_system(rn)
    # Catalyst lists the spatial independent variables among the parameters, so a rate in x
    # would otherwise be read as a rate with a constant parameter x
    sivs = Catalyst.get_sivs(rn)
    isempty(sivs) || throw(ArgumentError(
        "the ReactionSystem $(nameof(rn)) has the spatial independent variable" *
        "$(length(sivs) == 1 ? "" : "s") $(join(string.(sivs), ", ")); a ContactModel is a " *
        "model in time only (space enters through the network), so declare the reaction " *
        "system with one independent variable, time"))
    extra = [eq for eq in Catalyst.equations(rn) if !(eq isa Catalyst.Reaction)]
    isempty(extra) || throw(ArgumentError(
        "the ReactionSystem $(nameof(rn)) has $(length(extra)) non-reaction equation(s) " *
        "($(first(extra))); a ContactModel has contacts and node transitions only"))
    nev = length(MTKB.continuous_events(rn)) + length(MTKB.discrete_events(rn))
    nev == 0 || throw(ArgumentError(
        "the ReactionSystem $(nameof(rn)) has $(nev) event(s); a ContactModel cannot represent " *
        "events (in NetworkOutbreaks, use interventions such as ScheduledRateChange)"))
    return nothing
end

# ---------------------------------------------------------------------------------------------
# Reverse maps: ContactModel and ReactionNetworkData → Catalyst.ReactionSystem
# ---------------------------------------------------------------------------------------------

const _EXPR_OPS = Dict{Symbol,Function}(:+ => +, :- => -, :* => *, :/ => /, :^ => ^,
                                        :exp => exp, :log => log, :min => min, :max => max)

# A rate (Real | Symbol | Expr | Num) as a symbolic expression over the variables `vars` (by name).
# `species` names the species a symbolic rate law may use as `X(t)` (general reaction networks);
# a ContactModel rate is species-free.
_to_symbolic(x::Symbolics.Num, vars; species = ()) = _rebind(x, vars; species)
_to_symbolic(x::Real, vars; species = ()) = x
function _to_symbolic(x::Symbol, vars; species = ())
    haskey(vars, x) || throw(ArgumentError("the rate refers to $(x), which is neither a " *
                                           "parameter, a species nor time"))
    return vars[x]
end
function _to_symbolic(ex::Expr, vars; species = ())
    op = ex.args[1]
    haskey(_EXPR_OPS, op) || throw(ArgumentError("the rate `$(ex)` uses $(op), which is not in " *
                                                 "RATE_OPS $(NEC.RATE_OPS)"))
    return _EXPR_OPS[op](Any[_to_symbolic(a, vars; species) for a in ex.args[2:end]]...)
end
function _to_symbolic(x, vars; species = ())
    _issymbolic(x) && return _rebind(x, vars; species)
    throw(ArgumentError("cannot convert the rate $(repr(x)) to a Catalyst rate"))
end

# A symbolic rate with its variables replaced, by name, by the variables of the new system.
# Going through names is safe because _named_variables admits only variables that have a name of
# their own (never k[1], an array or β(t)) and no two distinct variables with one name.
function _rebind(x, vars; species = ())
    u = Symbolics.unwrap(x)
    subs = Dict{Any,Any}()
    for (n, v) in _named_variables(u, "the symbolic rate $(x)"; species)
        haskey(vars, n) || throw(ArgumentError("the symbolic rate $(x) refers to $(n), which is " *
                                               "neither a parameter, a species nor time"))
        subs[v] = Symbolics.unwrap(vars[n])
    end
    return Symbolics.substitute(u, subs)
end

# The names a rate refers to (parameters, and time or species where they occur).
_rate_names(r; species = ()) =
    r isa Symbolics.Num || _issymbolic(r) ?
    Symbol[first(p) for p in _named_variables(r, "the symbolic rate $(r)"; species)] :
    Symbol[NEC._parameter_name(p) for p in NEC.rate_parameters(r)]

function _parameters(names)
    return Dict{Symbol,Any}(n => only(Catalyst.@parameters $(n)) for n in names)
end

function _species(names, t)
    return Dict{Symbol,Any}(x => only(Catalyst.@species $(x)(t)) for x in names)
end

# The defaults of a model are parameter values by name (§B.1), which the reverse maps write as
# the initial conditions of the parameters. A default named like a species or t is not a
# parameter value and has no place in the reaction system, so it is an error rather than
# dropped (the initial states of a ContactModel come from a SeedSpec).
function _check_default_names(defs, spset, what)
    bad = sort!([n for n in keys(defs) if n in spset || n === :t])
    isempty(bad) && return nothing
    kinds = [n === :t ? "$(n) (time)" : "$(n) (a species)" for n in bad]
    throw(ArgumentError(
        "$(what) has default$(length(bad) == 1 ? "" : "s") for $(join(kinds, ", ")); the " *
        "defaults are parameter values, which the ReactionSystem records as the initial " *
        "conditions of its parameters (initial states come from a SeedSpec), so remove " *
        "$(length(bad) == 1 ? "it" : "them")"))
end

function _check_kappa(κ)
    κ isa Symbol && return κ
    (κ isa Real && !(κ isa Bool) && isfinite(κ) && κ > 0) && return κ
    throw(ArgumentError("κ must be a positive number or a parameter name (Symbol); got " *
                        "$(repr(κ))"))
end

"""
    Catalyst.ReactionSystem(cm::ContactModel; κ = 1, name = nameof(cm), complete = true)

The syntax-level reverse map (DESIGN §B.4, §D.5 "back to mass action", sense 1): the reaction
network MA(c_κ P) whose mass-action ODE, on population fractions, is the well-mixed model of
`cm` on `WellMixed(κ)`. Contacts become `k, s + J --> X + J` (`2J` when X = J), transitions
`a, X --> Y` (or `X --> ∅`), with the mass-action contact rate k from the rate convention on a
network of mean degree κ: κτ for `PerContact`, β for `FrequencyDependent` (for every κ), and β·N
for `DensityDependent(N)`. `κ` may be a number or a new parameter name; a name that is already a
parameter of `cm` (`κ = :τ` would give τ², S + I --> 2I), a species or `t` is an
`ArgumentError`.

Every contact carries the metadata `[contact = true]`, its layer (`[layer = :home]`) unless
`:all`, and, for the conventions other than `PerContact`, `[rate_convention = :frequency]` or
`[rate_convention = :density, population = N]`; a user-set susceptible set that differs from
the inferred one is written as `[susceptible = …]`. Each labelled species carries its
[`SpeciesLabel`](@ref) as species metadata (the key is the type `SpeciesLabel`, as in
`Symbolics.getmetadata(S_a, SpeciesLabel, nothing)`), and the system metadata records the species
order of `cm`, which `contact_model` uses when it is a permutation of the species it finds
(otherwise it orders the species as the IR does), and the rate convention of `cm`, which is how a
model without contacts keeps it. For `DensityDependent(N)` with a number N the product β·N is
rounded, so each contact also records β as `[ir_rate = β]`, which `contact_model` reads back
when it reproduces the rate of the reaction exactly. So the round trip
`contact_model(Catalyst.ReactionSystem(cm))` is `isequivalent` to `cm` with the same species
order, susceptible set, convention, layers, labels and defaults (with κ = 1 for a `PerContact`
model; with another κ it is the scaled model c_κ P). Parameter defaults become
`initial_conditions` of the parameters; a default named like a species or `t` is not a parameter
value and is an `ArgumentError`. Parameters are recreated by name, so a symbolic rate must use
scalar parameters and time only: an element `k[1]` of an array, a function of time such as
`β(t)`, or two different variables with one name is an `ArgumentError`. With
`complete = true` (the default) the system is completed, like the output of
`@reaction_network`.
"""
function Catalyst.ReactionSystem(cm::ContactModel; κ = 1, name::Symbol = nameof(cm),
                                 complete::Bool = true)
    κ = _check_kappa(κ)
    t = Catalyst.default_t()
    conv = NEC.rate_convention(cm)
    cs = NEC.contacts(cm)
    ts = NEC.node_transitions(cm)
    sp = NEC.species_names(cm)
    spset = Set(sp)
    (κ isa Symbol && (κ in spset || κ === :t)) && throw(ArgumentError(
        "κ = :$(κ) names $(κ === :t ? "time" : "a species of :$(nameof(cm))"); use another " *
        "parameter name"))
    pnames = Symbol[]
    addp(n) = (n === :t || n in spset || n in pnames) || push!(pnames, n)
    for r in Iterators.flatten((cs, ts)), n in _rate_names(r.rate)
        addp(n)
    end
    conv isa DensityDependent && conv.N isa Symbol && addp(conv.N)
    defs = NEC.parameter_defaults(cm)
    _check_default_names(defs, spset, "the ContactModel :$(nameof(cm))")
    for n in sort!(collect(keys(defs)))
        addp(n)
    end
    # κ must be a fresh name: κ = :τ would turn the contact rate κτ into τ^2
    (κ isa Symbol && κ in pnames) && throw(ArgumentError(
        "κ = :$(κ) is already a parameter of :$(nameof(cm)) (its parameters: " *
        "$(join(pnames, ", "))); the mass-action contact rate κ·τ needs a new parameter name"))
    κ isa Symbol && addp(κ)
    labels = NEC.species_labels(cm)
    spv = _species(sp, t)
    for (x, l) in labels
        haskey(spv, x) && (spv[x] = Symbolics.setmetadata(spv[x], SpeciesLabel, l))
    end
    pv = _parameters(pnames)
    vars = Dict{Symbol,Any}(pv)
    vars[:t] = t
    κs = κ isa Symbol ? pv[κ] : κ
    Ns = conv isa DensityDependent ? (conv.N isa Symbol ? pv[conv.N] : conv.N) : nothing
    Σ = NEC.susceptible_species(cm)
    write_sus = Σ != NEC._infer_susceptible(cs)
    rxs = Catalyst.Reaction[]
    for c in cs
        r = _to_symbolic(c.rate, vars)
        k = conv isa PerContact ? (isequal(κs, 1) ? r : κs * r) :
            conv isa FrequencyDependent ? r : r * Ns
        md = Pair{Symbol,Any}[:contact => true]
        c.layer === :all || push!(md, :layer => c.layer)
        conv isa FrequencyDependent && push!(md, :rate_convention => :frequency)
        conv isa DensityDependent &&
            append!(md, Pair{Symbol,Any}[:rate_convention => :density, :population => conv.N])
        # r·N is rounded for a number N: record r, so that it is read back exactly
        conv isa DensityDependent && conv.N isa Real && push!(md, :ir_rate => c.rate)
        if write_sus && isempty(rxs)
            push!(md, :susceptible => copy(Σ))
        end
        subs = Any[spv[c.recipient], spv[c.infector]]
        prods, pst = c.product === c.infector ? (Any[spv[c.infector]], [2]) :
                     (Any[spv[c.product], spv[c.infector]], [1, 1])
        push!(rxs, Catalyst.Reaction(k, subs, prods, [1, 1], pst; metadata = md))
    end
    for tr in ts
        md = Pair{Symbol,Any}[]
        write_sus && isempty(rxs) && push!(md, :susceptible => copy(Σ))
        prods = tr.to === nothing ? nothing : Any[spv[tr.to]]
        push!(rxs, Catalyst.Reaction(_to_symbolic(tr.rate, vars), Any[spv[tr.from]], prods,
                                     [1], tr.to === nothing ? nothing : [1]; metadata = md))
    end
    ic = Dict{Any,Any}(pv[n] => v for (n, v) in defs if haskey(pv, n))
    rs = Catalyst.ReactionSystem(rxs, t, Any[spv[x] for x in sp], Any[pv[n] for n in pnames];
                                 name, initial_conditions = ic,
                                 metadata = Dict{DataType,Any}(_SpeciesOrder => copy(sp),
                                                               _Convention => conv))
    return complete ? Catalyst.complete(rs) : rs
end

"""
    Catalyst.ReactionSystem(d::ReactionNetworkData; name = nameof(d), complete = true)

A Catalyst reaction network for a general reaction network (DESIGN §A.2): the targets of the
reverse maps from the edge-based model to mass action, such as the edge doubling D_μ
([`edge_doubling`](@ref)), and power-law or general kinetics. Each [`GeneralReaction`](@ref)
keeps its stoichiometry and becomes a `-->` reaction, or a `=>` reaction (`only_use_rate`) whose
rate law may involve species. Observables that are not simply a species become `observed`
equations (`obs ~ X + Y`); parameter defaults become `initial_conditions` (a default named like a
species or `t` is an `ArgumentError`).
"""
function Catalyst.ReactionSystem(d::ReactionNetworkData; name::Symbol = nameof(d),
                                 complete::Bool = true)
    t = Catalyst.default_t()
    sp = NEC.species_names(d)
    spset = Set(sp)
    pnames = Symbol[]
    addp(n) = (n === :t || n in spset || n in pnames) || push!(pnames, n)
    for r in d.reactions, n in _rate_names(r.rate; species = spset)
        addp(n)
    end
    _check_default_names(d.defaults, spset, "the ReactionNetworkData :$(nameof(d))")
    for n in sort!(collect(keys(d.defaults)))
        addp(n)
    end
    spv = _species(sp, t)
    pv = _parameters(pnames)
    vars = merge(Dict{Symbol,Any}(spv), Dict{Symbol,Any}(pv))
    vars[:t] = t
    rxs = Catalyst.Reaction[]
    for r in d.reactions
        subs = isempty(r.substrates) ? nothing : Any[spv[x] for (x, _) in r.substrates]
        sst = isempty(r.substrates) ? nothing : Int[n for (_, n) in r.substrates]
        prods = isempty(r.products) ? nothing : Any[spv[x] for (x, _) in r.products]
        pst = isempty(r.products) ? nothing : Int[n for (_, n) in r.products]
        rate = _to_symbolic(r.rate, vars; species = spset)
        push!(rxs, Catalyst.Reaction(rate, subs, prods, sst, pst; only_use_rate = r.only_use_rate))
    end
    obs = Any[]
    for k in sort!(collect(keys(d.observables)))
        members = d.observables[k]
        if k in spset
            members == [k] && continue
            throw(ArgumentError("ReactionNetworkData :$(d.name): the observable $(k) has the " *
                                "name of a species but is the sum of $(join(members, ", "))"))
        end
        ov = only(Symbolics.@variables $(k)(t))
        push!(obs, ov ~ sum(spv[x] for x in members))
    end
    ic = Dict{Any,Any}(pv[n] => v for (n, v) in d.defaults if haskey(pv, n))
    rs = Catalyst.ReactionSystem(rxs, t, Any[spv[x] for x in sp], Any[pv[n] for n in pnames];
                                 name, initial_conditions = ic, observed = obs)
    return complete ? Catalyst.complete(rs) : rs
end

end # module NetworkEpiCoreCatalystExt
