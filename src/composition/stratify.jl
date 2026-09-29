# Owner: WP8 (DESIGN_NetworkEpiCore.md §B.9, §D.2; work package in §G.2).
#
# Strata, strata(names; sizes), and the ContactModel method of the generics.jl stub `stratify`:
# the typed product P ×_T Q over T_net (Libkind et al. 2022, §3.2, a pullback of typed Petri
# nets). Q is the strata net: one species per stratum, contacts a + b → a + b between every pair
# of strata (weighted by `contact_rates`) and no transitions between strata, since strata are
# fixed node attributes, as in configuration networks and NetworkOutbreaks graphs.
#
# The syntax is only half of a stratified model: its network semantics needs a network typed over
# the same strata (`sbm_network`, `unstructured` in networks/descriptors.jl), which carries the
# degree distribution and the strata sizes, and checks edge reciprocity. The EdgeBasedModels 0.1
# `stratify(::OpenEBCM, …)` replaced every degree distribution by a Poisson law with the same mean
# and had no strata sizes (issue E24); here the degree law never passes through `stratify`.
#
# Include order: after ir/types.jl, ir/reaction_data.jl, networks/degrees.jl and
# networks/multivariate.jl, and BEFORE networks/descriptors.jl (whose sbm_network and
# unstructured take a Strata) and before ir/rates.jl, ir/typing.jl and ir/transforms.jl.
# Only types from the earlier files may appear in signatures and struct fields here; functions
# from later files (rate_mul, _derived_contact, ...) are called inside function bodies. The
# OpenContactModel method of `stratify` lives in composition/open.jl.

export Strata, strata

# ---------------------------------------------------------------------------------------------
# Strata
# ---------------------------------------------------------------------------------------------

"""
    Strata(names, sizes)

A set of strata (fixed node attributes such as age groups or locations): their `names` and their
population fractions `sizes` (positive, summing to 1). Build it with [`strata`](@ref).

A `Strata` is read by [`stratify`](@ref) (the syntax: species `X_a`, contacts between strata,
labels) and by the typed-network constructors `sbm_network(st; mean_contacts)` and
`unstructured(net, st)` (the semantics: a `MultitypeNetwork` with node types `names` and type
fractions `sizes`, which checks edge reciprocity n_a E[k_{a→b}] = n_b E[k_{b→a}]).

The fields `names::Vector{Symbol}` and `sizes::Vector{Float64}` are public.
"""
struct Strata
    names::Vector{Symbol}
    sizes::Vector{Float64}
    function Strata(names::AbstractVector, sizes::AbstractVector{<:Real})
        ns = Symbol[Symbol(a) for a in names]
        isempty(ns) && throw(ArgumentError("strata: at least one stratum is needed"))
        dup = _duplicates(ns)
        isempty(dup) || throw(ArgumentError("strata: the stratum names are not unique: " *
                                            "$(_list(dup))"))
        :all in ns && throw(ArgumentError(
            "strata: :all is reserved (it is the stratum of an unstratified species, " *
            "SpeciesLabel(...; stratum = :all)); choose another stratum name"))
        length(sizes) == length(ns) || throw(ArgumentError(
            "strata: $(length(sizes)) sizes for the $(length(ns)) strata $(_list(ns))"))
        all(x -> isfinite(x) && x > 0, sizes) || throw(ArgumentError(
            "strata: sizes must be finite and > 0 (they are population fractions); got " *
            "$(collect(sizes))"))
        total = sum(Float64, sizes)
        isapprox(total, 1.0; rtol = 1e-8) || throw(ArgumentError(
            "strata: sizes are population fractions and must sum to 1; got sum = $(total) for " *
            "$(collect(sizes)) (for counts pass sizes ./ sum(sizes))"))
        return new(ns, Float64[x / total for x in sizes])
    end
end

"""
    strata(names; sizes = fill(1/length(names), length(names))) -> Strata

The [`Strata`](@ref) `names` (Symbols, unique, not `:all`) with population fractions `sizes`
(finite, positive and summing to 1 within 10⁻⁸; they are renormalised exactly). The default is
equal sizes.

```julia
age = strata([:y, :o]; sizes = [0.4, 0.6])
sir_age = stratify(sir_model(), age; contact_rates = (a, b) -> a == b ? :τw : :τb)
net = sbm_network(age; mean_contacts = [6.0 3.0; 2.0 4.0])     # 0.4·3 == 0.6·2 (reciprocity)
```
"""
function strata(names::AbstractVector; sizes::Union{Nothing,AbstractVector{<:Real}} = nothing)
    K = length(names)
    return Strata(names, sizes === nothing ? fill(1 / max(K, 1), K) : sizes)
end

Base.length(st::Strata) = length(st.names)
Base.:(==)(a::Strata, b::Strata) = a.names == b.names && a.sizes == b.sizes
Base.hash(st::Strata, h::UInt) = hash(st.sizes, hash(st.names, hash(:Strata, h)))

function Base.show(io::IO, st::Strata)
    print(io, "strata([", join((repr(a) for a in st.names), ", "), "]; sizes = [",
          join((_number_string(x) for x in st.sizes), ", "), "])")
end

canonical_text(io::IO, st::Strata) =
    _netct_struct(io, "Strata", :names => st.names, :sizes => st.sizes)
canonical_text(st::Strata) = sprint(canonical_text, st)

# ---------------------------------------------------------------------------------------------
# stratify
# ---------------------------------------------------------------------------------------------

# Name of the species X in stratum a. With a single stratum the typed product with the one-point
# strata net is the identity, so names are kept (only the labels record the stratum).
_strat_name(X::Symbol, a::Symbol, K::Int) = K == 1 ? X : Symbol(X, :_, a)
_strat_name(::Nothing, a::Symbol, K::Int) = nothing

# The label of (X, a): base, count and stage are those of X; the stratum is a, or the pair
# `<old>_a` when X is already stratified (a product of strata, e.g. age × sex).
function _strat_label(cm::ContactModel, X::Symbol, a::Symbol)
    l = get(cm.labels, X, nothing)
    l === nothing && return SpeciesLabel(X, a, 0, 0)
    stratum = l.stratum === :all ? a : Symbol(l.stratum, :_, a)
    return SpeciesLabel(l.base, stratum, l.count, l.stage)
end

# A rate that is exactly 0: a number, or a symbolic expression that folds to the constant 0
# (rate_mul(0.0, τ) with a Symbolics τ is a symbolic 0, WP8 review), so that the reaction is a
# structural zero and not created. A symbolic rate with parameters or time is never taken for 0.
_is_zero_rate(r) = _isnum(r) ? iszero(r) : _issymbolic(r) && _is_constant_zero(r)
function _is_constant_zero(r)
    (isempty(rate_parameters(r)) && !_uses_time(r)) || return false
    v = rate_value(r)
    return _isnum(v) && iszero(v)
end

_rates_spec_label(spec::Symbol) = ":$(spec)"
_rates_spec_label(::AbstractDict) = "a Dict"
_rates_spec_label(::AbstractMatrix) = "a matrix of multipliers"
_rates_spec_label(::Function) = "a function"
_rates_spec_label(x) = repr(x)

# --- contact rates ----------------------------------------------------------------------------

function _check_contact_rates_spec(cm::ContactModel, st::Strata, spec, where)
    K = length(st)
    if spec isa Symbol
        spec === :same || throw(ArgumentError(
            "$(where): contact_rates must be :same, a Dict, a $(K)×$(K) matrix of multipliers " *
            "or a function; got :$(spec)"))
    elseif spec isa AbstractMatrix
        size(spec) == (K, K) || throw(ArgumentError(
            "$(where): contact_rates is a $(size(spec, 1))×$(size(spec, 2)) matrix; it must be " *
            "$(K)×$(K) (rows: the recipient's stratum, columns: the infector's; strata " *
            "$(_list(st.names)))"))
        for x in spec          # multipliers: numbers ≥ 0, or rates (a product with τ is formed)
            if _isnum(x)
                (isfinite(x) && x >= 0) || throw(ArgumentError(
                    "$(where): contact_rates multipliers must be finite and ≥ 0; got $(x)"))
            else
                _checkrate(x)
            end
        end
    elseif spec isa AbstractDict
        names = Set(c.name for c in cm.contacts)
        strata_set = Set(st.names)
        bad = Any[]
        for k in keys(spec)
            ok = (k isa Tuple{Symbol,Symbol} && all(in(strata_set), k)) ||
                 (k isa Tuple{Symbol,Symbol,Symbol} && k[1] in names &&
                  k[2] in strata_set && k[3] in strata_set)
            ok || push!(bad, k)
        end
        isempty(bad) || throw(ArgumentError(
            "$(where): contact_rates has the key(s) $(join(repr.(bad), ", ")); keys are " *
            "(a, b) or (contact name, a, b) with a the recipient's stratum and b the " *
            "infector's, over the strata $(_list(st.names)) and the contacts " *
            "$(_list([c.name for c in cm.contacts]))"))
        if any(k -> k isa Tuple{Symbol,Symbol}, keys(spec)) && length(cm.contacts) > 1
            throw(ArgumentError(
                "$(where): contact_rates keys (a, b) are ambiguous for a model with " *
                "$(length(cm.contacts)) contacts ($(_list([c.name for c in cm.contacts]))); key " *
                "the rates by (contact name, a, b)"))
        end
    elseif !(spec isa Function)
        throw(ArgumentError("$(where): contact_rates must be :same, a Dict, a $(K)×$(K) " *
                            "matrix of multipliers or a function; got $(repr(spec))"))
    end
    return nothing
end

function _stratum_contact_rate(cm::ContactModel, spec, c::Contact, i, j, st::Strata, where)
    a, b = st.names[i], st.names[j]
    spec === :same && return c.rate
    spec isa AbstractMatrix && return rate_mul(spec[i, j], c.rate)
    if spec isa AbstractDict
        haskey(spec, (c.name, a, b)) && return spec[(c.name, a, b)]
        haskey(spec, (a, b)) && return spec[(a, b)]
        throw(ArgumentError(
            "$(where): contact_rates has no rate for the contact `$(c.name)` from stratum " *
            "$(b) to stratum $(a) (key ($(repr(c.name)), $(repr(a)), $(repr(b)))" *
            (length(cm.contacts) == 1 ? " or ($(repr(a)), $(repr(b)))" : "") *
            "); give every pair, with 0 for no contact"))
    end
    # a function: (c, a, b) -> rate for any model; (a, b) -> rate for a single-contact model
    applicable(spec, c, a, b) && return spec(c, a, b)
    if applicable(spec, a, b)
        length(cm.contacts) == 1 || throw(ArgumentError(
            "$(where): contact_rates = (a, b) -> rate is ambiguous for a model with " *
            "$(length(cm.contacts)) contacts ($(_list([x.name for x in cm.contacts]))); pass " *
            "(c, a, b) -> rate, where c is the Contact (e.g. " *
            "`(c, a, b) -> a == b ? c.rate : rate_mul(0.5, c.rate)`)"))
        return spec(a, b)
    end
    throw(ArgumentError("$(where): contact_rates must accept (c::Contact, a, b) or (a, b)"))
end

# --- transition rates -------------------------------------------------------------------------

function _check_transition_rates_spec(cm::ContactModel, st::Strata, spec, where)
    if spec isa Symbol
        spec === :same || throw(ArgumentError(
            "$(where): transition_rates must be :same, a Dict or a function; got :$(spec)"))
    elseif spec isa AbstractDict
        names = Set(t.name for t in cm.transitions)
        strata_set = Set(st.names)
        bad = Any[]
        for k in keys(spec)
            ok = (k isa Symbol && k in strata_set) ||
                 (k isa Tuple{Symbol,Symbol} && k[1] in names && k[2] in strata_set)
            ok || push!(bad, k)
        end
        isempty(bad) || throw(ArgumentError(
            "$(where): transition_rates has the key(s) $(join(repr.(bad), ", ")); keys are a " *
            "stratum a or (transition name, a), over the strata $(_list(st.names)) and the " *
            "transitions $(_list([t.name for t in cm.transitions]))"))
        if any(k -> k isa Symbol, keys(spec)) && length(cm.transitions) > 1
            throw(ArgumentError(
                "$(where): transition_rates keys a are ambiguous for a model with " *
                "$(length(cm.transitions)) transitions ($(_list([t.name for t in cm.transitions]))); " *
                "key the rates by (transition name, a)"))
        end
    elseif !(spec isa Function)
        throw(ArgumentError("$(where): transition_rates must be :same, a Dict or a function; " *
                            "got $(repr(spec))"))
    end
    return nothing
end

function _stratum_transition_rate(cm::ContactModel, spec, t::NodeTransition, a::Symbol, where)
    spec === :same && return t.rate
    if spec isa AbstractDict
        haskey(spec, (t.name, a)) && return spec[(t.name, a)]
        haskey(spec, a) && return spec[a]
        throw(ArgumentError(
            "$(where): transition_rates has no rate for the transition `$(t.name)` in stratum " *
            "$(a) (key ($(repr(t.name)), $(repr(a)))" *
            (length(cm.transitions) == 1 ? " or $(repr(a))" : "") *
            "); give every stratum, with 0 for no transition"))
    end
    applicable(spec, t, a) && return spec(t, a)
    if applicable(spec, a)
        length(cm.transitions) == 1 || throw(ArgumentError(
            "$(where): transition_rates = a -> rate is ambiguous for a model with " *
            "$(length(cm.transitions)) transitions ($(_list([x.name for x in cm.transitions]))); " *
            "pass (t, a) -> rate, where t is the NodeTransition"))
        return spec(a)
    end
    throw(ArgumentError("$(where): transition_rates must accept (t::NodeTransition, a) or (a)"))
end

"""
    stratify(cm::ContactModel, st::Strata; contact_rates = :same, transition_rates = :same,
             name = Symbol(nameof(cm), :_strat)) -> ContactModel
    stratify(cm::ContactModel, names::AbstractVector{Symbol}; kw...)   # equal sizes

Stratify `cm` by the fixed node attributes `st`: the typed product P ×_T Q over T_net (Libkind
et al. 2022, §3.2), where the strata net Q has one species per stratum, contacts a + b → a + b
between every pair of strata and **no transitions between strata**.

- **Species.** (X, a) for every species X and stratum a, named `X_a` (`S_y`, `I_o`, …), with the
  label `SpeciesLabel(base(X); stratum = a)` (count and stage are kept; a species that is already
  stratified gets the stratum `<old>_a`, so stratifying twice gives the product of the strata).
  The susceptible classes are the (s, a) with s susceptible.
- **Contacts.** Each contact `s + J → X + J` gives, for every recipient stratum a and infector
  stratum b, `(s,a) + (J,b) → (X,a) + (J,b)` at the rate from `contact_rates`:
  - `:same`: the rate of the contact;
  - a function `(a, b) -> rate` (single-contact models) or `(c::Contact, a, b) -> rate`,
    evaluated now (the result is stored, not the function);
  - a `Dict` keyed by `(a, b)` (single-contact models) or `(contact name, a, b)`; every pair
    must be given;
  - a K×K matrix M of multipliers: the rate is M[a, b]·τ_r.
- **Transitions.** Each transition `X → Y | ∅` gives `(X,a) → (Y,a) | ∅` in every stratum at the
  rate from `transition_rates`: `:same`, a function `a -> rate` (single-transition models) or
  `(t::NodeTransition, a) -> rate`, or a `Dict` keyed by `a` (single-transition models) or
  `(transition name, a)`.
- A numeric rate of 0 is a structural zero: that reaction is not created.

Every reaction keeps its type (the product is taken over the type theory), so a T_EB model gives
a T_EB model with one susceptible class per stratum, which the edge-based model accepts on a
`MultitypeNetwork` with node types `st.names` (`sbm_network(st; mean_contacts)`,
`unstructured(net, st)`). The degree distributions and the strata sizes belong to that network,
never to the model. With a single stratum the result is the identity (`isequivalent(stratify(cm,
strata([:a])), cm)`): the species keep their names and only the labels record the stratum; this is
the syntactic side of the unit law M10.

The rate convention and parameter defaults are kept (stratified contacts should be `PerContact`
on a `MultitypeNetwork`; see `per_contact_rates`). Under mass action with `:same` rates the sums
Σ_a x_{X,a} evolve exactly as the unstratified model (the product lumps back to `cm`).
"""
function stratify(cm::ContactModel, st::Strata; contact_rates = :same,
                  transition_rates = :same, name::Symbol = Symbol(cm.name, :_strat))
    where = "stratify(:$(cm.name), $(st))"
    _check_contact_rates_spec(cm, st, contact_rates, where)
    _check_transition_rates_spec(cm, st, transition_rates, where)
    K = length(st)
    S(X, a) = _strat_name(X, a, K)

    species = Symbol[S(X, a) for X in cm.species for a in st.names]
    dup = _duplicates(species)
    isempty(dup) || throw(ArgumentError(
        "$(where): the stratified species names $(_list(dup)) are generated twice (from species " *
        "and strata whose names contain underscores); relabel the model or rename the strata"))
    sus = Symbol[S(X, a) for X in cm.susceptible for a in st.names]
    labels = Dict{Symbol,SpeciesLabel}(S(X, a) => _strat_label(cm, X, a)
                                       for X in cm.species for a in st.names)

    cs = Contact[]
    cmap = Int[]
    zeros_dropped = 0
    for (k, c) in enumerate(cm.contacts), i in 1:K, j in 1:K
        a, b = st.names[i], st.names[j]
        r = _stratum_contact_rate(cm, contact_rates, c, i, j, st, where)
        if _is_zero_rate(r)
            zeros_dropped += 1
            continue
        end
        push!(cs, _derived_contact(c, S(c.recipient, a), S(c.infector, b), S(c.product, a), r,
                                   K == 1 ? nothing : Symbol(:_, a, :_, b)))
        push!(cmap, k)
    end
    ts = NodeTransition[]
    tmap = Int[]
    nc = length(cm.contacts)
    for (k, t) in enumerate(cm.transitions), a in st.names
        r = _stratum_transition_rate(cm, transition_rates, t, a, where)
        if _is_zero_rate(r)
            zeros_dropped += 1
            continue
        end
        push!(ts, _derived_transition(t, S(t.from, a), S(t.to, a), r,
                                      K == 1 ? nothing : Symbol(:_, a)))
        push!(tmap, nc + k)
    end

    sizes = join((_number_string(x) for x in st.sizes), ", ")
    note = "stratify: typed product over T_net with the strata $(_list(st.names)) (sizes " *
           "$(sizes)); contacts (s,a) + (J,b) → (X,a) + (J,b), transitions (X,a) → (Y,a), no " *
           "transitions between strata; contact_rates = $(_rates_spec_label(contact_rates)), " *
           "transition_rates = $(_rates_spec_label(transition_rates))" *
           (zeros_dropped == 0 ? "" : "; $(zeros_dropped) zero-rate reaction(s) not created")
    return _rebuild(cm; name, species, susceptible = sus, contacts = cs, transitions = ts,
                    labels, provenance = _transform_provenance(cm, note, vcat(cmap, tmap)))
end

stratify(cm::ContactModel, names::AbstractVector{Symbol}; kw...) =
    stratify(cm, strata(names); kw...)
