# Owner: WP6 (DESIGN_NetworkEpiCore.md §A.2, §B.9, §D.5; work package in §G.2).
#
# General reaction networks: any stoichiometry and, optionally, a non-mass-action rate law.
# These are the targets of the reverse maps from the edge-based model to mass action: the edge
# doubling D_μ (M2, `edge_doubling`), Rempała's quotient E_μ (M3, returned as a ContactModel by
# `rempala_reduction`), power-law kinetics (M4) and general kinetics (M5). The Catalyst extension
# converts them with `Catalyst.ReactionSystem(::ReactionNetworkData; name)`.

export GeneralReaction, ReactionNetworkData

"""
    GeneralReaction(substrates, products, rate; only_use_rate = false, name)

A reaction `Σ a_i A_i → Σ b_j B_j` with any stoichiometry: `substrates` and `products` are
vectors of `species => stoichiometry` pairs (a bare species means stoichiometry 1; empty for ∅).
Under mass action its propensity is `rate · Π A_i^{a_i}`. With `only_use_rate = true`, `rate` is
the whole rate law (an `Expr` over [`RATE_OPS`](@ref) whose leaves may be species, parameters and
numbers, or a symbolic expression), as in Catalyst's `=>` reactions; this is how power-law and
general kinetics are written. `name` defaults to a readable form such as `:S_Φ_I_to_2Φ_I_I`.
"""
struct GeneralReaction
    substrates::Vector{Pair{Symbol,Int}}
    products::Vector{Pair{Symbol,Int}}
    rate::Any
    only_use_rate::Bool
    name::Symbol
    function GeneralReaction(substrates::AbstractVector, products::AbstractVector, rate,
                             only_use_rate::Bool, name::Symbol)
        subs = _stoich(substrates, name)
        prods = _stoich(products, name)
        (isempty(subs) && isempty(prods)) &&
            throw(ArgumentError("reaction `$(name)`: ∅ → ∅ does nothing"))
        return new(subs, prods, _checkrate(rate, name), only_use_rate, name)
    end
end

function GeneralReaction(substrates::AbstractVector, products::AbstractVector, rate;
                         only_use_rate::Bool = false,
                         name::Symbol = _default_general_name(substrates, products))
    return GeneralReaction(substrates, products, rate, only_use_rate, name)
end

function _stoich(v, name)
    out = Pair{Symbol,Int}[]
    for p in v
        x, n = p isa Pair ? (Symbol(first(p)), Int(last(p))) : (Symbol(p), 1)
        n >= 1 || throw(ArgumentError("reaction `$(name)`: stoichiometry of $(x) must be ≥ 1"))
        k = findfirst(q -> first(q) === x, out)
        k === nothing ? push!(out, x => n) : (out[k] = x => last(out[k]) + n)
    end
    return out
end

function _default_general_name(subs, prods)
    side(v) = isempty(v) ? "∅" :
              join((n == 1 ? string(x) : string(n, x) for (x, n) in _stoich(v, :reaction)), "_")
    return Symbol(side(subs), "_to_", side(prods))
end

"""
    ReactionNetworkData(name, species, reactions; defaults, provenance, observables)

A general reaction network (see [`GeneralReaction`](@ref)) over `species`: the target of the
reverse maps D_μ ([`edge_doubling`](@ref)), power-law and general kinetics. `observables` maps an
observable name to the species whose sum it is (for example `:I => [:I]` when `I` is a node
count and `Φ_I` an edge copy). Species are unique and every reaction refers to known species.
`defaults` are parameter values by name only: a default named like a species or `t` is an
`ArgumentError`, as for [`ContactModel`](@ref).
"""
struct ReactionNetworkData
    name::Symbol
    species::Vector{Symbol}
    reactions::Vector{GeneralReaction}
    defaults::Dict{Symbol,Float64}
    observables::Dict{Symbol,Vector{Symbol}}
    provenance::Provenance
    function ReactionNetworkData(name::Symbol, species::AbstractVector{Symbol},
                                 reactions::AbstractVector{GeneralReaction},
                                 defaults::AbstractDict, observables::AbstractDict,
                                 provenance::Provenance)
        sp = collect(Symbol, species)
        dup = _duplicates(sp)
        isempty(dup) || throw(ArgumentError("ReactionNetworkData :$(name): species are not " *
                                            "unique: $(_list(dup))"))
        known = Set(sp)
        for r in reactions, (x, _) in Iterators.flatten((r.substrates, r.products))
            x in known || throw(ArgumentError("ReactionNetworkData :$(name): reaction " *
                                              "`$(r.name)` refers to the unknown species $(x)"))
        end
        dupn = _duplicates([r.name for r in reactions])
        isempty(dupn) || throw(ArgumentError("ReactionNetworkData :$(name): reaction names " *
                                             "collide: $(_list(dupn))"))
        obs = Dict{Symbol,Vector{Symbol}}(Symbol(k) => collect(Symbol, v) for (k, v) in observables)
        for (k, v) in obs, x in v
            x in known || throw(ArgumentError("ReactionNetworkData :$(name): observable $(k) " *
                                              "refers to the unknown species $(x)"))
        end
        _validate_defaults("ReactionNetworkData :$(name)", keys(defaults), sp)
        defs = Dict{Symbol,Float64}(Symbol(k) => Float64(v) for (k, v) in defaults)
        return new(name, sp, collect(GeneralReaction, reactions), defs, obs, provenance)
    end
end

ReactionNetworkData(name::Symbol, species::AbstractVector{Symbol},
                    reactions::AbstractVector{GeneralReaction};
                    defaults::AbstractDict = Dict{Symbol,Float64}(),
                    observables::AbstractDict = Dict{Symbol,Vector{Symbol}}(),
                    provenance::Provenance = Provenance(:transform)) =
    ReactionNetworkData(name, species, reactions, defaults, observables, provenance)

species_names(d::ReactionNetworkData) = copy(d.species)
provenance(d::ReactionNetworkData) = d.provenance
Base.nameof(d::ReactionNetworkData) = d.name

"""
    rate_parameters(d::ReactionNetworkData) -> Vector

The parameters of the rates and rate laws of `d`, in order of first appearance (species that
appear in a rate law are not parameters).
"""
function rate_parameters(d::ReactionNetworkData)
    out = Any[]
    seen = Set{Symbol}()
    sp = Set(d.species)
    for r in d.reactions
        for p in rate_parameters(r.rate)
            n = _parameter_name(p)
            (n in seen || n in sp) || (push!(out, p); push!(seen, n))
        end
    end
    return out
end

function _side_string(v)
    isempty(v) && return "∅"
    return join((n == 1 ? string(x) : string(n, x) for (x, n) in v), " + ")
end

_reaction_string(r::GeneralReaction) =
    string(_rate_string(r.rate), ", ", _side_string(r.substrates),
           r.only_use_rate ? " => " : " --> ", _side_string(r.products))

Base.show(io::IO, r::GeneralReaction) = print(io, "GeneralReaction(", _reaction_string(r), ")")

Base.show(io::IO, d::ReactionNetworkData) =
    print(io, "ReactionNetworkData(:", d.name, "; ", length(d.species), " species, ",
          length(d.reactions), " reactions)")

function Base.show(io::IO, ::MIME"text/plain", d::ReactionNetworkData)
    print(io, "ReactionNetworkData :", d.name, "\n  species    ", join(d.species, "   "))
    for (k, r) in enumerate(d.reactions)
        print(io, "\n  ", k == 1 ? "reactions  " : "           ", "[", k, "] ", _reaction_string(r))
    end
    for (k, a) in enumerate(d.provenance.assumptions)
        print(io, "\n  ", k == 1 ? "notes      " : "           ", a)
    end
end
