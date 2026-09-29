# Owner: WP7 (DESIGN_NetworkEpiCore.md §E.2, §A.5; work package in §G.2).
#
# Seeding specifications shared by every back end (one rule everywhere, §E.2): SeedFraction,
# SeedCount and SeedNodes, the integer counts that NetworkOutbreaks places on nodes
# (`seed_counts`: RoundNearestTiesAway, errors instead of silent zero seeds or overfull
# populations; verified issue N01), the fractions that the deterministic back ends use
# (`seed_fractions`), and the default seeding rule (the unique entry state of the contacts).
# The field names and constructors of NetworkOutbreaks' former types are kept
# (`SeedFraction(:I => 0.01)`, `SeedNodes(:I => [1, 2]; default)`); NO re-exports these bindings.

export SeedSpec, SeedFraction, SeedCount, SeedNodes
export seed_counts, seed_fractions, default_seed, default_seed_state

"""
    SeedSpec

Abstract supertype of seeding specifications: [`SeedFraction`](@ref), [`SeedCount`](@ref) and
[`SeedNodes`](@ref). A specification names the compartments that start occupied; every other
node starts in the **background** compartment (normally the susceptible species): the `default`
field of the specification when it is set, otherwise the one the back end supplies
(`background` keyword of [`seed_counts`](@ref) and [`seed_fractions`](@ref)).
"""
abstract type SeedSpec end

const _SEED_TOL = sqrt(eps(Float64))

function _seed_check_names(names, what)
    dups = unique(n for n in names if count(==(n), names) > 1)
    isempty(dups) ||
        throw(ArgumentError("$what: compartment(s) $(join(repr.(dups), ", ")) appear more than once"))
    return nothing
end

"""
    SeedFraction(X => ρ_X, ...; default = nothing)
    SeedFraction(fractions::Vector{Pair{Symbol,Float64}}; default = nothing)

Seed a fraction ρ_X of the nodes in each named compartment X, chosen uniformly at random and
disjointly; the rest start in the background compartment (`default`, or the back end's). The
fractions must be finite, lie in [0, 1], name each compartment once and sum to at most 1 (within
√eps); if the background compartment itself is named, they must sum to 1.

Deterministic back ends use ρ_X directly (EB: θ(0) = 1, φ_X(0) = pop_X(0) = ρ_X,
q = 1 − Σρ). Stochastic back ends place [`seed_counts`](@ref) nodes: n_X = ρ_X N rounded to the
nearest integer, ties away from zero, and it is an **error** (never a silent zero seed) if a
positive ρ_X rounds to 0 or the counts exceed N. Scenarios require ρ_X N ∈ ℕ
(`seed_counts(…; exact = true)`), so both kinds of back end start from the same seeds.

On a `MultitypeNetwork` (a stratified model), `SeedFraction(:I_a => ρ)` is a fraction of **all**
N nodes, placed on nodes of type a, so the fraction within type a is ρ/n_a (§J.6); EB, pairwise
and NetworkOutbreaks all use this convention.
"""
struct SeedFraction <: SeedSpec
    fractions::Vector{Pair{Symbol,Float64}}
    default::Union{Symbol,Nothing}
    function SeedFraction(fractions::Vector{Pair{Symbol,Float64}}, default::Union{Symbol,Nothing})
        _seed_check_names([first(f) for f in fractions], "SeedFraction")
        for (X, ρ) in fractions
            (isfinite(ρ) && 0 <= ρ <= 1) ||
                throw(ArgumentError("SeedFraction for :$X must lie in [0, 1]; got $ρ"))
        end
        total = sum(last, fractions; init = 0.0)
        total <= 1 + _SEED_TOL ||
            throw(ArgumentError("SeedFraction: the fractions sum to $total > 1"))
        if default !== nothing && any(f -> first(f) === default, fractions)
            abs(total - 1) <= _SEED_TOL ||
                throw(ArgumentError("SeedFraction names its background compartment :$default, so " *
                                    "the fractions must sum to 1 (they sum to $total); unnamed " *
                                    "nodes are background"))
        end
        return new(copy(fractions), default)     # a copy: the caller's vector may change later
    end
end
SeedFraction(fractions::AbstractVector{<:Pair{Symbol,<:Real}}, default::Union{Symbol,Nothing}) =
    SeedFraction(Pair{Symbol,Float64}[X => Float64(ρ) for (X, ρ) in fractions], default)
SeedFraction(fractions::AbstractVector{<:Pair{Symbol,<:Real}}; default::Union{Symbol,Nothing} = nothing) =
    SeedFraction(fractions, default)
SeedFraction(pairs::Pair{Symbol,<:Real}...; default::Union{Symbol,Nothing} = nothing) =
    SeedFraction(Pair{Symbol,Float64}[X => Float64(ρ) for (X, ρ) in pairs], default)

"""
    SeedCount(X => n_X, ...; default = nothing)
    SeedCount(counts::Vector{Pair{Symbol,Int}}; default = nothing)

Seed exactly n_X nodes (integers ≥ 0, each compartment named once) in each named compartment,
chosen uniformly at random and disjointly; the rest start in the background compartment.
Deterministic back ends need the population size N to use it (ρ_X = n_X/N).
"""
struct SeedCount <: SeedSpec
    counts::Vector{Pair{Symbol,Int}}
    default::Union{Symbol,Nothing}
    function SeedCount(counts::Vector{Pair{Symbol,Int}}, default::Union{Symbol,Nothing})
        _seed_check_names([first(c) for c in counts], "SeedCount")
        for (X, n) in counts
            n >= 0 || throw(ArgumentError("SeedCount for :$X must be ≥ 0; got $n"))
        end
        return new(copy(counts), default)
    end
end
SeedCount(counts::AbstractVector{<:Pair{Symbol,<:Integer}}, default::Union{Symbol,Nothing}) =
    SeedCount(Pair{Symbol,Int}[X => Int(n) for (X, n) in counts], default)
SeedCount(counts::AbstractVector{<:Pair{Symbol,<:Integer}}; default::Union{Symbol,Nothing} = nothing) =
    SeedCount(counts, default)
SeedCount(pairs::Pair{Symbol,<:Integer}...; default::Union{Symbol,Nothing} = nothing) =
    SeedCount(Pair{Symbol,Int}[X => Int(n) for (X, n) in pairs], default)

"""
    SeedNodes(X => nodes, ...; default = nothing)
    SeedNodes(assignments::Vector{Pair{Symbol,Vector{Int}}}, default)

Explicit node assignments on a fixed graph (node indices ≥ 1; a node may be assigned only once);
every other node starts in `default` (or the back end's background compartment).
"""
struct SeedNodes <: SeedSpec
    assignments::Vector{Pair{Symbol,Vector{Int}}}
    default::Union{Symbol,Nothing}
    function SeedNodes(assignments::Vector{Pair{Symbol,Vector{Int}}}, default::Union{Symbol,Nothing})
        _seed_check_names([first(a) for a in assignments], "SeedNodes")
        seen = Set{Int}()
        for (X, nodes) in assignments
            for v in nodes
                v >= 1 || throw(ArgumentError("SeedNodes: node indices must be ≥ 1; got $v for :$X"))
                v in seen && throw(ArgumentError("SeedNodes: node $v is assigned more than once"))
                push!(seen, v)
            end
        end
        return new(Pair{Symbol,Vector{Int}}[X => copy(v) for (X, v) in assignments], default)
    end
end
SeedNodes(assignments::AbstractVector{<:Pair{Symbol,<:AbstractVector{<:Integer}}},
          default::Union{Symbol,Nothing}) =
    SeedNodes(Pair{Symbol,Vector{Int}}[X => Int.(collect(v)) for (X, v) in assignments], default)
SeedNodes(assignments::AbstractVector{<:Pair{Symbol,<:AbstractVector{<:Integer}}};
          default::Union{Symbol,Nothing} = nothing) = SeedNodes(assignments, default)
SeedNodes(pairs::Pair{Symbol,<:AbstractVector{<:Integer}}...; default::Union{Symbol,Nothing} = nothing) =
    SeedNodes(Pair{Symbol,Vector{Int}}[X => Int.(collect(v)) for (X, v) in pairs], default)

Base.:(==)(a::T, b::T) where {T<:Union{SeedFraction,SeedCount,SeedNodes}} = _net_fields_equal(a, b)
Base.hash(a::Union{SeedFraction,SeedCount,SeedNodes}, h::UInt) = _net_fields_hash(a, h)

_seed_background(seed::SeedSpec, background) = seed.default === nothing ? background : seed.default

# ---------------------------------------------------------------------------------------------
# Counts
# ---------------------------------------------------------------------------------------------

# n = ρN rounded to nearest, ties away from zero. A product within rounding error of a tie
# (0.035·100 = 3.5000000000000004) counts as a tie. `exact` requires ρN ∈ ℕ (scenarios).
function _seed_round(ρ::Float64, N::Integer, X::Symbol, exact::Bool)
    x = ρ * N
    if exact
        r = round(x)
        abs(x - r) <= 1e-9 * max(1.0, abs(x)) ||
            throw(ArgumentError("SeedFraction(:$X => $ρ) on N = $N nodes is not a whole number " *
                                "of nodes (ρN = $x); scenarios need ρN to be an integer"))
        return Int(r)
    end
    f = floor(x)
    abs(x - f - 0.5) <= 64 * eps(max(1.0, x)) && return Int(f) + 1
    return Int(round(x, RoundNearestTiesAway))
end

function _seed_zero_error(X, ρ, N)
    return ArgumentError("SeedFraction(:$X => $ρ) on N = $N nodes gives 0 nodes (ρN = $(ρ * N)); " *
                         "increase N or the fraction, or use SeedCount / SeedNodes")
end

"""
    seed_counts(seed::SeedSpec, N::Integer; background = nothing, exact = false)
        -> Vector{Pair{Symbol,Int}}

The integer number of nodes that start in each compartment when `seed` is applied to N nodes,
in the order of the specification. The background compartment (`seed.default`, else
`background`) is appended last with the remaining nodes and absorbs any rounding; without a
background only the named compartments are returned (the rest of the N nodes are background).

- `SeedFraction`: n_X = ρ_X N rounded to the nearest integer, ties away from zero
  (`RoundNearestTiesAway`; a product within rounding error of a tie counts as a tie). It is an
  `ArgumentError` if a positive ρ_X rounds to 0 or if the rounded counts exceed N. With
  `exact = true` every ρ_X N must be an integer (the `Scenario` rule of §E.2).
- `SeedCount`: the counts as given; they may not exceed N.
- `SeedNodes`: the numbers of listed nodes, which must lie in 1:N.

For example `seed_counts(SeedFraction(:I => 0.001), 500) == [:I => 1]`, while N = 499 is an
error, and `seed_counts(SeedFraction(:S => 0.9, :I => 0.1), 25; background = :S) ==
[:I => 3, :S => 22]`.
"""
function seed_counts(seed::SeedFraction, N::Integer; background::Union{Symbol,Nothing} = nothing,
                     exact::Bool = false)
    N >= 0 || throw(ArgumentError("seed_counts: N must be ≥ 0; got $N"))
    bg = _seed_background(seed, background)
    out = Pair{Symbol,Int}[]
    assigned = 0
    for (X, ρ) in seed.fractions
        X === bg && continue
        n = _seed_round(ρ, N, X, exact)
        (ρ > 0 && n == 0 && N > 0) && throw(_seed_zero_error(X, ρ, N))
        push!(out, X => n)
        assigned += n
    end
    if assigned > N
        # the advice depends on where the overflow comes from: a named background compartment
        # can absorb the rounding, several rounded-up seeds cannot
        named_bg = bg !== nothing && any(f -> first(f) === bg, seed.fractions)
        advice = bg === nothing ?
                 "pass the background compartment as `background` (or leave it unnamed) so " *
                 "that it absorbs the rounding" :
                 named_bg ? "leave the background compartment :$bg unnamed so that it absorbs " *
                            "the rounding" :
                 "the seeds alone round to more than N: use SeedCount for exact counts, or " *
                 "fractions whose ρN are integers"
        throw(ArgumentError("SeedFraction on N = $N nodes rounds to $assigned seeded nodes, more " *
                            "than N ($(join(("$X => $n" for (X, n) in out), ", "))); $advice"))
    end
    if bg !== nothing
        rest = N - assigned
        i = findfirst(f -> first(f) === bg, seed.fractions)
        if i !== nothing
            ρbg = last(seed.fractions[i])
            total = sum(last, seed.fractions)
            abs(total - 1) <= _SEED_TOL ||
                throw(ArgumentError("SeedFraction names the background compartment :$bg, so the " *
                                    "fractions must sum to 1 (they sum to $total); unnamed nodes " *
                                    "are background"))
            (ρbg > 0 && rest == 0 && N > 0) && throw(_seed_zero_error(bg, ρbg, N))
            exact && _seed_round(ρbg, N, bg, true)
        end
        push!(out, bg => rest)
    end
    return out
end

function seed_counts(seed::SeedCount, N::Integer; background::Union{Symbol,Nothing} = nothing,
                     exact::Bool = false)
    N >= 0 || throw(ArgumentError("seed_counts: N must be ≥ 0; got $N"))
    bg = _seed_background(seed, background)
    out = Pair{Symbol,Int}[X => n for (X, n) in seed.counts if X !== bg]
    assigned = sum(last, out; init = 0)
    assigned <= N ||
        throw(ArgumentError("SeedCount seeds $assigned nodes, more than N = $N"))
    if bg !== nothing
        rest = N - assigned
        i = findfirst(c -> first(c) === bg, seed.counts)
        if i !== nothing && last(seed.counts[i]) != rest
            throw(ArgumentError("SeedCount names the background compartment :$bg with " *
                                "$(last(seed.counts[i])) nodes, but N − (other seeds) = $rest"))
        end
        push!(out, bg => rest)
    end
    return out
end

function seed_counts(seed::SeedNodes, N::Integer; background::Union{Symbol,Nothing} = nothing,
                     exact::Bool = false)
    N >= 0 || throw(ArgumentError("seed_counts: N must be ≥ 0; got $N"))
    for (X, nodes) in seed.assignments, v in nodes
        v <= N || throw(ArgumentError("SeedNodes: node $v (compartment :$X) is out of range 1:$N"))
    end
    bg = _seed_background(seed, background)
    out = Pair{Symbol,Int}[X => length(nodes) for (X, nodes) in seed.assignments if X !== bg]
    bg === nothing && return out
    push!(out, bg => N - sum(last, out; init = 0))    # listed background nodes + unassigned ones
    return out
end

# ---------------------------------------------------------------------------------------------
# Fractions
# ---------------------------------------------------------------------------------------------

"""
    seed_fractions(seed::SeedSpec; N = nothing, background = nothing) -> Vector{Pair{Symbol,Float64}}

The initial fraction of nodes in each named compartment, for the deterministic back ends, in the
order of the specification; the background compartment (`seed.default`, else `background`) is
appended last with 1 − Σ ρ_X when known. `SeedFraction` returns its ρ_X exactly (N is not
needed); `SeedCount` and `SeedNodes` need N and return n_X/N.
"""
function seed_fractions(seed::SeedFraction; N::Union{Nothing,Integer} = nothing,
                        background::Union{Symbol,Nothing} = nothing)
    bg = _seed_background(seed, background)
    out = Pair{Symbol,Float64}[X => ρ for (X, ρ) in seed.fractions if X !== bg]
    bg === nothing && return out
    if any(f -> first(f) === bg, seed.fractions)
        total = sum(last, seed.fractions)
        abs(total - 1) <= _SEED_TOL ||
            throw(ArgumentError("SeedFraction names the background compartment :$bg, so the " *
                                "fractions must sum to 1 (they sum to $total)"))
    end
    push!(out, bg => max(0.0, 1 - sum(last, out; init = 0.0)))
    return out
end
function seed_fractions(seed::Union{SeedCount,SeedNodes}; N::Union{Nothing,Integer} = nothing,
                        background::Union{Symbol,Nothing} = nothing)
    N === nothing &&
        throw(ArgumentError("seed_fractions($(nameof(typeof(seed)))) needs the population size N"))
    N > 0 || throw(ArgumentError("seed_fractions: N must be > 0; got $N"))
    return Pair{Symbol,Float64}[X => n / N for (X, n) in seed_counts(seed, N; background)]
end

# ---------------------------------------------------------------------------------------------
# The default seeding rule (§E.2): the unique entry state of the contacts
# ---------------------------------------------------------------------------------------------

"""
    default_seed_state(cm::ContactModel) -> Symbol

The compartment seeded by default (§E.2, decision H7): the **unique entry state** into
infection, i.e. the unique product of the contacts that are infections (§J.8: a contact from a
susceptible class into the infection chain; see [`infected_species`](@ref)): I for SIR, E for
SEIR, I₁ after Erlang staging, and I for a model with contact tracing (the traced Q of
S + I → Q + I is not infected, so it is not an entry into infection). In a
reinfection-counted model ([`with_reinfection_counting`](@ref)) the population starts
uninfected, so the entry is the one reached from the count-0 susceptible classes (I_1 for SIS).
A model with several such entry states (two strains, stratified models) or none needs an
explicit `initial`, and this function throws an `ArgumentError` saying so.
"""
function default_seed_state(cm::ContactModel)
    return first(_default_seed_entry(cm))
end

# The default entry state and its background compartment (the susceptible class the seeds leave,
# when that is unique), or an ArgumentError.
function _default_seed_entry(cm::ContactModel)
    Σ, chain = Set(cm.susceptible), _infection_chain(cm)
    infections = [c for c in cm.contacts if _is_infection(c, Σ, chain)]
    if _is_reinfection_counted(cm)
        # a fresh population: every node has count 0, so infections start from count-0 classes
        infections = [c for c in infections if infection_count_of(cm, c.recipient) == 0]
    end
    entries = unique!(Symbol[c.product for c in infections])
    isempty(entries) &&
        throw(ArgumentError("model :$(cm.name) has no infection (a contact from a susceptible " *
                            "class into the infection chain), so it has no entry state to seed " *
                            "by default; pass an explicit `initial`, e.g. SeedFraction(:X => ρ)"))
    length(entries) == 1 ||
        throw(ArgumentError("model :$(cm.name) has several entry states " *
                            "($(join(entries, ", "))), so there is no default seed; pass an " *
                            "explicit `initial`, e.g. SeedFraction(" *
                            join(("$(repr(X)) => ρ_$X" for X in entries), ", ") * ")"))
    sources = unique!(Symbol[c.recipient for c in infections])
    sus = _is_reinfection_counted(cm) ? sources : cm.susceptible
    return only(entries), (length(sus) == 1 ? only(sus) : nothing)
end

"""
    default_seed(cm::ContactModel, ρ::Real) -> SeedFraction

The default seeding of `cm` with fraction ρ: `SeedFraction(default_seed_state(cm) => ρ)`, with
the susceptible class as the explicit background compartment when it is unique (the count-0
class of a reinfection-counted model). Used by `default_initial_conditions` and the factories
when no `initial` is given.
"""
function default_seed(cm::ContactModel, ρ::Real)
    X, bg = _default_seed_entry(cm)
    return SeedFraction(X => ρ; default = bg)
end

# ---------------------------------------------------------------------------------------------
# Canonical text
# ---------------------------------------------------------------------------------------------

canonical_text(io::IO, s::SeedFraction) =
    _netct_struct(io, "SeedFraction", :fractions => s.fractions, :default => s.default)
canonical_text(io::IO, s::SeedCount) =
    _netct_struct(io, "SeedCount", :counts => s.counts, :default => s.default)
canonical_text(io::IO, s::SeedNodes) =
    _netct_struct(io, "SeedNodes", :assignments => s.assignments, :default => s.default)

"""
    canonical_text(seed::SeedSpec) -> String

Canonical text of a seeding specification (§E.4), in the order of the specification, for
example `SeedFraction(fractions=[:I => 0.01], default=nothing)`.
"""
canonical_text(s::SeedSpec) = sprint(canonical_text, s)
