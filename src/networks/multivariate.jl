# Owner: WP7 (DESIGN_NetworkEpiCore.md §C.2; work package in §G.2).
#
# Multivariate degree laws: the joint law of the numbers (k_{a→b})_b of edges from a node of
# type a to nodes of each partner type b, with the joint PGF ψ_a(x) = E[Π_b x_b^{k_{a→b}}] and
# its partial derivatives (closed form, generic in x). Used by `MultitypeNetwork` (typed and
# stratified networks, `sbm_network`, `unstructured`) and by the degree-correlated descriptor.

export MultivariateDegree, IndependentDegrees, SplitDegrees, partner_types

"""
    MultivariateDegree

Abstract supertype of the law of (k_{a→b})_b, the numbers of edges from a node of type a to
nodes of each partner type b. Implementations: [`IndependentDegrees`](@ref) and
[`SplitDegrees`](@ref). Every law implements:

- [`partner_types`](@ref)`(m)`;
- [`pgf`](@ref)`(m, x)` = ψ_a(x) and [`pgf_derivative`](@ref)`(m, x, b, c, …)` =
  ∂_b ∂_c ⋯ ψ_a(x), where `x` maps partner types to values: an `AbstractDict{Symbol}`, a
  `NamedTuple` or a function `b -> x_b` (values may be `Real`, `Symbolics.Num` or dual numbers);
- [`mean_degree`](@ref)`(m, b)` = E[k_{a→b}] = ∂_b ψ_a(1), and `mean_degree(m)` = E[Σ_b k_{a→b}];
- `rand(rng, m)`: a `Vector{Int}` of edge counts aligned with `partner_types(m)`;
- [`canonical_text`](@ref).

A partner type that `m` does not mention has k_{a→b} ≡ 0 (a structural zero).
"""
abstract type MultivariateDegree end

"""
    IndependentDegrees(b₁ => d₁, b₂ => d₂, ...)
    IndependentDegrees(parts::Vector{Pair{Symbol,DegreeDistribution}})

Independent numbers of edges to each partner type: k_{a→b} ~ d_b independently, so
ψ_a(x) = Π_b ψ_{d_b}(x_b) and ∂_b ψ_a(1) = ⟨d_b⟩. `IndependentDegrees()` has no edges.
`sbm_network` builds these (Poisson blocks by default).
"""
struct IndependentDegrees <: MultivariateDegree
    parts::Vector{Pair{Symbol,DegreeDistribution}}
    function IndependentDegrees(parts::Vector{Pair{Symbol,DegreeDistribution}})
        _net_check_unique([first(p) for p in parts], "IndependentDegrees: partner type")
        return new(copy(parts))       # a copy: the caller's vector may change later
    end
end
IndependentDegrees(parts::AbstractVector{<:Pair{Symbol,<:DegreeDistribution}}) =
    IndependentDegrees(Pair{Symbol,DegreeDistribution}[p for p in parts])
IndependentDegrees(parts::Pair{Symbol,<:DegreeDistribution}...) =
    IndependentDegrees(Pair{Symbol,DegreeDistribution}[parts...])

"""
    SplitDegrees(total::DegreeDistribution, b₁ => w₁, b₂ => w₂, ...)
    SplitDegrees(total, weights::Vector{Pair{Symbol,Float64}})

A node draws its total degree k ~ `total` and splits its k stubs multinomially over the partner
types with probabilities w_b (finite, ≥ 0, summing to 1 within 1e-8; normalised). Hence
ψ_a(x) = ψ(Σ_b w_b x_b), ∂_b ψ_a(1) = w_b ⟨k⟩ and ∂_b ∂_c ψ_a(1) = w_b w_c ψ''(1): the
degree distribution of the node is preserved exactly (the thinning pull-back of the verified
issue E24). `unstructured(net, strata)` uses w_b = n_b; the degree-correlated descriptor uses
w_l = Q(l | k). Empty weights are allowed only when `total` has mean degree 0.
"""
struct SplitDegrees <: MultivariateDegree
    total::DegreeDistribution
    weights::Vector{Pair{Symbol,Float64}}
    function SplitDegrees(total::DegreeDistribution, weights::Vector{Pair{Symbol,Float64}})
        _net_check_unique([first(w) for w in weights], "SplitDegrees: partner type")
        all(w -> isfinite(last(w)) && last(w) >= 0, weights) ||
            throw(ArgumentError("SplitDegrees: weights must be finite and ≥ 0; got $weights"))
        if isempty(weights)
            _net_iszero_numeric(mean_degree(total)) ||
                throw(ArgumentError("SplitDegrees: no partner types for a total degree with " *
                                    "mean $(mean_degree(total))"))
            return new(total, weights)
        end
        s = sum(last, weights)
        isapprox(s, 1; atol = 1e-8) ||
            throw(ArgumentError("SplitDegrees: the weights must sum to 1; they sum to $s"))
        return new(total, Pair{Symbol,Float64}[b => w / s for (b, w) in weights])
    end
end
SplitDegrees(total::DegreeDistribution, weights::AbstractVector{<:Pair{Symbol,<:Real}}) =
    SplitDegrees(total, Pair{Symbol,Float64}[b => Float64(w) for (b, w) in weights])
SplitDegrees(total::DegreeDistribution, weights::Pair{Symbol,<:Real}...) =
    SplitDegrees(total, Pair{Symbol,Float64}[b => Float64(w) for (b, w) in weights])

function _net_check_unique(names::AbstractVector, what::AbstractString)
    dups = unique(n for n in names if count(==(n), names) > 1)
    isempty(dups) || throw(ArgumentError("$what(s) $(join(repr.(dups), ", ")) given more than once"))
    return nothing
end

Base.:(==)(a::IndependentDegrees, b::IndependentDegrees) =
    length(a.parts) == length(b.parts) &&
    all(first(p) == first(q) && last(p) == last(q) for (p, q) in zip(a.parts, b.parts))
Base.hash(a::IndependentDegrees, h::UInt) = hash(a.parts, hash(:IndependentDegrees, h))
Base.:(==)(a::SplitDegrees, b::SplitDegrees) = a.total == b.total && a.weights == b.weights
Base.hash(a::SplitDegrees, h::UInt) = hash(a.weights, hash(a.total, hash(:SplitDegrees, h)))

"""
    partner_types(m::MultivariateDegree) -> Vector{Symbol}

The partner types that `m` mentions, in order: the order of the counts returned by
`rand(rng, m)`. Every other type is a structural zero of `m`.
"""
partner_types(m::IndependentDegrees) = Symbol[first(p) for p in m.parts]
partner_types(m::SplitDegrees) = Symbol[first(w) for w in m.weights]

_net_arg(x::Function, b::Symbol) = x(b)
_net_arg(x, b::Symbol) = x[b]

# ---- joint PGF and partial derivatives ------------------------------------------------------

function pgf(m::IndependentDegrees, x)
    isempty(m.parts) && return 1.0
    return prod(pgf(d, _net_arg(x, b)) for (b, d) in m.parts)
end
function pgf_derivative(m::IndependentDegrees, x, bs::Symbol...)
    names = partner_types(m)
    all(in(names), bs) || return 0.0
    isempty(m.parts) && return 1.0
    return prod(pgf_derivative(d, _net_arg(x, b), count(==(b), bs)) for (b, d) in m.parts)
end

_net_split_argument(m::SplitDegrees, x) =
    isempty(m.weights) ? 0.0 : sum(w * _net_arg(x, b) for (b, w) in m.weights)
pgf(m::SplitDegrees, x) = pgf(m.total, _net_split_argument(m, x))
function pgf_derivative(m::SplitDegrees, x, bs::Symbol...)
    w = Dict(m.weights)
    all(b -> haskey(w, b), bs) || return 0.0
    scale = isempty(bs) ? 1.0 : prod(w[b] for b in bs)
    return scale * pgf_derivative(m.total, _net_split_argument(m, x), length(bs))
end

"""
    pgf(m::MultivariateDegree, x)
    pgf_derivative(m::MultivariateDegree, x, b::Symbol...)

The joint PGF ψ_a(x) = E[Π_b x_b^{k_{a→b}}] and its partial derivatives ∂_{b₁} ⋯ ∂_{bₙ} ψ_a(x)
(repeat a type for higher order: `pgf_derivative(m, x, :a, :a)` = ∂²_a ψ). `x` maps partner
types to values (an `AbstractDict{Symbol}`, a `NamedTuple` or a function); a derivative with
respect to a type that `m` does not mention is 0.
"""
pgf(m::MultivariateDegree, x)

# ---- moments (closed form) ---------------------------------------------------------------------

# ∂_{b₁}⋯∂_{bₙ} ψ_a(1), exact for symbolic parameters.
function _net_mv_moment(m::IndependentDegrees, bs::Symbol...)
    names = partner_types(m)
    all(in(names), bs) || return 0.0
    isempty(m.parts) && return 1.0
    return prod(_net_factorial_moment(d, count(==(b), bs)) for (b, d) in m.parts)
end
function _net_mv_moment(m::SplitDegrees, bs::Symbol...)
    w = Dict(m.weights)
    all(b -> haskey(w, b), bs) || return 0.0
    scale = isempty(bs) ? 1.0 : prod(w[b] for b in bs)
    return scale * _net_factorial_moment(m.total, length(bs))
end

"""
    mean_degree(m::MultivariateDegree, b::Symbol)
    mean_degree(m::MultivariateDegree)

E[k_{a→b}] = ∂_b ψ_a(1), the mean number of edges to partner type `b` (0 for a type that `m`
does not mention), and the total mean degree Σ_b E[k_{a→b}].
"""
mean_degree(m::MultivariateDegree, b::Symbol) = _net_mv_moment(m, b)
mean_degree(m::MultivariateDegree) = sum((mean_degree(m, b) for b in partner_types(m)); init = 0.0)

# ---- sampling --------------------------------------------------------------------------------

"""
    rand([rng,] m::MultivariateDegree) -> Vector{Int}

Draw the edge counts (k_{a→b})_b, aligned with [`partner_types`](@ref)`(m)`. For
`SplitDegrees`, the total degree is drawn and split multinomially over the partner types with
positive weight (sequential binomial draws), so zero-weight types always get 0 edges.
"""
Random.rand(rng::AbstractRNG, m::IndependentDegrees) = Int[rand(rng, d) for (_, d) in m.parts]
function Random.rand(rng::AbstractRNG, m::SplitDegrees)
    counts = zeros(Int, length(m.weights))
    positive = findall(w -> last(w) > 0, m.weights)
    isempty(positive) && return counts
    left = rand(rng, m.total)
    wleft = sum(last(m.weights[i]) for i in positive)
    for (j, i) in enumerate(positive)
        left == 0 && break
        if j == length(positive)
            counts[i] = left
        else
            w = last(m.weights[i])
            c = _net_rand_binomial(rng, left, min(1.0, w / wleft))
            counts[i] = c
            left -= c
            wleft -= w
        end
    end
    return counts
end
Random.rand(m::MultivariateDegree) = rand(Random.default_rng(), m)

# ---- canonical text ----------------------------------------------------------------------------

canonical_text(io::IO, m::IndependentDegrees) = _netct_struct(io, "IndependentDegrees", :parts => m.parts)
canonical_text(io::IO, m::SplitDegrees) =
    _netct_struct(io, "SplitDegrees", :total => m.total, :weights => m.weights)

"""
    canonical_text(m::MultivariateDegree) -> String

Canonical text of a multivariate degree law (§E.4), for example
`IndependentDegrees(parts=[:a => PoissonDegree(mean=6), :b => PoissonDegree(mean=2)])`.
"""
canonical_text(m::MultivariateDegree) = sprint(canonical_text, m)
