# Owner: WP7 (DESIGN_NetworkEpiCore.md §C.1; work package in §G.2).
#
# Degree distributions of configuration-model networks: the families of §C.1, their PGFs and
# PGF derivatives in closed form (generic in the argument, so they evaluate on Float64, on
# Symbolics.Num and on dual numbers), factorial and raw moments, the Poisson-type (PT) test,
# sampling, equality and canonical text (§E.4).
#
# Never export `Poisson`, `Binomial`, `NegativeBinomial` or `Geometric` (§A.2): the families are
# named `…Degree` so that `using Distributions` never clashes.
#
# The `_net*` helpers defined here (numeric tests, falling/rising factorials, the canonical-text
# printers) are shared by networks/multivariate.jl, networks/descriptors.jl and seeding.jl.

export DegreeDistribution, PoissonDegree, RegularDegree, BinomialDegree, NegBinDegree,
       GeometricDegree, PowerLawDegree, EmpiricalDegree, MixtureDegree
export degree_probabilities, degree_moment, closure_constant, is_poisson_type

# =============================================================================================
# Shared helpers (WP7 files)
# =============================================================================================

# A value is numeric when its value is known now. Symbolic values (Symbolics.Num is a Real) and
# dual numbers are not: validation is skipped for them, and functions that need numbers
# (probabilities, sampling, canonical text) refuse them.
const _NetNumber = Union{AbstractFloat,Integer,Rational,AbstractIrrational}
_net_isnumeric(x) = x isa _NetNumber

_net_float(x::Union{Integer,Rational,AbstractIrrational}) = float(x)
_net_float(x) = x

function _net_require_numeric(d, what::AbstractString)
    throw(ArgumentError("$what needs numeric parameters; $(d) has symbolic ones"))
end

# Falling factorial k(k−1)⋯(k−n+1) and rising factorial r(r+1)⋯(r+n−1); both are 1 for n = 0.
_net_falling(k, n::Integer) = n == 0 ? one(k) : prod(k - i for i in 0:(n - 1))
_net_rising(r, n::Integer) = n == 0 ? one(r) : prod(r + i for i in 0:(n - 1))

function _net_check_order(n::Integer)
    n >= 0 || throw(ArgumentError("the derivative order must be ≥ 0; got $n"))
    return nothing
end

# Stirling numbers of the second kind S(j, i), i = 0:j (E[K^j] = Σ_i S(j, i) E[(K)_i]).
function _net_stirling2(j::Integer)
    S = zeros(Int, j + 1, j + 1)            # S[n+1, i+1] = S(n, i)
    S[1, 1] = 1
    for n in 1:j, i in 1:n
        S[n + 1, i + 1] = i * S[n, i + 1] + S[n, i]
    end
    return S[j + 1, :]
end

# ---- canonical text (§E.4): explicit field names, `%.17g` reals, never `repr` or `hash` -------

function _netct_real(io::IO, x)
    if x isa Integer
        print(io, x)
    elseif _net_isnumeric(x)
        y = Float64(x)
        isfinite(y) || throw(ArgumentError("canonical_text: non-finite number $x"))
        print(io, @sprintf("%.17g", y == 0 ? 0.0 : y))   # −0.0 prints as 0
    else
        throw(ArgumentError("canonical_text needs numeric values; got $(x) of type " *
                            "$(typeof(x)): symbolic parameters cannot be hashed"))
    end
    return nothing
end

_netct_value(io::IO, x::Real) = _netct_real(io, x)
_netct_value(io::IO, x::Symbol) = print(io, ':', x)
_netct_value(io::IO, ::Nothing) = print(io, "nothing")
function _netct_value(io::IO, p::Pair)
    _netct_value(io, first(p))
    print(io, " => ")
    _netct_value(io, last(p))
    return nothing
end
function _netct_value(io::IO, v::AbstractVector)
    print(io, '[')
    for (i, x) in enumerate(v)
        i > 1 && print(io, ", ")
        _netct_value(io, x)
    end
    print(io, ']')
    return nothing
end
function _netct_value(io::IO, t::Tuple)
    print(io, '(')
    for (i, x) in enumerate(t)
        i > 1 && print(io, ", ")
        _netct_value(io, x)
    end
    print(io, ')')
    return nothing
end
# A matrix is written as its list of rows.
_netct_value(io::IO, M::AbstractMatrix) = _netct_value(io, [M[i, :] for i in axes(M, 1)])
_netct_value(io::IO, x) = canonical_text(io, x)            # nested NEC objects

function _netct_struct(io::IO, name::AbstractString, fields::Pair{Symbol}...)
    print(io, name, '(')
    for (i, (f, v)) in enumerate(fields)
        i > 1 && print(io, ", ")
        print(io, f, '=')
        _netct_value(io, v)
    end
    print(io, ')')
    return nothing
end

# ---- field-wise equality and hashing for WP7 types with vector fields -------------------------

function _net_fields_equal(a, b)
    typeof(a) === typeof(b) || return false
    for f in fieldnames(typeof(a))
        getfield(a, f) == getfield(b, f) || return false
    end
    return true
end
function _net_fields_hash(a, h::UInt)
    h = hash(nameof(typeof(a)), h)
    for f in fieldnames(typeof(a))
        h = hash(getfield(a, f), h)
    end
    return h
end

# =============================================================================================
# Types
# =============================================================================================

"""
    DegreeDistribution

Abstract supertype of degree distributions: the law of the number of edges (stubs) of a node in
a configuration-model network. Every family implements, in closed form and generic in the
argument `x` (a `Real`, a `Symbolics.Num` or a dual number):

- [`pgf`](@ref)`(d, x)` = ψ(x) = Σₖ pₖ xᵏ and [`pgf_derivative`](@ref)`(d, x, n)` = ψ⁽ⁿ⁾(x);
- [`mean_degree`](@ref) = ψ'(1), [`excess_degree`](@ref) = ψ''(1)/ψ'(1),
  [`degree_moment`](@ref) = E[Kʲ], [`closure_constant`](@ref) = ψ''(1)/ψ'(1)² and
  [`is_poisson_type`](@ref);

and, for numeric parameters only, [`degree_probabilities`](@ref), `rand(rng, d)`,
`rand(rng, d, n)` and [`canonical_text`](@ref).

Families: [`PoissonDegree`](@ref), [`RegularDegree`](@ref), [`BinomialDegree`](@ref),
[`NegBinDegree`](@ref) (and [`GeometricDegree`](@ref)), [`PowerLawDegree`](@ref),
[`EmpiricalDegree`](@ref) and [`MixtureDegree`](@ref). EdgeBasedModels' legacy `DegreePGF` is
also a subtype.
"""
abstract type DegreeDistribution end

"""
    PoissonDegree(mean)

Poisson degrees, pₖ = e^{−μ} μᵏ/k!, with ψ(x) = exp(μ(x − 1)) and ψ⁽ⁿ⁾(x) = μⁿ exp(μ(x − 1)).
The mean and the excess degree are both μ, and ψ' = μψ, so the family is Poisson type with
κ = 1 (closure constant 1).

The mean may be symbolic (EdgeBasedModels passes a `Symbolics.Num`); integer and rational
means are stored as `Float64`. `ConfigurationNetwork(PoissonDegree(μ))` is the large-N limit of
the Erdős–Rényi graph G(N, μ/(N − 1)).
"""
struct PoissonDegree{T} <: DegreeDistribution
    mean::T
    function PoissonDegree{T}(mean) where {T}
        if _net_isnumeric(mean) && !(isfinite(mean) && mean >= 0)
            throw(ArgumentError("PoissonDegree: the mean must be finite and ≥ 0; got $mean"))
        end
        return new{T}(mean)
    end
end
PoissonDegree(mean::T) where {T<:Real} = PoissonDegree{T}(mean)
PoissonDegree(mean::Union{Integer,Rational,AbstractIrrational}) = PoissonDegree(float(mean))

"""
    RegularDegree(k)

Every node has degree `k` (an integer ≥ 0): ψ(x) = xᵏ. Mean k, excess degree k − 1, closure
constant (k − 1)/k; ψ' = k ψ^{(k−1)/k}, so the family is Poisson type with κ = (k − 1)/k.
A real argument must be integral (`RegularDegree(6.0) == RegularDegree(6)`).
"""
struct RegularDegree <: DegreeDistribution
    k::Int
    function RegularDegree(k::Integer)
        k >= 0 || throw(ArgumentError("RegularDegree: the degree must be ≥ 0; got $k"))
        return new(Int(k))
    end
end
function RegularDegree(k::Real)
    (_net_isnumeric(k) && isfinite(k) && isinteger(k)) ||
        throw(ArgumentError("RegularDegree needs an integer degree; got $k"))
    return RegularDegree(Int(k))
end

"""
    BinomialDegree(n, p)

Binomial degrees, pₖ = C(n, k) pᵏ (1 − p)ⁿ⁻ᵏ, with ψ(x) = (1 − p + p x)ⁿ. Mean np, excess degree
(n − 1)p, closure constant (n − 1)/n; ψ' = np ψ^{(n−1)/n}, so the family is Poisson type with
κ = (n − 1)/n. `p` may be symbolic; integer and rational values are stored as `Float64`.
"""
struct BinomialDegree{T} <: DegreeDistribution
    n::Int
    p::T
    function BinomialDegree{T}(n::Integer, p) where {T}
        n >= 0 || throw(ArgumentError("BinomialDegree: n must be ≥ 0; got $n"))
        if _net_isnumeric(p) && !(0 <= p <= 1)
            throw(ArgumentError("BinomialDegree: p must lie in [0, 1]; got $p"))
        end
        return new{T}(Int(n), p)
    end
end
BinomialDegree(n::Integer, p::T) where {T<:Real} = BinomialDegree{T}(n, p)
BinomialDegree(n::Integer, p::Union{Integer,Rational,AbstractIrrational}) =
    BinomialDegree(n, float(p))

"""
    NegBinDegree(r, p)
    NegBinDegree(; mean, var)

Negative binomial degrees, pₖ = C(k + r − 1, k) pʳ (1 − p)ᵏ (r > 0, 0 < p ≤ 1; the number of
failures before the r-th success), with ψ(x) = (p/(1 − (1 − p)x))ʳ. Mean r(1 − p)/p, variance
r(1 − p)/p², closure constant (r + 1)/r; ψ' = (r(1 − p)/p) ψ^{(r+1)/r}, so the family is
Poisson type with κ = (r + 1)/r.

The keyword form is parameterised by the moments and needs `var > mean > 0`: p = mean/var and
r = mean²/(var − mean). For example `NegBinDegree(mean = 4, var = 8)` has r = 4, p = 1/2,
excess degree 5 and P(K = 0) = 1/16.
"""
struct NegBinDegree{T} <: DegreeDistribution
    r::T
    p::T
    function NegBinDegree{T}(r, p) where {T}
        if _net_isnumeric(r) && !(isfinite(r) && r > 0)
            throw(ArgumentError("NegBinDegree: r must be finite and > 0; got $r"))
        end
        if _net_isnumeric(p) && !(0 < p <= 1)
            throw(ArgumentError("NegBinDegree: p must lie in (0, 1]; got $p"))
        end
        return new{T}(r, p)
    end
end
function NegBinDegree(r::Real, p::Real)
    r1, p1 = promote(_net_float(r), _net_float(p))
    return NegBinDegree{typeof(r1)}(r1, p1)
end
function NegBinDegree(; mean::Real, var::Real)
    (isfinite(mean) && isfinite(var) && mean > 0) ||
        throw(ArgumentError("NegBinDegree(; mean, var): mean and var must be finite with " *
                            "mean > 0; got mean = $mean, var = $var"))
    var > mean ||
        throw(ArgumentError("NegBinDegree(; mean, var) needs var > mean (overdispersion); got " *
                            "mean = $mean, var = $var. Use PoissonDegree(mean) for var = mean " *
                            "and BinomialDegree for var < mean"))
    return NegBinDegree(mean^2 / (var - mean), mean / var)
end

"""
    GeometricDegree(mean)

Geometric degrees pₖ = p(1 − p)ᵏ with the given mean: `NegBinDegree(1.0, 1/(1 + mean))`
(Poisson type with κ = 2).
"""
function GeometricDegree(mean::Real)
    (_net_isnumeric(mean) && !(isfinite(mean) && mean >= 0)) &&
        throw(ArgumentError("GeometricDegree: the mean must be finite and ≥ 0; got $mean"))
    return NegBinDegree(1.0, 1 / (1 + mean))
end

"""
    PowerLawDegree(α, kmin, kmax)
    PowerLawDegree(α; kmin = 1, kmax)

Truncated, normalised power law pₖ ∝ k^{−α} for kmin ≤ k ≤ kmax (1 ≤ kmin ≤ kmax, both finite).
ψ is a polynomial, so every derivative is exact. `PowerLawDegree(2.5; kmin = 2, kmax = 60)` has
mean 3.985 and excess degree 8.663 (the heavy-tailed canonical scenario). It is not Poisson
type unless kmin = kmax.
"""
struct PowerLawDegree <: DegreeDistribution
    α::Float64
    kmin::Int
    kmax::Int
    function PowerLawDegree(α::Real, kmin::Integer, kmax::Integer)
        isfinite(α) || throw(ArgumentError("PowerLawDegree: α must be finite; got $α"))
        1 <= kmin <= kmax ||
            throw(ArgumentError("PowerLawDegree needs 1 ≤ kmin ≤ kmax; got kmin = $kmin, " *
                                "kmax = $kmax"))
        return new(Float64(α), Int(kmin), Int(kmax))
    end
end
PowerLawDegree(α::Real; kmin::Integer = 1, kmax::Integer) = PowerLawDegree(α, kmin, kmax)

"""
    EmpiricalDegree(p::AbstractVector)       # p[k+1] = P(K = k)
    EmpiricalDegree(d::AbstractDict{Int})    # EmpiricalDegree(Dict(2 => 5/6, 10 => 1/6))
    EmpiricalDegree(k => pₖ, ...)            # EmpiricalDegree(2 => 5/6, 10 => 1/6)
    EmpiricalDegree(g::Graphs.AbstractGraph) # degree histogram (NetworkEpiCoreGraphsExt)

A degree distribution with finite support given by its probabilities. They must be finite,
non-negative and sum to 1 within 1e-8; they are normalised and trailing zeros are dropped, so
`EmpiricalDegree([0, 0, 1, 0]) == EmpiricalDegree(2 => 1.0)`. ψ is the polynomial Σₖ pₖ xᵏ, so
derivatives are exact polynomial sums and NEC never differentiates symbolically. The bimodal
`EmpiricalDegree(2 => 5/6, 10 => 1/6)` (mean 10/3, excess degree 5, closure constant 3/2) is the
canonical non-Poisson-type example.
"""
struct EmpiricalDegree <: DegreeDistribution
    p::Vector{Float64}
    function EmpiricalDegree(p::AbstractVector{<:Real})
        isempty(p) && throw(ArgumentError("EmpiricalDegree: no probabilities given"))
        all(x -> _net_isnumeric(x) && isfinite(x) && x >= 0, p) ||
            throw(ArgumentError("EmpiricalDegree: probabilities must be finite and ≥ 0; got $p"))
        s = sum(p)
        isapprox(s, 1; atol = 1e-8) ||
            throw(ArgumentError("EmpiricalDegree: the probabilities must sum to 1; they sum to $s"))
        K = findlast(>(0), p)
        return new(Float64[p[i] / s for i in firstindex(p):(firstindex(p) + K - 1)])
    end
end
function EmpiricalDegree(d::AbstractDict{<:Integer,<:Real})
    isempty(d) && throw(ArgumentError("EmpiricalDegree: no probabilities given"))
    minimum(keys(d)) >= 0 || throw(ArgumentError("EmpiricalDegree: degrees must be ≥ 0"))
    p = zeros(Float64, maximum(keys(d)) + 1)
    for (k, v) in d
        p[k + 1] = v
    end
    return EmpiricalDegree(p)
end
function EmpiricalDegree(ps::Pair{<:Integer,<:Real}...)
    isempty(ps) && throw(ArgumentError("EmpiricalDegree: no probabilities given"))
    ks = [first(p) for p in ps]
    allunique(ks) ||
        throw(ArgumentError("EmpiricalDegree: degree(s) $(unique(k for k in ks if count(==(k), ks) > 1)) " *
                            "given more than once"))
    return EmpiricalDegree(Dict(ps...))
end

"""
    MixtureDegree(weights, components)
    MixtureDegree(w₁ => d₁, w₂ => d₂, ...)

The finite mixture ψ(x) = Σᵢ wᵢ ψᵢ(x) of degree distributions (weights finite, ≥ 0, summing to
1 within 1e-8; they are normalised). A mixture of distinct components is generally not Poisson
type; [`is_poisson_type`](@ref) decides numerically.
"""
struct MixtureDegree{D<:DegreeDistribution} <: DegreeDistribution
    weights::Vector{Float64}
    components::Vector{D}
    function MixtureDegree{D}(weights::AbstractVector{<:Real},
                              components::AbstractVector) where {D<:DegreeDistribution}
        length(weights) == length(components) ||
            throw(ArgumentError("MixtureDegree: $(length(weights)) weights for " *
                                "$(length(components)) components"))
        isempty(weights) && throw(ArgumentError("MixtureDegree: no components given"))
        all(w -> _net_isnumeric(w) && isfinite(w) && w >= 0, weights) ||
            throw(ArgumentError("MixtureDegree: weights must be finite and ≥ 0; got $weights"))
        s = sum(weights)
        isapprox(s, 1; atol = 1e-8) ||
            throw(ArgumentError("MixtureDegree: the weights must sum to 1; they sum to $s"))
        return new{D}(Float64[w / s for w in weights], collect(D, components))
    end
end
MixtureDegree(weights::AbstractVector{<:Real}, components::AbstractVector{D}) where {D<:DegreeDistribution} =
    MixtureDegree{D}(weights, components)
MixtureDegree(ps::Pair{<:Real,<:DegreeDistribution}...) =
    MixtureDegree([first(p) for p in ps], [last(p) for p in ps])

Base.:(==)(a::EmpiricalDegree, b::EmpiricalDegree) = a.p == b.p
Base.hash(a::EmpiricalDegree, h::UInt) = _net_fields_hash(a, h)
Base.:(==)(a::MixtureDegree, b::MixtureDegree) =
    a.weights == b.weights && length(a.components) == length(b.components) &&
    all(a.components .== b.components)
Base.hash(a::MixtureDegree, h::UInt) = hash(a.components, hash(a.weights, hash(:MixtureDegree, h)))

# =============================================================================================
# PGFs and their derivatives (closed form, generic in x)
# =============================================================================================

pgf(d::PoissonDegree, x) = exp(d.mean * (x - 1))
function pgf_derivative(d::PoissonDegree, x, n::Integer)
    _net_check_order(n)
    return d.mean^n * exp(d.mean * (x - 1))
end

pgf(d::RegularDegree, x) = x^d.k
function pgf_derivative(d::RegularDegree, x, n::Integer)
    _net_check_order(n)
    n > d.k && return zero(x)
    return _net_falling(d.k, n) * x^(d.k - n)
end

pgf(d::BinomialDegree, x) = (1 - d.p + d.p * x)^d.n
function pgf_derivative(d::BinomialDegree, x, n::Integer)
    _net_check_order(n)
    n > d.n && return zero(x)
    return _net_falling(d.n, n) * d.p^n * (1 - d.p + d.p * x)^(d.n - n)
end

pgf(d::NegBinDegree, x) = (d.p / (1 - (1 - d.p) * x))^d.r
function pgf_derivative(d::NegBinDegree, x, n::Integer)
    _net_check_order(n)
    n == 0 && return pgf(d, x)
    return _net_rising(d.r, n) * (1 - d.p)^n * d.p^d.r * (1 - (1 - d.p) * x)^(-d.r - n)
end

# Polynomial PGFs Σₖ pₖ xᵏ: only the non-zero coefficients produce terms, so symbolic arguments
# give clean expressions.
function _net_poly_derivative(p::AbstractVector{<:Real}, x, n::Integer)
    _net_check_order(n)
    acc = nothing
    for j in eachindex(p)
        k = j - firstindex(p)
        (p[j] == 0 || k < n) && continue
        term = (p[j] * _net_falling(float(k), n)) * x^(k - n)
        acc = acc === nothing ? term : acc + term
    end
    return acc === nothing ? zero(x) : acc
end

pgf(d::PowerLawDegree, x) = _net_poly_derivative(_net_powerlaw_probs(d), x, 0)
pgf_derivative(d::PowerLawDegree, x, n::Integer) = _net_poly_derivative(_net_powerlaw_probs(d), x, n)
pgf(d::EmpiricalDegree, x) = _net_poly_derivative(d.p, x, 0)
pgf_derivative(d::EmpiricalDegree, x, n::Integer) = _net_poly_derivative(d.p, x, n)

pgf(d::MixtureDegree, x) = sum(w * pgf(c, x) for (w, c) in zip(d.weights, d.components))
function pgf_derivative(d::MixtureDegree, x, n::Integer)
    _net_check_order(n)
    return sum(w * pgf_derivative(c, x, n) for (w, c) in zip(d.weights, d.components))
end

function _net_powerlaw_probs(d::PowerLawDegree)
    p = zeros(Float64, d.kmax + 1)
    for k in d.kmin:d.kmax
        p[k + 1] = float(k)^(-d.α)
    end
    return p ./ sum(p)
end

# =============================================================================================
# Moments
# =============================================================================================

# Factorial moments E[(K)ₙ] = ψ⁽ⁿ⁾(1), in closed form (exact for symbolic parameters).
_net_factorial_moment(d::PoissonDegree, n::Integer) = d.mean^n
_net_factorial_moment(d::RegularDegree, n::Integer) = float(_net_falling(d.k, n))
_net_factorial_moment(d::BinomialDegree, n::Integer) = _net_falling(d.n, n) * d.p^n
_net_factorial_moment(d::NegBinDegree, n::Integer) = _net_rising(d.r, n) * ((1 - d.p) / d.p)^n
_net_factorial_moment(d::PowerLawDegree, n::Integer) =
    sum(pk * _net_falling(float(j - 1), n) for (j, pk) in enumerate(_net_powerlaw_probs(d)))
_net_factorial_moment(d::EmpiricalDegree, n::Integer) =
    sum(pk * _net_falling(float(j - 1), n) for (j, pk) in enumerate(d.p))
_net_factorial_moment(d::MixtureDegree, n::Integer) =
    sum(w * _net_factorial_moment(c, n) for (w, c) in zip(d.weights, d.components))
_net_factorial_moment(d::DegreeDistribution, n::Integer) = pgf_derivative(d, 1, n)   # fallback

_net_iszero_numeric(x) = _net_isnumeric(x) && iszero(x)

function _net_require_edges(d, what)
    m = _net_factorial_moment(d, 1)
    _net_iszero_numeric(m) &&
        throw(ArgumentError("$what is undefined for $(d): its mean degree is 0 (no edges)"))
    return m
end

"""
    mean_degree(d::DegreeDistribution)

The mean degree ⟨k⟩ = ψ'(1), in closed form (symbolic parameters give an exact expression).
"""
mean_degree(d::DegreeDistribution) = _net_factorial_moment(d, 1)

"""
    excess_degree(d::DegreeDistribution)

The mean excess degree κ_ex = ψ''(1)/ψ'(1) = ⟨k(k − 1)⟩/⟨k⟩: the expected number of other edges
of a node reached along a random edge. With per-edge transmissibility T, a single-entry SIR-type
model has R₀ = T κ_ex. Undefined (an `ArgumentError`) when the mean degree is 0.
"""
function excess_degree(d::DegreeDistribution)
    m = _net_require_edges(d, "the excess degree")
    return _net_factorial_moment(d, 2) / m
end
excess_degree(d::PoissonDegree) = (_net_require_edges(d, "the excess degree"); d.mean)

"""
    degree_moment(d::DegreeDistribution, j::Integer)

The raw moment E[Kʲ] = Σᵢ S(j, i) ψ⁽ⁱ⁾(1), with S the Stirling numbers of the second kind; for
example E[K²] = μ + μ² for Poisson degrees.
"""
function degree_moment(d::DegreeDistribution, j::Integer)
    j >= 0 || throw(ArgumentError("degree_moment: the order must be ≥ 0; got $j"))
    S = _net_stirling2(j)
    return sum(S[i + 1] * _net_factorial_moment(d, i) for i in 0:j if S[i + 1] != 0)
end

"""
    closure_constant(d::DegreeDistribution)
    closure_constant(net::ConfigurationNetwork)

The heterogeneous pairwise closure constant K_ψ(1) = ψ''(1)/ψ'(1)² = ⟨k(k − 1)⟩/⟨k⟩², used by
NodeBasedModels' constant-K closure of the triples, [ABC] ≈ K [AB][BC]/[B]. That closure is
exact against the edge-based model iff ψ is Poisson type ([`is_poisson_type`](@ref)), in which
case K = κ: 1 for Poisson, (k − 1)/k for `RegularDegree(k)`, (r + 1)/r for `NegBinDegree`.
Undefined (an `ArgumentError`) when the mean degree is 0.
"""
function closure_constant(d::DegreeDistribution)
    m = _net_require_edges(d, "the closure constant")
    return _net_factorial_moment(d, 2) / m^2
end
closure_constant(d::PoissonDegree) = (_net_require_edges(d, "the closure constant"); 1.0)

# =============================================================================================
# The Poisson-type test ψ' = α ψ^κ
# =============================================================================================

"""
    is_poisson_type(d) -> Union{Nothing, NamedTuple{(:α, :κ)}}

Whether the degree PGF is Poisson type (PT), ψ' = α ψ^κ on [0, 1]; if so, return `(α, κ)` with
α = ψ'(1) = ⟨k⟩ and κ = ψ''(1)/ψ'(1)² (the closure constant), else `nothing`.

The PT families are exactly the Poisson (κ = 1), binomial and regular (κ = (n − 1)/n) and
negative binomial (κ = (r + 1)/r) laws. The closed-form families answer directly (also for
symbolic parameters). Any other distribution (empirical, power law, mixture) is tested
numerically: ψ'(x) = α ψ(x)^κ must hold at x ∈ {0, 0.2, 0.4, 0.6, 0.8, 0.95} to relative
tolerance 1e-9, which recognises, for example, an `EmpiricalDegree` that is really binomial or a
point mass. A distribution with mean degree 0 (no edges) returns `nothing`.
"""
function is_poisson_type end

_net_pt(α, κ) = (α = α, κ = κ)

is_poisson_type(d::PoissonDegree) = _net_iszero_numeric(d.mean) ? nothing : _net_pt(d.mean, 1.0)
is_poisson_type(d::RegularDegree) = d.k == 0 ? nothing : _net_pt(float(d.k), (d.k - 1) / d.k)
function is_poisson_type(d::BinomialDegree)
    (d.n == 0 || _net_iszero_numeric(d.p)) && return nothing
    return _net_pt(d.n * d.p, (d.n - 1) / d.n)
end
function is_poisson_type(d::NegBinDegree)
    (_net_isnumeric(d.p) && d.p == 1) && return nothing
    return _net_pt(d.r * (1 - d.p) / d.p, (d.r + 1) / d.r)
end
function is_poisson_type(d::DegreeDistribution)
    α = _net_factorial_moment(d, 1)
    _net_isnumeric(α) ||
        throw(ArgumentError("is_poisson_type($(d)): a numeric test needs numeric parameters"))
    iszero(α) && return nothing
    κ = _net_factorial_moment(d, 2) / α^2
    for x in (0.0, 0.2, 0.4, 0.6, 0.8, 0.95)
        lhs = pgf_derivative(d, x, 1)
        rhs = α * pgf(d, x)^κ
        abs(lhs - rhs) <= 1e-9 * (abs(lhs) + abs(rhs)) + 1e-14 || return nothing
    end
    return _net_pt(Float64(α), Float64(κ))
end

# =============================================================================================
# Probabilities
# =============================================================================================

"""
    degree_probabilities(d; tol = 1e-12, kmax = nothing) -> Vector{Float64}

The probabilities p[k+1] = P(K = k). With `kmax = nothing` the vector ends at the largest degree
of a finite support, or, for infinite support (Poisson, negative binomial), at the first
K ≥ ⟨k⟩ whose tail mass 1 − Σ_{k≤K} pₖ is at most `tol`. With an integer `kmax` it has exactly
`kmax + 1` entries (truncated or zero-padded, never renormalised). Needs numeric parameters.
"""
function degree_probabilities(d::DegreeDistribution; tol::Real = 1e-12,
                              kmax::Union{Nothing,Integer} = nothing)
    tol > 0 || throw(ArgumentError("degree_probabilities: tol must be > 0; got $tol"))
    kmax === nothing || kmax >= 0 ||
        throw(ArgumentError("degree_probabilities: kmax must be ≥ 0; got $kmax"))
    p = _net_probs(d, Float64(tol), kmax)
    kmax === nothing && return p
    q = zeros(Float64, kmax + 1)
    m = min(length(p), kmax + 1)
    q[1:m] .= @view p[1:m]
    return q
end

# Log-space recurrence p_k = p_{k−1}·exp(logratio(k)), from log p₀; stops at kmax if given,
# otherwise once k ≥ mean and the tail is ≤ tol.
function _net_series(logp0::Float64, logratio, mean::Float64, tol::Float64, kmax)
    p = Float64[]
    lp = logp0
    s = 0.0
    k = 0
    while true
        pk = exp(lp)
        push!(p, pk)
        s += pk
        if kmax === nothing
            k >= mean && (1 - s <= tol || pk < floatmin(Float64)) && break
            k < 100_000_000 || error("degree_probabilities: the series did not converge")
        else
            k >= kmax && break
        end
        k += 1
        lp += logratio(k)
    end
    return p
end

function _net_numeric_or_throw(d, xs...)
    all(_net_isnumeric, xs) || _net_require_numeric(d, "degree_probabilities")
    return nothing
end

function _net_probs(d::PoissonDegree, tol, kmax)
    _net_numeric_or_throw(d, d.mean)
    μ = Float64(d.mean)
    μ == 0 && return [1.0]
    return _net_series(-μ, k -> log(μ) - log(k), μ, tol, kmax)
end
function _net_probs(d::NegBinDegree, tol, kmax)
    _net_numeric_or_throw(d, d.r, d.p)
    r, p = Float64(d.r), Float64(d.p)
    p == 1 && return [1.0]
    lq = log1p(-p)
    return _net_series(r * log(p), k -> log(k - 1 + r) - log(k) + lq, r * (1 - p) / p, tol, kmax)
end
function _net_probs(d::BinomialDegree, tol, kmax)
    _net_numeric_or_throw(d, d.p)
    n, p = d.n, Float64(d.p)
    p == 0 && return [1.0]
    if p == 1
        q = zeros(Float64, n + 1)
        q[end] = 1.0
        return q
    end
    lr = log(p) - log1p(-p)
    return _net_series(n * log1p(-p), k -> log(n - k + 1) - log(k) + lr, n * p, tol, n)
end
function _net_probs(d::RegularDegree, tol, kmax)
    q = zeros(Float64, d.k + 1)
    q[end] = 1.0
    return q
end
_net_probs(d::PowerLawDegree, tol, kmax) = _net_powerlaw_probs(d)
_net_probs(d::EmpiricalDegree, tol, kmax) = copy(d.p)
function _net_probs(d::MixtureDegree, tol, kmax)
    parts = [_net_probs(c, tol, kmax) for c in d.components]
    if kmax === nothing          # recompute every component to the common length (no truncation gaps)
        K = maximum(length, parts) - 1
        parts = [_net_probs(c, tol, K) for c in d.components]
    end
    q = zeros(Float64, maximum(length, parts))
    for (w, p) in zip(d.weights, parts)
        q[1:length(p)] .+= w .* p
    end
    return q
end
_net_probs(d::DegreeDistribution, tol, kmax) =
    throw(ArgumentError("degree_probabilities is not implemented for $(typeof(d))"))

# =============================================================================================
# Sampling
# =============================================================================================

# Poisson by inversion; means above 500 are split into independent pieces (exact, since sums of
# independent Poisson variables are Poisson), so e^{−μ} never underflows.
function _net_rand_poisson(rng::AbstractRNG, μ::Float64)
    k = 0
    while μ > 0
        piece = min(μ, 500.0)
        u = rand(rng)
        j = 0
        pj = exp(-piece)
        F = pj
        while u > F
            j += 1
            pj *= piece / j
            F += pj
            (pj < 1e-300 && j > piece) && break
        end
        k += j
        μ -= piece
    end
    return k
end

# Binomial by inversion on chunks of ≤ 1000 trials with p ≤ 1/2 (sums of binomials with the same
# p are binomial), so (1 − p)ⁿ never underflows.
function _net_rand_binomial(rng::AbstractRNG, n::Integer, p::Float64)
    (n == 0 || p == 0) && return 0
    p == 1 && return Int(n)
    p > 0.5 && return Int(n) - _net_rand_binomial(rng, n, 1 - p)
    k = 0
    left = Int(n)
    ratio = p / (1 - p)
    while left > 0
        m = min(left, 1000)
        u = rand(rng)
        j = 0
        pj = (1 - p)^m
        F = pj
        while u > F && j < m
            j += 1
            pj *= (m - j + 1) / j * ratio
            F += pj
        end
        k += j
        left -= m
    end
    return k
end

# Negative binomial by inversion; r is split so that p^{r/m} ≥ e^{−575} (sums of independent
# negative binomials with the same p are negative binomial).
function _net_rand_negbin(rng::AbstractRNG, r::Float64, p::Float64)
    p == 1 && return 0
    m = max(1, ceil(Int, r * (-log(p)) / 575))
    rr = r / m
    q = 1 - p
    tailstart = rr * q / p
    k = 0
    for _ in 1:m
        u = rand(rng)
        j = 0
        pj = p^rr
        F = pj
        while u > F
            j += 1
            pj *= (j - 1 + rr) / j * q
            F += pj
            (pj < 1e-300 && j > tailstart) && break
        end
        k += j
    end
    return k
end

# Table sampler for finite supports (u ∈ (0, 1] skips zero-probability degrees).
struct _NetDegreeTable
    cdf::Vector{Float64}
end
# Build the table from probabilities (not through the default constructor, which takes a CDF).
function _net_degree_table(p::AbstractVector{<:Real})
    c = cumsum(Float64.(p))
    c ./= c[end]
    c[end] = 1.0
    return _NetDegreeTable(c)
end
_net_rand_table(rng::AbstractRNG, t::_NetDegreeTable) = searchsortedfirst(t.cdf, 1 - rand(rng)) - 1

struct _NetMixtureSampler{S}
    table::_NetDegreeTable
    samplers::Vector{S}
end

_net_sampler(d::DegreeDistribution) = d
_net_sampler(d::Union{PowerLawDegree,EmpiricalDegree}) = _net_degree_table(degree_probabilities(d))
_net_sampler(d::MixtureDegree) =
    _NetMixtureSampler(_net_degree_table(d.weights), [_net_sampler(c) for c in d.components])

_net_draw(rng::AbstractRNG, t::_NetDegreeTable) = _net_rand_table(rng, t)
_net_draw(rng::AbstractRNG, s::_NetMixtureSampler) =
    _net_draw(rng, s.samplers[_net_rand_table(rng, s.table) + 1])
function _net_draw(rng::AbstractRNG, d::PoissonDegree)
    _net_isnumeric(d.mean) || _net_require_numeric(d, "rand")
    return _net_rand_poisson(rng, Float64(d.mean))
end
_net_draw(rng::AbstractRNG, d::RegularDegree) = d.k
function _net_draw(rng::AbstractRNG, d::BinomialDegree)
    _net_isnumeric(d.p) || _net_require_numeric(d, "rand")
    return _net_rand_binomial(rng, d.n, Float64(d.p))
end
function _net_draw(rng::AbstractRNG, d::NegBinDegree)
    (_net_isnumeric(d.r) && _net_isnumeric(d.p)) || _net_require_numeric(d, "rand")
    return _net_rand_negbin(rng, Float64(d.r), Float64(d.p))
end
_net_draw(rng::AbstractRNG, d::Union{PowerLawDegree,EmpiricalDegree,MixtureDegree}) =
    _net_draw(rng, _net_sampler(d))
_net_draw(rng::AbstractRNG, d::DegreeDistribution) =
    throw(ArgumentError("rand is not implemented for $(typeof(d))"))

"""
    rand([rng,] d::DegreeDistribution) -> Int
    rand([rng,] d::DegreeDistribution, n::Integer) -> Vector{Int}

Draw degrees from `d` (numeric parameters only). Poisson, binomial and negative binomial
degrees are drawn by exact inversion (large parameters are split into independent pieces of
the same family); finite supports use a cumulative table, built once per call for `n` draws.
NetworkEpiCore owns the distribution types, so these methods are not type piracy.
"""
Random.rand(rng::AbstractRNG, d::DegreeDistribution) = _net_draw(rng, d)
function Random.rand(rng::AbstractRNG, d::DegreeDistribution, n::Integer)
    n >= 0 || throw(ArgumentError("rand: the number of draws must be ≥ 0; got $n"))
    s = _net_sampler(d)
    return Int[_net_draw(rng, s) for _ in 1:n]
end
Random.rand(d::DegreeDistribution) = rand(Random.default_rng(), d)
Random.rand(d::DegreeDistribution, n::Integer) = rand(Random.default_rng(), d, n)

# =============================================================================================
# Canonical text (§E.4)
# =============================================================================================

canonical_text(io::IO, d::PoissonDegree) = _netct_struct(io, "PoissonDegree", :mean => d.mean)
canonical_text(io::IO, d::RegularDegree) = _netct_struct(io, "RegularDegree", :k => d.k)
canonical_text(io::IO, d::BinomialDegree) =
    _netct_struct(io, "BinomialDegree", :n => d.n, :p => d.p)
canonical_text(io::IO, d::NegBinDegree) = _netct_struct(io, "NegBinDegree", :r => d.r, :p => d.p)
canonical_text(io::IO, d::PowerLawDegree) =
    _netct_struct(io, "PowerLawDegree", :α => d.α, :kmin => d.kmin, :kmax => d.kmax)
canonical_text(io::IO, d::EmpiricalDegree) = _netct_struct(io, "EmpiricalDegree", :p => d.p)
canonical_text(io::IO, d::MixtureDegree) =
    _netct_struct(io, "MixtureDegree", :weights => d.weights, :components => d.components)

"""
    canonical_text(d::DegreeDistribution) -> String

Canonical text of a degree distribution (§E.4): the family name with explicit field names and
`%.17g` numbers, for example `PoissonDegree(mean=5)` or `RegularDegree(k=6)`. Integer and
floating-point values of the same number print identically. Symbolic parameters are refused.
"""
canonical_text(d::DegreeDistribution) = sprint(canonical_text, d)
