# Owner: WP7 (DESIGN_NetworkEpiCore.md §C.2, §C.3; work package in §G.2).
#
# Network descriptors: the one network object shared by the back ends. EdgeBasedModels lifts a
# descriptor, NodeBasedModels closes over it, NetworkOutbreaks samples it (or runs it as a
# process). Descriptors are pure data: validated at construction, with summaries (mean and
# excess degree, clustering coefficient) and canonical text (§E.4) for hashing.
#
# Stretch descriptors (§C.3 / WP36): DegreeCorrelatedNetwork / degree_correlated (joint-degree,
# 2K), DormantContacts (Miller–Slim–Volz dormant-contact process) and MFSHNetwork (mean-field
# social heterogeneity). Each is lifted by EdgeBasedModels and simulated by NetworkOutbreaks
# (see their docstrings).

export NetworkDescriptor, WellMixed, ConfigurationNetwork, MultitypeNetwork, ClusteredDegree,
       ClusteredNetwork, NetworkProcess, NeighbourExchange, DormantContacts, DynamicNetwork,
       MultiplexNetwork, ExplicitGraph, MFSHNetwork, DegreeCorrelatedNetwork
export sbm_network, unstructured, degree_correlated
export mean_contacts, structural_zeros, excess_contacts, triangle_edge_fraction, layer_names,
       degree_assortativity

"""
    NetworkDescriptor

Abstract supertype of network descriptors (§C.2): [`WellMixed`](@ref),
[`ConfigurationNetwork`](@ref), [`MultitypeNetwork`](@ref), [`ClusteredNetwork`](@ref),
[`DynamicNetwork`](@ref), [`MultiplexNetwork`](@ref), [`ExplicitGraph`](@ref), and the stretch
descriptors [`DegreeCorrelatedNetwork`](@ref) and [`MFSHNetwork`](@ref). Every descriptor
implements [`mean_degree`](@ref) (the ⟨k⟩_net that rate conventions divide by) and
[`canonical_text`](@ref).
"""
abstract type NetworkDescriptor end

# =============================================================================================
# Well mixed
# =============================================================================================

"""
    WellMixed(κ)

A well-mixed population in which each node has κ fleeting contacts with uniformly random
partners (κ > 0, possibly symbolic). The per-capita infection hazard is κ Σ_r τ_r x_{J_r}, i.e.
β_r = κ τ_r: this is mass action, and it is the **unit** of the edge-based lift (M1), not the
η → ∞ limit of an arbitrary dynamic network (that limit is [`MFSHNetwork`](@ref) with the base's
degrees; it equals `WellMixed(κ)` only for a κ-regular base). `mean_degree(WellMixed(κ)) == κ`.
Integer and rational κ are stored as `Float64`.
"""
struct WellMixed{T} <: NetworkDescriptor
    κ::T
    function WellMixed{T}(κ) where {T}
        if _net_isnumeric(κ) && !(isfinite(κ) && κ > 0)
            throw(ArgumentError("WellMixed: κ must be finite and > 0; got $κ"))
        end
        return new{T}(κ)
    end
end
WellMixed(κ::T) where {T<:Real} = WellMixed{T}(κ)
WellMixed(κ::Union{Integer,Rational,AbstractIrrational}) = WellMixed(float(κ))

mean_degree(net::WellMixed) = net.κ
canonical_text(io::IO, net::WellMixed) = _netct_struct(io, "WellMixed", :κ => net.κ)

# =============================================================================================
# Configuration model
# =============================================================================================

"""
    ConfigurationNetwork(degrees::DegreeDistribution)

The configuration model with the given degree distribution: each node draws its degree and
stubs are paired uniformly at random (static edges). The large-N limit is locally tree-like, so
`clustering_coefficient` is 0. `pgf`, `pgf_derivative`, `mean_degree`, `excess_degree`,
`closure_constant`, `is_poisson_type` and `degree_probabilities` forward to `degrees`.
"""
struct ConfigurationNetwork{D<:DegreeDistribution} <: NetworkDescriptor
    degrees::D
end

pgf(net::ConfigurationNetwork, x) = pgf(net.degrees, x)
pgf_derivative(net::ConfigurationNetwork, x, n::Integer) = pgf_derivative(net.degrees, x, n)
mean_degree(net::ConfigurationNetwork) = mean_degree(net.degrees)
excess_degree(net::ConfigurationNetwork) = excess_degree(net.degrees)
closure_constant(net::ConfigurationNetwork) = closure_constant(net.degrees)
is_poisson_type(net::ConfigurationNetwork) = is_poisson_type(net.degrees)
degree_probabilities(net::ConfigurationNetwork; kw...) = degree_probabilities(net.degrees; kw...)
clustering_coefficient(::ConfigurationNetwork) = 0.0

Base.:(==)(a::ConfigurationNetwork, b::ConfigurationNetwork) = a.degrees == b.degrees
Base.hash(a::ConfigurationNetwork, h::UInt) = hash(a.degrees, hash(:ConfigurationNetwork, h))
canonical_text(io::IO, net::ConfigurationNetwork) =
    _netct_struct(io, "ConfigurationNetwork", :degrees => net.degrees)

# =============================================================================================
# Multitype (typed) configuration model
# =============================================================================================

"""
    MultitypeNetwork(types, sizes, degrees; check_reciprocity = true, rtol = 1e-8)
    MultitypeNetwork(; types, sizes, degrees, check_reciprocity = true, rtol = 1e-8)

A typed configuration model: a fraction `sizes[i]` of the nodes has type `types[i]`, and the
edges of a node of type a follow the law `degrees[i]` of (k_{a→b})_b (a
[`MultivariateDegree`](@ref); `degrees` may also be a `Dict{Symbol}` keyed by type).

The constructor checks that
- the types are unique, the sizes are finite, positive and sum to 1 within 1e-8 (they are
  normalised), and every law mentions only known types;
- **edge reciprocity** n_a E[k_{a→b}] = n_b E[k_{b→a}] holds for every pair (relative tolerance
  `rtol`); otherwise no network realises the laws and an `ArgumentError` lists the table of
  mismatches. A one-sided zero (E[k_{a→b}] = 0 < E[k_{b→a}]) is such a mismatch. Pairs whose
  means are symbolic are not checked, and `check_reciprocity = false` skips the check.

**Structural zeros** E[k_{a→b}] = 0 are recorded (`structural_zeros(net)`): the edge-based lift
creates no θ_{ab} coordinates for them, so no 0/0 is ever formed (verified issue E11).

Build typed networks with [`sbm_network`](@ref) and [`unstructured`](@ref); see also
[`mean_contacts`](@ref) and [`excess_contacts`](@ref).
"""
struct MultitypeNetwork <: NetworkDescriptor
    types::Vector{Symbol}
    sizes::Vector{Float64}
    degrees::Vector{MultivariateDegree}
    structural_zero::BitMatrix          # [a, b]: E[k_{a→b}] = 0 identically
    function MultitypeNetwork(types::AbstractVector{Symbol}, sizes::AbstractVector{<:Real},
                              degrees::AbstractVector{<:MultivariateDegree};
                              check_reciprocity::Bool = true, rtol::Real = 1e-8)
        K = length(types)
        K >= 1 || throw(ArgumentError("MultitypeNetwork: no types given"))
        _net_check_unique(collect(types), "MultitypeNetwork: type")
        length(sizes) == K ||
            throw(ArgumentError("MultitypeNetwork: $(length(sizes)) sizes for $K types"))
        length(degrees) == K ||
            throw(ArgumentError("MultitypeNetwork: $(length(degrees)) degree laws for $K types"))
        all(n -> _net_isnumeric(n) && isfinite(n) && n > 0, sizes) ||
            throw(ArgumentError("MultitypeNetwork: sizes must be finite and > 0; got $sizes"))
        s = sum(sizes)
        isapprox(s, 1; atol = 1e-8) ||
            throw(ArgumentError("MultitypeNetwork: the sizes (fractions of nodes) must sum to 1; " *
                                "they sum to $s"))
        n = Float64[x / s for x in sizes]
        for (a, m) in zip(types, degrees)
            unknown = setdiff(partner_types(m), types)
            isempty(unknown) ||
                throw(ArgumentError("MultitypeNetwork: the degree law of type :$a mentions " *
                                    "unknown type(s) $(join(repr.(unknown), ", ")); types are " *
                                    "$(join(repr.(types), ", "))"))
        end
        M = [mean_degree(degrees[i], types[j]) for i in 1:K, j in 1:K]
        check_reciprocity && _net_check_reciprocity(types, n, M, rtol)
        Z = BitMatrix([_net_iszero_numeric(M[i, j]) for i in 1:K, j in 1:K])
        return new(collect(types), n, collect(MultivariateDegree, degrees), Z)
    end
end
function MultitypeNetwork(types::AbstractVector{Symbol}, sizes::AbstractVector{<:Real},
                          degrees::AbstractDict{Symbol}; kw...)
    missing_types = setdiff(types, collect(keys(degrees)))
    isempty(missing_types) ||
        throw(ArgumentError("MultitypeNetwork: no degree law for type(s) $(join(repr.(missing_types), ", "))"))
    extra = setdiff(collect(keys(degrees)), types)
    isempty(extra) ||
        throw(ArgumentError("MultitypeNetwork: degree laws for unknown type(s) $(join(repr.(extra), ", "))"))
    return MultitypeNetwork(types, sizes, MultivariateDegree[degrees[a] for a in types]; kw...)
end
MultitypeNetwork(; types, sizes, degrees, kw...) = MultitypeNetwork(types, sizes, degrees; kw...)

function _net_check_reciprocity(types, n, M, rtol)
    K = length(types)
    rows = String[]
    onesided = false
    for i in 1:K, j in (i + 1):K
        (_net_isnumeric(M[i, j]) && _net_isnumeric(M[j, i])) || continue
        x, y = n[i] * M[i, j], n[j] * M[j, i]
        # a pair where exactly one side is exactly 0 is refused whatever the tolerance: the
        # structural zero of (a, b) implies that of (b, a) (WP7 review: 1e-15 against 0 passed
        # the absolute tolerance and left an asymmetric structural zero)
        side = iszero(M[i, j]) != iszero(M[j, i])
        (!side && isapprox(x, y; rtol = rtol, atol = 1e-14)) && continue
        onesided |= side
        a, b = types[i], types[j]
        push!(rows, "  $a ↔ $b:  n_$a·E[k_{$a→$b}] = $(_net_fmt(n[i])) × $(_net_fmt(M[i, j])) = " *
                    "$(_net_fmt(x))   vs   n_$b·E[k_{$b→$a}] = $(_net_fmt(n[j])) × " *
                    "$(_net_fmt(M[j, i])) = $(_net_fmt(y))")
    end
    isempty(rows) && return nothing
    msg = "MultitypeNetwork: edge reciprocity n_a·E[k_{a→b}] = n_b·E[k_{b→a}] fails " *
          "(rtol = $rtol), so no network realises these degree laws. Mismatches:\n" *
          join(rows, "\n")
    onesided && (msg *= "\n(A one-sided zero, E[k_{a→b}] = 0 < E[k_{b→a}], describes no network.)")
    throw(ArgumentError(msg))
end
_net_fmt(x) = _net_isnumeric(x) ? @sprintf("%.6g", x) : string(x)

"""
    mean_contacts(net::MultitypeNetwork) -> Matrix

The matrix M[a, b] = E[k_{a→b}] of mean numbers of edges from a node of type a to nodes of type
b (rows and columns in `net.types` order). Reciprocity reads n_a M[a, b] = n_b M[b, a].
"""
mean_contacts(net::MultitypeNetwork) =
    [mean_degree(net.degrees[i], net.types[j]) for i in eachindex(net.types), j in eachindex(net.types)]

"""
    structural_zeros(net::MultitypeNetwork) -> Vector{Tuple{Symbol,Symbol}}

The ordered type pairs (a, b) with E[k_{a→b}] = 0 identically: nodes of type a never have
edges to type b. By reciprocity (b, a) is then a structural zero too. The lift skips them.
"""
structural_zeros(net::MultitypeNetwork) =
    [(net.types[i], net.types[j]) for i in eachindex(net.types), j in eachindex(net.types)
     if net.structural_zero[i, j]] |> vec

"""
    excess_contacts(net::MultitypeNetwork) -> Array{Float64,3}

X[a, b, c]: the expected number of type-c partners of a type-b node reached along a random edge
from a type-a node, not counting that edge, X[a, b, c] = ∂_a ∂_c ψ_b(1)/∂_a ψ_b(1). It is 0 for a
structural zero (a, b) (no such edges, so no 0/0). For a single type it is the excess degree;
for `SplitDegrees` it is w_c κ_ex. For a single-entry SIR-type model with per-edge
transmissibility T, the next-generation matrix over edge types (a→b) is
K[(a→b), (b→c)] = T X[a, b, c]. Numeric parameters only.
"""
function excess_contacts(net::MultitypeNetwork)
    K = length(net.types)
    X = zeros(Float64, K, K, K)
    for i in 1:K, j in 1:K
        net.structural_zero[j, i] && continue            # the b-node has no edges back to a
        a = net.types[i]
        m = net.degrees[j]
        first_moment = _net_mv_moment(m, a)              # E[k_{b→a}]
        _net_isnumeric(first_moment) ||
            throw(ArgumentError("excess_contacts needs numeric parameters"))
        iszero(first_moment) && continue
        for k in 1:K
            X[i, j, k] = _net_mv_moment(m, a, net.types[k]) / first_moment
        end
    end
    return X
end

"""
    mean_degree(net::MultitypeNetwork)

The total mean degree Σ_a n_a Σ_b E[k_{a→b}] (the ⟨k⟩_net of the rate conventions, §B.6).
"""
mean_degree(net::MultitypeNetwork) = sum(n * mean_degree(m) for (n, m) in zip(net.sizes, net.degrees))

function Base.:(==)(a::MultitypeNetwork, b::MultitypeNetwork)
    return a.types == b.types && a.sizes == b.sizes && length(a.degrees) == length(b.degrees) &&
           all(a.degrees .== b.degrees)
end
Base.hash(a::MultitypeNetwork, h::UInt) =
    hash(a.degrees, hash(a.sizes, hash(a.types, hash(:MultitypeNetwork, h))))

canonical_text(io::IO, net::MultitypeNetwork) =
    _netct_struct(io, "MultitypeNetwork", :types => net.types, :sizes => net.sizes,
                  :degrees => net.degrees)

function Base.show(io::IO, ::MIME"text/plain", net::MultitypeNetwork)
    println(io, "MultitypeNetwork with $(length(net.types)) types")
    for (a, n, m) in zip(net.types, net.sizes, net.degrees)
        print(io, "  :", a, "  size ", _net_fmt(n), "  ")
        try
            print(io, canonical_text(m))                 # numeric laws: the canonical form
        catch err
            err isa ArgumentError || rethrow()
            show(io, m)                                   # symbolic parameters
        end
        println(io)
    end
    z = structural_zeros(net)
    print(io, "  structural zeros: ", isempty(z) ? "none" : join(("$a→$b" for (a, b) in z), ", "))
end

# ---- typed-network constructors over strata --------------------------------------------------

"""
    sbm_network(st::Strata; mean_contacts::AbstractMatrix, family = PoissonDegree)
    sbm_network(types::AbstractVector{Symbol}, sizes; mean_contacts, family = PoissonDegree)

A stochastic block model as a [`MultitypeNetwork`](@ref): a node of type a has
k_{a→b} ~ `family(mean_contacts[a, b])` independent edges to type b ([`IndependentDegrees`](@ref);
`family` is any callable mean ↦ `DegreeDistribution`, e.g. `RegularDegree` or
`m -> NegBinDegree(mean = m, var = 2m)`). Zero entries are structural zeros. The strata sizes
must satisfy reciprocity n_a M[a, b] = n_b M[b, a]; for example sizes (0.4, 0.6) with
`mean_contacts = [6 3; 2 4]` (0.4·3 = 0.6·2).
"""
function sbm_network(types::AbstractVector{Symbol}, sizes::AbstractVector{<:Real};
                     mean_contacts::AbstractMatrix{<:Real}, family = PoissonDegree)
    K = length(types)
    size(mean_contacts) == (K, K) ||
        throw(ArgumentError("sbm_network: mean_contacts must be $K×$K for types " *
                            "$(join(repr.(types), ", ")); got $(size(mean_contacts))"))
    all(x -> _net_isnumeric(x) && isfinite(x) && x >= 0, mean_contacts) ||
        throw(ArgumentError("sbm_network: mean_contacts must be finite and ≥ 0"))
    degrees = MultivariateDegree[
        IndependentDegrees(Pair{Symbol,DegreeDistribution}[types[j] => family(mean_contacts[i, j])
                                                           for j in 1:K if mean_contacts[i, j] > 0])
        for i in 1:K]
    return MultitypeNetwork(types, sizes, degrees)
end
sbm_network(st::Strata; mean_contacts::AbstractMatrix{<:Real}, family = PoissonDegree) =
    sbm_network(st.names, st.sizes; mean_contacts, family)

"""
    unstructured(net::ConfigurationNetwork, st::Strata)
    unstructured(net::ConfigurationNetwork, types::AbstractVector{Symbol}, sizes)
    unstructured(d::DegreeDistribution, ...)       # = unstructured(ConfigurationNetwork(d), ...)

Types independent of the network: every node keeps the degree law of `net`, and each of its
stubs goes to a type-b partner with probability n_b ([`SplitDegrees`](@ref)), so
ψ_a(x) = ψ(Σ_b n_b x_b). Reciprocity holds automatically (n_a ⟨k⟩ n_b = n_b ⟨k⟩ n_a), and the
stratified model on this network reproduces the unstratified one (the unit law M10).
"""
function unstructured(net::ConfigurationNetwork, types::AbstractVector{Symbol},
                      sizes::AbstractVector{<:Real})
    length(sizes) == length(types) ||
        throw(ArgumentError("unstructured: $(length(sizes)) sizes for $(length(types)) types"))
    all(x -> _net_isnumeric(x) && isfinite(x) && x > 0, sizes) ||
        throw(ArgumentError("unstructured: sizes must be finite and > 0; got $sizes"))
    s = sum(sizes)
    weights = Pair{Symbol,Float64}[b => w / s for (b, w) in zip(types, sizes)]
    degrees = MultivariateDegree[SplitDegrees(net.degrees, weights) for _ in types]
    return MultitypeNetwork(types, sizes, degrees)
end
unstructured(net::ConfigurationNetwork, st::Strata) = unstructured(net, st.names, st.sizes)
unstructured(d::DegreeDistribution, args...) = unstructured(ConfigurationNetwork(d), args...)

# =============================================================================================
# Clustered (Newman–Miller) configuration model
# =============================================================================================

"""
    ClusteredDegree(singles::DegreeDistribution, triangles::DegreeDistribution)
    ClusteredDegree(P::AbstractMatrix)          # P[s+1, t+1] = P(s single edges, t triangles)

The law of (s, t) in the Newman–Miller clustered configuration model: a node has s single stubs
(paired uniformly into single edges) and belongs to t triangles (triangle corners are grouped in
threes), so its degree is k = s + 2t. The two-argument form draws s and t independently; the
matrix form is a joint law (finite, ≥ 0, summing to 1 within 1e-8; normalised, trailing zero
rows and columns dropped).

The bivariate PGF is g(x, y) = E[xˢ yᵗ] ([`pgf`](@ref)`(cd, x, y)`, partial derivatives
[`pgf_derivative`](@ref)`(cd, x, y, i, j)` = ∂ˣⁱ∂ʸʲ g), and the degree PGF is G(z) = g(z, z²).
"""
struct ClusteredDegree{J}
    joint::J
    function ClusteredDegree{J}(joint) where {J}
        return new{J}(_net_clustered_joint(joint))
    end
end
ClusteredDegree(s::DegreeDistribution, t::DegreeDistribution) =
    ClusteredDegree{Tuple{typeof(s),typeof(t)}}((s, t))
ClusteredDegree(P::AbstractMatrix{<:Real}) = ClusteredDegree{Matrix{Float64}}(P)

_net_clustered_joint(j::Tuple{DegreeDistribution,DegreeDistribution}) = j
function _net_clustered_joint(P::AbstractMatrix{<:Real})
    isempty(P) && throw(ArgumentError("ClusteredDegree: the joint law is empty"))
    all(x -> _net_isnumeric(x) && isfinite(x) && x >= 0, P) ||
        throw(ArgumentError("ClusteredDegree: joint probabilities must be finite and ≥ 0"))
    s = sum(P)
    isapprox(s, 1; atol = 1e-8) ||
        throw(ArgumentError("ClusteredDegree: the joint probabilities must sum to 1; they sum to $s"))
    rows = findlast(i -> any(>(0), P[i, :]), axes(P, 1))
    cols = findlast(j -> any(>(0), P[:, j]), axes(P, 2))
    return Matrix{Float64}(P[firstindex(P, 1):rows, firstindex(P, 2):cols] ./ s)
end
_net_clustered_joint(x) =
    throw(ArgumentError("ClusteredDegree: expected two degree distributions or a joint " *
                        "probability matrix; got $(typeof(x))"))

function pgf(cd::ClusteredDegree{<:Tuple}, x, y)
    s, t = cd.joint
    return pgf(s, x) * pgf(t, y)
end
function pgf_derivative(cd::ClusteredDegree{<:Tuple}, x, y, i::Integer, j::Integer)
    s, t = cd.joint
    return pgf_derivative(s, x, i) * pgf_derivative(t, y, j)
end
pgf(cd::ClusteredDegree{Matrix{Float64}}, x, y) = pgf_derivative(cd, x, y, 0, 0)
function pgf_derivative(cd::ClusteredDegree{Matrix{Float64}}, x, y, i::Integer, j::Integer)
    _net_check_order(i)
    _net_check_order(j)
    P = cd.joint
    acc = nothing
    for a in axes(P, 1), b in axes(P, 2)
        s, t = a - 1, b - 1
        (P[a, b] == 0 || s < i || t < j) && continue
        term = (P[a, b] * _net_falling(float(s), i) * _net_falling(float(t), j)) * x^(s - i) * y^(t - j)
        acc = acc === nothing ? term : acc + term
    end
    return acc === nothing ? zero(x) * zero(y) : acc
end

# ∂ˣⁱ∂ʸʲ g(1, 1) in closed form.
function _net_cl_moment(cd::ClusteredDegree{<:Tuple}, i, j)
    s, t = cd.joint
    return _net_factorial_moment(s, i) * _net_factorial_moment(t, j)
end
_net_cl_moment(cd::ClusteredDegree{Matrix{Float64}}, i, j) =
    sum(cd.joint[a, b] * _net_falling(float(a - 1), i) * _net_falling(float(b - 1), j)
        for a in axes(cd.joint, 1), b in axes(cd.joint, 2))

# G'(1) = g_x + 2g_y and G''(1) = g_xx + 4g_xy + 4g_yy + 2g_y at (1, 1), for G(z) = g(z, z²).
_net_cl_G1(cd) = _net_cl_moment(cd, 1, 0) + 2 * _net_cl_moment(cd, 0, 1)
_net_cl_G2(cd) = _net_cl_moment(cd, 2, 0) + 4 * _net_cl_moment(cd, 1, 1) +
                 4 * _net_cl_moment(cd, 0, 2) + 2 * _net_cl_moment(cd, 0, 1)

mean_degree(cd::ClusteredDegree) = _net_cl_G1(cd)
function excess_degree(cd::ClusteredDegree)
    m = _net_cl_G1(cd)
    _net_iszero_numeric(m) && throw(ArgumentError("the excess degree is undefined: no edges"))
    return _net_cl_G2(cd) / m
end

"""
    clustering_coefficient(net::ClusteredNetwork)
    clustering_coefficient(cd::ClusteredDegree)

The clustering coefficient (transitivity) C = 3N_Δ/N_∧ = 2E[t]/E[k(k − 1)] with k = s + 2t, i.e.
2 g_y(1,1)/G''(1) with G(z) = g(z, z²) (Volz et al. 2011; verified issue E03). It is 0 when
E[t] = 0. For example C = 2·2/30 = 2/15 for `ClusteredNetwork(RegularDegree(2), RegularDegree(2))`
and 2κ_t/((κ_s + 2κ_t)² + 2κ_t) for Poisson (κ_s, κ_t). The fraction of edges that lie in
triangles, which the legacy EBM function returned, is [`triangle_edge_fraction`](@ref).
"""
function clustering_coefficient(cd::ClusteredDegree)
    gy = _net_cl_moment(cd, 0, 1)
    _net_iszero_numeric(gy) && return 0.0
    return 2 * gy / _net_cl_G2(cd)
end

"""
    triangle_edge_fraction(net::ClusteredNetwork)
    triangle_edge_fraction(cd::ClusteredDegree)

The fraction of edges that lie in triangles, 2E[t]/(E[s] + 2E[t]) (Volz's p_t). This is **not**
the clustering coefficient ([`clustering_coefficient`](@ref)); the two are related by
C = p_t G'(1)/G''(1). It is 0 when there are no edges.
"""
function triangle_edge_fraction(cd::ClusteredDegree)
    m = _net_cl_G1(cd)
    _net_iszero_numeric(m) && return 0.0
    return 2 * _net_cl_moment(cd, 0, 1) / m
end

"""
    rand([rng,] cd::ClusteredDegree) -> Tuple{Int,Int}

Draw (s, t): the numbers of single stubs and of triangles of a node.
"""
function Random.rand(rng::AbstractRNG, cd::ClusteredDegree{<:Tuple})
    s, t = cd.joint
    return (rand(rng, s), rand(rng, t))
end
function Random.rand(rng::AbstractRNG, cd::ClusteredDegree{Matrix{Float64}})
    idx = _net_rand_table(rng, _net_degree_table(vec(cd.joint))) + 1
    ci = CartesianIndices(cd.joint)[idx]
    return (ci[1] - 1, ci[2] - 1)
end
Random.rand(cd::ClusteredDegree) = rand(Random.default_rng(), cd)

Base.:(==)(a::ClusteredDegree, b::ClusteredDegree) = typeof(a) == typeof(b) && a.joint == b.joint
Base.hash(a::ClusteredDegree, h::UInt) = hash(a.joint, hash(:ClusteredDegree, h))

function canonical_text(io::IO, cd::ClusteredDegree{<:Tuple})
    s, t = cd.joint
    return _netct_struct(io, "ClusteredDegree", :singles => s, :triangles => t)
end
canonical_text(io::IO, cd::ClusteredDegree{Matrix{Float64}}) =
    _netct_struct(io, "ClusteredDegree", :p_st => cd.joint)
canonical_text(cd::ClusteredDegree) = sprint(canonical_text, cd)

"""
    ClusteredNetwork(joint::ClusteredDegree)
    ClusteredNetwork(singles::DegreeDistribution, triangles::DegreeDistribution)
    ClusteredNetwork(P::AbstractMatrix)

The Newman–Miller clustered configuration model with (s, t) ~ `joint` ([`ClusteredDegree`](@ref)).
`mean_degree` = E[s] + 2E[t], `excess_degree` = G''(1)/G'(1), and
[`clustering_coefficient`](@ref) = 2E[t]/E[k(k − 1)] (2/15 for
`ClusteredNetwork(RegularDegree(2), RegularDegree(2))`, degree 6).
"""
struct ClusteredNetwork{J} <: NetworkDescriptor
    joint::ClusteredDegree{J}
end
ClusteredNetwork(s::DegreeDistribution, t::DegreeDistribution) = ClusteredNetwork(ClusteredDegree(s, t))
ClusteredNetwork(P::AbstractMatrix{<:Real}) = ClusteredNetwork(ClusteredDegree(P))

mean_degree(net::ClusteredNetwork) = mean_degree(net.joint)
excess_degree(net::ClusteredNetwork) = excess_degree(net.joint)
clustering_coefficient(net::ClusteredNetwork) = clustering_coefficient(net.joint)
triangle_edge_fraction(net::ClusteredNetwork) = triangle_edge_fraction(net.joint)
pgf(net::ClusteredNetwork, x, y) = pgf(net.joint, x, y)
pgf_derivative(net::ClusteredNetwork, x, y, i::Integer, j::Integer) = pgf_derivative(net.joint, x, y, i, j)

Base.:(==)(a::ClusteredNetwork, b::ClusteredNetwork) = a.joint == b.joint
Base.hash(a::ClusteredNetwork, h::UInt) = hash(a.joint, hash(:ClusteredNetwork, h))
canonical_text(io::IO, net::ClusteredNetwork) = _netct_struct(io, "ClusteredNetwork", :joint => net.joint)

# =============================================================================================
# Dynamic networks
# =============================================================================================

"""
    NetworkProcess

Abstract supertype of edge processes on a [`DynamicNetwork`](@ref): [`NeighbourExchange`](@ref)
(dynamic fixed degree) and the stretch [`DormantContacts`](@ref).
"""
abstract type NetworkProcess end

function _net_check_rate(x, what)
    if _net_isnumeric(x) && !(isfinite(x) && x >= 0)
        throw(ArgumentError("$what must be finite and ≥ 0; got $x"))
    end
    return x
end

"""
    NeighbourExchange(η)

Neighbour exchange (Miller–Slim–Volz dynamic fixed-degree, DFD): each edge breaks at the
**per-edge** rate η, and the freed stubs immediately rejoin other freed stubs at random, so
degrees never change. NetworkOutbreaks realises it as degree-preserving double-edge swaps at
total rate ηE/2 (two edges per swap), so that each edge rewires at rate η. η = 0 is the static
configuration model; η → ∞ gives [`MFSHNetwork`](@ref) with the base's degrees. η may be
symbolic; integer and rational values are stored as `Float64`.
"""
struct NeighbourExchange{T} <: NetworkProcess
    η::T
    NeighbourExchange{T}(η) where {T} = new{T}(_net_check_rate(η, "NeighbourExchange: η"))
end
NeighbourExchange(η::T) where {T<:Real} = NeighbourExchange{T}(η)
NeighbourExchange(η::Union{Integer,Rational,AbstractIrrational}) = NeighbourExchange(float(η))

"""
    DormantContacts(η_form, η_break)
    DormantContacts(; η_form, η_break)

The Miller–Slim–Volz dormant-contact (DC) process (Part II, §3.2.4), a stretch descriptor
(WP36b). EdgeBasedModels lifts it with
`edge_based(cm, DynamicNetwork(base, DormantContacts(η_form = η₁, η_break = η₂)))` (the
expanded form, for every T_EB model; this replaces the legacy η₁ semantics of
`DynamicConfigurationModel`), and NetworkOutbreaks simulates it with `DormantContactProcess`,
through `simulate(model, DynamicNetwork(…); N, …)` or `sample_graph(net, N; rng)`, under
NextReaction and HAS. Each node has k_m stubs, k_m drawn from the
base degree distribution of the [`DynamicNetwork`](@ref); a stub is active (part of an edge) or
dormant. Active edges break at rate `η_break` (MSV's η₂) and their stubs become dormant; dormant
stubs become active, pairing with other activating stubs, at rate `η_form` (MSV's η₁). A stub is
active with probability ξ = η_form/(η_form + η_break), so `mean_degree` of the network is ξ⟨k_m⟩.
The DC model contains dynamic fixed degree (η_form ≫ η_break), dynamic variable degree
(η_break ≫ η_form with large k_m) and MFSH (large degrees with τ⟨k⟩ fixed) as limits.
"""
struct DormantContacts{T} <: NetworkProcess
    η_form::T
    η_break::T
    function DormantContacts{T}(η_form, η_break) where {T}
        _net_check_rate(η_form, "DormantContacts: η_form")
        _net_check_rate(η_break, "DormantContacts: η_break")
        if _net_isnumeric(η_form) && _net_isnumeric(η_break) && η_form + η_break == 0
            throw(ArgumentError("DormantContacts: η_form + η_break must be > 0"))
        end
        return new{T}(η_form, η_break)
    end
end
function DormantContacts(η_form::Real, η_break::Real)
    a, b = promote(_net_float(η_form), _net_float(η_break))
    return DormantContacts{typeof(a)}(a, b)
end
DormantContacts(; η_form::Real, η_break::Real) = DormantContacts(η_form, η_break)

canonical_text(io::IO, p::NeighbourExchange) = _netct_struct(io, "NeighbourExchange", :η => p.η)
canonical_text(io::IO, p::DormantContacts) =
    _netct_struct(io, "DormantContacts", :η_form => p.η_form, :η_break => p.η_break)
canonical_text(p::NetworkProcess) = sprint(canonical_text, p)

"""
    DynamicNetwork(base::ConfigurationNetwork, process::NetworkProcess)
    DynamicNetwork(degrees::DegreeDistribution, process::NetworkProcess)

A configuration network whose edges change by `process`. With [`NeighbourExchange`](@ref)`(η)`
it is the dynamic fixed-degree (DFD) model: the edge-based lift is Miller–Slim–Volz DFD with
M_S = θψ'(θ)/ψ'(1) and the seed factor q; η = 0 is the static model. With
[`DormantContacts`](@ref) (stretch), `base` gives the maximum degrees k_m.
`mean_degree` is ⟨k⟩ of the base for neighbour exchange and ξ⟨k_m⟩ for dormant contacts.
"""
struct DynamicNetwork{P<:NetworkProcess} <: NetworkDescriptor
    base::ConfigurationNetwork
    process::P
end
DynamicNetwork(d::DegreeDistribution, process::NetworkProcess) =
    DynamicNetwork(ConfigurationNetwork(d), process)

mean_degree(net::DynamicNetwork) = mean_degree(net.base)
excess_degree(net::DynamicNetwork{<:NeighbourExchange}) = excess_degree(net.base)
function mean_degree(net::DynamicNetwork{<:DormantContacts})
    p = net.process
    return p.η_form / (p.η_form + p.η_break) * mean_degree(net.base)
end

Base.:(==)(a::DynamicNetwork, b::DynamicNetwork) = a.base == b.base && a.process == b.process
Base.hash(a::DynamicNetwork, h::UInt) = hash(a.process, hash(a.base, hash(:DynamicNetwork, h)))
canonical_text(io::IO, net::DynamicNetwork) =
    _netct_struct(io, "DynamicNetwork", :base => net.base, :process => net.process)

# =============================================================================================
# Multiplex
# =============================================================================================

"""
    MultiplexNetwork(ℓ₁ => net₁, ℓ₂ => net₂, ...)
    MultiplexNetwork(layers::Vector{Pair{Symbol,ConfigurationNetwork}})

Independent configuration-network layers on the same node set (Miller–Volz 2013); a layer may
be given as a `ConfigurationNetwork` or as a `DegreeDistribution`. Layer names are unique and
`:all` is reserved (a `Contact` with `layer = :all` acts on every layer with the same τ).
`mean_degree(net)` is the total Σ_ℓ ⟨k_ℓ⟩ and `mean_degree(net, ℓ)` a layer's mean
(`mean_degree(net, :all)` is the total); `net[ℓ]` is a layer and [`layer_names`](@ref) lists
them. R₀ on a multiplex is ρ(K) over (layer, entry) blocks, never the sum of layer R₀s.
"""
struct MultiplexNetwork <: NetworkDescriptor
    layers::Vector{Pair{Symbol,ConfigurationNetwork}}
    function MultiplexNetwork(layers::Vector{Pair{Symbol,ConfigurationNetwork}})
        isempty(layers) && throw(ArgumentError("MultiplexNetwork: no layers given"))
        names = [first(l) for l in layers]
        _net_check_unique(names, "MultiplexNetwork: layer")
        :all in names &&
            throw(ArgumentError("MultiplexNetwork: the layer name :all is reserved (a contact " *
                                "with layer = :all acts on every layer)"))
        return new(layers)
    end
end
_net_as_configuration(x::ConfigurationNetwork) = x
_net_as_configuration(x::DegreeDistribution) = ConfigurationNetwork(x)
_net_as_configuration(x) =
    throw(ArgumentError("MultiplexNetwork: a layer must be a ConfigurationNetwork or a " *
                        "DegreeDistribution; got $(typeof(x))"))
MultiplexNetwork(layers::AbstractVector{<:Pair}) =
    MultiplexNetwork(Pair{Symbol,ConfigurationNetwork}[Symbol(l) => _net_as_configuration(n) for (l, n) in layers])
MultiplexNetwork(layers::Pair{Symbol,<:Union{ConfigurationNetwork,DegreeDistribution}}...) =
    MultiplexNetwork(Pair{Symbol,ConfigurationNetwork}[l => _net_as_configuration(n) for (l, n) in layers])

"""
    layer_names(net::MultiplexNetwork) -> Vector{Symbol}

The layer names of a multiplex network, in order.
"""
layer_names(net::MultiplexNetwork) = Symbol[first(l) for l in net.layers]

function Base.getindex(net::MultiplexNetwork, ℓ::Symbol)
    for (name, layer) in net.layers
        name === ℓ && return layer
    end
    throw(KeyError(ℓ))
end

mean_degree(net::MultiplexNetwork) = sum(mean_degree(layer) for (_, layer) in net.layers)
mean_degree(net::MultiplexNetwork, ℓ::Symbol) = ℓ === :all ? mean_degree(net) : mean_degree(net[ℓ])

Base.:(==)(a::MultiplexNetwork, b::MultiplexNetwork) =
    layer_names(a) == layer_names(b) && all(last(x) == last(y) for (x, y) in zip(a.layers, b.layers))
Base.hash(a::MultiplexNetwork, h::UInt) = hash(a.layers, hash(:MultiplexNetwork, h))
canonical_text(io::IO, net::MultiplexNetwork) = _netct_struct(io, "MultiplexNetwork", :layers => net.layers)

# =============================================================================================
# Explicit graph
# =============================================================================================

"""
    ExplicitGraph(g)

A fixed, explicit undirected graph (any `Graphs.AbstractGraph`). It is not an edge-based object:
EdgeBasedModels refuses it (use `ConfigurationNetwork(EmpiricalDegree(g))` for the annealed
approximation), NodeBasedModels runs individual-, pair-, motif- and neighbourhood-level models on
it, and NetworkOutbreaks simulates on it as is. With Graphs loaded
(`NetworkEpiCoreGraphsExt`), directed graphs are refused, and `mean_degree`, `excess_degree`,
`clustering_coefficient` (the transitivity) and `canonical_text` (the sorted edge list) are
available.
"""
struct ExplicitGraph{G} <: NetworkDescriptor
    graph::G
    function ExplicitGraph{G}(graph) where {G}
        _net_check_explicit_graph(graph)
        return new{G}(graph)
    end
end
ExplicitGraph(graph::G) where {G} = ExplicitGraph{G}(graph)

# Validation hook: the Graphs extension adds a method for Graphs.AbstractGraph.
function _net_check_explicit_graph(graph)
    graph isa Union{NetworkDescriptor,DegreeDistribution} &&
        throw(ArgumentError("ExplicitGraph wraps an explicit graph (e.g. a Graphs.SimpleGraph); " *
                            "got the descriptor $(graph)"))
    return nothing
end

# =============================================================================================
# Stretch: mean-field social heterogeneity
# =============================================================================================

"""
    MFSHNetwork(degrees::DegreeDistribution)

Mean-field social heterogeneity (MFSH; Miller–Slim–Volz Part II, §3.2.2, actual-degree
formulation), a stretch descriptor (WP36c). EdgeBasedModels lifts it with
`edge_based(cm, MFSHNetwork(d))` (form `:expanded` or `:compact`, every T_EB model), and
NetworkOutbreaks simulates it with `simulate(model, MFSHNetwork(d); N, …)` and
`FleetingContactSSA` (scenario algorithm `:fleeting`), in which each contact of a stub is with a
uniformly chosen stub of the other nodes. Each node has k stubs,
k ~ `degrees`, but its partners change so fast that successive contacts are independent
(fleeting contacts with heterogeneous activity). The EB equations are
θ̇ = −τθ + τθ·θψ'(θ)/ψ'(1) − γθ ln θ with S = ψ(θ) (SIR).
`MFSHNetwork(RegularDegree(κ))` is `WellMixed(κ)` (mass action), and MFSH with the base's
degrees is the η → ∞ limit of `DynamicNetwork(base, NeighbourExchange(η))`.
`mean_degree` is ⟨k⟩ of `degrees`.
"""
struct MFSHNetwork{D<:DegreeDistribution} <: NetworkDescriptor
    degrees::D
end
mean_degree(net::MFSHNetwork) = mean_degree(net.degrees)
Base.:(==)(a::MFSHNetwork, b::MFSHNetwork) = a.degrees == b.degrees
Base.hash(a::MFSHNetwork, h::UInt) = hash(a.degrees, hash(:MFSHNetwork, h))
canonical_text(io::IO, net::MFSHNetwork) = _netct_struct(io, "MFSHNetwork", :degrees => net.degrees)

# =============================================================================================
# Stretch: degree-correlated (joint-degree, 2K) configuration model
# =============================================================================================

"""
    DegreeCorrelatedNetwork(degrees, probabilities, edge_ends)

A configuration model with degree correlations between neighbours (the joint-degree or "2K"
model), a stretch descriptor (WP36a). EdgeBasedModels lifts it with its degree-class closure,
the exact quotient of the multitype form; NetworkOutbreaks samples it with a joint-degree (2K)
generator; the lift is validated against the ensemble (the `:sir_dc_bim_*` scenarios).
Build it with [`degree_correlated`](@ref).

Fields, on the support of the degree distribution only (degrees with pₖ > 0, ascending):
- `degrees::Vector{Int}` and `probabilities::Vector{Float64}` (pₖ, summing to 1);
- `edge_ends::Matrix{Float64}`: e[k, l], the probability that a uniformly random edge joins a
  degree-k and a degree-l node (symmetric, summing to 1), with marginal Σ_l e_kl = k pₖ/⟨k⟩.
  This is indexed by degree, not by excess degree as in Newman (2002).

Restricting to the support removes the spurious eigenvalues r(k − 1) of empty degree classes
from the next-generation matrix (verified issue E20). `MultitypeNetwork(net)` gives the
multitype form: one type `Symbol("k", k)` per degree class, of size pₖ, with
`SplitDegrees(RegularDegree(k), l => Q(l | k))` and Q(l | k) = e_kl/Σ_m e_km (reciprocity holds
because e is symmetric). `mean_degree` and `excess_degree` are those of the marginal degree
distribution; [`degree_assortativity`](@ref) is Newman's r.
"""
struct DegreeCorrelatedNetwork <: NetworkDescriptor
    degrees::Vector{Int}
    probabilities::Vector{Float64}
    edge_ends::Matrix{Float64}
    function DegreeCorrelatedNetwork(degrees::AbstractVector{<:Integer},
                                     probabilities::AbstractVector{<:Real},
                                     edge_ends::AbstractMatrix{<:Real}; rtol::Real = 1e-8)
        K = length(degrees)
        K >= 1 || throw(ArgumentError("DegreeCorrelatedNetwork: no degree classes given"))
        allunique(degrees) && issorted(degrees) && all(>=(0), degrees) ||
            throw(ArgumentError("DegreeCorrelatedNetwork: degrees must be distinct, ascending " *
                                "and ≥ 0; got $degrees"))
        length(probabilities) == K && size(edge_ends) == (K, K) ||
            throw(ArgumentError("DegreeCorrelatedNetwork: $K degrees need $K probabilities and a " *
                                "$K×$K edge_ends matrix"))
        all(p -> _net_isnumeric(p) && isfinite(p) && p > 0, probabilities) ||
            throw(ArgumentError("DegreeCorrelatedNetwork: probabilities must be finite and > 0 " *
                                "(restrict to the support); got $probabilities"))
        s = sum(probabilities)
        isapprox(s, 1; atol = 1e-8) ||
            throw(ArgumentError("DegreeCorrelatedNetwork: probabilities sum to $s, not 1"))
        p = Float64[x / s for x in probabilities]
        e = Matrix{Float64}(edge_ends)
        all(x -> isfinite(x) && x >= 0, e) ||
            throw(ArgumentError("DegreeCorrelatedNetwork: edge_ends must be finite and ≥ 0"))
        kbar = sum(degrees .* p)
        kbar > 0 || throw(ArgumentError("DegreeCorrelatedNetwork: the mean degree is 0 (no edges)"))
        isapprox(sum(e), 1; atol = 1e-8) ||
            throw(ArgumentError("DegreeCorrelatedNetwork: edge_ends sums to $(sum(e)), not 1"))
        e ./= sum(e)
        isapprox(e, transpose(e); rtol = rtol, atol = 1e-12) ||
            throw(ArgumentError("DegreeCorrelatedNetwork: edge_ends must be symmetric (an edge " *
                                "has two ends)"))
        e .= (e .+ transpose(e)) ./ 2
        q = vec(sum(e; dims = 2))
        target = degrees .* p ./ kbar
        bad = [i for i in 1:K if !isapprox(q[i], target[i]; rtol = rtol, atol = 1e-10)]
        isempty(bad) ||
            throw(ArgumentError("DegreeCorrelatedNetwork: the edge-end marginal Σ_l e_kl must " *
                                "equal k pₖ/⟨k⟩; it fails for degree(s) " *
                                join(("$(degrees[i]) ($(_net_fmt(q[i])) vs $(_net_fmt(target[i])))"
                                      for i in bad), ", ")))
        return new(collect(Int, degrees), p, e)
    end
end

"""
    degree_correlated(p::AbstractVector, e::AbstractMatrix)
    degree_correlated(d::DegreeDistribution, e::AbstractMatrix)
    degree_correlated(d::DegreeDistribution; r::Real, tol = 1e-12)

Build a [`DegreeCorrelatedNetwork`](@ref) (stretch).

- `p[k+1] = P(K = k)` and `e[k+1, l+1]` = the probability that a random edge joins degrees k
  and l (symmetric, summing to 1, with Σ_l e_kl = k pₖ/⟨k⟩). Degree classes with pₖ = 0 must
  have zero rows and are dropped (support restriction, verified issue E20).
- With a `DegreeDistribution` `d`, `p = degree_probabilities(d; tol)` (zero-padded to `e`).
- With `r`, Newman's assortative mixing on the support of `d`: e_kl = r q_k δ_kl + (1 − r) q_k q_l
  with q_k = k pₖ/⟨k⟩, whose degree assortativity is exactly `r`. Assortativity (r > 0) never
  lowers R₀ in this family. Infinite-support distributions are truncated where the tail is below
  `tol`; tail classes with tiny pₖ carry localised eigenvalues ≈ r(k − 1), so R₀ depends on the
  truncation (a limitation of the r-mixing model, E20).
"""
function degree_correlated(p::AbstractVector{<:Real}, e::AbstractMatrix{<:Real}; rtol::Real = 1e-8)
    K = length(p)
    size(e) == (K, K) ||
        throw(ArgumentError("degree_correlated: e must be $K×$K to match p (indices k+1, l+1); " *
                            "got $(size(e))"))
    all(x -> _net_isnumeric(x) && isfinite(x) && x >= 0, p) ||
        throw(ArgumentError("degree_correlated: probabilities must be finite and ≥ 0"))
    support = [i for i in 1:K if p[i] > 0]
    absent = setdiff(1:K, support)
    for i in absent
        (any(!iszero, e[i, :]) || any(!iszero, e[:, i])) &&
            throw(ArgumentError("degree_correlated: degree $(i - 1) has P(K = $(i - 1)) = 0 but " *
                                "a non-zero row or column in e (edges to an empty class)"))
    end
    return DegreeCorrelatedNetwork(support .- 1, p[support], e[support, support]; rtol)
end
function degree_correlated(d::DegreeDistribution, e::AbstractMatrix{<:Real}; tol::Real = 1e-12,
                           rtol::Real = 1e-8)
    p = degree_probabilities(d; tol)
    length(p) <= size(e, 1) ||
        throw(ArgumentError("degree_correlated: $(d) has degrees up to $(length(p) - 1) but e " *
                            "covers degrees 0:$(size(e, 1) - 1)"))
    return degree_correlated(vcat(p, zeros(size(e, 1) - length(p))), e; rtol)
end
function degree_correlated(d::DegreeDistribution; r::Real, tol::Real = 1e-12)
    p = degree_probabilities(d; tol)
    support = [i for i in eachindex(p) if p[i] > 0 && i > 1]     # degree-0 nodes have no edge ends
    ks = support .- 1
    q = ks .* p[support]
    q ./= sum(q)
    # e_kl ≥ 0 needs r ≤ 1 (off the diagonal) and r ≥ −min_k q_k/(1 − q_k) (on it)
    rmin = length(q) > 1 ? -minimum(qk / (1 - qk) for qk in q) : -Inf
    (isfinite(r) && rmin - 1e-12 <= r <= 1 + 1e-12) ||
        throw(ArgumentError("degree_correlated: r = $r gives negative edge-end probabilities; " *
                            "need −min_k q_k/(1 − q_k) = $(_net_fmt(rmin)) ≤ r ≤ 1"))
    e = [r * (i == j) * q[i] + (1 - r) * q[i] * q[j] for i in eachindex(q), j in eachindex(q)]
    all(>=(-1e-15), e) ||
        throw(ArgumentError("degree_correlated: r = $r gives negative edge-end probabilities " *
                            "(need −min_k q_k/(1 − q_k) ≤ r ≤ 1)"))
    full = zeros(length(p), length(p))
    full[support, support] .= max.(e, 0.0)
    return degree_correlated(p ./ sum(p), full)
end

"""
    degree_assortativity(net::DegreeCorrelatedNetwork)

Newman's degree assortativity r: the Pearson correlation of the degrees at the two ends of a
random edge, r = (Σ_kl k l e_kl − μ²)/σ² with μ and σ² the mean and variance of the edge-end
marginal q. `NaN` for a regular degree sequence (σ² = 0).
"""
function degree_assortativity(net::DegreeCorrelatedNetwork)
    k = Float64.(net.degrees)
    e = net.edge_ends
    q = vec(sum(e; dims = 2))
    μ = sum(k .* q)
    σ2 = sum(k .^ 2 .* q) - μ^2
    σ2 <= 1e-14 * max(1.0, μ^2) && return NaN
    return (sum(k[i] * k[j] * e[i, j] for i in eachindex(k), j in eachindex(k)) - μ^2) / σ2
end

mean_degree(net::DegreeCorrelatedNetwork) = sum(net.degrees .* net.probabilities)
excess_degree(net::DegreeCorrelatedNetwork) =
    sum(net.degrees .* (net.degrees .- 1) .* net.probabilities) / mean_degree(net)

"""
    MultitypeNetwork(net::DegreeCorrelatedNetwork)

The multitype form of a degree-correlated network: one type `Symbol("k", k)` per degree class
k, of size pₖ, whose nodes have exactly k stubs split over the classes with Q(l | k) =
e_kl/Σ_m e_km (`SplitDegrees(RegularDegree(k), …)`; degree-0 nodes get `IndependentDegrees()`).
"""
function MultitypeNetwork(net::DegreeCorrelatedNetwork)
    types = [Symbol("k", k) for k in net.degrees]
    degrees = MultivariateDegree[]
    for (i, k) in enumerate(net.degrees)
        row = net.edge_ends[i, :]
        if k == 0 || sum(row) == 0
            push!(degrees, IndependentDegrees())
        else
            Q = row ./ sum(row)
            push!(degrees, SplitDegrees(RegularDegree(k),
                                        Pair{Symbol,Float64}[types[j] => Q[j] for j in eachindex(Q) if Q[j] > 0]))
        end
    end
    return MultitypeNetwork(types, net.probabilities, degrees)
end

Base.:(==)(a::DegreeCorrelatedNetwork, b::DegreeCorrelatedNetwork) = _net_fields_equal(a, b)
Base.hash(a::DegreeCorrelatedNetwork, h::UInt) = _net_fields_hash(a, h)
canonical_text(io::IO, net::DegreeCorrelatedNetwork) =
    _netct_struct(io, "DegreeCorrelatedNetwork", :degrees => net.degrees,
                  :probabilities => net.probabilities, :edge_ends => net.edge_ends)

# =============================================================================================
# Canonical text of any descriptor
# =============================================================================================

"""
    canonical_text(net::NetworkDescriptor) -> String

Canonical text of a network descriptor (§E.4): one line with explicit field names and `%.17g`
numbers, nesting the canonical text of its parts, for example
`ConfigurationNetwork(degrees=PoissonDegree(mean=5))`. Symbolic parameters are refused. The
scenario hash (`scenario_hash`) embeds it.
"""
canonical_text(net::NetworkDescriptor) = sprint(canonical_text, net)
