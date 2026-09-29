# Owner: WP11 (DESIGN_NetworkEpiCore.md §B.6, §C.2, §C.3, §D.4, §E.2; work package in §G.2).
#
# Numeric threshold quantities of a T_EB ContactModel on a network descriptor: the per-edge
# transmissibility (absorption formula), the next-generation matrix and R₀ = ρ(K), the early
# growth rate (the leading eigenvalue of the edge-based field linearised at the disease-free
# state), the final size (bracketed / safeguarded-Newton solves with convergence checks), and
# `calibrate` (one scalar equation, solved by bracketing).
#
# Methods are added to the generics.jl stubs transmissibility, next_generation_matrix,
# basic_reproduction_number, early_growth_rate and final_size; `calibrate` and
# `next_generation_labels` are NetworkEpiCore-only verbs defined here.
#
# Verified issues addressed: E12 (multiplex R₀ is ρ(K), not the sum of layer R₀s), E14
# (branching/bypass transmissibility by the absorption formula), E18 (bracketed root finding and
# convergence checks, exactly 0 below threshold). The infector-side probability of a major
# outbreak (E15) is EdgeBasedModels' business; the final size here depends only on the marginal
# per-edge transmissibility, which is exact for any sojourn distribution.
#
# ---------------------------------------------------------------------------------------------
# One mathematical object behind every descriptor: an "edge-kind" branching process.
#
# - Node types a (one type for untyped descriptors; the strata of a MultitypeNetwork; the degree
#   classes of a DegreeCorrelatedNetwork) and typed states (a, X), X a non-susceptible species.
# - Edge kinds e with an infector-side node type src(e), a recipient-side node type dst(e) and
#   a layer: one kind for untyped descriptors, one per layer for a MultiplexNetwork, one per
#   ordered type pair (b → a) with E[k_{a→b}] > 0 for typed descriptors. The contacts acting on
#   a kind are those whose recipient is dst's susceptible class (and, for a multiplex, whose
#   layer is the kind's layer or :all).
# - M[e_in, e_out]: the expected number of e_out-edges (other than the arrival edge) of a node
#   reached along an e_in-edge: κ_ex on a configuration network; κ_ex,ℓ (same layer) or ⟨k_m⟩
#   (other layer) on a multiplex; X[c, b, a] = ∂_c∂_aψ_b(1)/∂_cψ_b(1) (`excess_contacts`) on
#   typed networks; κ on WellMixed(κ) and κ_ex + 1 = E[k²]/E[k] on MFSH (fleeting contacts).
# - V: the transition generator on the typed states (V_ii = total exit rate of i, V_ji = −rate
#   i → j); B_e = diag(Σ_{r on e with infector J} τ_r): transmission along a *persistent* edge
#   ends that edge's usefulness. Fleeting descriptors have no B (partners are always fresh).
#
# For an infector that enters state Y, the probability that it transmits across one given
# e-edge through contact r is T^e_r(Y) = τ_r [(V + B_e)⁻¹ e_Y]_{J_r}; the next-generation
# matrix over (arrival kind, entry state) is K_{(e_out,X) ← (e_in,Y)} = M[e_in,e_out]
# Σ_{r on e_out with product X} T^{e_out}_r(Y), and R₀ = ρ(K). The linearised edge-based field
# over (kind, state) is F − blockdiag(V + B_e), F_{(e_out,X),(e_in,J)} = M[e_in,e_out]
# Σ_{r on e_in: J → X} τ_r; its spectral abscissa is the early growth rate r.
#
# DynamicNetwork(base, NeighbourExchange(η)) (Miller–Slim–Volz DFD) adds "used" edges z: an
# infector's edges that have transmitted (or lead to its own infector) are refreshed at rate η,
# so y' = F_y − (V + B)y + ηz, z' = F_z + By − (V + η)z, with F_y = κ_ex Σ τ and F_z = Σ τ.
# ---------------------------------------------------------------------------------------------

export next_generation_labels, calibrate

# =============================================================================================
# Parameters
# =============================================================================================

const _AnalysisParams = Union{AbstractDict,NamedTuple}

_param_dict(p::AbstractDict) = p
_param_dict(p::NamedTuple) = Dict{Symbol,Any}(k => v for (k, v) in pairs(p))

_default_params() = Dict{Symbol,Float64}()

# =============================================================================================
# Descriptors: which analysis applies
# =============================================================================================

# :persistent — static edges (configuration, multiplex, multitype, degree-correlated);
# :fleeting   — partners are always fresh (WellMixed, MFSH);
# :exchange   — edges swap at rate η (DynamicNetwork with NeighbourExchange).
_analysis_mode(::ConfigurationNetwork) = :persistent
_analysis_mode(::MultiplexNetwork) = :persistent
_analysis_mode(::MultitypeNetwork) = :persistent
_analysis_mode(::DegreeCorrelatedNetwork) = :persistent
_analysis_mode(::WellMixed) = :fleeting
_analysis_mode(::MFSHNetwork) = :fleeting
_analysis_mode(::DynamicNetwork{<:NeighbourExchange}) = :exchange
_analysis_mode(::NetworkDescriptor) = nothing

function _unsupported_network(fname::Symbol, cm::ContactModel, net)
    label = _network_label(net)
    why = if net isa ClusteredNetwork
        "the clustered (Volz et al. 2011) threshold needs the triangle pair states of the " *
        "edge-based lift (a tree-of-triangles next-generation matrix, verified issue E04); it " *
        "lives in EdgeBasedModels: basic_reproduction_number(edge_based(model, net))"
    elseif net isa ExplicitGraph
        "a fixed graph has no ensemble next-generation matrix; use " *
        "ConfigurationNetwork(EmpiricalDegree(g)) for the annealed approximation, or the " *
        "individual-based models of NodeBasedModels on the graph itself"
    elseif net isa DynamicNetwork
        "the $(nameof(typeof(net.process))) process (a stretch descriptor) has no numeric " *
        "threshold analysis yet; NeighbourExchange is supported"
    else
        "the descriptor $(nameof(typeof(net))) has no numeric threshold analysis"
    end
    return ArgumentError("$(fname)(:$(cm.name), $(label)): $(why). Supported descriptors: " *
                         "WellMixed, ConfigurationNetwork, MultitypeNetwork, MultiplexNetwork, " *
                         "DegreeCorrelatedNetwork, MFSHNetwork and " *
                         "DynamicNetwork(base, NeighbourExchange(η)).")
end

function _numeric_descriptor(x, what, net)
    _net_isnumeric(x) || throw(ArgumentError(
        "the threshold analysis needs numeric network parameters; $(what) of " *
        "$(_network_label(net)) is $(x)"))
    return Float64(x)
end

# The network next-generation matrix is the linearisation of the edge-based field, so the
# model must be admissible for :edge_based on `net`. On fleeting descriptors (WellMixed, MFSH)
# partners are always fresh and the mass-action next-generation matrix also holds for arrows
# back into the susceptible class (SIS, SIRS: :resus), which are then tolerated.
function _require_analysis_admissible(cm::ContactModel, net, mode::Symbol)
    rep = admissibility(cm, net)
    tolerated = mode === :fleeting ? (:resus,) : ()
    blocking = [v for v in rep.violations
                if :edge_based in blocked_backends(v) && !(v.type in tolerated)]
    isempty(blocking) && return nothing
    accepted = [b for b in BACKENDS if rep.backends[b]]
    throw(AdmissibilityError(:edge_based, cm, net, blocking, accepted))
end

# =============================================================================================
# The edge-kind branching process
# =============================================================================================

struct _TypedContact
    name::Symbol
    τ::Float64
    infector::Int          # typed state index
    product::Int           # typed state index
end

struct _Kind
    label::NamedTuple      # (), (layer = ℓ,) or (type = a, from = b)
    src::Int               # node type of the infector end
    dst::Int               # node type of the recipient end
    layer::Symbol
    contacts::Vector{_TypedContact}
end

struct _Engine
    model::ContactModel
    net::NetworkDescriptor
    mode::Symbol
    types::Vector{Symbol}
    sizes::Vector{Float64}
    sus::Vector{Symbol}                     # the susceptible species of each node type
    states::Vector{Tuple{Int,Symbol}}       # typed non-susceptible states (type, species)
    index::Dict{Tuple{Int,Symbol},Int}
    kinds::Vector{_Kind}
    M::Matrix{Float64}                      # M[e_in, e_out]
    out::Vector{Vector{Tuple{Int,Float64}}} # per state: (destination state or 0, rate)
    V::Matrix{Float64}                      # transition generator on the typed states
    η::Float64                              # edge-exchange rate (:exchange only)
    laws::Any                               # what the final size needs to evaluate the PGFs
end

# ---- node types and typed states ------------------------------------------------------------

# The stratum of every species labelled with one (`SpeciesLabel(base; stratum = a)`). A
# non-susceptible species without a stratum is *shared* by the node types (heterogeneous
# susceptibility: S_lo + I → I, S_hi + I → I with one I): it has a typed state (a, X) on every node
# type a, as NetworkOutbreaks and the EdgeBasedModels heterogeneous lift treat it. This is the
# implicit stratification X ↦ X_a, s_a + J_b → X_a + J_b, with transitions within each type,
# which is exact because node types are fixed. A reaction may not move a node from one stratum
# into another, nor a node of every type into one stratum.
function _species_strata(cm::ContactModel)
    st = Dict{Symbol,Symbol}(x => l.stratum for (x, l) in cm.labels if l.stratum !== :all)
    function check(from, to, why)
        b = get(st, to, :all)
        a = get(st, from, :all)
        (b === :all || a === b) && return nothing
        throw(ArgumentError(a === :all ?
            "$(why) moves nodes of every node type from $(from), which has no stratum, into " *
            "$(to), which belongs to the stratum $(b); strata are fixed node attributes, so " *
            "label $(from) with a stratum or remove the stratum of $(to)" :
            "$(why) moves a node of stratum $(a) into $(to), which belongs to the stratum " *
            "$(b); strata are fixed node attributes"))
    end
    for c in cm.contacts
        check(c.recipient, c.product, "contact `$(c.name)`")
    end
    for t in cm.transitions
        t.to === nothing || check(t.from, t.to, "transition `$(t.name)`")
    end
    return st
end

_mentioned(cm::ContactModel, x::Symbol) =
    any(r -> x in _species_of(r), Iterators.flatten((cm.contacts, cm.transitions)))

function _node_types(cm::ContactModel, net::MultitypeNetwork)
    types = collect(Symbol, net.types)
    tindex = Dict(a => i for (i, a) in enumerate(types))
    st = _species_strata(cm)
    sus = Symbol[only([s for s in cm.susceptible if get(st, s, :all) === a]) for a in types]
    states = Tuple{Int,Symbol}[]
    for x in cm.species
        x in cm.susceptible && continue
        a = get(st, x, nothing)
        if a === nothing
            # shared by the node types: a state on every type
            _mentioned(cm, x) && append!(states, ((i, x) for i in eachindex(types)))
            continue
        end
        haskey(tindex, a) || throw(ArgumentError(
            "model :$(cm.name): the species $(x) belongs to the stratum $(a), which is not a " *
            "node type of the MultitypeNetwork (types $(_list(types)))"))
        push!(states, (tindex[a], x))
    end
    return types, collect(Float64, net.sizes), sus, states, net
end

function _node_types(cm::ContactModel, net::DegreeCorrelatedNetwork)
    mt = MultitypeNetwork(net)
    s = only(cm.susceptible)
    nonsus = [x for x in cm.species if !(x in cm.susceptible)]
    states = Tuple{Int,Symbol}[(a, x) for a in eachindex(mt.types) for x in nonsus]
    return collect(Symbol, mt.types), collect(Float64, mt.sizes), fill(s, length(mt.types)),
           states, mt
end

function _node_types(cm::ContactModel, net::NetworkDescriptor)
    nonsus = [x for x in cm.species if !(x in cm.susceptible)]
    return [:all], [1.0], [only(cm.susceptible)], Tuple{Int,Symbol}[(1, x) for x in nonsus], net
end

# ---- edge kinds ----------------------------------------------------------------------------

function _typed_contacts(cm, τ, index, src, dst, sus_dst, accept)
    out = _TypedContact[]
    for (k, c) in enumerate(cm.contacts)
        (c.recipient === sus_dst && accept(c)) || continue
        J = get(index, (src, c.infector), 0)
        J == 0 && continue                          # the infector lives on another node type
        X = get(index, (dst, c.product), 0)
        X == 0 && throw(ArgumentError(
            "contact `$(c.name)`: its product $(c.product) is not a state of the recipient's " *
            "node type $(dst)"))
        push!(out, _TypedContact(c.name, τ[k], J, X))
    end
    return out
end

_all_contacts(c) = true

function _kinds(cm, net::MultiplexNetwork, sus, index, τ)
    kinds = _Kind[]
    for (ℓ, layer) in net.layers
        k = _numeric_descriptor(mean_degree(layer), "the mean degree of layer :$(ℓ)", net)
        k > 0 || continue
        cs = _typed_contacts(cm, τ, index, 1, 1, sus[1], c -> c.layer === :all || c.layer === ℓ)
        push!(kinds, _Kind((layer = ℓ,), 1, 1, ℓ, cs))
    end
    return kinds
end

function _kinds(cm, net::Union{MultitypeNetwork,DegreeCorrelatedNetwork}, sus, index, τ,
                mt::MultitypeNetwork)
    kinds = _Kind[]
    types = mt.types
    for a in eachindex(types), b in eachindex(types)
        mt.structural_zero[a, b] && continue        # a-nodes have no edges to b-nodes
        cs = _typed_contacts(cm, τ, index, b, a, sus[a], _all_contacts)
        push!(kinds, _Kind((type = types[a], from = types[b]), b, a, :all, cs))
    end
    return kinds
end

function _kinds(cm, net::NetworkDescriptor, sus, index, τ)
    cs = _typed_contacts(cm, τ, index, 1, 1, sus[1], _all_contacts)
    return [_Kind(NamedTuple(), 1, 1, :all, cs)]
end

# ---- the offspring matrix M -----------------------------------------------------------------

function _positive_mean(d, net, what)
    m = _numeric_descriptor(mean_degree(d), what, net)
    return m > 0 ? m : 0.0
end

_excess_or_zero(c::ConfigurationNetwork, net) =
    _positive_mean(c, net, "the mean degree") > 0 ? Float64(excess_degree(c)) : 0.0
_offspring(net::ConfigurationNetwork, kinds, laws) = fill(_excess_or_zero(net, net), 1, 1)
_offspring(net::DynamicNetwork, kinds, laws) = fill(_excess_or_zero(net.base, net), 1, 1)
_offspring(net::WellMixed, kinds, laws) = fill(_numeric_descriptor(net.κ, "κ", net), 1, 1)
_offspring(net::MFSHNetwork, kinds, laws) =
    fill(_positive_mean(net.degrees, net, "the mean degree") > 0 ?
         Float64(excess_degree(net.degrees)) + 1.0 : 0.0, 1, 1)

function _offspring(net::MultiplexNetwork, kinds, laws)
    n = length(kinds)
    M = zeros(n, n)
    for (i, e) in enumerate(kinds), (j, f) in enumerate(kinds)
        layer = net[f.layer]
        M[i, j] = e.layer === f.layer ? Float64(excess_degree(layer)) : Float64(mean_degree(layer))
    end
    return M
end

function _offspring(::Union{MultitypeNetwork,DegreeCorrelatedNetwork}, kinds, mt::MultitypeNetwork)
    X = excess_contacts(mt)
    n = length(kinds)
    M = zeros(n, n)
    for (i, e) in enumerate(kinds), (j, f) in enumerate(kinds)
        e.dst == f.src || continue
        M[i, j] = X[e.src, e.dst, f.dst]
    end
    return M
end

# ---- assembling the engine ---------------------------------------------------------------------

# `τ = nothing`: structure only (rates set to 0), for the labels.
function _engine(cm::ContactModel, net::NetworkDescriptor, mode::Symbol,
                 τ::Union{Nothing,AbstractVector{<:Real}})
    numeric = τ !== nothing
    τv = numeric ? Float64.(τ) : zeros(length(cm.contacts))
    types, sizes, sus, states, laws = _node_types(cm, net)
    index = Dict{Tuple{Int,Symbol},Int}(s => i for (i, s) in enumerate(states))
    kinds = laws isa MultitypeNetwork ? _kinds(cm, net, sus, index, τv, laws) :
            _kinds(cm, net, sus, index, τv)
    M = _offspring(net, kinds, laws)
    n = length(states)
    out = [Tuple{Int,Float64}[] for _ in 1:n]
    V = zeros(n, n)
    for (i, (a, x)) in enumerate(states), t in cm.transitions
        t.from === x || continue
        rate = numeric ? Float64(t.rate) : 0.0
        dest = t.to === nothing ? 0 : get(index, (a, t.to), 0)
        push!(out[i], (dest, rate))
        V[i, i] += rate
        dest == 0 || (V[dest, i] -= rate)
    end
    η = mode === :exchange ? _numeric_descriptor(net.process.η, "η", net) : 0.0
    return _Engine(cm, net, mode, types, sizes, sus, states, index, kinds, M, out, V, η, laws)
end

function _prepare(cm::ContactModel, net::NetworkDescriptor, p, fname::Symbol)
    mode = _analysis_mode(net)
    mode === nothing && throw(_unsupported_network(fname, cm, net))
    _require_analysis_admissible(cm, net, mode)
    ci = instantiate(cm, _param_dict(p))
    τ = Float64[Float64(x) for x in per_contact_rates(ci, net)]
    all(x -> isfinite(x) && x >= 0, τ) || throw(ArgumentError(
        "$(fname)(:$(cm.name)): the per-contact rates $(τ) are not finite and ≥ 0 (a rate " *
        "convention divided by a zero mean degree?)"))
    return _engine(ci, net, mode, τ)
end

function _prepare_structure(cm::ContactModel, net::NetworkDescriptor, fname::Symbol)
    mode = _analysis_mode(net)
    mode === nothing && throw(_unsupported_network(fname, cm, net))
    _require_analysis_admissible(cm, net, mode)
    return _engine(cm, net, mode, nothing)
end

# ---- the infectious chain and the transmission operator ------------------------------------------

# States from which one of `targets` can be reached by positive-rate transitions.
function _ancestors(eng::_Engine, targets)
    n = length(eng.states)
    reach = falses(n)
    for t in targets
        reach[t] = true
    end
    changed = true
    while changed
        changed = false
        for i in 1:n
            reach[i] && continue
            if any(((d, r),) -> d != 0 && r > 0 && reach[d], eng.out[i])
                reach[i] = true
                changed = true
            end
        end
    end
    return findall(reach)
end

# The infectious chain of kind e: states from which an infector of a positive-rate contact on e
# can be reached. Only these can ever transmit along an e-edge.
_chain(eng::_Engine, e::Int) =
    _ancestors(eng, unique(c.infector for c in eng.kinds[e].contacts if c.τ > 0))

# Every state of `chain` must eventually leave it (through a transition to a state outside the
# chain, a susceptible class or ∅); otherwise the infectious period is infinite.
function _check_finite_period(eng::_Engine, chain, fname)
    inchain = falses(length(eng.states))
    inchain[chain] .= true
    good = falses(length(eng.states))
    for i in chain
        good[i] = any(((d, r),) -> r > 0 && (d == 0 || !inchain[d]), eng.out[i])
    end
    changed = true
    while changed
        changed = false
        for i in chain
            good[i] && continue
            if any(((d, r),) -> r > 0 && d != 0 && inchain[d] && good[d], eng.out[i])
                good[i] = true
                changed = true
            end
        end
    end
    bad = [eng.states[i][2] for i in chain if !good[i]]
    isempty(bad) && return nothing
    what = eng.mode === :fleeting ?
           "partners are always fresh on $(_network_label(eng.net))" :
           "edges are refreshed at rate η on $(_network_label(eng.net))"
    throw(ArgumentError(
        "$(fname)(:$(eng.model.name)): the species $(_list(unique(bad))) never leave the " *
        "infectious chain, so the infectious period is infinite; since $(what), R₀ is infinite"))
end

# The chain of kind e, its positions, and W = A⁻¹ with A = V + B_e (persistent), V (fleeting)
# or V + B_e + η (per-partnership, `partnership = true` on an exchange network).
function _operator(eng::_Engine, e::Int, fname::Symbol; partnership::Bool = false)
    chain = _chain(eng, e)
    pos = Dict{Int,Int}(s => k for (k, s) in enumerate(chain))
    isempty(chain) && return chain, pos, zeros(0, 0)
    A = eng.V[chain, chain]
    if eng.mode === :fleeting
        _check_finite_period(eng, chain, fname)
    else
        for c in eng.kinds[e].contacts
            c.τ > 0 && (A[pos[c.infector], pos[c.infector]] += c.τ)
        end
        partnership && (A += eng.η * I)
    end
    return chain, pos, A \ Matrix{Float64}(I, length(chain), length(chain))
end

# Per-contact transmissibilities T^e_r(Y) for one starting state Y (a typed state index).
function _contact_transmissibilities(eng::_Engine, e::Int, op, Y::Int)
    _, pos, W = op
    k = get(pos, Y, 0)
    return [(c, (k == 0 || c.τ == 0) ? 0.0 : c.τ * W[pos[c.infector], k])
            for c in eng.kinds[e].contacts]
end

_total_transmissibility(eng::_Engine, e::Int, op, Y::Int) =
    sum(last, _contact_transmissibilities(eng, e, op, Y); init = 0.0)

# =============================================================================================
# The next-generation matrix
# =============================================================================================

# NGM rows/columns: (kind, entry state) for each kind and each product of its contacts, in
# order of first appearance.
function _ngm_rows(eng::_Engine)
    rows = Tuple{Int,Int}[]
    labels = NamedTuple[]
    for (e, k) in enumerate(eng.kinds)
        seen = Int[]
        for c in k.contacts
            c.product in seen && continue
            push!(seen, c.product)
            push!(rows, (e, c.product))
            push!(labels, merge(k.label, (entry = eng.states[c.product][2],)))
        end
    end
    return rows, labels
end

function _ngm(eng::_Engine, fname::Symbol)
    eng.mode === :exchange && return _ngm_exchange(eng, fname)
    rows, _ = _ngm_rows(eng)
    ops = [_operator(eng, e, fname) for e in eachindex(eng.kinds)]
    n = length(rows)
    K = zeros(n, n)
    for (col, (ein, Y)) in enumerate(rows), (row, (eout, X)) in enumerate(rows)
        m = eng.M[ein, eout]
        m == 0 && continue
        s = 0.0
        for (c, T) in _contact_transmissibilities(eng, eout, ops[eout], Y)
            c.product == X && (s += T)
        end
        K[row, col] = m * s
    end
    return K
end

# The DFD operator on (available y, used z) edges of the chain: the positive form
# [[V + B, −η], [−B, V + η]] of the linear dynamics without new infections.
function _exchange_operator(eng::_Engine, fname::Symbol)
    chain = _chain(eng, 1)
    pos = Dict{Int,Int}(s => k for (k, s) in enumerate(chain))
    n = length(chain)
    n == 0 && return chain, pos, zeros(0, 0)
    _check_finite_period(eng, chain, fname)
    Vc = eng.V[chain, chain]
    Bm = zeros(n, n)
    for c in eng.kinds[1].contacts
        c.τ > 0 && (Bm[pos[c.infector], pos[c.infector]] += c.τ)
    end
    η = eng.η
    A = [Vc+Bm -η*I; -Bm Vc+η*I]
    return chain, pos, A
end

function _ngm_exchange(eng::_Engine, fname::Symbol)
    rows, _ = _ngm_rows(eng)
    chain, pos, A = _exchange_operator(eng, fname)
    n = length(chain)
    κex = eng.M[1, 1]
    K = zeros(length(rows), length(rows))
    isempty(chain) && return K
    for (col, (_, Y)) in enumerate(rows)
        k = get(pos, Y, 0)
        k == 0 && continue
        u = zeros(2n)
        u[k] = κex          # a newly infected node has κ_ex fresh edges ...
        u[n + k] = 1.0      # ... and one used edge (to its infector)
        w = A \ u           # expected edge-time with the infector side in each state
        for (row, (_, X)) in enumerate(rows), c in eng.kinds[1].contacts
            (c.product == X && c.τ > 0) && (K[row, col] += c.τ * w[pos[c.infector]])
        end
    end
    return K
end

_spectral_radius(K::AbstractMatrix) = isempty(K) ? 0.0 : Float64(maximum(abs, eigvals(K)))

"""
    next_generation_matrix(cm::ContactModel, net::NetworkDescriptor, p = Dict()) -> Matrix{Float64}
    next_generation_matrix(model, net, p = Dict())      # any model that `contact_model` accepts

The numeric next-generation matrix K of a T_EB model on a network descriptor, with parameter
values `p` (by name; model defaults fill the gaps) and contact rates converted to per-contact
τ by the model's rate convention ([`per_contact_rates`](@ref)). The rows and columns are the
types of a newly infected node, listed by [`next_generation_labels`](@ref): its entry state X,
and the kind of edge it was infected along.

With T^e_r(Y) = τ_r [(V + B_e)⁻¹ e_Y]_{J_r} the per-edge transmissibility of contact r from an
infector that entered Y (see [`transmissibility`](@ref)):

- `ConfigurationNetwork(d)`: K_{X←Y} = κ_ex Σ_{r: entry X} T_r(Y), κ_ex = ψ''(1)/ψ'(1).
- `WellMixed(κ)` (fleeting contacts, no edge exhaustion): K_{X←Y} = κ Σ_{r: entry X}
  τ_r [V⁻¹ e_Y]_{J_r}, the mass-action next-generation matrix. SIS and SIRS are accepted here.
- `MFSHNetwork(d)`: as WellMixed with κ replaced by E[k²]/E[k] = κ_ex + 1.
- `MultiplexNetwork`: (layer, entry) blocks, K_{(ℓ,X)←(m,Y)} = M_{mℓ} Σ_{r on ℓ, entry X}
  T^ℓ_r(Y), with M_{ℓℓ} = κ_ex,ℓ and M_{mℓ} = ⟨k_ℓ⟩ for m ≠ ℓ (a contact on `:all` acts on every
  layer). R₀ = ρ(K), **not** the sum of the layer R₀s (verified issue E12).
- `MultitypeNetwork` (a stratified model: one susceptible class per type): blocks over the edge
  kind (from type b to type a) and the entry state, K_{((b→a),X)←((c→b),Y)} = X[c,b,a]
  Σ_{r: S_a ← J_b, entry X} T^{(b→a)}_r(Y) with X[c,b,a] = ∂_c∂_aψ_b(1)/∂_cψ_b(1)
  ([`excess_contacts`](@ref)). When X[c,b,a] does not depend on c (Poisson or `SplitDegrees`
  blocks) this reduces to (type, entry) blocks, e.g. R₀ = T ρ(M) for a Poisson SBM with mean
  contacts M. Structural zeros create no blocks.
- `DegreeCorrelatedNetwork` (an unstratified model): the multitype form over degree classes.
- `DynamicNetwork(base, NeighbourExchange(η))` (Miller–Slim–Volz DFD): K_{X←Y} = Σ_{r: entry X}
  τ_r ∫ y_{J_r}, where y (available edges) and z (used edges) follow y' = −(V + B)y + ηz,
  z' = By − (V + η)z from y = κ_ex e_Y, z = e_Y. For SIR,
  R₀ = τ[(γ + η)κ_ex + η]/(γ(γ + η + τ)), from τκ_ex/(τ + γ) at η = 0 to τ(κ_ex + 1)/γ as η → ∞.

V is the transition generator on the non-susceptible states and B_e the rate at which
transmission along the edge ends its usefulness. Exits from the susceptible class
(vaccination) are evaluated at the initial state ξ = 1. The model must be admissible for
`:edge_based` on `net` (an [`AdmissibilityError`](@ref) otherwise; on fleeting descriptors arrows
back into the susceptible class are tolerated). `ClusteredNetwork` (EdgeBasedModels),
`ExplicitGraph` and dormant contacts are refused with an `ArgumentError`.
"""
function next_generation_matrix(cm::ContactModel, net::NetworkDescriptor,
                                p::_AnalysisParams = _default_params())
    eng = _prepare(cm, net, p, :next_generation_matrix)
    return _ngm(eng, :next_generation_matrix)
end
next_generation_matrix(model, net::NetworkDescriptor, p::_AnalysisParams = _default_params()) =
    next_generation_matrix(contact_model(model), net, p)

"""
    next_generation_labels(cm, net::NetworkDescriptor) -> Vector{NamedTuple}

The labels of the rows and columns of [`next_generation_matrix`](@ref)`(cm, net, p)`, in order:
the type of a newly infected node. `(entry = X,)` on untyped descriptors, `(layer = ℓ, entry = X)`
on a `MultiplexNetwork` (infected along a layer-ℓ edge into X), and `(type = a, from = b,
entry = X)` on typed descriptors (a type-a node infected by a type-b neighbour into X). They do
not depend on the parameter values.
"""
function next_generation_labels(cm::ContactModel, net::NetworkDescriptor)
    eng = _prepare_structure(cm, net, :next_generation_labels)
    return _ngm_rows(eng)[2]
end
next_generation_labels(model, net::NetworkDescriptor) =
    next_generation_labels(contact_model(model), net)

"""
    basic_reproduction_number(cm::ContactModel, net::NetworkDescriptor, p = Dict()) -> Float64
    basic_reproduction_number(model, net, p = Dict())   # any model that `contact_model` accepts

R₀ = ρ(K), the spectral radius of the numeric [`next_generation_matrix`](@ref) (see there for
each descriptor). For a single entry state on a configuration network R₀ = T κ_ex with T the
per-edge [`transmissibility`](@ref): R₀ = 2 for SIR with τ = 1/6, γ = 1/4 on any network with
excess degree 5, and R₀ = 1.70 for the canonical SEAIR (T = 0.34). On a multiplex R₀ is ρ(K),
never the sum of the layer R₀s: two 3-regular layers at T = 0.22 give 1.10, not 0.88 (E12).
"""
basic_reproduction_number(cm::ContactModel, net::NetworkDescriptor,
                          p::_AnalysisParams = _default_params()) =
    _spectral_radius(next_generation_matrix(cm, net, p))
basic_reproduction_number(model, net::NetworkDescriptor, p::_AnalysisParams = _default_params()) =
    basic_reproduction_number(contact_model(model), net, p)

# =============================================================================================
# Transmissibility
# =============================================================================================

function _pick_kind(eng::_Engine, from::Int, layer, recipient, fname)
    kinds = eng.kinds
    cand = collect(eachindex(kinds))
    if eng.net isa MultiplexNetwork
        if layer === nothing
            length(cand) == 1 || throw(ArgumentError(
                "$(fname)(:$(eng.model.name)): the per-edge transmissibility depends on the " *
                "layer; pass layer = one of $(_list(kinds[e].layer for e in cand))"))
        else
            cand = [e for e in cand if kinds[e].layer === layer]
            isempty(cand) && throw(ArgumentError(
                "$(fname): :$(layer) is not a layer (with edges) of $(_network_label(eng.net)); " *
                "layers: $(_list(k.layer for k in kinds))"))
        end
    elseif layer !== nothing
        throw(ArgumentError("$(fname): `layer` is only meaningful on a MultiplexNetwork"))
    end
    if eng.laws isa MultitypeNetwork
        b = eng.states[from][1]
        cand = [e for e in cand if kinds[e].src == b]
        if recipient !== nothing
            cand = [e for e in cand if eng.types[kinds[e].dst] === recipient]
            isempty(cand) && throw(ArgumentError(
                "$(fname): nodes of type $(eng.types[b]) have no edges to type $(recipient) " *
                "(or $(recipient) is not a node type; types: $(_list(eng.types)))"))
        elseif eng.net isa MultitypeNetwork && length(cand) > 1
            throw(ArgumentError(
                "$(fname)(:$(eng.model.name)): on a MultitypeNetwork the per-edge " *
                "transmissibility depends on the recipient's type; pass recipient = one of " *
                "$(_list(eng.types[kinds[e].dst] for e in cand))"))
        end
    elseif recipient !== nothing
        throw(ArgumentError("$(fname): `recipient` is only meaningful on a typed network"))
    end
    isempty(cand) && throw(ArgumentError("$(fname): no edge of $(_network_label(eng.net)) can " *
                                         "carry a transmission from $(eng.states[from][2])"))
    return first(cand)
end

function _from_state(eng::_Engine, from, fname)
    cm = eng.model
    if from === nothing
        entries = unique(eng.states[c.product][2] for k in eng.kinds for c in k.contacts)
        length(entries) == 1 || throw(ArgumentError(
            "$(fname)(:$(cm.name)): the model has $(isempty(entries) ? "no" : "several") entry " *
            "states ($(_list(entries))); pass from = the state the infector enters"))
        from = only(entries)
    end
    from isa Symbol || throw(ArgumentError("$(fname): `from` must be a species name"))
    from in cm.susceptible && throw(ArgumentError(
        "$(fname): $(from) is a susceptible class; `from` is the state an infector enters"))
    hits = [i for (i, (_, x)) in enumerate(eng.states) if x === from]
    isempty(hits) && throw(ArgumentError(
        "$(fname): $(from) is not a species of the model :$(cm.name) (species: " *
        "$(_list(cm.species)))"))
    # an unstratified model on a degree-correlated network has the state in every degree class;
    # the transmissibility is the same in each, so take a class that has edges
    for i in hits
        any(k -> k.src == eng.states[i][1], eng.kinds) && return i
    end
    return first(hits)
end

"""
    transmissibility(cm::ContactModel, net::NetworkDescriptor, p = Dict();
                     from = nothing, layer = nothing, recipient = nothing, by_contact = false)
    transmissibility(model, net, p = Dict(); kw...)   # any model that `contact_model` accepts

The per-edge transmissibility: the probability that a node which has just entered the state
`from` (default: the unique entry state of the contacts) eventually transmits across one given
edge to a susceptible neighbour, summed over the contacts that act on that edge. It is the
absorption probability

    T_r(Y) = τ_r [(V + B)⁻¹ e_Y]_{J_r},   T(Y) = Σ_r T_r(Y),

where V is the transition generator on the non-susceptible states and B = diag(Σ_{r: J_r = J} τ_r)
the rate at which transmission along the edge ends. This is exact for branching, bypass and
cycles (verified issue E14), where the old product formula was not. For SIR, T = τ/(τ + γ); for
n Erlang stages ([`erlang_stages`](@ref)) T_n = 1 − (nγ/(τ + nγ))ⁿ; for the canonical SEAIR
T = p τ_I/(τ_I + γ) + (1 − p) τ_A/(τ_A + γ) = 0.34; for E → I at pσ, E → R at (1 − p)σ,
T = p τ/(τ + γ).

- `layer`: on a `MultiplexNetwork` the contacts acting on the edge depend on its layer (a
  contact on `:all` acts on every layer); required when the network has several layers.
- `recipient`: on a `MultitypeNetwork` the node type of the susceptible neighbour (required when
  the infector's type has edges to several types); `from` is then a stratum's species.
- `by_contact = true` returns a `Dict{Symbol,Float64}` contact name ⇒ T_r(from).
- On `DynamicNetwork(base, NeighbourExchange(η))` it is the per-partnership transmissibility
  τ_r [(V + B + η)⁻¹ e_Y]_{J_r} (the partnership ends at rate η).
- `WellMixed` and `MFSHNetwork` have fleeting contacts and no persistent edges, so a per-edge
  transmissibility is not defined there (an `ArgumentError`); use
  [`next_generation_matrix`](@ref).
"""
function transmissibility(cm::ContactModel, net::NetworkDescriptor,
                          p::_AnalysisParams = _default_params(); from = nothing,
                          layer = nothing, recipient = nothing, by_contact::Bool = false)
    fname = :transmissibility
    eng = _prepare(cm, net, p, fname)
    eng.mode === :fleeting && throw(ArgumentError(
        "transmissibility(:$(cm.name), $(_network_label(net))): contacts are fleeting (partners " *
        "are always fresh), so there is no persistent edge and no per-edge transmissibility; " *
        "use next_generation_matrix or basic_reproduction_number"))
    Y = _from_state(eng, from, fname)
    e = _pick_kind(eng, Y, layer, recipient, fname)
    op = _operator(eng, e, fname; partnership = eng.mode === :exchange)
    Ts = _contact_transmissibilities(eng, e, op, Y)
    by_contact && return Dict{Symbol,Float64}(c.name => T for (c, T) in Ts)
    return sum(last, Ts; init = 0.0)
end
transmissibility(model, net::NetworkDescriptor, p::_AnalysisParams = _default_params(); kw...) =
    transmissibility(contact_model(model), net, p; kw...)

# =============================================================================================
# Early growth rate
# =============================================================================================

# The Jacobian J of the linearised field, and the indices of its entry coordinates (the states
# that new infections enter). Returns (J, entries).
function _growth_jacobian(eng::_Engine, fname)
    eng.mode === :exchange && return _growth_jacobian_exchange(eng, fname)
    chains = [_chain(eng, e) for e in eachindex(eng.kinds)]
    vars = Tuple{Int,Int}[(e, i) for e in eachindex(eng.kinds) for i in chains[e]]
    isempty(vars) && throw(ArgumentError(
        "$(fname)(:$(eng.model.name)): no contact has a positive rate on " *
        "$(_network_label(eng.net)), so there is no infectious subsystem to grow"))
    at = Dict(v => k for (k, v) in enumerate(vars))
    n = length(vars)
    J = zeros(n, n)
    for (col, (ein, j)) in enumerate(vars)
        # transitions and (persistent) exhaustion on the same kind
        for (row, (e, i)) in enumerate(vars)
            e == ein || continue
            J[row, col] -= eng.V[i, j]
        end
        if eng.mode === :persistent
            for c in eng.kinds[ein].contacts
                c.infector == j && (J[col, col] -= c.τ)
            end
        end
        # new infections along ein-edges feed every outgoing kind
        for c in eng.kinds[ein].contacts
            (c.infector == j && c.τ > 0) || continue
            for eout in eachindex(eng.kinds)
                m = eng.M[ein, eout]
                row = get(at, (eout, c.product), 0)
                (m == 0 || row == 0) && continue
                J[row, col] += m * c.τ
            end
        end
    end
    entries = unique!(Int[at[(eout, c.product)] for e in eachindex(eng.kinds)
                          for c in eng.kinds[e].contacts if c.τ > 0
                          for eout in eachindex(eng.kinds)
                          if eng.M[e, eout] != 0 && haskey(at, (eout, c.product))])
    return J, entries
end

function _growth_jacobian_exchange(eng::_Engine, fname)
    chain = _chain(eng, 1)
    n = length(chain)
    n == 0 && throw(ArgumentError(
        "$(fname)(:$(eng.model.name)): no contact has a positive rate, so there is no " *
        "infectious subsystem to grow"))
    pos = Dict(s => k for (k, s) in enumerate(chain))
    Vc = eng.V[chain, chain]
    Bm = zeros(n, n)
    Fy = zeros(n, n)
    Fz = zeros(n, n)
    κex = eng.M[1, 1]
    for c in eng.kinds[1].contacts
        c.τ > 0 || continue
        j = pos[c.infector]
        Bm[j, j] += c.τ
        i = get(pos, c.product, 0)
        i == 0 && continue
        Fy[i, j] += κex * c.τ
        Fz[i, j] += c.τ
    end
    η = eng.η
    entries = unique!(Int[pos[c.product] for c in eng.kinds[1].contacts
                          if c.τ > 0 && haskey(pos, c.product)])
    return [Fy-Vc-Bm η*I; Fz+Bm -Vc-η*I], entries
end

# The coordinates reachable from the entry coordinates through the nonzero pattern of J (column
# → row): the subsystem that an infection starts. It is forward-invariant, so J is block
# triangular and its other eigenvalues belong to states that no infection reaches (an infector
# that nothing produces), which do not govern the growth of an epidemic.
function _reachable(J::AbstractMatrix, entries::Vector{Int})
    seen = falses(size(J, 1))
    stack = copy(entries)
    seen[entries] .= true
    while !isempty(stack)
        col = pop!(stack)
        for row in axes(J, 1)
            (J[row, col] != 0 && !seen[row]) || continue
            seen[row] = true
            push!(stack, row)
        end
    end
    return findall(seen)
end

"""
    early_growth_rate(cm::ContactModel, net::NetworkDescriptor, p = Dict()) -> Float64
    early_growth_rate(model, net, p = Dict())   # any model that `contact_model` accepts

The initial exponential growth rate r: the leading eigenvalue (spectral abscissa) of the
edge-based field linearised at the disease-free state, restricted to the infectious chain (the
states from which an infector can be reached). On a configuration network the linearisation in
the edge variables φ is F − (V + B), F_{X,J} = κ_ex Σ_{r: J → X} τ_r, so for SIR
r = τ(κ_ex − 1) − γ (5/12 for τ = 1/6, γ = 1/4, κ_ex = 5) and for SEIR r is the dominant root of
(r + σ)(r + τ + γ) = στκ_ex. On `WellMixed(κ)` it is the mass-action F − V with F = κ Σ τ
(κτ − γ for SIR); on `MFSHNetwork` κ becomes κ_ex + 1; multiplex and typed networks use the
(kind, state) blocks of [`next_generation_matrix`](@ref); `DynamicNetwork(base,
NeighbourExchange(η))` adds the used-edge variables (for SIR the Jacobian
[[τκ_ex − τ − γ, η], [2τ, −(γ + η)]] in available and used edges, which is the
Miller–Slim–Volz DFD field linearised). r > 0 exactly when R₀ > 1.

The linearisation is restricted to the states that an infection reaches (from the entry states,
through transitions and further infections): an infectious state that nothing produces does not
govern the growth, so below threshold r is the decay rate of the epidemic, not the exit rate of
such a state.
"""
function early_growth_rate(cm::ContactModel, net::NetworkDescriptor,
                           p::_AnalysisParams = _default_params())
    eng = _prepare(cm, net, p, :early_growth_rate)
    J, entries = _growth_jacobian(eng, :early_growth_rate)
    live = _reachable(J, entries)
    isempty(live) && throw(ArgumentError(
        "early_growth_rate(:$(cm.name)): no contact with a positive rate produces a state from " *
        "which a transmission can follow, so there is no infectious subsystem to grow"))
    return Float64(maximum(real, eigvals(J[live, live])))
end
early_growth_rate(model, net::NetworkDescriptor, p::_AnalysisParams = _default_params()) =
    early_growth_rate(contact_model(model), net, p)

# =============================================================================================
# Root finding (verified issue E18: bracketing, convergence checks, no silent answers)
# =============================================================================================

# Brent's method on [a, b] with f(a)·f(b) ≤ 0 (Brent 1973; the zbrent form). Throws if it has
# not converged in `maxiter` steps.
function _brent(f, a::Float64, b::Float64, fa::Float64, fb::Float64; tol::Float64,
                maxiter::Int = 300, what::AbstractString = "root")
    fa == 0 && return a
    fb == 0 && return b
    (isnan(fa) || isnan(fb) || sign(fa) == sign(fb)) && throw(ArgumentError(
        "$(what): [$a, $b] does not bracket a root (f = $fa, $fb)"))
    c, fc = b, fb
    d = e = b - a
    for _ in 1:maxiter
        if sign(fb) == sign(fc)
            c, fc = a, fa
            d = e = b - a
        end
        if abs(fc) < abs(fb)
            a, b, c = b, c, b
            fa, fb, fc = fb, fc, fb
        end
        tol1 = 2 * eps(Float64) * abs(b) + tol / 2
        xm = (c - b) / 2
        (abs(xm) <= tol1 || fb == 0) && return b
        if abs(e) >= tol1 && abs(fa) > abs(fb)
            s = fb / fa
            if a == c
                pp = 2xm * s
                qq = 1 - s
            else
                qq = fa / fc
                r = fb / fc
                pp = s * (2xm * qq * (qq - r) - (b - a) * (r - 1))
                qq = (qq - 1) * (r - 1) * (s - 1)
            end
            pp > 0 && (qq = -qq)
            pp = abs(pp)
            if 2pp < min(3xm * qq - abs(tol1 * qq), abs(e * qq))
                e = d
                d = pp / qq
            else
                d = xm
                e = d
            end
        else
            d = xm
            e = d
        end
        a, fa = b, fb
        b += abs(d) > tol1 ? d : copysign(tol1, xm)
        fb = f(b)
        isnan(fb) && throw(ArgumentError("$(what): the function is NaN at $b"))
    end
    throw(ErrorException("$(what): no convergence in $(maxiter) Brent steps"))
end

# =============================================================================================
# Final size
# =============================================================================================

# Seed fractions per typed state (a fraction of the nodes of that state's type) and the unseeded
# fraction q_a of each type. Seeds are population fractions (SeedFraction semantics: a fraction
# of all N nodes). On a MultitypeNetwork a stratum's species seeds nodes of that type only, so the
# within-type fraction is ρ_X/n_a, and a species without a stratum (shared by the types) seeds the
# nodes left free by the stratum seeds, uniformly over all types (§J.6, as NetworkOutbreaks places
# it): a fraction ρ_X·F_a/ΣF of all nodes on type a, where F_a is the free fraction of all nodes on
# type a. On untyped and degree-correlated descriptors seeds are uniform over all nodes.
function _seed_vector(eng::_Engine, initial, N, fname)
    f = zeros(length(eng.states))
    q = ones(length(eng.types))
    initial === nothing && return f, q
    initial isa SeedSpec || throw(ArgumentError("$(fname): `initial` must be a SeedSpec"))
    cm = eng.model
    typed = eng.laws isa MultitypeNetwork && eng.net isa MultitypeNetwork
    shared = Tuple{Symbol,Float64}[]
    for (x, ρ) in seed_fractions(initial; N)
        x in cm.susceptible && continue             # the background compartment
        x in cm.species || throw(ArgumentError(
            "$(fname)(:$(cm.name)): the seeded compartment $(x) is not a species of the model"))
        ρ == 0 && continue
        hits = [i for (i, (_, y)) in enumerate(eng.states) if y === x]
        isempty(hits) && throw(ArgumentError(
            "$(fname)(:$(cm.name)): cannot place the seeds of $(x) on a node type"))
        if typed && length(hits) > 1
            push!(shared, (x, ρ))                   # placed after the stratum seeds
            continue
        end
        for i in hits
            a = eng.states[i][1]
            frac = typed ? ρ / eng.sizes[a] : ρ
            f[i] += frac
            q[a] -= frac
        end
    end
    if !isempty(shared)
        free = [eng.sizes[a] * max(q[a], 0.0) for a in eachindex(eng.types)]
        total = sum(free)
        ρs = sum(last, shared)
        ρs <= total + 1e-12 || throw(ArgumentError(
            "$(fname)(:$(cm.name)): the seeds of the species without a stratum ($(ρs) of all " *
            "nodes) exceed the nodes left by the stratum seeds ($(total))"))
        for (x, ρ) in shared, (i, (a, y)) in enumerate(eng.states)
            y === x || continue
            frac = ρ * free[a] / total / eng.sizes[a]
            f[i] += frac
            q[a] -= frac
        end
    end
    for (a, qa) in enumerate(q)
        qa < -1e-12 && throw(ArgumentError(
            "$(fname)(:$(cm.name)): the seeds exceed the nodes of type $(eng.types[a]) " *
            "(unseeded fraction $(qa))"))
        q[a] = max(qa, 0.0)
    end
    return f, q
end

function _require_final_size_model(eng::_Engine, fname)
    cm = eng.model
    back = [t for t in cm.transitions
            if !(t.from in cm.susceptible) && t.to !== nothing && t.to in cm.susceptible]
    isempty(back) || throw(ArgumentError(
        "$(fname)(:$(cm.name)): the model returns nodes to the susceptible class " *
        "($(_list(t.name for t in back))), as SIS and SIRS do, so the epidemic can become " *
        "endemic and there is no final size"))
    exits = [t for t in cm.transitions if t.from in cm.susceptible]
    isempty(exits) || throw(ArgumentError(
        "$(fname)(:$(cm.name)): the model has exits from the susceptible class " *
        "($(_list(t.name for t in exits))); the final size then depends on the course of the " *
        "epidemic (the survival factor ξ(t)), so it has no fixed-point equation; solve the " *
        "edge-based ODE (EdgeBasedModels.edge_based) to large t instead"))
    eng.mode === :exchange && throw(ArgumentError(
        "$(fname)(:$(cm.name), $(_network_label(eng.net))): with neighbour exchange the final " *
        "size depends on the course of the epidemic and has no fixed-point equation; solve the " *
        "edge-based DFD ODE (EdgeBasedModels.edge_based) to large t instead"))
    entry = zeros(Int, length(eng.types))
    for a in eachindex(eng.types)
        prods = unique(c.product for k in eng.kinds for c in k.contacts if k.dst == a)
        length(prods) <= 1 || throw(ArgumentError(
            "$(fname)(:$(cm.name)): the model has several entry states " *
            "($(_list(eng.states[x][2] for x in prods))); the split between them depends on the " *
            "course of the epidemic, so the final-size equation needs a single entry state (per " *
            "node type); solve the edge-based ODE (EdgeBasedModels.edge_based) instead"))
        isempty(prods) || (entry[a] = only(prods))
    end
    return entry
end

# ---- PGFs of the node types, as functions of the kind variables θ -----------------------------

# Value ψ_b(θ), ∂_ēψ_b(θ)/∂_ēψ_b(1) and ∂_ē∂_fψ_b(θ)/∂_ēψ_b(1) for the incoming kinds ē, f of b.
function _pgf_value(eng::_Engine, b::Int, θ)
    net = eng.net
    if net isa ConfigurationNetwork
        return Float64(pgf(net, θ[1]))
    elseif net isa MultiplexNetwork
        return prod(Float64(pgf(net[k.layer], θ[e])) for (e, k) in enumerate(eng.kinds); init = 1.0)
    else
        return Float64(pgf(eng.laws.degrees[b], _partner_arguments(eng, b, θ)))
    end
end

function _partner_arguments(eng::_Engine, b::Int, θ)
    x = Dict{Symbol,Float64}(a => 1.0 for a in eng.types)
    for (e, k) in enumerate(eng.kinds)
        k.dst == b && (x[eng.types[k.src]] = θ[e])
    end
    return x
end

function _pgf_ratio(eng::_Engine, b::Int, ē::Int, θ)
    net = eng.net
    if net isa ConfigurationNetwork
        k1 = Float64(pgf_derivative(net, 1.0, 1))
        return k1 > 0 ? Float64(pgf_derivative(net, θ[1], 1)) / k1 : 0.0   # no edges: no infection
    elseif net isa MultiplexNetwork
        layer = net[eng.kinds[ē].layer]
        v = Float64(pgf_derivative(layer, θ[ē], 1) / pgf_derivative(layer, 1.0, 1))
        for (f, k) in enumerate(eng.kinds)
            f == ē || (v *= Float64(pgf(net[k.layer], θ[f])))
        end
        return v
    else
        a = eng.types[eng.kinds[ē].src]
        law = eng.laws.degrees[b]
        return Float64(pgf_derivative(law, _partner_arguments(eng, b, θ), a) / mean_degree(law, a))
    end
end

function _pgf_ratio_derivative(eng::_Engine, b::Int, ē::Int, f::Int, θ)
    net = eng.net
    if net isa ConfigurationNetwork
        k1 = Float64(pgf_derivative(net, 1.0, 1))
        return k1 > 0 ? Float64(pgf_derivative(net, θ[1], 2)) / k1 : 0.0
    elseif net isa MultiplexNetwork
        ℓ = net[eng.kinds[ē].layer]
        norm = Float64(pgf_derivative(ℓ, 1.0, 1))
        if f == ē
            v = Float64(pgf_derivative(ℓ, θ[ē], 2)) / norm
        else
            m = net[eng.kinds[f].layer]
            v = Float64(pgf_derivative(ℓ, θ[ē], 1)) / norm * Float64(pgf_derivative(m, θ[f], 1))
        end
        for (g, k) in enumerate(eng.kinds)
            (g == ē || g == f) || (v *= Float64(pgf(net[k.layer], θ[g])))
        end
        return v
    else
        a = eng.types[eng.kinds[ē].src]
        c = eng.types[eng.kinds[f].src]
        law = eng.laws.degrees[b]
        x = _partner_arguments(eng, b, θ)
        return Float64(pgf_derivative(law, x, a, c) / mean_degree(law, a))
    end
end

# The reversed kind (same edge seen from the other end).
function _reverse_kinds(eng::_Engine)
    rev = zeros(Int, length(eng.kinds))
    for (e, k) in enumerate(eng.kinds)
        for (f, l) in enumerate(eng.kinds)
            if l.src == k.dst && l.dst == k.src && l.layer === k.layer
                rev[e] = f
                break
            end
        end
        rev[e] == 0 && throw(ErrorException("internal: no reverse of edge kind $(k.label)"))
    end
    return rev
end

# ---- persistent edges: θ_e = c_e + a_e Π_{src(e)}(ē, θ) ------------------------------------------

function _final_size_persistent(eng::_Engine, initial, N, fname)
    entry = _require_final_size_model(eng, fname)
    f, q = _seed_vector(eng, initial, N, fname)
    nk = length(eng.kinds)
    ops = [_operator(eng, e, fname) for e in 1:nk]
    rev = _reverse_kinds(eng)
    c = zeros(nk)
    a = zeros(nk)
    seedT = zeros(nk)                        # Σ_Y f(Y) T_e(Y): transmission by the seeds
    for (e, k) in enumerate(eng.kinds)
        b = k.src
        s = 0.0
        for (i, (t, _)) in enumerate(eng.states)
            (t == b && f[i] > 0) || continue
            Ti = _total_transmissibility(eng, e, ops[e], i)
            s += f[i] * (1 - Ti)
            seedT[e] += f[i] * Ti
        end
        Te = entry[b] == 0 ? 0.0 : _total_transmissibility(eng, e, ops[e], entry[b])
        c[e] = s + q[b] * (1 - Te)
        a[e] = q[b] * Te
    end
    G(θ) = [c[e] + a[e] * _pgf_ratio(eng, eng.kinds[e].src, rev[e], θ) for e in 1:nk]
    function DG(θ)
        D = zeros(nk, nk)
        for e in 1:nk
            a[e] == 0 && continue
            b = eng.kinds[e].src
            for g in 1:nk
                eng.kinds[g].dst == b || continue
                D[e, g] = a[e] * _pgf_ratio_derivative(eng, b, rev[e], g, θ)
            end
        end
        return D
    end
    θ = if nk == 1
        _solve_theta_scalar(θ1 -> G([θ1])[1] - θ1, θ1 -> DG([θ1])[1, 1] - 1, seedT[1] > 0, fname)
    else
        _solve_theta_vector(G, DG, seedT, a, eng, fname)
    end
    S = sum(eng.sizes[b] * q[b] * _pgf_value(eng, b, θ) for b in eachindex(eng.types))
    return clamp(1 - S, 0.0, 1.0)
end

# Scalar θ equation g(θ) = G(θ) − θ, convex on [0, 1] (ψ' has non-negative coefficients),
# g(0) ≥ 0. With transmitting seeds g(1) < 0 and the root in [0, 1) is unique. Without them
# g(1) = 0: θ = 1 unless g'(1) = qTκ_ex − 1 > 0, in which case the large-outbreak root lies
# where g < 0 just below 1 (found by halving the distance to 1).
function _solve_theta_scalar(g, dg, seeded::Bool, fname)
    what = "$(fname): the final-size equation"
    g0 = g(0.0)
    g0 <= 0 && return [0.0]
    if seeded
        return [_brent(g, 0.0, 1.0, g0, g(1.0); tol = 1e-15, what)]
    end
    dg(1.0) > 0 || return [1.0]                  # R₀ ≤ 1: no large outbreak
    δ = 0.5
    hi = 1 - δ
    ghi = g(hi)
    while ghi >= 0
        δ /= 2
        δ < 1e-15 && return [1.0]                # numerically at the threshold
        hi = 1 - δ
        ghi = g(hi)
    end
    lo = hi == 0.5 ? 0.0 : 1 - 2δ
    return [_brent(g, lo, hi, g(lo), ghi; tol = 1e-15, what)]
end

# Vector θ equations: a monotone system with non-negative power-series coefficients. Newton's
# method from 0 converges monotonically to the least fixed point (Etessami & Yannakakis 2009);
# each step is safeguarded by a monotone fixed-point step. Kinds that no seeded infection can
# reach keep θ = 1; without seeds every kind is active and θ = 1 is returned unless the spectral
# radius of G'(1) exceeds 1 (the large-outbreak limit).
function _solve_theta_vector(G, DG, seedT, a, eng::_Engine, fname)
    nk = length(seedT)
    ones_ = ones(nk)
    seeded = any(>(0), seedT)
    active = if seeded
        act = seedT .> 0
        changed = true
        while changed
            changed = false
            for (e, k) in enumerate(eng.kinds)
                act[e] && continue
                if a[e] > 0 && any(act[g] for g in 1:nk if eng.kinds[g].dst == k.src)
                    act[e] = true
                    changed = true
                end
            end
        end
        act
    else
        _spectral_radius(DG(ones_)) > 1 || return ones_
        trues(nk)
    end
    idx = findall(active)
    θ = ones(nk)
    θ[idx] .= 0.0
    for _ in 1:500
        Gθ = G(θ)
        res = Gθ[idx] .- θ[idx]
        maximum(abs, res) <= 1e-15 && return θ
        J = DG(θ)[idx, idx] - I
        step = try
            -(J \ res)
        catch err
            err isa LinearAlgebra.SingularException || rethrow()
            fill(NaN, length(idx))
        end
        cand = θ[idx] .+ step
        if all(isfinite, cand) && all(cand .>= θ[idx] .- 1e-14) && all(cand .<= 1 + 1e-12)
            θn = clamp.(cand, 0.0, 1.0)
        else
            θn = clamp.(Gθ[idx], 0.0, 1.0)       # monotone fallback
        end
        if maximum(abs, θn .- θ[idx]) <= 1e-15
            θ[idx] .= θn
            break
        end
        θ[idx] .= θn
    end
    res = maximum(abs, G(θ)[idx] .- θ[idx])
    res <= 1e-10 || throw(ErrorException(
        "$(fname): the final-size equations did not converge (residual $(res))"))
    return θ
end

# ---- fleeting contacts: cumulative hazard equations -------------------------------------------

# WellMixed(κ): u = A + qB(1 − e^{−κu}), S∞ = q e^{−κu}; MFSH: v = A + qB(1 − π(e^{−v})) with
# π(θ) = θψ'(θ)/ψ'(1), S∞ = q ψ(e^{−v}). B = Σ_r τ_r [V⁻¹ e_entry]_{J_r} (expected cumulative
# per-partner hazard of an infected node) and A = Σ_Y ρ_Y (the same from seed state Y).
function _final_size_fleeting(eng::_Engine, initial, N, fname)
    entry = _require_final_size_model(eng, fname)
    f, q = _seed_vector(eng, initial, N, fname)
    op = _operator(eng, 1, fname)
    hazard(Y) = _total_transmissibility(eng, 1, op, Y)
    A = sum((f[i] * hazard(i) for i in eachindex(f) if f[i] > 0); init = 0.0)
    B = entry[1] == 0 ? 0.0 : hazard(entry[1])
    qB = q[1] * B
    net = eng.net
    if net isa WellMixed
        κ = eng.M[1, 1]
        φ = u -> exp(-κ * u)
        slope = κ
        S∞ = u -> q[1] * exp(-κ * u)
    else
        d = net.degrees
        k1 = Float64(pgf_derivative(d, 1.0, 1))
        φ = v -> (θ = exp(-v); θ * Float64(pgf_derivative(d, θ, 1)) / k1)
        slope = eng.M[1, 1]                      # −dπ(e^{−v})/dv at 0 = 1 + κ_ex
        S∞ = v -> q[1] * Float64(pgf(d, exp(-v)))
    end
    h(u) = A + qB * (1 - φ(u)) - u
    what = "$(fname): the final-size equation"
    hi = A + qB
    if A > 0
        u = _brent(h, 0.0, hi, h(0.0), h(hi); tol = 1e-15 * max(1.0, hi), what)
    elseif qB * slope > 1
        lo = hi / 2
        hlo = h(lo)
        while hlo <= 0
            lo /= 2
            lo < 1e-300 && break
            hlo = h(lo)
        end
        u = hlo > 0 ? _brent(h, lo, hi, hlo, h(hi); tol = 1e-15 * max(1.0, hi), what) : 0.0
    else
        u = 0.0
    end
    return clamp(1 - S∞(u), 0.0, 1.0)
end

"""
    final_size(cm::ContactModel, net::NetworkDescriptor, p = Dict(); initial = nothing, N = nothing)
        -> Float64
    final_size(model, net, p = Dict(); kw...)   # any model that `contact_model` accepts

The final size R∞: the fraction of nodes **ever infected, including the seeds** (§E.2), for a
T_EB model with a single entry state (per node type) and no exits from the susceptible class.
On a configuration network it solves

    θ∞ = Σ_X ρ_X (1 − T(X)) + q [1 − T + T ψ'(θ∞)/ψ'(1)],   R∞ = 1 − q ψ(θ∞),

with q = 1 − Σ_X ρ_X, T the per-edge [`transmissibility`](@ref) from the entry state and T(X)
from a seed state X (0 for removed seeds). With seeds only in the entry state this is
θ∞ = 1 − T + T q ψ'(θ∞)/ψ'(1). The final size depends on the infectious period only through T,
so it is exact for any sojourn distribution (unlike the probability of a major outbreak,
verified issue E15, which is EdgeBasedModels' infector-side `epidemic_probability`).

- `initial`: a `SeedSpec` (`SeedFraction(:I => 0.01)`; `SeedCount`/`SeedNodes` need `N`), the
  same seeding as the ODE back ends, whose `:cumulative` observable tends to R∞. With
  `initial = nothing` (or seeds that cannot transmit) the result is the large-outbreak limit of
  a vanishing infectious seed: exactly 0 when R₀ ≤ 1 (or the non-transmitting seeds alone),
  otherwise the non-trivial root.
- `MultiplexNetwork`: one θ_ℓ per layer, θ_ℓ = … + qT_ℓ ψ_ℓ'(θ_ℓ)/ψ_ℓ'(1) Π_{m≠ℓ} ψ_m(θ_m)
  (Miller & Volz 2013); `MultitypeNetwork` and `DegreeCorrelatedNetwork`: one θ per edge kind
  with the joint PGFs of the types (seed fractions are fractions of all nodes; a stratum's
  species seeds nodes of that type).
- `WellMixed(κ)`: the mass-action final size u = A + qB(1 − e^{−κu}), R∞ = 1 − q e^{−κu}, with
  B = Σ_r τ_r [V⁻¹ e_entry]_{J_r} (R₀ = κB); `MFSHNetwork`: −ln θ = A + qB(1 − θψ'(θ)/ψ'(1)),
  R∞ = 1 − qψ(θ).

The scalar equation is solved by Brent's method on a bracket, the vector equations by Newton's
method from 0 with monotone safeguards; both check convergence and throw rather than return an
unconverged value (verified issue E18: the old fixed-point iteration returned values up to 150×
too small just above threshold). Models with several entry states (two strains), exits
(vaccination) or neighbour exchange have no fixed-point equation: solve the edge-based ODE.
"""
function final_size(cm::ContactModel, net::NetworkDescriptor,
                    p::_AnalysisParams = _default_params();
                    initial::Union{Nothing,SeedSpec} = nothing, N::Union{Nothing,Integer} = nothing)
    fname = :final_size
    eng = _prepare(cm, net, p, fname)
    eng.mode === :fleeting && return _final_size_fleeting(eng, initial, N, fname)
    return _final_size_persistent(eng, initial, N, fname)
end
final_size(model, net::NetworkDescriptor, p::_AnalysisParams = _default_params(); kw...) =
    final_size(contact_model(model), net, p; kw...)

# =============================================================================================
# Calibration
# =============================================================================================

const _CALIBRATION_TARGETS = (:R0, :growth, :r, :final_size)

"""
    calibrate(cm, net::NetworkDescriptor, p = Dict(); target = :R0 => 2.0, vary = :τ,
              bracket = nothing, initial = nothing, N = nothing, rtol = 1e-12)
        -> Dict{Symbol,Float64}

Solve one scalar equation for the parameter `vary`: the value at which the quantity named by
`target` equals the given number, with every other parameter taken from `p` (and the model
defaults). Returns a copy of `p` (as `Dict{Symbol,Float64}`) with `vary` set to the solution.

- `target = :R0 => R` ([`basic_reproduction_number`](@ref)), `:growth => r` (alias `:r`;
  [`early_growth_rate`](@ref)) or `:final_size => z` ([`final_size`](@ref) with `initial`).
- `vary` is any rate parameter of the model: a per-contact rate, a recovery rate, or a common
  factor (e.g. `c` in τ_home = 3c, τ_comm = c).
- The root is bracketed by scanning geometrically outwards (factors of 2, up to 2^±60) from the
  current value of `vary` (in `p`, else the model default, else 1), or taken from
  `bracket = (lo, hi)`, then refined by Brent's method to relative tolerance `rtol`. If the
  target is not attained (for example R₀ > κ_ex for SIR on a configuration network, since
  T = τ/(τ + γ) < 1) an `ArgumentError` reports the range that was reached.

Calibration is a separate verb because it is not natural (F6): it solves a per-model equation,
unlike a rate convention, and does not commute with gluing or stratification. For example the
Poisson SBM with mean contacts [6 2; 2 4] (ρ = 7.236) needs τ = 0.0955 for R₀ = 2 at γ = 1/4.
"""
function calibrate(cm::ContactModel, net::NetworkDescriptor, p::_AnalysisParams = _default_params();
                   target::Pair{Symbol,<:Real} = :R0 => 2.0, vary::Symbol = :τ,
                   bracket::Union{Nothing,Tuple{Real,Real}} = nothing,
                   initial::Union{Nothing,SeedSpec} = nothing, N::Union{Nothing,Integer} = nothing,
                   rtol::Real = 1e-12)
    what, value = first(target), Float64(last(target))
    what in _CALIBRATION_TARGETS || throw(ArgumentError(
        "calibrate: unknown target :$(what); expected one of $(_CALIBRATION_TARGETS)"))
    names = _parameter_names(cm)
    vary in names || throw(ArgumentError(
        "calibrate(:$(cm.name)): :$(vary) is not a rate parameter of the model (parameters: " *
        "$(_list(names)))"))
    base = Dict{Symbol,Float64}(k => v for (k, v) in cm.defaults)
    for (k, v) in _param_dict(p)
        base[Symbol(k)] = Float64(v)
    end
    quantity = if what === :R0
        q -> basic_reproduction_number(cm, net, q)
    elseif what === :final_size
        q -> final_size(cm, net, q; initial, N)
    else
        q -> early_growth_rate(cm, net, q)
    end
    function f(v)
        q = copy(base)
        q[vary] = v
        return quantity(q) - value
    end
    # evaluation that treats a degenerate parameter value (e.g. an infinite R₀) as missing
    function fsafe(v)
        try
            return f(v)
        catch err
            err isa ArgumentError || err isa LinearAlgebra.SingularException ||
                err isa DomainError || err isa ErrorException || rethrow()
            return NaN
        end
    end
    what_s = "calibrate(:$(cm.name), target = :$(what) => $(value), vary = :$(vary))"
    lo, hi, flo, fhi = if bracket !== nothing
        a, b = Float64.(bracket)
        (0 <= a < b) || throw(ArgumentError("$(what_s): bracket must satisfy 0 ≤ lo < hi"))
        a, b, f(a), f(b)
    else
        _calibration_bracket(fsafe, get(base, vary, 1.0), what_s, value)
    end
    root = _brent(f, lo, hi, flo, fhi; tol = Float64(rtol) * max(abs(lo), abs(hi), eps()),
                  what = what_s)
    out = Dict{Symbol,Float64}(Symbol(k) => Float64(v) for (k, v) in _param_dict(p))
    out[vary] = root
    return out
end
calibrate(model, net::NetworkDescriptor, p::_AnalysisParams = _default_params(); kw...) =
    calibrate(contact_model(model), net, p; kw...)

# Scan v0·2^k (k = 0, ±1, …, ±60) outwards from v0 for adjacent grid points with a sign change
# of f, evaluating lazily (a degenerate value, NaN, is skipped).
function _calibration_bracket(f, v0, what_s, value)
    v0 = (isfinite(v0) && v0 > 0) ? Float64(v0) : 1.0
    cache = Dict{Int,Float64}()
    val(k) = get!(() -> f(v0 * 2.0^k), cache, k)
    for dist in 0:59
        for (i, j) in ((dist, dist + 1), (-dist - 1, -dist))
            fi, fj = val(i), val(j)
            (isnan(fi) || isnan(fj)) && continue
            (fi == 0 || fj == 0 || sign(fi) != sign(fj)) && return v0 * 2.0^i, v0 * 2.0^j, fi, fj
        end
    end
    finite = [v + value for v in values(cache) if !isnan(v)]
    range = isempty(finite) ? "no value could be evaluated" :
            "the values reached lie in [$(minimum(finite)), $(maximum(finite))]"
    throw(ArgumentError("$(what_s): the target is not attained for $(v0 * 2.0^-60) ≤ value ≤ " *
                        "$(v0 * 2.0^60); $(range). Pass `bracket = (lo, hi)` if it lies elsewhere"))
end
