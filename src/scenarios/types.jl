# Owner: WP12 (DESIGN_NetworkEpiCore.md §E.2, §E.4; work package in §G.2).
#
# The data types of the shared validation scenarios: conditioning and time-alignment rules,
# the simulation settings `SimConfig`, and the `Scenario` itself (pure data: model, network,
# parameters, seeding, time grid, simulation settings, the back ends it is meant for, tags and
# the expected values that NetworkEpiCore computes when the scenario is built). The canonical
# text and hash are in scenarios/canonical_text.jl, the registry in scenarios/registry.jl and
# the canonical list of §E.3 in scenarios/canonical.jl.

export MajorOutbreak, Survival, Unconditioned, NoAlignment, CumulativeCrossing
export SimConfig, Scenario
export SCENARIO_BACKENDS, BACKEND_VERDICTS, SIM_ALGORITHMS, EXPECTED_QUANTITIES

# =============================================================================================
# Conditioning and time alignment (§E.2)
# =============================================================================================

"""
    MajorOutbreak(threshold = 0.05)

Conditioning rule for SIR-type scenarios (§E.2): a run is a **major outbreak** if its cumulative
incidence *excluding the seeds* reaches `threshold`·N by the end of the time span, i.e.
(`:cumulative`(t_end) − Σ_{X infected} ρ_X) ≥ `threshold`, where the sum is over the seeds in
infected compartments ([`infected_species`](@ref); §J.8), the seeds that `:cumulative` counts
(a seed in R, a vaccinated V or a traced Q is not an infection). Excluding the seeds makes the
rule independent of the seed fraction. Summaries store the statistics conditioned on major runs
and the unconditioned ones, and P(major) with a 95% Wilson interval; comparisons use the
conditioned mean.
"""
struct MajorOutbreak
    threshold::Float64
    function MajorOutbreak(threshold::Real)
        (isfinite(threshold) && 0 <= threshold <= 1) ||
            throw(ArgumentError("MajorOutbreak: the threshold is a fraction in [0, 1]; got $threshold"))
        return new(Float64(threshold))
    end
end
MajorOutbreak() = MajorOutbreak(0.05)

"""
    Survival()

Conditioning rule for scenarios with an endemic state (SIS, SIRS; §E.2): a run is kept if its
prevalence (the `:infectious` observable) at the end of the time span is positive.
"""
struct Survival end

"""
    Unconditioned()

No conditioning: every run counts as a "major" run, so the conditioned and unconditioned
statistics of a summary coincide.
"""
struct Unconditioned end

"""
    NoAlignment()

No time alignment of the runs (the default for canonical scenarios, §E.2): with a fixed positive
seed fraction ρ the law-of-large-numbers limit is the ODE started from the same ρ, with no random
delay at leading order.
"""
struct NoAlignment end

"""
    CumulativeCrossing(level)

Time alignment for small-seed scenarios (§E.2). Let c_i be the first time at which the
cumulative incidence *excluding the seeds* of run i reaches `level` (a fraction of N, e.g. 0.02).
The reference time t* is the grid time nearest the median of c_i over the kept runs, and run i
is shifted by t* − c_i, so that every run crosses the level at t*; the shifts and t* are stored
in the summary (`extras[:alignment]`, with t* as `"reference_time"`), and aligned and unaligned
summaries are shown side by side. Runs that never cross the level are not shifted.

t* is not the time at which a deterministic curve crosses the level. To compare a deterministic
curve with an aligned summary, shift it the same way first: find t_det, the time at which its
`:cumulative` minus its initial value first reaches `level`, and shift it by t* − t_det
(`NetworkOutbreaks.aligned_curves(det, ref)` does this). A raw `compare(ref, det)` against an
aligned summary compares curves with different time origins.
"""
struct CumulativeCrossing
    level::Float64
    function CumulativeCrossing(level::Real)
        (isfinite(level) && 0 < level < 1) ||
            throw(ArgumentError("CumulativeCrossing: the level is a fraction in (0, 1); got $level"))
        return new(Float64(level))
    end
end

const _Condition = Union{MajorOutbreak,Survival,Unconditioned}
const _Alignment = Union{NoAlignment,CumulativeCrossing}

Base.show(io::IO, c::MajorOutbreak) = print(io, "MajorOutbreak(", c.threshold, ")")
Base.show(io::IO, c::CumulativeCrossing) = print(io, "CumulativeCrossing(", c.level, ")")

# =============================================================================================
# Simulation settings
# =============================================================================================

"""
    SIM_ALGORITHMS

The stochastic simulation algorithms a [`SimConfig`](@ref) may name; NetworkOutbreaks maps each
to its implementation: `:next_reaction` (NextReaction, the default), `:direct` (DirectSSA, the
reference implementation), `:composition_rejection`, `:has`, `:mass_action` (MassActionSSA,
the exact count-level lumping used for `WellMixed` networks) and `:fleeting`
(FleetingContactSSA, the count-level sampler of an `MFSHNetwork`, in which each contact of a
stub is with a uniformly chosen stub of the other nodes).
"""
const SIM_ALGORITHMS = (:next_reaction, :direct, :composition_rejection, :has, :mass_action,
                        :fleeting)

"""
    SimConfig(; N = 10_000, nsims = 200, graphs = :per_run, algorithm = :next_reaction,
              base_seed = 20260926, condition = MajorOutbreak(0.05), align = NoAlignment())

Settings of the reference stochastic ensemble of a [`Scenario`](@ref) (§E.2), run by
NetworkOutbreaks:

- `N` nodes and `nsims` runs;
- `graphs`: `:per_run` (a fresh graph for every run, so runs are iid and the standard error is
  sd/√n; the default), `:fixed` (one quenched graph for every run, the `_fixed` scenarios of the
  individual- and pair-based models, returned by `scenario_graph(sc)`), or `(:pool, G)` (G graphs
  shared by the runs, whose standard error must then use the between-graph variance);
- `algorithm`: one of [`SIM_ALGORITHMS`](@ref);
- `base_seed` (a `UInt64`): graph r is drawn with `NetworkOutbreaks.stable_rng(base_seed + r)`
  and SSA run r with `NetworkOutbreaks.stable_rng(base_seed + 2^32 + r)` (§J.7), where
  `stable_rng(s) = StableRNG(splitmix64(s + golden))`; raw `StableRNG(base_seed + r)` streams are
  not used, because adjacent raw seeds are strongly correlated;
- `condition`: [`MajorOutbreak`](@ref), [`Survival`](@ref) or [`Unconditioned`](@ref);
- `align`: [`NoAlignment`](@ref) or [`CumulativeCrossing`](@ref).

Every field enters the scenario hash ([`scenario_hash`](@ref)).
"""
struct SimConfig
    N::Int
    nsims::Int
    graphs::Union{Symbol,Tuple{Symbol,Int}}
    algorithm::Symbol
    base_seed::UInt64
    condition::_Condition
    align::_Alignment
    function SimConfig(N::Integer, nsims::Integer, graphs, algorithm::Symbol, base_seed::Integer,
                       condition::_Condition, align::_Alignment)
        N >= 1 || throw(ArgumentError("SimConfig: N must be ≥ 1; got $N"))
        nsims >= 1 || throw(ArgumentError("SimConfig: nsims must be ≥ 1; got $nsims"))
        g = _check_graphs(graphs)
        algorithm in SIM_ALGORITHMS || throw(ArgumentError(
            "SimConfig: unknown algorithm :$(algorithm); expected one of $(SIM_ALGORITHMS)"))
        base_seed >= 0 || throw(ArgumentError("SimConfig: base_seed must be ≥ 0; got $base_seed"))
        return new(Int(N), Int(nsims), g, algorithm, UInt64(base_seed), condition, align)
    end
end

function SimConfig(; N::Integer = 10_000, nsims::Integer = 200, graphs = :per_run,
                   algorithm::Symbol = :next_reaction, base_seed::Integer = 20260926,
                   condition::_Condition = MajorOutbreak(0.05), align::_Alignment = NoAlignment())
    return SimConfig(N, nsims, graphs, algorithm, base_seed, condition, align)
end

function _check_graphs(g::Symbol)
    g in (:per_run, :fixed) || throw(ArgumentError(
        "SimConfig: graphs must be :per_run, :fixed or (:pool, G); got :$(g)"))
    return g
end
function _check_graphs(g::Tuple{Symbol,Integer})
    (first(g) === :pool && last(g) >= 1) || throw(ArgumentError(
        "SimConfig: graphs must be :per_run, :fixed or (:pool, G) with G ≥ 1; got $(g)"))
    return (:pool, Int(last(g)))
end
_check_graphs(g) = throw(ArgumentError(
    "SimConfig: graphs must be :per_run, :fixed or (:pool, G); got $(repr(g))"))

Base.:(==)(a::SimConfig, b::SimConfig) =
    all(getfield(a, f) == getfield(b, f) for f in fieldnames(SimConfig))
Base.hash(s::SimConfig, h::UInt) =
    foldl((acc, f) -> hash(getfield(s, f), acc), fieldnames(SimConfig); init = hash(:SimConfig, h))

function Base.show(io::IO, s::SimConfig)
    print(io, "SimConfig(N = ", s.N, ", nsims = ", s.nsims, ", graphs = ", repr(s.graphs),
          ", algorithm = ", repr(s.algorithm), ", base_seed = ", Int(s.base_seed), ", condition = ",
          s.condition, ", align = ", s.align, ")")
end

# =============================================================================================
# Back ends, verdicts and expected quantities
# =============================================================================================

"""
    SCENARIO_BACKENDS

The deterministic back ends a [`Scenario`](@ref) can declare in its `backends` dictionary, as a
`NamedTuple` mapping each key to the back end of [`admissibility`](@ref) (see `BACKENDS`) that
decides whether the model can be given to it:

| key | back end | admissibility |
|---|---|---|
| `:edge_based` | EdgeBasedModels `edge_based(model, net)` (configuration, well-mixed, multitype, multiplex; Volz clustered; DFD; the stretch lifts) | `:edge_based` |
| `:pairwise_const` | NodeBasedModels heterogeneous pairwise, constant closure K = `closure_constant(net)` | `:pairwise` |
| `:pairwise_bernoulli` | NodeBasedModels homogeneous pairwise, Bernoulli closure (regular networks) | `:pairwise` |
| `:pairwise_keeling` | NodeBasedModels Keeling clustered closure, ϕ = `clustering_coefficient(net)` | `:pairwise` |
| `:pairwise_multitype` | NodeBasedModels population-level multitype pairwise (stretch) | `:pairwise` |
| `:pgf_closure` | NodeBasedModels `PGFClosure` (S-anchored, exact for any degree PGF) | `:s_anchored` |
| `:s_anchored` | NodeBasedModels S-anchored pairwise subsystem PW^S | `:s_anchored` |
| `:mean_field` | NodeBasedModels `MeanFieldClosure` (well mixed) | `:pairwise` |
| `:reinfection` | NodeBasedModels pairwise on `with_reinfection_counting(model, L)` | `:pairwise` |
| `:motif` | NodeBasedModels motif-based closures (m = 2, 3, 4) | `:pairwise` |
| `:neighbourhood` | NodeBasedModels neighbourhood-based model (n = 2) | `:pairwise` |
| `:individual` | NodeBasedModels individual-based model on a sampled or fixed graph | `:individual` |
| `:pair` | NodeBasedModels pair-based model on a sampled or fixed graph | `:pair` |
| `:mass_action` | the mass-action ODE (`mass_action`, EdgeBasedModels reverse maps) | `:mass_action` |

The reference is always the NetworkOutbreaks ensemble, so every scenario model must be admissible
for `:stochastic`. Each declared back end carries one of the [`BACKEND_VERDICTS`](@ref).
"""
const SCENARIO_BACKENDS = (edge_based = :edge_based, pairwise_const = :pairwise,
                           pairwise_bernoulli = :pairwise, pairwise_keeling = :pairwise,
                           pairwise_multitype = :pairwise, pgf_closure = :s_anchored,
                           s_anchored = :s_anchored, mean_field = :pairwise,
                           reinfection = :pairwise, motif = :pairwise,
                           neighbourhood = :pairwise, individual = :individual, pair = :pair,
                           mass_action = :mass_action)

"""
    BACKEND_VERDICTS

What a [`Scenario`](@ref) declares about each of its back ends, relative to the reference
ensemble (§E.2, §E.3):

- `:exact_limit`: the back end is the large-N limit of the stochastic model, so the gap to the
  ensemble mean vanishes as N grows (EBM and NBM tests assert D∞(I) < 0.005 and |ΔR∞| < 0.005
  against the committed summary);
- `:biased`: a structural bias that does not vanish with N (pinned by the tests, e.g.
  |ΔR∞| > 0.02 for constant-K pairwise on a non-Poisson-type network);
- `:approximate`: an approximation whose error is reported, not asserted (Keeling clustered,
  motif, neighbourhood, graph-level models on cycles);
- `:inadmissible`: the back end refuses the model (the scenario records it, and the tests check
  that `admissibility` agrees).
"""
const BACKEND_VERDICTS = (:exact_limit, :biased, :approximate, :inadmissible)

"""
    EXPECTED_QUANTITIES

The quantities a [`Scenario`](@ref) can ask NetworkEpiCore to compute when it is built (its
`expected` dictionary; never typed by hand), each from the scenario's model, network, parameters
and seeding:

- `:R0` — [`basic_reproduction_number`](@ref); `:T` — [`transmissibility`](@ref) from the unique
  entry state (on a `DynamicNetwork` with neighbour exchange this is the per-partnership
  transmissibility of one edge epoch, τ/(τ + γ + η) for SIR, not the T of R₀ = T·κ_ex);
  `:r` — [`early_growth_rate`](@ref);
- `:final_size` — [`final_size`](@ref) with the scenario's seeding (the limit of `:cumulative`);
- `:R0_additive` — the (wrong) sum of the single-layer R₀s of a multiplex scenario, for comparison
  with R₀ = ρ(K);
- `:mean_degree`, `:excess_degree`, `:closure_constant`, `:clustering`
  ([`clustering_coefficient`](@ref)), `:assortativity` (`degree_assortativity`) — summaries of
  the network descriptor.
"""
const EXPECTED_QUANTITIES = (:R0, :T, :r, :final_size, :R0_additive, :mean_degree,
                             :excess_degree, :closure_constant, :clustering, :assortativity)

# The single-layer part of a multiplex model: the contacts on layer ℓ (and on :all), on :all.
function _layer_model(cm::ContactModel, ℓ::Symbol)
    cs = Contact[Contact(c.recipient, c.infector, c.product, c.rate, :all, c.name)
                 for c in cm.contacts if c.layer === ℓ || c.layer === :all]
    return _rebuild(cm; contacts = cs)
end

function _expected_value(q::Symbol, cm::ContactModel, net, p, initial, N)
    q === :R0 && return basic_reproduction_number(cm, net, p)
    q === :T && return transmissibility(cm, net, p)
    q === :r && return early_growth_rate(cm, net, p)
    q === :final_size && return final_size(cm, net, p; initial, N)
    q === :mean_degree && return mean_degree(net)
    q === :excess_degree && return excess_degree(net)
    q === :closure_constant && return closure_constant(net)
    q === :clustering && return clustering_coefficient(net)
    q === :assortativity && return degree_assortativity(net)
    if q === :R0_additive
        net isa MultiplexNetwork || throw(ArgumentError(
            "the expected quantity :R0_additive needs a MultiplexNetwork; got $(nameof(typeof(net)))"))
        return sum(basic_reproduction_number(_layer_model(cm, ℓ), net[ℓ], p) for ℓ in layer_names(net))
    end
    throw(ArgumentError("unknown expected quantity :$(q); expected one of $(EXPECTED_QUANTITIES)"))
end

function _expected_values(quantities, cm::ContactModel, net, p, initial, N, where)
    out = Dict{Symbol,Float64}()
    for q in quantities
        q in EXPECTED_QUANTITIES || throw(ArgumentError(
            "$(where): unknown expected quantity :$(q); expected one of $(EXPECTED_QUANTITIES)"))
        v = try
            _expected_value(q, cm, net, p, initial, N)
        catch err
            err isa ArgumentError || rethrow()
            throw(ArgumentError("$(where): NetworkEpiCore cannot compute the expected quantity " *
                                ":$(q) for this scenario: $(err.msg)"))
        end
        out[q] = Float64(v)
    end
    return out
end

# =============================================================================================
# Scenario
# =============================================================================================

"""
    Scenario(id::Symbol; title, model, network, params, initial, tspan, tstep = 0.25,
             tgrid = nothing, observables = nothing, sim = SimConfig(), backends = Dict(),
             tags = Symbol[], expected = (), notes = "")

A shared validation scenario (§E.3, §E.4): pure data that the edge-based (EBM), node-based
(NBM) and stochastic (NetworkOutbreaks) back ends all read, so that their curves can be compared
against one committed reference ensemble.

- `id`: a Symbol of letters, digits and underscores (it names the summary files);
- `model`: anything `contact_model` accepts, stored as a [`ContactModel`](@ref); its rates must
  be numbers, parameter names or arithmetic `Expr`s (no symbolic rates);
- `network`: a [`NetworkDescriptor`](@ref);
- `params`: a value for **every** rate parameter of the model, and nothing else (stored as
  `Dict{Symbol,Float64}`; model defaults are not used);
- `initial`: a [`SeedFraction`](@ref) naming non-susceptible species; ρ_X·N must be an integer for
  every X (so the deterministic and stochastic seeds are identical), and on a `MultitypeNetwork`
  every type size n_a·N must be an integer and the seeds of a stratum's species fit in it; a
  species without a stratum (shared by the node types, as in heterogeneous susceptibility) is
  seeded on the nodes of every type left free by the stratum seeds (§J.6), and must fit in them;
- `tspan = (t0, t1)` and `tgrid` (default `t0:tstep:t1`), the grid of every curve and summary;
- `observables`: default every species, then `:infectious` (the sum of the infectors, the
  `infectious_species` of the model) and `:cumulative`, per node (§J.8): the seeds placed in
  infected compartments ([`infected_species`](@ref); not those in R, a vaccinated V or a traced
  Q) plus the cumulative number of entries into infection, by any reaction, from a compartment
  that is not infected into one that is (a tracing contact S + I → Q + I is not one). It is the
  fraction ever infected for T_EB models and cumulative incidence for SIS/SIRS; its limit is the
  final size;
- `sim`: the [`SimConfig`](@ref) of the reference ensemble;
- `backends`: `key => verdict` for the deterministic back ends the scenario is meant for (keys of
  [`SCENARIO_BACKENDS`](@ref), verdicts in [`BACKEND_VERDICTS`](@ref));
- `tags`: Symbols used by [`scenarios`](@ref) to select scenarios (see there for the vocabulary);
- `expected`: names from [`EXPECTED_QUANTITIES`](@ref); each is **computed now** by
  NetworkEpiCore from the model, network, parameters and seeding, never typed by hand;
- `notes`: free text.

The positional constructor `Scenario(id, title, model, network, params, initial, tspan, tgrid,
observables, sim, backends, tags, expected, notes)` takes the same data (with `expected` as
quantity names). Both validate all of this, including that the model is admissible for
`:stochastic` (the reference ensemble) and that every declared back end other than an
`:inadmissible` one accepts the model on the network. The title, notes, tags, back ends and
expected values do not enter the [`scenario_hash`](@ref); everything that the simulation reads
does.

Use [`scenario`](@ref) to look up a registered scenario and [`derive`](@ref) to vary one.
"""
struct Scenario
    id::Symbol
    title::String
    model::ContactModel
    network::NetworkDescriptor
    params::Dict{Symbol,Float64}
    initial::SeedSpec
    tspan::Tuple{Float64,Float64}
    tgrid::StepRangeLen{Float64,Base.TwicePrecision{Float64},Base.TwicePrecision{Float64},Int}
    observables::Vector{Symbol}
    sim::SimConfig
    backends::Dict{Symbol,Symbol}
    tags::Vector{Symbol}
    expected::Dict{Symbol,Float64}
    notes::String
    function Scenario(id::Symbol, title::AbstractString, model::ContactModel,
                      network::NetworkDescriptor, params::AbstractDict, initial::SeedSpec,
                      tspan::Tuple{Real,Real}, tgrid::AbstractRange, observables::AbstractVector,
                      sim::SimConfig, backends::AbstractDict, tags::AbstractVector,
                      expected, notes::AbstractString)
        where = "Scenario :$(id)"
        _check_scenario_id(id)
        p = _check_scenario_params(model, params, where)
        ts = (Float64(tspan[1]), Float64(tspan[2]))
        grid = _check_tgrid(ts, tgrid, where)
        obs = _check_observables(model, observables, where)
        _check_scenario_seeds(model, network, initial, sim, where)
        bk = _check_backends(model, network, backends, where)
        _check_stochastic(model, network, where)
        tg = unique!(collect(Symbol, tags))
        # expected values are computed here from quantity names; they cannot be given
        (expected isa AbstractDict || !all(q -> q isa Symbol, expected)) && throw(ArgumentError(
            "$(where): `expected` lists quantity names from EXPECTED_QUANTITIES (e.g. " *
            "(:R0, :final_size)); their values are computed by NetworkEpiCore, never given"))
        ex = _expected_values(collect(Symbol, expected), model, network, p, initial, sim.N, where)
        return new(id, String(title), model, network, p, initial, ts, grid, obs, sim, bk, tg, ex,
                   String(notes))
    end
end

function Scenario(id::Symbol; title::AbstractString = string(id), model, network::NetworkDescriptor,
                  params::AbstractDict, initial::SeedSpec, tspan::Tuple{Real,Real},
                  tstep::Real = 0.25, tgrid::Union{Nothing,AbstractRange} = nothing,
                  observables::Union{Nothing,AbstractVector} = nothing, sim::SimConfig = SimConfig(),
                  backends::AbstractDict = Dict{Symbol,Symbol}(), tags::AbstractVector = Symbol[],
                  expected = (), notes::AbstractString = "")
    cm = contact_model(model)
    grid = tgrid === nothing ? _default_tgrid(tspan, tstep, "Scenario :$(id)") : tgrid
    obs = observables === nothing ? _default_observables(cm) : observables
    return Scenario(id, title, cm, network, params, initial, tspan, grid, obs, sim, backends, tags,
                    expected, notes)
end

function _check_scenario_id(id::Symbol)
    occursin(r"^[A-Za-z][A-Za-z0-9_]*$", String(id)) || throw(ArgumentError(
        "Scenario: the id :$(id) must start with a letter and contain only ASCII letters, digits " *
        "and underscores (it names the summary files)"))
    return nothing
end

function _check_scenario_params(cm::ContactModel, params::AbstractDict, where)
    for r in Iterators.flatten((cm.contacts, cm.transitions))
        _is_symbolic_rate(r.rate) && throw(ArgumentError(
            "$(where): the rate of `$(r.name)` is symbolic; scenario rates must be numbers, " *
            "parameter names or arithmetic Exprs (so that they can be hashed)"))
    end
    if cm.convention isa DensityDependent && _is_symbolic_rate(cm.convention.N)
        throw(ArgumentError("$(where): the DensityDependent population size is symbolic"))
    end
    p = Dict{Symbol,Float64}()
    for (k, v) in params
        (v isa Real && !_is_symbolic_rate(v) && isfinite(v)) || throw(ArgumentError(
            "$(where): parameter $(k) must be a finite number; got $(repr(v))"))
        p[Symbol(k)] = Float64(v)
    end
    names = _parameter_names(cm)
    missing_ = [n for n in names if !haskey(p, n)]
    extra = sort!([k for k in keys(p) if !(k in names)])
    isempty(missing_) || throw(ArgumentError(
        "$(where): no value for the rate parameter(s) $(_list(missing_)); a scenario gives every " *
        "parameter explicitly (model defaults are not used)"))
    isempty(extra) || throw(ArgumentError(
        "$(where): $(_list(extra)) are not rate parameters of the model :$(cm.name) (parameters: " *
        "$(_list(names)))"))
    instantiate(cm, p)            # every rate evaluates to a number ≥ 0
    return p
end

const _TGrid = StepRangeLen{Float64,Base.TwicePrecision{Float64},Base.TwicePrecision{Float64},Int}

function _default_tgrid(tspan, tstep, where)
    t0, t1 = Float64(tspan[1]), Float64(tspan[2])
    (isfinite(t0) && isfinite(t1) && t1 > t0) ||
        throw(ArgumentError("$(where): tspan must be finite with t0 < t1; got $(tspan)"))
    (isfinite(tstep) && tstep > 0) ||
        throw(ArgumentError("$(where): tstep must be finite and > 0; got $(tstep)"))
    n = round(Int, (t1 - t0) / tstep)
    isapprox(t0 + n * tstep, t1; rtol = 1e-12, atol = 1e-12) || throw(ArgumentError(
        "$(where): tstep = $(tstep) does not divide tspan = $(tspan)"))
    return range(t0; step = Float64(tstep), length = n + 1)
end

function _check_tgrid(ts::Tuple{Float64,Float64}, tgrid::AbstractRange, where)
    t0, t1 = ts
    (isfinite(t0) && isfinite(t1) && t1 > t0) ||
        throw(ArgumentError("$(where): tspan must be finite with t0 < t1; got $(ts)"))
    length(tgrid) >= 2 || throw(ArgumentError("$(where): tgrid needs at least two points"))
    step(tgrid) > 0 || throw(ArgumentError("$(where): tgrid must be increasing"))
    grid = range(Float64(first(tgrid)); step = Float64(step(tgrid)), length = length(tgrid))
    tol = 1e-9 * max(1.0, abs(t1))
    (abs(first(grid) - t0) <= tol && abs(last(grid) - t1) <= tol) || throw(ArgumentError(
        "$(where): tgrid must run from tspan[1] = $(t0) to tspan[2] = $(t1); got " *
        "$(first(grid)):$(step(grid)):$(last(grid))"))
    return grid::_TGrid
end

# species, then :infectious (Σ infectors) and :cumulative (infected seeds + entries into infection)
_default_observables(cm::ContactModel) = vcat(species_names(cm), [:infectious, :cumulative])

function _check_observables(cm::ContactModel, observables, where)
    obs = collect(Symbol, observables)
    isempty(obs) && throw(ArgumentError("$(where): no observables"))
    allunique(obs) || throw(ArgumentError("$(where): observables are not unique: $(obs)"))
    known = Set(vcat(cm.species, [:infectious, :cumulative]))
    bad = [x for x in obs if !(x in known)]
    isempty(bad) || throw(ArgumentError(
        "$(where): unknown observable(s) $(_list(bad)); observables are species of the model, " *
        ":infectious and :cumulative"))
    return obs
end

function _check_scenario_seeds(cm::ContactModel, net, initial::SeedSpec, sim::SimConfig, where)
    initial isa SeedFraction || throw(ArgumentError(
        "$(where): the seeding must be a SeedFraction (every scenario states ρ_X explicitly); " *
        "got $(nameof(typeof(initial)))"))
    isempty(initial.fractions) && throw(ArgumentError("$(where): the seeding names no compartment"))
    for (X, ρ) in initial.fractions
        X in cm.species || throw(ArgumentError(
            "$(where): the seeded compartment $(X) is not a species of the model :$(cm.name)"))
        X in cm.susceptible && throw(ArgumentError(
            "$(where): the seeded compartment $(X) is susceptible; seeds are placed in infected " *
            "states and every other node starts susceptible"))
        ρ > 0 || throw(ArgumentError("$(where): the seed fraction of $(X) must be > 0"))
    end
    d = initial.default
    (d === nothing || d in cm.susceptible) || throw(ArgumentError(
        "$(where): the background compartment $(d) of the seeding must be susceptible"))
    try
        seed_counts(initial, sim.N; exact = true)
    catch err
        err isa ArgumentError || rethrow()
        throw(ArgumentError("$(where): $(err.msg) (N = $(sim.N))"))
    end
    net isa MultitypeNetwork && _check_type_seeds(cm, net, initial, sim.N, where)
    return nothing
end

function _check_type_seeds(cm::ContactModel, net::MultitypeNetwork, initial, N, where)
    for (a, n) in zip(net.types, net.sizes)
        abs(n * N - round(n * N)) <= 1e-9 * max(1.0, n * N) || throw(ArgumentError(
            "$(where): the node type $(a) has size $(n), which is not a whole number of nodes at " *
            "N = $(N) (n·N = $(n * N))"))
    end
    # A species labelled with a stratum is seeded on the nodes of that type; a shared species (no
    # stratum) on the free nodes of every type (§J.6, as NetworkOutbreaks places it), so it counts
    # against the whole population.
    load = Dict{Symbol,Float64}()
    shared = 0.0
    for (X, ρ) in initial.fractions
        a = haskey(cm.labels, X) ? cm.labels[X].stratum : :all
        if a === :all
            shared += ρ
            continue
        end
        a in net.types || throw(ArgumentError(
            "$(where): the seeded species $(X) belongs to the stratum $(a), which is not a node " *
            "type of the MultitypeNetwork (types $(_list(net.types)))"))
        load[a] = get(load, a, 0.0) + ρ
    end
    for (a, n) in zip(net.types, net.sizes)
        get(load, a, 0.0) <= n + 1e-12 || throw(ArgumentError(
            "$(where): the seeds of the node type $(a) ($(load[a]) of all nodes) exceed its size $(n)"))
    end
    free = sum(net.sizes) - sum(values(load); init = 0.0)
    shared <= free + 1e-12 || throw(ArgumentError(
        "$(where): the seeds of the species without a stratum ($(shared) of all nodes) exceed " *
        "the nodes left by the stratum seeds ($(free))"))
    return nothing
end

function _check_backends(cm::ContactModel, net, backends::AbstractDict, where)
    out = Dict{Symbol,Symbol}()
    rep = admissibility(cm, net)
    for (k, v) in backends
        key, verdict = Symbol(k), Symbol(v)
        haskey(SCENARIO_BACKENDS, key) || throw(ArgumentError(
            "$(where): unknown back end :$(key); expected one of $(keys(SCENARIO_BACKENDS))"))
        verdict in BACKEND_VERDICTS || throw(ArgumentError(
            "$(where): unknown verdict :$(verdict) for :$(key); expected one of $(BACKEND_VERDICTS)"))
        ok = rep.backends[SCENARIO_BACKENDS[key]]
        if verdict === :inadmissible && ok
            throw(ArgumentError("$(where): the back end :$(key) is declared inadmissible, but " *
                                "admissibility accepts the model on this network"))
        elseif verdict !== :inadmissible && !ok
            throw(ArgumentError("$(where): the back end :$(key) ($(verdict)) does not accept the " *
                                "model on this network (admissibility of " *
                                ":$(SCENARIO_BACKENDS[key]) is false); declare it :inadmissible"))
        end
        out[key] = verdict
    end
    return out
end

function _check_stochastic(cm::ContactModel, net, where)
    is_admissible(cm, :stochastic; network = net) || throw(ArgumentError(
        "$(where): NetworkOutbreaks cannot simulate the model on this network (admissibility of " *
        ":stochastic is false), so it has no reference ensemble"))
    return nothing
end

Base.show(io::IO, sc::Scenario) = print(io, "Scenario(:", sc.id, ")")

function Base.show(io::IO, ::MIME"text/plain", sc::Scenario)
    println(io, "Scenario :", sc.id, " — ", sc.title)
    println(io, "  model        ", sc.model)
    println(io, "  network      ", canonical_text(sc.network))
    println(io, "  params       ", join(("$(k) = $(_fmt_value(sc.params[k]))" for k in sort!(collect(keys(sc.params)))), ", "))
    println(io, "  initial      ", join(("$(X) $(_fmt_value(ρ))" for (X, ρ) in sc.initial.fractions), ", "))
    println(io, "  time         ", first(sc.tgrid), ":", step(sc.tgrid), ":", last(sc.tgrid),
            " (", length(sc.tgrid), " points)")
    println(io, "  observables  ", join(sc.observables, ", "))
    println(io, "  sim          ", sc.sim)
    bk = sort!(collect(sc.backends); by = first)
    println(io, "  backends     ", isempty(bk) ? "none" : join(("$(k) => $(v)" for (k, v) in bk), ", "))
    println(io, "  tags         ", join(sc.tags, ", "))
    ex = sort!(collect(sc.expected); by = first)
    println(io, "  expected     ", isempty(ex) ? "none" :
                                   join(("$(k) = $(_fmt_value(v))" for (k, v) in ex), ", "))
    isempty(sc.notes) || println(io, "  notes        ", sc.notes)
    print(io, "  hash         ", scenario_hash(sc))
end

_fmt_value(x::Real) = @sprintf("%.6g", x)
