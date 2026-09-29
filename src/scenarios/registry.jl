# Owner: WP12 (DESIGN_NetworkEpiCore.md §E.3, §E.4; work package in §G.2).
#
# The scenario registry: registration, lookup by id, selection by tags, and `derive` (a variant
# of a scenario with a new id and a new hash). The canonical list of §E.3 (scenarios/canonical.jl)
# is built on first access, so that loading NetworkEpiCore never runs the registry computations
# and an error in them cannot break `using NetworkEpiCore`.

export register_scenario!, scenario, scenario_ids, scenarios, derive

const _SCENARIOS = Dict{Symbol,Scenario}()
const _SCENARIO_ORDER = Symbol[]
const _SCENARIO_LOCK = ReentrantLock()
const _CANONICAL_BUILT = Ref(false)

# Build the canonical list once (it is defined in scenarios/canonical.jl).
function _ensure_canonical!()
    _CANONICAL_BUILT[] && return nothing
    lock(_SCENARIO_LOCK) do
        _CANONICAL_BUILT[] && return nothing
        built = _canonical_scenarios()
        for sc in built
            haskey(_SCENARIOS, sc.id) && error("canonical scenario :$(sc.id) is defined twice")
            _SCENARIOS[sc.id] = sc
            push!(_SCENARIO_ORDER, sc.id)
        end
        _CANONICAL_BUILT[] = true
    end
    return nothing
end

"""
    register_scenario!(sc::Scenario; replace = false) -> Scenario

Add `sc` to the scenario registry under `sc.id`, after the canonical scenarios of §E.3. Registering
an id that exists is an error unless `replace = true` (which keeps its position in the listing).
Registered scenarios are returned by [`scenario`](@ref), [`scenario_ids`](@ref) and
[`scenarios`](@ref) for the rest of the session.
"""
function register_scenario!(sc::Scenario; replace::Bool = false)
    _ensure_canonical!()
    lock(_SCENARIO_LOCK) do
        if haskey(_SCENARIOS, sc.id)
            replace || throw(ArgumentError(
                "register_scenario!: a scenario :$(sc.id) is already registered; pass " *
                "replace = true to replace it, or derive a new id"))
        else
            push!(_SCENARIO_ORDER, sc.id)
        end
        _SCENARIOS[sc.id] = sc
    end
    return sc
end

"""
    scenario(id::Symbol) -> Scenario
    scenario(sc::Scenario) -> Scenario

The registered scenario `id` (for example `scenario(:sir_pois5)`: SIR on Poisson(5) with
τ = 1/6, γ = 1/4, 1% seeds in I and t ∈ [0, 60]). An unknown id is an `ArgumentError` that
suggests the closest registered ids. A `Scenario` is returned as is.
"""
function scenario(id::Symbol)
    _ensure_canonical!()
    sc = lock(() -> get(_SCENARIOS, id, nothing), _SCENARIO_LOCK)
    sc === nothing || return sc
    ids = scenario_ids()
    near = sort(ids; by = x -> _edit_distance(string(x), string(id)))[1:min(3, length(ids))]
    throw(ArgumentError("no scenario :$(id) is registered; did you mean " *
                        join((":$(x)" for x in near), ", ", " or ") * "? (scenario_ids() lists them)"))
end
scenario(sc::Scenario) = sc

function _edit_distance(a::AbstractString, b::AbstractString)
    x, y = collect(a), collect(b)
    d = collect(0:length(y))
    for i in eachindex(x)
        prev, d[1] = d[1], i
        for j in eachindex(y)
            cur = d[j + 1]
            d[j + 1] = min(d[j + 1] + 1, d[j] + 1, prev + (x[i] == y[j] ? 0 : 1))
            prev = cur
        end
    end
    return d[end]
end

_has_tags(sc::Scenario, want, exclude) =
    all(t -> t in sc.tags, want) && !any(t -> t in sc.tags, exclude)

"""
    scenario_ids(; tags = (), exclude = ()) -> Vector{Symbol}

The ids of the registered scenarios, in registration order (the order of the table in §E.3,
then derived variants and stretch scenarios, then user registrations), restricted to scenarios
that carry **all** of `tags` and **none** of `exclude`. See [`scenarios`](@ref) for the tags.
"""
function scenario_ids(; tags = (), exclude = ())
    _ensure_canonical!()
    return lock(_SCENARIO_LOCK) do
        Symbol[id for id in _SCENARIO_ORDER if _has_tags(_SCENARIOS[id], tags, exclude)]
    end
end

"""
    scenarios(; tags = (), exclude = ()) -> Vector{Scenario}

The registered scenarios that carry **all** of `tags` and **none** of `exclude`, in registration
order; for example `scenarios(; tags = [:ebm], exclude = [:deferred])` lists what the
EdgeBasedModels vignettes and tests can compare against. Tags of the canonical list:

- `:canonical` (every scenario NetworkEpiCore registers), `:ebm` and `:nbm` (used by the
  EdgeBasedModels and NodeBasedModels vignettes and tests; most scenarios carry both);
- model: `:sir`, `:seir`, `:seair`, `:erlang`, `:twostrain`, `:vaccination`, `:sis`, `:sirs`,
  `:stratified`;
- network: `:configuration`, `:pt` / `:non_pt` (Poisson-type degree distribution or not),
  `:well_mixed`, `:clustered`, `:multitype`, `:multiplex`, `:dynamic`, `:neighbour_exchange`,
  `:degree_correlated`, `:dormant_contacts`, `:mfsh`, `:heterogeneous_susceptibility`
  (susceptibility classes that are the strata of `unstructured(net, st)`, sharing the other
  compartments);
- protocol: `:n_scaling` (run at N = 10³, 10⁴, 10⁵), `:small_seed` (time-aligned),
  `:quenched` (one fixed graph), `:dense_ladder` (Λ1), `:unit_law` (M1/M10), `:derived`
  (made by [`derive`](@ref));
- `:stretch` (a stretch capability, WP36 / Volz SEIR: not used by vignettes until validated),
  with `:clustered_general` or `:multitype_pairwise`;
- `:deferred`: NetworkOutbreaks cannot simulate the scenario yet (its process or graph generator
  is deferred), so it has no committed summary; reference-ensemble generation skips it. No
  registered scenario carries it at present: the joint-degree sampler, the dormant-contact
  process and the fleeting-contact sampler all exist (WP36a–c).
"""
scenarios(; tags = (), exclude = ()) = Scenario[scenario(id) for id in scenario_ids(; tags, exclude)]

# ---------------------------------------------------------------------------------------------
# derive
# ---------------------------------------------------------------------------------------------

const _SIM_KEYS = (:N, :nsims, :graphs, :algorithm, :base_seed, :condition, :align)
const _SCENARIO_KEYS = (:title, :model, :network, :params, :initial, :tspan, :tgrid, :tstep,
                        :observables, :backends, :tags, :expected, :notes, :sim)

"""
    derive(sc::Scenario; id = nothing, replace_params = false, kw...) -> Scenario

A variant of `sc` with some fields changed, a new id and a new [`scenario_hash`](@ref). The
result is not registered (see [`register_scenario!`](@ref)).

Keywords:
- simulation settings `N`, `nsims`, `graphs`, `algorithm`, `base_seed`, `condition`, `align`
  (or a whole `sim`);
- `model`, `network`, `initial`, `tspan`, `tgrid` or `tstep`, `observables`, `title`, `notes`,
  `backends`, `tags`, `expected` (quantity names);
- `params`: merged into `sc.params` (given names override); with `replace_params = true` it
  replaces them.

A new `model` or `network` must come with `backends` and `tags` (an `ArgumentError`
otherwise): the back-end verdicts (`:exact_limit`, `:biased`, …) and descriptive tags (`:pt`,
`:configuration`, …) of `sc` are statements about its model on its network, and would be false
for another one (a non-Poisson-type network makes constant-K pairwise `:biased`). Pass
`backends = sc.backends, tags = sc.tags` to keep them deliberately.

A new `tspan` keeps the grid step unless `tgrid` or `tstep` is given; a new `model` resets the
observables to its species, `:infectious` and `:cumulative` unless `observables` is given. The
expected values are recomputed by NetworkEpiCore for the same quantities (never copied), and the
tag `:derived` is added unless `tags` is given. The default id appends `_N<N>_nsims<nsims>`-style parts when only
simulation sizes, graphs, algorithm or seed change, and `_d<first 8 hex digits of the new hash>`
otherwise, for example `derive(scenario(:sir_pois5); N = 1000, nsims = 2000)` has id
`:sir_pois5_N1000_nsims2000`. A derivation that changes nothing the simulation reads is an error.
"""
function derive(sc::Scenario; id::Union{Nothing,Symbol} = nothing, replace_params::Bool = false,
                kw...)
    given = Dict{Symbol,Any}(kw)
    unknown = [k for k in keys(given) if !(k in _SIM_KEYS || k in _SCENARIO_KEYS)]
    isempty(unknown) || throw(ArgumentError(
        "derive(:$(sc.id)): unknown keyword(s) $(_list(sort!(unknown))); expected " *
        "$(_list(vcat(collect(_SIM_KEYS), collect(_SCENARIO_KEYS))))"))
    haskey(given, :sim) && any(k -> k in _SIM_KEYS, keys(given)) && throw(ArgumentError(
        "derive(:$(sc.id)): pass either `sim` or individual simulation settings, not both"))
    changed = [k for k in (:model, :network) if haskey(given, k)]
    missing_ = [k for k in (:backends, :tags) if !haskey(given, k)]
    (isempty(changed) || isempty(missing_)) || throw(ArgumentError(
        "derive(:$(sc.id)): a new $(join(changed, " and ")) needs $(join(("`$k`" for k in missing_),
        " and ")): the back-end verdicts and tags of :$(sc.id) describe its own model on its own " *
        "network and may be false for the new one; pass them explicitly (backends = " *
        "sc.backends, tags = sc.tags keeps them)"))
    sim = get(given, :sim) do
        s = sc.sim
        SimConfig(; N = get(given, :N, s.N), nsims = get(given, :nsims, s.nsims),
                  graphs = get(given, :graphs, s.graphs), algorithm = get(given, :algorithm, s.algorithm),
                  base_seed = get(given, :base_seed, s.base_seed),
                  condition = get(given, :condition, s.condition), align = get(given, :align, s.align))
    end
    model = contact_model(get(given, :model, sc.model))
    params = if haskey(given, :params)
        replace_params ? Dict{Symbol,Any}(given[:params]) :
        merge(Dict{Symbol,Any}(sc.params), Dict{Symbol,Any}(given[:params]))
    else
        sc.params
    end
    tspan = get(given, :tspan, sc.tspan)
    tgrid = if haskey(given, :tgrid)
        given[:tgrid]
    elseif haskey(given, :tstep) || haskey(given, :tspan)
        _default_tgrid(tspan, get(given, :tstep, step(sc.tgrid)), "derive(:$(sc.id))")
    else
        sc.tgrid
    end
    observables = get(given, :observables) do
        haskey(given, :model) ? _default_observables(model) : sc.observables
    end
    tags = get(given, :tags) do
        :derived in sc.tags ? copy(sc.tags) : vcat(sc.tags, [:derived])
    end
    expected = get(given, :expected, collect(keys(sc.expected)))
    build(newid) = Scenario(newid; title = get(given, :title, sc.title), model,
                            network = get(given, :network, sc.network), params,
                            initial = get(given, :initial, sc.initial), tspan, tgrid, observables,
                            sim, backends = get(given, :backends, sc.backends), tags,
                            expected = _sorted_quantities(expected),
                            notes = get(given, :notes, sc.notes))
    trial = build(sc.id)
    h = scenario_hash(trial)
    h == scenario_hash(sc) && throw(ArgumentError(
        "derive(:$(sc.id)): the derived scenario has the same canonical text as :$(sc.id) " *
        "(nothing the simulation reads changed), so it would share its summary"))
    newid = id === nothing ? _derived_id(sc, given, h) : id
    return newid === sc.id ? trial : build(newid)
end

# Expected quantities in the order of EXPECTED_QUANTITIES (a stable order for printing).
_sorted_quantities(qs) = Symbol[q for q in EXPECTED_QUANTITIES if q in collect(Symbol, qs)] ∪
                         Symbol[q for q in collect(Symbol, qs) if !(q in EXPECTED_QUANTITIES)]

const _READABLE_KEYS = (:N, :nsims, :graphs, :algorithm, :base_seed)

function _derived_id(sc::Scenario, given, h)
    changed = sort!([k for k in keys(given) if !(k in (:title, :notes, :tags, :backends, :expected))];
                    by = k -> something(findfirst(==(k), _READABLE_KEYS), 99))
    if !isempty(changed) && all(k -> k in _READABLE_KEYS, changed)
        parts = String[]
        for k in changed
            v = given[k]
            push!(parts, v isa Tuple ? string(k, "_", join(string.(v), "")) :
                         v isa Symbol ? string(k, "_", v) : string(k, v))
        end
        return Symbol(sc.id, "_", join(parts, "_"))
    end
    return Symbol(sc.id, "_d", first(h, 8))
end
