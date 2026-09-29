# Owner: WP12 (DESIGN_NetworkEpiCore.md §E.4; work package in §G.2).
#
# Canonical text (the `canonical_text` stub of generics.jl) of rates, reactions, models,
# conditioning and alignment rules, `SimConfig` and `Scenario`, and the scenario hash: the
# SHA-256 of the scenario's canonical text. Explicit field names, `%.17g` reals (through the
# helpers of networks/degrees.jl), never `repr` or `Base.hash`, so the text is identical across
# sessions, Julia versions and platforms.

export scenario_hash

"""
    SCENARIO_FORMAT

Version of the canonical scenario text (the first line, `scenario_format = 1`). Bump it whenever
the text of an existing scenario would change for a reason other than its content.
"""
const SCENARIO_FORMAT = 1

# ---------------------------------------------------------------------------------------------
# Rates, reactions, models
# ---------------------------------------------------------------------------------------------

"""
    canonical_text(io::IO, rate::Expr)

Canonical text of an arithmetic rate expression, in prefix form with parameter names as
`:name` and numbers in `%.17g`: `:(3γ)` is `(* 3 :γ)` and `:((1 - p) * σ)` is
`(* (- 1 :p) :σ)`. A `Symbol` rate is `:τ` and a numeric rate its `%.17g` value. Symbolic rates
cannot be hashed and are refused.
"""
function canonical_text(io::IO, ex::Expr)
    (ex.head === :call && !isempty(ex.args) && ex.args[1] isa Symbol) || throw(ArgumentError(
        "canonical_text: rate expressions must be calls of $(RATE_OPS); got $(ex)"))
    print(io, '(', ex.args[1])
    for a in ex.args[2:end]
        print(io, ' ')
        _netct_value(io, a)
    end
    print(io, ')')
    return nothing
end
canonical_text(ex::Expr) = sprint(canonical_text, ex)

canonical_text(io::IO, c::Contact) =
    _netct_struct(io, "Contact", :recipient => c.recipient, :infector => c.infector,
                  :product => c.product, :rate => c.rate, :layer => c.layer)
canonical_text(io::IO, t::NodeTransition) =
    _netct_struct(io, "NodeTransition", :from => t.from, :to => t.to, :rate => t.rate)
canonical_text(io::IO, l::SpeciesLabel) =
    _netct_struct(io, "SpeciesLabel", :base => l.base, :stratum => l.stratum, :count => l.count,
                  :stage => l.stage)
canonical_text(io::IO, ::PerContact) = print(io, "PerContact()")
canonical_text(io::IO, ::FrequencyDependent) = print(io, "FrequencyDependent()")
canonical_text(io::IO, c::DensityDependent) = _netct_struct(io, "DensityDependent", :N => c.N)

"""
    canonical_text(cm::ContactModel) -> String

Canonical text of a model (§E.4), one line: the species in model order, the susceptible species,
the rate convention, the contacts and transitions **in IR order** (their order fixes the random
streams of NetworkOutbreaks) with their rates as canonical text, and the species labels in species
order. The model name, reaction names, defaults and provenance do not enter: they do not change
what any back end computes.
"""
function canonical_text(io::IO, cm::ContactModel)
    labels = Pair{Symbol,SpeciesLabel}[X => cm.labels[X] for X in cm.species if haskey(cm.labels, X)]
    _netct_struct(io, "ContactModel", :species => cm.species, :susceptible => cm.susceptible,
                  :convention => cm.convention, :contacts => cm.contacts,
                  :transitions => cm.transitions, :labels => labels)
    return nothing
end

# ---------------------------------------------------------------------------------------------
# Simulation settings
# ---------------------------------------------------------------------------------------------

canonical_text(io::IO, c::MajorOutbreak) = _netct_struct(io, "MajorOutbreak", :threshold => c.threshold)
canonical_text(io::IO, ::Survival) = print(io, "Survival()")
canonical_text(io::IO, ::Unconditioned) = print(io, "Unconditioned()")
canonical_text(io::IO, ::NoAlignment) = print(io, "NoAlignment()")
canonical_text(io::IO, c::CumulativeCrossing) = _netct_struct(io, "CumulativeCrossing", :level => c.level)

# (field, value) lines of a SimConfig, in field order (sorted by the scenario text).
_sim_fields(s::SimConfig) = (:N => s.N, :nsims => s.nsims, :graphs => s.graphs,
                             :algorithm => s.algorithm, :base_seed => s.base_seed,
                             :condition => s.condition, :align => s.align)

"""
    canonical_text(s::SimConfig) -> String

Canonical text of simulation settings, one line with every field.
"""
canonical_text(io::IO, s::SimConfig) = _netct_struct(io, "SimConfig", _sim_fields(s)...)

canonical_text(x::Union{Contact,NodeTransition,SpeciesLabel,RateConvention,ContactModel,
                        MajorOutbreak,Survival,Unconditioned,NoAlignment,CumulativeCrossing,
                        SimConfig}) = sprint(canonical_text, x)

# ---------------------------------------------------------------------------------------------
# Scenario
# ---------------------------------------------------------------------------------------------

# The time grid as (start, step, length), never as its list of points.
struct _TGridText
    grid::AbstractRange
end
canonical_text(io::IO, g::_TGridText) =
    _netct_struct(io, "StepRangeLen", :start => first(g.grid), :step => step(g.grid),
                  :length => length(g.grid))

"""
    canonical_text(sc::Scenario) -> String

The canonical text of a scenario (§E.4): the versioned header `scenario_format = 1`, then one
`key = value` line per key in sorted order:

- `initial` (the seeding), `model` (see `canonical_text(::ContactModel)`), `network` (the
  descriptor's canonical text), `observables`, `params` (sorted by name);
- `sim.<field>` for every [`SimConfig`](@ref) field;
- `tgrid` (start, step, length) and `tspan`.

Every real number is printed with `%.17g`. The id, title, notes, tags, back ends and expected
values are not part of it, so renaming or annotating a scenario keeps its committed summary; any
change to what the simulation reads changes the text and hence [`scenario_hash`](@ref).
"""
function canonical_text(io::IO, sc::Scenario)
    params = Pair{Symbol,Float64}[k => sc.params[k] for k in sort!(collect(keys(sc.params)); by = string)]
    lines = Pair{String,Any}["initial" => sc.initial, "model" => sc.model, "network" => sc.network,
                             "observables" => sc.observables, "params" => params,
                             "tgrid" => _TGridText(sc.tgrid), "tspan" => sc.tspan]
    for (f, v) in _sim_fields(sc.sim)
        push!(lines, "sim.$(f)" => v)
    end
    sort!(lines; by = first)
    println(io, "scenario_format = ", SCENARIO_FORMAT)
    for (k, v) in lines
        print(io, k, " = ")
        _netct_value(io, v)
        println(io)
    end
    return nothing
end
canonical_text(sc::Scenario) = sprint(canonical_text, sc)

"""
    scenario_hash(sc::Scenario) -> String

The SHA-256 (64 lowercase hex digits) of the canonical text of `sc`
([`canonical_text`](@ref)`(sc)`). Together with NetworkOutbreaks' `ALGORITHM_REVISION` it is
the cache key of the committed reference summaries, whose files are named
`<id>__<first 8 hex digits>` ([`summary_basename`](@ref)). It is identical across sessions,
Julia versions and platforms; [`derive`](@ref) always gives a new hash.
"""
scenario_hash(sc::Scenario) = bytes2hex(SHA.sha256(canonical_text(sc)))
