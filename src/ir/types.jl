# Owner: WP6 (DESIGN_NetworkEpiCore.md §B.1, §A.2; work package in §G.2).
#
# The intermediate representation (IR) of a network epidemic model: contacts s + J → X + J at a
# per-contact rate and node transitions X → Y | ∅, collected in a validated `ContactModel`.
# Rate validation and evaluation live in ir/rates.jl, typing in ir/typing.jl; functions from
# those files are called from bodies here (they are resolved at run time).
#
# Never export: `Transition`, `exit`, `Node` (§A.2); no `@enum` (types are Symbols).

export RATE_OPS
export Contact, NodeTransition, SpeciesLabel, Provenance
export RateConvention, PerContact, FrequencyDependent, DensityDependent
export ContactModel
export species_names, susceptible_species, infectious_species, entry_species, infected_species
export contacts, node_transitions, rate_convention, species_labels, parameter_defaults,
       provenance

"""
    RATE_OPS

The operators an `Expr` rate may use: `(:+, :-, :*, :/, :^, :exp, :log, :min, :max)`.

A rate is a `Real`, a `Symbol` (a parameter name), an arithmetic `Expr` over `RATE_OPS` with
`Real` and `Symbol` leaves (`:t` is time, for the ODE back ends only), or a species-free
symbolic expression (Symbolics). A Julia `Function` is rejected: it cannot be lowered, hashed or
run in NetworkOutbreaks.
"""
const RATE_OPS = (:+, :-, :*, :/, :^, :exp, :log, :min, :max)

# ---------------------------------------------------------------------------------------------
# Reactions
# ---------------------------------------------------------------------------------------------

"""
    Contact(s, J, X, τ; layer = :all, name)

A contact reaction `s + J → X + J`: a node in state `s` (the recipient) that shares an edge with
a node in state `J` (the infector) moves to state `X` at the **per-contact** rate `τ`, and `J`
is unchanged (it is catalytic). `X` may equal `J` (as in `S + I → 2I`); branching at infection is
several contacts sharing `(s, J)`; a contact whose product is not infectious (contact tracing
`S + D → Q + D`) is still a contact.

- `τ` is a rate (see [`RATE_OPS`](@ref)) read through the model's [`RateConvention`](@ref).
- `layer = :all` acts on every layer of a `MultiplexNetwork`; otherwise only on the named layer.
- `name` defaults to `Symbol(s, :_, J, :_to_, X)`, with `_<layer>` appended when the layer is
  not `:all`.

The constructor requires `s ≠ J` and `s ≠ X`, and validates the rate.
"""
struct Contact
    recipient::Symbol
    infector::Symbol
    product::Symbol
    rate::Any
    layer::Symbol
    name::Symbol
    function Contact(s::Symbol, J::Symbol, X::Symbol, rate, layer::Symbol, name::Symbol)
        s === J && throw(ArgumentError("contact `$(name)`: the recipient $(s) cannot be its own " *
                                       "infector (a contact is s + J → X + J with s ≠ J)"))
        s === X && throw(ArgumentError("contact `$(name)`: the product equals the recipient " *
                                       "$(s), so the reaction does nothing"))
        return new(s, J, X, _checkrate(rate, name), layer, name)
    end
end

function Contact(s::Symbol, J::Symbol, X::Symbol, τ; layer::Symbol = :all,
                 name::Symbol = _default_contact_name(s, J, X, layer))
    return Contact(s, J, X, τ, layer, name)
end

_default_contact_name(s, J, X, layer) =
    layer === :all ? Symbol(s, :_, J, :_to_, X) : Symbol(s, :_, J, :_to_, X, :_, layer)

"""
    NodeTransition(X, Y, a; name)
    NodeTransition(X, nothing, a; name)

A node-local transition `X → Y` at per-capita rate `a`, or a removal `X → ∅` when `Y` is
`nothing` (the node becomes inert and absorbing). The back ends lower a removal, and an exit
`s → ∅`, to an auto-added absorbing sink species `:removed` (§J.2), as NetworkOutbreaks does and
as the Lean syntax represents it; with the sink, the conservation laws θ = φ_S + Σφ_X and
S + Σpop = 1 of the edge-based model hold. `name` defaults to `Symbol(X, :_to_, Y)` (with `∅` for
a removal). The constructor requires `X ≠ Y` and validates the rate.
"""
struct NodeTransition
    from::Symbol
    to::Union{Symbol,Nothing}
    rate::Any
    name::Symbol
    function NodeTransition(X::Symbol, Y::Union{Symbol,Nothing}, rate, name::Symbol)
        X === Y && throw(ArgumentError("transition `$(name)`: $(X) → $(X) does nothing"))
        return new(X, Y, _checkrate(rate, name), name)
    end
end

function NodeTransition(X::Symbol, Y::Union{Symbol,Nothing}, a;
                        name::Symbol = Symbol(X, :_to_, something(Y, :∅)))
    return NodeTransition(X, Y, a, name)
end

# Structural equality (rates compared with `isequal`, so Expr rates compare by value).
Base.:(==)(a::Contact, b::Contact) =
    a.recipient === b.recipient && a.infector === b.infector && a.product === b.product &&
    a.layer === b.layer && a.name === b.name && isequal(a.rate, b.rate)
Base.hash(c::Contact, h::UInt) =
    hash((c.recipient, c.infector, c.product, c.layer, c.name, c.rate), hash(:Contact, h))
Base.:(==)(a::NodeTransition, b::NodeTransition) =
    a.from === b.from && a.to === b.to && a.name === b.name && isequal(a.rate, b.rate)
Base.hash(t::NodeTransition, h::UInt) =
    hash((t.from, t.to, t.name, t.rate), hash(:NodeTransition, h))

_shape(c::Contact) = (c.recipient, c.infector, c.product, c.layer)
_shape(t::NodeTransition) = (t.from, t.to)
_species_of(c::Contact) = (c.recipient, c.infector, c.product)
_species_of(t::NodeTransition) = t.to === nothing ? (t.from,) : (t.from, t.to)
_with_rate(c::Contact, r) = Contact(c.recipient, c.infector, c.product, r, c.layer, c.name)
_with_rate(t::NodeTransition, r) = NodeTransition(t.from, t.to, r, t.name)
# The reaction with a copy of its rate expression (the constructors copy an Expr rate).
_own_rate(r::Union{Contact,NodeTransition}) = r.rate isa Expr ? _with_rate(r, r.rate) : r

# ---------------------------------------------------------------------------------------------
# Labels, provenance and rate conventions
# ---------------------------------------------------------------------------------------------

"""
    SpeciesLabel(base, stratum, count, stage)
    SpeciesLabel(base; stratum = :all, count = 0, stage = 0)

Parse-free provenance of a refined species: its `base` compartment (`:S` for `:S_y` or `:S_2`),
its `stratum` (`:all` if unstratified), its infection `count` (0 if not reinfection-counted)
and its Erlang `stage` (0 if none). Set by `stratify`, [`erlang_stages`](@ref) and
[`with_reinfection_counting`](@ref), and read by [`base_compartment_of`](@ref) and
[`infection_count_of`](@ref) instead of parsing names.
"""
struct SpeciesLabel
    base::Symbol
    stratum::Symbol
    count::Int
    stage::Int
end
SpeciesLabel(base::Symbol; stratum::Symbol = :all, count::Integer = 0, stage::Integer = 0) =
    SpeciesLabel(base, stratum, count, stage)

"""
    Provenance(source, method, assumptions, reaction_map)
    Provenance(source; method = :explicit, assumptions = String[], reaction_map = Int[])

Where a [`ContactModel`](@ref) came from, printed by `show` as an RN-style audit trail.

- `source`: `:direct`, `:factory`, `:catalyst`, `:mtk`, `:legacy_ebm`, `:legacy_nbm` or
  `:transform`;
- `method`: how reactions were classified (`:explicit`, `:stoichiometry`, `:metadata`,
  `:predicate`, `:flux_pairing`, …);
- `assumptions`: every choice the front end or transform made, in words;
- `reaction_map`: IR reaction `k` (contacts first, then transitions) came from source reaction
  `reaction_map[k]`.
"""
struct Provenance
    source::Symbol
    method::Symbol
    assumptions::Vector{String}
    reaction_map::Vector{Int}
end
Provenance(source::Symbol; method::Symbol = :explicit,
           assumptions::AbstractVector{<:AbstractString} = String[],
           reaction_map::AbstractVector{<:Integer} = Int[]) =
    Provenance(source, method, String.(assumptions), Int.(reaction_map))

"""
    RateConvention

How the written constant of a [`Contact`](@ref) becomes the per-contact rate τ at lift time
([`per_contact_rates`](@ref)), with ⟨k⟩ = `mean_degree(net)`:

- [`PerContact`](@ref): τ = rate (the default);
- [`FrequencyDependent`](@ref): the rate is β of β S I/N on fractions, τ = β/⟨k⟩;
- [`DensityDependent`](@ref)`(N)`: the rate is β of β S I in counts, τ = β N/⟨k⟩.
"""
abstract type RateConvention end

"""
    PerContact()

The written contact rate is the per-contact (per-edge) rate τ. See [`RateConvention`](@ref).
"""
struct PerContact <: RateConvention end

"""
    FrequencyDependent()

The written contact rate is the mass-action β of β S I/N (fractions); τ = β/⟨k⟩ at lift time.
See [`RateConvention`](@ref).
"""
struct FrequencyDependent <: RateConvention end

"""
    DensityDependent(N)

The written contact rate is the mass-action β of β S I in counts, with population size `N` (a
number or a parameter name); τ = β N/⟨k⟩ at lift time. See [`RateConvention`](@ref).
"""
struct DensityDependent{T} <: RateConvention
    N::T
end
Base.:(==)(a::DensityDependent, b::DensityDependent) = isequal(a.N, b.N)
Base.hash(c::DensityDependent, h::UInt) = hash(c.N, hash(:DensityDependent, h))

Base.show(io::IO, ::PerContact) = print(io, "PerContact()")
Base.show(io::IO, ::FrequencyDependent) = print(io, "FrequencyDependent()")
Base.show(io::IO, c::DensityDependent) = print(io, "DensityDependent(", repr(c.N), ")")

# ---------------------------------------------------------------------------------------------
# The model
# ---------------------------------------------------------------------------------------------

"""
    ContactModel(name::Symbol; contacts = Contact[], transitions = NodeTransition[],
                 species = :infer, susceptible = :infer, convention = PerContact(),
                 defaults = Dict{Symbol,Float64}(), labels = Dict{Symbol,SpeciesLabel}(),
                 rate_params = :infer, provenance = nothing, merge_duplicates = false)

The model object shared by every back end: a reaction network whose reactions are
[`Contact`](@ref)s `s + J → X + J` and [`NodeTransition`](@ref)s `X → Y | ∅`.

- `species`: inferred in order of first appearance (a contact `s + J → X + J` is read as s, X,
  J, so SEIR is ordered S, E, I, R), or given (it may contain species that no reaction touches).
  The stored order is **susceptible species first**, then that order.
- `susceptible`: the Sus-typed species Σ. Inferred as the contact recipients that are never a
  contact product; a `Symbol` or vector overrides the inference. The choice is recorded in the
  provenance assumptions. With Σ fixed the typing is unique ([`typing`](@ref)).
- `convention`: the [`RateConvention`](@ref) of the contact rates.
- `defaults`: parameter values by name, and only those: a default named like a species or `t`
  is an `ArgumentError` (initial states come from a `SeedSpec`, never from the model);
  `rate_params`: the parameters, inferred from the rates in order of first appearance.
- `merge_duplicates = true` adds the rates of reactions with the same shape (the additive
  semantics of gluing); otherwise duplicates are an error.

The constructor checks that species are unique, every reaction refers to known species, rates
are valid ([`RATE_OPS`](@ref); numeric rates ≥ 0), reaction names are unique and no two reactions
are identical. So that the back ends can turn names into variables without collisions, no species
may share its name with a rate parameter, no species may be named `t` (time), and the parameter
names `seed_<X>` (the seed fraction of species `X`) are reserved. A symbolic rate may use only
scalar parameters and time `t`: an array element `k[1]`, an array or a function of time `β(t)`
has no parameter name of its own, and is an `ArgumentError`.

Read fields through [`species_names`](@ref), [`susceptible_species`](@ref), [`contacts`](@ref),
[`node_transitions`](@ref), [`rate_parameters`](@ref), [`rate_convention`](@ref),
[`species_labels`](@ref), [`parameter_defaults`](@ref) and [`provenance`](@ref).

```julia
seir = ContactModel(:seir; contacts    = [Contact(:S, :I, :E, :τ)],
                           transitions = [NodeTransition(:E, :I, :σ), NodeTransition(:I, :R, :γ)])
```
"""
struct ContactModel
    name::Symbol
    species::Vector{Symbol}
    susceptible::Vector{Symbol}
    contacts::Vector{Contact}
    transitions::Vector{NodeTransition}
    rate_params::Vector{Any}
    defaults::Dict{Symbol,Float64}
    convention::RateConvention
    labels::Dict{Symbol,SpeciesLabel}
    provenance::Provenance
    function ContactModel(name::Symbol, species::AbstractVector{Symbol},
                          susceptible::AbstractVector{Symbol}, contacts::AbstractVector{Contact},
                          transitions::AbstractVector{NodeTransition}, rate_params::AbstractVector,
                          defaults::AbstractDict, convention::RateConvention,
                          labels::AbstractDict, provenance::Provenance)
        sp = collect(Symbol, species)
        sus = collect(Symbol, susceptible)
        # own copies of the rate expressions (Exprs are mutable), so that no two models, and no
        # caller, share them
        cs = Contact[_own_rate(c) for c in contacts]
        ts = NodeTransition[_own_rate(t) for t in transitions]
        _validate_model(name, sp, sus, cs, ts, labels)
        _validate_names(name, sp, rate_params)
        _validate_symbolic_rates("ContactModel :$(name)",
                                 Any[(r.name, r.rate) for r in Iterators.flatten((cs, ts))],
                                 convention)
        _validate_defaults("ContactModel :$(name)", keys(defaults), sp)
        # species order: susceptible species first (in their given order), then the rest
        known, susset = Set(sp), Set(sus)
        order = vcat(sus, [x for x in sp if !(x in susset)])
        length(order) == length(known) ||
            throw(ArgumentError("ContactModel :$(name): susceptible species must be unique"))
        defs = Dict{Symbol,Float64}(Symbol(k) => Float64(v) for (k, v) in defaults)
        labs = Dict{Symbol,SpeciesLabel}(Symbol(k) => v for (k, v) in labels)
        nr = length(cs) + length(ts)
        pv = provenance
        if length(pv.reaction_map) != nr
            pv = Provenance(pv.source, pv.method, pv.assumptions, collect(1:nr))
        end
        return new(name, order, sus, cs, ts, collect(Any, rate_params), defs, convention, labs, pv)
    end
end

function _validate_model(name, sp, sus, cs, ts, labels)
    where = "ContactModel :$(name)"
    dup = _duplicates(sp)
    isempty(dup) || throw(ArgumentError("$where: species are not unique: $(_list(dup))"))
    known = Set(sp)
    for x in sus
        x in known || throw(ArgumentError("$where: susceptible species $(x) is not a species"))
    end
    for r in Iterators.flatten((cs, ts)), x in _species_of(r)
        x in known || throw(ArgumentError("$where: reaction `$(r.name)` refers to the unknown " *
                                          "species $(x)"))
    end
    names = Symbol[r.name for r in Iterators.flatten((cs, ts))]
    dupn = _duplicates(names)
    isempty(dupn) || throw(ArgumentError("$where: reaction names collide: $(_list(dupn)); " *
                                         "pass `name = …` to the reactions"))
    for group in (cs, ts)
        shapes = Dict{Any,Symbol}()
        for r in group
            s = _shape(r)
            haskey(shapes, s) && throw(ArgumentError(
                "$where: reactions `$(shapes[s])` and `$(r.name)` are identical " *
                "($(_arrow_string(r))); pass merge_duplicates = true to add their rates"))
            shapes[s] = r.name
        end
    end
    for k in keys(labels)
        Symbol(k) in known || throw(ArgumentError("$where: label for the unknown species $(k)"))
    end
    return nothing
end

# Names that would collide once a back end turns species and parameters into variables (E26):
# a species named like a rate parameter, a species named `t` (time), and the seed parameters
# `seed_<X>` that EdgeBasedModels generates for the seed fraction of species X (§A.3).
_seed_parameter_name(X::Symbol) = Symbol(:seed_, X)

function _validate_names(name, sp, rate_params)
    where = "ContactModel :$(name)"
    :t in sp && throw(ArgumentError("$where: a species cannot be named t, which denotes time"))
    pnames = Set(_parameter_name(p) for p in rate_params)
    both = [x for x in sp if x in pnames]
    isempty(both) || throw(ArgumentError(
        "$where: $(_list(both)) is used both as a species and as a rate parameter; rename one"))
    seeds = [_seed_parameter_name(x) for x in sp if _seed_parameter_name(x) in pnames]
    isempty(seeds) || throw(ArgumentError(
        "$where: the parameter name(s) $(_list(seeds)) are reserved for the seed fractions of " *
        "the species (seed_<X>); rename the rate parameter(s)"))
    return nothing
end

# The defaults are parameter values by name (§B.1). A default named like a species or t would
# be an initial state or a time, which a model does not carry (initial states come from a
# SeedSpec), and the reverse maps could not write it, so it is an error rather than ignored.
function _validate_defaults(where, names, species)
    sp = Set{Symbol}(species)
    bad = sort!([Symbol(k) for k in names if Symbol(k) in sp || Symbol(k) === :t])
    isempty(bad) && return nothing
    kinds = [n === :t ? "$(n) (time)" : "$(n) (a species)" for n in bad]
    throw(ArgumentError(
        "$(where): `defaults` are parameter values by name, but $(join(kinds, ", ")) " *
        "$(length(bad) == 1 ? "is" : "are") not a parameter; initial states come from a " *
        "SeedSpec (e.g. SeedFraction(:I => 0.01)), so remove $(length(bad) == 1 ? "it" : "them")"))
end

# A symbolic rate may use only scalar parameters (named by Symbols) and time t (§B.1): an
# element k[1] of an array, an array, or a called variable β(t) has no Symbol name of its own
# that a back end could bind (E25). The check needs the Symbolics extension, which is loaded
# whenever a rate is symbolic.
function _validate_symbolic_rates(where, rates, convention)
    all_rates = copy(rates)
    convention isa DensityDependent && push!(all_rates, (:DensityDependent, convention.N))
    for (rname, r) in all_rates
        (_is_symbolic_rate(r) && applicable(_symbolic_nonscalar_variables, r)) || continue
        bad = _symbolic_nonscalar_variables(r)
        isempty(bad) && continue
        what = rname === :DensityDependent ? "the DensityDependent population size" :
               "the rate of `$(rname)`"
        throw(ArgumentError(
            "$(where): $(what) uses $(join(bad, ", ")); a symbolic rate may use only scalar " *
            "parameters and time t (write k[1] as a scalar parameter such as k1, and a " *
            "time-dependent rate as an expression in t, e.g. β0*exp(-a*t))"))
    end
    return nothing
end

function _duplicates(xs)
    seen = Set{eltype(xs)}()
    dup = eltype(xs)[]
    for x in xs
        x in seen ? (x in dup || push!(dup, x)) : push!(seen, x)
    end
    return dup
end

_list(xs) = join(string.(xs), ", ")

function ContactModel(name::Symbol; contacts::AbstractVector = Contact[],
                      transitions::AbstractVector = NodeTransition[],
                      species = :infer, susceptible = :infer,
                      convention::RateConvention = PerContact(),
                      defaults::AbstractDict = Dict{Symbol,Float64}(),
                      labels::AbstractDict = Dict{Symbol,SpeciesLabel}(),
                      rate_params = :infer, provenance::Union{Nothing,Provenance} = nothing,
                      merge_duplicates::Bool = false)
    cs = collect(Contact, contacts)
    ts = collect(NodeTransition, transitions)
    pv = something(provenance, Provenance(:direct))
    rmap = length(pv.reaction_map) == length(cs) + length(ts) ? copy(pv.reaction_map) :
           collect(1:(length(cs) + length(ts)))
    if merge_duplicates
        cs, ts, rmap = _merge_duplicates(cs, ts, rmap)
    end
    sp = species === :infer ? _infer_species(cs, ts) : collect(Symbol, species)
    assumptions = copy(pv.assumptions)
    if susceptible === :infer
        sus = _infer_susceptible(cs)
        push!(assumptions, "Sus inferred as recipients \\ contact products = {$(_list(sus))}")
    else
        sus = susceptible isa Symbol ? [susceptible] : collect(Symbol, susceptible)
        push!(assumptions, "Sus set by the user = {$(_list(sus))}")
    end
    params = rate_params === :infer ? _infer_rate_params(cs, ts, convention) :
             collect(Any, rate_params)
    prov = Provenance(pv.source, pv.method, assumptions, rmap)
    return ContactModel(name, sp, sus, cs, ts, params, defaults, convention, labels, prov)
end

function _merge_duplicates(cs, ts, rmap)
    nc = length(cs)
    outc, mapc = _merge_group(cs, rmap[1:nc])
    outt, mapt = _merge_group(ts, rmap[(nc + 1):end])
    return outc, outt, vcat(mapc, mapt)
end

function _merge_group(rs::Vector{R}, rmap) where {R}
    out = R[]
    outmap = Int[]
    index = Dict{Any,Int}()
    for (r, k) in zip(rs, rmap)
        s = _shape(r)
        if haskey(index, s)
            i = index[s]
            out[i] = _with_rate(out[i], rate_add(out[i].rate, r.rate))
        else
            push!(out, r)
            push!(outmap, k)
            index[s] = length(out)
        end
    end
    return out, outmap
end

# Order of first appearance, reading a contact s + J → X + J as "s becomes X (through J)", so
# that SEIR is ordered S, E, I, R and SEAIR S, E, I, A, R.
_appearance_order(c::Contact) = (c.recipient, c.product, c.infector)
_appearance_order(t::NodeTransition) = _species_of(t)

function _infer_species(cs, ts)
    sp = Symbol[]
    seen = Set{Symbol}()
    for r in Iterators.flatten((cs, ts)), x in _appearance_order(r)
        x in seen || (push!(sp, x); push!(seen, x))
    end
    return sp
end

function _infer_susceptible(cs)
    products = Set(c.product for c in cs)
    sus = Symbol[]
    for c in cs
        s = c.recipient
        (s in products || s in sus) || push!(sus, s)
    end
    return sus
end

function _infer_rate_params(cs, ts, convention)
    params = Any[]
    seen = Set{Symbol}()
    for r in Iterators.flatten((cs, ts)), p in rate_parameters(r.rate)
        n = _parameter_name(p)
        n in seen || (push!(params, p); push!(seen, n))
    end
    if convention isa DensityDependent
        for p in rate_parameters(convention.N)
            n = _parameter_name(p)
            n in seen || (push!(params, p); push!(seen, n))
        end
    end
    return params
end

# Rebuild a model from parts without re-inferring anything (used by the transforms).
function _rebuild(cm::ContactModel; name = cm.name, species = cm.species,
                  susceptible = cm.susceptible, contacts = cm.contacts,
                  transitions = cm.transitions, rate_params = :infer, defaults = cm.defaults,
                  convention = cm.convention, labels = cm.labels, provenance = cm.provenance)
    cs = collect(Contact, contacts)
    ts = collect(NodeTransition, transitions)
    params = rate_params === :infer ? _infer_rate_params(cs, ts, convention) : rate_params
    return ContactModel(name, species, susceptible, cs, ts, params, defaults, convention,
                        labels, provenance)
end

# Provenance of a transformed model: keeps the audit trail and adds one line.
function _transform_provenance(cm::ContactModel, note::AbstractString, reaction_map)
    src = cm.provenance.source === :transform ? String[] :
          ["transform of a $(cm.provenance.source) model (method $(cm.provenance.method))"]
    return Provenance(:transform, :explicit,
                      vcat(cm.provenance.assumptions, src, [String(note)]),
                      collect(Int, reaction_map))
end

# ---------------------------------------------------------------------------------------------
# Queries
# ---------------------------------------------------------------------------------------------

"""
    species_names(cm::ContactModel) -> Vector{Symbol}

The species of `cm` in model order (susceptible species first). The order is significant for
every back end.
"""
species_names(cm::ContactModel) = copy(cm.species)

"""
    susceptible_species(cm::ContactModel) -> Vector{Symbol}

The Sus-typed species Σ of `cm` (inferred or set by the user; see [`ContactModel`](@ref)).
"""
susceptible_species(cm::ContactModel) = copy(cm.susceptible)

"""
    infectious_species(cm::ContactModel) -> Vector{Symbol}

The distinct infectors `J` of the contacts, in order of first appearance. A tracer (the `D` of
`S + D → Q + D`) is an infector in this sense.
"""
infectious_species(cm::ContactModel) = unique!([c.infector for c in cm.contacts])

"""
    entry_species(cm::ContactModel) -> Vector{Symbol}

The distinct products of the contacts whose recipient is susceptible: the states a node enters
when it leaves Σ through a contact (I for SIR, E for SEIR, I₁ after Erlang staging). This is the
typing-level definition, so it also lists the product of a tracing contact (Q of
S + I → Q + I) and of a contact between susceptible classes (S₂ of S₁ + I → S₂ + I). The
default seeded compartment ([`default_seed_state`](@ref)) is chosen among the entries into
infection only (products in the infection chain, §J.8; see [`infected_species`](@ref)); with
several of those an explicit seeding is required (§E.2).
"""
entry_species(cm::ContactModel) =
    unique!([c.product for c in cm.contacts if c.recipient in cm.susceptible])

"""
    infected_species(cm::ContactModel) -> Vector{Symbol}

The species counted as *infected*, in model order (DESIGN §J.8). Infection status is structural
and decided from the typing; it is the one rule behind the final size and the `:cumulative`
observable of every back end (the edge-based accumulator, the pairwise accumulator ODE and
NetworkOutbreaks' `final_size`):

1. The susceptible classes Σ are the Sus-typed species ([`susceptible_species`](@ref)).
2. The *infection chain* is the set of species from which an infector
   ([`infectious_species`](@ref)) can be reached through node transitions that do not start in
   Σ. An *infection* is a contact from a class in Σ into the chain. A contact whose product is not
   in the chain (tracing `S + D → Q + D`) is not an infection, and neither is a contact whose
   recipient is not in Σ (superinfection `I₁ + I₂ → I₁₂ + I₂`, quarantine of latents
   `E + I → E_q + I`).
3. Every reaction other than an infection preserves infection status. A species is infected if
   it is infectious, or if it lies on a status-preserving path from the product of an infection
   to an infectious species. No class in Σ is infected, and neither is the sink of a removal
   `X → ∅` (the `:removed` compartment of the lowerings).

So E and I of SEIR are infected, E and E_q of the quarantine model are too, and S, R, a
vaccinated V (`S → V`) and a traced Q are not. In the superinfection model the recipient I₁ is
infected, and I₁₂, which never infects, is not. For SIS and SIRS it is `[:I]`; after
[`with_reinfection_counting`](@ref) every infectious I_p.
"""
function infected_species(cm::ContactModel)
    Σ = Set{Symbol}(cm.susceptible)
    inf = Set{Symbol}(infectious_species(cm))
    cs = Tuple{Symbol,Symbol}[(c.recipient, c.product) for c in cm.contacts]
    # a removal X → ∅ leads to the absorbing sink, which is never infected and starts nothing
    ts = Tuple{Symbol,Symbol}[(t.from, t.to) for t in cm.transitions if t.to !== nothing]
    chain = _backward_closure!(copy(inf), ts, Σ)
    infection = Bool[s in Σ && !(x in Σ) && x in chain for (s, x) in cs]
    preserving = vcat([c for (c, f) in zip(cs, infection) if !f], ts)
    fwd = _forward_closure!(Set{Symbol}(x for ((_, x), f) in zip(cs, infection) if f),
                            preserving, Σ)
    bwd = _backward_closure!(copy(inf), preserving, Σ)
    return Symbol[X for X in cm.species if !(X in Σ) && (X in inf || (X in fwd && X in bwd))]
end

# The infection chain (§J.8): the species from which an infector can be reached through node
# transitions that do not start in a susceptible class.
_infection_chain(cm::ContactModel) =
    _backward_closure!(Set{Symbol}(infectious_species(cm)),
                       [(t.from, t.to) for t in cm.transitions if t.to !== nothing],
                       Set{Symbol}(cm.susceptible))

# Is the contact an infection (§J.8): from a susceptible class into the infection chain?
_is_infection(c::Contact, Σ, chain) =
    c.recipient in Σ && !(c.product in Σ) && c.product in chain

# The entries into infection: the distinct products of the infections.
function _infection_entries(cm::ContactModel)
    Σ, chain = Set(cm.susceptible), _infection_chain(cm)
    return unique!(Symbol[c.product for c in cm.contacts if _is_infection(c, Σ, chain)])
end

# Grow `set` backwards (from `to` to `from`) along the (from, to) pairs `rs`, never adding a
# species in `barrier`.
function _backward_closure!(set::Set{Symbol}, rs, barrier::Set{Symbol})
    changed = true
    while changed
        changed = false
        for (from, to) in rs
            (to in set && !(from in set) && !(from in barrier)) || continue
            push!(set, from)
            changed = true
        end
    end
    return set
end

# Grow `set` forwards along the (from, to) pairs `rs`, never entering a species in `barrier`.
function _forward_closure!(set::Set{Symbol}, rs, barrier::Set{Symbol})
    changed = true
    while changed
        changed = false
        for (from, to) in rs
            (from in set && !(to in set) && !(to in barrier)) || continue
            push!(set, to)
            changed = true
        end
    end
    return set
end

"""
    contacts(cm::ContactModel) -> Vector{Contact}

The contact reactions of `cm`, in IR order (reaction indices `1:length(contacts(cm))`). The
vector and the rate expressions are copies: mutating them does not change `cm`.
"""
contacts(cm::ContactModel) = Contact[_own_rate(c) for c in cm.contacts]

"""
    node_transitions(cm::ContactModel) -> Vector{NodeTransition}

The node transitions of `cm`, in IR order (after the contacts in the reaction numbering). The
vector and the rate expressions are copies: mutating them does not change `cm`.
"""
node_transitions(cm::ContactModel) = NodeTransition[_own_rate(t) for t in cm.transitions]

"""
    rate_convention(cm::ContactModel) -> RateConvention

The [`RateConvention`](@ref) of the contact rates of `cm`.
"""
rate_convention(cm::ContactModel) = cm.convention

"""
    species_labels(cm::ContactModel) -> Dict{Symbol,SpeciesLabel}

The [`SpeciesLabel`](@ref)s of the refined species of `cm` (empty unless stratified, staged or
reinfection-counted).
"""
species_labels(cm::ContactModel) = copy(cm.labels)

"""
    parameter_defaults(cm::ContactModel) -> Dict{Symbol,Float64}

Default parameter values of `cm`, by name (from Catalyst/MTK defaults or the user).
[`instantiate`](@ref) uses them for parameters that are not given explicitly.
"""
parameter_defaults(cm::ContactModel) = copy(cm.defaults)

"""
    provenance(cm::ContactModel) -> Provenance

The [`Provenance`](@ref) of `cm`: source, classification method, assumptions and reaction map.
"""
provenance(cm::ContactModel) = cm.provenance

Base.nameof(cm::ContactModel) = cm.name

"""
    contact_model(cm::ContactModel) -> ContactModel

The identity: a `ContactModel` is already in the intermediate representation.
"""
contact_model(cm::ContactModel) = cm

# ---------------------------------------------------------------------------------------------
# Printing
# ---------------------------------------------------------------------------------------------

# RN style, as in the error texts of §B.7: "τ, S + I --> 2I", "γ, I --> R", "μ, I --> ∅".
function _reaction_string(c::Contact)
    rhs = c.product === c.infector ? "2$(c.infector)" : "$(c.product) + $(c.infector)"
    lay = c.layer === :all ? "" : ", [layer = :$(c.layer)]"
    return "$(_rate_string(c.rate)), $(c.recipient) + $(c.infector) --> $(rhs)$(lay)"
end
_reaction_string(t::NodeTransition) =
    "$(_rate_string(t.rate)), $(t.from) --> $(something(t.to, :∅))"

# Arrow style, as in the `show` report of §B.1: "S + I → I + I", "I → R".
_arrow_string(c::Contact) = "$(c.recipient) + $(c.infector) → $(c.product) + $(c.infector)" *
                            (c.layer === :all ? "" : " [$(c.layer)]")
_arrow_string(t::NodeTransition) = "$(t.from) → $(something(t.to, :∅))"

function Base.show(io::IO, c::Contact)
    print(io, "Contact(", repr(c.recipient), ", ", repr(c.infector), ", ", repr(c.product), ", ",
          repr(c.rate))
    c.layer === :all || print(io, "; layer = ", repr(c.layer))
    print(io, ")")
end
Base.show(io::IO, ::MIME"text/plain", c::Contact) =
    print(io, "Contact ", _arrow_string(c), " at ", _rate_string(c.rate))

Base.show(io::IO, t::NodeTransition) =
    print(io, "NodeTransition(", repr(t.from), ", ", repr(t.to), ", ", repr(t.rate), ")")
Base.show(io::IO, ::MIME"text/plain", t::NodeTransition) =
    print(io, "NodeTransition ", _arrow_string(t), " at ", _rate_string(t.rate))

_plural(n, word) = string(n, " ", word, n == 1 ? "" : "s")

Base.show(io::IO, cm::ContactModel) =
    print(io, "ContactModel(:", cm.name, "; ", length(cm.species), " species, ",
          _plural(length(cm.contacts), "contact"), ", ",
          _plural(length(cm.transitions), "transition"), ")")

const _SOURCE_LABELS = Dict(:direct => "ContactModel constructor", :factory => "canned model",
                            :catalyst => "Catalyst.ReactionSystem",
                            :mtk => "ModelingToolkit.System",
                            :legacy_ebm => "EdgeBasedModels legacy type",
                            :legacy_nbm => "NodeBasedModels legacy type",
                            :transform => "transform")

_convention_label(::PerContact) = "PerContact"
_convention_label(::FrequencyDependent) = "FrequencyDependent"
_convention_label(c::DensityDependent) = "DensityDependent($(_rate_string(c.N)))"

# The RN-style typing report (§B.1), the "canonical first cell" output.
function Base.show(io::IO, ::MIME"text/plain", cm::ContactModel)
    pv = cm.provenance
    src = get(_SOURCE_LABELS, pv.source, string(pv.source))
    println(io, "ContactModel :", cm.name, "  (source: ", src, "; method: ", pv.method,
            "; rates: ", _convention_label(cm.convention), ")")
    tp = typing(cm)
    sp = [x in cm.susceptible ? "$(x) (Sus)" : string(x) for x in cm.species]
    print(io, "  species       ", join(sp, "   "))
    rows = Tuple{String,String,String,String,String}[]
    for (k, c) in enumerate(cm.contacts)
        info = c.recipient in cm.susceptible ? "infector $(c.infector), entry $(c.product)" :
               "infector $(c.infector)"
        push!(rows, ("[$k]", _arrow_string(c), _rate_string(c.rate),
                     string(last(tp.reaction_types[k])), info))
    end
    nc = length(cm.contacts)
    for (k, t) in enumerate(cm.transitions)
        push!(rows, ("[$(nc + k)]", _arrow_string(t), _rate_string(t.rate),
                     string(last(tp.reaction_types[nc + k])), ""))
    end
    w = [maximum((textwidth(r[i]) for r in rows); init = 0) for i in 1:4]
    for (k, r) in enumerate(rows)
        head = k == 1 ? "contacts      " : k == nc + 1 ? "transitions   " : "              "
        (k == 1 && nc == 0) && (head = "transitions   ")
        line = string(rpad(r[1], w[1]), " ", rpad(r[2], w[2]), "    ", rpad(r[3], w[3]), "    ",
                      rpad(r[4], w[4]), isempty(r[5]) ? "" : "    " * r[5])
        print(io, "\n  ", head, rstrip(line))
    end
    rep = admissibility(cm)
    marks = join(("$(b) $(rep.backends[b] ? "✓" : "✗")" for b in BACKENDS), "  ")
    theory = tp.theory === :T_EB ? "T_EB" : "T_net"
    print(io, "\n  typing        ", theory, "  ⇒  ", marks)
    for (k, v) in enumerate(rep.violations)
        print(io, "\n  ", k == 1 ? "violations    " : "              ", _violation_summary(cm, v))
    end
    for (k, a) in enumerate(pv.assumptions)
        print(io, "\n  ", k == 1 ? "assumptions   " : "              ", a)
    end
end
