# Owner: WP6 (DESIGN_NetworkEpiCore.md §B.2, §B.7; work package in §G.2).
#
# Typing of a ContactModel over the type theory T_net (eight transition types) and its
# sub-theory T_EB = {contact, exit, progress, remove} (no arrow into Sus), and the admissibility
# of each back end. The error texts of §B.7 are produced here, verbatim.

export typing, Typing, Violation, blocked_backends
export admissibility, AdmissibilityReport, is_admissible, require_admissible, AdmissibilityError

"""
    SPECIES_TYPES

The two species types: `:sus` (a susceptible class, in Σ) and `:node` (every other species).
"""
const SPECIES_TYPES = (:sus, :node)

"""
    REACTION_TYPES

The eight transition types of the theory T_net (Σ is the susceptible set):

| type | shape | example |
|---|---|---|
| `:contact` | contact with s ∈ Σ, J ∉ Σ, X ∉ Σ | S + I → 2I; tracing S + D → Q + D |
| `:exit` | transition X ∈ Σ → Y ∉ Σ or ∅ | vaccination S → V |
| `:progress` | transition X ∉ Σ → Y ∉ Σ | E → I, I → R |
| `:remove` | transition X ∉ Σ → ∅ | I → ∅ |
| `:resus` | transition X ∉ Σ → Y ∈ Σ | I → S (SIS), R → S (SIRS) |
| `:sus_move` | transition X ∈ Σ → Y ∈ Σ | S₁ → S₂ |
| `:sus_contact` | contact with X ∈ Σ or J ∈ Σ | S₁ + I → S₂ + I |
| `:node_contact` | contact with s ∉ Σ | I + S → R + S |

See [`T_EB_TYPES`](@ref).
"""
const REACTION_TYPES = (:contact, :exit, :progress, :remove, :resus, :sus_move, :sus_contact,
                        :node_contact)

"""
    T_EB_TYPES

The transition types of the sub-theory T_EB ⊂ T_net: `(:contact, :exit, :progress, :remove)`,
the types with no arrow into a susceptible class. The edge-based model and the S-anchored
pairwise model are defined on T_EB models only.
"""
const T_EB_TYPES = (:contact, :exit, :progress, :remove)

"""
    BACKENDS

The back ends whose admissibility [`admissibility`](@ref) reports: `:edge_based` (EBM),
`:s_anchored` (the S-anchored pairwise subsystem), `:pairwise`, `:individual` and `:pair`
(NBM), `:stochastic` (NetworkOutbreaks) and `:mass_action`.
"""
const BACKENDS = (:edge_based, :s_anchored, :pairwise, :individual, :pair, :stochastic,
                  :mass_action)

"""
    VIOLATION_TYPES

The kinds of [`Violation`](@ref): the four non-T_EB reaction types (`:resus`, `:sus_move`,
`:sus_contact`, `:node_contact`), `:multiple_sus` (not exactly one susceptible class per node
type), `:no_susceptible`, `:explicit_graph` (the edge-based model needs a random-graph
ensemble), `:time_dependent` (NetworkOutbreaks needs constant rates) and `:layer` (a contact on
a layer the network does not have).
"""
const VIOLATION_TYPES = (:resus, :sus_move, :sus_contact, :node_contact, :multiple_sus,
                         :no_susceptible, :explicit_graph, :time_dependent, :layer)

const _EB_BACKENDS = (:edge_based, :s_anchored)
const _NETWORK_BACKENDS = (:edge_based, :s_anchored, :pairwise, :individual, :pair, :stochastic)

"""
    Violation(reaction, type, reason, suggestion[, species])

Why a model is not admissible for some back ends: the offending `reaction` (its name, or
`nothing` for a model-level violation), the violation `type` (one of
[`VIOLATION_TYPES`](@ref)), a `reason` and a `suggestion` in words, and the susceptible
`species` concerned (or `nothing`). [`blocked_backends`](@ref) lists the back ends it rules out.
"""
struct Violation
    reaction::Union{Symbol,Nothing}
    type::Symbol
    reason::String
    suggestion::String
    species::Union{Symbol,Nothing}
    function Violation(reaction, type::Symbol, reason::AbstractString,
                       suggestion::AbstractString, species = nothing)
        type in VIOLATION_TYPES || throw(ArgumentError(
            "unknown violation type :$(type); expected one of $(VIOLATION_TYPES)"))
        return new(reaction, type, String(reason), String(suggestion), species)
    end
end

"""
    blocked_backends(v::Violation) -> Tuple

The back ends (see [`BACKENDS`](@ref)) that the violation `v` rules out: a reaction outside T_EB,
`:multiple_sus` and `:no_susceptible` rule out `:edge_based` and `:s_anchored`;
`:explicit_graph` rules out `:edge_based`; `:time_dependent` rules out `:stochastic`; `:layer`
rules out every network back end.
"""
function blocked_backends(v::Violation)
    v.type === :explicit_graph && return (:edge_based,)
    v.type === :time_dependent && return (:stochastic,)
    v.type === :layer && return _NETWORK_BACKENDS
    return _EB_BACKENDS
end

"""
    Typing

The typing of a [`ContactModel`](@ref) (see [`typing`](@ref)):

- `species_types::Dict{Symbol,Symbol}`: `:sus` or `:node` per species;
- `reaction_types::Vector{Pair{Symbol,Symbol}}`: reaction name ⇒ transition type (one of
  [`REACTION_TYPES`](@ref)), in IR order (contacts, then transitions);
- `theory`: `:T_EB` if every reaction type is in [`T_EB_TYPES`](@ref), else `:T_net`;
- `violations`: one [`Violation`](@ref) per reaction outside T_EB.
"""
struct Typing
    species_types::Dict{Symbol,Symbol}
    reaction_types::Vector{Pair{Symbol,Symbol}}
    theory::Symbol
    violations::Vector{Violation}
end

"""
    AdmissibilityReport

The result of [`admissibility`](@ref): `backends::Dict{Symbol,Bool}` (one entry per back end in
[`BACKENDS`](@ref)) and every `violations::Vector{Violation}` found.
"""
struct AdmissibilityReport
    backends::Dict{Symbol,Bool}
    violations::Vector{Violation}
end

# ---------------------------------------------------------------------------------------------
# Typing
# ---------------------------------------------------------------------------------------------

function _reaction_type(c::Contact, Σ)
    c.recipient in Σ || return :node_contact
    (c.product in Σ || c.infector in Σ) && return :sus_contact
    return :contact
end
function _reaction_type(t::NodeTransition, Σ)
    if t.from in Σ
        return (t.to !== nothing && t.to in Σ) ? :sus_move : :exit
    end
    t.to === nothing && return :remove
    return t.to in Σ ? :resus : :progress
end

const _KEELING_HINT = "NodeBasedModels.node_based(model, net; closure = KeelingClosure())"

function _type_violation(r, type, Σ)
    if type === :resus
        return Violation(r.name, type, "produces the susceptible species $(r.to)", _KEELING_HINT,
                         r.to)
    elseif type === :sus_move
        return Violation(r.name, type, "moves a node between the susceptible classes " *
                         "$(r.from) and $(r.to)", _KEELING_HINT, r.to)
    elseif type === :sus_contact
        r.product in Σ &&
            return Violation(r.name, type, "produces the susceptible species $(r.product)",
                             _KEELING_HINT, r.product)
        return Violation(r.name, type, "has the susceptible species $(r.infector) as its infector",
                         _KEELING_HINT, r.infector)
    else # :node_contact
        return Violation(r.name, type, "changes the state of the non-susceptible species " *
                         "$(r.recipient) through a contact", _KEELING_HINT, nothing)
    end
end

"""
    typing(cm) -> Typing

Type every species of `cm` as `:sus` (in the susceptible set Σ) or `:node`, and every reaction
with one of the eight transition types of T_net ([`REACTION_TYPES`](@ref)). With Σ fixed the
typing is unique. The model is typed over T_EB when every reaction type is in
[`T_EB_TYPES`](@ref) (no arrow into Sus); each reaction outside T_EB gives a
[`Violation`](@ref). Typing is not an error: each back end checks its own admissibility
([`admissibility`](@ref)).

Any model description that `contact_model` accepts may be passed.
"""
function typing(cm::ContactModel)
    Σ = Set(cm.susceptible)
    st = Dict{Symbol,Symbol}(x => (x in Σ ? :sus : :node) for x in cm.species)
    rt = Pair{Symbol,Symbol}[]
    vs = Violation[]
    for r in Iterators.flatten((cm.contacts, cm.transitions))
        ty = _reaction_type(r, Σ)
        push!(rt, r.name => ty)
        ty in T_EB_TYPES || push!(vs, _type_violation(r, ty, Σ))
    end
    theory = isempty(vs) ? :T_EB : :T_net
    return Typing(st, rt, theory, vs)
end
typing(x) = typing(contact_model(x))

# ---------------------------------------------------------------------------------------------
# Admissibility
# ---------------------------------------------------------------------------------------------

const _ORDINALS = ("first", "second", "third", "fourth", "fifth", "sixth")
_ordinal(k) = k <= length(_ORDINALS) ? _ORDINALS[k] : "$(k)th"

const _STRATIFY_HINT = "stratify(model, st) on a MultitypeNetwork (sbm_network or unstructured) " *
                       "for strata, or NodeBasedModels.node_based(model, net)"

# The hint on an untyped network also covers heterogeneous susceptibility (several susceptible
# classes sharing the other compartments): label each susceptible class with a stratum and use
# the typed network unstructured(net, st). On a degree-correlated network the node types are the
# degree classes.
const _HETSUS_HINT = "for heterogeneous susceptibility, label each susceptible class with a " *
                     "stratum (SpeciesLabel(:S; stratum = a)) and use unstructured(net, st) " *
                     "(EdgeBasedModels.edge_based(model, net, st)); for strata, " * _STRATIFY_HINT
_untyped_hint(net) = net isa DegreeCorrelatedNetwork ?
    "stratify over the degree classes on MultitypeNetwork(net): with mt = MultitypeNetwork(net), " *
    "stratify(model, strata(mt.types; sizes = mt.sizes)) on mt, or NodeBasedModels.node_based(model, net)" :
    _HETSUS_HINT

# The first contact whose recipient is `s` (the reaction a Sus-level violation is attached to).
function _first_recipient_contact(cm, s)
    k = findfirst(c -> c.recipient === s, cm.contacts)
    return k === nothing ? nothing : cm.contacts[k].name
end

_stratum(cm, x) = haskey(cm.labels, x) ? cm.labels[x].stratum : :all

function _susceptible_violations(cm::ContactModel, net)
    Σ = cm.susceptible
    vs = Violation[]
    if isempty(Σ)
        push!(vs, Violation(nothing, :no_susceptible,
                            "the model has no susceptible class (no contact converts a " *
                            "susceptible node)",
                            "add a contact s + J → X + J whose recipient s is susceptible"))
        return vs
    end
    if _is_multitype(net)
        types = _network_types(net)
        seen = Dict{Symbol,Symbol}()
        for s in Σ
            a = _stratum(cm, s)
            if !(a in types)
                why = a === :all ? "$(s) has no stratum, so it is not assigned to a node type " *
                                   "of the MultitypeNetwork (types $(_list(types)))" :
                      "$(s) belongs to the stratum $(a), which is not a node type of the " *
                      "MultitypeNetwork (types $(_list(types)))"
                push!(vs, Violation(_first_recipient_contact(cm, s), :multiple_sus,
                                    why * " (multiple_sus)", _STRATIFY_HINT, s))
            elseif haskey(seen, a)
                push!(vs, Violation(_first_recipient_contact(cm, s), :multiple_sus,
                                    "$(s) is a second susceptible class of the node type $(a), " *
                                    "after $(seen[a]) (multiple_sus)", _STRATIFY_HINT, s))
            else
                seen[a] = s
            end
        end
        for a in types
            haskey(seen, a) || push!(vs, Violation(nothing, :multiple_sus,
                "no susceptible class is assigned to the node type $(a) (multiple_sus)",
                _STRATIFY_HINT, nothing))
        end
        return vs
    end
    if net === nothing
        # No network yet: the susceptible classes must lie in distinct strata.
        seen = Dict{Symbol,Int}()
        for s in Σ
            a = _stratum(cm, s)
            k = get(seen, a, 0) + 1
            seen[a] = k
            k > 1 && push!(vs, Violation(_first_recipient_contact(cm, s), :multiple_sus,
                                         "$(s) is a $(_ordinal(k)) susceptible class" *
                                         (a === :all ? "" : " of the stratum $(a)") *
                                         " (multiple_sus)", _STRATIFY_HINT, s))
        end
        return vs
    end
    # An untyped network has one node type: exactly one susceptible class.
    for (k, s) in enumerate(Σ)
        k == 1 && continue
        push!(vs, Violation(_first_recipient_contact(cm, s), :multiple_sus,
                            "$(s) is a $(_ordinal(k)) susceptible class (multiple_sus)",
                            _untyped_hint(net), s))
    end
    return vs
end

# Node types of a MultitypeNetwork.
_network_types(net) = collect(Symbol, net.types)

function _network_violations(cm::ContactModel, net)
    vs = Violation[]
    net === nothing && return vs
    if _is_explicit_graph(net)
        push!(vs, Violation(nothing, :explicit_graph,
            "edge-based models need a random-graph ensemble, not the fixed graph of an " *
            "ExplicitGraph",
            "ConfigurationNetwork(EmpiricalDegree(g)) for the annealed approximation, or " *
            "NodeBasedModels.node_based(model, net; level = :individual)"))
    end
    layers = _is_multiplex(net) ? Set(layer_names(net)) : Set{Symbol}()
    for c in cm.contacts
        c.layer === :all && continue
        if !(c.layer in layers)
            why = _is_multiplex(net) ?
                  "is on the layer :$(c.layer), which is not a layer of the network (layers " *
                  "$(_list(sort!(collect(layers)))))" :
                  "is on the layer :$(c.layer), but the network has no layers"
            push!(vs, Violation(c.name, :layer, why,
                                "use a MultiplexNetwork with that layer, or layer = :all"))
        end
    end
    return vs
end

function _time_violations(cm::ContactModel)
    vs = Violation[]
    for r in Iterators.flatten((cm.contacts, cm.transitions))
        _uses_time(r.rate) && push!(vs, Violation(r.name, :time_dependent,
            "has a time-dependent rate; NetworkOutbreaks needs rates that are constant after " *
            "instantiate",
            "use a constant rate and a NetworkOutbreaks intervention (ScheduledRateChange) for " *
            "the time variation"))
    end
    return vs
end

"""
    admissibility(cm, net = nothing) -> AdmissibilityReport

Which back ends ([`BACKENDS`](@ref)) accept the model `cm` on the network descriptor `net`
(`nothing`: no network given yet), with every [`Violation`](@ref):

- `:edge_based` and `:s_anchored` need a T_EB model ([`typing`](@ref)) with exactly one
  susceptible class per node type: one on an untyped network; on a `MultitypeNetwork`, labels
  that map the susceptible classes to distinct strata, one per node type (`:multiple_sus`);
  without a network, the susceptible classes must lie in distinct strata. The edge-based model
  also needs a random-graph ensemble, not an `ExplicitGraph`;
- `:pairwise`, `:individual` and `:pair` accept every IR model (total on T_net);
- `:stochastic` needs rates that are constant after [`instantiate`](@ref);
- `:mass_action` accepts every IR model;
- a contact on a layer the network does not have rules out every network back end.

These are the typing-level verdicts of §B.2 (plus `ExplicitGraph` for the edge-based model).
They do not include the limits of the individual back-end implementations on a descriptor
(§C.3: for example the edge-based lift on a `ClusteredNetwork`, or neighbour exchange for
models beyond SIR/SEIR, and the node-based levels available on each descriptor), which the
back ends check themselves with their own errors; so "accepted" here means admissible in
principle, not implemented for every descriptor.

Any model description that `contact_model` accepts may be passed.
"""
function admissibility(cm::ContactModel, net = nothing)
    vs = copy(typing(cm).violations)
    append!(vs, _susceptible_violations(cm, net))
    append!(vs, _network_violations(cm, net))
    append!(vs, _time_violations(cm))
    ok = Dict{Symbol,Bool}(b => true for b in BACKENDS)
    for v in vs, b in blocked_backends(v)
        ok[b] = false
    end
    return AdmissibilityReport(ok, vs)
end
admissibility(x, net = nothing) = admissibility(contact_model(x), net)

function _check_backend(backend::Symbol)
    backend in BACKENDS ||
        throw(ArgumentError("unknown back end :$(backend); expected one of $(BACKENDS)"))
    return backend
end

"""
    is_admissible(cm, backend::Symbol; network = nothing) -> Bool

Whether the back end `backend` (one of [`BACKENDS`](@ref)) accepts `cm` on `network`; see
[`admissibility`](@ref).
"""
is_admissible(cm, backend::Symbol; network = nothing) =
    admissibility(cm, network).backends[_check_backend(backend)]

"""
    AdmissibilityError(backend, model, network, violations, accepted)

Thrown by [`require_admissible`](@ref) when the back end `backend` does not accept the
[`ContactModel`](@ref) `model` on `network`. It lists the blocking [`Violation`](@ref)s, the
reason from the literature, the back ends that do accept the model (`accepted`) and a
suggestion, as in §B.7 of the design.
"""
struct AdmissibilityError <: Exception
    backend::Symbol
    model::ContactModel
    network::Any
    violations::Vector{Violation}
    accepted::Vector{Symbol}
end

"""
    require_admissible(cm, backend::Symbol; network = nothing) -> nothing

Throw an [`AdmissibilityError`](@ref) unless the back end `backend` accepts `cm` on `network`
(see [`admissibility`](@ref)). Every back end calls it before lowering a model.
"""
function require_admissible(cm::ContactModel, backend::Symbol; network = nothing)
    _check_backend(backend)
    rep = admissibility(cm, network)
    rep.backends[backend] && return nothing
    blocking = [v for v in rep.violations if backend in blocked_backends(v)]
    accepted = [b for b in BACKENDS if rep.backends[b]]
    throw(AdmissibilityError(backend, cm, network, blocking, accepted))
end
require_admissible(x, backend::Symbol; network = nothing) =
    require_admissible(contact_model(x), backend; network)

# ---------------------------------------------------------------------------------------------
# Messages
# ---------------------------------------------------------------------------------------------

function _reaction_by_name(cm::ContactModel, name::Symbol)
    for r in Iterators.flatten((cm.contacts, cm.transitions))
        r.name === name && return r
    end
    return nothing
end

function _type_annotation(r::Contact, Σ, ty)
    a = "type $(ty): $(r.recipient in Σ ? "sus" : "node") → $(r.product in Σ ? "sus" : "node")"
    return r.infector in Σ ? a * ", infector sus" : a
end
_type_annotation(r::NodeTransition, Σ, ty) =
    "type $(ty): $(r.from in Σ ? "sus" : "node") → " *
    (r.to === nothing ? "∅" : r.to in Σ ? "sus" : "node")

_quoted(cm, name) = "`" * _reaction_string(_reaction_by_name(cm, name)) * "`"

const _PRODUCING = (:resus, :sus_move, :sus_contact)

# One sentence per violation. A :multiple_sus sentence absorbs the violations that produce the
# same susceptible class ("R1 is a second susceptible class (multiple_sus) and is produced by
# `γ, I1 --> R1` (resus)."); the absorbed ones are returned in `absorbed`.
function _violation_sentences(cm::ContactModel, vs::Vector{Violation})
    Σ = Set(cm.susceptible)
    absorbed = Set{Int}()
    for (i, v) in enumerate(vs)
        v.type === :multiple_sus && v.species !== nothing || continue
        for (j, w) in enumerate(vs)
            (w.type in _PRODUCING && w.species === v.species && w.reaction !== nothing) &&
                push!(absorbed, j)
        end
    end
    out = String[]
    for (i, v) in enumerate(vs)
        i in absorbed && continue
        push!(out, _violation_sentence(cm, v, vs, Σ))
    end
    return out
end

function _violation_sentence(cm::ContactModel, v::Violation, vs, Σ)
    if v.type in _PRODUCING || v.type === :node_contact
        r = _reaction_by_name(cm, v.reaction)
        return "$(_quoted(cm, v.reaction)) ($(_type_annotation(r, Σ, v.type))) $(v.reason)."
    elseif v.type === :multiple_sus
        producers = [w for w in vs if w.type in _PRODUCING && w.species === v.species &&
                     v.species !== nothing && w.reaction !== nothing]
        tail = isempty(producers) ? "" :
               " and is produced by " *
               join(("$(_quoted(cm, w.reaction)) ($(w.type))" for w in producers), " and ")
        v.reaction === nothing && return uppercasefirst(v.reason) * tail * "."
        return "$(_quoted(cm, v.reaction)): $(v.reason)$(tail)."
    elseif v.reaction === nothing
        return uppercasefirst(v.reason) * "."
    else
        return "$(_quoted(cm, v.reaction)) $(v.reason)."
    end
end

# A short form for `show(::ContactModel)`.
_violation_summary(cm::ContactModel, v::Violation) =
    _violation_sentence(cm, v, Violation[], Set(cm.susceptible))

# A descriptor as it is written: `ConfigurationNetwork(RegularDegree(3))`, without module
# qualification and without the type parameters that the default `show` of a parametric struct
# prints.
_network_label(::ExplicitGraph) = "ExplicitGraph(g)"
function _network_label(net)
    s = sprint(show, net; context = :module => @__MODULE__)
    while true
        t = replace(s, r"\{[^{}]*\}" => "")
        t == s && return s
        s = t
    end
end

function _backend_call(backend::Symbol, name::Symbol, net)
    n = net === nothing ? "" : ", " * _network_label(net)
    backend === :edge_based && return "edge_based(:$(name)$(n))"
    backend === :pairwise && return "node_based(:$(name)$(n))"
    backend in (:s_anchored, :individual, :pair) &&
        return "node_based(:$(name)$(n); level = :$(backend))"
    backend === :stochastic && return "simulate(:$(name)$(n))"
    return "mass_action(:$(name))"
end

function _reason_sentence(backend::Symbol, v::Violation)
    subject = backend === :s_anchored ? "The S-anchored pairwise model" : "The edge-based model"
    if v.type in _PRODUCING
        return "$(subject) is exact only when no reaction produces a susceptible class " *
               "(Miller, Slim & Volz 2012, Part I)."
    elseif v.type === :node_contact
        return "$(subject) is exact only when every contact converts a susceptible node; a " *
               "contact that changes a non-susceptible node breaks edge independence " *
               "(Miller, Slim & Volz 2012, Part I)."
    elseif v.type in (:multiple_sus, :no_susceptible)
        return "$(subject) needs exactly one susceptible class per node type (an untyped " *
               "network has one node type)."
    elseif v.type === :explicit_graph
        return "The edge-based model describes a random-graph ensemble, not one fixed graph."
    elseif v.type === :time_dependent
        return "NetworkOutbreaks simulates with constant rates; time variation is done with " *
               "interventions."
    else # :layer
        return "Layer-labelled contacts need a MultiplexNetwork with those layers."
    end
end

function _accepted_text(accepted::Vector{Symbol}, failing::Symbol, vs = Violation[])
    # A contact on a layer the network does not have rules out every network back end; only the
    # mass-action ODE, which ignores the network and its layers, is left, and it is not a
    # substitute for the layered model.
    if any(v -> v.type === :layer, vs) && all(==(:mass_action), accepted)
        return "No network back end accepts a contact on a layer that the network does not " *
               "have (mass_action ignores the network and its layers, so it is no substitute)."
    end
    parts = String[]
    (:edge_based in accepted && failing !== :edge_based) && push!(parts, "edge_based")
    levels = String[]
    :s_anchored in accepted && push!(levels, "s_anchored")
    :pairwise in accepted && push!(levels, "pairwise")
    :individual in accepted && push!(levels, "individual")
    :pair in accepted && push!(levels, "pair")
    :pairwise in accepted && append!(levels, ("motif", "neighbourhood"))
    isempty(levels) || push!(parts, "node_based ($(join(levels, ", ")))")
    :stochastic in accepted && push!(parts, "simulate")
    :mass_action in accepted && push!(parts, "mass_action")
    isempty(parts) && return "No back end accepts this model on this network."
    return "Back ends that accept this model: $(join(parts, ", "))."
end

# Greedy word wrap of one paragraph: lines of at most `width` columns after the indent.
function _wrap(io::IO, text::AbstractString; width::Int = 80, indent::AbstractString = "  ")
    line = ""
    for w in split(text, ' '; keepempty = false)
        if isempty(line)
            line = w
        elseif textwidth(line) + 1 + textwidth(w) <= width
            line = line * " " * w
        else
            print(io, "\n", indent, line)
            line = w
        end
    end
    isempty(line) || print(io, "\n", indent, line)
    return nothing
end

function Base.showerror(io::IO, e::AdmissibilityError)
    print(io, "AdmissibilityError: ", _backend_call(e.backend, e.model.name, e.network), ":")
    for s in _violation_sentences(e.model, e.violations)
        _wrap(io, s)
    end
    isempty(e.violations) && return nothing
    first_v = first(e.violations)
    _wrap(io, _reason_sentence(e.backend, first_v) * " " *
              _accepted_text(e.accepted, e.backend, e.violations))
    _wrap(io, "Try: " * first_v.suggestion * ".")
    return nothing
end

# ---------------------------------------------------------------------------------------------
# Printing
# ---------------------------------------------------------------------------------------------

Base.show(io::IO, v::Violation) =
    print(io, "Violation(", repr(v.reaction), ", ", repr(v.type), ", ", repr(v.reason), ")")

function Base.show(io::IO, ::MIME"text/plain", t::Typing)
    print(io, "Typing over ", t.theory === :T_EB ? "T_EB" : "T_net", ": ",
          join(("$(n) => $(ty)" for (n, ty) in t.reaction_types), ", "))
    for v in t.violations
        print(io, "\n  ", v.type, ": ", something(v.reaction, :model), " ", v.reason)
    end
end

function Base.show(io::IO, ::MIME"text/plain", r::AdmissibilityReport)
    print(io, "AdmissibilityReport: ",
          join(("$(b) $(r.backends[b] ? "✓" : "✗")" for b in BACKENDS), "  "))
    for v in r.violations
        print(io, "\n  ", v.type, ": ", something(v.reaction, :model), " ", v.reason)
    end
end
