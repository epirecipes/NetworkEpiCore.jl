# Owner: WP8 (DESIGN_NetworkEpiCore.md §B.9, §D.2; work package in §G.2).
#
# Open models and gluing: OpenContactModel, open_model(cm; legs), glue (binary with `on`, n-ary
# with `identify`), disjoint_union, and the OpenContactModel methods of `contact_model` and
# `stratify`.
#
# Semantics (§D.2): an open model is a structured multicospan of exposed species (its legs).
# Gluing is the pushout of the species sets along the identified species, with the reaction lists
# **concatenated**: identical reactions add their rates, so glue(A, A) doubles every rate, unlike
# Catalyst's `extend`, which is a union (F7). disjoint_union is the monoidal product (no
# identification, namespaced). The typing is preserved: an identified species may not be
# susceptible in one part and a non-susceptible contact species in another.
#
# The old EdgeBasedModels `compose` validated neither port names nor port types and dropped the
# wired ports (issue E22); its `tensor` was not closed, not associative and accepted duplicate
# names (E23). Both are replaced by the functions below.
#
# Never export `compose`, `⊗` or `namespace` (§A.2).
#
# Include order: after the whole IR (ir/*.jl).

export OpenContactModel, open_model, glue, disjoint_union

# ---------------------------------------------------------------------------------------------
# OpenContactModel
# ---------------------------------------------------------------------------------------------

"""
    OpenContactModel

An open [`ContactModel`](@ref): a structured multicospan L₁ → Sp(P) ← L₂ … whose legs are sets
of exposed species, along which [`glue`](@ref) identifies species. Build it with
[`open_model`](@ref); `glue` and [`disjoint_union`](@ref) return one.

Public fields:

- `model::ContactModel`: the apex (the closed model);
- `legs::Vector{Vector{Symbol}}`: the exposed species, one vector per leg;
- `inclusions::Vector{Dict{Symbol,Symbol}}`: for a model returned by `glue` or
  `disjoint_union`, the species map from each part (in argument order) into `model`, the cocone
  of the pushout (each map is injective); otherwise ([`open_model`](@ref), `stratify`) the single
  identity map. Back ends use them to push per-part vector fields forward (the open-system
  composition of §D.3, law H1).

The legs are hypergraph-style: every exposed species stays exposed. The result of `glue` has the
legs of all its parts pushed forward, including the legs along which the parts were glued (so
the glued species stays exposed on both of them), and legs accumulate under repeated gluing;
this differs from structured-cospan composition, where the inner legs disappear. Pass
`legs = …` to `glue` to choose the outer boundary. Unitality holds for the apex model, not for
its legs.

Every function that takes a model accepts an `OpenContactModel` through
[`contact_model`](@ref), which returns `model` (so `edge_based(om, net)`, `typing(om)` and
`isequivalent(om, cm)` work).
"""
struct OpenContactModel
    model::ContactModel
    legs::Vector{Vector{Symbol}}
    inclusions::Vector{Dict{Symbol,Symbol}}
    function OpenContactModel(model::ContactModel, legs, inclusions::AbstractVector)
        lg = _validate_legs(model, legs, "open_model(:$(model.name))")
        inc = Dict{Symbol,Symbol}[Dict{Symbol,Symbol}(Symbol(k) => Symbol(v) for (k, v) in d)
                                  for d in inclusions]
        known = Set(model.species)
        for d in inc, v in values(d)
            v in known || throw(ArgumentError(
                "OpenContactModel(:$(model.name)): an inclusion maps to $(v), which is not a " *
                "species of the model"))
        end
        return new(model, lg, inc)
    end
end

OpenContactModel(model::ContactModel, legs) = OpenContactModel(model, legs, [_identity_map(model)])

_identity_map(cm::ContactModel) = Dict{Symbol,Symbol}(x => x for x in cm.species)

# A leg may be given as a Vector of Symbols; `legs` itself may be a single leg (a flat vector of
# Symbols) or a vector of legs.
function _validate_legs(cm::ContactModel, legs, where)
    lg = if legs isa AbstractVector && all(x -> x isa Symbol, legs) && !isempty(legs)
        [collect(Symbol, legs)]
    elseif legs isa AbstractVector && all(x -> x isa AbstractVector, legs)
        [collect(Symbol, l) for l in legs]
    elseif legs isa AbstractVector && isempty(legs)
        Vector{Symbol}[]
    else
        throw(ArgumentError("$(where): legs must be a vector of legs (vectors of species " *
                            "names), or one leg as a vector of species names; got $(repr(legs))"))
    end
    known = Set(cm.species)
    for (k, l) in enumerate(lg)
        unknown = [x for x in l if !(x in known)]
        isempty(unknown) || throw(ArgumentError(
            "$(where): leg $(k) exposes $(_list(unknown)), which " *
            (length(unknown) == 1 ? "is not a species" : "are not species") *
            " of the model (species: $(_list(cm.species)))"))
        dup = _duplicates(l)
        isempty(dup) || throw(ArgumentError("$(where): leg $(k) lists $(_list(dup)) twice"))
    end
    return lg
end

"""
    open_model(cm; legs = [species_names(cm)]) -> OpenContactModel

Expose species of the model `cm` (a [`ContactModel`](@ref), or anything
[`contact_model`](@ref) accepts) on legs, making it an [`OpenContactModel`](@ref) that
[`glue`](@ref) can compose. `legs` is a vector of legs, each a vector of species names (a flat
vector of names is one leg); every exposed name must be a species of `cm`, and a leg may not
list a species twice. The default exposes every species on one leg.

```julia
tr = open_model(ContactModel(:tr; contacts = [Contact(:S, :I, :E, :τ)]); legs = [[:S], [:E, :I]])
pr = open_model(ContactModel(:pr; transitions = [NodeTransition(:E, :I, :σ),
                                                 NodeTransition(:I, :R, :γ)]);
                legs = [[:E, :I, :R]])
seir = glue(tr, pr; on = [:E, :I])       # isequivalent(seir, seir_model())
```
"""
open_model(cm::ContactModel; legs = [species_names(cm)]) = OpenContactModel(cm, legs)
open_model(om::OpenContactModel; legs = om.legs) =
    OpenContactModel(om.model, legs, om.inclusions)
open_model(x; kw...) = open_model(contact_model(x); kw...)

"""
    contact_model(om::OpenContactModel) -> ContactModel

The closed model (the apex `om.model`) of an open model.
"""
contact_model(om::OpenContactModel) = om.model

Base.nameof(om::OpenContactModel) = om.model.name

_legs_string(legs) = "[" * join(("[" * join(string.(l), ", ") * "]" for l in legs), ", ") * "]"

Base.show(io::IO, om::OpenContactModel) =
    print(io, "OpenContactModel(:", om.model.name, "; ", length(om.model.species),
          " species, legs ", _legs_string(om.legs), ")")

function Base.show(io::IO, mime::MIME"text/plain", om::OpenContactModel)
    print(io, "Open")
    show(io, mime, om.model)
    print(io, "\n  legs          ", _legs_string(om.legs))
end

# ---------------------------------------------------------------------------------------------
# glue
# ---------------------------------------------------------------------------------------------

# A part of a gluing: the open model and its namespace (the model name unless given as
# `ns => model`).
_as_part(x::Pair{Symbol}) = (_as_open(last(x)), first(x))
_as_part(x) = (om = _as_open(x); (om, nameof(om)))
_as_open(om::OpenContactModel) = om
_as_open(cm::ContactModel) = open_model(cm)
_as_open(x) = open_model(contact_model(x))

# The type of a species in one part, as far as that part determines it: :sus (a susceptible
# class), :node (a non-susceptible species that takes part in a contact), or :free (a species
# that no contact touches; e.g. the S of a vaccination-only part, which a part without contacts
# cannot type). An identification may not join :sus with :node.
function _part_species_type(cm::ContactModel, x::Symbol)
    x in cm.susceptible && return :sus
    for c in cm.contacts
        (x === c.recipient || x === c.infector || x === c.product) && return :node
    end
    return :free
end

_exposed(om::OpenContactModel) = Set(Iterators.flatten(om.legs))

_part_label(parts, i) = ":$(nameof(parts[i][1]))" * (length(parts) > 2 ? " (part $(i))" : "")

# Union-find over (part, species).
function _uf_find!(parent::Dict{Tuple{Int,Symbol},Tuple{Int,Symbol}}, x)
    root = x
    while parent[root] != root
        root = parent[root]
    end
    while parent[x] != root                  # path compression
        parent[x], x = root, parent[x]
    end
    return root
end

function _check_identified(parts, i, x, where)
    (1 <= i <= length(parts)) || throw(ArgumentError(
        "$(where): part index $(i) is out of range (there are $(length(parts)) parts)"))
    om = parts[i][1]
    x in om.model.species || throw(ArgumentError(
        "$(where): $(x) is not a species of $(_part_label(parts, i)) (species: " *
        "$(_list(om.model.species)))"))
    x in _exposed(om) || throw(ArgumentError(
        "$(where): $(x) is not exposed by a leg of $(_part_label(parts, i)) (legs " *
        "$(_legs_string(om.legs))); expose it with open_model(model; legs = …) before gluing"))
    return (i, x)
end

# The identifications of a binary or n-ary glue, as pairs of (part, species).
function _identifications(parts, on, identify, where)
    n = length(parts)
    ids = Pair{Tuple{Int,Symbol},Tuple{Int,Symbol}}[]
    if on === nothing && identify === nothing
        # default: identify every species name exposed by at least two parts
        counts = Dict{Symbol,Vector{Int}}()
        for (i, (om, _)) in enumerate(parts), x in _exposed(om)
            push!(get!(counts, x, Int[]), i)
        end
        for (x, is) in counts
            length(is) >= 2 || continue
            for j in is[2:end]
                push!(ids, (is[1], x) => (j, x))
            end
        end
    end
    if on !== nothing
        items = on isa Union{Symbol,Pair} ? [on] : collect(on)
        for item in items
            if item isa Pair
                n == 2 || throw(ArgumentError(
                    "$(where): `on = [x => y]` pairs are for two parts; with $(n) parts use " *
                    "identify = [(i, x) => (j, y), …]"))
                push!(ids, _check_identified(parts, 1, Symbol(first(item)), where) =>
                           _check_identified(parts, 2, Symbol(last(item)), where))
            else
                x = Symbol(item)
                is = [i for (i, (om, _)) in enumerate(parts) if x in om.model.species]
                if n == 2
                    for i in 1:2
                        _check_identified(parts, i, x, where)
                    end
                else
                    length(is) >= 2 || throw(ArgumentError(
                        "$(where): $(x) (in `on`) is a species of " *
                        (isempty(is) ? "no part" : "only $(_part_label(parts, only(is)))") *
                        "; an identified species must be in at least two parts"))
                    for i in is
                        _check_identified(parts, i, x, where)
                    end
                end
                for j in is[2:end]
                    push!(ids, (is[1], x) => (j, x))
                end
            end
        end
    end
    if identify !== nothing
        items = identify isa Pair ? [identify] : collect(identify)
        for item in items
            (item isa Pair && first(item) isa Tuple && last(item) isa Tuple &&
             length(first(item)) == 2 && length(last(item)) == 2) || throw(ArgumentError(
                "$(where): identify entries are (i, :X) => (j, :Y) (part index, species); " *
                "got $(repr(item))"))
            (i, x), (j, y) = first(item), last(item)
            push!(ids, _check_identified(parts, Int(i), Symbol(x), where) =>
                       _check_identified(parts, Int(j), Symbol(y), where))
        end
    end
    return ids
end

# The rate of merged identical reactions: k copies of the same rate are k·rate (so glue(A, A)
# reads 2τ), otherwise the sum.
function _summed_rate(rates::Vector)
    length(rates) == 1 && return rates[1]
    all(r -> isequal(r, rates[1]), rates) && return rate_mul(length(rates), rates[1])
    return reduce(rate_add, rates)
end

# Concatenate reactions, merging identical ones (same shape) with their rates added.
function _concatenate!(out::Vector{R}, outmap::Vector{Int}, merged::Vector{String},
                       rs::Vector{R}, rmap::Vector{Int}) where {R}
    groups = Dict{Any,Vector{Int}}()
    order = Any[]
    for (k, r) in enumerate(rs)
        s = _shape(r)
        haskey(groups, s) || push!(order, s)
        push!(get!(groups, s, Int[]), k)
    end
    for s in order
        ks = groups[s]
        r = rs[ks[1]]
        if length(ks) > 1
            r = _with_rate(r, _summed_rate(Any[rs[k].rate for k in ks]))
            push!(merged, "$(_arrow_string(r)) ($(length(ks)) copies)")
        end
        push!(out, r)
        push!(outmap, rmap[ks[1]])
    end
    return out
end

function _merge_defaults(parts, where)
    defs = Dict{Symbol,Float64}()
    owner = Dict{Symbol,Int}()
    for (i, (om, _)) in enumerate(parts), (k, v) in om.model.defaults
        if haskey(defs, k) && defs[k] != v
            throw(ArgumentError(
                "$(where): the parts give different default values to the parameter $(k) " *
                "($(defs[k]) in $(_part_label(parts, owner[k])), $(v) in " *
                "$(_part_label(parts, i))); rates are shared by parameter name, so rename the " *
                "parameter in one part or make the defaults agree"))
        end
        defs[k] = v
        haskey(owner, k) || (owner[k] = i)
    end
    return defs
end

function _merge_convention(parts, where)
    with_contacts = [(i, om.model.convention) for (i, (om, _)) in enumerate(parts)
                     if !isempty(om.model.contacts)]
    isempty(with_contacts) && return first(parts)[1].model.convention
    i1, c1 = first(with_contacts)
    for (i, c) in with_contacts
        c == c1 || throw(ArgumentError(
            "$(where): the rate conventions differ ($(_convention_label(c1)) in " *
            "$(_part_label(parts, i1)), $(_convention_label(c)) in $(_part_label(parts, i))); " *
            "a convention acts on every contact, so glue parts with the same convention"))
    end
    return c1
end

# The common machinery of glue and disjoint_union.
function _glue(parts::Vector{<:Tuple{OpenContactModel,Symbol}}, ids;
               namespace::Bool, name::Symbol, legs, strata_labels::Bool, fname::Symbol)
    where = "$(fname)(" * join((":$(nameof(om))" for (om, _) in parts), ", ") * ")"
    n = length(parts)
    if namespace
        dupns = _duplicates([ns for (_, ns) in parts])
        isempty(dupns) || throw(ArgumentError(
            "$(where): the namespaces $(_list(dupns)) are used by more than one part (the " *
            "namespace is the model name unless given); pass distinct namespaces, e.g. " *
            "$(fname)(:a => model, :b => model)"))
    end

    # classes of identified species
    parent = Dict{Tuple{Int,Symbol},Tuple{Int,Symbol}}()
    for (i, (om, _)) in enumerate(parts), x in om.model.species
        parent[(i, x)] = (i, x)
    end
    for (u, v) in ids
        ru, rv = _uf_find!(parent, u), _uf_find!(parent, v)
        ru == rv && continue
        # the root is the member of the earliest part (a valid class has one member per part)
        isless(ru, rv) ? (parent[rv] = ru) : (parent[ru] = rv)
    end
    members = Dict{Tuple{Int,Symbol},Vector{Tuple{Int,Symbol}}}()
    roots = Tuple{Int,Symbol}[]
    for (i, (om, _)) in enumerate(parts), x in om.model.species
        r = _uf_find!(parent, (i, x))
        haskey(members, r) || push!(roots, r)
        push!(get!(members, r, Tuple{Int,Symbol}[]), (i, x))
    end

    # each class: at most one species per part, and a consistent type
    for r in roots
        ms = members[r]
        length(ms) == 1 && continue
        is = first.(ms)
        dup = _duplicates(is)
        if !isempty(dup)
            i = first(dup)
            xs = [x for (j, x) in ms if j == i]
            throw(ArgumentError(
                "$(where): the identifications join $(_list(xs)) of $(_part_label(parts, i)); " *
                "gluing identifies species of different parts (merge species within a model " *
                "with relabel)"))
        end
        types = [(i, x, _part_species_type(parts[i][1].model, x)) for (i, x) in ms]
        s = findfirst(t -> t[3] === :sus, types)
        v = findfirst(t -> t[3] === :node, types)
        if s !== nothing && v !== nothing
            (is_, xs_, _), (iv, xv, _) = types[s], types[v]
            throw(ArgumentError(
                "$(where): $(xs_) of $(_part_label(parts, is_)) is susceptible but $(xv) of " *
                "$(_part_label(parts, iv)) is not (it takes part in a contact as an infector " *
                "or product there); gluing must preserve the susceptible class"))
        end
    end

    # names of the classes
    classname = Dict{Tuple{Int,Symbol},Symbol}()
    for r in roots
        (i, x) = r                                   # the first member (in part order)
        single = length(members[r]) == 1
        classname[r] = (namespace && single) ? Symbol(x, :_, parts[i][2]) : x
    end
    byname = Dict{Symbol,Vector{Tuple{Int,Symbol}}}()
    for r in roots
        push!(get!(byname, classname[r], Tuple{Int,Symbol}[]), r)
    end
    for r in roots
        rs = byname[classname[r]]
        length(rs) == 1 && continue
        y = classname[r]
        owners = unique([i for q in rs for (i, _) in members[q]])
        if namespace
            throw(ArgumentError(
                "$(where): namespacing gives the species name $(y) to more than one species " *
                "(of $(join((_part_label(parts, i) for i in owners), " and "))); rename a " *
                "species or choose other namespaces"))
        end
        throw(ArgumentError(
            "$(where): the species $(y) of $(join((_part_label(parts, i) for i in owners), " and ")) " *
            "are not identified; identify them (`on` or `identify`, and expose $(y) on a leg of " *
            "each part) or pass namespace = true"))
    end

    inclusions = Dict{Symbol,Symbol}[]
    for (i, (om, _)) in enumerate(parts)
        push!(inclusions, Dict{Symbol,Symbol}(x => classname[_uf_find!(parent, (i, x))]
                                              for x in om.model.species))
    end
    species = Symbol[classname[r] for r in roots]
    sus = Symbol[classname[r] for r in roots
                 if any(x in parts[i][1].model.susceptible for (i, x) in members[r])]

    # labels: the identified species must agree; disjoint_union types species by part
    labels = Dict{Symbol,SpeciesLabel}()
    for r in roots
        ls = [(i, parts[i][1].model.labels[x]) for (i, x) in members[r]
              if haskey(parts[i][1].model.labels, x)]
        y = classname[r]
        if strata_labels
            (i, x) = r
            l = get(parts[i][1].model.labels, x, nothing)
            ns = parts[i][2]
            labels[y] = l === nothing ? SpeciesLabel(x, ns, 0, 0) :
                        SpeciesLabel(l.base, l.stratum === :all ? ns : Symbol(l.stratum, :_, ns),
                                     l.count, l.stage)
        elseif !isempty(ls)
            l1 = last(first(ls))
            for (i, l) in ls
                l == l1 || throw(ArgumentError(
                    "$(where): the identified species $(y) has different labels in " *
                    "$(_part_label(parts, first(first(ls)))) ($(l1)) and " *
                    "$(_part_label(parts, i)) ($(l))"))
            end
            labels[y] = l1
        end
    end

    # reactions, pushed forward and concatenated; source reactions are numbered by part
    # (each part: contacts, then transitions)
    allc, allcmap, allt, alltmap = Contact[], Int[], NodeTransition[], Int[]
    offset = 0
    for (i, (om, ns)) in enumerate(parts)
        m = inclusions[i]
        cm = om.model
        suffix = namespace ? Symbol(:_, ns) : nothing
        for (k, c) in enumerate(cm.contacts)
            push!(allc, _derived_contact(c, m[c.recipient], m[c.infector], m[c.product], c.rate,
                                         suffix))
            push!(allcmap, offset + k)
        end
        nc = length(cm.contacts)
        for (k, t) in enumerate(cm.transitions)
            Y = t.to === nothing ? nothing : m[t.to]
            push!(allt, _derived_transition(t, m[t.from], Y, t.rate, suffix))
            push!(alltmap, offset + nc + k)
        end
        offset += nc + length(cm.transitions)
    end
    merged = String[]
    cs, cmap = Contact[], Int[]
    _concatenate!(cs, cmap, merged, allc, allcmap)
    ts, tmap = NodeTransition[], Int[]
    _concatenate!(ts, tmap, merged, allt, alltmap)
    cs, ts = _unique_names(cs), _unique_names(ts)

    convention = _merge_convention(parts, where)
    defaults = _merge_defaults(parts, where)
    params = Any[]
    seen = Set{Symbol}()
    for (om, _) in parts, p in om.model.rate_params
        k = _parameter_name(p)
        k in seen || (push!(params, p); push!(seen, k))
    end
    for p in _infer_rate_params(cs, ts, convention)          # e.g. the k of k·τ (numbers only)
        k = _parameter_name(p)
        k in seen || (push!(params, p); push!(seen, k))
    end

    identified = [classname[r] for r in roots if length(members[r]) > 1]
    what = fname === :disjoint_union ?
           "disjoint_union of $(join(("$(nameof(om)) (namespace $(ns))" for (om, ns) in parts), ", ")): " *
           "no identification; species X of part a renamed X_a and labelled with the stratum a" :
           "glue of $(join((":$(nameof(om))" for (om, _) in parts), ", ")) along " *
           (isempty(identified) ? "no species" : _list(identified)) *
           ": pushout of the species; reactions concatenated, the rates of identical reactions " *
           "added" * (namespace ? "; other species namespaced as X_<namespace>" : "")
    assumptions = String[what,
                         "Sus = the union of the parts' susceptible classes = {$(_list(sus))}"]
    isempty(merged) || push!(assumptions, "identical reactions merged: " * join(merged, "; "))
    for (om, ns) in parts, a in om.model.provenance.assumptions
        push!(assumptions, "$(ns): $(a)")
    end
    pv = Provenance(:transform, :explicit, assumptions, vcat(cmap, tmap))
    model = ContactModel(name, species, sus, cs, ts, params, defaults, convention, labels, pv)

    outlegs = legs === nothing ?
              [Symbol[inclusions[i][x] for x in l] for (i, (om, _)) in enumerate(parts)
               for l in om.legs] : legs
    return OpenContactModel(model, outlegs, inclusions)
end

"""
    glue(A, B; on = <shared exposed names>, namespace = false, name, legs) -> OpenContactModel
    glue(ms...; identify = [(i, :X) => (j, :Y), …], on, namespace = false, name, legs)

Compose open models along identified species: the **pushout** of the species sets with the
reaction lists **concatenated** (§D.2). The parts are [`OpenContactModel`](@ref)s, or
`ContactModel`s (every species exposed), or anything [`contact_model`](@ref) accepts; a part
may be given as `namespace => model`.

- **Identification.** `on` lists species names identified between the parts (by default every
  name exposed on a leg of at least two parts); for two parts it may also hold pairs `x => y`
  identifying A's `x` with B's `y`. `identify` gives n-ary identifications `(i, :X) => (j, :Y)`
  between part `i`'s `X` and part `j`'s `Y`. Every identified species must be **exposed on a
  leg** of its part, and a class of identified species has at most one species per part. An
  identified class takes the name of its member in the earliest part.
- **Typing.** Identified species must have compatible types: a species that is susceptible in
  one part cannot be joined to one that is a contact infector or product in another (a species
  that no contact of its part touches, such as the S of a vaccination-only part, takes the type
  of the other side). The susceptible classes of the result are the union of the parts'.
- **Reactions.** The reactions of all parts are pushed forward and concatenated; reactions that
  become identical are merged with their **rates added**, so `glue(A, A)` doubles every rate
  (Catalyst's `extend(A, A) == A` is a union instead, F7). Rate parameters are shared by name
  (a rate `τ` in two parts is one parameter) and parameter defaults must agree; parts with
  contacts must have the same rate convention.
- **Clashes.** Two species with the same name that are not identified are an error, unless
  `namespace = true`, which renames every non-identified species `X` of part `i` to
  `X_<namespace_i>` (the model name unless given as `namespace => model`).
- **Result.** An `OpenContactModel` whose legs are, by default, the parts' legs pushed forward
  (pass `legs` to choose), with `inclusions` holding each part's species map. The default model
  name joins the part names with `_`.

Laws: `glue` is associative and unital up to relabelling (the unit is a model with no reactions
exposing the glued species on two legs, or the empty model), symmetric up to relabelling, and
commutes with the rate conventions, `scale_contact_rates` and `stratify`; the mass-action vector
field of the result is the sum of the parts' fields pushed forward along `inclusions` (H1′),
all tested in NetworkEpiCore. The same law for the edge-based lift (H1, strict because the
per-reaction lift is local) is tested by EdgeBasedModels; the pairwise models are only lax
(F2), so compose the syntax first, then lift.

```julia
tr = open_model(ContactModel(:tr; contacts = [Contact(:S, :I, :E, :τ)]); legs = [[:S], [:E, :I]])
pr = open_model(ContactModel(:pr; transitions = [NodeTransition(:E, :I, :σ),
                                                 NodeTransition(:I, :R, :γ)]); legs = [[:E, :I, :R]])
seir = glue(tr, pr; on = [:E, :I])                   # isequivalent(seir, seir_model())
sirv = glue(sir_model(), ContactModel(:vax; transitions = [NodeTransition(:S, :V, :ν)]))
```
"""
function glue(ms...; on = nothing, identify = nothing, namespace::Bool = false,
              name::Union{Nothing,Symbol} = nothing, legs = nothing)
    isempty(ms) && throw(ArgumentError("glue needs at least one model"))
    parts = Tuple{OpenContactModel,Symbol}[_as_part(m) for m in ms]
    where = "glue(" * join((":$(nameof(om))" for (om, _) in parts), ", ") * ")"
    ids = _identifications(parts, on, identify, where)
    nm = something(name, Symbol(join((nameof(om) for (om, _) in parts), "_")))
    return _glue(parts, ids; namespace, name = nm, legs, strata_labels = false, fname = :glue)
end

"""
    disjoint_union(ms...; name) -> OpenContactModel

The monoidal product of open models: [`glue`](@ref) with no identification, namespaced. Every
species `X` of part `i` becomes `X_<namespace_i>` (the namespace is the model name, or `ns` for a
part given as `ns => model`; namespaces must be distinct), and is labelled with the stratum
`namespace_i` (or `<stratum>_<namespace_i>` if it is already stratified), so the result is
typed over the parts: the edge-based model accepts it on a `MultitypeNetwork` whose node types
are the namespaces and whose cross blocks are zero (law H8, block diagonal). Rate parameters are
shared by name, as in `glue`.

```julia
two = disjoint_union(:city => sir_model(τ = :τc), :rural => sir_model(τ = :τr))
species_names(two.model)      # [:S_city, :S_rural, :I_city, :R_city, :I_rural, :R_rural]
```
"""
function disjoint_union(ms...; name::Union{Nothing,Symbol} = nothing)
    isempty(ms) && throw(ArgumentError("disjoint_union needs at least one model"))
    parts = Tuple{OpenContactModel,Symbol}[_as_part(m) for m in ms]
    nm = something(name, Symbol(join((ns for (_, ns) in parts), "_")))
    return _glue(parts, Pair{Tuple{Int,Symbol},Tuple{Int,Symbol}}[]; namespace = true,
                 name = nm, legs = nothing, strata_labels = true, fname = :disjoint_union)
end

# ---------------------------------------------------------------------------------------------
# stratify an open model
# ---------------------------------------------------------------------------------------------

"""
    stratify(om::OpenContactModel, st; kw...) -> OpenContactModel

Stratify the apex of an open model (see `stratify(::ContactModel, ::Strata)`); each exposed
species `X` is replaced on its leg by all its strata `X_a`.
"""
function stratify(om::OpenContactModel, st::Strata; kw...)
    m = stratify(om.model, st; kw...)
    K = length(st)
    legs = [Symbol[_strat_name(x, a, K) for x in l for a in st.names] for l in om.legs]
    return OpenContactModel(m, legs)
end
stratify(om::OpenContactModel, names::AbstractVector{Symbol}; kw...) =
    stratify(om, strata(names); kw...)
