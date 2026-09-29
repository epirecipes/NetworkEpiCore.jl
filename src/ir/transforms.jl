# Owner: WP6 (DESIGN_NetworkEpiCore.md §B.9, §D.2, §D.5; work package in §G.2).
#
# Syntax-side transforms of a ContactModel (maps of nets over T_net): relabel, erlang_stages,
# with_reinfection_counting (with its lumping map reinfection_totals and the label queries
# base_compartment_of / infection_count_of), and the two reverse-map targets on Poisson networks,
# edge_doubling (D_μ, M2) and rempala_reduction (E_μ, M3).

export relabel, erlang_stages, edge_doubling, rempala_reduction

# A reaction keeps a user-given name (with a suffix when it is copied) and gets a fresh default
# name when its old name was the default one.
_has_default_name(c::Contact) = c.name === _default_contact_name(c.recipient, c.infector,
                                                                   c.product, c.layer)
_has_default_name(t::NodeTransition) = t.name === Symbol(t.from, :_to_, something(t.to, :∅))

function _derived_contact(c::Contact, s, J, X, rate, suffix)
    name = _has_default_name(c) ? _default_contact_name(s, J, X, c.layer) :
           suffix === nothing ? c.name : Symbol(c.name, suffix)
    return Contact(s, J, X, rate, c.layer, name)
end

function _derived_transition(t::NodeTransition, X, Y, rate, suffix)
    name = _has_default_name(t) ? Symbol(X, :_to_, something(Y, :∅)) :
           suffix === nothing ? t.name : Symbol(t.name, suffix)
    return NodeTransition(X, Y, rate, name)
end

# ---------------------------------------------------------------------------------------------
# relabel
# ---------------------------------------------------------------------------------------------

"""
    relabel(cm::ContactModel, f::AbstractDict{Symbol,Symbol}) -> ContactModel

Push `cm` forward along the species map `f` (species not in `f` keep their names): a bijection
renames species; a merge identifies species of the **same type** (susceptible with susceptible,
node with node), and reactions that become identical are merged with their rates added (the
pushforward, so that EB(relabel(P)) = f_* EB(P), Lean `lift_map`). A merge that collapses a
reaction (a contact whose recipient becomes its infector or product, or a transition X → X) is
an error. Labels are kept when the preimages agree.
"""
function relabel(cm::ContactModel, f::AbstractDict)
    fmap = Dict{Symbol,Symbol}(Symbol(k) => Symbol(v) for (k, v) in f)
    for k in keys(fmap)
        k in cm.species || throw(ArgumentError("relabel(:$(cm.name)): $(k) is not a species"))
    end
    m(x::Symbol) = get(fmap, x, x)
    m(::Nothing) = nothing
    Σ = Set(cm.susceptible)
    pre = Dict{Symbol,Vector{Symbol}}()
    for x in cm.species
        push!(get!(pre, m(x), Symbol[]), x)
    end
    for (y, xs) in pre
        length(xs) > 1 || continue
        n_sus = count(in(Σ), xs)
        0 < n_sus < length(xs) && throw(ArgumentError(
            "relabel(:$(cm.name)): $(_list(xs)) ↦ $(y) merges susceptible and non-susceptible " *
            "species; a merge must preserve the susceptible set"))
    end
    species = unique!(Symbol[m(x) for x in cm.species])
    sus = unique!(Symbol[m(x) for x in cm.susceptible])
    cs = Contact[]
    cmap = Int[]
    for (k, c) in enumerate(cm.contacts)
        s, J, X = m(c.recipient), m(c.infector), m(c.product)
        (s === J || s === X) && throw(ArgumentError(
            "relabel(:$(cm.name)): the contact `$(_reaction_string(c))` collapses to " *
            "$(s) + $(J) → $(X) + $(J), which is not a contact"))
        push!(cs, _derived_contact(c, s, J, X, c.rate, nothing))
        push!(cmap, k)
    end
    ts = NodeTransition[]
    tmap = Int[]
    nc = length(cm.contacts)
    for (k, t) in enumerate(cm.transitions)
        X, Y = m(t.from), m(t.to)
        X === Y && throw(ArgumentError("relabel(:$(cm.name)): the transition " *
                                       "`$(_reaction_string(t))` collapses to $(X) → $(X)"))
        push!(ts, _derived_transition(t, X, Y, t.rate, nothing))
        push!(tmap, nc + k)
    end
    cs, ts, rmap = _merge_duplicates(cs, ts, vcat(cmap, tmap))
    cs, ts = _unique_names(cs), _unique_names(ts)
    labels = Dict{Symbol,SpeciesLabel}()
    for (y, xs) in pre
        ls = [get(cm.labels, x, nothing) for x in xs]
        (first(ls) !== nothing && all(==(first(ls)), ls)) && (labels[y] = first(ls))
    end
    note = "relabel: " * join(("$(k) ↦ $(v)" for (k, v) in sort!(collect(fmap))), ", ")
    return _rebuild(cm; species, susceptible = sus, contacts = cs, transitions = ts, labels,
                    provenance = _transform_provenance(cm, note, rmap))
end

# After a merge two different reactions may carry the same (default) name: suffix duplicates.
function _unique_names(rs::Vector{R}) where {R}
    seen = Dict{Symbol,Int}()
    out = R[]
    for r in rs
        k = get(seen, r.name, 0)
        seen[r.name] = k + 1
        if k == 0
            push!(out, r)
        else
            nm = Symbol(r.name, :_, k + 1)
            push!(out, r isa Contact ?
                  Contact(r.recipient, r.infector, r.product, r.rate, r.layer, nm) :
                  NodeTransition(r.from, r.to, r.rate, nm))
        end
    end
    return out
end

# ---------------------------------------------------------------------------------------------
# erlang_stages
# ---------------------------------------------------------------------------------------------

"""
    erlang_stages(cm::ContactModel, X::Symbol, n::Integer) -> ContactModel

The method of stages: replace the non-susceptible species `X` by `X_1 → X_2 → … → X_n`, so that
the sojourn in `X` becomes Erlang(n, n·a_tot) with the **same mean** 1/a_tot, where a_tot is the
total rate of the transitions out of `X`:

- each internal transition `X_i → X_{i+1}` has rate `n·a_tot`;
- each transition `X → Y_j` at rate a_j leaves from `X_n` at rate `n·a_j` (so the total exit
  rate is n·a_tot and the branching probabilities a_j/a_tot are kept);
- transitions and contacts into `X` enter `X_1`;
- every contact with infector `X` (or recipient `X`) is copied to each stage with the same τ.

Labels record the stage (`SpeciesLabel(...; stage = i)`). The generated names must not collide
with existing species. This fixes the Erlang exit-rate defect of EBM 0.1 (ebm-core #9): there
the last stage left at the user's a instead of n·a.

Stage first, then count reinfections: a reinfection-counted model
([`with_reinfection_counting`](@ref)) is refused, because the stages of one refined species
X_p would have no species of the uncounted model to lump into ([`reinfection_totals`](@ref));
`with_reinfection_counting(erlang_stages(cm, X, n), L)` stages every count alike.
"""
function erlang_stages(cm::ContactModel, X::Symbol, n::Integer)
    where = "erlang_stages(:$(cm.name), :$(X), $(n))"
    n >= 1 || throw(ArgumentError("$(where): the number of stages must be ≥ 1"))
    _is_reinfection_counted(cm) && throw(ArgumentError(
        "$(where): the model is reinfection-counted; stage first, then count " *
        "(with_reinfection_counting(erlang_stages(model, X, n), L)), so that every count is " *
        "staged alike and reinfection_totals lumps the stages consistently"))
    X in cm.species || throw(ArgumentError("$(where): $(X) is not a species"))
    X in cm.susceptible && throw(ArgumentError(
        "$(where): $(X) is a susceptible class; only non-susceptible states have a sojourn " *
        "time to stage"))
    lab = get(cm.labels, X, nothing)
    (lab !== nothing && lab.stage != 0) &&
        throw(ArgumentError("$(where): $(X) is already Erlang stage $(lab.stage) of $(lab.base)"))
    exits = [t for t in cm.transitions if t.from === X]
    isempty(exits) && throw(ArgumentError(
        "$(where): $(X) has no outgoing transition, so it has no sojourn time to stage"))
    stages = [Symbol(X, :_, i) for i in 1:n]
    clash = [s for s in stages if s in cm.species]
    isempty(clash) || throw(ArgumentError(
        "$(where): the stage names $(_list(clash)) collide with existing species; relabel first"))
    a_tot = reduce(rate_add, (t.rate for t in exits))
    internal = rate_mul(n, a_tot)

    cs = Contact[]
    cmap = Int[]
    for (k, c) in enumerate(cm.contacts)
        P = c.product === X ? stages[1] : c.product
        recips = c.recipient === X ? stages : [c.recipient]
        infs = c.infector === X ? stages : [c.infector]
        copies = length(recips) * length(infs) > 1
        for (i, s) in enumerate(recips), (j, J) in enumerate(infs)
            idx = c.recipient === X ? i : j
            push!(cs, _derived_contact(c, s, J, P, c.rate, copies ? Symbol(:_, idx) : nothing))
            push!(cmap, k)
        end
    end
    ts = NodeTransition[]
    tmap = Int[]
    nc = length(cm.contacts)
    chain_done = false
    for (k, t) in enumerate(cm.transitions)
        if t.from === X
            if !chain_done
                for i in 1:(n - 1)
                    push!(ts, NodeTransition(stages[i], stages[i + 1], internal,
                                             Symbol(stages[i], :_to_, stages[i + 1])))
                    push!(tmap, nc + k)
                end
                chain_done = true
            end
            push!(ts, _derived_transition(t, stages[n], t.to, rate_mul(n, t.rate), nothing))
        elseif t.to === X
            push!(ts, _derived_transition(t, t.from, stages[1], t.rate, nothing))
        else
            push!(ts, t)
        end
        push!(tmap, nc + k)
    end
    species = Symbol[]
    for x in cm.species
        x === X ? append!(species, stages) : push!(species, x)
    end
    labels = copy(cm.labels)
    delete!(labels, X)
    for (i, s) in enumerate(stages)
        labels[s] = lab === nothing ? SpeciesLabel(X, :all, 0, i) :
                    SpeciesLabel(lab.base, lab.stratum, lab.count, i)
    end
    note = "erlang_stages: $(X) ↦ $(join(stages, " → ")); internal rate $(n)·a_tot with a_tot = " *
           "$(_rate_string(a_tot)); exits from $(last(stages)) at $(n)·a_j"
    return _rebuild(cm; species, contacts = cs, transitions = ts, labels,
                    provenance = _transform_provenance(cm, note, vcat(cmap, tmap)))
end

# ---------------------------------------------------------------------------------------------
# Reinfection counting (Keeling, House, Cooper & Pellis 2016, approximation 1)
# ---------------------------------------------------------------------------------------------

const _REINFECTION_TAG = "with_reinfection_counting"

_is_reinfection_counted(cm::ContactModel) =
    any(l -> l.count > 0, values(cm.labels)) ||
    any(a -> startswith(a, _REINFECTION_TAG), cm.provenance.assumptions)

# The infection chain (`_infection_chain`) and what counts as an infection (`_is_infection`,
# which increments the infection count) are the §J.8 rule of ir/types.jl (`infected_species`).

"""
    with_reinfection_counting(cm::ContactModel, L::Integer) -> ContactModel

Refine every species `X` into `X_p` by the number `p` of infections the node has had, saturating
at `L` (Keeling, House, Cooper & Pellis 2016, approximation 1):

- an infection (a contact from a susceptible class into the infection chain, the §J.8 rule of
  [`infected_species`](@ref)) takes `s_p` to `X_{min(p+1, L)}`, whatever the infector's count.
  A contact into a species that never becomes infectious (I₁₂ of R₁ + I₂ → I₁₂ + I₂ in a
  partial-immunity model where I₁₂ never infects) is therefore not counted, unlike NBM 0.1,
  which counted every `:infection` transition; the mass-action lumping is exact either way;
- every other reaction keeps the count (`X_p → Y_p`; a contact tracing `S + D → Q + D` keeps it
  too);
- species a node can be in without an infection (susceptible classes and what they reach without
  infection) start at count 0, the others at `min(1, L)`; unreachable refined species are
  dropped, so SIR gains no reinfection states.

Every refined species carries a [`SpeciesLabel`](@ref) with its count, read by
[`infection_count_of`](@ref) and [`base_compartment_of`](@ref). The mass-action and CTMC lumpings
back to `cm` ([`reinfection_totals`](@ref)) are exact (M12). For SIS or SIRS the result has an
arrow into a susceptible class (`I_p → S_p`, type `:resus`) and several susceptible classes, so
it is a T_net model for the node-based and stochastic back ends only; the pairwise lumping is
not exact (the closure acts at the refined level).
"""
function with_reinfection_counting(cm::ContactModel, L::Integer)
    where = "with_reinfection_counting(:$(cm.name), $(L))"
    L >= 0 || throw(ArgumentError("$(where): L must be ≥ 0"))
    _is_reinfection_counted(cm) && throw(ArgumentError("$(where): the model is already " *
                                                       "reinfection-counted"))
    Σ = Set(cm.susceptible)
    chain = _infection_chain(cm)
    infection = Dict(c.name => _is_infection(c, Σ, chain) for c in cm.contacts)

    # species reachable from Σ without an infection start at count 0, the others at min(1, L)
    clean = Set{Symbol}(Σ)
    changed = true
    while changed
        changed = false
        for t in cm.transitions
            (t.from in clean && t.to !== nothing && !(t.to in clean)) || continue
            push!(clean, t.to)
            changed = true
        end
        for c in cm.contacts
            (!infection[c.name] && c.recipient in clean && !(c.product in clean)) || continue
            push!(clean, c.product)
            changed = true
        end
    end
    p1 = min(1, L)
    present = Set{Tuple{Symbol,Int}}((x, x in clean ? 0 : p1) for x in cm.species)
    counts(x) = sort!([p for (y, p) in present if y === x])

    # close the set of refined species under the refined reactions
    changed = true
    while changed
        changed = false
        for c in cm.contacts, p in counts(c.recipient)
            isempty(counts(c.infector)) && continue
            q = infection[c.name] ? min(p + 1, L) : p
            (c.product, q) in present && continue
            push!(present, (c.product, q))
            changed = true
        end
        for t in cm.transitions
            t.to === nothing && continue
            for p in counts(t.from)
                (t.to, p) in present && continue
                push!(present, (t.to, p))
                changed = true
            end
        end
    end

    name(x, p) = Symbol(x, :_, p)
    species = Symbol[name(x, p) for x in cm.species for p in counts(x)]
    sus = Symbol[name(x, p) for x in cm.susceptible for p in counts(x)]
    cs = Contact[]
    cmap = Int[]
    for (k, c) in enumerate(cm.contacts), p in counts(c.recipient), q in counts(c.infector)
        pp = infection[c.name] ? min(p + 1, L) : p
        push!(cs, _derived_contact(c, name(c.recipient, p), name(c.infector, q),
                                   name(c.product, pp), c.rate, Symbol(:_, p, :_, q)))
        push!(cmap, k)
    end
    ts = NodeTransition[]
    tmap = Int[]
    nc = length(cm.contacts)
    for (k, t) in enumerate(cm.transitions), p in counts(t.from)
        Y = t.to === nothing ? nothing : name(t.to, p)
        push!(ts, _derived_transition(t, name(t.from, p), Y, t.rate, Symbol(:_, p)))
        push!(tmap, nc + k)
    end
    labels = Dict{Symbol,SpeciesLabel}()
    for x in cm.species, p in counts(x)
        l = get(cm.labels, x, nothing)
        labels[name(x, p)] = l === nothing ? SpeciesLabel(x, :all, p, 0) :
                             SpeciesLabel(l.base, l.stratum, p, l.stage)
    end
    note = "$(_REINFECTION_TAG)(L = $(L)): X ↦ X_p by infection count p ≤ $(L) (saturating); " *
           "infections: $(_list([c.name for c in cm.contacts if infection[c.name]]))"
    return _rebuild(cm; name = Symbol(cm.name, :_reinf_L, L), species, susceptible = sus,
                    contacts = cs, transitions = ts, labels,
                    provenance = _transform_provenance(cm, note, vcat(cmap, tmap)))
end

function _check_species(cm::ContactModel, X::Symbol, fname)
    X in cm.species || throw(ArgumentError("$(fname)(:$(cm.name), :$(X)): $(X) is not a species " *
                                           "of the model"))
    return X
end

"""
    base_compartment_of(cm::ContactModel, X::Symbol) -> Symbol
    base_compartment_of(name::Symbol) -> Symbol

The base compartment of the species `X` of `cm`, read from its [`SpeciesLabel`](@ref) (`:S` for
`:S_2` after reinfection counting, `:I` for the Erlang stage `:I_3`, `:S` for the stratum
`:S_y`); an unlabelled species is its own base.

The one-argument form is the legacy name parser of EBM and NBM 0.1 (`:S_3` ↦ `:S`: a trailing
`_<digits>` is removed); prefer the model form, which does not depend on names.
"""
function base_compartment_of(cm::ContactModel, X::Symbol)
    _check_species(cm, X, :base_compartment_of)
    l = get(cm.labels, X, nothing)
    return l === nothing ? X : l.base
end
function base_compartment_of(name::Symbol)
    m = match(r"^(.+)_(\d+)$", string(name))
    return m === nothing ? name : Symbol(m.captures[1])
end

"""
    infection_count_of(cm::ContactModel, X::Symbol) -> Union{Int,Nothing}
    infection_count_of(name::Symbol) -> Union{Int,Nothing}

The infection count of the species `X` of a reinfection-counted model
([`with_reinfection_counting`](@ref)), read from its [`SpeciesLabel`](@ref); `nothing` if the
model is not reinfection-counted.

The one-argument form is the legacy name parser of EBM and NBM 0.1 (`:S_3` ↦ `3`, `nothing`
without a trailing `_<digits>`); prefer the model form.
"""
function infection_count_of(cm::ContactModel, X::Symbol)
    _check_species(cm, X, :infection_count_of)
    _is_reinfection_counted(cm) || return nothing
    l = get(cm.labels, X, nothing)
    return l === nothing ? nothing : l.count
end
function infection_count_of(name::Symbol)
    m = match(r"^(.+)_(\d+)$", string(name))
    return m === nothing ? nothing : parse(Int, m.captures[2])
end

# The species of the model before reinfection counting that the refined species X lumps into.
function _uncounted_name(cm::ContactModel, X::Symbol)
    _is_reinfection_counted(cm) || return X
    l = get(cm.labels, X, nothing)
    l === nothing && return X
    s = string(X)
    suffix = "_$(l.count)"
    return endswith(s, suffix) ? Symbol(chop(s; tail = length(suffix))) : l.base
end

"""
    reinfection_totals(cm::ContactModel, u::AbstractDict{Symbol}) -> Dict{Symbol}
    reinfection_totals(cm::ContactModel, u::AbstractVector{<:Real}) -> Dict{Symbol}

The lumping of [`with_reinfection_counting`](@ref): sum the values of the refined species `X_p`
over the infection count `p`, keyed by the species of the model before counting. `u` holds a
value per species, either by name (numbers or time series) or as a state vector in the order of
`species_names(cm)`. For a model that is not reinfection-counted this is the identity map. The
mass-action and CTMC lumpings are exact (M12).
"""
function reinfection_totals(cm::ContactModel, u::AbstractDict)
    out = Dict{Symbol,valtype(u)}()
    for (X, v) in u
        k = _uncounted_name(cm, _check_species(cm, Symbol(X), :reinfection_totals))
        out[k] = haskey(out, k) ? out[k] .+ v : (v isa AbstractArray ? copy(v) : v)
    end
    return out
end
function reinfection_totals(cm::ContactModel, u::AbstractVector{<:Real})
    length(u) == length(cm.species) || throw(ArgumentError(
        "reinfection_totals(:$(cm.name), u): u has $(length(u)) entries for " *
        "$(length(cm.species)) species"))
    return reinfection_totals(cm, Dict{Symbol,eltype(u)}(zip(cm.species, u)))
end

# ---------------------------------------------------------------------------------------------
# Reverse-map targets on Poisson networks: D_μ (M2) and E_μ (M3)
# ---------------------------------------------------------------------------------------------

function _require_poisson_liftable(cm::ContactModel, fname)
    require_admissible(cm, :edge_based)
    length(cm.susceptible) == 1 || throw(ArgumentError(
        "$(fname)(:$(cm.name)): needs exactly one susceptible class on a Poisson network " *
        "(found $(_list(cm.susceptible)))"))
    for c in cm.contacts
        c.layer === :all || throw(ArgumentError(
            "$(fname)(:$(cm.name)): the contact `$(c.name)` is on the layer :$(c.layer); the " *
            "Poisson maps are for one configuration network"))
    end
    return only(cm.susceptible)
end

# The per-contact rate τ_r, and the mass-action rate μ·τ_r, on a Poisson(μ) network.
_poisson_tau(cm, c, μ) = _convert_rate(cm.convention, c.rate, μ)
_poisson_ma_rate(::PerContact, r, μ) = rate_mul(μ, r)
_poisson_ma_rate(::FrequencyDependent, r, μ) = r
_poisson_ma_rate(c::DensityDependent, r, μ) = rate_mul(r, c.N)

function _push_merged!(rs::Vector{GeneralReaction}, subs, prods, rate)
    r = GeneralReaction(subs, prods, rate)
    k = findfirst(x -> x.substrates == r.substrates && x.products == r.products, rs)
    if k === nothing
        push!(rs, r)
    else
        old = rs[k]
        rs[k] = GeneralReaction(old.substrates, old.products, rate_add(old.rate, rate), false,
                                old.name)
    end
    return rs
end

"""
    edge_doubling(cm::ContactModel, μ) -> ReactionNetworkData

The network D_μ P of the Poisson isomorphism (M2): EB_{Poisson(μ)}(P) ≅ MA(D_μ P) through
π(θ, ξ, φ, pop) = (S = qξe^{μ(θ−1)}, Φ_X = φ_X, X = pop_X), natural in P. For every
non-susceptible species `X` there is an edge copy `Φ_X` next to the node copy `X`:

- each contact `s + J → X + J` (per-contact rate τ) becomes `s + Φ_J → Φ_X + X + Φ_J` at μτ;
- each infector `J` gets `Φ_J → ∅` at Σ_{r: J_r = J} τ_r (the edge has transmitted);
- each transition `X → Y | ∅` acts on both copies at its rate;
- each exit `s → Y` becomes `s → Φ_Y + Y` (for a Poisson network φ_s = S).

The initial condition is S(0) = q, Φ_X(0) = X(0) = ρ_X. The model must be admissible for the
edge-based model with a single susceptible class, and the rate convention is applied with
⟨k⟩ = μ.
"""
function edge_doubling(cm::ContactModel, μ)
    s = _require_poisson_liftable(cm, :edge_doubling)
    nodes = [x for x in cm.species if x !== s]
    Φ(x) = Symbol("Φ_", x)
    clash = [Φ(x) for x in nodes if Φ(x) in cm.species]
    isempty(clash) || throw(ArgumentError(
        "edge_doubling(:$(cm.name)): the edge-copy names $(_list(clash)) collide with species"))
    rs = GeneralReaction[]
    removal = Dict{Symbol,Any}()
    order = Symbol[]
    for c in cm.contacts
        τ = _poisson_tau(cm, c, μ)
        _push_merged!(rs, [s => 1, Φ(c.infector) => 1],
                      [Φ(c.product) => 1, c.product => 1, Φ(c.infector) => 1],
                      _poisson_ma_rate(cm.convention, c.rate, μ))
        J = c.infector
        if haskey(removal, J)
            removal[J] = rate_add(removal[J], τ)
        else
            removal[J] = τ
            push!(order, J)
        end
    end
    for J in order
        _push_merged!(rs, [Φ(J) => 1], Pair{Symbol,Int}[], removal[J])
    end
    for t in cm.transitions
        if t.from === s                                   # exit
            prods = t.to === nothing ? Pair{Symbol,Int}[] : [Φ(t.to) => 1, t.to => 1]
            _push_merged!(rs, [s => 1], prods, t.rate)
        else
            for f in (Φ, identity)
                prods = t.to === nothing ? Pair{Symbol,Int}[] : [f(t.to) => 1]
                _push_merged!(rs, [f(t.from) => 1], prods, t.rate)
            end
        end
    end
    species = vcat(s, Φ.(nodes), nodes)
    obs = Dict{Symbol,Vector{Symbol}}(x => [x] for x in cm.species)
    note = "edge_doubling D_μ (M2), μ = $(_rate_string(μ)): EB on Poisson(μ) ≅ MA of this " *
           "network via S = qξe^{μ(θ−1)}, Φ_X = φ_X, X = pop_X"
    pv = Provenance(:transform, :explicit, vcat(cm.provenance.assumptions, [note]), Int[])
    return ReactionNetworkData(Symbol(cm.name, :_edge_doubling), species, rs;
                               defaults = cm.defaults, observables = obs, provenance = pv)
end

"""
    rempala_reduction(cm::ContactModel, μ) -> ContactModel

Rempała's quotient E_μ P (M3), "back to mass action on the same species": the model c_μ P (every
contact at μτ) plus a removal `J → ∅` at τ_r for every contact r with infector J (merged per
infector and with existing removals). Its mass-action dynamics are the image of
EB_{Poisson(μ)}(P) under π = (θ, ξ, φ, pop) ↦ (S = qξe^{μ(θ−1)}, φ): **every non-susceptible
species of the result stands for the edge variable φ_X, not for the node fraction**. For SIR
this is MA(β = μτ, γ_MA = γ + τ) on (S, φ_I).

The result has the `PerContact` convention and is read as mass action (`κ = 1`). The model
must be admissible for the edge-based model with a single susceptible class.
"""
function rempala_reduction(cm::ContactModel, μ)
    _require_poisson_liftable(cm, :rempala_reduction)
    cs = Contact[]
    for c in cm.contacts
        push!(cs, Contact(c.recipient, c.infector, c.product,
                          _poisson_ma_rate(cm.convention, c.rate, μ), c.layer, c.name))
    end
    ts = copy(cm.transitions)
    rmap = collect(1:(length(cm.contacts) + length(cm.transitions)))
    for (k, c) in enumerate(cm.contacts)
        τ = _poisson_tau(cm, c, μ)
        i = findfirst(t -> t.from === c.infector && t.to === nothing, ts)
        if i === nothing
            push!(ts, NodeTransition(c.infector, nothing, τ, Symbol(c.infector, :_to_∅)))
            push!(rmap, k)
        else
            ts[i] = _with_rate(ts[i], rate_add(ts[i].rate, τ))
        end
    end
    note = "rempala_reduction E_μ (M3), μ = $(_rate_string(μ)): mass action (κ = 1); the " *
           "non-susceptible species are the edge variables φ_X, and S = qξe^{μ(θ−1)}"
    return _rebuild(cm; name = Symbol(cm.name, :_rempala), contacts = cs, transitions = ts,
                    convention = PerContact(),
                    provenance = _transform_provenance(cm, note, rmap))
end
