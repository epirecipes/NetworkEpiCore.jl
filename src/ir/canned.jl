# Owner: WP6 (DESIGN_NetworkEpiCore.md §B.3; work package in §G.2).
#
# Canned models, each returning a ContactModel with Symbol rates by default (any rate may be
# passed: a number, a Symbol, an Expr or a symbolic expression). EBM and NBM re-export these
# same bindings (§A.7). The per-contact rate is τ; `β` is accepted as a deprecated alias of `τ`
# by the four models that EBM and NBM exported before 0.2, and so is EBM's `susceptible`
# keyword (the name of the susceptible species).

export sir_model, seir_model, sis_model, sirs_model, seair_model, twostrain_model, sirv_model,
       layered_sir_model

function _deprecated_rate_alias(τ, β, fname::Symbol)
    β === nothing && return τ
    τ === :τ || throw(ArgumentError(
        "$(fname): pass the per-contact rate as τ only (β is its deprecated alias; got both)"))
    Base.depwarn("`$(fname)(; β = …)` is deprecated: the per-contact (per-edge) rate is now " *
                 "called τ, and β is reserved for mass-action rates. Use `$(fname)(; τ = …)`.",
                 fname)
    return β
end

function _deprecated_susceptible_alias(S, susceptible, fname::Symbol)
    susceptible === nothing && return S
    S === :S || throw(ArgumentError(
        "$(fname): pass the susceptible species as S only (susceptible is its deprecated alias)"))
    Base.depwarn("`$(fname)(; susceptible = …)` is deprecated; use `$(fname)(; S = …)`.", fname)
    return susceptible
end

_factory_provenance(nr) = Provenance(:factory; method = :explicit, reaction_map = 1:nr)

"""
    sir_model(; τ = :τ, γ = :γ, S = :S, I = :I, R = :R) -> ContactModel

SIR on a network: the contact `S + I → 2I` at per-contact rate `τ` and recovery `I → R` at `γ`.
Typed over T_EB, so every back end accepts it. The species names can be changed with `S`, `I`
and `R`.

`β` is a deprecated alias of `τ` and `susceptible` of `S` (the EdgeBasedModels 0.1 keywords).
"""
function sir_model(; τ = :τ, γ = :γ, S::Symbol = :S, I::Symbol = :I, R::Symbol = :R,
                   β = nothing, susceptible::Union{Nothing,Symbol} = nothing)
    τ = _deprecated_rate_alias(τ, β, :sir_model)
    S = _deprecated_susceptible_alias(S, susceptible, :sir_model)
    return ContactModel(:sir; contacts = [Contact(S, I, I, τ)],
                        transitions = [NodeTransition(I, R, γ)],
                        provenance = _factory_provenance(2))
end

"""
    seir_model(; τ = :τ, σ = :σ, γ = :γ) -> ContactModel

SEIR on a network: the contact `S + I → E + I` at per-contact rate `τ`, `E → I` at `σ` and
`I → R` at `γ`. Typed over T_EB; the entry (and default seeded) state is `E`.

`β` is a deprecated alias of `τ` and `susceptible` of the name `:S`.
"""
function seir_model(; τ = :τ, σ = :σ, γ = :γ, β = nothing,
                    susceptible::Union{Nothing,Symbol} = nothing)
    τ = _deprecated_rate_alias(τ, β, :seir_model)
    S = _deprecated_susceptible_alias(:S, susceptible, :seir_model)
    return ContactModel(:seir; contacts = [Contact(S, :I, :E, τ)],
                        transitions = [NodeTransition(:E, :I, σ), NodeTransition(:I, :R, γ)],
                        provenance = _factory_provenance(3))
end

"""
    sis_model(; τ = :τ, γ = :γ) -> ContactModel

SIS on a network: `S + I → 2I` at per-contact rate `τ` and `I → S` at `γ`. The transition
`I → S` is of type `:resus` (an arrow into the susceptible class), so the model is typed over
T_net only: the edge-based model refuses it, and the node-based, stochastic and mass-action back
ends accept it (see [`admissibility`](@ref)).

`β` is a deprecated alias of `τ` and `susceptible` of the name `:S`.
"""
function sis_model(; τ = :τ, γ = :γ, β = nothing, susceptible::Union{Nothing,Symbol} = nothing)
    τ = _deprecated_rate_alias(τ, β, :sis_model)
    S = _deprecated_susceptible_alias(:S, susceptible, :sis_model)
    return ContactModel(:sis; contacts = [Contact(S, :I, :I, τ)],
                        transitions = [NodeTransition(:I, S, γ)],
                        provenance = _factory_provenance(2))
end

"""
    sirs_model(; τ = :τ, γ = :γ, ε = :ε) -> ContactModel

SIRS on a network: `S + I → 2I` at per-contact rate `τ`, `I → R` at `γ` and loss of immunity
`R → S` at `ε`. The transition `R → S` is of type `:resus`, so the model is typed over T_net
only (the edge-based model refuses it).

`β` is a deprecated alias of `τ` and `susceptible` of the name `:S`.
"""
function sirs_model(; τ = :τ, γ = :γ, ε = :ε, β = nothing,
                    susceptible::Union{Nothing,Symbol} = nothing)
    τ = _deprecated_rate_alias(τ, β, :sirs_model)
    S = _deprecated_susceptible_alias(:S, susceptible, :sirs_model)
    return ContactModel(:sirs; contacts = [Contact(S, :I, :I, τ)],
                        transitions = [NodeTransition(:I, :R, γ), NodeTransition(:R, S, ε)],
                        provenance = _factory_provenance(3))
end

"""
    seair_model(; τI = :τI, τA = :τA, σ = :σ, p = :p, γ = :γ) -> ContactModel

SEAIR with branching after latency and two infectors: contacts `S + I → E + I` at `τI` and
`S + A → E + A` at `τA`; `E → I` at `p σ`, `E → A` at `(1 - p) σ`; `I → R` and `A → R` at `γ`.
Typed over T_EB; the entry state is `E`. The branching rates are `Expr`s (`:(p * σ)` and
`:((1 - p) * σ)`) unless `p` and `σ` are numbers.
"""
function seair_model(; τI = :τI, τA = :τA, σ = :σ, p = :p, γ = :γ)
    return ContactModel(:seair;
                        contacts = [Contact(:S, :I, :E, τI), Contact(:S, :A, :E, τA)],
                        transitions = [NodeTransition(:E, :I, rate_mul(p, σ)),
                                       NodeTransition(:E, :A, rate_mul(_rate_sub(1, p), σ)),
                                       NodeTransition(:I, :R, γ), NodeTransition(:A, :R, γ)],
                        provenance = _factory_provenance(6))
end

"""
    twostrain_model(; τ1 = :τ1, τ2 = :τ2, γ = :γ) -> ContactModel

Two competing strains with full cross-immunity: `S + I1 → 2I1` at `τ1`, `S + I2 → 2I2` at `τ2`,
and `I1 → R`, `I2 → R` at `γ`. One susceptible class, two infectors and two entry states, typed
over T_EB. With two entry states the seeding must be given explicitly.
"""
function twostrain_model(; τ1 = :τ1, τ2 = :τ2, γ = :γ)
    return ContactModel(:twostrain;
                        contacts = [Contact(:S, :I1, :I1, τ1), Contact(:S, :I2, :I2, τ2)],
                        transitions = [NodeTransition(:I1, :R, γ), NodeTransition(:I2, :R, γ)],
                        provenance = _factory_provenance(4))
end

"""
    sirv_model(; τ = :τ, γ = :γ, ν = :ν) -> ContactModel

SIR with vaccination: `S + I → 2I` at per-contact rate `τ`, `I → R` at `γ` and `S → V` at `ν`.
The vaccination is of type `:exit` (a transition out of the susceptible class), which the
edge-based model admits through the survival factor ξ = e^{−νt}.
"""
function sirv_model(; τ = :τ, γ = :γ, ν = :ν)
    return ContactModel(:sirv; contacts = [Contact(:S, :I, :I, τ)],
                        transitions = [NodeTransition(:I, :R, γ), NodeTransition(:S, :V, ν)],
                        provenance = _factory_provenance(3))
end

"""
    layered_sir_model(layers, τs; γ = :γ, name = :sir_layered) -> ContactModel

SIR on a multiplex network with a per-layer contact rate: for each layer ℓ in `layers` (a vector
of distinct `Symbol`s) the contact `S + I → 2I` on layer ℓ at per-contact rate `τs[ℓ's index]`,
and recovery `I → R` at `γ`. For example `layered_sir_model([:home, :comm], [:(3c), :c])` is the
model of the `:sir_mpx` scenario, to be used on a `MultiplexNetwork` with those layer names
(on a network without them no network back end accepts it; §B.2).
"""
function layered_sir_model(layers::AbstractVector{Symbol}, τs::AbstractVector; γ = :γ,
                           name::Symbol = :sir_layered)
    isempty(layers) && throw(ArgumentError("layered_sir_model: give at least one layer"))
    length(layers) == length(τs) || throw(ArgumentError(
        "layered_sir_model: $(length(layers)) layers but $(length(τs)) rates"))
    allunique(layers) || throw(ArgumentError("layered_sir_model: the layers $(layers) are not distinct"))
    :all in layers && throw(ArgumentError(
        "layered_sir_model: :all is not a layer name (a contact on :all acts on every layer)"))
    cs = [Contact(:S, :I, :I, τ; layer = ℓ) for (ℓ, τ) in zip(layers, τs)]
    return ContactModel(name; contacts = cs, transitions = [NodeTransition(:I, :R, γ)],
                        provenance = _factory_provenance(length(cs) + 1))
end
