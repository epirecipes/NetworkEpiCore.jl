# Owner: WP10 (DESIGN_NetworkEpiCore.md §D.3, §D.5, §D.7; work package in §G.2).
#
# Runtime morphism objects: `SymbolicODE` (a closed object of the category Dyn), `Evidence`,
# `Semiconjugacy` (a map π with Dπ·F = G∘π), `VerificationResult`, and `NaturalTransformation`
# with its registry (`register_transformation!`, `transformations`, `transformation`).
#
# Everything that looks inside a symbolic expression lives in NetworkEpiCoreSymbolicsExt: the
# methods of `verify`, `pushforward` (stubs in generics.jl), `vector_fields_equal`,
# `check_naturality` and `as_parameter` (stubs below), and the symbolic `mass_action` /
# `symbolic_ode` of a ContactModel. Core only stores and validates.
#
# Coordinates and parameters are identified **by name** everywhere (a state `θ(t)`, a plain
# variable `θ` and the Symbol `:θ` all name the coordinate θ), so objects built by EBM (from MTK
# equations), NBM and NEC can be compared without sharing variable objects.
#
# Include order: after analysis/ngm.jl.

export SymbolicODE, state_names, Evidence, Semiconjugacy, VerificationResult,
       NaturalTransformation
export MORPHISM_KINDS, EXACTNESS_LEVELS, EVIDENCE_KINDS
export register_transformation!, transformations, transformation
export check_naturality, vector_fields_equal, as_parameter

"""
    MORPHISM_KINDS

The kinds of a [`Semiconjugacy`](@ref) (§D.5): `:conjugacy` (a diffeomorphic semiconjugacy, an
isomorphism of Dyn), `:semiconjugacy`, `:restriction` (the inclusion of an invariant
subsystem) and `:lumping` (an exact lumping of a Markov chain, a linear semiconjugacy of its
forward equation).
"""
const MORPHISM_KINDS = (:conjugacy, :semiconjugacy, :restriction, :lumping)

"""
    EXACTNESS_LEVELS

How exact a map between representations is (§D.5): `:exact` (a morphism of Dyn),
`:limit` (holds only in a limit, such as μ → ∞; never called a morphism) and `:calibration`
(parameters matched to a target such as R₀; not natural, F6).
"""
const EXACTNESS_LEVELS = (:exact, :limit, :calibration)

"""
    EVIDENCE_KINDS

The kinds of [`Evidence`](@ref): `:lean` (a compiled, gated Lean theorem), `:symbolic` (a
symbolic residual that simplifies to 0), `:numeric` (a numeric check) and `:paper` (a
published result).
"""
const EVIDENCE_KINDS = (:lean, :symbolic, :numeric, :paper)

# ---------------------------------------------------------------------------------------------
# Names of coordinates
# ---------------------------------------------------------------------------------------------

# The name of a state or parameter entry: a Symbol, or a symbolic variable (named through the
# Symbolics extension hook of ir/rates.jl; `θ(t)` is named θ).
_coordinate_name(x::Symbol) = x
_coordinate_name(x::AbstractString) = Symbol(x)
_coordinate_name(x) = _parameter_name(x)

function _check_unique_names(names, what, where)
    dup = _duplicates(names)
    isempty(dup) || throw(ArgumentError("$where: $what are not unique: $(_list(dup))"))
    return nothing
end

# ---------------------------------------------------------------------------------------------
# SymbolicODE
# ---------------------------------------------------------------------------------------------

"""
    SymbolicODE(name, states, rhs, parameters, domain)
    SymbolicODE(name; states, rhs, parameters = :infer, domain = [])

A closed, autonomous dynamical system u̇ = F(u) with a symbolic vector field: an object of the
category Dyn (§D.3).

- `states`: the coordinates, as symbolic variables (`θ`, or MTK-style `θ(t)`) or `Symbol`s;
  their names must be unique.
- `rhs`: `rhs[i]` is the symbolic expression of the time derivative of `states[i]`.
- `parameters`: the parameters of the field (symbolic variables or names). `:infer` (Symbolics
  extension) takes every variable of `rhs` that is not a state, except time `t`, in order of
  first appearance.
- `domain`: probe boxes `x => (lo, hi)` for states and parameters (keys are variables or names),
  used by [`verify`](@ref) and [`vector_fields_equal`](@ref) for numeric probes. The box also
  says where a local semiconjugacy (`SemiconjOn U`) is claimed to hold, e.g. `θ => (0.05, 1.0)`
  for maps that divide by ψ(θ). Unlisted states are probed in (0.05, 0.95), unlisted
  parameters in (0.1, 1.0), and time `t` (a free variable named t) in (0.1, 1000) on a log
  scale.

Coordinates and parameters are identified by name, so `θ(t)`, `θ` and `:θ` are the same
coordinate. NEC builds these with `mass_action(cm; κ)` / `symbolic_ode(cm; κ)` (Symbolics
extension); EBM and NBM return them from `symbolic_ode(sys)`.
"""
struct SymbolicODE
    name::Symbol
    states::Vector{Any}
    rhs::Vector{Any}
    parameters::Vector{Any}
    domain::Vector{Pair{Any,Tuple{Float64,Float64}}}
    function SymbolicODE(name::Symbol, states::AbstractVector, rhs::AbstractVector,
                         parameters::AbstractVector, domain)
        where = "SymbolicODE :$(name)"
        length(states) == length(rhs) || throw(ArgumentError(
            "$where: $(length(states)) states but $(length(rhs)) right-hand sides"))
        snames = Symbol[_coordinate_name(x) for x in states]
        _check_unique_names(snames, "state names", where)
        pnames = Symbol[_coordinate_name(p) for p in parameters]
        _check_unique_names(pnames, "parameter names", where)
        both = [n for n in pnames if n in snames]
        isempty(both) || throw(ArgumentError(
            "$where: $(_list(both)) is both a state and a parameter"))
        return new(name, collect(Any, states), collect(Any, rhs), collect(Any, parameters),
                   _probe_boxes(domain, where))
    end
end

function SymbolicODE(name::Symbol; states::AbstractVector, rhs::AbstractVector,
                     parameters = :infer, domain = Pair{Any,Tuple{Float64,Float64}}[])
    params = parameters === :infer ? _infer_ode_parameters(name, states, rhs) :
             collect(Any, parameters)
    return SymbolicODE(name, states, rhs, params, domain)
end

function _infer_ode_parameters(name, states, rhs)
    applicable(_free_variables, rhs, states) || throw(ArgumentError(
        "SymbolicODE :$(name): inferring the parameters needs NetworkEpiCoreSymbolicsExt " *
        "(`using Symbolics`); or pass `parameters = [...]`"))
    return _free_variables(rhs, states)
end

"""
    _free_variables(exprs, states) -> Vector

Hook for NetworkEpiCoreSymbolicsExt: the variables of `exprs` that are not (by name) among
`states`, excluding time `t`, in order of first appearance.
"""
function _free_variables end

function _probe_boxes(domain, where)
    out = Pair{Any,Tuple{Float64,Float64}}[]
    for (k, box) in (domain isa AbstractDict ? pairs(domain) : domain)
        length(box) == 2 || throw(ArgumentError(
            "$where: the probe box of $(k) must be a pair of numbers (lo, hi); got $(box)"))
        lo, hi = Float64(box[1]), Float64(box[2])
        (isfinite(lo) && isfinite(hi) && lo < hi) || throw(ArgumentError(
            "$where: the probe box of $(k) must satisfy lo < hi (finite); got ($(lo), $(hi))"))
        push!(out, k => (lo, hi))
    end
    return out
end

"""
    state_names(ode::SymbolicODE) -> Vector{Symbol}

The names of the coordinates of `ode`, in order (`θ(t)` is named `:θ`).
"""
state_names(ode::SymbolicODE) = Symbol[_coordinate_name(x) for x in ode.states]

Base.nameof(ode::SymbolicODE) = ode.name

"""
    symbolic_ode(ode::SymbolicODE) -> SymbolicODE

The identity, so that functions taking "anything with a symbolic vector field" accept a
`SymbolicODE`.
"""
symbolic_ode(ode::SymbolicODE) = ode

Base.show(io::IO, ode::SymbolicODE) =
    print(io, "SymbolicODE(:", ode.name, "; ", length(ode.states), " states, ",
          length(ode.parameters), " parameters)")

function Base.show(io::IO, ::MIME"text/plain", ode::SymbolicODE)
    print(io, "SymbolicODE :", ode.name, " (", length(ode.states), " states)")
    for (x, f) in zip(ode.states, ode.rhs)
        print(io, "\n  d", _coordinate_name(x), "/dt = ", f)
    end
    isempty(ode.parameters) ||
        print(io, "\n  parameters  ", join(string.(_coordinate_name.(ode.parameters)), ", "))
    for (k, (lo, hi)) in ode.domain
        print(io, "\n  domain      ", _coordinate_name(k), " ∈ (", lo, ", ", hi, ")")
    end
end

# ---------------------------------------------------------------------------------------------
# Evidence
# ---------------------------------------------------------------------------------------------

"""
    Evidence(kind, ref)

Where the claim of a morphism is established: `kind` is one of [`EVIDENCE_KINDS`](@ref)
(`:lean`, `:symbolic`, `:numeric`, `:paper`) and `ref` a reference, e.g.
`Evidence(:lean, "NEP.rempala")`, `Evidence(:symbolic, "test/suites/morphisms.jl")` or
`Evidence(:paper, "Rempała 2023, Thm 1")`. Vignettes cite only Lean names listed in
`proofs/CITABLE.txt`.
"""
struct Evidence
    kind::Symbol
    ref::String
    function Evidence(kind::Symbol, ref::AbstractString)
        kind in EVIDENCE_KINDS || throw(ArgumentError(
            "Evidence: kind must be one of $(EVIDENCE_KINDS); got :$(kind)"))
        return new(kind, String(ref))
    end
end
Base.:(==)(a::Evidence, b::Evidence) = a.kind === b.kind && a.ref == b.ref
Base.hash(e::Evidence, h::UInt) = hash((e.kind, e.ref), hash(:Evidence, h))
Base.show(io::IO, e::Evidence) = print(io, "Evidence(:", e.kind, ", ", repr(e.ref), ")")

# ---------------------------------------------------------------------------------------------
# Semiconjugacy
# ---------------------------------------------------------------------------------------------

"""
    Semiconjugacy(name, source, target, map; parameter_map = [], kind = :semiconjugacy,
                  exactness = :exact, evidence = Evidence[])

A morphism π: (V, F) → (W, G) of Dyn between two [`SymbolicODE`](@ref)s: a smooth map with
Dπ(u)·F(u) = G(π(u)) (§D.3), so that π maps solutions of the source to solutions of the target.

- `map`: `target state => expression in the source states` (and source parameters), one entry
  per target state (keys are variables or names); stored in target-state order.
- `parameter_map`: `target parameter => expression in the source parameters`, e.g.
  `β => μ*τ, γ_MA => γ + τ` for Rempała's quotient (M3). Every key must name a parameter of the
  target (`target.parameters`); a misspelt key is an error. A target parameter that is not listed
  is identified with the source parameter of the same name.
- `kind`: one of [`MORPHISM_KINDS`](@ref); `exactness`: one of [`EXACTNESS_LEVELS`](@ref)
  (limits and calibrations are labelled so, and are expected to fail [`verify`](@ref));
  `evidence`: a vector of [`Evidence`](@ref).

[`verify`](@ref) checks the identity symbolically and numerically, and [`pushforward`](@ref)
maps a source trajectory to target coordinates (Symbolics extension).
"""
struct Semiconjugacy
    name::Symbol
    source::SymbolicODE
    target::SymbolicODE
    map::Vector{Pair{Any,Any}}
    parameter_map::Vector{Pair{Any,Any}}
    kind::Symbol
    exactness::Symbol
    evidence::Vector{Evidence}
    function Semiconjugacy(name::Symbol, source::SymbolicODE, target::SymbolicODE,
                           map::AbstractVector, parameter_map::AbstractVector, kind::Symbol,
                           exactness::Symbol, evidence::AbstractVector)
        where = "Semiconjugacy :$(name)"
        kind in MORPHISM_KINDS || throw(ArgumentError(
            "$where: kind must be one of $(MORPHISM_KINDS); got :$(kind)"))
        exactness in EXACTNESS_LEVELS || throw(ArgumentError(
            "$where: exactness must be one of $(EXACTNESS_LEVELS); got :$(exactness)"))
        tnames = state_names(target)
        given = Dict{Symbol,Any}()
        for (k, v) in map
            n = _coordinate_name(k)
            n in tnames || throw(ArgumentError(
                "$where: the map assigns $(n), which is not a state of the target " *
                ":$(target.name) (states: $(_list(tnames)))"))
            haskey(given, n) && throw(ArgumentError("$where: the map assigns $(n) twice"))
            given[n] = v
        end
        missing_ = [n for n in tnames if !haskey(given, n)]
        isempty(missing_) || throw(ArgumentError(
            "$where: the map gives no expression for the target state(s) $(_list(missing_))"))
        ordered = Pair{Any,Any}[target.states[i] => given[n] for (i, n) in enumerate(tnames)]
        pm = Pair{Any,Any}[]
        seen = Symbol[]
        tparams = Symbol[_coordinate_name(p) for p in target.parameters]
        for (k, v) in parameter_map
            n = _coordinate_name(k)
            n in tnames && throw(ArgumentError(
                "$where: the parameter map assigns $(n), which is a target state"))
            n in tparams || throw(ArgumentError(
                "$where: the parameter map assigns $(n), which is not a parameter of the " *
                "target :$(target.name) (parameters: " *
                "$(isempty(tparams) ? "none" : _list(tparams)))"))
            n in seen && throw(ArgumentError("$where: the parameter map assigns $(n) twice"))
            push!(seen, n)
            push!(pm, k => v)
        end
        return new(name, source, target, ordered, pm, kind, exactness,
                   collect(Evidence, evidence))
    end
end

function Semiconjugacy(name::Symbol, source::SymbolicODE, target::SymbolicODE, map;
                       parameter_map = Pair{Any,Any}[], kind::Symbol = :semiconjugacy,
                       exactness::Symbol = :exact, evidence = Evidence[])
    _pairs(x) = x isa AbstractDict ? collect(Pair{Any,Any}, pairs(x)) : collect(Pair{Any,Any}, x)
    return Semiconjugacy(name, source, target, _pairs(map), _pairs(parameter_map), kind,
                         exactness, collect(Evidence, evidence))
end

Base.nameof(m::Semiconjugacy) = m.name

Base.show(io::IO, m::Semiconjugacy) =
    print(io, "Semiconjugacy(:", m.name, ": :", m.source.name, " → :", m.target.name,
          "; kind = :", m.kind, ", exactness = :", m.exactness, ")")

function Base.show(io::IO, ::MIME"text/plain", m::Semiconjugacy)
    print(io, "Semiconjugacy :", m.name, "  (kind :", m.kind, ", exactness :", m.exactness, ")")
    print(io, "\n  source  ", m.source)
    print(io, "\n  target  ", m.target)
    for (k, v) in m.map
        print(io, "\n  map     ", _coordinate_name(k), " = ", v)
    end
    for (k, v) in m.parameter_map
        print(io, "\n  params  ", _coordinate_name(k), " = ", v)
    end
    for e in m.evidence
        print(io, "\n  evidence ", e)
    end
end

# ---------------------------------------------------------------------------------------------
# VerificationResult
# ---------------------------------------------------------------------------------------------

"""
    VerificationResult(ok, method, max_residual, probes, details)

The outcome of [`verify`](@ref) (and of [`check_naturality`](@ref)):

- `ok`: whether the identity holds (symbolically, or numerically within `rtol`);
- `method`: `:symbolic` (every component of Dπ·F − G∘π simplified to 0) or `:numeric`;
- `max_residual`: 0.0 when the symbolic residual is 0; otherwise the largest relative residual
  ‖Dπ·F − G∘π‖∞ / max(‖Dπ·F‖∞, ‖G∘π‖∞) over the numeric probes;
- `probes`: the number of numeric probe points used (0 for a purely symbolic success);
- `details`: a human-readable account, naming the failing components and their residuals.
"""
struct VerificationResult
    ok::Bool
    method::Symbol
    max_residual::Float64
    probes::Int
    details::String
end

Base.show(io::IO, r::VerificationResult) =
    print(io, "VerificationResult(ok = ", r.ok, ", method = :", r.method, ", residual = ",
          r.max_residual, ")")

function Base.show(io::IO, ::MIME"text/plain", r::VerificationResult)
    show(io, r)
    r.probes > 0 && print(io, "  [", r.probes, " probes]")
    isempty(r.details) || print(io, "\n  ", replace(r.details, "\n" => "\n  "))
end

# ---------------------------------------------------------------------------------------------
# Natural transformations and their registry
# ---------------------------------------------------------------------------------------------

"""
    NaturalTransformation(name; source, target, applies, component, kind = :semiconjugacy,
                          evidence = Evidence[])

A natural transformation η: F ⇒ G between two representation functors (for example
`:edge_based ⇒ :mass_action`), registered by the package that owns the source representation
(EBM registers M1–M5, NBM the M6 target check).

- `source`, `target`: the names of the representations (`Symbol`s such as `:edge_based`,
  `:mass_action`, `:s_anchored`);
- `applies(cm, net) -> Bool`: whether the component exists for the model `cm` on the network
  `net` (e.g. only on a Poisson network);
- `component(cm, net) -> Semiconjugacy`: the component η_P;
- `kind` (one of [`MORPHISM_KINDS`](@ref)) and `evidence`.

Calling `η(cm, net)` returns the component, after checking `applies`. Naturality with respect to
gluing is checked by [`check_naturality`](@ref). Register with
[`register_transformation!`](@ref) (from the registering package's `__init__`).
"""
struct NaturalTransformation
    name::Symbol
    source::Symbol
    target::Symbol
    applies::Function
    component::Function
    kind::Symbol
    evidence::Vector{Evidence}
    function NaturalTransformation(name::Symbol, source::Symbol, target::Symbol,
                                   applies::Function, component::Function, kind::Symbol,
                                   evidence::AbstractVector)
        kind in MORPHISM_KINDS || throw(ArgumentError(
            "NaturalTransformation :$(name): kind must be one of $(MORPHISM_KINDS); got " *
            ":$(kind)"))
        return new(name, source, target, applies, component, kind, collect(Evidence, evidence))
    end
end

NaturalTransformation(name::Symbol; source::Symbol, target::Symbol, applies::Function,
                      component::Function, kind::Symbol = :semiconjugacy,
                      evidence = Evidence[]) =
    NaturalTransformation(name, source, target, applies, component, kind,
                          collect(Evidence, evidence))

function (η::NaturalTransformation)(cm, net)
    η.applies(cm, net) || throw(ArgumentError(
        "natural transformation :$(η.name) ($(η.source) ⇒ $(η.target)) does not apply to " *
        ":$(nameof(cm)) on $(nameof(typeof(net)))"))
    m = η.component(cm, net)
    m isa Semiconjugacy || throw(ArgumentError(
        "natural transformation :$(η.name): the component returned a $(typeof(m)), not a " *
        "Semiconjugacy"))
    return m
end

Base.nameof(η::NaturalTransformation) = η.name
Base.show(io::IO, η::NaturalTransformation) =
    print(io, "NaturalTransformation(:", η.name, ": ", η.source, " ⇒ ", η.target, "; kind = :",
          η.kind, ")")

const _TRANSFORMATIONS = NaturalTransformation[]
const _TRANSFORMATIONS_LOCK = ReentrantLock()

"""
    register_transformation!(η::NaturalTransformation) -> η

Add `η` to the registry of natural transformations, replacing a registered transformation of
the same name. Packages call this from their `__init__` (a registration made while a package
precompiles would not persist). See [`transformations`](@ref).
"""
function register_transformation!(η::NaturalTransformation)
    lock(_TRANSFORMATIONS_LOCK) do
        k = findfirst(x -> x.name === η.name, _TRANSFORMATIONS)
        k === nothing ? push!(_TRANSFORMATIONS, η) : (_TRANSFORMATIONS[k] = η)
    end
    return η
end

"""
    transformations(; source = nothing, target = nothing) -> Vector{NaturalTransformation}
    transformations(cm, net; source = nothing, target = nothing)

The registered natural transformations, in order of registration, optionally filtered by source
and target representation. With a model and a network, only those whose `applies(cm, net)` is
true.
"""
function transformations(; source::Union{Nothing,Symbol} = nothing,
                         target::Union{Nothing,Symbol} = nothing)
    all_ = lock(() -> copy(_TRANSFORMATIONS), _TRANSFORMATIONS_LOCK)
    return [η for η in all_ if (source === nothing || η.source === source) &&
                               (target === nothing || η.target === target)]
end

transformations(cm, net; source::Union{Nothing,Symbol} = nothing,
                target::Union{Nothing,Symbol} = nothing) =
    [η for η in transformations(; source, target) if η.applies(cm, net)]

"""
    transformation(name::Symbol) -> NaturalTransformation

The registered natural transformation called `name`; an `ArgumentError` lists the registered
names if there is none.
"""
function transformation(name::Symbol)
    all_ = transformations()
    k = findfirst(η -> η.name === name, all_)
    k === nothing && throw(ArgumentError(
        "no natural transformation :$(name) is registered (registered: " *
        "$(isempty(all_) ? "none" : _list([η.name for η in all_])))"))
    return all_[k]
end

# ---------------------------------------------------------------------------------------------
# Functions implemented by NetworkEpiCoreSymbolicsExt
# ---------------------------------------------------------------------------------------------

"""
    as_parameter(name::Symbol) -> Symbolics.Num
    as_parameter(r)                                   # Real, symbolic, or Expr rate

The symbolic parameter called `name` (NetworkEpiCoreSymbolicsExt): a Symbolics variable that
ModelingToolkit treats as a parameter when ModelingToolkitBase is loaded (it equals
`@parameters name`). This is the one helper by which every back end turns a `Symbol` rate into
a parameter. For a rate `r`: a number or a symbolic expression is returned as it is, and an
`Expr` rate becomes the symbolic expression with its parameters replaced by `as_parameter`
(pass `t = …` for a rate that depends on time). `as_parameter(:t)` is an error: `t` is time.
"""
function as_parameter end

"""
    vector_fields_equal(a::SymbolicODE, b::SymbolicODE; rename = :auto, rtol = 1e-10,
                        probes = 8, rng_seed = 1, max_renamings = 50_000) -> Bool

Whether two symbolic vector fields are equal up to a renaming of their coordinates
(NetworkEpiCoreSymbolicsExt). Parameters are matched by name.

- `rename = :auto`: names are compared without a time argument (`θ(t)` is `θ`) and without an
  MTK namespace prefix (`sys₊θ` is `θ`). If the two systems then have the same set of state
  names, the names are trusted: states are matched by name, so a field in which two states are
  swapped (S and I exchanged) is not equal. If the state names differ, a bijection between the
  coordinates is searched for (candidates are narrowed by evaluating each field on the
  diagonal, where all states are equal, which no renaming changes; its points lie in the box
  of every state), so equality under any renaming of the states is detected.
- `rename = :search`: as `:auto`, but the bijection is searched for even when the state names
  coincide (equality under any permutation of the states).
- `rename::AbstractDict`: an explicit map from names of `a` to names of `b` (states and
  parameters; unlisted names are kept).
- `rename = :none`: exact names.

Each pair of fields is compared component by component. The difference is expanded and its
terms are collected by monomial; a monomial cancels when its net coefficient is at most `rtol`
times the sum of the absolute values of its coefficients on the two sides (floating-point
netting), and every other one is kept however small it is, so a missing term 2e-13·S·I next to
0.1·I is a difference. The terms that remain are simplified exactly (constants folded, so
exp(0) = 1) and, where that is not conclusive (identities such as sin²x + cos²x = 1), evaluated
at `probes` seeded random points, where their sum must be at most `rtol` times the sum of their
absolute values. States are probed in (0.05, 0.95), parameters in (0.1, 1.0) and time `t` in
(0.1, 1000) on a log scale, unless a `domain` of `a` or `b` gives a box. When both give a box
for a coordinate, it is probed in their intersection (disjoint boxes are an `ArgumentError`);
the box of a state of `a` bounds the state of `b` that the renaming matches it with. Arguments
that are not `SymbolicODE`s go through `symbolic_ode`.

A difference that is 0 at every probe point is read as equality only when the probes are
evidence of that; otherwise it is an error (the answer is unknown, not `false`):

- every term of the difference that does not cancel must be non-zero at some probe point. A
  term that is 0 at every one of them (one that vanishes on the probe box but not everywhere,
  such as ν·ifelse(t > 150, 1, 0) with t probed below 150 or max(a − 2, 0) with a below 2, or
  one too small to evaluate) is not seen, and the other terms may cancel without it, as in
  sin²x + cos²x − 1 + max(a − 2, 0)·x;
- the cancellation must hold whatever values the non-analytic parts of the difference take.
  The probes are evidence of an identity between analytic expressions (arithmetic, powers,
  exp, log, sqrt, trigonometric and hyperbolic functions), which is 0 on the probe box only if
  it is 0 on the connected region around it where it stays analytic. A piecewise part (max,
  min, abs, ifelse, sign, floor, …, and any other function) can be constant on the probe box
  but not everywhere, so each is replaced by an unknown drawn afresh at every probe point, of
  either sign and of magnitude from 0.1 to 1000 (log scale; half of its probes negative):
  max(a − 2, 0)·(sin²x + cos²x) against max(a − 2, 0) is equal, but x/(1 + max(a − 2, 0))
  against x, max(x, 0) against x, ν·ifelse(t > 150, 1, 0) against ν·ifelse(t > 151, 1, 0), or
  sqrt(g²)·x against g·x for g = ifelse(a > 2, −1, 1) (equal only while g > 0) is undecided.
  This is conservative: an identity that holds only for the values the part can take, such as
  sqrt(max(u, 0)²) = max(u, 0), is undecided too; write the field without the part.

The probes confirm an analytic identity on the probe box and on the connected region around it
where the difference stays analytic, but not across a branch point outside the box:
sqrt((2 − a)²)·x against (2 − a)·x is equal on the default box a ∈ (0.1, 1.0), although the two
differ for a > 2. The default parameter box is narrow (rates and κ above 1 are common), so give
a `domain` that covers the parameter values of interest.

A difference that is not finite at a probe point (unless another probe point shows that the
fields differ) is an `ArgumentError` asking for a `domain` on which both fields are defined.

The bijection search tries at most `max_renamings` (default 50 000) complete assignments of the
states. Fields too symmetric to tell their states apart can exhaust it; that is an error (the
answer is unknown, not `false`) asking for `rename = Dict(…)`. In the search, a field value that
is not finite (a field evaluated outside the region where it is defined) is no evidence either
way: it rules out no renaming, and a renaming that nothing rules out is decided by comparing
the renamed fields as above. So equal fields are found even where they are not finite at some
points, and a renaming that the probes cannot decide gives the `ArgumentError` above, not
`false`.
"""
function vector_fields_equal end

"""
    check_naturality(η::NaturalTransformation, A, B; network, on = nothing, glued = nothing,
                     method = :auto, probes = 16, rng_seed = 1, rtol = 1e-10)
        -> VerificationResult

Check that the natural transformation `η` commutes with gluing (NetworkEpiCoreSymbolicsExt),
for open models `A` and `B` glued on the species `on`: the glued model is `glue(A, B; on)`, so
`on = nothing` (the default) is `glue`'s own default, every species name exposed on a leg of
both parts; pass `glued` to give the glued model instead. With C the glued model and
m_X = η.component(X, network):

1. the components m_A, m_B and m_C each [`verify`](@ref);
2. the source functor is strict on this gluing: the source field of m_C is the sum of those of
   m_A and m_B on shared coordinates (and likewise the target), which is the open-system
   composition of §D.3;
3. the maps agree: m_C's map restricted to the target coordinates of A (of B) is m_A's (m_B's).

Coordinates are matched by name, so this applies to gluing on shared names (no namespacing).
`η.component` must accept each part. Returns one `VerificationResult` whose `details` list every
failed check. A comparison that the probes cannot decide (a difference that is 0 at every probe
point without the probes being evidence that it is 0, or that is not finite at one; see
[`vector_fields_equal`](@ref)) is a failed check.
"""
function check_naturality end
