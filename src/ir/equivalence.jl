# Owner: WP6 (DESIGN_NetworkEpiCore.md §B.3; work package in §G.2). Edited by the NEC steward
# (§J.3: the evidence rule for rate comparisons).
#
# isequivalent: two models are equivalent when they have the same species, the same susceptible
# set, the same rate convention, and the same typed reactions up to order with equal rates.
# Rates are compared as functions of their parameters and time, so `:(p * σ)`, `:(σ * p)` and a
# symbolic `p*σ` are all equal. Names of the model and of the reactions, labels, defaults and
# provenance are not compared. An equality that the probes cannot establish is an error, never
# `false` or `true` (§J.3).

export isequivalent

"""
    isequivalent(a, b, more...; rtol = 1e-10, probes = 4) -> Bool

Whether the models are the same `ContactModel` up to order: the same species and susceptible
species (as sets), the same [`RateConvention`](@ref), and the same reactions (contacts keyed by
recipient, infector, product and layer; transitions by source and target) with equal rates.
With Σ fixed the typing is unique, so equal reactions are equally typed. Model and reaction
names, labels, defaults and provenance are ignored. Arguments that are not `ContactModel`s go
through `contact_model`.

Rates are equal when they are the same function of their parameters and of time t, which
decides algebraic identities such as `:((1 - p) * σ) == :(σ - p * σ)` and compares a `Symbol`
rate with a symbolic one. The rule is that of `vector_fields_equal` (§J.3):

- With the Symbolics extension loaded (`using Symbolics`), two rates that are not identical are
  compared exactly where possible (after folding constants) and otherwise at `max(probes, 8)`
  seeded probe points (parameters in (0.1, 1.0), t in (0.1, 1000) on a log scale), where the
  probes must be *evidence*: every term of the difference that does not cancel must be non-zero
  at some probe point, and the cancellation must hold whatever values the non-analytic parts
  (`min`, `max`, …) take. So `:γ` and `:(γ + ν * max(t - 1, 0))` are different (the term is seen
  for t > 1), while `:(max(τ, 0))` against `:τ` cannot be decided on probes.
- Without it, both rates are evaluated at `probes` seeded points (the same boxes). A point where
  they differ decides that they are different; agreement at every point is evidence of equality
  only for rates without `min`/`max` (an analytic difference that is 0 on an open box is 0).

When the answer cannot be decided (a non-analytic part, a term that is 0 at every probe point,
or rates that cannot be evaluated at the probes), `isequivalent` throws an `ArgumentError` that
says why: the answer is unknown, not `false`. A reaction pair that is decidably different makes
the result `false` even when another pair is undecided.
"""
function isequivalent(a::ContactModel, b::ContactModel; rtol::Real = 1e-10, probes::Int = 4)
    Set(a.species) == Set(b.species) || return false
    Set(a.susceptible) == Set(b.susceptible) || return false
    a.convention == b.convention || return false
    vc = _same_reactions(a.contacts, b.contacts; rtol, probes)
    vc === :different && return false
    vt = _same_reactions(a.transitions, b.transitions; rtol, probes)
    vt === :different && return false
    for v in (vc, vt)
        v === :equal || throw(_undecided_rates_error(a, b, v))
    end
    return true
end
isequivalent(a, b; kw...) = isequivalent(contact_model(a), contact_model(b); kw...)
isequivalent(a, b, c, more...; kw...) =
    isequivalent(a, b; kw...) && isequivalent(a, c, more...; kw...)

# :equal, :different, or the first undecided rate comparison (a NamedTuple with the reaction
# and the verdict).
function _same_reactions(ra, rb; rtol, probes)
    length(ra) == length(rb) || return :different
    da = Dict(_shape(r) => r for r in ra)
    db = Dict(_shape(r) => r for r in rb)
    keys(da) == keys(db) || return :different
    undecided = nothing
    for k in keys(da)
        v = _rates_verdict(da[k].rate, db[k].rate; rtol, probes)
        v.verdict === :different && return :different
        (v.verdict === :undecided && undecided === nothing) &&
            (undecided = (reaction = da[k], other = db[k], verdict = v))
    end
    return something(undecided, :equal)
end

function _undecided_rates_error(a::ContactModel, b::ContactModel, u)
    x, y = u.reaction.rate, u.other.rate
    return ArgumentError(
        "isequivalent(:$(a.name), :$(b.name)): cannot decide whether the rates " *
        "`$(_rate_string(x))` and `$(_rate_string(y))` of the reaction $(_arrow_string(u.reaction)) " *
        "are equal; the answer is unknown, not false: the difference $(u.verdict.why_text)")
end

# Are the rates x and y equal? Returns (verdict = :equal | :different | :undecided, why_text).
function _rates_equal(x, y; rtol = 1e-10, probes = 4)
    v = _rates_verdict(x, y; rtol, probes)
    v.verdict === :undecided && throw(ArgumentError(
        "cannot decide whether the rates `$(_rate_string(x))` and `$(_rate_string(y))` are " *
        "equal; the answer is unknown, not false: the difference $(v.why_text)"))
    return v.verdict === :equal
end

_rate_verdict(v::Symbol, why_text::AbstractString = "") = (verdict = v, why_text = String(why_text))

function _rates_verdict(x, y; rtol = 1e-10, probes = 4)
    if _isnum(x) && _isnum(y)
        return _rate_verdict((isapprox(x, y; rtol, atol = 0) || (iszero(x) && iszero(y))) ?
                             :equal : :different)
    end
    isequal(x, y) && return _rate_verdict(:equal)
    ext = Base.get_extension(@__MODULE__, :NetworkEpiCoreSymbolicsExt)
    if ext !== nothing
        n = max(probes, 8)
        v = ext._expressions_verdict(x, y; rtol, probes = n)
        v.verdict === :undecided || return _rate_verdict(v.verdict)
        return _rate_verdict(:undecided, ext._undecided_why(v.why, v.what, n))
    end
    return _probe_rates_verdict(x, y; rtol, probes)
end

# Without the Symbolics extension: evaluate both rates at seeded probe points (parameters from
# (0.1, 1), t from (0.1, 1000) on a log scale, stratified so that early and late times are both
# probed). A point where they differ, relative to the size of their terms, decides "different".
# Agreement everywhere is evidence of equality only for analytic rates (RATE_OPS without min and
# max): an analytic difference that vanishes on an open box vanishes identically.
function _probe_rates_verdict(x, y; rtol = 1e-10, probes = 4)
    names = union(Symbol[_parameter_name(p) for p in rate_parameters(x)],
                  Symbol[_parameter_name(p) for p in rate_parameters(y)])
    timed = _uses_time(x) || _uses_time(y)
    rng = Random.Xoshiro(0x6e6563)
    seen = 0
    for j in 1:probes
        p = Dict{Symbol,Float64}(n => 0.1 + 0.9 * rand(rng) for n in names)
        t = timed ? 0.1 * 10_000.0^((j - 1 + rand(rng)) / probes) : nothing
        vx, gx = _probe_value(x, p, t)
        vy, gy = _probe_value(y, p, t)
        (isfinite(vx) && isfinite(vy)) || continue
        seen += 1
        tol = rtol * max(gx, gy)
        (abs(vx - vy) <= tol || vx == vy) || return _rate_verdict(:different)
    end
    seen == 0 && return _rate_verdict(:undecided,
        "cannot be evaluated at any of the $(probes) probe points (load Symbolics to compare " *
        "the rates symbolically)")
    if _has_nonanalytic(x) || _has_nonanalytic(y)
        return _rate_verdict(:undecided,
            "is 0 at the $(probes) probe points, but min and max are not analytic, so the probes " *
            "are no evidence that it is 0 elsewhere (load Symbolics, whose comparison treats " *
            "them as unknowns of either sign)")
    end
    return _rate_verdict(:equal)
end

# The value of a rate at a probe point, and its gross size (the value with every sum taken over
# absolute values), which scales the tolerance to the cancellation in the rate. A point outside
# the rate's real domain gives NaN.
function _probe_value(r, p, t)
    try
        return Float64(rate_value(r, p; t)), _gross_value(r, p, t)
    catch err
        err isa DomainError || rethrow()
        return NaN, NaN
    end
end

_gross_value(r::Real, p, t) = abs(Float64(r))
_gross_value(r::Symbol, p, t) = abs(Float64(r === :t ? t : p[r]))
function _gross_value(ex::Expr, p, t)
    op = ex.args[1]
    args = ex.args[2:end]
    op in (:+, :-) && return sum(a -> _gross_value(a, p, t), args)
    op === :* && return prod(a -> _gross_value(a, p, t), args)
    op === :/ && return _gross_value(args[1], p, t) / abs(Float64(rate_value(args[2], p; t)))
    return abs(Float64(rate_value(ex, p; t)))
end
_gross_value(r, p, t) = abs(Float64(rate_value(r, p; t)))

_has_nonanalytic(r::Expr) = r.args[1] in (:min, :max) || any(_has_nonanalytic, r.args[2:end])
_has_nonanalytic(r) = false
