# Owner: WP10 (DESIGN_NetworkEpiCore.md §A.2, §B.5; work package in §G.2).
# Triggered by ModelingToolkitBase + Symbolics.
#
# `contact_model(sys::ModelingToolkitBase.System; …)`: the ModelingToolkit front end, by flux
# pairing (§B.5, prototype proto_mtk.jl). The right-hand sides are expanded into additive terms;
# every term must be a first-order flux a·Y or a bilinear flux τ·Y·Z of the unknowns. Terms are
# grouped by their monomial (Y, or Y·Z), and for each monomial the coefficients in the equations
# are paired: the unknowns that lose it against those that gain it.
#
# - a·Y lost by D(Y) and gained by D(Z): the transition Y → Z at a; an unmatched remainder of the
#   loss is the removal Y → ∅;
# - τ·Y·Z lost by D(Y) only: a contact with recipient Y and infector Z (Z is catalytic: D(Z) does
#   not lose it), one contact per unknown that gains it (D(Z) itself gaining it gives Y + Z → 2Z);
# - a term lost by both D(Y) and D(Z) is ambiguous (an infector that changes state, or several
#   contacts sharing one flux): an error asks for `contacts = [...]`; unmatched gains are births;
# - reactions given explicitly (`contacts`, `transitions`) are checked against the ODE (each must
#   be one of its fluxes, see _check_explicit) and taken out before the rest is paired.
#
# Grouping by monomial (rather than pairing single terms, as §B.5 step 3 sketches) handles
# expansions such as (1 − p)σE = σE − pσE and a loss −2γI split between two gains. It nets the
# gains and losses of one monomial in one equation, so every coefficient must have a sign that
# does not depend on the parameters (see "Signs of coefficients"): the S-catalysed recovery ODE
# D(I) = τSI − δSI (S + I → 2I with I + S → R + S) gives the coefficient τ − δ and is an error that
# asks for `contacts = [δ*I*S => (:I, :R, :S)]`; with numeric rates (0.5 − 0.2 = 0.3) it is read
# as the contacts S + I → I + I and S + I → R + I, which give the same ODE, and the node-catalysed
# reading is named in the provenance. Netting is exact up to floating point: a coefficient is
# kept as its parts in the parameters, each with its net and its gross numeric coefficient, and
# only a part that nets to at most 1e-12 of its gross coefficient is read as 0, so small rates
# (per-pair rates of counts ODEs) are never dropped (see "Coefficients"). Every decision is
# written to the provenance assumptions: the ODE fixes one network compatible with it, not a
# unique one (F3), so Catalyst is the canonical front end.
#
# Also `_toparam`, used by NetworkEpiCoreSymbolicsExt.as_parameter to mark a variable as an MTK
# parameter.
module NetworkEpiCoreMTKExt

import NetworkEpiCore
import NetworkEpiCore: ContactModel, Contact, NodeTransition, Provenance, PerContact,
                       FrequencyDependent, DensityDependent
import ModelingToolkitBase
import Symbolics
import Random

const NEC = NetworkEpiCore
const MB = ModelingToolkitBase
const SU = Symbolics.SymbolicUtils

# Mark a variable as a ModelingToolkit parameter (called by NetworkEpiCoreSymbolicsExt).
_toparam(v) = MB.toparam(v)

# ---------------------------------------------------------------------------------------------
# Expression utilities (the Symbolics extension has its own copies; extensions share no code)
# ---------------------------------------------------------------------------------------------

_unwrap(x) = Symbolics.unwrap(x)
_wrap(x) = x isa SU.BasicSymbolic ? Symbolics.wrap(x) : x

function _isvariable(x)
    x isa SU.BasicSymbolic || return false
    SU.issym(x) && return true
    if SU.iscall(x)
        op = SU.operation(x)
        op isa SU.BasicSymbolic && SU.issym(op) && return true
    end
    return false
end

function _variables!(out::Vector{Any}, x)
    x = _unwrap(x)
    x isa SU.BasicSymbolic || return out
    if _isvariable(x)
        any(y -> isequal(y, x), out) || push!(out, x)
    elseif SU.iscall(x)
        for a in SU.arguments(x)
            _variables!(out, a)
        end
    end
    return out
end
_variables(x) = _variables!(Any[], x)

_name(v) = Symbol(Symbolics.getname(_unwrap(v)))

function _number(x)
    x = _unwrap(x)
    if x isa SU.BasicSymbolic
        SU.isconst(x) || return nothing
        x = SU.unwrap_const(x)
    end
    return x isa Number ? x : nothing
end

_iszero_const(x) = (n = _number(x); n !== nothing && iszero(n))

# Fold the constant subexpressions of x (exp(0) → 1.0, log(1) → 0). Without folding, exp(0)·τ − τ
# does not simplify to 0.
_fold(x) = Symbolics.substitute(_wrap(_unwrap(x)), Dict{Any,Any}(); fold = Val(true))

# Is r identically 0? Exact: the constants are folded, then the expression is expanded and
# simplified. Numeric probes never decide this.
function _symbolic_zero(r)
    _number(r) !== nothing && return _iszero_const(r)
    try
        e = Symbolics.expand(_fold(r))
        _iszero_const(e) && return true
        s = Symbolics.simplify(e; expand = true)
        _iszero_const(s) && return true
        return _iszero_const(Symbolics.simplify_fractions(s))
    catch
        return false
    end
end

_isop(x, f) = x isa SU.BasicSymbolic && SU.iscall(x) && SU.operation(x) === f

# The additive terms of an expanded expression; a quotient whose numerator is a sum is split
# (expand does not distribute over division).
function _additive_terms(x)
    x = _unwrap(x)
    _iszero_const(x) && return Any[]
    if _isop(x, +)
        out = Any[]
        for a in SU.arguments(x)
            append!(out, _additive_terms(a))
        end
        return out
    elseif _isop(x, /)
        num, den = SU.arguments(x)
        ts = _additive_terms(Symbolics.expand(_wrap(num)))
        length(ts) > 1 &&
            return Any[_unwrap(Symbolics.wrap(t) / Symbolics.wrap(den)) for t in ts]
    end
    return Any[x]
end

# ---------------------------------------------------------------------------------------------
# Converting a symbolic coefficient to an IR rate (Real | Symbol | Expr, else symbolic)
# ---------------------------------------------------------------------------------------------

const _OPS = Dict{Any,Symbol}((+) => :+, (*) => :*, (-) => :-, (/) => :/, (^) => :^,
                              exp => :exp, log => :log, min => :min, max => :max)

# A term's numeric coefficient and the rest (for writing a - b instead of a + -1*b).
function _negated(x)
    n = _number(x)
    n !== nothing && return n < 0 ? -n : nothing
    if _isop(x, *)
        args = SU.arguments(x)
        c = _number(first(args))
        (c !== nothing && c < 0) || return nothing
        return _unwrap(-Symbolics.wrap(x))
    end
    return nothing
end

function _to_expr(x)
    x = _unwrap(x)
    n = _number(x)
    n !== nothing && return n
    x isa SU.BasicSymbolic || return nothing
    SU.issym(x) && return _name(x)
    SU.iscall(x) || return nothing
    op = SU.operation(x)
    haskey(_OPS, op) || return nothing
    args = SU.arguments(x)
    if op === (+)
        pos = Any[]
        neg = Any[]
        for a in args
            m = _negated(a)
            m === nothing ? push!(pos, a) : push!(neg, m)
        end
        isempty(pos) && return nothing
        acc = _to_expr(first(pos))
        acc === nothing && return nothing
        for a in pos[2:end]
            e = _to_expr(a)
            e === nothing && return nothing
            acc = Expr(:call, :+, acc, e)
        end
        for a in neg
            e = _to_expr(a)
            e === nothing && return nothing
            acc = Expr(:call, :-, acc, e)
        end
        return acc
    end
    es = Any[_to_expr(a) for a in args]
    any(isnothing, es) && return nothing
    if op === (*) && length(es) >= 2 && es[1] isa Real && es[1] == -1
        return Expr(:call, :-, length(es) == 2 ? es[2] : Expr(:call, :*, es[2:end]...))
    end
    return Expr(:call, _OPS[op], es...)
end

function _ir_rate(c)
    x = _unwrap(c)
    n = _number(x)
    n !== nothing && return n isa Integer ? n : Float64(n)
    e = _to_expr(x)
    return e === nothing ? Symbolics.wrap(x) : e
end

# ---------------------------------------------------------------------------------------------
# Coefficients
# ---------------------------------------------------------------------------------------------
#
# The coefficient of one monomial of the unknowns (Y, or Y·Z) in one equation is the sum of the
# terms collected from the ODE and from the explicit reactions. It is kept as its parts in the
# parameters, each a monomial m with its net numeric coefficient and its gross one (the sum of the
# absolute values of the numeric coefficients that were added): adding the terms 0.5τ and −0.2τ
# gives the part τ with net 0.3 and gross 0.7, and adding 0.1 + 0.2 (merged by Symbolics into
# 0.30000000000000004) and −0.3 gives the part 1 with net 5.6e-17 and gross 0.6. A part whose
# net is at most _REL_TOL times its gross is floating-point netting and is read as 0. The test is
# relative, so a real rate is kept however small it is (the per-pair rate 5.6e-13 of an SIR ODE
# in counts), and a part that comes from a single term is never dropped. (Symbolics merges like
# terms of one expression when it is built: 0.1τ + 0.2τ − 0.3τ written in one equation is the
# single term 5.6e-17τ, which is kept.)

const _REL_TOL = 1e-12

struct _Coef
    monomials::Vector{Any}
    net::Vector{Number}
    gross::Vector{Float64}
end

_nocoef() = _Coef(Any[], Number[], Float64[])

function _push_part!(c::_Coef, m, net, gross)
    i = findfirst(x -> isequal(x, m), c.monomials)
    if i === nothing
        push!(c.monomials, m)
        push!(c.net, net)
        push!(c.gross, gross)
    else
        c.net[i] += net
        c.gross[i] += gross
    end
    return c
end

# A term of an expanded expression as (numeric coefficient, monomial in the other variables).
function _split_part(x)
    x = _unwrap(x)
    n = _number(x)
    n !== nothing && return n, 1
    if _isop(x, *)
        k = 1
        rest = Any[]
        for a in SU.arguments(x)
            m = _number(a)
            m === nothing ? push!(rest, a) : (k *= m)
        end
        isempty(rest) && return k, 1
        return k, length(rest) == 1 ? _unwrap(rest[1]) : _unwrap(prod(Symbolics.wrap, rest))
    elseif _isop(x, /)
        num, den = SU.arguments(x)
        k, m = _split_part(num)
        return k, _unwrap(Symbolics.wrap(m) / Symbolics.wrap(den))
    end
    return 1, x
end

# The coefficient of an expression, split into its parts.
function _coef(x)
    c = _nocoef()
    x = _unwrap(x)
    e = _number(x) === nothing ? Symbolics.expand(_wrap(x)) : x
    for u in _additive_terms(e)
        k, m = _split_part(u)
        _push_part!(c, m, k, Float64(abs(k)))
    end
    return c
end

function Base.:+(a::_Coef, b::_Coef)
    c = _Coef(copy(a.monomials), copy(a.net), copy(a.gross))
    for i in eachindex(b.monomials)
        _push_part!(c, b.monomials[i], b.net[i], b.gross[i])
    end
    return c
end
Base.:-(a::_Coef) = _Coef(copy(a.monomials), Number[-x for x in a.net], copy(a.gross))
Base.:-(a::_Coef, b::_Coef) = a + (-b)

_isresidue(net, gross) = iszero(net) || abs(net) <= _REL_TOL * gross

# The value of a coefficient, with its floating-point residues read as 0.
function _value(c::_Coef)
    acc = Symbolics.Num(0)
    for i in eachindex(c.monomials)
        _isresidue(c.net[i], c.gross[i]) && continue
        acc += c.net[i] * Symbolics.wrap(c.monomials[i])
    end
    return acc
end
_ir_rate(c::_Coef) = _ir_rate(_value(c))

# Does the sum of the expressions net to 0 (exactly, or up to floating-point residues)?
_nets_to_zero(xs) = (c = sum(_coef, xs; init = _nocoef());
                     all(i -> _isresidue(c.net[i], c.gross[i]), eachindex(c.net)))

# ---------------------------------------------------------------------------------------------
# Signs of coefficients
# ---------------------------------------------------------------------------------------------
#
# A coefficient is an expression in the parameters (and in t, with allow_t). Its sign decides the
# pairing (who loses a flux and who gains it), so it must be the same for every admissible value
# of the parameters; a coefficient whose sign depends on them is an error, never a guess.
#
# 0. A coefficient is 0 only when that is exact: a number 0, a sum of floating-point netting
#    residues (see "Coefficients"), or an expression that is 0 symbolically after folding its
#    constants. The probes below never decide that a coefficient is 0 (§J.3): one that is 0 at
#    every probe point but not provably 0, such as ν·ifelse(t > 150, 1, 0) or max(p − 1, 0) on
#    the box (or an identity that the simplifier cannot prove, (exp(log p) − p)·ν), is never
#    dropped.
# 1. By its form: an expression built from positive numbers and variables with +, *, /, ^, exp
#    and sqrt is positive for all positive values of its variables (every parameter is taken to
#    be positive; a negative parameter default is an error), and its negation is negative.
# 2. Otherwise numerically, on a deterministic probe set of the box of its k variables, [0.1, 0.9]
#    for a parameter and the time box for time t (allow_t; [0.1, 1000] on a log scale unless
#    `time_box` says otherwise): the grid of the lower ends, centres and upper ends for k ≤ 6
#    (every vertex, edge midpoint and the centre); every vertex and the centre for 7 ≤ k ≤ 10;
#    1024 seeded random vertices and the centre beyond; plus 32 seeded interior points. The box
#    reads each parameter as a rate or a fraction, so that (1 − p)σ is positive while τ − δ is
#    not (and τ·cos(t) is not). The comparisons with 0 are relative: at each point the
#    coefficient is 0 when it is at most _REL_TOL times the sum of the absolute values of its
#    additive terms there, so the verdict does not change when every rate is scaled by 1e-13.
#    A coefficient that is positive at some points and negative at others has no sign (an
#    error). One that is positive at some points and 0 at the others is positive: a rate needs
#    to be non-negative, not strictly positive, so a rate switched on at t = 150 is the gain of
#    its product (and a negative one, likewise, is a loss). One that is 0 at every point has no
#    sign that the probes can read; step 3 may give it one, and otherwise it is an error.
#    A sign read this way is written to the provenance.
# 3. The strictly positive parameter defaults, as one more point, must not give the opposite
#    sign, and they give the sign of a coefficient that is 0 at every point of the box. A default
#    of 0 switches a flux off; it is not used as a probe value (the flux ν·S of a vaccination rate
#    ν = 0 is still the transition S → V).

const _PROBE_BOX = (0.1, 0.9)
const _TIME_BOX = (0.1, 1000.0)
const _PROBE_SEED = 0x6d746b

# The state of the sign decisions of one call: the strictly positive defaults, the time variable
# (named t: the system's independent variable, renamed to t if it has another name) and its
# probe box, a cache by coefficient, and notes for the provenance (signs read numerically;
# alternative readings; floating-point residues read as 0).
struct _Probes
    defaults::Dict{Symbol,Float64}
    iv::Any
    time::Any
    time_box::Tuple{Float64,Float64}
    cache::Dict{Any,Any}
    notes::Vector{String}
end

# The IR's time is the variable named t (NetworkEpiCoreSymbolicsExt detects time by that name):
# an independent variable with another name, such as s, is renamed to t in every rate.
function _probes(defaults::Dict{Symbol,Float64}, iv, time_box = _TIME_BOX)
    iv = _unwrap(iv)
    time = _name(iv) === :t ? iv : _unwrap(Symbolics.variable(:t))
    return _Probes(Dict{Symbol,Float64}(k => v for (k, v) in defaults if v > 0), iv, time,
                   (Float64(time_box[1]), Float64(time_box[2])), Dict{Any,Any}(), String[])
end

# A coefficient (free of the unknowns) with the independent variable renamed to t.
_retime(c, P::_Probes) = isequal(P.iv, P.time) ? c :
    _unwrap(Symbolics.substitute(_wrap(_unwrap(c)), Dict{Any,Any}(P.iv => P.time)))

_note!(P::_Probes, note) = (note in P.notes || push!(P.notes, note); P)

# The probe box of a variable, and whether it is sampled on a log scale (time, on a box that
# starts above 0, so that t = 0.1, 10 and 1000 are all probed).
function _box(v, P::_Probes)
    isequal(v, P.time) || return (_PROBE_BOX, false)
    return (P.time_box, P.time_box[1] > 0)
end

# The point of a box at the unit coordinate u.
_at(((lo, hi), logscale), u) = logscale ? lo * (hi / lo)^u : lo + (hi - lo) * u

# "p, σ ∈ [0.1, 0.9] and t ∈ [0.1, 1000.0] (log scale)"
function _where_text(names, boxes)
    parts = String[]
    for b in unique(boxes)
        nm = join(names[[i for i in eachindex(names) if boxes[i] == b]], ", ")
        push!(parts, "$(nm) ∈ [$(b[1][1]), $(b[1][2])]" * (b[2] ? " (log scale)" : ""))
    end
    return join(parts, " and ")
end

# Positive for all positive values of its variables, by the form of the expression alone.
function _manifestly_positive(x)
    x = _unwrap(x)
    n = _number(x)
    n !== nothing && return n isa Real && n > 0
    x isa SU.BasicSymbolic || return false
    _isvariable(x) && return true
    SU.iscall(x) || return false
    op = SU.operation(x)
    args = SU.arguments(x)
    (op === (+) || op === (*) || op === (/)) && return all(_manifestly_positive, args)
    op === (^) && return _manifestly_positive(args[1])      # b^e > 0 for b > 0 and real e
    op === sqrt && return _manifestly_positive(args[1])
    return op === exp
end

# The probe points of §2 above in unit coordinates (0 and 1 are the ends of each box), one
# value per variable.
function _probe_points(k::Int)
    lo, mid, hi = 0.0, 0.5, 1.0
    pts = Vector{Float64}[]
    if k <= 6
        for v in Iterators.product(ntuple(_ -> (lo, mid, hi), k)...)
            push!(pts, collect(Float64, v))
        end
    elseif k <= 10
        for v in Iterators.product(ntuple(_ -> (lo, hi), k)...)
            push!(pts, collect(Float64, v))
        end
        push!(pts, fill(mid, k))
    else
        rng = Random.Xoshiro(_PROBE_SEED)
        for _ in 1:1024
            push!(pts, Float64[rand(rng, Bool) ? hi : lo for _ in 1:k])
        end
        push!(pts, fill(mid, k))
    end
    rng = Random.Xoshiro(_PROBE_SEED + 1)
    for _ in 1:32
        push!(pts, Float64[rand(rng) for _ in 1:k])
    end
    return pts
end

# The value of x under the substitution `sub` (NaN when it is not a finite real number there).
function _value_at(x, sub::AbstractDict)
    v = try
        _number(Symbolics.substitute(_wrap(x), sub; fold = Val(true)))
    catch
        nothing
    end
    (v isa Number && isreal(v)) || return NaN
    return Float64(real(v))
end

# The value at a point of the sum of the additive terms `parts`, and its scale (the sum of the
# absolute values of the terms there), for the relative comparisons with 0.
function _value_scale(parts, vars, point)
    sub = Dict{Any,Any}(v => p for (v, p) in zip(vars, point))
    v = 0.0
    s = 0.0
    for u in parts
        y = _value_at(u, sub)
        v += y
        s += abs(y)
    end
    return v, s
end

_fmt(v) = string(round(v; sigdigits = 3))
_point_text(names, point) = join(["$(n) = $(_fmt(v))" for (n, v) in zip(names, point)], ", ")

# The sign of a coefficient: (sign, how, text), with sign ∈ {1, -1, 0} or 2 (not decidable).
# `how` is :number, :form or :zero (exact), :probes (read numerically), or, for sign 2,
# :indefinite (both signs occur), :defaults (the defaults contradict the probes), :vanishes (0 at
# every probe point, but not provably 0) or :undefined; `text` says what the probes found.
# Sign 0 is only ever exact (step 0 above).
_classify(c::_Coef, P::_Probes) = _classify(_value(c), P)

function _classify(c, P::_Probes)
    x = _unwrap(c)
    x isa SU.BasicSymbolic && (x = _unwrap(Symbolics.expand(_wrap(x))))
    return get!(() -> _classify_uncached(x, P), P.cache, x)
end

_signword(s) = s > 0 ? "positive" : "negative"

function _classify_uncached(x, P::_Probes)
    n = _number(x)
    if n !== nothing
        isreal(n) || return (2, :undefined, "it is not real")
        return (iszero(n) ? 0 : Int(sign(Float64(real(n)))), :number, "")
    end
    _manifestly_positive(x) && return (1, :form, "")
    _manifestly_positive(Symbolics.expand(-_wrap(x))) && return (-1, :form, "")
    _symbolic_zero(x) && return (0, :zero, "")
    # not provably 0 (the simplifier cannot show it): from here on it is never read as 0
    parts = _additive_terms(x)
    vars = sort!(_variables(x); by = v -> string(_name(v)))
    names = Symbol[_name(v) for v in vars]
    boxes = [_box(v, P) for v in vars]
    pts = [Float64[_at(b, u) for (b, u) in zip(boxes, pt)] for pt in _probe_points(length(vars))]
    vs = [_value_scale(parts, vars, p) for p in pts]
    vals = first.(vs)
    tols = _REL_TOL .* last.(vs)
    bad = findfirst(!isfinite, vals)
    bad === nothing ||
        return (2, :undefined, "it is not a finite real number at $(_point_text(names, pts[bad]))")
    pos(i) = vals[i] > tols[i]
    neg(i) = vals[i] < -tols[i]
    idx = eachindex(vals)
    npos, nneg, N = count(pos, idx), count(neg, idx), length(pts)
    if npos > 0 && nneg > 0
        i, j = findfirst(pos, idx), findfirst(neg, idx)
        return (2, :indefinite,
                "$(_fmt(vals[i])) at $(_point_text(names, pts[i])) but $(_fmt(vals[j])) at " *
                "$(_point_text(names, pts[j]))")
    end
    s = npos > 0 ? 1 : nneg > 0 ? -1 : 0         # 0 here: it vanishes at every probe point
    where = _where_text(names, boxes)
    found = s == 0 ? "0 at all $(N) probe points with $(where)" :
            npos + nneg == N ? "$(_signword(s)) at all $(N) probe points with $(where)" :
            "$(_signword(s)) at $(npos + nneg) of the $(N) probe points and 0 at the other " *
            "$(N - npos - nneg), with $(where)"
    if any(nm -> haskey(P.defaults, nm), names)
        d = Float64[get(P.defaults, nm, _at(b, 0.5)) for (nm, b) in zip(names, boxes)]
        v, sc = _value_scale(parts, vars, d)
        given = [i for i in eachindex(names) if haskey(P.defaults, names[i])]
        rest = [i for i in eachindex(names) if !haskey(P.defaults, names[i])]
        at = _point_text(names[given], d[given]) *
             (isempty(rest) ? "" : "; " * join(["$(names[i]) at $(_fmt(d[i]))" for i in rest],
                                               ", ") * ", with no positive default")
        sd = !isfinite(v) ? 2 : v > _REL_TOL * sc ? 1 : v < -_REL_TOL * sc ? -1 : 0
        if sd == 2 || (s != 0 && sd == -s)
            onbox = s == 0 ? "0" : npos + nneg == N ? _signword(s) : "non-" * _signword(-s)
            return (2, :defaults, "it is $(onbox) for $(where) but $(_fmt(v)) at the " *
                                  "parameter defaults ($(at))")
        elseif s == 0 && sd != 0
            # 0 on the whole box, but not at the defaults: the defaults give the sign
            return (sd, :probes, "0 at all $(N) probe points with $(where) but $(_fmt(v)) at " *
                                 "the parameter defaults ($(at))")
        end
        found *= sd == s ? " and at the parameter defaults" * (s == 0 ? " ($(at))" : "") :
                 ", and 0 at the parameter defaults ($(at))"
    end
    s == 0 && return (2, :vanishes, found)
    return (s, :probes, found)
end

# The escape hatch, for the reactions whose fluxes are proportional to the monomial `mono`.
_explicit_hint(mono) = "pass the reactions explicitly with contacts = [flux => (from, to, " *
                       "infector), …] and transitions = [flux => (from, to), …], listing every " *
                       "reaction whose flux is proportional to $(mono)"

_coef_value(c::_Coef) = _value(c)
_coef_value(c) = c

# +1, -1 or 0 (exactly zero); an error for a coefficient whose sign depends on the parameters,
# cannot be evaluated, or cannot be read because it is 0 on the whole probe box. `what` names
# the coefficient and `mono` the monomial of the unknowns that it multiplies. A sign read from
# the probes is noted for the provenance.
function _sign(c, P, name, what, mono)
    mono = string(mono)
    s, how, text = _classify(c, P)
    (s == 2 || how === :probes) || return s
    shown = _show(_coef_value(c))
    if s == 2
        head = "contact_model(:$(name)): the sign of the coefficient `$(shown)` of $(what)"
        hint = _explicit_hint(mono)
        timed = any(v -> isequal(v, P.time), _variables(_coef_value(c)))
        why = timed ?
              "a time-dependent rate cannot change sign on the time box t ∈ " *
              "[$(P.time_box[1]), $(P.time_box[2])] (pass time_box = the time span of the " *
              "solution if it is shorter)" :
              occursin('*', mono) ?
              "the ODE may net several reactions into one term (for example a contact and a " *
              "node-catalysed transition such as I + S → R + S)" :
              "a rate written as a difference of parameters, such as γ − m or (1 − q1 − q2)σ, " *
              "has no sign on the probe box"
        how === :indefinite && throw(ArgumentError(
            "$head depends on the parameters ($(text)): $(why); " * hint))
        how === :defaults && throw(ArgumentError(
            "$head cannot be fixed: $(text), and a rate cannot change sign; check the " *
            "defaults, or " * hint))
        how === :vanishes && throw(ArgumentError(
            "contact_model(:$(name)): the coefficient `$(shown)` of $(what) is not provably 0, " *
            "but it is $(text), so its sign cannot be read (a rate that is switched on " *
            "outside the probe box, such as ν*ifelse(t > 150, 1, 0) for t ≤ 100 or " *
            "max(p - 1, 0)*ν for p ≤ 1, is 0 there); a coefficient is read as 0 only when it " *
            "is exactly 0. Pass a time_box (for time-dependent rates) or parameter defaults " *
            "at which it is not 0, simplify it if it is 0, or " * hint))
        throw(ArgumentError("$head cannot be decided: $(text); " * hint))
    end
    _note!(P, "the sign of the coefficient `$(shown)` of $(what) is read numerically: " *
              "$(text) (its form alone does not fix it)")
    return s
end

# Exactly zero (a number 0, floating-point netting residues only, or 0 symbolically): never
# decided by the probes.
_iszero_coef(c, P) = first(_classify(c, P)) == 0

# The parts of a coefficient that are floating-point netting residues other than an exact 0 are
# read as 0; say so in the provenance, so that the decision is visible (a real removal within
# 1e-12 of the gross coefficient of its monomial would be read as netting).
function _residue_notes!(P::_Probes, c::_Coef, what, mono)
    for i in eachindex(c.monomials)
        (!iszero(c.net[i]) && _isresidue(c.net[i], c.gross[i])) || continue
        term = _flux_text(_ir_rate(c.net[i] * Symbolics.wrap(c.monomials[i])), mono)
        _note!(P, "floating-point netting: $(what) is `$(term)`, at most $(_REL_TOL) of the " *
                  "sum $(_fmt(c.gross[i])) of the absolute values of its terms, and is read as 0")
    end
    return P
end
_residue_notes!(P::_Probes, c, what, mono) = P

# ---------------------------------------------------------------------------------------------
# Display
# ---------------------------------------------------------------------------------------------

# Expressions printed without the time argument of their variables: `τ*S*I` rather than
# `τ*S(t)*I(t)`; the argument of a function such as cos(t) is kept.
function _show(x)
    x = _unwrap(x)
    s = string(_wrap(x))
    for v in _variables(x)
        (v isa SU.BasicSymbolic && SU.iscall(v)) || continue
        nm = string(_name(v))
        arg = join((string(_wrap(a)) for a in SU.arguments(v)), ", ")
        s = replace(s, Regex("(?<![\\p{L}\\p{N}_₊])\\Q$(nm)\\E\\(\\Q$(arg)\\E\\)") => nm)
    end
    return s
end

_rate_text(r) = (s = NEC._rate_string(r);
                 (r isa Expr && r.args[1] in (:+, :-)) ? "($s)" : s)

_flux_text(rate, Y) = string(_rate_text(rate), "*", Y)
_flux_text(rate, Y, Z) = string(_rate_text(rate), "*", Y, "*", Z)

# ---------------------------------------------------------------------------------------------
# The front end
# ---------------------------------------------------------------------------------------------

const _F3_NOTE = "flux pairing: the ODE fixes one network compatible with it, not a unique " *
                 "one (F3); Catalyst is the canonical front end"

function _differential_state(eq, iv)
    lhs = _unwrap(eq.lhs)
    lhs isa SU.BasicSymbolic && SU.iscall(lhs) || return nothing
    op = SU.operation(lhs)
    op isa Symbolics.Differential || return nothing
    (op.order == 1 && isequal(_unwrap(op.x), _unwrap(iv))) || return nothing
    return only(SU.arguments(lhs))
end

# The ODE right-hand sides D(X) ~ f by unknown, after eliminating algebraic and observed
# equations with mtkcompile/full_equations.
function _odes(sys, name, notes)
    iv = MB.get_iv(sys)
    iv === nothing && throw(ArgumentError(
        "contact_model(:$(name)): the system has no independent variable; an ODE system " *
        "D(X) ~ f(X) is needed"))
    eqs = MB.equations(sys)
    algebraic = any(eq -> _differential_state(eq, iv) === nothing, eqs)
    if algebraic
        compiled = try
            MB.mtkcompile(sys)
        catch err
            why = first(splitlines(sprint(showerror, err; context = :limit => true)))
            throw(ArgumentError(
                "contact_model(:$(name)): the system has algebraic equations and mtkcompile " *
                "failed ($(why)); call mtkcompile yourself and pass the compiled system"))
        end
        eqs = MB.full_equations(compiled)
        push!(notes, "algebraic and observed equations eliminated with mtkcompile (full_equations)")
    elseif !isempty(MB.observed(sys))
        eqs = MB.full_equations(sys)
        push!(notes, "observed equations substituted (full_equations)")
    end
    states = Any[]
    rhs = Any[]
    for (k, eq) in enumerate(eqs)
        X = _differential_state(eq, iv)
        X === nothing && throw(ArgumentError(
            "contact_model(:$(name)): equation $(k) (`$(_show(eq.lhs)) ~ $(_show(eq.rhs))`) " *
            "is not a first-order ODE D(X) ~ f"))
        push!(states, _unwrap(X))
        push!(rhs, _unwrap(eq.rhs))
    end
    return iv, states, rhs
end

# Does f depend on time other than through the unknowns (t itself, or a called parameter β(t))?
function _explicit_time(x, states, iv)
    x = _unwrap(x)
    x isa SU.BasicSymbolic || return false
    any(s -> isequal(s, x), states) && return false
    SU.issym(x) && return isequal(x, _unwrap(iv))
    SU.iscall(x) || return false
    op = SU.operation(x)
    op isa SU.BasicSymbolic && SU.issym(op) && return true      # a called variable, e.g. β(t)
    return any(a -> _explicit_time(a, states, iv), SU.arguments(x))
end

# Denominators that contain unknowns (for β*S*I/(S + I + R)).
function _state_denominators!(out, x, states)
    x = _unwrap(x)
    x isa SU.BasicSymbolic && SU.iscall(x) || return out
    args = SU.arguments(x)
    if _isop(x, /)
        d = _unwrap(args[2])
        if any(v -> any(s -> isequal(s, v), states), _variables(d))
            any(y -> isequal(y, d), out) || push!(out, d)
        end
    elseif _isop(x, ^)
        e = _number(args[2])
        b = _unwrap(args[1])
        if e !== nothing && e < 0 && any(v -> any(s -> isequal(s, v), states), _variables(b))
            any(y -> isequal(y, b), out) || push!(out, b)
        end
    end
    for a in args
        _state_denominators!(out, a, states)
    end
    return out
end

# β*S*I/N with N = S + I + R conserved: substitute N → 1 (the ODE read on fractions).
function _conserved_denominators!(rhs, states, snames, name, notes)
    dens = Any[]
    for f in rhs
        _state_denominators!(dens, f, states)
    end
    isempty(dens) && return false
    for d in dens
        ts = _additive_terms(Symbolics.expand(_wrap(d)))
        idx = [findfirst(s -> isequal(s, t), states) for t in ts]
        (all(!isnothing, idx) && allunique(idx)) || throw(ArgumentError(
            "contact_model(:$(name)): rates = :frequency: the denominator `$(_show(d))` is not " *
            "a sum of unknowns"))
        total = sum(Symbolics.wrap(rhs[i]) for i in idx)
        exact = _symbolic_zero(total)
        (exact || _nets_to_zero(rhs[idx])) || throw(ArgumentError(
            "contact_model(:$(name)): rates = :frequency: the population `$(_show(d))` is not " *
            "conserved (the sum of its equations is not 0), so the contact rates cannot be read " *
            "on fractions"))
        push!(notes, "N = $(join(snames[sort(idx)], " + ")) is conserved (its equations sum " *
                     "to 0$(exact ? "" : " up to floating-point netting")), so contact terms " *
                     "divided by N are read on fractions (N = 1): FrequencyDependent")
    end
    for i in eachindex(rhs)
        rhs[i] = _unwrap(Symbolics.expand(Symbolics.substitute(Symbolics.wrap(rhs[i]),
                                                              Dict{Any,Any}(d => 1 for d in dens))))
    end
    return true
end

# The monomial of a term: (indices of the unknowns, coefficient), or an error. The coefficient
# has the independent variable renamed to t (_retime).
function _monomial(u, k, states, snames, name, hint, P::_Probes)
    key, c = _monomial(u, k, states, snames, name, hint)
    return key, _retime(c, P)
end

function _monomial(u, k, states, snames, name, hint)
    vs = [v for v in _variables(u) if any(s -> isequal(s, v), states)]
    idx = sort!([findfirst(s -> isequal(s, v), states) for v in vs])
    bad(kind) = ArgumentError(
        "contact_model(:$(name)): the term `$(_show(u))` of D($(snames[k])) is not mass action " *
        "in the unknowns ($(kind)); the IR supports first-order transitions a*X and bilinear " *
        "contacts τ*X*J only" * hint)
    free(c) = !any(v -> any(s -> isequal(s, v), states), _variables(c))
    if isempty(idx)
        throw(ArgumentError(
            "contact_model(:$(name)): the term `$(_show(u))` of D($(snames[k])) involves no " *
            "unknown: births change the node set; use the ODE itself for mass action (a network " *
            "model has a fixed set of nodes)"))
    elseif length(idx) == 1
        Y = states[idx[1]]
        a, b, lin = Symbolics.linear_expansion(_wrap(u), _wrap(Y))
        (lin && _iszero_const(b) && free(a)) || throw(bad("not linear in $(snames[idx[1]])"))
        return (idx[1],), _unwrap(a)
    elseif length(idx) == 2
        Y, Z = states[idx[1]], states[idx[2]]
        a, b, lin = Symbolics.linear_expansion(_wrap(u), _wrap(Y))
        (lin && _iszero_const(b)) || throw(bad("non-bilinear incidence"))
        c, d, lin2 = Symbolics.linear_expansion(a, _wrap(Z))
        (lin2 && _iszero_const(d) && free(c)) || throw(bad("non-bilinear incidence"))
        return (idx[1], idx[2]), _unwrap(c)
    else
        throw(bad("higher order: $(length(idx)) unknowns in one term"))
    end
end


# A recovered reaction: its sort key (indices of the unknowns), the IR reaction, the index of the
# equation that loses its flux (for the reaction map), and its provenance line.
struct _Found{R}
    key::Tuple{Int,Int,Int}
    reaction::R
    equation::Int
    note::String
end

function _unknown_index(x, snames, name, kind)
    n = x isa Symbol ? x : _name(x)
    i = findfirst(==(n), snames)
    i === nothing && throw(ArgumentError(
        "contact_model(:$(name)): `$(kind)` refers to $(n), which is not an unknown " *
        "(unknowns: $(join(snames, ", ")))"))
    return i
end

# The rate of an explicit reaction must be positive. A rate whose sign the probe box does not fix
# (a fraction constrained jointly with others, such as (1 − q1 − q2)σ, or a rate that is 0 on
# the whole box) is taken as given, and noted; one that is exactly 0, or negative on the box or
# at the parameter defaults, is an error. A positive sign read from the probes or the defaults
# (not from the form of the rate) is noted as well.
function _explicit_rate!(c, P, name, what)
    s, how, text = _classify(c, P)
    if s == 1
        how === :probes && _note!(P, "the sign of the rate `$(_show(c))` of the explicit " *
                                     "$(what) is read numerically: $(text) (its form alone " *
                                     "does not fix it)")
        return nothing
    end
    if s == 2 && how !== :defaults
        _note!(P, "the rate `$(_show(c))` of the explicit $(what) is taken as given: " *
                  (how === :vanishes ? "it is not provably 0, but it is $(text)" :
                   "its sign is not fixed on the probe box"))
        return nothing
    end
    throw(ArgumentError(
        "contact_model(:$(name)): the explicit $(what) has the rate `$(_show(c))`, which is not " *
        "positive" * (how === :defaults ? " at the parameter defaults" : "")))
end

# Reactions given explicitly. Their fluxes are collected in the table E (monomial => (equation
# => coefficient), the part of the ODE that they account for: a loss in the equation of the
# unknown that makes the reaction, a gain in that of its product), and `roles` records for each
# (monomial, equation) whether the explicit reactions only lose there (-1), only gain (+1) or
# both (0); _check_explicit compares E with the ODE before it is taken out of the monomial table.
function _explicit_reactions!(E, ekeys, roles, found_c, found_t, spec, kind, states, snames,
                              name, crate, P)
    spec === nothing && return nothing
    n = length(snames)
    for entry in spec
        entry isa Pair || throw(ArgumentError(
            "contact_model(:$(name)): `$(kind)` entries are flux => (from, to" *
            (kind === :contacts ? ", infector)" : ")")))
        u = _unwrap(Symbolics.expand(_wrap(_unwrap(first(entry)))))
        ends = last(entry)
        if kind === :contacts
            length(ends) == 3 || throw(ArgumentError(
                "contact_model(:$(name)): a contact is flux => (from, to, infector)"))
            s, X, J = (_unknown_index(e, snames, name, kind) for e in ends)
            key, c = _monomial(u, s, states, snames, name, "", P)
            key == Tuple(sort([s, J])) || throw(ArgumentError(
                "contact_model(:$(name)): the contact flux `$(_show(u))` is not " *
                "τ*$(snames[s])*$(snames[J])"))
            S, JJ, XX = snames[s], snames[J], snames[X]
            _explicit_rate!(c, P, name, "contact $(S) + $(JJ) → $(XX) + $(JJ)")
            r, _ = crate(c)
            ct = Contact(S, JJ, XX, r)
            _add!(E, ekeys, key, s, -_coef(c))         # D(s) loses u
            _add!(E, ekeys, key, X, _coef(c))          # D(X) gains u
            _role!(roles, key, s, -1)
            _role!(roles, key, X, 1)
            push!(found_c, _Found((s, J, X), ct, s,
                                  "contact $(S) + $(JJ) → $(XX) + $(JJ) at $(_rate_text(r)): " *
                                  "from the `contacts` keyword"))
        else
            length(ends) == 2 || throw(ArgumentError(
                "contact_model(:$(name)): a transition is flux => (from, to), with to = " *
                "nothing for a removal"))
            X = _unknown_index(ends[1], snames, name, kind)
            key, a = _monomial(u, X, states, snames, name, "", P)
            key == (X,) || throw(ArgumentError(
                "contact_model(:$(name)): the transition flux `$(_show(u))` is not " *
                "a*$(snames[X])"))
            Y = ends[2] === nothing ? nothing : _unknown_index(ends[2], snames, name, kind)
            target = Y === nothing ? "∅" : string(snames[Y])
            _explicit_rate!(a, P, name, "transition $(snames[X]) → $(target)")
            r = _ir_rate(a)
            tr = NodeTransition(snames[X], Y === nothing ? nothing : snames[Y], r)
            _add!(E, ekeys, key, X, -_coef(a))         # D(X) loses u
            _role!(roles, key, X, -1)
            if Y !== nothing
                _add!(E, ekeys, key, Y, _coef(a))
                _role!(roles, key, Y, 1)
            end
            push!(found_t, _Found((X, something(Y, n + 1), 0), tr, X,
                                  "transition $(snames[X]) → $(target) at $(_rate_text(r)): " *
                                  "from the `transitions` keyword"))
        end
    end
    return nothing
end

_role!(roles, key, k, r) = (roles[(key, k)] = get(roles, (key, k), r) == r ? r : 0; roles)

# Each explicit reaction must be a flux of the ODE. For every equation D(k) in which the explicit
# reactions only lose (or only gain) through a monomial m, with e their total there and o the
# ODE's coefficient: o = 0 is an error (the ODE has no such term, so the reaction would be
# cancelled by an invented reverse one); if o is a loss (a gain) as well, the rest o − e must not
# be a gain (a loss): the reactions must not take out more than the ODE has. If o has the other
# sign, or no fixed sign, the ODE nets the explicit flux with other reactions (as D(I) =
# τSI − δSI does), and the check passes.
function _check_explicit(C, E, ekeys, roles, P, snames, name)
    for key in ekeys
        Ys = snames[collect(key)]
        mono = join(Ys, "*")
        for k in sort!(collect(keys(E[key])))
            role = roles[(key, k)]
            role == 0 && continue               # explicit losses and gains meet in D(k)
            e = E[key][k]
            o = haskey(C, key) && haskey(C[key], k) ? C[key][k] : _nocoef()
            so = first(_classify(o, P))
            verb = role < 0 ? "lose" : "gain"
            head = "contact_model(:$(name)): the explicit reactions make D($(snames[k])) " *
                   "$(verb) `$(_flux_text(_ir_rate(role < 0 ? -e : e), Ys...))`"
            tail = ": an explicit reaction must be a flux of the ODE, a term that the equation " *
                   "of the unknown that makes it loses and that of its product gains"
            so == 0 && throw(ArgumentError(
                "$head, but D($(snames[k])) has no term in $(mono)" * tail))
            if so == role && first(_classify(o - e, P)) == -role
                throw(ArgumentError(
                    "$head, but D($(snames[k])) $(verb)s only " *
                    "`$(_flux_text(_ir_rate(role < 0 ? -o : o), Ys...))`" * tail))
            end
        end
    end
    return nothing
end

function _add!(C, keys_, key, k, c::_Coef)
    if !haskey(C, key)
        C[key] = Dict{Int,_Coef}()
        push!(keys_, key)
    end
    d = C[key]
    d[k] = haskey(d, k) ? d[k] + c : c
    return C
end


const _ACCUMULATOR_HINT = " (an accumulator such as cumulative incidence is not a node state; " *
                          "remove it from the system)"

# a·Y: gains in D(Z) are transitions Y → Z; the rest of the loss in D(Y) is the removal Y → ∅.
function _pair_linear!(found_t, y, coefs, snames, P, name)
    Y = snames[y]
    n = length(snames)
    loss = haskey(coefs, y) ? -coefs[y] : _nocoef()
    sl = _sign(loss, P, name, "$(Y) in D($(Y))", Y)
    gains = [(k, c) for (k, c) in sort!(collect(coefs); by = first) if k != y]
    for (k, g) in gains
        _sign(g, P, name, "$(Y) in D($(snames[k]))", Y) > 0 || throw(ArgumentError(
            "contact_model(:$(name)): D($(snames[k])) loses `$(_flux_text(_ir_rate(-g), Y))`, " *
            "a term proportional to $(Y): a transition changes only the state of the node that " *
            "makes it"))
    end
    if sl <= 0 && !isempty(gains)
        k, g = first(gains)
        throw(ArgumentError(
            "contact_model(:$(name)): D($(snames[k])) gains `$(_flux_text(_ir_rate(g), Y))` but " *
            "D($(Y)) does not lose it: births change the node set; use the ODE itself for mass " *
            "action" * _ACCUMULATOR_HINT))
    end
    sl < 0 && throw(ArgumentError(
        "contact_model(:$(name)): D($(Y)) gains `$(_flux_text(_ir_rate(-loss), Y))`, growth in " *
        "proportion to $(Y) itself: births change the node set; use the ODE itself for mass " *
        "action"))
    total = sum(last.(gains); init = _nocoef())
    for (k, g) in gains
        r = _ir_rate(g)
        push!(found_t, _Found((y, k, 0), NodeTransition(Y, snames[k], r), y,
                              "$(_flux_text(r, Y)) leaves D($(Y)) and enters D($(snames[k])): " *
                              "transition $(Y) → $(snames[k]) at $(_rate_text(r))"))
    end
    rest = loss - total
    _residue_notes!(P, rest, "the loss of $(Y) less its gains", Y)
    sr = _sign(rest, P, name, "the loss of $(Y)", Y)
    if sr > 0
        r = _ir_rate(rest)
        push!(found_t, _Found((y, n + 1, 0), NodeTransition(Y, nothing, r), y,
                              "$(_flux_text(r, Y)) leaves D($(Y)) and no other unknown gains " *
                              "it: removal $(Y) → ∅ at $(_rate_text(r))"))
    elseif sr < 0
        throw(ArgumentError(
            "contact_model(:$(name)): the gains of `$(_flux_text(_ir_rate(total), Y))` exceed " *
            "its loss `$(_flux_text(_ir_rate(loss), Y))` in D($(Y)): births change the node " *
            "set; use the ODE itself for mass action" * _ACCUMULATOR_HINT))
    end
    return nothing
end

# τ·Y·Z: the unknown that loses it is the recipient, the other the infector; each unknown that
# gains it is a product.
function _pair_bilinear!(found_c, key, coefs, snames, P, name, crate)
    y, z = key
    Y, Z = snames[y], snames[z]
    ks = sort!(collect(keys(coefs)))
    sg = Dict{Int,Int}(k => _sign(coefs[k], P, name, "$(Y)*$(Z) in D($(snames[k]))", "$(Y)*$(Z)")
                       for k in ks)
    # only the two nodes of the edge can change state through it
    for k in ks
        (k == y || k == z || sg[k] > 0) && continue
        throw(ArgumentError(
            "contact_model(:$(name)): D($(snames[k])) loses " *
            "`$(_flux_text(_ir_rate(-coefs[k]), Y, Z))`, although $(snames[k]) is neither $(Y) " *
            "nor $(Z): a contact changes only the state of its recipient, one of the two nodes " *
            "of the edge"))
    end
    sy, sz = get(sg, y, 0), get(sg, z, 0)
    gainers = Symbol[snames[k] for k in ks if k != y && k != z]      # every one gains it
    if sy < 0 && sz < 0
        ly, lz = -coefs[y], -coefs[z]
        lost = _symbolic_zero(_value(ly - lz)) ?
               "the term `$(_flux_text(_ir_rate(ly), Y, Z))` is lost by both D($(Y)) and D($(Z))" :
               "the term in $(Y)*$(Z) is lost by both D($(Y)) " *
               "(`$(_flux_text(_ir_rate(ly), Y, Z))`) and D($(Z)) " *
               "(`$(_flux_text(_ir_rate(lz), Y, Z))`)"
        isempty(gainers) && throw(ArgumentError(
            "contact_model(:$(name)): $(lost), and no unknown gains it: a contact moves the " *
            "recipient to a product state (s + J → X + J); there is no contact with product ∅"))
        X1, X2 = length(gainers) >= 2 ? (gainers[1], gainers[2]) : (gainers[1], gainers[1])
        throw(ArgumentError(
            "contact_model(:$(name)): $(lost): either the infector changes state on " *
            "transmission (not a network contact) or several contacts share this flux (e.g. " *
            "$(Y) + $(Z) → $(X1) + $(Z) and $(Z) + $(Y) → $(X2) + $(Y)), and the ODE cannot " *
            "tell which. Pass contacts = [flux => (from, to, infector), …] to say which"))
    end
    if sy >= 0 && sz >= 0
        k = first(k for k in ks if sg[k] > 0)
        throw(ArgumentError(
            "contact_model(:$(name)): D($(snames[k])) gains " *
            "`$(_flux_text(_ir_rate(coefs[k]), Y, Z))` but neither D($(Y)) nor D($(Z)) loses " *
            "it: births change the node set; use the ODE itself for mass action" *
            _ACCUMULATOR_HINT))
    end
    s, j = sy < 0 ? (y, z) : (z, y)
    S, J = snames[s], snames[j]
    loss = -coefs[s]
    products = [(k, coefs[k]) for k in ks if k != s]     # all gain it (checked above)
    total = sum(last.(products); init = _nocoef())
    rest = loss - total
    _residue_notes!(P, rest, "the loss of $(S) through $(Y)*$(Z) less its gains", "$(Y)*$(Z)")
    sr = _sign(rest, P, name, "the loss of $(S) through $(Y)*$(Z)", "$(Y)*$(Z)")
    sr > 0 && throw(ArgumentError(
        "contact_model(:$(name)): D($(S)) loses `$(_flux_text(_ir_rate(loss), S, J))` but its " *
        "products gain only `$(_flux_text(_ir_rate(total), S, J))`: a contact moves the " *
        "recipient to a product state (s + J → X + J); there is no contact with product ∅"))
    sr < 0 && throw(ArgumentError(
        "contact_model(:$(name)): the gains of `$(_flux_text(_ir_rate(total), S, J))` exceed " *
        "the loss `$(_flux_text(_ir_rate(loss), S, J))` in D($(S)): births change the node set; " *
        "use the ODE itself for mass action" * _ACCUMULATOR_HINT))
    for (k, g) in products
        r, flux = crate(_value(g))
        X = snames[k]
        catalyst = k == j ? "$(J) is gained" : "D($(J)) does not lose it"
        push!(found_c, _Found((s, j, k), Contact(S, J, X, r), s,
                              "$(flux(S, J)) leaves D($(S)) and enters D($(X)); $(catalyst), " *
                              "so $(J) is the infector: contact $(S) + $(J) → $(X) + $(J) at " *
                              "$(_rate_text(r))"))
    end
    # S + J → J + J at a with S + J → X + J at b has the same terms as S + J → J + J at a + b
    # with the node-catalysed J + S → X + S at b (a T_net model): the ODE nets the two readings
    # into one coefficient of D(J), and the pairing keeps the contacts (F3).
    others = [(k, g) for (k, g) in products if k != j]
    if any(p -> first(p) == j, products) && !isempty(others)
        whole = first(crate(_value(loss)))
        alt = join(["$(J) + $(S) → $(snames[k]) + $(S) at $(_rate_text(first(crate(_value(g)))))"
                    for (k, g) in others], ", ")
        push!(P.notes, "the terms in $(S)*$(J) are also those of $(S) + $(J) → $(J) + $(J) at " *
                       "$(_rate_text(whole)) with the node-catalysed $(alt) (a T_net reading; " *
                       "F3): the contacts are kept; pass contacts = [flux => (from, to, " *
                       "infector), …] for the other reading")
    end
    return nothing
end

# The IR rate of a contact coefficient, and the text of its flux, for each rate convention. With
# rates = :frequency, the stored rate is β = coefficient × N, for a population N that is a
# number or a parameter name (then the coefficient must be β/N with β free of N).
function _contact_rate_rule(rates, population, name)
    if rates === :frequency && population isa Real
        Nn = population
        (isfinite(Nn) && Nn > 0) || throw(ArgumentError(
            "contact_model(:$(name)): rates = :frequency: the population must be positive; got " *
            "$(Nn)"))
        return function (c)
            r = _ir_rate(Symbolics.simplify(Symbolics.wrap(_unwrap(c)) * Nn))
            return r, (S, J) -> string(_flux_text(r, S, J), "/", NEC._rate_string(Nn))
        end
    elseif rates === :frequency && population !== nothing
        pop = Symbol(population)
        N = NEC.as_parameter(pop)
        return function (c)
            k = Symbolics.simplify(Symbolics.wrap(_unwrap(c)) * N)
            any(v -> _name(v) === pop, _variables(k)) && throw(ArgumentError(
                "contact_model(:$(name)): rates = :frequency, population = :$(pop): the " *
                "contact coefficient `$(_show(c))` is not of the form β/$(pop) with β free of " *
                "$(pop)"))
            r = _ir_rate(k)
            return r, (S, J) -> string(_flux_text(r, S, J), "/", pop)
        end
    end
    return function (c)
        r = _ir_rate(c)
        return r, (S, J) -> _flux_text(r, S, J)
    end
end


"""
    contact_model(sys::ModelingToolkitBase.System; susceptible = :infer, rates = :per_contact,
                  population = nothing, contacts = nothing, transitions = nothing,
                  allow_t = false, time_box = (0.1, 1000.0), name = nameof(sys)) -> ContactModel

The ModelingToolkit front end (§B.5): recover a network model from a mass-action ODE system
D(X) ~ f(X) by **flux pairing**. The right-hand sides are expanded into additive terms, each a
first-order flux a·Y or a bilinear flux τ·Y·Z of the unknowns; for each such monomial the
unknowns that lose it are paired with those that gain it:

- a·Y lost by D(Y) and gained by D(Z): the transition `Y → Z` at a; the part of the loss that no
  unknown gains is the removal `Y → ∅`;
- τ·Y·Z lost by D(Y) and not by D(Z): a contact `Y + Z → X + Z` for each unknown X that gains it
  (Z is the infector, unchanged by the contact; X may be Z itself, as in S + I → 2I).

The model records `provenance.method = :flux_pairing`, and every pairing decision is written to
the provenance assumptions (printed by `show`). The ODE fixes one network compatible with it, not
a unique one (F3), so the Catalyst front end is the canonical one. Reactions are ordered by the
order of the unknowns (contacts by recipient, infector and product; transitions by source and
target).

Keywords:

- `susceptible`: passed to [`ContactModel`](@ref) (`:infer`, a `Symbol` or a vector);
- `rates`: `:per_contact` (the coefficient of τ·S·I is the per-contact τ; a coefficient that
  contains the parameter `N`, or `population`, triggers a warning), `:frequency` (β·S·I/N read
  as `FrequencyDependent`, storing β: with `population = :N` the coefficient must be β/N with β
  free of N; with a number, `population = 1000`, β is 1000 times the coefficient; without
  `population`, a denominator that is a conserved sum of unknowns, such as S + I + R, is read as
  N = 1) or `:density` (`DensityDependent(population)`, a number or a parameter name);
- `contacts = [flux => (from, to, infector), …]` and `transitions = [flux => (from, to), …]`
  (`to = nothing` for a removal): reactions given explicitly; their fluxes are taken out of the
  ODE before the rest is paired, which resolves the ambiguous cases. Each must be a flux of the
  ODE: an equation that it changes must have a term in its monomial (so an explicit reaction is
  never cancelled by an invented reverse one), and it must not take out more than an equation
  that has the flux with the same sign contains. An equation in which the ODE nets the flux with
  other reactions (D(I) = τSI − δSI) passes. The reactions left are paired as usual, so a
  monomial whose coefficients have no fixed sign needs every reaction whose flux is
  proportional to it. The rate of an explicit reaction must be positive; one whose sign the
  probe box does not fix, such as (1 − q₁ − q₂)σ, or one that is 0 on the whole box, is taken as
  given and noted;
- `allow_t = true` keeps rates that depend on time explicitly (ODE back ends only); otherwise a
  non-autonomous system is an error. The independent variable is the IR's time `t` in every
  rate, whatever its name in the system (an independent variable `s` is renamed to `t`; a
  parameter may not then be called `t`);
- `time_box = (lo, hi)`: the interval of time on which the signs of time-dependent coefficients
  are probed (with `allow_t`), on a log scale when `lo > 0`. Pass the time span of the intended
  solution when it is longer than 1000 (a seasonal rate τ·sin(2πt/3650) is positive up to
  t = 1825).

**Zero.** A coefficient is read as 0 only when it is exactly 0: a number, a sum of
floating-point netting residues (see **Scale**), or an expression that simplifies to 0 once
its constants are folded (exp(0) = 1). A coefficient that is 0 at every probe point but not
provably 0 is never dropped (a vaccination rate ν·ifelse(t > 150, 1, 0) probed only up to
t = 100, max(p − 1, 0)·ν for p in [0.1, 0.9], or an identity that the simplifier cannot prove,
such as (exp(log(p)) − p)·ν): the parameter defaults give its sign if they make it non-zero
(noted), and otherwise it is an error that names it.

**Signs.** The coefficients of one monomial in one equation are summed before pairing, so each
must have a sign that does not depend on the parameters. Every parameter is read as positive (a
rate, or a fraction such as p); a negative parameter default is an error. A coefficient built
from positive numbers and parameters with +, *, /, ^, exp and sqrt is positive. Any other is
evaluated on a deterministic probe set of the box [0.1, 0.9] of its parameters and the
`time_box` of t (the grid of the ends and centres of up to six variables, the vertices and the
centre for more, and seeded interior points). It must not take both signs: (1 − p)·σ is
accepted, and τ − δ (or τ·cos(t), or τ·sin(2πt/365) on the default time box) is not. A
coefficient that is positive at some points and 0 at the others is positive (a rate need only
be non-negative, so (τ − δ)² and τ·max(t − 200, 0) are rates), and likewise for negative.
Fractions constrained jointly, such as (1 − q₁ − q₂)σ, are not positive on the box and need the
explicit reactions. Strictly positive parameter defaults are one more probe, which must not
give the opposite sign; a default of 0 (a flux switched off) is not a probe. A sign read from
the probes is written to the provenance, with the number of points at which the coefficient is
0.

For example the S-catalysed recovery ODE D(S) = −τSI, D(I) = τSI − δSI, D(R) = δSI
(S + I → 2I with I + S → R + S) gives D(I) the coefficient τ − δ, and is an error asking for
`contacts = [δ*I*S => (:I, :R, :S)]`, which gives the T_net model. With numeric rates (τ = 0.5,
δ = 0.2) the ODE is read as the contacts S + I → I + I at 0.3 and S + I → R + I at 0.2, which
give the same ODE, and the provenance names the node-catalysed reading.

**Scale.** Comparisons with 0 are relative, never absolute, so the result does not depend on
the units: the per-pair rate β ≈ 5.6e-13 of an SIR ODE in counts (N = 8e9, hourly time) is
kept. Coefficients are netted part by part (a part is a monomial in the parameters), and a part
is read as 0 only when its net is at most 1e-12 of the sum of the absolute values of the terms
that were added to it (floating-point netting, as in 0.1 + 0.2 − 0.3; a non-zero residue read
as 0 is noted in the provenance); at a probe point a value is 0 only when it is at most 1e-12 of
the sum of the absolute values of its terms there.

Algebraic and observed equations are eliminated first with `mtkcompile`/`full_equations`.
Errors name the offending term: a term without unknowns or an unmatched gain (births), a term
that is not first order or bilinear (for example non-bilinear incidence β·S·I/(1 + a·I)), a
bilinear term lost by both of its unknowns (ambiguous) or by a third unknown, a loss that no
product gains, a coefficient whose sign depends on the parameters or that vanishes on the whole
probe box, and an explicit reaction that is not a flux of the ODE. The `reaction_map` of the
provenance gives, for each IR reaction, the index of the equation that loses its flux.
Parameter defaults are read with `ModelingToolkitBase.initial_conditions`.
"""
function NEC.contact_model(sys::MB.System; susceptible = :infer, rates::Symbol = :per_contact,
                           population = nothing, contacts = nothing, transitions = nothing,
                           allow_t::Bool = false, time_box = _TIME_BOX,
                           name::Symbol = nameof(sys))
    rates in (:per_contact, :frequency, :density) || throw(ArgumentError(
        "contact_model(:$(name)): rates must be :per_contact, :frequency or :density; got " *
        ":$(rates)"))
    (length(time_box) == 2 && all(x -> x isa Real && isfinite(x), time_box) &&
     0 <= time_box[1] < time_box[2]) || throw(ArgumentError(
        "contact_model(:$(name)): time_box must be (lo, hi) with 0 ≤ lo < hi, finite; got " *
        "$(repr(time_box))"))
    notes = String[_F3_NOTE]
    iv, states, rhs = _odes(sys, name, notes)
    snames = Symbol[_name(x) for x in states]
    # parameters and their defaults
    params = Any[_unwrap(p) for p in MB.parameters(sys)]
    defaults = Dict{Symbol,Float64}()
    ic = MB.initial_conditions(sys)
    for p in params
        v = haskey(ic, p) ? ic[p] : Symbolics.getdefaultval(p, nothing)
        x = v === nothing ? nothing : _number(v)
        x isa Real && (defaults[_name(p)] = Float64(x))
    end
    # every parameter is read as positive (a rate, or a fraction such as p in (1 − p)σ)
    used = Set{Symbol}(_name(v) for f in rhs for v in _variables(f) if !isequal(v, iv))
    negative = sort!([nm for (nm, v) in defaults if v < 0 && nm in used])
    isempty(negative) || throw(ArgumentError(
        "contact_model(:$(name)): the parameter $(negative[1]) has the negative default " *
        "$(defaults[negative[1]]): the signs of the coefficients are decided for positive " *
        "parameters (rates, and fractions such as p in (1 − p)σ), so a negative rate or " *
        "fraction cannot be read"))
    # time dependence; the independent variable is the IR's time t
    ivname = _name(iv)
    ivname !== :t && :t in used && throw(ArgumentError(
        "contact_model(:$(name)): the system's independent variable is $(ivname) and a " *
        "parameter is called t; in the IR, t is time (the independent variable), so rename " *
        "the parameter"))
    timed = [k for k in eachindex(rhs) if _explicit_time(rhs[k], states, iv)]
    if !isempty(timed)
        allow_t || throw(ArgumentError(
            "contact_model(:$(name)): the right-hand side of D($(snames[timed[1]])) depends " *
            "on t explicitly (`$(_show(rhs[timed[1]]))`); pass allow_t = true to keep " *
            "time-dependent rates (ODE back ends only)"))
        push!(notes, "the rates depend on t (allow_t = true): time-dependent rates are for the " *
                     "ODE back ends only" *
                     (ivname === :t ? "" : "; the independent variable $(ivname) is written t"))
    end
    # rate convention
    if rates === :frequency && population === nothing
        _conserved_denominators!(rhs, states, snames, name, notes) || throw(ArgumentError(
            "contact_model(:$(name)): rates = :frequency needs population = :N (the parameter " *
            "that divides the contact rates), or contact terms divided by a conserved sum of " *
            "unknowns such as S + I + R"))
    end
    rates === :density && population === nothing && throw(ArgumentError(
        "contact_model(:$(name)): rates = :density needs population = N (a number or a " *
        "parameter name)"))
    convention = rates === :per_contact ? PerContact() :
                 rates === :frequency ? FrequencyDependent() : DensityDependent(population)
    crate = _contact_rate_rule(rates, population, name)
    hint = rates === :frequency ? "" :
           "; for β*S*I/N with N a conserved sum of unknowns pass rates = :frequency"
    P = _probes(defaults, iv, time_box)
    # the monomial table: monomial => (equation index => coefficient)
    C = Dict{Tuple,Dict{Int,_Coef}}()
    keys_ = Tuple[]
    for k in eachindex(rhs)
        for u in _additive_terms(Symbolics.expand(Symbolics.wrap(rhs[k])))
            key, c = _monomial(u, k, states, snames, name, hint, P)
            _add!(C, keys_, key, k, _coef(c))
        end
    end
    # explicit reactions: checked against the ODE, then taken out of the table
    found_c = _Found{Contact}[]
    found_t = _Found{NodeTransition}[]
    E = Dict{Tuple,Dict{Int,_Coef}}()
    ekeys = Tuple[]
    roles = Dict{Tuple{Tuple,Int},Int}()
    _explicit_reactions!(E, ekeys, roles, found_c, found_t, contacts, :contacts, states, snames,
                         name, crate, P)
    _explicit_reactions!(E, ekeys, roles, found_c, found_t, transitions, :transitions, states,
                         snames, name, crate, P)
    _check_explicit(C, E, ekeys, roles, P, snames, name)
    for key in ekeys, (k, e) in E[key]
        _add!(C, keys_, key, k, -e)
    end
    for key in keys_
        mono = join(snames[collect(key)], "*")
        for k in sort!(collect(keys(C[key])))
            _residue_notes!(P, C[key][k], "the coefficient of $(mono) in D($(snames[k]))", mono)
        end
        # only exact zeros are left out (a coefficient that vanishes on the probe box is paired,
        # and _sign reads its sign from the defaults or names it in an error)
        coefs = Dict{Int,_Coef}(k => c for (k, c) in C[key] if !_iszero_coef(c, P))
        isempty(coefs) && continue
        if length(key) == 1
            _pair_linear!(found_t, key[1], coefs, snames, P, name)
        else
            _pair_bilinear!(found_c, key, coefs, snames, P, name, crate)
        end
    end
    sort!(found_c; by = f -> f.key)
    sort!(found_t; by = f -> f.key)
    append!(notes, [f.note for f in found_c])
    append!(notes, [f.note for f in found_t])
    append!(notes, P.notes)
    cs = Contact[f.reaction for f in found_c]
    ts = NodeTransition[f.reaction for f in found_t]
    if rates === :frequency && population !== nothing
        pop = NEC._rate_string(population isa Real ? population : Symbol(population))
        push!(notes, "contact rates of the form β/$(pop) read as frequency-dependent with " *
                     "population $(pop): the stored constant is β (FrequencyDependent)")
    elseif rates === :density
        push!(notes, "contact rates read as density-dependent with population " *
                     "$(NEC._rate_string(population)) (DensityDependent)")
    elseif rates === :per_contact
        pop = population === nothing ? :N : Symbol(population)
        for c in cs
            if pop in Symbol[NEC._parameter_name(p) for p in NEC.rate_parameters(c.rate)]
                @warn "rate $(NEC._rate_string(c.rate)) looks frequency-dependent; pass rates = " *
                      ":frequency, population = :$(pop)"
                break
            end
        end
    end
    pv = Provenance(:mtk; method = :flux_pairing, assumptions = notes,
                    reaction_map = vcat(Int[f.equation for f in found_c],
                                        Int[f.equation for f in found_t]))
    return ContactModel(name; contacts = cs, transitions = ts, species = snames, susceptible,
                        convention, defaults, provenance = pv, merge_duplicates = true)
end

end # module NetworkEpiCoreMTKExt
