# Owner: WP10 (DESIGN_NetworkEpiCore.md §A.2, §B.6, §D.7; work package in §G.2).
# Triggered by Symbolics.
#
# - Symbolic rates: the hooks of ir/rates.jl (`_symbolic_rate_parameters`,
#   `_symbolic_parameter_name`, `_symbolic_rate_value`, `_symbolic_rate_uses_time`), which
#   substitute **by name** with `fold = Val(true)`, and `as_parameter`. With these, the generic
#   rate arithmetic of ir/rates.jl (`rate_mul`, `rate_add`, `rate_div`) works on `Num`.
# - `mass_action(cm; κ)` / `symbolic_ode(cm; κ)`: the mass-action ODE of c_κ P as a SymbolicODE;
#   `mass_action(d::ReactionNetworkData)` for the general targets of the reverse maps.
# - `verify`, `pushforward`, `vector_fields_equal`, `check_naturality` on the morphism objects of
#   src/morphisms.jl.
#
# Coordinates and parameters are identified by name throughout: before any comparison, every
# variable of an expression is replaced by a fresh plain variable determined by its role and its
# name (`_fresh`), so `θ(t)`, `θ` and `:θ` are the same coordinate and objects from EBM (MTK
# variables), NBM and NEC can be compared.
#
# Zero tests are exact: constants folded (`fold = Val(true)`), then expanded and simplified.
# Numeric probes only confirm identities that the simplifier cannot prove, and only when they are
# evidence (see "What the probes are evidence of" below): every term of the difference that does
# not cancel is non-zero at some probe point, and the cancellation holds when its non-analytic
# parts (max, min, abs, ifelse, …) are replaced by unknowns of either sign and of magnitude 0.1
# to 1000. Otherwise the answer is undecided, never equal (§J.3). Time t has its own probe box,
# (0.1, 1000) on a log scale. Analytic identities are confirmed on the probe box, not across a
# branch point outside it (sqrt((2 − a)²) = 2 − a for a ≤ 2).
#
# An extension cannot export names: every function implemented here is declared in the package
# (generics.jl for verify, pushforward, mass_action, symbolic_ode; ir/rates.jl for the rate hooks;
# morphisms.jl for as_parameter, vector_fields_equal, check_naturality and _free_variables).
module NetworkEpiCoreSymbolicsExt

import NetworkEpiCore
import NetworkEpiCore: ContactModel, SymbolicODE, Semiconjugacy, VerificationResult,
                       NaturalTransformation, ReactionNetworkData, PerContact,
                       FrequencyDependent, DensityDependent
import Symbolics
import Random

const NEC = NetworkEpiCore
const SU = Symbolics.SymbolicUtils

# =============================================================================================
# Expression utilities
# =============================================================================================

_unwrap(x) = Symbolics.unwrap(x)
_wrap(x) = x isa SU.BasicSymbolic ? Symbolics.wrap(x) : x

# A variable: a Sym, a called variable such as S(t) or β(t), or an indexed array element x[1].
function _isvariable(x)
    x isa SU.BasicSymbolic || return false
    SU.issym(x) && return true
    if SU.iscall(x)
        op = SU.operation(x)
        op isa SU.BasicSymbolic && SU.issym(op) && return true
        if op === getindex
            a = _unwrap(first(SU.arguments(x)))
            return a isa SU.BasicSymbolic && SU.issym(a)
        end
    end
    return false
end

# The variables of an expression in order of first appearance (depth first, with the arguments of
# sums and products in the canonical order of _sorted_arguments, below). A called variable S(t)
# is one variable: its argument t is not collected.
function _variables!(out::Vector{Any}, x)
    x = _unwrap(x)
    x isa SU.BasicSymbolic || return out
    if _isvariable(x)
        any(y -> isequal(y, x), out) || push!(out, x)
    elseif SU.iscall(x)
        for a in _sorted_arguments(x)
            _variables!(out, a)
        end
    end
    return out
end
_variables(x) = _variables!(Any[], x)
function _variables(xs::AbstractVector)
    out = Any[]
    for x in xs
        _variables!(out, x)
    end
    return out
end

# The name of a variable (θ(t) is named θ; an indexed element x[1] is named Symbol("x[1]")).
function _name(v)
    v = _unwrap(v)
    if v isa SU.BasicSymbolic && SU.iscall(v) && SU.operation(v) === getindex
        return Symbol(string(v))
    end
    return Symbol(Symbolics.getname(v))
end
_name(s::Symbol) = s
_name(s::AbstractString) = Symbol(s)

# Does the expression depend on a variable named t anywhere (also inside S(t) or β(t))?
function _has_time(x)
    x = _unwrap(x)
    x isa SU.BasicSymbolic || return false
    SU.issym(x) && return Symbolics.getname(x) === :t
    SU.iscall(x) || return false
    return any(_has_time, SU.arguments(x))
end

# A plain Julia number, if the expression is (or folds to) a constant; otherwise nothing.
function _number(x)
    x = _unwrap(x)
    if x isa SU.BasicSymbolic
        SU.isconst(x) || return nothing
        x = SU.unwrap_const(x)
    end
    return x isa Number ? x : nothing
end

_iszero_const(x) = (n = _number(x); n !== nothing && iszero(n))

# ---------------------------------------------------------------------------------------------
# Canonical order and printing
# ---------------------------------------------------------------------------------------------
#
# SymbolicUtils keeps (and prints) the terms of a sum and the factors of a product in an internal
# order that has changed between releases and, in recent ones, depends on hashes that differ
# between Julia sessions: `q1*σ` or `σ*q1`, `-x + max(x, 0)` or `max(x, 0) - x`, and `t > 150`
# is stored as `150 < t`. Everything that depends on an order (messages, the order in which
# variables are collected and probed, the IR expressions of the front ends) uses the order fixed
# here instead, so it is the same in every session and every release:
#
# - in a product, the number, then variables and their powers by name, then the other factors by
#   their text (`-S*ν*ifelse(t > 150, 1, 0)`, `x*max(-2 + a, 0)`, `q1*σ`);
# - in a sum, the number, then monomials in variables by degree and text, then the other terms by
#   their text (`-2 + a`, `σ - q1*σ - q2*σ`, `-x + max(x, 0)`);
# - a comparison with a number on the left and no number on the right is turned around
#   (`t > 150`, `a > 2`).
#
# `_canonical_string` prints an expression in that order, in the format of SymbolicUtils
# (`2β`, `-10000.0a`, `x*(y^2)`, `x / (1 + a)`, `(1//2)*x`).

_isop(x, f) = x isa SU.BasicSymbolic && SU.iscall(x) && SU.operation(x) === f

const _FLIPPED = Dict{Any,Any}((<) => (>), (>) => (<), (<=) => (>=), (>=) => (<=))

# A factor that is a variable or a power of one (the base is returned), else nothing.
function _variable_base(a)
    _isvariable(a) && return a
    if _isop(a, ^)
        b, e = SU.arguments(a)
        (_isvariable(b) && _number(e) isa Real) && return b
    end
    return nothing
end

_typetext(v) = v isa SU.BasicSymbolic ? string(SU.symtype(v)) : string(typeof(v))

# Sort key of a factor of a product: (class, name or text, text, type).
function _factor_key(a)
    a = _unwrap(a)
    n = _number(a)
    n !== nothing && return (0, "", string(n), "")
    b = _variable_base(a)
    b !== nothing && return (1, _canonical_string(b), _canonical_string(a), _typetext(b))
    return (2, _canonical_string(a), "", _typetext(a))
end

# A term of a sum as (numeric coefficient, the other factors).
function _coefficient_split(x)
    n = _number(x)
    n !== nothing && return (n, Any[])
    if _isop(x, *)
        c = 1
        rest = Any[]
        for a in SU.arguments(x)
            m = _number(a)
            m === nothing ? push!(rest, _unwrap(a)) : (c *= m)
        end
        return (c, rest)
    end
    return (1, Any[x])
end

# Sort key of a term of a sum: (class, degree, exponents, text without the coefficient, text,
# type). Monomials of one degree are in graded lexicographic order of their exponents by variable
# name (`δ^2 - 2δ*τ + τ^2`).
function _term_key(x)
    x = _unwrap(x)
    c, rest = _coefficient_split(x)
    noexp = Tuple{String,Float64}[]
    isempty(rest) && return (0, 0.0, noexp, "", string(c), "")
    degree = 0.0
    monomial = true
    exps = Tuple{String,Float64}[]
    for f in rest
        b = _variable_base(f)
        if b === nothing
            monomial = false
            continue
        end
        e = b === f ? 1.0 : Float64(_number(SU.arguments(f)[2]))
        degree += e
        push!(exps, (_canonical_string(b), -e))
    end
    mag = _mul_string(1, _sorted_factors(rest))
    return (monomial ? 1 : 2, monomial ? degree : 0.0, monomial ? sort!(exps) : noexp, mag,
            _canonical_string(x), join(_typetext.(rest), ","))
end

# v sorted by the keys f(v[i]), each computed once (stable).
function _sort_by_key(v::Vector{Any}, f)
    length(v) <= 1 && return v
    return v[sortperm(map(f, v))]
end

_sorted_factors(fs) = _sort_by_key(collect(Any, fs), _factor_key)

# The arguments of x in the canonical order (sums and products sorted; other calls as they are).
function _sorted_arguments(x)
    args = collect(Any, SU.arguments(x))
    _isop(x, +) && return _sort_by_key(args, _term_key)
    _isop(x, *) && return _sort_by_key(args, _factor_key)
    return args
end

# The canonical text of every compound subexpression is computed once: the sort keys and the
# text of a parent are built from those of its children, so ordering the arguments of a large
# expression (the lifted fields of EdgeBasedModels have thousands of terms) stays linear in its
# size times its depth. The cache is keyed by object (SymbolicUtils expressions are immutable)
# and emptied when it grows large.
const _CANONICAL_CACHE = IdDict{Any,String}()
const _CANONICAL_LOCK = ReentrantLock()
const _CANONICAL_CACHE_MAX = 200_000

function _canonical_string(x)
    x = _unwrap(x)
    x isa SU.BasicSymbolic || return string(x)
    SU.iscall(x) || return _render(x)
    s = lock(() -> get(_CANONICAL_CACHE, x, nothing), _CANONICAL_LOCK)
    s === nothing || return s
    s = _render(x)
    lock(_CANONICAL_LOCK) do
        length(_CANONICAL_CACHE) >= _CANONICAL_CACHE_MAX && empty!(_CANONICAL_CACHE)
        _CANONICAL_CACHE[x] = s
    end
    return s
end

function _render(x)
    io = IOBuffer()
    _cprint(io, x)
    return String(take!(io))
end

_paren_number(n) = n isa Rational || (n isa Complex && !iszero(imag(n))) ||
                   (n isa Number && !isfinite(n))

function _print_number(io, n)
    _paren_number(n) ? print(io, "(", n, ")") : print(io, n)
end

# An argument of a product, a power or a binary operator: in parentheses if it is itself a
# product, sum, power, quotient or binary operation (as SymbolicUtils prints it).
function _cprint_arg(io, a)
    a = _unwrap(a)
    if a isa SU.BasicSymbolic && SU.iscall(a)
        f = SU.operation(a)
        if !(f isa SU.BasicSymbolic) && (f === (*) || f === (+) || f === (^) || f === (/) ||
                                         (applicable(nameof, f) &&
                                          Base.isbinaryoperator(nameof(f))))
            print(io, "(", _canonical_string(a), ")")
            return
        end
    end
    print(io, _canonical_string(a))
end

# A product c·f₁·f₂⋯ with the factors already in order.
function _mul_string(c, fs)
    io = IOBuffer()
    _print_mul(io, c, fs)
    return String(take!(io))
end

function _print_mul(io, c, fs)
    isempty(fs) && return _print_number(io, c)
    (isone(c) && length(fs) == 1) && return print(io, _canonical_string(fs[1]))  # sin(x)^2
    if c == -1
        print(io, "-")
    elseif !isone(c)
        _print_number(io, c)
        _paren_number(c) && print(io, "*")          # (1//2)*x, but 2x and -10000.0a
    end
    for (i, f) in enumerate(fs)
        i == 1 || print(io, "*")
        _cprint_arg(io, f)
    end
end

function _cprint(io, x)
    n = _number(x)
    n !== nothing && return _print_number(io, n)
    x isa SU.BasicSymbolic || return print(io, x)
    SU.iscall(x) || return print(io, x)
    f = SU.operation(x)
    args = SU.arguments(x)
    if f === (+)
        for (i, t) in enumerate(_sorted_arguments(x))
            c, rest = _coefficient_split(t)
            neg = c isa Real && c < 0
            if i == 1
                neg && print(io, "-")
            else
                print(io, neg ? " - " : " + ")
            end
            _print_mul(io, neg ? -c : c, _sorted_factors(rest))
        end
    elseif f === (*)
        c, rest = _coefficient_split(x)
        _print_mul(io, c, _sorted_factors(rest))
    elseif f === (^) && length(args) == 2
        b, e = args
        nb = _number(b)
        if nb isa Real && nb < 0
            print(io, "(")
            _cprint(io, b)
            print(io, ")")
        else
            _cprint_arg(io, b)
        end
        print(io, "^")
        _cprint_arg(io, e)
    elseif haskey(_FLIPPED, f) && length(args) == 2
        l, r = args
        if _number(l) !== nothing && _number(r) === nothing
            l, r, f = r, l, _FLIPPED[f]
        end
        _cprint_arg(io, l)
        print(io, " ", nameof(f), " ")
        _cprint_arg(io, r)
    elseif _isvariable(x) || f === getindex
        print(io, x)
    elseif !(f isa SU.BasicSymbolic) && applicable(nameof, f) &&
           Base.isunaryoperator(nameof(f)) && length(args) == 1
        print(io, nameof(f))
        _cprint_arg(io, args[1])
    elseif !(f isa SU.BasicSymbolic) && applicable(nameof, f) &&
           Base.isbinaryoperator(nameof(f)) && length(args) > 1
        for (i, a) in enumerate(args)
            i == 1 || print(io, " ", nameof(f), " ")
            _cprint_arg(io, a)
        end
    else
        f isa SU.BasicSymbolic ? _cprint(io, f) :
            print(io, applicable(nameof, f) ? nameof(f) : f)
        print(io, "(")
        for (i, a) in enumerate(args)
            i == 1 || print(io, ", ")
            print(io, _canonical_string(a))
        end
        print(io, ")")
    end
    return nothing
end

NEC._symbolic_string(x::Union{Symbolics.Num,SU.BasicSymbolic}) = _canonical_string(x)

# Fold the constant subexpressions of x (exp(0) → 1.0, log(1) → 0): simplify does not, so
# without folding exp(0)·τ − τ is not recognised as 0 (§D.7). An ifelse whose branches are equal,
# ifelse(c, x, x), is x (_fold_ifelse), so that it is neither an opaque part nor a failed zero test.
_fold(x) = Symbolics.substitute(_wrap(_fold_ifelse(_unwrap(x))), Dict{Any,Any}(); fold = Val(true))

# The subexpressions ifelse(c, x, x) of x, as pairs ifelse(c, x, x) => x.
function _equal_branch_ifelses!(out::Vector{Pair{Any,Any}}, x)
    x = _unwrap(x)
    (x isa SU.BasicSymbolic && SU.iscall(x)) || return out
    args = SU.arguments(x)
    if SU.operation(x) === ifelse && length(args) == 3 && isequal(args[2], args[3])
        push!(out, x => args[2])
    end
    for a in args
        _equal_branch_ifelses!(out, a)
    end
    return out
end

# x with every ifelse(c, y, y) replaced by y (nested ones too).
function _fold_ifelse(x)
    x = _unwrap(x)
    x isa SU.BasicSymbolic || return x
    for _ in 1:16
        prs = _equal_branch_ifelses!(Pair{Any,Any}[], x)
        isempty(prs) && return x
        x = _unwrap(Symbolics.substitute(_wrap(x), Dict{Any,Any}(prs); fold = Val(false)))
        x isa SU.BasicSymbolic || return x
    end
    return x
end

# The number of nodes of an expression tree, counted up to `cap` (then cap + 1).
function _node_count(x, cap::Int)
    n = 0
    stack = Any[_unwrap(x)]
    while !isempty(stack)
        y = pop!(stack)
        n += 1
        n > cap && return n
        (y isa SU.BasicSymbolic && SU.iscall(y)) && append!(stack, SU.arguments(y))
    end
    return n
end

# Whether the expression has a floating-point constant (a coefficient or an exponent, such as
# the 5/6 of an empirical degree distribution or the r = 4.0 of a negative binomial PGF).
function _has_float(x)
    stack = Any[_unwrap(x)]
    while !isempty(stack)
        y = pop!(stack)
        c = _number(y)
        if c !== nothing
            c isa AbstractFloat && return true
        elseif y isa SU.BasicSymbolic && SU.iscall(y)
            append!(stack, SU.arguments(y))
        end
    end
    return false
end

# The symbolic zero test is a shortcut, not the decision (the numeric probes decide what it
# cannot), so it is budgeted.
#
# - Floating-point constants (the 5/6 of an empirical degree distribution, the p = 2/3 of a
#   negative binomial PGF) are replaced by the simplest rationals within a relative
#   _RATIONALIZE_RTOL of them (`rationalize`) before simplifying: SymbolicUtils combines fractions
#   with polynomial GCDs, which over floating-point coefficients can recurse until the stack
#   overflows (verify of the M6 map on the bimodal {2, 10} network; the error used to be
#   swallowed) or run for minutes. So 0.8333333333333334 is 5/6 and 1.4999999999999998 is 3/2,
#   and an identity that holds for the exact constants simplifies to 0; a genuinely different
#   coefficient, or a rounding residue such as 1e-16·x (whose own relative tolerance is 1e-28),
#   stays non-zero. The zero test therefore holds up to a relative perturbation of 1e-12 of the
#   floating-point constants, well inside the numeric rtol of `verify`.
# - An expression is simplified only when it has at most _SIMPLIFY_MAX_NODES nodes after
#   expansion (the rule-based simplifier took tens of seconds on the power-law PGF's 1100-node
#   residuals); a larger one is left to the probes.
const _SIMPLIFY_MAX_NODES = 1000

const _RATIONALIZE_RTOL = 1e-12

# x with every floating-point constant c replaced by the simplest rational within a relative
# _RATIONALIZE_RTOL of it.
# (an integer as an Int, so that x^4.0 becomes the polynomial power x^4; otherwise a
# Rational{BigInt}, because the polynomial arithmetic of the simplifier can overflow Int128).
function _rationalize_float(c::AbstractFloat)
    r = rationalize(BigInt, c; tol = _RATIONALIZE_RTOL * abs(Float64(c)))
    (isone(denominator(r)) && typemin(Int) <= numerator(r) <= typemax(Int)) && return Int(numerator(r))
    return r
end
_rationalize_floats(x) =
    SU.Postwalk(y -> (c = _number(y); c isa AbstractFloat && isfinite(c) ?
                                      _rationalize_float(c) : y))(_unwrap(x))

# Is the expression identically zero? Exact: fold the constants, expand, then simplify (which
# combines fractions). `false` means "not shown to be 0"; it never throws (a stack overflow in
# the simplifier is reported with a warning, not swallowed silently).
function _symbolic_zero(r)
    _number(r) !== nothing && return _iszero_const(r)
    try
        f = _fold(r)
        # floating-point constants become rationals before any arithmetic on them, so that
        # 6·0.8333333333333334 is 5 and not 5.000000000000001
        rational = _has_float(f)
        rational && (f = _wrap(_rationalize_floats(f)))
        e = Symbolics.expand(f)
        _iszero_const(e) && return true
        _node_count(e, _SIMPLIFY_MAX_NODES) > _SIMPLIFY_MAX_NODES && return false
        if rational
            # combine the fractions (exact polynomial GCDs) and expand; the rule-based
            # simplifier, which costs tens of seconds on these PGFs, is skipped
            s = Symbolics.simplify_fractions(e)
            _iszero_const(s) && return true
            return _iszero_const(Symbolics.expand(s))
        end
        s = Symbolics.simplify(e; expand = true)
        _iszero_const(s) && return true
        s = Symbolics.simplify_fractions(s)
        _iszero_const(s) && return true
        return _iszero_const(Symbolics.expand(Symbolics.simplify(s)))
    catch err
        err isa InterruptException && rethrow()
        err isa StackOverflowError && @warn(
            "NetworkEpiCore: symbolic simplification overflowed the stack; the expression " *
            "is treated as not shown to be 0 (verify and vector_fields_equal then decide it " *
            "with the numeric probes)", maxlog = 1)
        return false
    end
end

# Replace every variable of `e` by f(name) (a replacement expression or number), or leave it
# when f returns `nothing`. Symbols and Exprs (RATE_OPS arithmetic) are accepted as well.
function _rename(e, f)
    if e isa Symbol
        r = f(e)
        return r === nothing ? _unwrap(Symbolics.variable(e)) : _unwrap(r)
    elseif e isa Expr
        names = NEC.rate_parameters(e)
        vals = Dict{Symbol,Any}(n => _wrap(_rename(n, f)) for n in names)
        tv = NEC._uses_time(e) ? _wrap(_rename(:t, f)) : nothing
        return _unwrap(NEC.rate_value(e, vals; t = tv))
    end
    x = _unwrap(e)
    x isa SU.BasicSymbolic || return x
    subs = Dict{Any,Any}()
    for v in _variables(x)
        r = f(_name(v))
        r === nothing || (subs[v] = _unwrap(r))
    end
    isempty(subs) && return x
    return _unwrap(Symbolics.substitute(x, subs; fold = Val(true)))
end

# A fresh plain variable for the coordinate `name` in the role `role` (:x source state, :y target
# state, :p parameter, …). The ‹role› prefix cannot occur in a user's variable names.
_fresh(role::Symbol, name::Symbol) = _unwrap(Symbolics.variable(Symbol("‹", role, "›", name)))
_fresh_name(v) = (s = string(_name(v)); k = findfirst('›', s); Symbol(s[nextind(s, k):end]))

# Readable form of an expression in fresh variables (the ‹role› prefixes removed).
function _display(e)
    x = _unwrap(e)
    x isa SU.BasicSymbolic || return string(x)
    subs = Dict{Any,Any}(v => _unwrap(Symbolics.variable(_fresh_name(v)))
                         for v in _variables(x) if occursin('›', string(_name(v))))
    isempty(subs) && return _canonical_string(x)
    return _canonical_string(Symbolics.substitute(x, subs))
end

# Numeric evaluation of expressions in the variables `vars` (vectors of values in that order):
# compiled with build_function where possible, by substitution otherwise.
function _compile(exprs::AbstractVector, vars::AbstractVector)
    ex = [_wrap(_unwrap(e)) for e in exprs]
    vs = [_wrap(_unwrap(v)) for v in vars]
    f = try
        Symbolics.build_function(ex, vs; expression = Val(false))[1]
    catch
        nothing
    end
    if f !== nothing
        return vals -> Float64.(collect(f(vals)))
    end
    return function (vals)
        d = Dict{Any,Any}(_unwrap(v) => x for (v, x) in zip(vars, vals))
        return [_substitute_float(e, d) for e in ex]
    end
end

# Outside its real domain a function is NaN, as in compiled code (build_function uses NaNMath).
function _substitute_float(e, d)
    try
        return _tofloat(Symbolics.substitute(e, d; fold = Val(true)))
    catch err
        err isa DomainError && return NaN
        rethrow()
    end
end

function _tofloat(x)
    n = _number(x)
    n === nothing && throw(ArgumentError(
        "the expression $(_canonical_string(x)) did not evaluate to a number (free variables " *
        "$(join(string.(_name.(_variables(x))), ", ")))"))
    return Float64(real(n))
end

# Probe boxes by name, from a vector of `key => (lo, hi)`.
_boxes(domain) = Dict{Symbol,Tuple{Float64,Float64}}(NEC._coordinate_name(k) => v
                                                     for (k, v) in domain)
const _STATE_BOX = (0.05, 0.95)
const _PARAM_BOX = (0.1, 1.0)
const _TIME_BOX = (0.1, 1000.0)

_draw(rng, (lo, hi)) = lo + (hi - lo) * rand(rng)

# Time t (a free variable named t) has its own box, (0.1, 1000) unless the domain gives one. It is
# drawn on a log scale when the box starts above 0, and stratified: probe j of n draws t from the
# j-th of n equal slices of the (log) box, so that early and late times are always both probed
# and a term such as ν·ifelse(t > 150, 1, 0) is not 0 at every probe point.
function _draw_time(rng, (lo, hi), j::Integer = 1, n::Integer = 1)
    u = (j - 1 + rand(rng)) / n
    return lo > 0 ? lo * (hi / lo)^u : lo + (hi - lo) * u
end

# A probe value for the parameter (or time) named n, at probe j of `probes`.
_draw_param(rng, n::Symbol, boxes, j::Integer = 1, probes::Integer = 1) =
    n === :t ? _draw_time(rng, get(boxes, :t, _TIME_BOX), j, probes) :
    _draw(rng, get(boxes, n, _PARAM_BOX))

# =============================================================================================
# Symbolic rates: the hooks of ir/rates.jl
# =============================================================================================

NEC._is_symbolic_rate(::SU.BasicSymbolic) = true
NEC._is_symbolic_rate(::Symbolics.Num) = true

const _SymRate = Union{Symbolics.Num,SU.BasicSymbolic}

function NEC._symbolic_rate_parameters(r::_SymRate)
    return Any[Symbolics.wrap(v) for v in _variables(r) if _name(v) !== :t]
end

NEC._symbolic_parameter_name(p::_SymRate) =
    _isvariable(_unwrap(p)) ? _name(p) : Symbol(string(p))

# Parameter values keyed by name (keys may be Symbols, strings or symbolic variables).
function _by_name(p::AbstractDict)
    out = Dict{Symbol,Any}()
    for (k, v) in p
        out[k isa Symbol ? k : _name(k)] = v
    end
    return out
end

# rate_value on a symbolic rate: every variable is substituted by name (fold = Val(true)), and
# every one must have a value, as for Symbol and Expr rates. A missing parameter is an error that
# names it (never a partly evaluated expression that a caller might read as a number). A rate
# that depends on time t anywhere, also through a called parameter β(t) (as `_uses_time` says),
# needs `t = …`, even when β is given by name. A value may itself be symbolic (the variable
# itself keeps a parameter free).
function NEC._symbolic_rate_value(r::_SymRate, p::AbstractDict, t)
    vals = _by_name(p)
    subs = Dict{Any,Any}()
    unbound = Symbol[]
    timed = t === nothing && _has_time(r)
    for v in _variables(r)
        n = _name(v)
        if n === :t
            t === nothing || (subs[v] = _unwrap(t))
        elseif haskey(vals, n)
            subs[v] = _unwrap(vals[n])
        else
            n in unbound || push!(unbound, n)
        end
    end
    if !isempty(unbound)
        elements = [n for n in unbound if occursin('[', string(n))]
        throw(ArgumentError(
            "rate `$(NEC._rate_string(r))`: no value for the parameter" *
            (length(unbound) > 1 ? "s " : " ") * join(unbound, ", ") *
            (isempty(elements) ? "" :
             " (an array element is a parameter of its own, named by its full name: pass " *
             "Symbol(\"$(first(elements))\") => value)")))
    end
    timed && throw(ArgumentError(
        "rate `$(NEC._rate_string(r))` depends on time t; pass `t = …` (time-dependent rates " *
        "are for the ODE back ends only)"))
    out = isempty(subs) ? _unwrap(r) : _unwrap(Symbolics.substitute(r, subs; fold = Val(true)))
    n = _number(out)
    return n === nothing ? Symbolics.wrap(out) : n
end

NEC._symbolic_rate_uses_time(r::_SymRate) = _has_time(r)

# The variables of a rate that are neither a scalar parameter nor time t, described for the
# ContactModel constructor's error: an element k[1] of an array, an array k, or a called variable
# β(t) (a function of time). The IR names every rate parameter by a Symbol, so none of these can
# be given a value by the back ends (§B.1, E25).
function NEC._symbolic_nonscalar_variables(r::_SymRate)
    out = String[]
    for v in _variables(r)
        x = _unwrap(v)
        isarray = SU.symtype(x) <: AbstractArray
        (SU.issym(x) && !isarray) && continue
        desc = if SU.iscall(x) && SU.operation(x) === getindex
            "$(_canonical_string(x)) (an element of the array $(first(SU.arguments(x))))"
        elseif isarray
            "$(_canonical_string(x)) (an array)"
        else
            "$(_canonical_string(x)) (a function of " *
            "$(join(_canonical_string.(SU.arguments(x)), ", ")))"
        end
        desc in out || push!(out, desc)
    end
    return out
end

# ---------------------------------------------------------------------------------------------
# as_parameter
# ---------------------------------------------------------------------------------------------

# ModelingToolkit recognises a parameter by metadata that only ModelingToolkitBase defines; when
# NetworkEpiCoreMTKExt is loaded, it adds that metadata (the result then equals `@parameters τ`).
function _mark_parameter(v)
    ext = Base.get_extension(NetworkEpiCore, :NetworkEpiCoreMTKExt)
    return ext === nothing ? v : ext._toparam(v)
end

function NEC.as_parameter(name::Symbol)
    name === :t && throw(ArgumentError(
        "as_parameter(:t): t is time (the independent variable), not a parameter; evaluate a " *
        "time-dependent rate with rate_value(r, p; t = …)"))
    v = _unwrap(Symbolics.variable(name))
    v = Symbolics.setmetadata(v, Symbolics.VariableSource, (:parameters, name))
    return Symbolics.wrap(_mark_parameter(v))
end
NEC.as_parameter(x::Symbolics.Num) = x
NEC.as_parameter(x::SU.BasicSymbolic) = Symbolics.wrap(x)
NEC.as_parameter(x::Real) = x

function NEC.as_parameter(ex::Expr; t = nothing)
    NEC._check_rate_expr(ex, "", ex)
    (NEC._uses_time(ex) && t === nothing) && throw(ArgumentError(
        "as_parameter: the rate `$(NEC._rate_string(ex))` depends on time t; pass t = … (for " *
        "example ModelingToolkit's t_nounits)"))
    vals = Dict{Symbol,Any}(n => NEC.as_parameter(n) for n in NEC.rate_parameters(ex))
    return NEC.rate_value(ex, vals; t)
end

# The symbolic form of an IR rate, with time t.
_symbolic_rate(r::Symbol, t) = r === :t ? t : NEC.as_parameter(r)
_symbolic_rate(r::Expr, t) = NEC.as_parameter(r; t)
_symbolic_rate(r, t) = NEC._is_symbolic_rate(r) ? _wrap(_unwrap(r)) : r

# =============================================================================================
# Mass action (§D.4 MA; §D.5 "syntax" sense of back to mass action)
# =============================================================================================

_time() = Symbolics.variable(:t)
_state_variable(name::Symbol, t) = only(Symbolics.@variables $name(t))

# The mass-action rate of a contact in c_κ P: κ τ with τ from the rate convention on WellMixed(κ).
_ma_rate(::PerContact, r, κ) = NEC.rate_mul(κ, r)
_ma_rate(::FrequencyDependent, r, κ) = r
_ma_rate(c::DensityDependent, r, κ) = NEC.rate_mul(r, c.N)

function NEC._free_variables(exprs::AbstractVector, states::AbstractVector)
    snames = Set(NEC._coordinate_name(x) for x in states)
    return Any[Symbolics.wrap(v) for v in _variables(collect(exprs))
               if !(_name(v) in snames) && _name(v) !== :t]
end

"""
    mass_action(cm::ContactModel; κ = 1) -> SymbolicODE

The mass-action ODE of c_κ P on the species of `cm` (states `X(t)`, as ModelingToolkit writes
them): each contact `s + J → X + J` contributes the flux κ τ s J, where τ is its per-contact rate
on `WellMixed(κ)` (§B.6: κ τ = the written rate for `FrequencyDependent`, and rate·N for
`DensityDependent(N)`), and each transition `X → Y | ∅` the flux a X. `κ` may be a number, a
`Symbol` or a symbolic expression. Parameters are `as_parameter` variables. This is MA(c_κ P),
the target of the well-mixed unit M1.

A removal `X → ∅` (or an exit `s → ∅`) only drains its source here: the ODE has no state for the
absorbing sink `:removed` that the lowerings add (§J.2). The sink is a function of the other
states (1 minus their sum), so this ODE is the quotient that forgets it, which is what the M1
semiconjugacy and EdgeBasedModels' reverse maps target; a back end that keeps the sink (such as
NodeBasedModels' `MeanFieldSystem`) agrees with it on the other states.
"""
function NEC.mass_action(cm::ContactModel; κ = 1)
    t = _time()
    sp = NEC.species_names(cm)
    X = Dict{Symbol,Any}(x => _state_variable(x, t) for x in sp)
    rhs = Dict{Symbol,Any}(x => Symbolics.Num(0) for x in sp)
    conv = NEC.rate_convention(cm)
    for c in NEC.contacts(cm)
        flux = _symbolic_rate(_ma_rate(conv, c.rate, κ), t) * X[c.recipient] * X[c.infector]
        rhs[c.recipient] -= flux
        rhs[c.product] += flux
    end
    for tr in NEC.node_transitions(cm)
        flux = _symbolic_rate(tr.rate, t) * X[tr.from]
        rhs[tr.from] -= flux
        tr.to === nothing || (rhs[tr.to] += flux)
    end
    states = Any[X[x] for x in sp]
    f = Any[rhs[x] for x in sp]
    return SymbolicODE(Symbol(cm.name, :_mass_action), states, f,
                       NEC._free_variables(f, states), Pair{Any,Tuple{Float64,Float64}}[])
end

"""
    symbolic_ode(cm::ContactModel; κ = 1) -> SymbolicODE

The same as [`mass_action`](@ref)`(cm; κ)`: the mass-action ODE of c_κ P.
"""
NEC.symbolic_ode(cm::ContactModel; κ = 1) = NEC.mass_action(cm; κ)

"""
    mass_action(d::ReactionNetworkData) -> SymbolicODE

The mass-action ODE of a general reaction network (the targets of the reverse maps, e.g.
`edge_doubling(cm, μ)`): a reaction `Σ a_i A_i → Σ b_j B_j` at rate k has the propensity
k Π A_i^{a_i} (no combinatoric factor), or its `rate` itself when `only_use_rate = true` (a rate
law whose leaves may be species).
"""
function NEC.mass_action(d::ReactionNetworkData)
    t = _time()
    X = Dict{Symbol,Any}(x => _state_variable(x, t) for x in d.species)
    rhs = Dict{Symbol,Any}(x => Symbolics.Num(0) for x in d.species)
    for r in d.reactions
        flux = if r.only_use_rate
            _rate_law(r.rate, X, t)
        else
            k = _symbolic_rate(r.rate, t)
            for (a, n) in r.substrates
                k = k * X[a]^n
            end
            k
        end
        for (a, n) in r.substrates
            rhs[a] -= n * flux
        end
        for (b, n) in r.products
            rhs[b] += n * flux
        end
    end
    states = Any[X[x] for x in d.species]
    f = Any[rhs[x] for x in d.species]
    return SymbolicODE(Symbol(d.name, :_mass_action), states, f,
                       NEC._free_variables(f, states), Pair{Any,Tuple{Float64,Float64}}[])
end

NEC.symbolic_ode(d::ReactionNetworkData) = NEC.mass_action(d)

function _rate_law(r, X, t)
    f(n) = n === :t ? t : haskey(X, n) ? X[n] : NEC.as_parameter(n)
    return _wrap(_rename(r, f))
end

# =============================================================================================
# What the probes are evidence of
# =============================================================================================
#
# A difference that the simplifier cannot prove to be 0, but that is 0 (to rtol) at every probe
# point, is read as 0 only when the probes are evidence of that. Its terms are those that do not
# cancel (_difference_terms), and two things are asked of them:
#
# 1. Every term is non-zero at some probe point. A term that is 0 at every one of them, such as
#    ν·ifelse(t > 150, 1, 0) with t probed below 150, max(a − 2, 0) with a below 2, or exp(−10⁴a)
#    (which underflows), is not seen, and the terms that are seen may cancel without it.
# 2. The cancellation does not depend on the values of the non-analytic parts. Every maximal
#    subexpression whose operation is not in _ANALYTIC_OPS (max, min, abs, ifelse, sign, floor,
#    …, and any function that is not listed) is replaced by an independent unknown, drawn afresh
#    at each probe point, and the terms must still cancel. An analytic difference that is 0 on
#    the probe box is 0 on the connected region around it where it stays analytic (the identity
#    theorem), so random probes are evidence for an identity such as sin²x + cos²x = 1. A
#    piecewise one need not be: x/(1 + max(a − 2, 0)) = x only for a ≤ 2, and max(x, 0) = x only
#    for x ≥ 0. When the identity holds whatever value the piecewise part takes, as in
#    max(a − 2, 0)·(sin²x + cos²x) = max(a − 2, 0), it is confirmed.
#
#    A part can take any value off the probe box (max(t − 150, 0) is 850 at t = 1000, and
#    ifelse(a > 2, −1, 1) is −1 for a > 2), so the unknowns take both signs and magnitudes from
#    0.1 to 1000 (_stand_in_values). An identity that holds only for positive or small values of
#    a part, such as sqrt(g²) = g, is then not confirmed; nor is one that holds for the values the
#    part can take but not for others (sqrt(max(u, 0)²) = max(u, 0)): the check is conservative.
#
# Requirement 1 is asked of the terms with those unknowns in place, so a term that is 0 at every
# probe point only because a non-analytic factor is (max(a − 2, 0)·(e^x·e − e^{x+1})) is seen
# once the factor is free, and it is then 2 that decides.
#
# What the probes are not evidence against: an analytic identity that holds on the probe box but
# not across a branch point outside it. sqrt((2 − a)²) = 2 − a for a ≤ 2 only, and the default
# parameter box is (0.1, 1.0); the identity theorem covers only the connected region around the
# box where the expression stays analytic. A `domain` box that covers the parameter values of
# interest (rates and κ above 1 are common) is the remedy.

# The operations under which the probes are evidence of an identity: the field operations and
# functions that are analytic where they are real.
const _ANALYTIC_OPS = Set{Any}([+, -, *, /, ^, inv, identity, abs2, exp, exp2, exp10, expm1, log,
                                log2, log10, log1p, sqrt, cbrt, sin, cos, tan, sec, csc, cot,
                                sinpi, cospi, sinh, cosh, tanh, asin, acos, atan, asinh, acosh,
                                atanh])

# The maximal subexpressions of x whose operation is not analytic, in order of first appearance
# (in the canonical order of the arguments). A variable (θ, S(t), x[1]) is not one.
function _opaque_parts!(out::Vector{Any}, x)
    x = _unwrap(x)
    (x isa SU.BasicSymbolic && SU.iscall(x) && !_isvariable(x)) || return out
    if SU.operation(x) in _ANALYTIC_OPS
        for a in _sorted_arguments(x)
            _opaque_parts!(out, a)
        end
    else
        any(y -> isequal(y, x), out) || push!(out, x)
    end
    return out
end

# The seed of the draws of the unknowns that stand for the non-analytic parts: separate from the
# probe points, so that adding a part does not move them.
_atom_seed(rng_seed::Integer) = (rng_seed % UInt64) ⊻ 0x7761746f6d73

# The magnitudes of the unknowns that stand for the non-analytic parts: 10^u, u in this range.
const _STAND_IN_LOG10 = (-1.0, 3.0)

# The fewest draws of the unknowns in _probe_evidence: 4 of each sign, stratified over the
# magnitudes (below 1 and above 100 both occur), however few probe points there are.
const _MIN_STAND_IN_POINTS = 8

# Values of k unknowns at n probe points (an n×k matrix). For each unknown, alternate points (in
# a random order) are positive and negative, and within each sign the magnitudes are stratified
# on a log scale over 10^_STAND_IN_LOG10: point q of the m of one sign draws from the q-th of m
# equal slices. So every unknown is probed with both signs, and with values both below 1 and
# above 100 once there are 8 probe points (4 of each sign).
function _stand_in_values(rng, k::Integer, n::Integer)
    W = Matrix{Float64}(undef, n, k)
    lo, hi = _STAND_IN_LOG10
    for c in 1:k
        signs = Random.shuffle(rng, Float64[isodd(j) ? 1 : -1 for j in 1:n])
        for sg in (1.0, -1.0)
            idx = findall(==(sg), signs)
            slices = Random.randperm(rng, length(idx))
            for (q, j) in enumerate(idx)
                u = (slices[q] - 1 + rand(rng)) / length(idx)
                W[j, c] = sg * 10.0^(lo + (hi - lo) * u)
            end
        end
    end
    return W
end

_probe_text(vars, p) = join(["$(_fresh_name(v)) = $(round(x; sigdigits = 3))"
                             for (v, x) in zip(vars, p)], ", ")

# Whether the probes are evidence that Σ ts = 0, when it is 0 (to rtol) at every point of `pts`
# (values of `vars`); see above. Returns (why, what): why is :none when they are evidence;
# otherwise :vanishing (what: a term that is 0 at every probe point), :piecewise (what: the
# non-analytic parts on whose values the cancellation depends) or :nonfinite (what: a probe
# point at which a term is not finite).
function _probe_evidence(ts::Vector{Any}, vars::Vector{Any}, pts, rng, rtol)
    ts = Any[_fold_ifelse(x) for x in ts]            # ifelse(c, x, x) is x, not an opaque part
    f = _compile(ts, vars)
    seen = falses(length(ts))              # 1., on the terms as they are
    for p in pts
        y = f(p)
        all(isfinite, y) || return (why = :nonfinite, what = _probe_text(vars, p))
        seen .|= y .!= 0
    end
    parts = Any[]
    for x in ts
        _opaque_parts!(parts, x)
    end
    evidence = if isempty(parts)
        all(seen)                          # 2. holds: the terms are analytic
    else
        ws = Any[_fresh(:w, Symbol(k)) for k in eachindex(parts)]
        sub = Dict{Any,Any}(zip(parts, ws))
        as = Any[_unwrap(x) isa SU.BasicSymbolic ?
                 _unwrap(Symbolics.substitute(_wrap(x), sub; fold = Val(false))) : x
                 for x in ts]
        fa = _compile(as, vcat(vars, ws))
        free = falses(length(as))          # 1., with the unknowns in place
        cancels = true
        # at least _MIN_STAND_IN_POINTS draws of the unknowns (cycling through the probe points),
        # so that each unknown takes both signs and small and large magnitudes whatever `probes`
        m = max(length(pts), _MIN_STAND_IN_POINTS)
        W = _stand_in_values(rng, length(ws), m)
        for j in 1:m
            p = pts[mod1(j, length(pts))]
            w = W[j, :]
            y = fa(vcat(p, w))
            if !all(isfinite, y)
                # a large value can overflow (exp(w) at w = 1000): the same signs, redrawn with
                # magnitudes in (0.1, 1)
                w = sign.(w) .* (0.1 .+ 0.9 .* rand(rng, length(w)))
                y = fa(vcat(p, w))
            end
            if all(isfinite, y)
                free .|= y .!= 0
                abs(sum(y)) <= rtol * sum(abs, y) || (cancels = false)
            else
                cancels = false
            end
        end
        all(free) && cancels
    end
    evidence && return (why = :none, what = "")
    k = findfirst(!, seen)
    k === nothing || return (why = :vanishing, what = _display(ts[k]))
    shown = ["`$(_display(x))`" for x in parts]
    return (why = :piecewise, what = "the values that " * join(shown, ", ", " and ") *
                                     (length(shown) == 1 ? " takes" : " take"))
end

# Why the probes cannot decide a difference (for messages), from _probe_evidence.
function _undecided_why(why::Symbol, what, probes)
    why === :nonfinite && return "is not finite at the probe point $(what)"
    why === :vanishing && return (
        "does not cancel: its term `$(what)` is 0 at all $(probes) probe points, so they are no " *
        "evidence that the difference is 0 (a term that vanishes on the probe box but not " *
        "everywhere, such as ν*ifelse(t > 150, 1, 0) or max(x - 2, 0), or one too small to " *
        "evaluate)")
    return "is 0 at all $(probes) probe points only through $(what) there, so they are no " *
           "evidence that it is 0 (an identity is confirmed numerically only when it holds " *
           "whatever values its non-analytic parts, such as max, min, abs or ifelse, take: " *
           "max(x, 0) = x holds only for x ≥ 0)"
end

# The verdict of a comparison: :equal, :different or :undecided, with the component and, for
# :undecided, why (see _probe_evidence).
_verdict(v::Symbol, comp::Integer = 0, why::Symbol = :none, what = "") =
    (verdict = v, comp = Int(comp), why = why, what = string(what))

# =============================================================================================
# verify (§D.7)
# =============================================================================================

# The residual problem of a semiconjugacy, in fresh variables: source states xs, parameters ps,
# the source field F, the map π, and the target field composed with π (with the parameter map).
struct _Residual
    snames::Vector{Symbol}
    tnames::Vector{Symbol}
    xs::Vector{Any}
    ps::Vector{Any}
    pnames::Vector{Symbol}
    F::Vector{Any}
    π::Vector{Any}
    JF::Vector{Any}
    Gπ::Vector{Any}
    unbound::Vector{Symbol}
end

function _residual(m::Semiconjugacy)
    src, tgt = m.source, m.target
    sn = NEC.state_names(src)
    tn = NEC.state_names(tgt)
    xs = Any[_fresh(:x, n) for n in sn]
    sdict = Dict{Symbol,Any}(zip(sn, xs))
    fsrc(n) = haskey(sdict, n) ? sdict[n] : _fresh(:p, n)
    F = Any[_rename(f, fsrc) for f in src.rhs]
    π = Any[_rename(last(p), fsrc) for p in m.map]
    pmap = Dict{Symbol,Any}(NEC._coordinate_name(k) => _rename(v, fsrc)
                            for (k, v) in m.parameter_map)
    tdict = Dict{Symbol,Any}(zip(tn, π))
    ftgt(n) = haskey(tdict, n) ? tdict[n] : haskey(pmap, n) ? pmap[n] : _fresh(:p, n)
    Gπ = Any[_rename(g, ftgt) for g in tgt.rhs]
    J = Symbolics.jacobian(Any[_wrap(e) for e in π], Any[_wrap(x) for x in xs])
    Fw = Any[_wrap(f) for f in F]
    JF = Any[_unwrap(sum(J[i, j] * Fw[j] for j in eachindex(Fw); init = Symbolics.Num(0)))
             for i in eachindex(π)]
    # parameters: every fresh ‹p› variable that occurs
    allv = _variables(vcat(F, π, Gπ))
    ps = Any[v for v in allv if startswith(string(_name(v)), "‹p›")]
    pnames = Symbol[_fresh_name(v) for v in ps]
    # target parameters that neither the source nor the parameter map determines
    srcnames = Set(Symbol[_fresh_name(v) for v in _variables(vcat(F, π))
                          if startswith(string(_name(v)), "‹p›")])
    for (k, v) in m.parameter_map, w in _variables(pmap[NEC._coordinate_name(k)])
        push!(srcnames, _fresh_name(w))
    end
    for p in src.parameters
        push!(srcnames, NEC._coordinate_name(p))
    end
    unbound = Symbol[n for n in pnames if !(n in srcnames) && n !== :t]     # t is time
    return _Residual(sn, tn, xs, ps, pnames, F, π, JF, Gπ, unbound)
end

# Numeric residuals at seeded probes: the largest relative residual and its component, and the
# probe points (values of vcat(R.xs, R.ps)).
function _numeric_residual(R::_Residual, domain, probes, rng_seed)
    boxes = _boxes(domain)
    vars = vcat(R.xs, R.ps)
    fJF = _compile(R.JF, vars)
    fG = _compile(R.Gπ, vars)
    rng = Random.Xoshiro(rng_seed)
    worst, worst_i = 0.0, 0
    pts = Vector{Float64}[]
    for j in 1:probes
        vals = Float64[_draw(rng, get(boxes, n, _STATE_BOX)) for n in R.snames]
        append!(vals, Float64[_draw_param(rng, n, boxes, j, probes) for n in R.pnames])
        push!(pts, vals)
        a = fJF(vals)
        b = fG(vals)
        (all(isfinite, a) && all(isfinite, b)) || throw(ArgumentError(
            "verify: the fields are not finite at a probe point; restrict the probe boxes " *
            "with the source's `domain`"))
        res = abs.(a .- b)
        scale = max(maximum(abs, a; init = 0.0), maximum(abs, b; init = 0.0))
        rel = scale > 0 ? res ./ scale : res
        if !isempty(rel)
            r, i = findmax(rel)
            r > worst && ((worst, worst_i) = (r, i))
        end
    end
    return worst, worst_i, pts
end

# The components (among `idx`) whose residual is 0 at the probe points `pts` without the probes
# being evidence that it is 0 (_probe_evidence), as (component, evidence). This is asked of every
# component that is not exactly 0, however the two sides round: whether a term is seen, or a
# cancellation depends on a non-analytic part, does not depend on rounding.
function _undecided_components(R::_Residual, idx, pts, rtol, rng_seed)
    out = Tuple{Int,NamedTuple}[]
    vars = vcat(R.xs, R.ps)
    rng = Random.Xoshiro(_atom_seed(rng_seed))
    for i in idx
        ts = _difference_terms(R.JF[i], R.Gπ[i], rtol)
        isempty(ts) && continue
        # the probes first; the (costlier) exact zero test only when they are not evidence
        ev = _probe_evidence(ts, vars, pts, rng, rtol)
        (ev.why === :none || _symbolic_zero(sum(_wrap, ts))) && continue
        push!(out, (i, ev))
    end
    return out
end

_residual_text(R::_Residual, i) = _display(Symbolics.simplify(Symbolics.expand(
    Symbolics.wrap(R.JF[i]) - Symbolics.wrap(R.Gπ[i]))))

"""
    verify(m::Semiconjugacy; method = :auto, probes = 16, rng_seed = 1, rtol = 1e-10)
        -> VerificationResult

Check the semiconjugacy identity Dπ·F = G∘π of `m` (the target parameters replaced through the
parameter map; unlisted target parameters are the source parameters of the same name).

- `:symbolic`: every component of Jπ·F − G∘π, with `substitute(…; fold = Val(true))` (without
  folding, `exp(0)` survives and zero tests fail), expanded and simplified, must be 0. If it is
  not, the result is not ok, and the residual is still measured at the numeric probes.
- `:numeric`: seeded random probes (source states and parameters drawn from the source's
  `domain`, default boxes (0.05, 0.95) for states, (0.1, 1.0) for parameters and (0.1, 1000)
  on a log scale for time t); ok when the largest relative residual
  ‖Jπ·F − G∘π‖∞ / max(‖Jπ·F‖∞, ‖G∘π‖∞) is at most `rtol`, and the probes are evidence that
  every component is 0. In each component that is not exactly 0, the terms of the residual
  that do not cancel must each be non-zero at some probe point (a term such as
  ν·ifelse(t > 150, 1, 0) on a box of t below 150, or max(a − 2, 0) for a below 2, is not seen,
  and the others may cancel without it), and their cancellation must hold whatever values the
  non-analytic parts (max, min, abs, ifelse, …; every function other than the arithmetic
  operations, powers, exp, log, sqrt and the trigonometric and hyperbolic functions) take:
  each is replaced by an unknown drawn afresh at every probe, of either sign and of magnitude
  from 0.1 to 1000 (log scale; half of the probes of each unknown negative). So −(a + b)x
  against −ax − bx + max(a − 2, 0)x, or x against x/(1 + max(a − 2, 0)), is not ok (both are 0
  on the default box of a, but not for a > 2), and neither is sqrt(g²)x against gx for
  g = ifelse(a > 2, −1, 1) (it holds only while g > 0), while a residual
  max(a − 2, 0)·(sin²b + cos²b − 1)x is 0 whatever the value of the max, and is ok. The check
  is conservative: an identity that holds only for the values the part can take
  (sqrt(max(u, 0)²) = max(u, 0)) is not ok either; write it without the part.
- `:auto`: symbolic first; numeric when the symbolic residual is not provably 0 or the source
  has more than 50 states.

The symbolic zero test is budgeted, so that `verify` does not overflow the stack or run for
minutes on PGFs with floating-point coefficients (empirical, negative binomial, power-law
degrees): floating-point constants are replaced by the simplest rationals within a relative
1e-12 of them before fractions are combined (so 0.8333333333333334 is 5/6, while a rounding
residue such as 1e-16·x stays non-zero), and a residual is simplified only when it has at most
1000 nodes after expansion. What it does not show to be 0 is decided by the numeric probes
(method `:numeric`).

The numeric probes confirm an analytic identity on the probe box, and hence on the connected
region around it where the residual stays analytic, but not across a branch point outside the
box: sqrt((2 − a)²)y against (2 − a)y is ok on the default box a ∈ (0.1, 1.0), although the two
differ for a > 2. The default parameter box is narrow (rates and κ above 1 are common): give
the source a `domain` that covers the parameter values the morphism is claimed for.

`details` names the worst component and prints the nonzero symbolic residuals.
"""
function NEC.verify(m::Semiconjugacy; method::Symbol = :auto, probes::Integer = 16,
                    rng_seed::Integer = 1, rtol::Real = 1e-10)
    method in (:auto, :symbolic, :numeric) || throw(ArgumentError(
        "verify: method must be :auto, :symbolic or :numeric; got :$(method)"))
    probes >= 1 || throw(ArgumentError("verify: probes must be ≥ 1"))
    R = _residual(m)
    n = length(R.tnames)
    notes = String[]
    isempty(R.unbound) || push!(notes, "target parameter(s) $(join(R.unbound, ", ")) are " *
                                       "determined neither by the source nor by the parameter map")
    try_symbolic = method === :symbolic || (method === :auto && length(R.snames) <= 50)
    nonzero = Int[]
    if try_symbolic
        nonzero = [i for i in 1:n
                   if !_symbolic_zero(Symbolics.wrap(R.JF[i]) - Symbolics.wrap(R.Gπ[i]))]
        if isempty(nonzero)
            return VerificationResult(true, :symbolic, 0.0, 0,
                                      "Dπ·F − G∘π simplifies to 0 in all $(n) components " *
                                      "($(join(R.tnames, ", ")))" *
                                      (isempty(notes) ? "" : "; " * join(notes, "; ")))
        end
    end
    worst, wi, pts = _numeric_residual(R, m.source.domain, probes, rng_seed)
    ok = method !== :symbolic && worst <= rtol
    undecided = Tuple{Int,NamedTuple}[]
    if ok
        # every component that is not exactly 0, whether or not its two sides rounded alike
        undecided = _undecided_components(R, try_symbolic ? nonzero : 1:n, pts, rtol, rng_seed)
        ok = isempty(undecided)
    end
    head = if method === :symbolic
        "Dπ·F − G∘π does not simplify to 0 in component(s) $(join(R.tnames[nonzero], ", "))"
    elseif !isempty(undecided)
        "Dπ·F − G∘π cannot be decided in component(s) " *
        "$(join(R.tnames[first.(undecided)], ", ")): it is 0 to rtol = $(rtol) at $(probes) " *
        "probes, but they are no evidence that it is 0; widen the probe boxes with the " *
        "source's `domain`, or simplify the fields"
    elseif ok
        "Dπ·F − G∘π is 0 to rtol = $(rtol) at $(probes) probes (max relative residual " *
        "$(worst))" * (isempty(nonzero) || !try_symbolic ? "" :
                       "; symbolic simplification was not conclusive for " *
                       "$(join(R.tnames[nonzero], ", "))")
    else
        "Dπ·F − G∘π ≠ 0: max relative residual $(worst) at $(probes) probes" *
        (wi == 0 ? "" : ", worst in component $(R.tnames[wi])")
    end
    lines = [head]
    if !isempty(undecided)
        for (i, ev) in undecided
            push!(lines, "residual of d$(R.tnames[i])/dt: $(_residual_text(R, i)): it " *
                         _undecided_why(ev.why, ev.what, probes))
        end
    elseif !ok
        shown = !isempty(nonzero) ? nonzero : wi == 0 ? Int[] : [wi]
        for i in shown
            push!(lines, "residual of d$(R.tnames[i])/dt: $(_residual_text(R, i))")
        end
    end
    append!(lines, notes)
    return VerificationResult(ok, method === :symbolic ? :symbolic : :numeric, worst,
                              probes, join(lines, "\n"))
end

# =============================================================================================
# pushforward
# =============================================================================================

"""
    pushforward(m::Semiconjugacy, sol, tgrid; p = Dict{Symbol,Float64}())
        -> Dict{Symbol,Vector{Float64}}

The target coordinates π(u(t)) along a source trajectory, on `tgrid`, keyed by target state
name (so that both sides of a morphism can be plotted together). `p` gives the values (by name)
of the source parameters that the map uses (e.g. `q` and `μ` in S = q e^{μ(θ−1)}).

The source trajectory `sol` may be

- an `AbstractDict` from source state names to vectors of values on `tgrid`;
- an `AbstractMatrix` whose rows are the source states at the times of `tgrid` (columns in the
  order of the source states);
- a vector of state vectors (one per time, in source state order), like `sol.u`;
- anything callable, `sol(t)` returning the source state vector (in source state order) or a
  `Dict` by name. For an MTK solution whose unknowns are in another order, pass
  `t -> sol(t; idxs = states)`.
"""
function NEC.pushforward(m::Semiconjugacy, sol, tgrid; p::AbstractDict = Dict{Symbol,Float64}())
    src = m.source
    sn = NEC.state_names(src)
    tn = NEC.state_names(m.target)
    xs = Any[_fresh(:x, n) for n in sn]
    sdict = Dict{Symbol,Any}(zip(sn, xs))
    vals = _by_name(p)
    missing_ = Symbol[]
    function fsrc(n)
        haskey(sdict, n) && return sdict[n]
        haskey(vals, n) && return vals[n]
        n in missing_ || push!(missing_, n)
        return _fresh(:p, n)
    end
    π = Any[_rename(last(q), fsrc) for q in m.map]
    isempty(missing_) || throw(ArgumentError(
        "pushforward(:$(m.name)): the map needs values for the parameter(s) " *
        "$(join(missing_, ", ")); pass p = Dict(…)"))
    f = _compile(π, xs)
    ts = collect(tgrid)
    U = _trajectory(sol, ts, sn)
    out = Dict{Symbol,Vector{Float64}}(n => Vector{Float64}(undef, length(ts)) for n in tn)
    for k in eachindex(ts)
        y = f(U[k])
        for (i, n) in enumerate(tn)
            out[n][k] = y[i]
        end
    end
    return out
end

# The source states along the grid, as one Vector{Float64} per time point.
function _trajectory(sol::AbstractDict, ts, sn)
    d = _by_name(sol)
    for n in sn
        haskey(d, n) || throw(ArgumentError("pushforward: no values for the source state $(n)"))
        length(d[n]) == length(ts) || throw(ArgumentError(
            "pushforward: $(length(d[n])) values of $(n) for $(length(ts)) time points"))
    end
    return [Float64[d[n][k] for n in sn] for k in eachindex(ts)]
end
function _trajectory(sol::AbstractMatrix, ts, sn)
    size(sol) == (length(ts), length(sn)) || throw(ArgumentError(
        "pushforward: the matrix must be (time points × source states) = " *
        "$((length(ts), length(sn))); got $(size(sol))"))
    return [Float64.(sol[k, :]) for k in eachindex(ts)]
end
function _trajectory(sol::AbstractVector{<:AbstractVector}, ts, sn)
    length(sol) == length(ts) || throw(ArgumentError(
        "pushforward: $(length(sol)) state vectors for $(length(ts)) time points"))
    return [_state_vector(u, sn) for u in sol]
end
_trajectory(sol, ts, sn) = [_state_vector(sol(t), sn) for t in ts]

function _state_vector(u::AbstractVector, sn)
    length(u) == length(sn) || throw(ArgumentError(
        "pushforward: a state vector has $(length(u)) entries; the source has " *
        "$(length(sn)) states ($(join(sn, ", ")))"))
    return Float64.(collect(u))
end
function _state_vector(u::AbstractDict, sn)
    d = _by_name(u)
    return Float64[d[n] for n in sn]
end

# =============================================================================================
# vector_fields_equal
# =============================================================================================

_strip_namespace(n::Symbol) = (s = string(n); k = findlast('₊', s);
                               k === nothing ? n : Symbol(s[nextind(s, k):end]))

# Names of the states and parameters of `ode` after a renaming rule; if the rule makes names
# collide, the exact names are kept.
function _normal_names(names::Vector{Symbol}, rule)
    out = Symbol[rule(n) for n in names]
    return allunique(out) ? out : names
end

# The fields of `ode` in fresh variables: states named by `snames` (role `role`), parameters by
# the rule `prule` (shared role :p).
function _fields(ode::SymbolicODE, snames::Vector{Symbol}, role::Symbol, prule)
    orig = NEC.state_names(ode)
    d = Dict{Symbol,Any}(o => _fresh(role, s) for (o, s) in zip(orig, snames))
    f(n) = haskey(d, n) ? d[n] : _fresh(:p, prule(n))
    return Any[_rename(e, f) for e in ode.rhs]
end

# The additive terms of an expanded expression; a quotient whose numerator is a sum is split
# (expand does not distribute over division).
function _additive_terms(x)
    x = _unwrap(x)
    _iszero_const(x) && return Any[]
    if x isa SU.BasicSymbolic && SU.iscall(x) && SU.operation(x) === (+)
        return reduce(vcat, (_additive_terms(a) for a in _sorted_arguments(x)); init = Any[])
    elseif x isa SU.BasicSymbolic && SU.iscall(x) && SU.operation(x) === (/)
        num, den = SU.arguments(x)
        ts = _additive_terms(Symbolics.expand(_wrap(num)))
        length(ts) > 1 &&
            return Any[_unwrap(Symbolics.wrap(t) / Symbolics.wrap(den)) for t in ts]
    end
    return Any[x]
end

# A term as (numeric coefficient, the rest): 2.5τ*S is (2.5, τ*S).
function _split_term(x)
    x = _unwrap(x)
    n = _number(x)
    n !== nothing && return n, 1
    if x isa SU.BasicSymbolic && SU.iscall(x) && SU.operation(x) === (*)
        k = 1
        rest = Any[]
        for a in SU.arguments(x)
            m = _number(a)
            m === nothing ? push!(rest, a) : (k *= m)
        end
        isempty(rest) && return k, 1
        return k, length(rest) == 1 ? _unwrap(rest[1]) : _unwrap(prod(Symbolics.wrap, rest))
    elseif x isa SU.BasicSymbolic && SU.iscall(x) && SU.operation(x) === (/)
        num, den = SU.arguments(x)
        k, m = _split_term(num)
        return k, _unwrap(Symbolics.wrap(m) / Symbolics.wrap(den))
    end
    return 1, x
end

# The terms of a − b that do not cancel. Both sides are expanded and their terms collected by
# monomial (the term without its numeric coefficient), with the net coefficient and the gross
# one (the sum of the absolute values of the coefficients on both sides). A monomial whose net
# is at most rtol times its gross is floating-point netting and cancels; every other monomial
# is kept with its net coefficient, however small, so a missing 2e-13*S*I next to 0.1*I is a
# difference. If an expansion fails, the terms are a and −b themselves.
function _difference_terms(a, b, rtol)
    ms = Any[]
    net = Number[]
    gross = Float64[]
    try
        for (x, sg) in ((a, 1), (b, -1))
            x = _unwrap(x)
            e = _number(x) === nothing ? _unwrap(Symbolics.expand(_wrap(x))) : x
            for u in _additive_terms(e)
                k, m = _split_term(u)
                i = findfirst(y -> isequal(y, m), ms)
                if i === nothing
                    push!(ms, m)
                    push!(net, sg * k)
                    push!(gross, Float64(abs(k)))
                else
                    net[i] += sg * k
                    gross[i] += Float64(abs(k))
                end
            end
        end
    catch
        return Any[_unwrap(a), _unwrap(-_wrap(_unwrap(b)))]
    end
    return Any[_unwrap(net[i] * _wrap(ms[i])) for i in eachindex(ms)
               if !(iszero(net[i]) || abs(net[i]) <= rtol * gross[i])]
end

# A probe value for the fresh variable v: time (named t, in any role) from the time box on a log
# scale, a parameter from the parameter box, a state from the state box, unless `boxes` (by name)
# gives one.
function _draw_var(rng, v, boxes, j::Integer = 1, probes::Integer = 1)
    n = _fresh_name(v)
    n === :t && return _draw_time(rng, get(boxes, :t, _TIME_BOX), j, probes)
    return _draw(rng, get(boxes, n, startswith(string(_name(v)), "‹p›") ? _PARAM_BOX : _STATE_BOX))
end

# Do the expression vectors a and b agree componentwise? Returns a _verdict: :equal, :different
# (with the first component found to differ) or :undecided (with the first component that the
# probes cannot decide, and why). Each component's difference is reduced to the terms that do not
# cancel (_difference_terms); if any remain and do not simplify to 0 (exactly, after folding
# constants), they are evaluated at `probes` seeded points, where their sum must be at most rtol
# times the sum of their absolute values, component by component. The tolerance is relative to
# the terms that differ, not to the size of the fields, so a small missing term is never masked
# by large terms of the same (or another) component. A difference that the probes find to be 0
# is equal only when they are evidence of that (_probe_evidence): an identity that the
# simplifier cannot prove (sin²x + cos²x − 1) passes; a term that is 0 at every probe point
# (ν·ifelse(t > 150, 1, 0), max(x − 2, 0)), or a cancellation that depends on the value of a
# non-analytic part (max(x, 0) − x), is undecided, and so is a term that is not finite at a probe
# point (unless another probe point shows a difference).
function _agreement(a::Vector{Any}, b::Vector{Any}, boxes; rtol, probes, rng_seed)
    length(a) == length(b) || return _verdict(:different)
    diffs = Vector{Any}[]
    comps = Int[]
    for i in eachindex(a)
        ts = _difference_terms(a[i], b[i], rtol)
        isempty(ts) && continue
        _symbolic_zero(sum(_wrap, ts)) && continue
        push!(diffs, ts)
        push!(comps, i)
    end
    isempty(diffs) && return _verdict(:equal)
    terms = reduce(vcat, diffs)
    vars = _variables(terms)
    f = _compile(terms, vars)
    stops = cumsum(length.(diffs))
    ranges = [(k == 1 ? 1 : stops[k - 1] + 1):stops[k] for k in eachindex(stops)]
    rng = Random.Xoshiro(rng_seed)
    pts = [Float64[_draw_var(rng, v, boxes, j, probes) for v in vars] for j in 1:probes]
    bad = zeros(Int, length(ranges))     # a probe point where a term of component k is not finite
    for (j, p) in enumerate(pts)
        y = f(p)
        for (k, r) in enumerate(ranges)
            yr = view(y, r)
            if all(isfinite, yr)
                abs(sum(yr)) <= rtol * sum(abs, yr) || return _verdict(:different, comps[k])
            elseif bad[k] == 0
                bad[k] = j
            end
        end
    end
    arng = Random.Xoshiro(_atom_seed(rng_seed))
    for k in eachindex(ranges)
        bad[k] > 0 &&
            return _verdict(:undecided, comps[k], :nonfinite, _probe_text(vars, pts[bad[k]]))
        ev = _probe_evidence(diffs[k], vars, pts, arng, rtol)
        ev.why === :none || return _verdict(:undecided, comps[k], ev.why, ev.what)
    end
    return _verdict(:equal)
end

# The verdict (_verdict: :equal, :different or :undecided, with why) on whether the scalar
# expressions x and y are equal, every variable identified by name as a parameter (or time t),
# by the rule of vector_fields_equal: exact after folding, else seeded probes that must be
# evidence (_probe_evidence). x and y may be numbers, Symbols, Exprs (IR rates) or symbolic
# expressions; `domain` gives probe boxes by name. For the comparisons of rates outside this
# extension (ir/equivalence.jl, the Catalyst front end), so that they follow the same rule (§J.3).
function _expressions_verdict(x, y; domain = Pair{Any,Tuple{Float64,Float64}}[],
                              rtol::Real = 1e-10, probes::Integer = 8, rng_seed::Integer = 1)
    f(n) = _fresh(:p, n)
    return _agreement(Any[_rename(x, f)], Any[_rename(y, f)], _boxes(domain); rtol, probes,
                      rng_seed)
end

# The difference a − b, as text (for messages).
_difference_text(a, b) = _display(Symbolics.simplify(Symbolics.wrap(a) - Symbolics.wrap(b)))

"""
    vector_fields_equal(a::SymbolicODE, b::SymbolicODE; rename = :auto, rtol = 1e-10,
                        probes = 8, rng_seed = 1, max_renamings = 50_000) -> Bool

Whether the vector fields of `a` and `b` are equal up to a renaming of the coordinates; see the
docstring in NetworkEpiCore for the renaming rules.
"""
function NEC.vector_fields_equal(a::SymbolicODE, b::SymbolicODE; rename = :auto,
                                 rtol::Real = 1e-10, probes::Integer = 8, rng_seed::Integer = 1,
                                 max_renamings::Integer = 50_000)
    max_renamings >= 1 || throw(ArgumentError("vector_fields_equal: max_renamings must be ≥ 1"))
    (rename in (:auto, :search, :none) || rename isa AbstractDict) || throw(ArgumentError(
        "vector_fields_equal: rename must be :auto, :search, :none or a Dict of names; got " *
        "$(repr(rename))"))
    length(a.states) == length(b.states) || return false
    explicit = rename isa AbstractDict ?
               Dict{Symbol,Symbol}(_name(k) => _name(v) for (k, v) in rename) :
               Dict{Symbol,Symbol}()
    search = rename === :auto || rename === :search
    base = search ? _strip_namespace : identity
    rule_a(n) = haskey(explicit, n) ? explicit[n] : base(n)
    rule_b(n) = base(n)
    an = _normal_names(NEC.state_names(a), rule_a)
    bn = _normal_names(NEC.state_names(b), rule_b)
    sboxa, pboxa = _split_boxes(a, an, rule_a)
    sboxb, pboxb = _split_boxes(b, bn, rule_b)
    pboxes = _meet_boxes(a, b, pboxa, pboxb)       # parameters and time, shared by name
    Fb = _fields(b, bn, :v, rule_b)
    if rename !== :search && Set(an) == Set(bn)
        # the same state names: they are trusted (matched by name)
        Fa = _fields(a, an, :v, rule_a)
        order = [findfirst(==(n), an) for n in bn]
        boxes = merge(pboxes, _meet_boxes(a, b, sboxa, sboxb))
        v = _agreement(Fa[order], Fb, boxes; rtol, probes, rng_seed)
        v.verdict === :undecided &&
            _undecided_error(a, b, bn[v.comp], Fa[order][v.comp], Fb[v.comp], v, probes)
        return v.verdict === :equal
    end
    search || return false
    return _search_bijection(a, b, an, bn, rule_a, rule_b, sboxa, sboxb, pboxes; rtol, probes,
                             rng_seed, max_leaves = max_renamings)
end

const _Boxes = Dict{Symbol,Tuple{Float64,Float64}}

# The probe boxes of the domain of `ode`, keyed by the names its coordinates have in the
# comparison (`snames` for its states, the renaming rule for its parameters and time), as two
# dictionaries: the boxes of its states, and the others.
function _split_boxes(ode::SymbolicODE, snames::Vector{Symbol}, rule)
    orig = NEC.state_names(ode)
    s, p = _Boxes(), _Boxes()
    for (k, box) in _boxes(ode.domain)
        i = findfirst(==(k), orig)
        i === nothing ? (p[rule(k)] = box) : (s[snames[i]] = box)
    end
    return s, p
end

# The box in which a coordinate is probed when either system may give it one (`nothing`: not
# given): the intersection, which is empty (lo ≥ hi) when the two boxes are disjoint.
_meet(::Nothing, ::Nothing) = nothing
_meet(::Nothing, y) = y
_meet(x, ::Nothing) = x
_meet(x, y) = (max(x[1], y[1]), min(x[2], y[2]))
_isempty_box(x) = x !== nothing && x[1] >= x[2]

# The boxes of the coordinates that a and b share by name: each is probed where both domains
# hold. Disjoint boxes leave nothing to compare: an ArgumentError.
function _meet_boxes(a, b, x::_Boxes, y::_Boxes)
    out = _Boxes()
    for n in union(keys(x), keys(y))
        box = _meet(get(x, n, nothing), get(y, n, nothing))
        _isempty_box(box) && throw(ArgumentError(_disjoint_text(a, b, n, x[n], n, y[n])))
        out[n] = box
    end
    return out
end

_disjoint_text(a, b, m, x, n, y) =
    "vector_fields_equal(:$(a.name), :$(b.name)): the domains give disjoint probe boxes, " *
    "$(m) ∈ $(x) in :$(a.name) and $(n) ∈ $(y) in :$(b.name), so the fields cannot be compared " *
    "there"

NEC.vector_fields_equal(a, b; kw...) =
    NEC.vector_fields_equal(NEC.symbolic_ode(a), NEC.symbolic_ode(b); kw...)

# The answer is unknown, not false: the probes are no evidence that the difference x − y of
# d(n)/dt is 0 (the _verdict v says why). A difference that is not finite at a probe point is an
# ArgumentError, as in verify.
function _undecided_error(a, b, n, x, y, v, probes)
    head = "vector_fields_equal(:$(a.name), :$(b.name)): cannot decide d$(n)/dt: the " *
           "difference `$(_difference_text(x, y))` $(_undecided_why(v.why, v.what, probes))"
    v.why === :nonfinite && throw(ArgumentError(
        head * "; restrict the probe boxes with a `domain` on which both fields are defined"))
    tbox = " (time t is probed in (0.1, 1000) on a log scale by default)"
    hint = v.why === :vanishing ?
           "give the variables of the difference a `domain` box where the term is not 0" * tbox *
           ", or raise probes" :
           "give its variables a `domain` box on which the difference shows if it is not 0" *
           tbox * ", or write the fields without the non-analytic parts that the identity " *
           "depends on"
    error(head * "; the answer is unknown, not false: " * hint)
end

# The additive terms of the components of F (expanded), flattened, with the range of each
# component's terms; evaluated, they give each component's value and the size of its terms
# (_values).
function _term_list(F::Vector{Any})
    ts = Any[]
    rs = UnitRange{Int}[]
    for f in F
        t = try
            _additive_terms(_number(f) === nothing ? Symbolics.expand(_wrap(_unwrap(f))) : f)
        catch
            Any[_unwrap(f)]
        end
        push!(rs, (length(ts) + 1):(length(ts) + length(t)))
        append!(ts, t)
    end
    return ts, rs
end

# The value of each component, and the sum of the absolute values of its terms, from the values
# `y` of the terms of _term_list.
_values(y, rs) = (Float64[sum(view(y, r); init = 0.0) for r in rs],
                  Float64[sum(abs, view(y, r); init = 0.0) for r in rs])

# The points of the diagonal (every state equal) at which the fields are evaluated for the
# signature of the bijection search, in the default state box; in a common box of the states
# they are placed at the same relative positions.
const _DIAGONAL = (0.23, 0.61, 0.87)

_draw_at((lo, hi), u) = lo + (hi - lo) * u

# Search for a bijection σ between the states of a and b with F_a[i] ∘ σ⁻¹ = F_b[σ(i)].
# Candidates are narrowed by a renaming-invariant signature (each field evaluated on the
# diagonal, where all states equal c, for three values of c in the box common to all states),
# then checked at two generic points, then by _agreement. Values are compared with a tolerance
# relative to the size of the terms of the fields, not to their values (rounding in
# sin²x + cos²x − 1 + 10⁻⁹x exceeds 10⁻⁸ of its value), so neither test rejects a renaming under
# which the fields are equal. A value that is not finite is no evidence either way: it excludes
# no candidate and rejects no bijection, and _agreement decides (the ArgumentError of
# _undecided_error if no probe point can). The probe boxes follow σ: a's box of its state i and
# b's box of its state σ(i) both bound the coordinate they share. Giving up after `max_leaves`
# complete assignments is an error: the answer is unknown, not false.
function _search_bijection(a, b, an, bn, rule_a, rule_b, sboxa::_Boxes, sboxb::_Boxes,
                           pboxes::_Boxes; rtol, probes, rng_seed,
                           max_leaves::Integer = 50_000)
    n = length(an)
    Fa = _fields(a, an, :a, rule_a)          # a-states in role :a
    Fb = _fields(b, bn, :v, rule_b)
    xa = Any[_fresh(:a, s) for s in an]
    xb = Any[_fresh(:v, s) for s in bn]
    params = Any[v for v in _variables(vcat(Fa, Fb)) if startswith(string(_name(v)), "‹p›")]
    rng = Random.Xoshiro(rng_seed)
    pvals = Float64[_draw_param(rng, _fresh_name(v), pboxes) for v in params]
    ta, ra = _term_list(Fa)
    tb, rb = _term_list(Fb)
    fa = _compile(ta, vcat(xa, params))
    fb = _compile(tb, vcat(xb, params))
    # a looser tolerance than _agreement's, which accepts differences up to rtol of their terms
    tol = max(1e-8, 4 * rtol)
    agree(va, sa, vb, sb) = !(isfinite(sa) && isfinite(sb)) || abs(va - vb) <= tol * max(sa, sb)
    common = reduce(_meet, vcat(collect(values(sboxa)), collect(values(sboxb))); init = nothing)
    cand = if _isempty_box(common)
        [collect(1:n) for _ in 1:n]          # no point of the diagonal is in every state's box
    else
        lo, hi = common === nothing ? _STATE_BOX : common
        cs = [_draw_at((lo, hi), (c - _STATE_BOX[1]) / (_STATE_BOX[2] - _STATE_BOX[1]))
              for c in _DIAGONAL]
        siga = [_values(fa(vcat(fill(c, n), pvals)), ra) for c in cs]
        sigb = [_values(fb(vcat(fill(c, n), pvals)), rb) for c in cs]
        [[j for j in 1:n
          if all(agree(siga[k][1][i], siga[k][2][i], sigb[k][1][j], sigb[k][2][j])
                 for k in eachindex(cs))] for i in 1:n]
    end
    any(isempty, cand) && return false
    # two generic points, placed in the probe boxes of each bijection
    U = [rand(rng, n) for _ in 1:2]
    order = sortperm(length.(cand))
    σ = zeros(Int, n)
    used = falses(n)
    leaves = Ref(0)
    undecided = Ref{Any}(nothing)            # a bijection that the probes could not decide
    clash = Ref{Any}(nothing)                # a bijection that pairs states of disjoint boxes
    function leafboxes()
        bx = copy(pboxes)
        for i in 1:n
            box = _meet(get(sboxa, an[i], nothing), get(sboxb, bn[σ[i]], nothing))
            if _isempty_box(box)
                clash[] === nothing && (clash[] = (i, σ[i]))
                return nothing
            end
            box === nothing || (bx[bn[σ[i]]] = box)
        end
        return bx
    end
    function leafok(bx)
        for u in U
            y = Float64[_draw_at(get(bx, bn[j], _STATE_BOX), u[j]) for j in 1:n]
            va, sa = _values(fa(vcat(y[σ], pvals)), ra)
            vb, sb = _values(fb(vcat(y, pvals)), rb)
            all(agree(va[i], sa[i], vb[σ[i]], sb[σ[i]]) for i in 1:n) || return false
        end
        return true
    end
    function exact(bx)
        sub = Dict{Any,Any}(xa[i] => xb[σ[i]] for i in 1:n)
        Fa_b = Any[_unwrap(Symbolics.substitute(e, sub)) for e in Fa][invperm(σ)]
        v = _agreement(Fa_b, Fb, bx; rtol, probes, rng_seed)
        v.verdict === :undecided && undecided[] === nothing && (undecided[] = (v, Fa_b[v.comp]))
        return v.verdict === :equal
    end
    function assign(k)
        if k > n
            leaves[] += 1
            leaves[] > max_leaves && return false
            bx = leafboxes()
            return bx !== nothing && leafok(bx) && exact(bx)
        end
        i = order[k]
        for j in cand[i]
            used[j] && continue
            σ[i] = j
            used[j] = true
            assign(k + 1) && return true
            used[j] = false
            leaves[] > max_leaves && return false
        end
        return false
    end
    assign(1) && return true
    leaves[] > max_leaves && error(
        "vector_fields_equal(:$(a.name), :$(b.name)): gave up the search for a renaming of the " *
        "$(n) states after $(max_leaves) candidate bijections (the fields are too symmetric to " *
        "tell the states apart); the answer is unknown, not false: pass rename = Dict(…) with " *
        "the correspondence of the states, or raise max_renamings")
    # (no assignment here to a name that the closures above use: it would be shared with them)
    und = undecided[]
    und === nothing ||
        _undecided_error(a, b, bn[und[1].comp], und[2], Fb[und[1].comp], und[1], probes)
    cl = clash[]
    cl === nothing || throw(ArgumentError(_disjoint_text(a, b, an[cl[1]], sboxa[an[cl[1]]],
                                                         bn[cl[2]], sboxb[bn[cl[2]]])))
    return false
end

# =============================================================================================
# check_naturality
# =============================================================================================

_underlying(x::ContactModel) = x
_underlying(x) = hasproperty(x, :model) ? getproperty(x, :model) : NEC.contact_model(x)

# The field of `ode` by coordinate name, in fresh variables shared by name (role :v for every
# coordinate and parameter, so that coordinates of different systems with the same name meet).
function _named_fields(ode::SymbolicODE)
    names = NEC.state_names(ode)
    f(n) = _fresh(:v, n)
    return Dict{Symbol,Any}(n => _rename(e, f) for (n, e) in zip(names, ode.rhs))
end

function _sum_fields(parts::Dict{Symbol,Any}...)
    out = Dict{Symbol,Any}()
    for d in parts, (k, v) in d
        out[k] = haskey(out, k) ? _unwrap(Symbolics.wrap(out[k]) + Symbolics.wrap(v)) : v
    end
    return out
end

function _compare_named(whole::Dict{Symbol,Any}, parts::Dict{Symbol,Any}, what, boxes; kw...)
    kw = values(kw)
    lines = String[]
    only_whole = setdiff(keys(whole), keys(parts))
    only_parts = setdiff(keys(parts), keys(whole))
    # a coordinate that one side lacks must have a zero field on the other
    for k in only_whole
        _symbolic_zero(whole[k]) || push!(lines, "$(what): the glued model has the coordinate " *
                                                  "$(k), which neither part has")
    end
    for k in only_parts
        push!(lines, "$(what): the parts have the coordinate $(k), which the glued model lacks")
    end
    common = sort!(collect(intersect(keys(whole), keys(parts))))
    for k in common
        x, y = whole[k], parts[k]
        v = _agreement(Any[x], Any[y], boxes; kw...)
        if v.verdict === :different
            push!(lines, "$(what): d$(k)/dt of the glued model ≠ the sum over the parts " *
                         "(difference $(_difference_text(x, y)))")
        elseif v.verdict === :undecided
            push!(lines, "$(what): cannot decide whether d$(k)/dt of the glued model is the " *
                         "sum over the parts: the difference `$(_difference_text(x, y))` " *
                         _undecided_why(v.why, v.what, kw.probes))
        end
    end
    return lines
end

function _named_map(m::Semiconjugacy)
    f(n) = _fresh(:v, n)
    return Dict{Symbol,Any}(NEC._coordinate_name(k) => _rename(v, f) for (k, v) in m.map)
end

"""
    check_naturality(η::NaturalTransformation, A, B; on = nothing, network, glued = nothing,
                     method = :auto, probes = 16, rng_seed = 1, rtol = 1e-10)
        -> VerificationResult

Check that `η` commutes with gluing `A` and `B`; see the docstring in NetworkEpiCore.
"""
function NEC.check_naturality(η::NaturalTransformation, A, B; on = nothing, network,
                              glued = nothing, method::Symbol = :auto, probes::Integer = 16,
                              rng_seed::Integer = 1, rtol::Real = 1e-10)
    C = glued !== nothing ? glued : NEC.glue(A, B; on)     # on = nothing: glue's default
    mA, mB, mC = (η.component(_underlying(X), network) for X in (A, B, C))
    lines = String[]
    worst = 0.0
    allsym = true
    for (label, m) in (("A", mA), ("B", mB), ("glued", mC))
        r = NEC.verify(m; method, probes, rng_seed, rtol)
        worst = max(worst, r.max_residual)
        allsym &= r.method === :symbolic
        r.ok || push!(lines, "component on $(label) fails verify: " *
                             replace(r.details, "\n" => "; "))
    end
    boxes = merge(_boxes(mA.source.domain), _boxes(mB.source.domain), _boxes(mC.source.domain))
    kw = (; rtol, probes, rng_seed)
    append!(lines, _compare_named(_named_fields(mC.source),
                                  _sum_fields(_named_fields(mA.source), _named_fields(mB.source)),
                                  "source", boxes; kw...))
    append!(lines, _compare_named(_named_fields(mC.target),
                                  _sum_fields(_named_fields(mA.target), _named_fields(mB.target)),
                                  "target", boxes; kw...))
    πC = _named_map(mC)
    for (label, m) in (("A", mA), ("B", mB))
        for (k, v) in _named_map(m)
            if !haskey(πC, k)
                push!(lines, "map: the target coordinate $(k) of $(label) is not a target " *
                             "coordinate of the glued model")
            else
                w = _agreement(Any[πC[k]], Any[v], boxes; kw...)
                if w.verdict === :different
                    push!(lines, "map: $(k) = $(_display(πC[k])) on the glued model but " *
                                 "$(_display(v)) on $(label)")
                elseif w.verdict === :undecided
                    push!(lines, "map: cannot decide whether $(k) = $(_display(πC[k])) on the " *
                                 "glued model equals $(_display(v)) on $(label): the difference " *
                                 _undecided_why(w.why, w.what, kw.probes))
                end
            end
        end
    end
    ok = isempty(lines)
    details = ok ? "η = :$(η.name) commutes with this gluing: the components verify, the " *
                   "source and target fields of the glued model are the sums over the parts, " *
                   "and the maps agree" : join(lines, "\n")
    return VerificationResult(ok, allsym ? :symbolic : :numeric, worst, allsym ? 0 : probes,
                              details)
end

end # module NetworkEpiCoreSymbolicsExt
