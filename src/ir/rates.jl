# Owner: WP6 (DESIGN_NetworkEpiCore.md §B.1, §B.6; work package in §G.2).
#
# Rates: validation (Real | Symbol | arithmetic Expr over RATE_OPS | symbolic; Functions are
# rejected), evaluation (`rate_value`, with a small safe Expr interpreter), arithmetic on rates
# (`rate_mul`, `rate_add`, `rate_div`), parameter discovery (`rate_parameters`), `instantiate`,
# the rate conventions (`per_contact_rates`) and the endofunctor c_λ (`scale_contact_rates`).
#
# Symbolic rates (Symbolics.Num / BasicSymbolic) are stored as they are. NEC core cannot look
# inside them; NetworkEpiCoreSymbolicsExt (WP10) supplies the hooks declared at the end of this
# file (`_symbolic_rate_parameters`, `_symbolic_rate_value`, `_symbolic_rate_uses_time`) and
# `as_parameter`, which the arithmetic below uses to combine a symbolic rate with a Symbol or
# Expr rate.

export rate_value, rate_mul, rate_add, rate_div, rate_parameters, instantiate
export per_contact_rates, scale_contact_rates

# ---------------------------------------------------------------------------------------------
# Kinds of rate
# ---------------------------------------------------------------------------------------------

"""
    _is_symbolic_rate(x) -> Bool

Whether `x` is a symbolic expression (a Symbolics `Num` or a SymbolicUtils term). Decided by the
module that owns the type, so core needs no Symbolics dependency; the Symbolics extension may add
more specific methods.
"""
_is_symbolic_rate(x) = nameof(parentmodule(typeof(x))) in (:Symbolics, :SymbolicUtils)

_rate_error(r, where) = ArgumentError(
    "$(where)rates must be a Real, a Symbol, an arithmetic Expr over RATE_OPS " *
    "$(RATE_OPS) with Real and Symbol leaves, or a species-free symbolic expression; got " *
    "$(r isa Function ? "the Julia Function $(r)" : repr(r)) of type $(typeof(r)). " *
    (r isa Function ? "A Function cannot be lowered, hashed or run in NetworkOutbreaks." : ""))

_where(name) = name === nothing ? "" : "reaction `$(name)`: "

"""
    _checkrate(r, name = nothing)

Validate a rate and return it (an `Expr` is copied): a `Real` must be finite and ≥ 0 (not
`NaN`, `Inf` or a `Bool`), an `Expr` may only use [`RATE_OPS`](@ref) over `Real` and `Symbol`
leaves, a `Function` is rejected.
"""
_checkrate(r, name = nothing) =
    _is_symbolic_rate(r) ? r : throw(_rate_error(r, _where(name)))
_checkrate(r::Function, name = nothing) = throw(_rate_error(r, _where(name)))
_checkrate(r::Symbol, name = nothing) = r
function _checkrate(r::Real, name = nothing)
    _is_symbolic_rate(r) && return r
    r isa Bool && throw(ArgumentError(
        "$(_where(name))a rate must be a number, not the Bool $(r)"))
    (isfinite(r) && r >= 0) || throw(ArgumentError(
        "$(_where(name))numeric rates must be ≥ 0 and finite (not NaN or Inf); got $(r)"))
    return r
end
function _checkrate(r::Expr, name = nothing)
    _check_rate_expr(r, _where(name), r)
    return copy(r)          # Exprs are mutable: a model never shares its rate expressions
end

const _UNARY_OPS = (:exp, :log)

function _check_rate_expr(ex, where, whole)
    ex isa Symbol && return nothing
    if ex isa Real
        (_is_symbolic_rate(ex) || ex isa Bool || !isfinite(ex)) &&
            throw(ArgumentError("$(where)rate `$(whole)` contains the leaf $(repr(ex)); Expr " *
                                "leaves must be finite numbers or parameter names"))
        return nothing
    end
    ex isa Expr || throw(ArgumentError(
        "$(where)rate `$(whole)` contains $(repr(ex)) of type $(typeof(ex)); Expr leaves must " *
        "be Real numbers or Symbols (parameter names)"))
    (ex.head === :call && !isempty(ex.args) && ex.args[1] isa Symbol) ||
        throw(ArgumentError("$(where)rate `$(whole)`: only calls of $(RATE_OPS) are allowed " *
                            "(found the `$(ex.head)` expression `$(ex)`)"))
    op = ex.args[1]
    op in RATE_OPS || throw(ArgumentError(
        "$(where)rate `$(whole)` uses `$(op)`; only $(RATE_OPS) are allowed in Expr rates"))
    n = length(ex.args) - 1
    ok = op in _UNARY_OPS ? n == 1 : op in (:/, :^) ? n == 2 : op === :- ? n in (1, 2) :
         op in (:min, :max) ? n >= 2 : n >= 1
    ok || throw(ArgumentError("$(where)rate `$(whole)`: `$(op)` called with $(n) arguments"))
    for a in ex.args[2:end]
        _check_rate_expr(a, where, whole)
    end
    return nothing
end

# ---------------------------------------------------------------------------------------------
# Parameters of a rate
# ---------------------------------------------------------------------------------------------

"""
    rate_parameters(cm::ContactModel) -> Vector{Any}
    rate_parameters(r) -> Vector

The parameters of a model's rates in order of first appearance (names for `Symbol`/`Expr`
rates; the symbolic parameters for symbolic rates, which need the Symbolics extension), or of a
single rate `r`. Time `:t` is not a parameter. A `DensityDependent(:N)` convention contributes
`N`.
"""
rate_parameters(cm::ContactModel) = copy(cm.rate_params)
rate_parameters(r::Symbol) = r === :t ? Symbol[] : [r]
rate_parameters(r::Real) = _is_symbolic_rate(r) ? _symbolic_parameters(r) : Symbol[]
function rate_parameters(r::Expr)
    out = Symbol[]
    _collect_symbols!(out, r)
    return out
end
rate_parameters(r) = _is_symbolic_rate(r) ? _symbolic_parameters(r) : throw(_rate_error(r, ""))
rate_parameters(::Nothing) = Symbol[]

function _collect_symbols!(out, ex)
    if ex isa Symbol
        (ex === :t || ex in out) || push!(out, ex)
    elseif ex isa Expr
        for a in ex.args[2:end]
            _collect_symbols!(out, a)
        end
    end
    return out
end

function _symbolic_parameters(r)
    applicable(_symbolic_rate_parameters, r) ||
        throw(ArgumentError("the symbolic rate `$(r)` needs NetworkEpiCoreSymbolicsExt " *
                            "(`using Symbolics`) to list its parameters"))
    return _symbolic_rate_parameters(r)
end

# The name of a parameter entry of `rate_parameters` (a Symbol, or a symbolic variable).
_parameter_name(p::Symbol) = p
_parameter_name(p) = applicable(_symbolic_parameter_name, p) ? _symbolic_parameter_name(p) :
                     Symbol(string(p))

# Parameter names that must have values to evaluate the rates of `cm` (convention included),
# computed from the rates themselves (a front end may list more parameters in `rate_params`).
function _parameter_names(cm::ContactModel)
    names = Symbol[]
    rates = Any[r.rate for r in Iterators.flatten((cm.contacts, cm.transitions))]
    cm.convention isa DensityDependent && push!(rates, cm.convention.N)
    for r in rates, p in rate_parameters(r)
        n = _parameter_name(p)
        n in names || push!(names, n)
    end
    return names
end

# Does the rate depend on time?
_uses_time(r::Symbol) = r === :t
_uses_time(r::Real) = _is_symbolic_rate(r) && _symbolic_uses_time(r)
_uses_time(r::Expr) = any(a -> _uses_time_leaf(a), r.args[2:end])
_uses_time(r) = _is_symbolic_rate(r) && _symbolic_uses_time(r)
_uses_time_leaf(a::Symbol) = a === :t
_uses_time_leaf(a::Expr) = _uses_time(a)
_uses_time_leaf(a) = false
_symbolic_uses_time(r) =
    applicable(_symbolic_rate_uses_time, r) ? _symbolic_rate_uses_time(r) : false

# ---------------------------------------------------------------------------------------------
# Evaluation
# ---------------------------------------------------------------------------------------------

"""
    rate_value(r, p::AbstractDict = Dict{Symbol,Float64}(); t = nothing)

Evaluate a rate with parameter values `p` (keyed by name): a `Real` is returned as it is, a
`Symbol` is looked up, an `Expr` is evaluated by a small safe interpreter that knows only
[`RATE_OPS`](@ref), and `:t` takes the value of the keyword `t`. Symbolic rates are evaluated by
the Symbolics extension, which substitutes **by name** with `fold = Val(true)`.

The interpreter is generic in the number type, so `p` may hold `Float64`s, dual numbers or
symbolic values.
"""
function rate_value(r::Real, p::AbstractDict = Dict{Symbol,Float64}(); t = nothing)
    _is_symbolic_rate(r) || return r
    return _symbolic_value(r, p, t)
end
rate_value(r::Symbol, p::AbstractDict = Dict{Symbol,Float64}(); t = nothing) =
    _leaf_value(r, p, t, r)
function rate_value(r::Expr, p::AbstractDict = Dict{Symbol,Float64}(); t = nothing)
    _check_rate_expr(r, "", r)
    return _eval_rate(r, p, t, r)
end
function rate_value(r, p::AbstractDict = Dict{Symbol,Float64}(); t = nothing)
    _is_symbolic_rate(r) || throw(_rate_error(r, ""))
    return _symbolic_value(r, p, t)
end

function _symbolic_value(r, p, t)
    applicable(_symbolic_rate_value, r, p, t) ||
        throw(ArgumentError("the symbolic rate `$(r)` needs NetworkEpiCoreSymbolicsExt " *
                            "(`using Symbolics`) to be evaluated"))
    return _symbolic_rate_value(r, p, t)
end

function _leaf_value(s::Symbol, p, t, whole)
    if s === :t
        t === nothing && throw(ArgumentError(
            "rate `$(_rate_string(whole))` depends on time t; pass `t = …` (time-dependent " *
            "rates are for the ODE back ends only)"))
        return t
    end
    haskey(p, s) && return p[s]
    throw(ArgumentError("rate `$(_rate_string(whole))`: no value for the parameter $(s)"))
end

_eval_rate(x::Real, p, t, whole) = x
_eval_rate(x::Symbol, p, t, whole) = _leaf_value(x, p, t, whole)
function _eval_rate(ex::Expr, p, t, whole)
    op = ex.args[1]
    args = map(a -> _eval_rate(a, p, t, whole), ex.args[2:end])
    return _apply_op(Val(op), args)
end
_apply_op(::Val{:+}, a) = +(a...)
_apply_op(::Val{:-}, a) = -(a...)
_apply_op(::Val{:*}, a) = *(a...)
_apply_op(::Val{:/}, a) = /(a...)
_apply_op(::Val{:^}, a) = _pow(a...)
_apply_op(::Val{:exp}, a) = exp(a...)
_apply_op(::Val{:log}, a) = log(a...)
_apply_op(::Val{:min}, a) = min(a...)
_apply_op(::Val{:max}, a) = max(a...)
# An integer base with a negative integer exponent is a real number (2^-1 = 0.5), not Julia's
# DomainError for Int powers.
_pow(x::Integer, n::Integer) = n < 0 ? float(x)^n : x^n
_pow(x, n) = x^n

# ---------------------------------------------------------------------------------------------
# Arithmetic on rates
# ---------------------------------------------------------------------------------------------

# A numeric (non-symbolic) Real.
_isnum(x) = x isa Real && !_is_symbolic_rate(x)
_issymbolic(x) = _is_symbolic_rate(x)

# Convert a Symbol/Expr rate to a symbolic expression (needs the Symbolics extension).
function _to_symbolic(x)
    (_isnum(x) || _issymbolic(x)) && return x
    _uses_time(x) && throw(ArgumentError(
        "cannot combine the time-dependent rate `$(_rate_string(x))` with a symbolic rate; " *
        "write both symbolically"))
    (isdefined(@__MODULE__, :as_parameter) && applicable(as_parameter, :τ)) || throw(ArgumentError(
        "combining the rate `$(_rate_string(x))` with a symbolic rate needs " *
        "NetworkEpiCoreSymbolicsExt (`using Symbolics`)"))
    x isa Symbol && return as_parameter(x)
    return rate_value(x, Dict{Symbol,Any}(n => as_parameter(n) for n in rate_parameters(x)))
end

"""
    rate_mul(a, b)

The product of two rates, simplified where that is exact: numbers are multiplied, 1 is the unit,
0 absorbs, numeric coefficients are folded (`rate_mul(3, :(2γ)) == :(6γ)`) and products are
flattened (`rate_mul(:ε, :τ2) == :(ε * τ2)`). A symbolic rate combines with a `Symbol` or `Expr`
rate through `as_parameter` (Symbolics extension).
"""
function rate_mul(a, b)
    _checkrate_factor(a)
    _checkrate_factor(b)
    if _issymbolic(a) || _issymbolic(b)
        return _to_symbolic(a) * _to_symbolic(b)
    end
    _isnum(a) && _isnum(b) && return a * b
    _isnum(b) && return rate_mul(b, a)
    if _isnum(a)
        iszero(a) && return zero(a)
        isone(a) && return b
        if b isa Expr && b.args[1] === :* && _isnum(b.args[2])
            c = a * b.args[2]
            rest = b.args[3:end]
            iszero(c) && return c
            isone(c) && return length(rest) == 1 ? rest[1] : Expr(:call, :*, rest...)
            return Expr(:call, :*, c, rest...)
        end
        return Expr(:call, :*, a, _factors(b)...)
    end
    fa, fb = _factors(a), _factors(b)
    if !isempty(fb) && _isnum(fb[1])           # keep a numeric coefficient in front
        return rate_mul(fb[1], Expr(:call, :*, fa..., fb[2:end]...))
    end
    return Expr(:call, :*, fa..., fb...)
end

_factors(x::Expr) = x.args[1] === :* ? x.args[2:end] : Any[x]
_factors(x) = Any[x]

# A factor or term may be negative (e.g. the -p of 1 - p); only NaN and Functions are rejected.
_checkrate_factor(x::Function) = throw(_rate_error(x, ""))
_checkrate_factor(x::Expr) = _check_rate_expr(x, "", x)
_checkrate_factor(x::Real) = (_isnum(x) && isnan(x)) ? throw(_rate_error(x, "")) : nothing
_checkrate_factor(x::Symbol) = nothing
_checkrate_factor(x) = _issymbolic(x) ? nothing : throw(_rate_error(x, ""))

"""
    rate_add(a, b)

The sum of two rates (for example the merged rate of two identical reactions, or the total exit
rate `a_tot` of [`erlang_stages`](@ref)). Numbers are added, 0 is the unit and sums are
flattened (`rate_add(:γ, :μ) == :(γ + μ)`). A symbolic rate combines with a `Symbol` or `Expr`
rate through `as_parameter` (Symbolics extension).
"""
function rate_add(a, b)
    _checkrate_factor(a)
    _checkrate_factor(b)
    if _issymbolic(a) || _issymbolic(b)
        return _to_symbolic(a) + _to_symbolic(b)
    end
    _isnum(a) && _isnum(b) && return a + b
    _isnum(a) && iszero(a) && return b
    _isnum(b) && iszero(b) && return a
    return Expr(:call, :+, _terms(a)..., _terms(b)...)
end

_terms(x::Expr) = x.args[1] === :+ ? x.args[2:end] : Any[x]
_terms(x) = Any[x]

"""
    rate_div(a, b)

The quotient of two rates, used by the rate conventions (τ = β/⟨k⟩). Numbers are divided and 1 is
the unit; otherwise the result is `:(a / b)`. A symbolic rate combines with a `Symbol` or `Expr`
rate through `as_parameter` (Symbolics extension).
"""
function rate_div(a, b)
    _checkrate_factor(a)
    _checkrate_factor(b)
    if _issymbolic(a) || _issymbolic(b)
        return _to_symbolic(a) / _to_symbolic(b)
    end
    _isnum(a) && _isnum(b) && return a / b
    _isnum(b) && isone(b) && return a
    _isnum(a) && iszero(a) && return zero(a)
    return Expr(:call, :/, a, b)
end

_rate_sub(a, b) = _isnum(a) && _isnum(b) ? a - b :
                  (_issymbolic(a) || _issymbolic(b)) ? _to_symbolic(a) - _to_symbolic(b) :
                  Expr(:call, :-, a, b)

# ---------------------------------------------------------------------------------------------
# Printing rates (RN style: spaces around + and -, none around * / ^)
# ---------------------------------------------------------------------------------------------

_rate_string(r) = string(r)
_rate_string(r::Symbol) = string(r)
_rate_string(r::Real) = _is_symbolic_rate(r) ? string(r) : _number_string(r)
_rate_string(r::Expr) = _expr_string(r)[1]

_number_string(x::Integer) = string(x)
_number_string(x::AbstractFloat) = isinteger(x) && abs(x) < 1e15 ? string(Int(x)) : string(x)
_number_string(x::Rational) = string(numerator(x), "//", denominator(x))
_number_string(x) = string(x)

# Returns (text, precedence): 1 for + and -, 2 for * and /, 3 for unary minus, 4 for ^, 5 atoms.
function _expr_string(x)
    x isa Expr || return (_rate_string(x), (_isnum(x) && x < 0) ? 3 : 5)
    op = x.args[1]
    args = x.args[2:end]
    if op === :+
        return (join((_paren(a, 1) for a in args), " + "), 1)
    elseif op === :- && length(args) == 1
        return ("-" * _paren(args[1], 4), 3)
    elseif op === :-
        return (string(_paren(args[1], 1), " - ", _paren(args[2], 2)), 1)
    elseif op === :*
        parts = String[]
        i = 1
        if length(args) >= 2 && args[1] isa Union{Integer,AbstractFloat} && args[1] >= 0 &&
           args[2] isa Symbol
            push!(parts, _number_string(args[1]) * string(args[2]))
            i = 3
        end
        for a in args[i:end]
            push!(parts, _paren(a, 2))
        end
        return (join(parts, "*"), 2)
    elseif op === :/
        return (string(_paren(args[1], 2), "/", _paren(args[2], 3)), 2)
    elseif op === :^
        return (string(_paren(args[1], 5), "^", _paren(args[2], 5)), 4)
    else
        return (string(op, "(", join((_expr_string(a)[1] for a in args), ", "), ")"), 5)
    end
end

function _paren(a, level)
    s, p = _expr_string(a)
    return p < level ? "(" * s * ")" : s
end

# ---------------------------------------------------------------------------------------------
# instantiate
# ---------------------------------------------------------------------------------------------

"""
    instantiate(cm::ContactModel, p::AbstractDict = Dict{Symbol,Float64}()) -> ContactModel

The same model with every rate evaluated to a `Float64` from the parameter values `p` (by name),
falling back to the model's [`parameter_defaults`](@ref). A `DensityDependent(:N)` convention is
resolved to a number too. Throws an `ArgumentError` listing every missing parameter, and one for
a rate that depends on time (time variation in NetworkOutbreaks is done with interventions) or
evaluates to a negative number.
"""
function instantiate(cm::ContactModel, p::AbstractDict = Dict{Symbol,Float64}())
    vals = Dict{Symbol,Any}(k => v for (k, v) in cm.defaults)
    for (k, v) in p
        vals[Symbol(k)] = v
    end
    missing_ = [n for n in _parameter_names(cm) if !haskey(vals, n)]
    isempty(missing_) || throw(ArgumentError(
        "instantiate(:$(cm.name)): missing parameter values for $(_list(missing_)) " *
        "(pass them in p or set model defaults)"))
    ev(r, name) = _instantiate_rate(r, vals, name)
    cs = [_with_rate(c, ev(c.rate, c.name)) for c in cm.contacts]
    ts = [_with_rate(t, ev(t.rate, t.name)) for t in cm.transitions]
    conv = cm.convention isa DensityDependent ?
           DensityDependent(ev(cm.convention.N, :DensityDependent)) : cm.convention
    return _rebuild(cm; contacts = cs, transitions = ts, convention = conv, rate_params = Any[])
end

function _instantiate_rate(r, vals, name)
    _uses_time(r) && throw(ArgumentError(
        "instantiate: the rate `$(_rate_string(r))` of `$(name)` depends on time t, so it has " *
        "no constant value (use an intervention for time variation in NetworkOutbreaks)"))
    v = rate_value(r, vals)
    x = try
        Float64(v)
    catch
        throw(ArgumentError("instantiate: the rate `$(_rate_string(r))` of `$(name)` did not " *
                            "evaluate to a number (got $(repr(v)))"))
    end
    (isnan(x) || x < 0) && throw(ArgumentError(
        "instantiate: the rate `$(_rate_string(r))` of `$(name)` evaluates to $(x); rates must " *
        "be ≥ 0"))
    return x
end

# ---------------------------------------------------------------------------------------------
# Rate conventions (§B.6)
# ---------------------------------------------------------------------------------------------

"""
    per_contact_rates(cm::ContactModel, net = nothing) -> Vector

The per-contact rate τ_r of every contact of `cm` (in IR order), from the model's
[`RateConvention`](@ref) and the mean degree ⟨k⟩ = `mean_degree(net)` of the network:

- `PerContact`: τ_r = rate_r (no network needed);
- `FrequencyDependent`: τ_r = rate_r/⟨k⟩;
- `DensityDependent(N)`: τ_r = rate_r·N/⟨k⟩.

On a `MultiplexNetwork`, a contact on layer ℓ uses that layer's mean degree and a contact on
`:all` the total. On a `MultitypeNetwork` ⟨k⟩ is the total mean degree, and a stratified model
must be `PerContact` (an error asks for explicit τ). Every back end calls this function, so τ
is identical in EB, pairwise and NetworkOutbreaks. The conversion acts reaction by reaction and
commutes with gluing.
"""
function per_contact_rates(cm::ContactModel, net = nothing)
    conv = cm.convention
    conv isa PerContact && return Any[c.rate for c in cm.contacts]
    net === nothing && throw(ArgumentError(
        "per_contact_rates(:$(cm.name)): the $(_convention_label(conv)) convention needs a " *
        "network (τ = β/⟨k⟩ uses its mean degree)"))
    if _is_multitype(net) && any(l -> l.stratum !== :all, values(cm.labels))
        throw(ArgumentError(
            "per_contact_rates(:$(cm.name)): a stratified model on a MultitypeNetwork must give " *
            "per-contact rates τ explicitly (convention PerContact), not " *
            "$(_convention_label(conv))"))
    end
    return Any[_convert_rate(conv, c.rate, _contact_mean_degree(net, c)) for c in cm.contacts]
end

_convert_rate(::FrequencyDependent, r, k) = rate_div(r, k)
_convert_rate(c::DensityDependent, r, k) = rate_div(rate_mul(r, c.N), k)
_convert_rate(::PerContact, r, k) = r

# Descriptor kinds (the descriptor types come from networks/descriptors.jl).
_is_multitype(net) = net isa MultitypeNetwork
_is_multiplex(net) = net isa MultiplexNetwork
_is_explicit_graph(net) = net isa ExplicitGraph

function _contact_mean_degree(net, c::Contact)
    c.layer === :all && return mean_degree(net)
    _is_multiplex(net) || throw(ArgumentError(
        "contact `$(c.name)` is on the layer :$(c.layer), which needs a MultiplexNetwork " *
        "(got $(nameof(typeof(net))))"))
    c.layer in layer_names(net) || throw(ArgumentError(
        "contact `$(c.name)`: :$(c.layer) is not a layer of the network (layers: " *
        "$(_list(layer_names(net))))"))
    return mean_degree(net, c.layer)
end

"""
    scale_contact_rates(cm::ContactModel, c) -> ContactModel

The endofunctor c_λ: every contact rate τ becomes c·τ (for example c_κ, which turns a
`WellMixed(κ)` model into its mass-action rates). Transitions, the convention and labels are
unchanged, so it commutes with gluing and stratification.
"""
function scale_contact_rates(cm::ContactModel, c)
    cs = [_with_rate(k, rate_mul(c, k.rate)) for k in cm.contacts]
    nr = length(cm.contacts) + length(cm.transitions)
    pv = _transform_provenance(cm, "scale_contact_rates by $(_rate_string(c))", 1:nr)
    return _rebuild(cm; contacts = cs, provenance = pv)
end

# ---------------------------------------------------------------------------------------------
# Hooks for NetworkEpiCoreSymbolicsExt (WP10). Declared without methods; the extension adds
# methods for symbolic types. Contracts:
#   _symbolic_rate_parameters(r)       -> Vector of the parameters of r (names or variables),
#                                         in order of first appearance, excluding time t
#   _symbolic_parameter_name(p)        -> Symbol, the name of a symbolic parameter
#   _symbolic_rate_value(r, p, t)      -> r with every variable substituted by name from p (and
#                                         the independent variable t by t unless t === nothing),
#                                         folded (`fold = Val(true)`). A parameter with no value
#                                         in p is an ArgumentError that names it (never a partly
#                                         evaluated expression); a rate that depends on t, also
#                                         through a called parameter β(t), needs t = … (an
#                                         ArgumentError otherwise). A value in p may itself be
#                                         symbolic, and then so is the result.
#   _symbolic_rate_uses_time(r)        -> Bool, whether r depends on the independent variable
#   _symbolic_nonscalar_variables(r)   -> Vector{String}, the variables of r that are neither a
#                                         scalar parameter nor time t (an array element k[1], a
#                                         called parameter β(t)), which a ContactModel rejects
# ---------------------------------------------------------------------------------------------

function _symbolic_rate_parameters end
function _symbolic_parameter_name end
function _symbolic_rate_value end
function _symbolic_rate_uses_time end
function _symbolic_nonscalar_variables end
