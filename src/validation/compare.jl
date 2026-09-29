# Owner: WP12 (DESIGN_NetworkEpiCore.md §E.2, §E.5; work package in §G.2).
#
# Deterministic curves (`ModelCurves`, built by EdgeBasedModels and NodeBasedModels through the
# `model_curves` stub) and their comparison with a reference ensemble summary: the metrics of
# §E.2 (D∞ and its argmax, SE∞, z∞, ΔR∞ with a 95% CI, Δpeak, Δt_peak, coverage) in a
# `ComparisonTable`. EBM and NBM vignettes and tests run exactly this code.

export ModelCurves, ComparisonTable, compare

"""
    ModelCurves(t, values; label = "model", representation = :model, metadata = Dict())

Deterministic curves of one representation on a time grid `t`: `values` maps observables
(species, `:infectious`, `:cumulative`; see [`Scenario`](@ref)) to vectors of population
fractions, as a `Dict{Symbol}` or a `NamedTuple`. `label` names the curves in tables and legends;
`representation` (for example `:edge_based`, `:pairwise`, `:pgf_closure`, `:mass_action`,
`:mean_field`, `:individual`, `:pair`) fixes the line style of the plot recipes; `metadata` is
free. `c[X]` is the curve of observable `X`.

EdgeBasedModels and NodeBasedModels build them with `model_curves(sys, sol; t = sc.tgrid, label)`.
"""
struct ModelCurves
    label::String
    t::Vector{Float64}
    values::Dict{Symbol,Vector{Float64}}
    representation::Symbol
    metadata::Dict{Symbol,Any}
    function ModelCurves(label::AbstractString, t::AbstractVector{<:Real}, values::AbstractDict,
                         representation::Symbol, metadata::AbstractDict)
        tt = collect(Float64, t)
        (length(tt) >= 1 && issorted(tt; lt = <=)) || throw(ArgumentError(
            "ModelCurves $(repr(label)): t must be a non-empty, strictly increasing grid"))
        isempty(values) && throw(ArgumentError("ModelCurves $(repr(label)): no curves given"))
        v = Dict{Symbol,Vector{Float64}}()
        for (k, x) in values
            length(x) == length(tt) || throw(ArgumentError(
                "ModelCurves $(repr(label)): the curve $(k) has $(length(x)) values for " *
                "$(length(tt)) times"))
            v[Symbol(k)] = collect(Float64, x)
        end
        return new(String(label), tt, v, representation,
                   Dict{Symbol,Any}(Symbol(k) => x for (k, x) in metadata))
    end
end
ModelCurves(t::AbstractVector{<:Real}, values::AbstractDict; label::AbstractString = "model",
            representation::Symbol = :model, metadata::AbstractDict = Dict{Symbol,Any}()) =
    ModelCurves(label, t, values, representation, metadata)
ModelCurves(t::AbstractVector{<:Real}, values::NamedTuple; kw...) =
    ModelCurves(t, Dict{Symbol,Any}(pairs(values)); kw...)

Base.getindex(c::ModelCurves, X::Symbol) = c.values[X]
Base.haskey(c::ModelCurves, X::Symbol) = haskey(c.values, X)
Base.show(io::IO, c::ModelCurves) =
    print(io, "ModelCurves(", repr(c.label), "; ", length(c.t), " times, ",
          join(sort!(collect(keys(c.values)); by = string), ", "), ")")

# The curve of observable X on the grid t: the stored values when the grids agree, otherwise
# linear interpolation (the curve must cover t).
function _curve_on(c::ModelCurves, X::Symbol, t::AbstractVector{Float64})
    y = c.values[X]
    if length(c.t) == length(t) && all(i -> abs(c.t[i] - t[i]) <= 1e-9 * max(1.0, abs(t[i])), eachindex(t))
        return y
    end
    tol = 1e-9 * max(1.0, abs(last(t)))
    (first(c.t) <= first(t) + tol && last(c.t) >= last(t) - tol) || throw(ArgumentError(
        "ModelCurves $(repr(c.label)) cover t ∈ [$(first(c.t)), $(last(c.t))], which does not " *
        "contain the reference grid [$(first(t)), $(last(t))]"))
    out = similar(t)
    for (i, s) in enumerate(t)
        j = searchsortedlast(c.t, s)
        if j < 1
            out[i] = y[1]
        elseif j >= length(c.t)
            out[i] = y[end]
        else
            w = (s - c.t[j]) / (c.t[j + 1] - c.t[j])
            out[i] = (1 - w) * y[j] + w * y[j + 1]
        end
    end
    return out
end

# =============================================================================================
# The comparison table
# =============================================================================================

const _ComparisonRow = NamedTuple{(:label, :observable, :D∞, :t_D∞, :SE∞, :z∞, :ΔR∞, :ΔR∞_ci,
                                   :Δpeak, :Δt_peak, :coverage),
                                  Tuple{String,Symbol,Float64,Float64,Float64,Float64,Float64,
                                        NTuple{2,Float64},Float64,Float64,Float64}}

"""
    ComparisonTable

The result of [`compare`](@ref): `id` and `scenario_hash` of the reference summary, the
`statistics` compared (`:cond` or `:uncond`), the number `n` of runs they average, and `rows`,
one `NamedTuple` per (curve, observable) with the fields

- `label`, `observable`;
- `D∞` = max_t |x_det(t) − x̄(t)| and `t_D∞`, its (first) argmax;
- `SE∞` = max_t se(t), the largest standard error of the mean on the grid;
- `z∞` = max_t |x_det − x̄|/max(se, 10⁻⁴);
- `ΔR∞` = R_det(t_end) − mean(final size) over the compared runs, where R_det is the curve's
  `:cumulative` (`NaN` without one), and `ΔR∞_ci`, its 95% interval ±1.96·sd/√n;
- `Δpeak` = max x_det − max x̄ and `Δt_peak`, the difference of their times;
- `coverage`: the fraction of the grid with |x_det − x̄| ≤ 1.96·max(se, 10⁻⁴), inside the mean
  band.

`t[label, X]` returns a row; iterating the table iterates the rows. The EBM and NBM tests assert
D∞(I) < 0.005 and |ΔR∞| < 0.005 for back ends declared `:exact_limit` (§E.2).
"""
struct ComparisonTable
    id::Symbol
    scenario_hash::String
    statistics::Symbol
    n::Int
    rows::Vector{_ComparisonRow}
end

Base.length(t::ComparisonTable) = length(t.rows)
Base.iterate(t::ComparisonTable, i::Int = 1) = i > length(t.rows) ? nothing : (t.rows[i], i + 1)
Base.eltype(::Type{ComparisonTable}) = _ComparisonRow

function Base.getindex(t::ComparisonTable, label::AbstractString, X::Symbol)
    for r in t.rows
        (r.label == label && r.observable === X) && return r
    end
    throw(KeyError((label, X)))
end

"""
    compare(ref::EnsembleSummary, curves::ModelCurves...; observables = nothing,
            statistics = :cond) -> ComparisonTable
    compare(ref::EnsembleSummary, curves::AbstractVector{ModelCurves}; kw...)

Compare deterministic curves with the mean of a reference ensemble on the summary's time grid
(curves on another grid are interpolated linearly), with the metrics of §E.2 (see
[`ComparisonTable`](@ref)). `statistics = :cond` (the default) compares with the runs that
satisfied the scenario's conditioning rule (major outbreaks, or survival for SIS/SIRS),
`:uncond` with all runs. `observables` defaults to the summary's observables that every curve
provides.
"""
function compare(ref::EnsembleSummary, curves::AbstractVector{ModelCurves};
                 observables::Union{Nothing,AbstractVector} = nothing, statistics::Symbol = :cond)
    isempty(curves) && throw(ArgumentError("compare: no curves given"))
    statistics in (:cond, :uncond) || throw(ArgumentError(
        "compare: statistics must be :cond or :uncond; got :$(statistics)"))
    obs = _comparison_observables(ref, curves, observables)
    stats = statistics === :cond ? ref.cond : ref.uncond
    runs = statistics === :cond ? ref.final_size[ref.major] : ref.final_size
    n = length(runs)
    fs_mean = n == 0 ? NaN : sum(runs) / n
    fs_se = n <= 1 ? NaN : sqrt(sum(abs2, runs .- fs_mean) / (n - 1)) / sqrt(n)
    rows = _ComparisonRow[]
    for c in curves
        R = haskey(c, :cumulative) ? _curve_on(c, :cumulative, ref.t)[end] : NaN
        ΔR = R - fs_mean
        ci = (ΔR - 1.96 * fs_se, ΔR + 1.96 * fs_se)
        for X in obs
            st = stats[X]
            x = _curve_on(c, X, ref.t)
            d = x .- st.mean
            ad = abs.(d)
            iD = argmax(ad)            # first maximum
            z = ad ./ max.(st.se, 1e-4)
            ip, jp = argmax(x), argmax(st.mean)
            push!(rows, _ComparisonRow((c.label, X, ad[iD], ref.t[iD], maximum(st.se), maximum(z),
                                        ΔR, ci, x[ip] - st.mean[jp], ref.t[ip] - ref.t[jp],
                                        count(<=(1.96), z) / length(z))))
        end
    end
    return ComparisonTable(ref.id, ref.scenario_hash, statistics, n, rows)
end
compare(ref::EnsembleSummary, curves::ModelCurves...; kw...) =
    compare(ref, collect(ModelCurves, curves); kw...)

function _comparison_observables(ref::EnsembleSummary, curves, observables)
    if observables === nothing
        obs = [X for X in ref.observables if all(c -> haskey(c, X), curves)]
        isempty(obs) && throw(ArgumentError(
            "compare: no observable of the summary ($(_list(ref.observables))) is provided by " *
            "every curve"))
        return obs
    end
    obs = collect(Symbol, observables)
    for X in obs
        X in ref.observables || throw(ArgumentError(
            "compare: the summary :$(ref.id) has no observable $(X) (it has $(_list(ref.observables)))"))
        for c in curves
            haskey(c, X) || throw(ArgumentError(
                "compare: the curves $(repr(c.label)) have no observable $(X)"))
        end
    end
    return obs
end

function Base.show(io::IO, t::ComparisonTable)
    print(io, "ComparisonTable(:", t.id, ", ", length(t.rows), " rows)")
end

function Base.show(io::IO, ::MIME"text/plain", t::ComparisonTable)
    println(io, "ComparisonTable :", t.id, "  (scenario ", first(t.scenario_hash, 8), "; ",
            t.statistics === :cond ? "conditioned" : "unconditioned", " mean of ", t.n, " runs)")
    w = maximum((textwidth(r.label) for r in t.rows); init = 5)
    ow = maximum((textwidth(string(r.observable)) for r in t.rows); init = 10)
    println(io, "  ", rpad("curve", w), "  ", rpad("observable", ow),
            "        D∞     t(D∞)       SE∞        z∞       ΔR∞  95% CI                 Δpeak   Δt_peak  coverage")
    for (k, r) in enumerate(t.rows)
        print(io, "  ", rpad(r.label, w), "  ", rpad(string(r.observable), ow),
              @sprintf("  %8.5f  %8.2f  %8.5f  %8.2f  %8.5f  [%8.5f, %8.5f]  %8.5f  %8.2f  %8.3f",
                       r.D∞, r.t_D∞, r.SE∞, r.z∞, r.ΔR∞, r.ΔR∞_ci..., r.Δpeak, r.Δt_peak,
                       r.coverage))
        k < length(t.rows) && println(io)
    end
end
