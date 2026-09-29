# Owner: WP12 (DESIGN_NetworkEpiCore.md §E.2, §E.5; work package in §G.2).
#
# RecipesBase recipes shared by the EdgeBasedModels and NodeBasedModels vignettes (NEC owns the
# exported names, which an extension could not export; decision H3):
#
#   plot(ref::EnsembleSummary, X)       spread band (q2.5–q97.5 of the runs), mean and median
#   plot!(c::ModelCurves, X)            one deterministic curve, styled by its representation
#   comparisonplot(ref, curves...; observables)
#                                       top row: spread band + mean + curves; bottom row: the
#                                       residual x_det − x̄ with the mean band ±1.96·SE
#
# Bands are always labelled and never min–max (§E.2).

export comparisonplot, comparisonplot!

# Line styles by representation (a fixed style per representation across both vignette sets).
const _REPRESENTATION_STYLES = Dict{Symbol,NamedTuple{(:color, :linestyle),Tuple{Symbol,Symbol}}}(
    :edge_based => (color = :royalblue, linestyle = :solid),
    :pairwise => (color = :darkorange, linestyle = :dash),
    :pgf_closure => (color = :forestgreen, linestyle = :dashdot),
    :s_anchored => (color = :forestgreen, linestyle = :dashdot),
    :mass_action => (color = :purple, linestyle = :dot),
    :mean_field => (color = :purple, linestyle = :dot),
    :individual => (color = :sienna, linestyle = :dash),
    :pair => (color = :teal, linestyle = :dashdot))

const _ENSEMBLE_COLOR = :gray40

function _summary_stats_for(s::EnsembleSummary, X::Symbol, statistics::Symbol)
    statistics in (:cond, :uncond) || throw(ArgumentError(
        "statistics must be :cond or :uncond; got :$(statistics)"))
    d = statistics === :cond ? s.cond : s.uncond
    haskey(d, X) || throw(ArgumentError(
        "the summary :$(s.id) has no observable $(X) (it has $(_list(s.observables)))"))
    return d[X]
end

_runs_label(s::EnsembleSummary, statistics) =
    statistics === :cond ? "$(s.n_major) of $(s.nsims) runs" : "$(s.nsims) runs"

# The stochastic ensemble of observable X: spread band, mean (and median), optionally the mean band.
@recipe function f(s::EnsembleSummary, X::Symbol; statistics = :cond, band = :spread, median = true)
    st = _summary_stats_for(s, X, statistics)
    xguide --> "t"
    yguide --> string(X)
    legend --> :best
    if band in (:spread, :both)
        @series begin
            seriestype := :path
            fillrange := st.q975
            fillalpha --> 0.25
            fillcolor --> _ENSEMBLE_COLOR
            linealpha := 0
            primary := true
            label --> "SSA q2.5–q97.5 ($(_runs_label(s, statistics)))"
            s.t, st.q025
        end
    end
    if band in (:mean, :both)
        @series begin
            seriestype := :path
            fillrange := st.mean .+ 1.96 .* st.se
            fillalpha --> 0.45
            fillcolor --> _ENSEMBLE_COLOR
            linealpha := 0
            label --> "SSA mean ± 1.96 SE"
            s.t, st.mean .- 1.96 .* st.se
        end
    end
    if median
        @series begin
            seriestype := :path
            linecolor --> :black
            linestyle --> :dot
            linewidth --> 1
            label --> "SSA median"
            s.t, st.q50
        end
    end
    @series begin
        seriestype := :path
        linecolor --> :black
        linewidth --> 2
        label --> "SSA mean"
        s.t, st.mean
    end
end

# One deterministic curve.
@recipe function f(c::ModelCurves, X::Symbol)
    haskey(c, X) || throw(ArgumentError("the curves $(repr(c.label)) have no observable $(X)"))
    style = get(_REPRESENTATION_STYLES, c.representation, nothing)
    seriestype := :path
    xguide --> "t"
    yguide --> string(X)
    label --> c.label
    linewidth --> 2
    if style !== nothing
        linecolor --> style.color
        linestyle --> style.linestyle
    end
    c.t, c.values[X]
end

"""
    comparisonplot(ref::EnsembleSummary, curves::ModelCurves...; observables = nothing,
                   statistics = :cond, band = :spread)
    comparisonplot!(...)

The two-row comparison figure of §E.5 (a RecipesBase user recipe; load Plots to draw it). One
column per observable (default: the summary's observables that every curve provides):

- **top row:** the reference ensemble's *spread* band (the pointwise q2.5–q97.5 of the runs) and
  its mean, with every deterministic curve on top (a fixed style per representation);
- **bottom row:** the residual x_det − x̄ of every curve with the *mean* band ±1.96·SE around 0,
  the band inside which an exact-in-the-limit representation should stay.

`statistics = :uncond` uses all runs instead of the major (or surviving) ones; `band = :both`
also draws the mean band in the top row. The numbers behind the figure are
[`compare`](@ref)`(ref, curves...)`.
"""
@userplot ComparisonPlot

function _comparison_args(args)
    (length(args) >= 1 && args[1] isa EnsembleSummary) || throw(ArgumentError(
        "comparisonplot(ref::EnsembleSummary, curves::ModelCurves...; observables)"))
    curves = ModelCurves[]
    for a in args[2:end]
        if a isa ModelCurves
            push!(curves, a)
        elseif a isa AbstractVector && all(x -> x isa ModelCurves, a)
            append!(curves, a)
        else
            throw(ArgumentError("comparisonplot: expected ModelCurves after the summary; got $(typeof(a))"))
        end
    end
    return args[1], curves
end

@recipe function f(cp::ComparisonPlot; observables = nothing, statistics = :cond, band = :spread)
    ref, curves = _comparison_args(cp.args)
    obs = isempty(curves) ? (observables === nothing ? ref.observables : collect(Symbol, observables)) :
          _comparison_observables(ref, curves, observables)
    n = length(obs)
    layout := (2, n)
    size --> (380 * max(n, 1) + 60, 620)
    legend --> :best
    # subplot attributes as 1 × 2n rows (top row first): titles on top, guides on the bottom row
    title --> permutedims(vcat(string.(obs), fill("", n)))
    xguide --> permutedims(vcat(fill("", n), fill("t", n)))
    yguide --> permutedims(vcat(["fraction"], fill("", n - 1), ["model − SSA mean"], fill("", n - 1)))
    for (j, X) in enumerate(obs)
        st = _summary_stats_for(ref, X, statistics)
        first_col = j == 1
        # ---- top: ensemble and curves ------------------------------------------------------
        if band in (:spread, :both)
            @series begin
                subplot := j
                seriestype := :path
                fillrange := st.q975
                fillalpha := 0.25
                fillcolor := _ENSEMBLE_COLOR
                linealpha := 0
                label := first_col ? "SSA q2.5–q97.5 ($(_runs_label(ref, statistics)))" : ""
                ref.t, st.q025
            end
        end
        if band in (:mean, :both)
            @series begin
                subplot := j
                seriestype := :path
                fillrange := st.mean .+ 1.96 .* st.se
                fillalpha := 0.45
                fillcolor := _ENSEMBLE_COLOR
                linealpha := 0
                label := first_col ? "SSA mean ± 1.96 SE" : ""
                ref.t, st.mean .- 1.96 .* st.se
            end
        end
        @series begin
            subplot := j
            seriestype := :path
            linecolor := :black
            linewidth := 2
            label := first_col ? "SSA mean" : ""
            ref.t, st.mean
        end
        for c in curves
            style = get(_REPRESENTATION_STYLES, c.representation, nothing)
            @series begin
                subplot := j
                seriestype := :path
                linewidth := 2
                label := first_col ? c.label : ""
                if style !== nothing
                    linecolor := style.color
                    linestyle := style.linestyle
                end
                c.t, c.values[X]
            end
        end
        # ---- bottom: residuals with the mean band ------------------------------------------
        @series begin
            subplot := n + j
            seriestype := :path
            fillrange := 1.96 .* st.se
            fillalpha := 0.35
            fillcolor := _ENSEMBLE_COLOR
            linealpha := 0
            label := first_col ? "± 1.96 SE of the SSA mean" : ""
            ref.t, -1.96 .* st.se
        end
        @series begin
            subplot := n + j
            seriestype := :path
            linecolor := :black
            linewidth := 1
            label := ""
            ref.t, zeros(length(ref.t))
        end
        for c in curves
            style = get(_REPRESENTATION_STYLES, c.representation, nothing)
            @series begin
                subplot := n + j
                seriestype := :path
                linewidth := 2
                label := ""
                if style !== nothing
                    linecolor := style.color
                    linestyle := style.linestyle
                end
                ref.t, _curve_on(c, X, ref.t) .- st.mean
            end
        end
    end
end
