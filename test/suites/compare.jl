# Owner: WP12. `ModelCurves` and `compare` (DESIGN §E.2) on synthetic data with known D∞, z∞,
# SE∞, ΔR∞ (and its CI), Δpeak, Δt_peak and coverage; interpolation onto the summary grid;
# errors; and a smoke test of the plot recipes with Plots.

using NetworkEpiCore, Test
ENV["GKSwstype"] = "100"                                         # headless GR for the recipe test
using Plots

const SCC = scenario(:sir_reg6)
const TGRID = collect(SCC.tgrid)                 # 0:0.25:60, 241 points

# A reference summary whose mean curves and standard errors are known exactly.
function reference(; se = 0.002, finals = [0.93, 0.92, 0.94, 0.02], major = BitVector([1, 1, 1, 0]))
    t = TGRID
    n = length(t)
    I = 0.29 .* exp.(-((t .- 11) ./ 4) .^ 2)
    cum = 0.01 .+ 0.92 .* (1 .- exp.(-t ./ 6))
    S = 1 .- cum
    R = cum .- I
    st(m; s = se) = (mean = m, sd = fill(s * 2, n), se = fill(s, n), q025 = m .- 0.03, q25 = m .- 0.01,
                     q50 = m, q75 = m .+ 0.01, q975 = m .+ 0.03)
    cond = Dict(:S => st(S), :I => st(I), :R => st(R), :infectious => st(I), :cumulative => st(cum))
    uncond = Dict(k => st(v.mean .* 0.9) for (k, v) in cond)
    nm = count(major)
    return EnsembleSummary(; id = SCC.id, scenario_hash = scenario_hash(SCC), algorithm_revision = "test",
        N = 10_000, nsims = length(finals), n_major = nm, p_major = nm / length(finals),
        p_major_ci = (0.2, 0.99), t, observables = SCC.observables, cond, uncond, final_size = finals,
        peak = [(11.0, 0.29) for _ in finals], major), (; S, I, R, cum)
end

@testset "ModelCurves" begin
    c = ModelCurves(TGRID, Dict(:I => zeros(241), :S => ones(241)); label = "edge-based",
                    representation = :edge_based)
    @test c[:I] == zeros(241) && haskey(c, :S) && !haskey(c, :R)
    @test c.label == "edge-based" && c.representation === :edge_based
    @test ModelCurves(TGRID, (I = zeros(241),)).values == Dict(:I => zeros(241))
    @test ModelCurves(TGRID, (I = zeros(241),)).label == "model"
    @test_throws ArgumentError ModelCurves(TGRID, Dict(:I => zeros(10)))
    @test_throws ArgumentError ModelCurves(reverse(TGRID), Dict(:I => zeros(241)))
    @test_throws ArgumentError ModelCurves(TGRID, Dict{Symbol,Vector{Float64}}())
    @test occursin("edge-based", sprint(show, c))
end

@testset "compare: known metrics on synthetic data" begin
    ref, m = reference()
    t = TGRID
    # a curve with a known bump in I: +0.004 on t ∈ [20, 30] and −0.006 at t = 40 exactly
    bumpI = copy(m.I)
    bumpI[(t .>= 20) .& (t .<= 30)] .+= 0.004
    k40 = findfirst(==(40.0), t)
    bumpI[k40] -= 0.006
    # the final size of the curve differs from the major-run mean (0.93) by +0.004
    cum = copy(m.cum)
    cum[end] = 0.934
    det = ModelCurves(t, Dict(:S => m.S, :I => bumpI, :R => m.R, :infectious => m.I, :cumulative => cum);
                      label = "edge-based", representation = :edge_based)
    tab = compare(ref, det)
    @test tab isa ComparisonTable
    @test tab.statistics === :cond && tab.n == 3 && tab.id === :sir_reg6
    @test length(tab) == 5 && [r.observable for r in tab] == SCC.observables
    rI = tab["edge-based", :I]
    @test rI.D∞ ≈ 0.006 rtol = 1e-12
    @test rI.t_D∞ == 40.0
    @test rI.SE∞ == 0.002
    @test rI.z∞ ≈ 3.0 rtol = 1e-12                               # 0.006 / 0.002
    nin = count(x -> x > 1.96 * 0.002, abs.(bumpI .- m.I))       # 0.004 and 0.006 are outside
    @test nin == count((t .>= 20) .& (t .<= 30)) + 1
    @test rI.coverage ≈ 1 - nin / 241 rtol = 1e-12
    @test rI.Δpeak ≈ 0.0 atol = 1e-15                            # the bump is away from the peak
    @test rI.Δt_peak == 0.0
    # ΔR∞ = R_det(t_end) − mean(final size of major runs) with a 95% CI ±1.96 sd/√n
    fs = [0.93, 0.92, 0.94]
    sd = sqrt(sum(abs2, fs .- 0.93) / 2)
    @test rI.ΔR∞ ≈ 0.934 - 0.93 rtol = 1e-10
    @test rI.ΔR∞_ci[1] ≈ 0.004 - 1.96 * sd / sqrt(3) rtol = 1e-10
    @test rI.ΔR∞_ci[2] ≈ 0.004 + 1.96 * sd / sqrt(3) rtol = 1e-10
    @test all(r -> r.ΔR∞ == rI.ΔR∞, tab)                         # per curve
    rS = tab["edge-based", :S]
    @test rS.D∞ == 0.0 && rS.z∞ == 0.0 && rS.coverage == 1.0
    rc = tab["edge-based", :cumulative]
    @test rc.D∞ ≈ 0.934 - m.cum[end] rtol = 1e-10
    @test rc.t_D∞ == 60.0
    # the se floor 1e-4 in z∞ (and coverage) when the SSA has no spread
    ref0, m0 = reference(; se = 0.0)
    r0 = compare(ref0, det)["edge-based", :I]
    @test r0.z∞ ≈ 0.006 / 1e-4 rtol = 1e-12
    @test r0.SE∞ == 0.0
    # a shifted peak: Δpeak and Δt_peak
    shiftI = 0.30 .* exp.(-((t .- 12) ./ 4) .^ 2)
    det2 = ModelCurves(t, Dict(:I => shiftI); label = "pairwise", representation = :pairwise)
    r2 = compare(ref, det2)["pairwise", :I]
    @test r2.Δpeak ≈ 0.30 - 0.29 rtol = 1e-10
    @test r2.Δt_peak == 1.0
    @test isnan(r2.ΔR∞) && all(isnan, r2.ΔR∞_ci)                # no :cumulative curve
    # several curves; observables default to the ones every curve has
    tab2 = compare(ref, det, det2)
    @test [(r.label, r.observable) for r in tab2] == [("edge-based", :I), ("pairwise", :I)]
    @test isequal(compare(ref, [det, det2]).rows, tab2.rows)
    tab3 = compare(ref, det; observables = [:cumulative, :I])
    @test [r.observable for r in tab3] == [:cumulative, :I]
    # unconditioned statistics: all runs, the unconditioned mean
    tu = compare(ref, det; statistics = :uncond)
    @test tu.n == 4
    @test tu["edge-based", :I].ΔR∞ ≈ 0.934 - sum([0.93, 0.92, 0.94, 0.02]) / 4 rtol = 1e-10
    @test tu["edge-based", :S].D∞ ≈ maximum(abs.(m.S .- 0.9 .* m.S)) rtol = 1e-12
    # the table prints
    txt = sprint(show, MIME"text/plain"(), tab)
    @test occursin("D∞", txt) && occursin("edge-based", txt) && occursin("conditioned mean of 3 runs", txt)
    @test_throws KeyError tab["edge-based", :Q]
end

@testset "compare: curves on another grid are interpolated" begin
    ref, m = reference()
    fine = collect(0.0:0.05:60.0)
    f(t) = 0.29 * exp(-((t - 11) / 4)^2)
    det = ModelCurves(fine, Dict(:I => f.(fine)); label = "fine")
    r = compare(ref, det)["fine", :I]
    @test r.D∞ < 1e-14                                            # the grids share their points
    lin = ModelCurves([0.0, 60.0], Dict(:I => [0.0, 0.6]); label = "line")
    rl = compare(ref, lin)["line", :I]
    @test rl.D∞ ≈ maximum(abs.(0.01 .* TGRID .- m.I)) rtol = 1e-12
    short = ModelCurves(collect(0.0:0.25:50.0), Dict(:I => zeros(201)); label = "short")
    @test_throws ArgumentError compare(ref, short)
end

@testset "compare: errors" begin
    ref, m = reference()
    det = ModelCurves(TGRID, Dict(:I => m.I); label = "x")
    @test_throws ArgumentError compare(ref, det; statistics = :median)
    @test_throws ArgumentError compare(ref, det; observables = [:R])            # the curve has no R
    @test_throws ArgumentError compare(ref, det; observables = [:Q])            # the summary has no Q
    @test_throws ArgumentError compare(ref, ModelCurves(TGRID, Dict(:Q => m.I)))
    @test_throws ArgumentError compare(ref, ModelCurves[])
end

@testset "plot recipes (Plots)" begin
    ref, m = reference()
    det = ModelCurves(TGRID, Dict(:S => m.S, :I => m.I .+ 0.001, :R => m.R, :infectious => m.I,
                                  :cumulative => m.cum); label = "edge-based", representation = :edge_based)
    pw = ModelCurves(TGRID, Dict(:I => m.I .- 0.002, :cumulative => m.cum); label = "pairwise",
                     representation = :pairwise)
    p = Plots.plot(ref, :I)
    @test p isa Plots.Plot
    @test length(p.series_list) == 3                              # spread band, median, mean
    Plots.plot!(p, det, :I)
    @test length(p.series_list) == 4
    @test p.series_list[end][:label] == "edge-based"
    pb = Plots.plot(ref, :I; band = :both, median = false)
    @test length(pb.series_list) == 3                             # spread, mean band, mean
    cp = comparisonplot(ref, det, pw; observables = [:I, :cumulative])
    @test cp isa Plots.Plot
    @test length(cp.subplots) == 4                                # 2 rows × 2 observables
    # per column: top = band + mean + 2 curves, bottom = band + zero line + 2 residuals
    @test length(cp.series_list) == 2 * (4 + 4)
    @test length(comparisonplot(ref, det).subplots) == 2 * 5
    file = joinpath(mktempdir(), "comparison.png")
    Plots.savefig(cp, file)
    @test isfile(file) && filesize(file) > 1000
    @test_throws ArgumentError comparisonplot(det)
    @test_throws ArgumentError Plots.plot(ref, :Q)
end
