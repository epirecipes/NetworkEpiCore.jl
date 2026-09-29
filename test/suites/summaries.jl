# Owner: WP12. Ensemble summaries (DESIGN §E.4): validation, the TOML + two-CSV file format with
# an exact round trip (including NaN, Inf, alignment shifts, realised graph statistics, extras
# and provenance), byte-identical rewrites, and the refusal to load stale or missing summaries.

using NetworkEpiCore, Test

const SC = scenario(:sir_pois5)

# A synthetic summary on the scenario grid; `same = true` makes the unconditioned statistics
# equal to the conditioned ones (every run major).
function synthetic_summary(; sc = SC, nsims = 5, major = BitVector([1, 1, 0, 1, 1]), same = false,
                           shifts = Float64[], extras = Dict{Symbol,Any}())
    t = collect(sc.tgrid)
    n = length(t)
    stats(a) = (mean = a .* sin.(t) .^ 2, sd = a .* (0.01 .+ t ./ 1e4), se = a .* (0.01 .+ t ./ 1e4) ./ sqrt(nsims),
                q025 = a .* (t ./ 97), q25 = fill(a / 3, n), q50 = a .* exp.(-t ./ 7), q75 = a .* t .^ 0.5,
                q975 = a .* (1 .+ t) ./ 3)
    cond = Dict(X => stats(k / 10) for (k, X) in enumerate(sc.observables))
    uncond = same ? cond : Dict(X => stats(k / 11) for (k, X) in enumerate(sc.observables))
    # exotic values survive the round trip
    cond[:I].sd[1] = NaN
    cond[:R].q975[end] = Inf
    nm = count(major)
    return EnsembleSummary(; id = sc.id, scenario_hash = scenario_hash(sc), algorithm_revision = "NO-rev-7",
        N = sc.sim.N, nsims, n_major = nm, p_major = nm / nsims, p_major_ci = (0.1 + 1e-17, 0.9999),
        t, observables = sc.observables, cond, uncond,
        final_size = [0.80031, 0.79987, 0.0103, 1 / 3, 0.8],
        peak = [(11.25, 0.2311), (11.5, 0.2342), (0.0, 0.01), (π, 1 / 7), (12.0, 0.23)], major,
        shifts, realised = Dict(:mean_degree => [5.001, 4.998, 5.0, 4.9993, 5.0002],
                                :erased_fraction => [0.0, 1e-4, 2e-4, 0.0, 0.0]),
        extras, provenance = Dict("julia" => "1.12.7", "NetworkOutbreaks" => "0.2.0",
                                  "date" => "2026-09-26", "wall_time_s" => "4.2"))
end

@testset "EnsembleSummary validation" begin
    s = synthetic_summary()
    @test s.n_major == 4 && s.p_major == 0.8 && s.nsims == 5
    @test s.cond[:I] isa SummaryStats
    @test keys(s.cond[:I]) == (:mean, :sd, :se, :q025, :q25, :q50, :q75, :q975)
    @test s == synthetic_summary()
    @test s != synthetic_summary(; same = true)
    @test sprint(show, s) == "EnsembleSummary(:sir_pois5, 34c89792, N = 10000, nsims = 5)"
    @test occursin("P(major) = 0.8000", sprint(show, MIME"text/plain"(), s))
    good = (; id = s.id, scenario_hash = s.scenario_hash, algorithm_revision = "r", N = 100, nsims = 5,
            n_major = 4, p_major = 0.8, p_major_ci = (0.4, 0.95), t = s.t, observables = s.observables,
            cond = s.cond, uncond = s.uncond, final_size = s.final_size, peak = s.peak, major = s.major)
    @test EnsembleSummary(; good...) isa EnsembleSummary
    bad = [(; scenario_hash = "abc"),                                   # not a full hash
           (; scenario_hash = uppercase(s.scenario_hash)),
           (; n_major = 3), (; p_major = 0.75),
           (; p_major_ci = (0.9, 0.4)), (; p_major_ci = (-0.1, 0.5)),
           (; final_size = s.final_size[1:4]), (; peak = s.peak[1:3]),
           (; major = BitVector([1, 1, 1, 1])),
           (; t = reverse(s.t)), (; t = s.t[1:end-1]),
           (; observables = [:S, :I]), (; observables = vcat(s.observables, [:S])),
           (; cond = Dict(X => v for (X, v) in s.cond if X !== :R)),
           (; nsims = 0), (; N = 0),
           # provenance is Dict{String,String}: a number is an ArgumentError with a message,
           # not a MethodError from String(v) (WP12 review)
           (; provenance = Dict("wall_time_s" => 4.2))]
    for b in bad
        @test_throws ArgumentError EnsembleSummary(; merge(good, b)...)
    end
    perr = try EnsembleSummary(; merge(good, (; provenance = Dict("wall_time_s" => 4.2)))...) catch e; e end
    @test occursin("provenance values must be strings", perr.msg) && occursin("wall_time_s", perr.msg)
    @test_throws ArgumentError EnsembleSummary(; good..., shifts = [1.0, 2.0])
    @test_throws ArgumentError EnsembleSummary(; good..., realised = Dict(:mean_degree => [1.0]))
    incomplete = Dict(X => (mean = v.mean, sd = v.sd) for (X, v) in s.cond)
    @test_throws ArgumentError EnsembleSummary(; merge(good, (; cond = incomplete))...)
end

@testset "save_summary / load_summary round trip" begin
    dir = mktempdir()
    ex = Dict{Symbol,Any}(:reinfection_histogram => [0.5, 0.25, 0.125, 0.125], :L => 3,
                          :label => "SIS", :converged => true, :bounds => [1, 2, 3])
    for s in (synthetic_summary(), synthetic_summary(; same = true),
              synthetic_summary(; shifts = [0.25, -1.5, 0.0, 1 / 3, 2.0], extras = ex),
              synthetic_summary(; major = BitVector([0, 0, 0, 0, 0])))
        paths = save_summary(dir, s)
        base = summary_basename(s.id, s.scenario_hash)
        @test base == "sir_pois5__" * first(scenario_hash(SC), 8)
        @test paths.toml == joinpath(dir, base * ".toml")
        @test paths.curves == joinpath(dir, base * ".curves.csv")
        @test paths.runs == joinpath(dir, base * ".runs.csv")
        @test all(isfile, values(paths))
        @test !any(f -> endswith(f, ".tmp"), readdir(dir))
        r = load_summary(dir, s.id, s.scenario_hash)
        @test r == s                                                # every field, NaN-aware
        for f in fieldnames(EnsembleSummary)
            @test isequal(getfield(r, f), getfield(s, f))
        end
        @test load_summary(dir, SC) == s
        @test load_summary(dir, SC; algorithm_revision = "NO-rev-7") == s
        # the files depend only on the summary: saving again gives the same bytes
        bytes = Dict(k => read(p) for (k, p) in pairs(paths))
        save_summary(dir, r)
        @test all(read(p) == bytes[k] for (k, p) in pairs(paths))
    end
    # the unconditioned columns are written only when they differ
    s1, s2 = synthetic_summary(), synthetic_summary(; same = true)
    h1 = split(readline(save_summary(joinpath(dir, "a"), s1).curves), ',')
    h2 = split(readline(save_summary(joinpath(dir, "b"), s2).curves), ',')
    @test length(h1) == 1 + 2 * 8 * length(SC.observables)
    @test length(h2) == 1 + 8 * length(SC.observables)
    @test h1[1] == "t" && h1[2] == "cond.S.mean" && "uncond.cumulative.q975" in h1
    # extras: TOML values (vectors keep their element type; symbols come back as strings)
    s3 = synthetic_summary(; extras = Dict{Symbol,Any}(:strata => :a, :M => [1.0 2.0; 3.0 4.0],
                                                      :hist => Dict(1 => 0.5, 2 => 0.5)))
    save_summary(dir, s3)
    r3 = load_summary(dir, SC)
    @test r3.extras[:strata] == "a"
    @test r3.extras[:M] == [[1.0, 2.0], [3.0, 4.0]]
    @test r3.extras[:hist] == Dict("1" => 0.5, "2" => 0.5)
    @test_throws ArgumentError save_summary(dir, synthetic_summary(; extras = Dict{Symbol,Any}(:f => sin)))
    # runs.csv: one row per run, with the alignment shifts when present
    s4 = synthetic_summary(; shifts = [0.25, -1.5, 0.0, 1 / 3, 2.0])
    lines = readlines(save_summary(dir, s4).runs)
    @test first(lines) == "run,final_size,peak_t,peak_value,major,shift,realised.erased_fraction,realised.mean_degree"
    @test length(lines) == 1 + s4.nsims
    @test startswith(lines[2], "1,0.80031,11.25,0.2311,1,0.25,")
end

@testset "stale, missing and foreign summaries are refused" begin
    dir = mktempdir()
    s = synthetic_summary()
    paths = save_summary(dir, s)
    other = derive(SC; nsims = 400, id = SC.id)      # same id, new hash: the committed file is stale
    err = try
        load_summary(dir, other); nothing
    catch e
        e
    end
    @test err isa ArgumentError
    @test occursin("no summary", err.msg) && occursin(basename(paths.toml), err.msg)   # names the stale file
    @test_throws ArgumentError load_summary(dir, SC.id, first(s.scenario_hash, 8))    # short hash
    @test_throws ArgumentError load_summary(dir, SC; algorithm_revision = "NO-rev-8")
    @test_throws ArgumentError load_summary(joinpath(dir, "nowhere"), SC)
    # a file whose stored hash disagrees with its name (a colliding prefix or an edited file)
    txt = read(paths.toml, String)
    fake = s.scenario_hash[1:8] * repeat("0", 56)
    write(paths.toml, replace(txt, s.scenario_hash => fake))
    @test_throws ArgumentError load_summary(dir, SC)
    write(paths.toml, replace(txt, "summary_format = 1" => "summary_format = 99"))
    @test_throws ArgumentError load_summary(dir, SC)
    write(paths.toml, txt)
    @test load_summary(dir, SC) == s
    mv(paths.runs, paths.runs * ".bak")
    @test_throws ArgumentError load_summary(dir, SC)                 # an incomplete summary
    mv(paths.runs * ".bak", paths.runs)
    @test load_summary(dir, SC) == s
    @test_throws ArgumentError summary_basename(:x, "abc")
end
