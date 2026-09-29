# Owner: WP12 (DESIGN_NetworkEpiCore.md §E.2, §E.4; work package in §G.2).
#
# The summary of a reference stochastic ensemble (`EnsembleSummary`) and its file format: one
# TOML file (scalars, provenance, extras) and two CSV files (the pointwise statistics on the time
# grid; the per-run values), written and read with the standard library only. NetworkOutbreaks
# produces the summaries and commits them under data/scenarios/; EdgeBasedModels and
# NodeBasedModels read them with `load_summary` and compare their curves with `compare`.

export SummaryStats, EnsembleSummary, save_summary, load_summary, summary_basename

"""
    SummaryStats

The pointwise statistics of one observable over the runs of an ensemble, each a
`Vector{Float64}` on the summary's time grid:
`(mean, sd, se, q025, q25, q50, q75, q975)` — the mean, standard deviation, standard error of the
mean, and the 2.5%, 25%, 50%, 75% and 97.5% quantiles. The *spread* band is q025–q975 and the
*mean* band mean ± 1.96·se (§E.2). `SummaryStats(; mean, sd, se, q025, q25, q50, q75, q975)`
builds one.
"""
const SummaryStats = NamedTuple{(:mean, :sd, :se, :q025, :q25, :q50, :q75, :q975),
                                NTuple{8,Vector{Float64}}}

const _STAT_NAMES = (:mean, :sd, :se, :q025, :q25, :q50, :q75, :q975)

_summary_stats(nt::NamedTuple) = begin
    missing_ = [s for s in _STAT_NAMES if !haskey(nt, s)]
    isempty(missing_) || throw(ArgumentError(
        "summary statistics need the fields $(_STAT_NAMES); missing $(_list(missing_))"))
    SummaryStats(Tuple(collect(Float64, getfield(nt, s)) for s in _STAT_NAMES))
end

"""
    EnsembleSummary(; id, scenario_hash, algorithm_revision, N, nsims, n_major, p_major,
                    p_major_ci, t, observables, cond, uncond, final_size, peak, major,
                    shifts = Float64[], realised = Dict(), extras = Dict(), provenance = Dict())

The summary of a reference stochastic ensemble for one [`Scenario`](@ref) (§E.4), produced by
NetworkOutbreaks and read by EdgeBasedModels and NodeBasedModels:

- `id`, `scenario_hash` (the 64-hex [`scenario_hash`](@ref) of the scenario it summarises) and
  `algorithm_revision` (NetworkOutbreaks' `ALGORITHM_REVISION`): together the cache key;
- `N`, `nsims`; `n_major` runs satisfied the scenario's conditioning rule, `p_major =
  n_major/nsims` with the 95% Wilson interval `p_major_ci`;
- `t` (the scenario's time grid) and `observables`;
- `cond` and `uncond`: `observable => `[`SummaryStats`](@ref), over the major runs and over all
  runs (comparisons use `cond`);
- per run (length `nsims`): `final_size` (fraction ever infected, including seeds), `peak`
  (`(t_peak, peak value)` of prevalence), `major::BitVector`, `shifts` (time-alignment shifts;
  empty without alignment) and `realised` (`name => values`, e.g. `:mean_degree`,
  `:excess_degree`, `:clustering`, `:erased_fraction` of each run's graph);
- `extras` (e.g. `:reinfection_histogram`) and `provenance` (Julia and package versions, git
  SHAs, date, wall time).

The constructor checks that every array has the right length, that `n_major == count(major)`,
`p_major == n_major/nsims` and `0 ≤ lo ≤ hi ≤ 1` for the interval. See [`save_summary`](@ref)
and [`load_summary`](@ref).
"""
struct EnsembleSummary
    id::Symbol
    scenario_hash::String
    algorithm_revision::String
    N::Int
    nsims::Int
    n_major::Int
    p_major::Float64
    p_major_ci::NTuple{2,Float64}
    t::Vector{Float64}
    observables::Vector{Symbol}
    cond::Dict{Symbol,SummaryStats}
    uncond::Dict{Symbol,SummaryStats}
    final_size::Vector{Float64}
    peak::Vector{NTuple{2,Float64}}
    major::BitVector
    shifts::Vector{Float64}
    realised::Dict{Symbol,Vector{Float64}}
    extras::Dict{Symbol,Any}
    provenance::Dict{String,String}
    function EnsembleSummary(id::Symbol, scenario_hash::AbstractString,
                             algorithm_revision::AbstractString, N::Integer, nsims::Integer,
                             n_major::Integer, p_major::Real, p_major_ci::Tuple{Real,Real},
                             t::AbstractVector{<:Real}, observables::AbstractVector,
                             cond::AbstractDict, uncond::AbstractDict,
                             final_size::AbstractVector{<:Real}, peak::AbstractVector,
                             major::AbstractVector{Bool}, shifts::AbstractVector{<:Real},
                             realised::AbstractDict, extras::AbstractDict, provenance::AbstractDict)
        where = "EnsembleSummary :$(id)"
        occursin(r"^[0-9a-f]{64}$", scenario_hash) || throw(ArgumentError(
            "$(where): scenario_hash must be the 64 lowercase hex digits of scenario_hash(sc)"))
        N >= 1 && nsims >= 1 || throw(ArgumentError("$(where): N and nsims must be ≥ 1"))
        tt = collect(Float64, t)
        (!isempty(tt) && issorted(tt; lt = <=) && all(isfinite, tt)) || throw(ArgumentError(
            "$(where): t must be a non-empty, strictly increasing grid of finite times"))
        obs = collect(Symbol, observables)
        (isempty(obs) || !allunique(obs)) && throw(ArgumentError(
            "$(where): observables must be non-empty and unique; got $(obs)"))
        c = _stats_dict(cond, obs, length(tt), "$(where) (cond)")
        u = _stats_dict(uncond, obs, length(tt), "$(where) (uncond)")
        _check_length(final_size, nsims, "final_size", where)
        _check_length(peak, nsims, "peak", where)
        _check_length(major, nsims, "major", where)
        isempty(shifts) || _check_length(shifts, nsims, "shifts", where)
        n_major == count(major) || throw(ArgumentError(
            "$(where): n_major = $(n_major) but $(count(major)) runs are marked major"))
        isapprox(p_major, n_major / nsims; atol = 1e-12) || throw(ArgumentError(
            "$(where): p_major = $(p_major) differs from n_major/nsims = $(n_major / nsims)"))
        lo, hi = Float64.(p_major_ci)
        0 <= lo <= hi <= 1 || throw(ArgumentError(
            "$(where): p_major_ci must satisfy 0 ≤ lo ≤ hi ≤ 1; got $(p_major_ci)"))
        rl = Dict{Symbol,Vector{Float64}}()
        for (k, v) in realised
            _check_length(v, nsims, "realised[:$(k)]", where)
            rl[Symbol(k)] = collect(Float64, v)
        end
        pk = NTuple{2,Float64}[(Float64(first(x)), Float64(last(x))) for x in peak]
        bad = [k for (k, v) in provenance if !(v isa AbstractString)]
        isempty(bad) || throw(ArgumentError(
            "$(where): provenance values must be strings (it is a Dict{String,String} of versions, " *
            "commits and settings); $(join(repr.(bad), ", ")) " *
            "$(length(bad) == 1 ? "is" : "are") not: pass string(value)"))
        return new(id, String(scenario_hash), String(algorithm_revision), Int(N), Int(nsims),
                   Int(n_major), Float64(p_major), (lo, hi), tt, obs, c, u,
                   collect(Float64, final_size), pk, BitVector(major), collect(Float64, shifts), rl,
                   Dict{Symbol,Any}(Symbol(k) => v for (k, v) in extras),
                   Dict{String,String}(String(k) => String(v) for (k, v) in provenance))
    end
end

function EnsembleSummary(; id::Symbol, scenario_hash::AbstractString,
                         algorithm_revision::AbstractString, N::Integer, nsims::Integer,
                         n_major::Integer, p_major::Real, p_major_ci::Tuple{Real,Real},
                         t::AbstractVector{<:Real}, observables::AbstractVector,
                         cond::AbstractDict, uncond::AbstractDict,
                         final_size::AbstractVector{<:Real}, peak::AbstractVector,
                         major::AbstractVector{Bool}, shifts::AbstractVector{<:Real} = Float64[],
                         realised::AbstractDict = Dict{Symbol,Vector{Float64}}(),
                         extras::AbstractDict = Dict{Symbol,Any}(),
                         provenance::AbstractDict = Dict{String,String}())
    return EnsembleSummary(id, scenario_hash, algorithm_revision, N, nsims, n_major, p_major,
                           p_major_ci, t, observables, cond, uncond, final_size, peak, major,
                           shifts, realised, extras, provenance)
end

function _stats_dict(d::AbstractDict, obs, n, where)
    Set(Symbol(k) for k in keys(d)) == Set(obs) || throw(ArgumentError(
        "$(where): statistics are given for $(_list(sort!(Symbol.(collect(keys(d)))))) but the " *
        "observables are $(_list(obs))"))
    out = Dict{Symbol,SummaryStats}()
    for (k, v) in d
        s = _summary_stats(v)
        for f in _STAT_NAMES
            length(getfield(s, f)) == n || throw(ArgumentError(
                "$(where): $(k).$(f) has $(length(getfield(s, f))) values for $(n) grid times"))
        end
        out[Symbol(k)] = s
    end
    return out
end

_check_length(v, n, what, where) = length(v) == n || throw(ArgumentError(
    "$(where): $(what) has $(length(v)) entries for nsims = $(n) runs"))

function Base.:(==)(a::EnsembleSummary, b::EnsembleSummary)
    return all(isequal(getfield(a, f), getfield(b, f)) for f in fieldnames(EnsembleSummary))
end

Base.show(io::IO, s::EnsembleSummary) =
    print(io, "EnsembleSummary(:", s.id, ", ", first(s.scenario_hash, 8), ", N = ", s.N,
          ", nsims = ", s.nsims, ")")

function Base.show(io::IO, ::MIME"text/plain", s::EnsembleSummary)
    println(io, "EnsembleSummary :", s.id, "  (scenario ", first(s.scenario_hash, 8),
            ", algorithm revision ", s.algorithm_revision, ")")
    println(io, "  N = ", s.N, ", nsims = ", s.nsims, ", major runs ", s.n_major,
            @sprintf(" (P(major) = %.4f, 95%% CI %.4f–%.4f)", s.p_major, s.p_major_ci...))
    println(io, "  t ∈ [", first(s.t), ", ", last(s.t), "], ", length(s.t), " grid times; ",
            "observables ", join(s.observables, ", "))
    fs = s.final_size[s.major]
    if !isempty(fs)
        m = sum(fs) / length(fs)
        sd = length(fs) > 1 ? sqrt(sum(abs2, fs .- m) / (length(fs) - 1)) : NaN
        print(io, @sprintf("  final size (major runs): mean %.4f, sd %.4f", m, sd))
    else
        print(io, "  final size: no major runs")
    end
end

# =============================================================================================
# Files
# =============================================================================================

"""
    summary_basename(id::Symbol, scenario_hash::AbstractString) -> String

The base name `"<id>__<first 8 hex digits of the hash>"` of the three files of a summary
(`.toml`, `.curves.csv`, `.runs.csv`), as committed under NetworkOutbreaks'
`data/scenarios/`.
"""
function summary_basename(id::Symbol, hash::AbstractString)
    length(hash) >= 8 || throw(ArgumentError("summary_basename: the hash needs at least 8 hex digits"))
    return string(id, "__", first(hash, 8))
end

const _SUMMARY_FORMAT = 1

# Round-trip exact text of a number: the shortest decimal that parses back to the same Float64
# (Julia's `print`), `NaN` / `Inf`; integers as integers.
_csv_number(io::IO, x::Integer) = print(io, x)
_csv_number(io::IO, x::Real) = print(io, Float64(x))

function _write_csv(path::AbstractString, header::Vector{String}, columns::Vector{Vector{Any}})
    n = isempty(columns) ? 0 : length(first(columns))
    open(path, "w") do io
        println(io, join(header, ','))
        for i in 1:n
            for (j, col) in enumerate(columns)
                j > 1 && print(io, ',')
                _csv_number(io, col[i])
            end
            println(io)
        end
    end
    return path
end

function _read_csv(path::AbstractString)
    isfile(path) || throw(ArgumentError("load_summary: the summary file $(path) is missing"))
    data, header = DelimitedFiles.readdlm(path, ',', Float64, '\n'; header = true)
    names = String[strip(string(h)) for h in vec(header)]
    return names, data
end

# Values that TOML can hold (extras): numbers, strings, booleans, vectors, matrices (as vectors
# of rows) and dictionaries with string keys.
_toml_value(x::Bool) = x
_toml_value(x::Integer) = Int64(x)
_toml_value(x::Real) = Float64(x)
_toml_value(x::AbstractString) = String(x)
_toml_value(x::Symbol) = String(x)
_toml_value(x::AbstractVector) = Any[_toml_value(v) for v in x]
_toml_value(x::AbstractVector{<:Real}) = eltype(x) <: Integer ? Int64.(x) : Float64.(x)
_toml_value(x::AbstractVector{Bool}) = collect(Bool, x)
_toml_value(x::AbstractMatrix) = Any[_toml_value(collect(r)) for r in eachrow(x)]
_toml_value(x::AbstractDict) = Dict{String,Any}(string(k) => _toml_value(v) for (k, v) in x)
_toml_value(x) = throw(ArgumentError(
    "save_summary: an extras value of type $(typeof(x)) cannot be written to TOML; use numbers, " *
    "strings, vectors, matrices or dictionaries of them"))

function _atomic_write(f, path::AbstractString)
    tmp = path * ".tmp"
    f(tmp)
    mv(tmp, path; force = true)
    return path
end

"""
    save_summary(dir, s::EnsembleSummary) -> NamedTuple{(:toml, :curves, :runs)}

Write `s` to three files in `dir` (created if needed), named by
[`summary_basename`](@ref)`(s.id, s.scenario_hash)`:

- `<base>.toml`: `summary_format = 1`, the id, the full scenario hash, the algorithm revision,
  N, nsims, n_major, p_major and its interval, the observables, the names of the two CSV files,
  `[provenance]` and `[extras]` (TOML values; symbols are written as strings and matrices as
  lists of rows);
- `<base>.curves.csv`: the column `t`, then `cond.<obs>.<stat>` and `uncond.<obs>.<stat>` for
  every observable and every statistic of [`SummaryStats`](@ref) (the `uncond` columns are left
  out when they equal the `cond` ones, as when every run is major; the TOML key
  `uncond_equals_cond` records it);
- `<base>.runs.csv`: `run`, `final_size`, `peak_t`, `peak_value`, `major` (0/1), `shift` (only
  with alignment) and `realised.<name>` per run.

Numbers are written as the shortest decimal that reads back to the same `Float64`, so
`load_summary` returns an identical summary, and the files depend only on the summary (the same
summary always gives byte-identical files). Existing files are replaced.
"""
function save_summary(dir::AbstractString, s::EnsembleSummary)
    mkpath(dir)
    base = summary_basename(s.id, s.scenario_hash)
    paths = (toml = joinpath(dir, base * ".toml"), curves = joinpath(dir, base * ".curves.csv"),
             runs = joinpath(dir, base * ".runs.csv"))
    # curves
    header = ["t"]
    cols = Vector{Any}[collect(Any, s.t)]
    same = isequal(s.cond, s.uncond)       # every run major: store the statistics once
    sets = same ? (("cond", s.cond),) : (("cond", s.cond), ("uncond", s.uncond))
    for (which, stats) in sets, X in s.observables, f in _STAT_NAMES
        push!(header, "$(which).$(X).$(f)")
        push!(cols, collect(Any, getfield(stats[X], f)))
    end
    _atomic_write(tmp -> _write_csv(tmp, header, cols), paths.curves)
    # runs
    rheader = ["run", "final_size", "peak_t", "peak_value", "major"]
    rcols = Vector{Any}[collect(Any, 1:s.nsims), collect(Any, s.final_size),
                        Any[first(p) for p in s.peak], Any[last(p) for p in s.peak],
                        Any[Int(m) for m in s.major]]
    if !isempty(s.shifts)
        push!(rheader, "shift")
        push!(rcols, collect(Any, s.shifts))
    end
    for k in sort!(collect(keys(s.realised)); by = string)
        push!(rheader, "realised.$(k)")
        push!(rcols, collect(Any, s.realised[k]))
    end
    _atomic_write(tmp -> _write_csv(tmp, rheader, rcols), paths.runs)
    # toml
    d = Dict{String,Any}("summary_format" => _SUMMARY_FORMAT, "id" => String(s.id),
                         "scenario_hash" => s.scenario_hash,
                         "algorithm_revision" => s.algorithm_revision, "N" => s.N,
                         "nsims" => s.nsims, "n_major" => s.n_major, "p_major" => s.p_major,
                         "p_major_ci" => collect(s.p_major_ci),
                         "observables" => String.(s.observables),
                         "statistics" => String.(collect(_STAT_NAMES)),
                         "curves_file" => basename(paths.curves), "runs_file" => basename(paths.runs),
                         "uncond_equals_cond" => same,
                         "provenance" => Dict{String,Any}(s.provenance),
                         "extras" => Dict{String,Any}(String(k) => _toml_value(v) for (k, v) in s.extras))
    _atomic_write(paths.toml) do tmp
        open(io -> TOML.print(io, d; sorted = true), tmp, "w")
    end
    return paths
end

"""
    load_summary(dir, id::Symbol, scenario_hash::AbstractString; algorithm_revision = nothing)
        -> EnsembleSummary
    load_summary(dir, sc::Scenario; algorithm_revision = nothing) -> EnsembleSummary

Read the summary written by [`save_summary`](@ref) for scenario `id` with the full 64-hex
`scenario_hash` from `dir`. It **never returns a stale summary**: it is an `ArgumentError` if the
files are missing (the message lists the summaries of `id` that do exist, i.e. stale hashes), if
the hash stored in the file differs from the one requested, or if `algorithm_revision` is given
and differs from the stored one.
"""
function load_summary(dir::AbstractString, id::Symbol, hash::AbstractString;
                      algorithm_revision::Union{Nothing,AbstractString} = nothing)
    occursin(r"^[0-9a-f]{64}$", hash) || throw(ArgumentError(
        "load_summary(:$(id)): pass the full 64-hex scenario hash (scenario_hash(sc)) so that a " *
        "stale summary cannot be loaded"))
    base = summary_basename(id, hash)
    tpath = joinpath(dir, base * ".toml")
    if !isfile(tpath)
        others = isdir(dir) ? sort!([f for f in readdir(dir)
                                     if startswith(f, string(id, "__")) && endswith(f, ".toml")]) :
                 String[]
        throw(ArgumentError(
            "load_summary: no summary $(base) for scenario :$(id) in $(dir)" *
            (isempty(others) ? "" : "; summaries of :$(id) with other (stale) hashes: " *
                                    join(others, ", ")) *
            ". Regenerate it with NetworkOutbreaks (scripts/regenerate_scenarios.jl)"))
    end
    d = TOML.parsefile(tpath)
    get(d, "summary_format", 0) == _SUMMARY_FORMAT || throw(ArgumentError(
        "load_summary: $(tpath) has summary_format $(get(d, "summary_format", "none")); this " *
        "version of NetworkEpiCore reads format $(_SUMMARY_FORMAT)"))
    d["scenario_hash"] == hash || throw(ArgumentError(
        "load_summary: $(tpath) summarises scenario hash $(d["scenario_hash"]), not the requested " *
        "$(hash) (a stale or colliding summary); regenerate it"))
    d["id"] == String(id) || throw(ArgumentError(
        "load_summary: $(tpath) is the summary of :$(d["id"]), not :$(id)"))
    if algorithm_revision !== nothing && d["algorithm_revision"] != algorithm_revision
        throw(ArgumentError(
            "load_summary: $(tpath) was generated with algorithm revision " *
            "$(d["algorithm_revision"]), not $(algorithm_revision); regenerate it"))
    end
    obs = Symbol.(d["observables"])
    cnames, cdata = _read_csv(joinpath(dir, d["curves_file"]))
    col(names, data, name) = begin
        j = findfirst(==(name), names)
        j === nothing && throw(ArgumentError("load_summary: column $(name) missing in $(dir)"))
        data[:, j]
    end
    t = col(cnames, cdata, "t")
    stats(which) = Dict{Symbol,SummaryStats}(
        X => SummaryStats(Tuple(col(cnames, cdata, "$(which).$(X).$(f)") for f in _STAT_NAMES))
        for X in obs)
    cond = stats("cond")
    uncond = get(d, "uncond_equals_cond", false) ? cond : stats("uncond")
    rnames, rdata = _read_csv(joinpath(dir, d["runs_file"]))
    realised = Dict{Symbol,Vector{Float64}}(Symbol(n[10:end]) => col(rnames, rdata, n)
                                            for n in rnames if startswith(n, "realised."))
    shifts = "shift" in rnames ? col(rnames, rdata, "shift") : Float64[]
    peak = NTuple{2,Float64}[(a, b) for (a, b) in zip(col(rnames, rdata, "peak_t"),
                                                       col(rnames, rdata, "peak_value"))]
    extras = Dict{Symbol,Any}(Symbol(k) => v for (k, v) in get(d, "extras", Dict{String,Any}()))
    prov = Dict{String,String}(k => string(v) for (k, v) in get(d, "provenance", Dict{String,Any}()))
    ci = d["p_major_ci"]
    return EnsembleSummary(Symbol(d["id"]), d["scenario_hash"], d["algorithm_revision"], d["N"],
                           d["nsims"], d["n_major"], d["p_major"], (ci[1], ci[2]), t, obs,
                           cond, uncond, col(rnames, rdata, "final_size"), peak,
                           col(rnames, rdata, "major") .!= 0, shifts, realised, extras, prov)
end
load_summary(dir::AbstractString, sc::Scenario; kw...) =
    load_summary(dir, sc.id, scenario_hash(sc); kw...)
