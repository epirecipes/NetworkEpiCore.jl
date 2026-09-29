# Owner: WP5 (DESIGN_NetworkEpiCore.md §A.2 "NEC export hygiene" and §A.8).
#
# Part 1 (always runs, in NEC's own test environment):
#   - export hygiene: the never-exported names, every export defined and documented, no `@enum`,
#     the generic stubs of the §A.2 table, the ContactModel accessors;
#   - NEC loads with its hard dependencies only (stdlib + RecipesBase), without its weak deps;
#   - every NEC export resolves to NEC's binding next to the ecosystem packages of §A.8 that are
#     installed here (Catalyst, ModelingToolkit, Symbolics, Graphs, StatsBase, Distributions,
#     Plots, …), and NEC plus its loaded extensions have no method ambiguities.
#
# Part 2 (the collision integration test of §A.8): NEC, EdgeBasedModels, NodeBasedModels and
# NetworkOutbreaks loaded together with Catalyst, ModelingToolkit, StatsBase, Graphs,
# Distributions and Plots. It self-skips unless all three sibling packages are at least 0.2 and
# present in the active environment. Run it in the root workspace environment:
#
#     cd NetworkEpiCore.jl
#     NEC_TEST_SUITES=integration julia --project=../dev test/runtests.jl
#
# NEC_INTEGRATION=force runs part 2 whatever the sibling versions; NEC_INTEGRATION=skip skips it.

using Test
using NetworkEpiCore
import TOML

const NEC = NetworkEpiCore

# §A.2: names NetworkEpiCore never exports.
const NEVER_EXPORTED = (:parameters, :species, :reactions, :equations, :compose, :solve, :simulate,
                        :pairwise, :Transition, :Poisson, :Binomial, :NegativeBinomial, :Geometric,
                        :exit, :Node, :⊗, :namespace)

# §A.2 generics table (src/generics.jl), plus `canonical_text`, which several NEC files extend.
const GENERIC_STUBS = (:basic_reproduction_number, :next_generation_matrix, :transmissibility,
                       :final_size, :epidemic_probability,
                       :epidemic_threshold, :early_growth_rate, :disease_free_equilibrium,
                       :default_initial_conditions, :solve_epidemic, :model_curves, :symbolic_ode,
                       :compartment, :compartments, :population_fraction,
                       :mean_degree, :excess_degree, :pgf, :pgf_derivative, :clustering_coefficient,
                       :contact_model, :mass_action, :stratify,
                       :with_reinfection_counting, :reinfection_totals, :base_compartment_of,
                       :infection_count_of, :reinfection_histogram,
                       :verify, :pushforward, :canonical_text)

# §A.2 "Access": ContactModel fields are read through these exported accessors.
const CONTACT_MODEL_ACCESSORS = (:species_names, :rate_parameters, :contacts, :node_transitions)

# Packages loaded next to NEC (§A.8), apart from the three siblings.
const ECOSYSTEM = (:Catalyst, :ModelingToolkit, :ModelingToolkitBase, :Symbolics, :Graphs,
                   :StatsBase, :Distributions, :Plots, :StableRNGs, :Statistics, :LinearAlgebra,
                   :Random)
const SIBLINGS = (:EdgeBasedModels, :NodeBasedModels, :NetworkOutbreaks)
const A8_PACKAGES = (:Catalyst, :ModelingToolkit, :StatsBase, :Graphs, :Distributions, :Plots)

# Hard dependencies of NEC that are not standard libraries, with their own dependencies.
const ALLOWED_NONSTDLIB = ("NetworkEpiCore", "RecipesBase", "PrecompileTools", "Preferences")

# `names` also lists `public` (unexported) names from Julia 1.11 on; only exports enter `using`.
isexported_(m::Module, s::Symbol) = isdefined(Base, :isexported) ? Base.isexported(m, s) : true
exported_names(m::Module) = sort!([n for n in names(m) if n !== nameof(m) && isexported_(m, n)])

available(pkg::Symbol) = Base.identify_package(String(pkg)) !== nothing

function has_docstring(m::Module, s::Symbol)
    b = Base.Docs.Binding(m, s)             # normalised to the module that owns the binding
    return haskey(Base.Docs.meta(b.mod), b)
end

is_enum(x) = x isa Base.Enum || (x isa Type && x !== Union{} && x <: Base.Enum)

"Does `n` resolve in `sandbox` to the binding that module `M` exports under that name?"
resolves_to(sandbox::Module, n::Symbol, M::Module) =
    isdefined(sandbox, n) && getfield(sandbox, n) === getfield(M, n)

"The version in the Project.toml of `pkg` as found in the active environment, or `nothing`."
function package_version(pkg::Symbol)
    id = Base.identify_package(String(pkg))
    id === nothing && return nothing
    src = Base.locate_package(id)
    src === nothing && return nothing
    for f in ("JuliaProject.toml", "Project.toml")
        p = joinpath(dirname(dirname(src)), f)
        isfile(p) && return VersionNumber(get(TOML.parsefile(p), "version", "0.0.0"))
    end
    return nothing
end

"""
Run `code` in a fresh Julia process that sees the same environment (load path and active
project) as this one; return its exit status and captured output.
"""
function run_julia(code::AbstractString)
    sep = Sys.iswindows() ? ";" : ":"
    env = ("JULIA_LOAD_PATH" => join(LOAD_PATH, sep), "JULIA_PROJECT" => Base.active_project())
    out, err = IOBuffer(), IOBuffer()
    proc = withenv(env...) do
        cmd = ignorestatus(`$(Base.julia_cmd()) --startup-file=no -e $code`)
        run(pipeline(cmd; stdout = out, stderr = err))
    end
    return (ok = success(proc), out = String(take!(out)), err = String(take!(err)))
end

# ---------------------------------------------------------------------------------------------
# Part 1: export hygiene (§A.2)
# ---------------------------------------------------------------------------------------------

@testset "export hygiene (§A.2)" begin
    exported = exported_names(NEC)
    @test isempty(intersect(exported, NEVER_EXPORTED))
    @test isempty([n for n in exported if !isdefined(NEC, n)])       # no dangling exports
    @test isempty([n for n in exported if isdefined(NEC, n) && !has_docstring(NEC, n)])
    @test isempty([n for n in names(NEC; all = true)
                   if isdefined(NEC, n) && is_enum(getfield(NEC, n))])
end

@testset "generic stubs (§A.2 table)" begin
    for n in GENERIC_STUBS
        @test isexported_(NEC, n)
        @test isdefined(NEC, n) && getfield(NEC, n) isa Function
        @test isdefined(NEC, n) && parentmodule(getfield(NEC, n)) === NEC   # owned, not imported
        @test has_docstring(NEC, n)
    end
end

@testset "ContactModel accessors (§A.2)" begin
    if isdefined(NEC, :ContactModel)
        for n in CONTACT_MODEL_ACCESSORS
            @test isexported_(NEC, n) && isdefined(NEC, n)
        end
    else
        @test_skip "ContactModel is not defined yet (WP6)"
    end
end

@testset "loads with stdlib + RecipesBase only (§A.1)" begin
    code = """
    using NetworkEpiCore
    for id in sort!(collect(keys(Base.loaded_modules)); by = k -> k.name)
        id.uuid === nothing && continue
        # by name: an upgradable stdlib (e.g. DelimitedFiles) may be loaded from the depot
        println(isdir(joinpath(Sys.STDLIB, id.name)) ? "STDLIB " : "PACKAGE ", id.name)
    end
    """
    # A fresh process in the current environment: `using NetworkEpiCore` alone loads exactly
    # NEC's dependency closure (extensions load only with their trigger packages), whatever else
    # the environment contains.
    r = run_julia(code)
    @test r.ok
    r.ok || @info "subprocess failed" r.err
    loaded = [split(l)[2] for l in split(r.out, '\n') if startswith(l, "PACKAGE ")]
    @test "NetworkEpiCore" in loaded
    @test isempty(setdiff(loaded, ALLOWED_NONSTDLIB))
end

# Load the installed ecosystem packages into a sandbox module (a separate top-level statement,
# so that the checks below run in a world that sees the new bindings).
const ECO = Tuple(p for p in ECOSYSTEM if available(p))
const ECO_SANDBOX = Module(:NECEcosystemSandbox)
Core.eval(ECO_SANDBOX, :(using NetworkEpiCore))
for p in ECO
    Core.eval(ECO_SANDBOX, Expr(:using, Expr(:., p)))
end

@testset "NEC exports resolve next to the ecosystem (§A.8, siblings excluded)" begin
    @info "Ecosystem loaded next to NetworkEpiCore" packages = ECO
    @test :Plots in ECO && :Catalyst in ECO && :ModelingToolkit in ECO   # from the test env
    clashes = [n for n in exported_names(NEC) if !resolves_to(ECO_SANDBOX, n, NEC)]
    @test isempty(clashes)
    exts = filter(!isnothing, [Base.get_extension(NEC, e) for e in (:NetworkEpiCoreSymbolicsExt,
           :NetworkEpiCoreCatalystExt, :NetworkEpiCoreMTKExt, :NetworkEpiCoreGraphsExt)])
    @test length(exts) == 4                        # Symbolics, Catalyst, MTK and Graphs are loaded
    @test isempty(Test.detect_ambiguities(NEC, exts...))
end

# ---------------------------------------------------------------------------------------------
# Part 2: the collision integration test (§A.8)
# ---------------------------------------------------------------------------------------------

const INTEGRATION_MODE = lowercase(strip(get(ENV, "NEC_INTEGRATION", "auto")))
INTEGRATION_MODE in ("auto", "force", "skip") ||
    error("NEC_INTEGRATION must be auto, force or skip; got $(repr(INTEGRATION_MODE))")

function integration_skip_reason()
    INTEGRATION_MODE == "skip" && return "NEC_INTEGRATION=skip"
    INTEGRATION_MODE == "force" && return nothing
    absent = [p for p in (SIBLINGS..., A8_PACKAGES...) if !available(p)]
    isempty(absent) || return "not in the active environment: $(join(absent, ", "))"
    old = [p => package_version(p) for p in SIBLINGS
           if something(package_version(p), v"0") < v"0.2.0-"]
    isempty(old) || return "sibling packages below 0.2: $(join(("$p $v" for (p, v) in old), ", "))"
    return nothing
end

const SKIP_REASON = integration_skip_reason()
const A8_SANDBOX = Module(:NECIntegrationSandbox)
if SKIP_REASON === nothing
    Core.eval(A8_SANDBOX, :(using NetworkEpiCore))
    for p in (SIBLINGS..., A8_PACKAGES...)
        Core.eval(A8_SANDBOX, Expr(:using, Expr(:., p)))
    end
end

@testset "collision integration (§A.8)" begin
    if SKIP_REASON !== nothing
        @info "Skipping the §A.8 collision test" reason = SKIP_REASON
        @test_skip SKIP_REASON
    else
        mods = Tuple(getfield(A8_SANDBOX, p) for p in SIBLINGS)
        @info "Running the §A.8 collision test" versions = [p => package_version(p)
                                                             for p in SIBLINGS]

        @testset "every NEC export resolves to NEC's binding" begin
            unresolved = [n for n in exported_names(NEC) if !resolves_to(A8_SANDBOX, n, NEC)]
            @test isempty(unresolved)
        end

        # every name the sibling exports or declares public (§A.8 says `names`, which on Julia
        # 1.11+ also lists `public` names) that NEC defines must be NEC's binding
        @testset "$(nameof(M)) re-exports the NEC bindings" for M in mods
            diverging = [n for n in names(M)
                         if n !== nameof(M) && isdefined(NEC, n) && isdefined(M, n) &&
                            getfield(M, n) !== getfield(NEC, n)]
            @test isempty(diverging)
        end

        @testset "every sibling export resolves unambiguously" begin
            unresolved = [Symbol(nameof(M), :., n) for M in mods for n in exported_names(M)
                          if !resolves_to(A8_SANDBOX, n, M)]
            @test isempty(unresolved)
        end

        # NEC's loaded extensions too: a sibling method on an NEC generic could be ambiguous
        # with an extension method (WP5 review)
        @testset "no method ambiguities" begin
            exts = filter(!isnothing, [Base.get_extension(NEC, e)
                                       for e in (:NetworkEpiCoreSymbolicsExt,
                                                 :NetworkEpiCoreCatalystExt,
                                                 :NetworkEpiCoreMTKExt, :NetworkEpiCoreGraphsExt)])
            @test length(exts) == 4                 # Catalyst, MTK and Graphs are loaded here
            @test isempty(Test.detect_ambiguities(NEC, exts..., mods...))
        end

        @testset "subprocess: no \"both … export\" warning" begin
            code = """
            using EdgeBasedModels, NodeBasedModels, NetworkOutbreaks, Catalyst, StatsBase
            for M in (EdgeBasedModels, NodeBasedModels, NetworkOutbreaks), n in names(M)
                isdefined(Base, :isexported) && !Base.isexported(M, n) && continue
                isdefined(Main, n) || println("UNRESOLVED ", nameof(M), ".", n)
            end
            """
            r = run_julia(code)
            @test r.ok
            r.ok || @info "subprocess failed" r.err
            @test !occursin(r"both \S+ and \S+ export", r.err)
            @test isempty([l for l in split(r.out, '\n') if startswith(l, "UNRESOLVED")])
        end

        # the full §A.8 load line in a fresh process (steward-2): every export of NEC and of the
        # siblings resolves, no "both … export" warning, and no method ambiguities among NEC, its
        # extensions and the siblings
        @testset "subprocess: the full §A.8 load line" begin
            code = """
            using NetworkEpiCore, EdgeBasedModels, NodeBasedModels, NetworkOutbreaks, Catalyst,
                  ModelingToolkit, StatsBase, Graphs, Plots
            using Test
            for M in (NetworkEpiCore, EdgeBasedModels, NodeBasedModels, NetworkOutbreaks), n in names(M)
                isdefined(Base, :isexported) && !Base.isexported(M, n) && continue
                isdefined(Main, n) || println("UNRESOLVED ", nameof(M), ".", n)
            end
            exts = filter(!isnothing, [Base.get_extension(NetworkEpiCore, e)
                                       for e in (:NetworkEpiCoreSymbolicsExt, :NetworkEpiCoreCatalystExt,
                                                 :NetworkEpiCoreMTKExt, :NetworkEpiCoreGraphsExt)])
            println("EXTENSIONS ", length(exts))
            amb = Test.detect_ambiguities(NetworkEpiCore, exts..., EdgeBasedModels, NodeBasedModels,
                                          NetworkOutbreaks)
            for (a, b) in amb
                println("AMBIGUOUS ", a, " <> ", b)
            end
            println("AMBIGUITIES ", length(amb))
            """
            r = run_julia(code)
            @test r.ok
            r.ok || @info "subprocess failed" r.err
            @test !occursin(r"both \S+ and \S+ export", r.err)
            lines = split(r.out, '\n')
            @test isempty([l for l in lines if startswith(l, "UNRESOLVED")])
            @test "EXTENSIONS 4" in lines
            @test "AMBIGUITIES 0" in lines
            any(startswith("AMBIGUOUS"), lines) &&
                @info "method ambiguities" filter(startswith("AMBIGUOUS"), lines)
        end
    end
end
