# Build the NetworkEpiCore documentation:
#
#     julia --project=docs docs/make.jl
#
# The docs environment needs Documenter and must develop NetworkEpiCore by path (docs/Project.toml
# with [sources] NetworkEpiCore = {path = ".."}). Set DOCS_BUILD=<dir> to build somewhere other
# than docs/build.
using Documenter
using NetworkEpiCore

const DOCS = @__DIR__
const ROOT = dirname(DOCS)
const REMOTE = Documenter.Remotes.GitHub("epirecipes", "NetworkEpiCore.jl")
const BUILD = get(ENV, "DOCS_BUILD", joinpath(DOCS, "build"))

DocMeta.setdocmeta!(NetworkEpiCore, :DocTestSetup, :(using NetworkEpiCore); recursive = true)

makedocs(;
    source    = joinpath(DOCS, "src"),
    build     = BUILD,
    sitename  = "NetworkEpiCore.jl",
    modules   = [NetworkEpiCore],
    authors   = "Simon Frost",
    # The package directory need not be a git checkout: name its remote explicitly (source links
    # point at the main branch).
    remotes   = Dict(ROOT => (REMOTE, "main")),
    format    = Documenter.HTML(;
        canonical           = "https://epirecip.es/NetworkEpiCore.jl/",
        edit_link           = nothing,
        repolink            = "https://github.com/epirecipes/NetworkEpiCore.jl",
        assets              = String[],
        prettyurls          = false,
        size_threshold      = nothing,
        size_threshold_warn = nothing,
    ),
    pages     = [
        "Home"                             => "index.md",
        "Morphisms"                        => "morphisms.md",
        "Shared scenarios and validation"  => "scenarios.md",
        "Lean library"                     => "lean.md",
        "API"                              => "api.md",
    ],
    checkdocs = :exports,
    warnonly  = [:missing_docs, :cross_references],
)
