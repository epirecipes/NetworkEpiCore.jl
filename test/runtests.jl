# Owner: WP5 (DESIGN_NetworkEpiCore.md §G.1 "Tests").
#
# Runs every test/suites/*.jl in sorted order, each in its own module so that suites cannot
# leak names into one another. Each work package owns its suite files; nobody edits this file.
#
# Selecting suites (comma-separated basenames, with or without `.jl`):
#
#     NEC_TEST_SUITES=ir_types,networks_degrees julia --project=. -e 'using Pkg; Pkg.test()'
#     julia --project=. -e 'using Pkg; Pkg.test(test_args = ["integration"])'
#
# ENV["NEC_TEST_SUITES"] takes precedence over test arguments. An unknown name is an error.

using Test

const SUITE_DIR = joinpath(@__DIR__, "suites")

suite_name(file::AbstractString) = first(splitext(basename(file)))

function available_suites()
    isdir(SUITE_DIR) || return String[]
    return sort!([f for f in readdir(SUITE_DIR)
                  if endswith(f, ".jl") && isfile(joinpath(SUITE_DIR, f))])
end

function requested_suites()
    spec = strip(get(ENV, "NEC_TEST_SUITES", ""))
    names = isempty(spec) ? String.(ARGS) : String.(split(spec, ','))
    return String[suite_name(strip(n)) for n in names if !isempty(strip(n))]
end

function selected_suites()
    files = available_suites()
    wanted = requested_suites()
    isempty(wanted) && return files
    known = Dict(suite_name(f) => f for f in files)
    unknown = [w for w in wanted if !haskey(known, w)]
    isempty(unknown) || error("NEC_TEST_SUITES names unknown suite(s) $(join(unknown, ", ")); " *
                              "available: $(join(sort!(collect(keys(known))), ", "))")
    return [f for f in files if suite_name(f) in wanted]   # keep the sorted order
end

# A module name for a suite file (suite basenames may contain characters invalid in identifiers).
suite_module(file) = Symbol("NECSuite_", replace(suite_name(file), r"[^A-Za-z0-9_]" => "_"))

const SELECTED = selected_suites()
isempty(requested_suites()) ||
    @info "Running selected NetworkEpiCore test suites" suites = suite_name.(SELECTED)

@testset "NetworkEpiCore" begin
    for file in SELECTED
        path = joinpath(SUITE_DIR, file)
        t0 = time()
        @testset "$(suite_name(file))" begin
            # A fresh top-level module per suite: `include` evaluates each top-level statement of
            # the suite in the latest world, so a suite may load packages and then use them.
            Core.eval(Main, Expr(:module, true, suite_module(file),
                                 Expr(:block, :(using Test), :(include($path)))))
        end
        @info "Suite finished" suite = suite_name(file) seconds = round(time() - t0; digits = 1)
    end
end
