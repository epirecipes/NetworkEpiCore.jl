# Owner: WP6. isequivalent (DESIGN §B.3): same species, same typed reactions up to order, equal
# rates.

using NetworkEpiCore
using Random
const NEC = NetworkEpiCore

seir_direct() = ContactModel(:seir; contacts = [Contact(:S, :I, :E, :τ)],
                             transitions = [NodeTransition(:E, :I, :σ), NodeTransition(:I, :R, :γ)])

@testset "isequivalent" begin
    @test isequivalent(seir_direct(), seir_model())
    @test isequivalent(sir_model(), sir_model(), sir_model())
    @test !isequivalent(sir_model(), seir_model())
    # order-insensitive: reactions and species in any order, any reaction names
    seair = seair_model()
    rng = Random.Xoshiro(1)
    for _ in 1:5
        shuffled = ContactModel(:other; contacts = shuffle(rng, contacts(seair)),
                                transitions = shuffle(rng, node_transitions(seair)),
                                species = shuffle(rng, species_names(seair)))
        @test isequivalent(seair, shuffled)
        @test isequivalent(shuffled, seair)
    end
    renamed = ContactModel(:x; contacts = [Contact(:S, :I, :I, :τ; name = :infect)],
                           transitions = [NodeTransition(:I, :R, :γ; name = :recover)])
    @test isequivalent(renamed, sir_model())
    # rates are compared as functions of the parameters
    a = ContactModel(:a; contacts = [Contact(:S, :I, :E, :τ)],
                     transitions = [NodeTransition(:E, :I, :(p * σ)),
                                    NodeTransition(:E, :R, :((1 - p) * σ)),
                                    NodeTransition(:I, :R, :γ)])
    b = ContactModel(:b; contacts = [Contact(:S, :I, :E, :τ)],
                     transitions = [NodeTransition(:E, :I, :(σ * p)),
                                    NodeTransition(:E, :R, :(σ - p * σ)),
                                    NodeTransition(:I, :R, :γ)])
    @test isequivalent(a, b)
    c = ContactModel(:c; contacts = [Contact(:S, :I, :E, :τ)],
                     transitions = [NodeTransition(:E, :I, :(p * σ)),
                                    NodeTransition(:E, :R, :((1 - p) * γ)),
                                    NodeTransition(:I, :R, :γ)])
    @test !isequivalent(a, c)
    @test isequivalent(sir_model(τ = 0.5, γ = 0.25), sir_model(τ = 1 / 2, γ = 0.5 / 2))
    @test !isequivalent(sir_model(τ = 0.5, γ = 0.25), sir_model(τ = 0.5, γ = 0.26))
    @test !isequivalent(sir_model(), sir_model(τ = :β))
    @test isequivalent(sir_model(τ = :(2τ)), sir_model(τ = :(τ + τ)))
    # the susceptible set, the convention and the layers matter
    @test !isequivalent(sir_model(),
                        ContactModel(:x; contacts = contacts(sir_model()),
                                     transitions = node_transitions(sir_model()),
                                     susceptible = [:S, :R]))
    @test !isequivalent(sir_model(),
                        ContactModel(:x; contacts = contacts(sir_model()),
                                     transitions = node_transitions(sir_model()),
                                     convention = FrequencyDependent()))
    @test !isequivalent(sir_model(),
                        ContactModel(:x; contacts = [Contact(:S, :I, :I, :τ; layer = :home)],
                                     transitions = node_transitions(sir_model())))
    # an extra isolated species makes a different model
    @test !isequivalent(sir_model(),
                        ContactModel(:x; contacts = contacts(sir_model()),
                                     transitions = node_transitions(sir_model()),
                                     species = [:S, :I, :R, :V]))
    # time-dependent rates are probed in t as well
    @test isequivalent(sir_model(τ = :(τ0 * exp(-a * t))), sir_model(τ = :(exp(-a * t) * τ0)))
    @test !isequivalent(sir_model(τ = :(τ0 * exp(-a * t))), sir_model(τ = :(τ0 * exp(-a))))
    # a merged duplicate equals the summed rate
    @test isequivalent(ContactModel(:m; contacts = [Contact(:S, :I, :I, :τ1), Contact(:S, :I, :I, :τ2)],
                                    merge_duplicates = true),
                       ContactModel(:n; contacts = [Contact(:S, :I, :I, :(τ2 + τ1))]))
end

# §J.3: a rate comparison decides equality only on evidence (WP10fix request to the NEC steward).
# Before, t and the parameters were drawn from (0.2, 0.8), so a term switched on outside that box
# (ν·max(t − 1, 0)) was never seen and isequivalent returned true.
using Symbolics      # for the extension's path below (a top-level statement: world age)

@testset "isequivalent: the evidence rule (§J.3)" begin
    # the core fallback (used without the Symbolics extension), called directly
    pv(x, y) = NEC._probe_rates_verdict(x, y).verdict
    @test pv(:γ, :(γ + ν * max(t - 1, 0))) === :different          # t probed up to 1000
    @test pv(:γ, :(γ + ν * max(τ - 2, 0))) === :undecided          # 0 on the box, not elsewhere
    @test pv(:(max(τ, 0)), :τ) === :undecided                      # min/max: no evidence
    @test pv(:((1 - p) * σ), :(σ - p * σ)) === :equal              # analytic identity
    @test pv(:(σ - σ * p - σ * (1 - p)), 0.0) === :equal           # float cancellation, relative
    @test pv(:(exp(-1000 * τ)), 0.0) === :different                # a small term is still a term
    @test pv(:(τ0 * exp(-a * t)), :(exp(-a * t) * τ0)) === :equal
    @test pv(:(log(τ - 5)), :(log(τ - 5) + 0)) === :undecided      # no probe can be evaluated
    @test pv(:(log(τ - 0.5)), :(log(2τ - 1) - log(2))) === :equal  # the probes inside the domain
    # with the Symbolics extension, isequivalent uses its rule (vector_fields_equal's)
    @test Base.get_extension(NEC, :NetworkEpiCoreSymbolicsExt) !== nothing
    γs, νs = as_parameter.((:γ, :ν))
    tv = Symbolics.variable(:t)
    # the reviewer's probe (scratchpad/wp10fix3/equiv_probe.jl): true before the fix
    @test !isequivalent(sir_model(; γ = γs), sir_model(; γ = γs + νs * max(tv - 1, 0)))
    @test !isequivalent(sir_model(; γ = :γ), sir_model(; γ = :(γ + ν * max(t - 1, 0))))
    @test !NEC._rates_equal(:γ, :(γ + ν * max(t - 1, 0)))
    # undecided is an error that says why, never false (and never true)
    err = try
        isequivalent(sir_model(; γ = :(max(γ, 0))), sir_model(; γ = :γ))
        nothing
    catch e
        e
    end
    @test err isa ArgumentError
    @test occursin("cannot decide whether the rates `max(γ, 0)` and `γ`", err.msg) &&
          occursin("the answer is unknown, not false", err.msg) && occursin("max", err.msg)
    @test_throws ArgumentError isequivalent(sir_model(; γ = :γ),
                                            sir_model(; γ = :(γ + ν * max(τ - 2, 0))))
    @test_throws ArgumentError NEC._rates_equal(:(max(γ, 0)), :γ)
    # a decidable difference elsewhere makes the answer false even when a rate pair is undecided
    @test !isequivalent(sir_model(; τ = :τ, γ = :(max(γ, 0))), sir_model(; τ = :β, γ = :γ))
    # the old tests hold on this path too: identities, Symbol against symbolic, time
    @test isequivalent(sir_model(τ = :(2τ)), sir_model(τ = :(τ + τ)))
    @test isequivalent(sir_model(), sir_model(; τ = as_parameter(:τ)))
    @test isequivalent(sir_model(τ = :(τ0 * exp(-a * t))), sir_model(τ = :(exp(-a * t) * τ0)))
    @test !isequivalent(sir_model(τ = :(τ0 * exp(-a * t))), sir_model(τ = :(τ0 * exp(-a))))
    @test isequivalent(sir_model(τ = :(log(τ - 0.5))), sir_model(τ = :(log(-0.5 + τ))))
end
