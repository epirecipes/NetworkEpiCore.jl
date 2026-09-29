# Owner: WP6. The canned models of DESIGN §B.3 and their deprecated keywords (§A.7).

using NetworkEpiCore
const NEC = NetworkEpiCore

shape(cm) = (species_names(cm),
             [(c.recipient, c.infector, c.product, c.rate) for c in contacts(cm)],
             [(t.from, t.to, t.rate) for t in node_transitions(cm)])

@testset "canned models" begin
    @test shape(sir_model()) == ([:S, :I, :R], [(:S, :I, :I, :τ)], [(:I, :R, :γ)])
    @test shape(seir_model()) ==
          ([:S, :E, :I, :R], [(:S, :I, :E, :τ)], [(:E, :I, :σ), (:I, :R, :γ)])
    @test shape(sis_model()) == ([:S, :I], [(:S, :I, :I, :τ)], [(:I, :S, :γ)])
    @test shape(sirs_model()) ==
          ([:S, :I, :R], [(:S, :I, :I, :τ)], [(:I, :R, :γ), (:R, :S, :ε)])
    @test shape(seair_model()) ==
          ([:S, :E, :I, :A, :R], [(:S, :I, :E, :τI), (:S, :A, :E, :τA)],
           [(:E, :I, :(p * σ)), (:E, :A, :((1 - p) * σ)), (:I, :R, :γ), (:A, :R, :γ)])
    @test shape(twostrain_model()) ==
          ([:S, :I1, :I2, :R], [(:S, :I1, :I1, :τ1), (:S, :I2, :I2, :τ2)],
           [(:I1, :R, :γ), (:I2, :R, :γ)])
    @test shape(sirv_model()) ==
          ([:S, :I, :R, :V], [(:S, :I, :I, :τ)], [(:I, :R, :γ), (:S, :V, :ν)])
    for (f, name) in ((sir_model, :sir), (seir_model, :seir), (sis_model, :sis),
                      (sirs_model, :sirs), (seair_model, :seair), (twostrain_model, :twostrain),
                      (sirv_model, :sirv))
        cm = f()
        @test nameof(cm) === name
        @test provenance(cm).source === :factory
        @test rate_convention(cm) == PerContact()
        @test susceptible_species(cm) == [:S]
    end
    # entry states (the default seeded compartment is the unique entry, §E.2)
    @test entry_species(sir_model()) == [:I]
    @test entry_species(seir_model()) == [:E]
    @test entry_species(seair_model()) == [:E]
    @test entry_species(twostrain_model()) == [:I1, :I2]
    @test infectious_species(seair_model()) == [:I, :A]
    # rates may be numbers, Symbols or Exprs
    m = sir_model(τ = 0.5, γ = :(2γ0))
    @test shape(m)[2] == [(:S, :I, :I, 0.5)] && shape(m)[3] == [(:I, :R, :(2γ0))]
    @test rate_parameters(m) == Any[:γ0]
    num = seair_model(τI = 1 / 6, τA = 1 / 12, σ = 0.2, p = 0.6, γ = 0.25)
    @test [t.rate for t in node_transitions(num)] ≈ [0.6 * 0.2, 0.4 * 0.2, 0.25, 0.25]
    @test rate_parameters(seair_model()) == Any[:τI, :τA, :p, :σ, :γ]
    # species names of sir_model can be changed
    @test species_names(sir_model(S = :U, I = :J, R = :Q)) == [:U, :J, :Q]
    # the typings of §B.2
    @test typing(sir_model()).theory === :T_EB && typing(sirv_model()).theory === :T_EB
    @test typing(sis_model()).theory === :T_net && typing(sirs_model()).theory === :T_net
    @test last.(typing(sirv_model()).reaction_types) == [:contact, :progress, :exit]
end

@testset "deprecated keywords (β ⇒ τ, susceptible ⇒ S)" begin
    for f in (sir_model, seir_model, sis_model, sirs_model)
        old = @test_deprecated f(β = 0.3)
        @test isequivalent(old, f(τ = 0.3))
        @test_throws ArgumentError f(β = 0.3, τ = 0.2)
        renamed = @test_deprecated f(susceptible = :U)
        @test susceptible_species(renamed) == [:U]
    end
    @test_throws ArgumentError sir_model(S = :V, susceptible = :U)
end

@testset "layered_sir_model (steward-2, design §A.6)" begin
    m = layered_sir_model([:home, :comm], [:(3c), :c])
    @test m isa ContactModel && m.name === :sir_layered
    @test [c.layer for c in contacts(m)] == [:home, :comm]
    @test [c.rate for c in contacts(m)] == [:(3c), :c]
    @test typing(m).theory === :T_EB
    @test isequivalent(m, scenario(:sir_mpx).model)
    net = MultiplexNetwork(:home => RegularDegree(3), :comm => PoissonDegree(5))
    @test is_admissible(m, :edge_based; network = net)
    @test !is_admissible(m, :edge_based; network = ConfigurationNetwork(PoissonDegree(5)))
    @test layered_sir_model([:a], [0.1]; γ = 0.2, name = :one).name === :one
    @test_throws ArgumentError layered_sir_model(Symbol[], [])
    @test_throws ArgumentError layered_sir_model([:a, :b], [0.1])
    @test_throws ArgumentError layered_sir_model([:a, :a], [0.1, 0.2])
    @test_throws ArgumentError layered_sir_model([:all], [0.1])
end
