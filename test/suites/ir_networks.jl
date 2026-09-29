# Owner: WP6. Network-dependent parts of the IR (DESIGN §B.2, §B.6): admissibility on typed,
# layered and explicit networks, and the rate conventions (per_contact_rates).

using NetworkEpiCore
import Graphs
const NEC = NetworkEpiCore

stratified_sir(strata::Vector{Symbol}) = ContactModel(Symbol(:sir_, join(strata));
    contacts = [Contact(Symbol(:S_, a), Symbol(:I_, b), Symbol(:I_, a), :τ) for a in strata for b in strata],
    transitions = [NodeTransition(Symbol(:I_, a), Symbol(:R_, a), :γ) for a in strata],
    labels = Dict(Symbol(X, :_, a) => SpeciesLabel(X; stratum = a) for X in (:S, :I, :R) for a in strata))

layered_sir() = ContactModel(:sir_mpx; contacts = [Contact(:S, :I, :I, :τh; layer = :home),
                                                   Contact(:S, :I, :I, :τc; layer = :comm)],
                             transitions = [NodeTransition(:I, :R, :γ)])

refused(cm, net) = Set(b for (b, ok) in admissibility(cm, net).backends if !ok)
vtypes(cm, net) = [v.type for v in admissibility(cm, net).violations]

@testset "one susceptible class per node type" begin
    ab = stratified_sir([:a, :b])
    config = ConfigurationNetwork(RegularDegree(6))
    sbm = sbm_network([:a, :b], [0.5, 0.5]; mean_contacts = [4.0 2.0; 2.0 4.0])
    unstr = unstructured(config, [:a, :b], [0.5, 0.5])
    @test isempty(refused(ab, nothing))                      # distinct strata, no network yet
    @test isempty(refused(ab, sbm)) && isempty(refused(ab, unstr))
    @test refused(ab, config) == Set([:edge_based, :s_anchored])   # an untyped network
    @test vtypes(ab, config) == [:multiple_sus]
    # the strata must be the node types of the network
    ac = sbm_network([:a, :c], [0.5, 0.5]; mean_contacts = [4.0 2.0; 2.0 4.0])
    rep = admissibility(ab, ac)
    @test !rep.backends[:edge_based] && rep.backends[:pairwise]
    @test [v.type for v in rep.violations] == [:multiple_sus, :multiple_sus]
    @test occursin("stratum b, which is not a node type", rep.violations[1].reason)
    @test occursin("no susceptible class is assigned to the node type c", rep.violations[2].reason)
    # an unstratified model on a typed network
    rep2 = admissibility(sir_model(), sbm)
    @test !rep2.backends[:edge_based]
    @test occursin("S has no stratum", first(rep2.violations).reason)
    # two susceptible classes in one stratum
    twice = ContactModel(:twice; contacts = [Contact(:S1, :I, :I, :τ), Contact(:S2, :I, :I, :τ)],
                         transitions = [NodeTransition(:I, :R, :γ)],
                         labels = Dict(:S1 => SpeciesLabel(:S; stratum = :a),
                                       :S2 => SpeciesLabel(:S; stratum = :a)))
    @test !is_admissible(twice, :edge_based)
    @test !is_admissible(twice, :edge_based; network = sbm)
    @test occursin("a second susceptible class of the node type a",
                   first(admissibility(twice, sbm).violations).reason)
    # the plain models on every untyped descriptor
    for net in (WellMixed(5.0), config, ConfigurationNetwork(PoissonDegree(5.0)),
                ClusteredNetwork(RegularDegree(2), RegularDegree(2)),
                DynamicNetwork(ConfigurationNetwork(RegularDegree(6)), NeighbourExchange(1.0)))
        @test isempty(refused(sir_model(), net)) && isempty(refused(seair_model(), net))
        @test refused(sis_model(), net) == Set([:edge_based, :s_anchored])
    end
end

@testset "layers and explicit graphs" begin
    lay = layered_sir()
    mpx = MultiplexNetwork(:home => ConfigurationNetwork(RegularDegree(3)),
                           :comm => ConfigurationNetwork(PoissonDegree(5.0)))
    @test isempty(refused(lay, mpx)) && isempty(refused(lay, nothing))
    @test refused(lay, ConfigurationNetwork(RegularDegree(3))) ==
          Set([:edge_based, :s_anchored, :pairwise, :individual, :pair, :stochastic])
    @test vtypes(lay, ConfigurationNetwork(RegularDegree(3))) == [:layer, :layer]
    school = MultiplexNetwork(:home => RegularDegree(3), :school => PoissonDegree(4.0))
    rep = admissibility(lay, school)
    @test [v.reaction for v in rep.violations] == [:S_I_to_I_comm]
    @test rep.backends[:mass_action] && !rep.backends[:stochastic]
    # a contact on :all is fine on a multiplex network
    @test isempty(refused(sir_model(), mpx))
    # an explicit graph is not an edge-based object
    g = ExplicitGraph(Graphs.path_graph(5))
    @test refused(sir_model(), g) == Set([:edge_based])
    err = try
        require_admissible(sir_model(), :edge_based; network = g)
    catch e
        e
    end
    flat = replace(sprint(showerror, err), r"\s+" => " ")
    @test startswith(flat, "AdmissibilityError: edge_based(:sir, ExplicitGraph(g)): Edge-based " *
                           "models need a random-graph ensemble, not the fixed graph of an ExplicitGraph.")
    @test occursin("Try: ConfigurationNetwork(EmpiricalDegree(g)) for the annealed approximation, " *
                   "or NodeBasedModels.node_based(model, net; level = :individual).", flat)
    @test occursin("Back ends that accept this model: node_based (s_anchored, pairwise, individual, " *
                   "pair, motif, neighbourhood), simulate, mass_action.", flat)
end
# Network-dependent conventions (§B.6); the descriptors come from networks/descriptors.jl.
@testset "rate conventions on networks" begin
    fd = ContactModel(:seir; contacts = [Contact(:S, :I, :E, :β)],
                      transitions = [NodeTransition(:E, :I, :σ), NodeTransition(:I, :R, :γ)],
                      convention = FrequencyDependent())
    @test per_contact_rates(fd, WellMixed(5.0)) == Any[:(β / 5.0)]
    @test rate_value(only(per_contact_rates(fd, ConfigurationNetwork(RegularDegree(6)))),
                     Dict(:β => 0.6)) ≈ 0.1
    @test rate_value(only(per_contact_rates(fd, ConfigurationNetwork(PoissonDegree(4.0)))),
                     Dict(:β => 1.0)) ≈ 0.25
    dd = ContactModel(:x; contacts = [Contact(:S, :I, :I, :β)], convention = DensityDependent(:N))
    @test rate_value(only(per_contact_rates(dd, ConfigurationNetwork(RegularDegree(4)))),
                     Dict(:β => 0.001, :N => 1000.0)) ≈ 0.25
    pc = ContactModel(:x; contacts = [Contact(:S, :I, :I, :τ)])
    @test per_contact_rates(pc, ConfigurationNetwork(RegularDegree(4))) == Any[:τ]
    # multiplex: a layered contact uses its layer's mean degree, :all the total
    mpx = MultiplexNetwork(:home => ConfigurationNetwork(RegularDegree(3)),
                           :comm => ConfigurationNetwork(PoissonDegree(5.0)))
    lay = ContactModel(:x; contacts = [Contact(:S, :I, :I, :βh; layer = :home),
                                       Contact(:S, :I, :I, :βc; layer = :comm),
                                       Contact(:S, :A, :I, :βa)],
                       convention = FrequencyDependent())
    τs = per_contact_rates(lay, mpx)
    p = Dict(:βh => 0.3, :βc => 0.5, :βa => 0.8)
    @test rate_value(τs[1], p) ≈ 0.1 && rate_value(τs[2], p) ≈ 0.1 && rate_value(τs[3], p) ≈ 0.1
    @test_throws ArgumentError per_contact_rates(lay, ConfigurationNetwork(RegularDegree(3)))
    bad = ContactModel(:x; contacts = [Contact(:S, :I, :I, :β; layer = :school)],
                       convention = FrequencyDependent())
    @test_throws ArgumentError per_contact_rates(bad, mpx)
end

@testset "rate conventions on typed networks" begin
    ab = stratified_sir([:a, :b])
    sbm = sbm_network([:a, :b], [0.5, 0.5]; mean_contacts = [4.0 2.0; 2.0 4.0])
    @test per_contact_rates(ab, sbm) == fill(:τ, 4)                  # PerContact: as written
    fd = ContactModel(:x; contacts = contacts(ab), transitions = node_transitions(ab),
                      labels = species_labels(ab), convention = FrequencyDependent())
    err = try
        per_contact_rates(fd, sbm)
    catch e
        e
    end
    @test err isa ArgumentError && occursin("per-contact rates τ explicitly", err.msg)
    # an unstratified frequency-dependent model on a typed network uses the total mean degree
    fsir = ContactModel(:fsir; contacts = [Contact(:S, :I, :I, :β)], convention = FrequencyDependent())
    @test rate_value(only(per_contact_rates(fsir, sbm)), Dict(:β => 1.2)) ≈ 1.2 / 6.0
end
