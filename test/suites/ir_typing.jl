# Owner: WP6. Typing over T_net ⊃ T_EB and back-end admissibility (DESIGN §B.2) for a corpus of
# models, with the error texts of §B.7. Network-dependent verdicts are in ir_networks.jl.

using NetworkEpiCore
const NEC = NetworkEpiCore

C(s, J, X, r; kw...) = Contact(s, J, X, r; kw...)
T(X, Y, r; kw...) = NodeTransition(X, Y, r; kw...)
M(name; kw...) = ContactModel(name; kw...)

const EB_NO = Set([:edge_based, :s_anchored])
const NONE = Set{Symbol}()

# (model, Σ, reaction types in IR order, theory, back ends refused without a network,
#  violation types in order)
corpus = [
    # 1-4: the classical models
    (:sir, sir_model(), [:S], [:contact, :progress], :T_EB, NONE, Symbol[]),
    (:seir, seir_model(), [:S], [:contact, :progress, :progress], :T_EB, NONE, Symbol[]),
    (:sis, sis_model(), [:S], [:contact, :resus], :T_net, EB_NO, [:resus]),
    (:sirs, sirs_model(), [:S], [:contact, :progress, :resus], :T_net, EB_NO, [:resus]),
    # 5-6: branching after latency with two infectors; two strains
    (:seair, seair_model(), [:S], [:contact, :contact, :progress, :progress, :progress, :progress],
     :T_EB, NONE, Symbol[]),
    (:twostrain, twostrain_model(), [:S], [:contact, :contact, :progress, :progress], :T_EB, NONE,
     Symbol[]),
    # 7: partial cross-immunity: R1 is a second susceptible class produced by I1 → R1
    (:partial, M(:partial; contacts = [C(:S, :I1, :I1, :τ1), C(:S, :I2, :I2, :τ2),
                                       C(:R1, :I2, :I12, :(ε * τ2))],
                 transitions = [T(:I1, :R1, :γ), T(:I2, :R2, :γ), T(:I12, :R, :γ)]),
     [:S, :R1], [:contact, :contact, :contact, :resus, :progress, :progress], :T_net, EB_NO,
     [:resus, :multiple_sus]),
    # 8-9: exits from the susceptible class (vaccination, importation)
    (:sirv, sirv_model(), [:S], [:contact, :progress, :exit], :T_EB, NONE, Symbol[]),
    (:import, M(:import; contacts = [C(:S, :I, :E, :τ)],
                transitions = [T(:E, :I, :σ), T(:I, :R, :γ), T(:S, :E, :η)]),
     [:S], [:contact, :progress, :progress, :exit], :T_EB, NONE, Symbol[]),
    # 10: contact tracing (a contact whose product is not infectious)
    (:trace, M(:trace; contacts = [C(:S, :I, :I, :τ), C(:S, :D, :Q, :α)],
               transitions = [T(:I, :D, :γ), T(:D, :R, :δ)]),
     [:S], [:contact, :contact, :progress, :progress], :T_EB, NONE, Symbol[]),
    # 11: S-catalysed recovery (a contact that changes a non-susceptible node)
    (:scat, M(:scat; contacts = [C(:S, :I, :I, :τ), C(:I, :S, :R, :δ)],
              transitions = [T(:I, :R, :γ)]),
     [:S], [:contact, :node_contact, :progress], :T_net, EB_NO, [:node_contact]),
    # 12-13: reinfection counting: SIS gains several susceptible classes and resus arrows;
    # SIR gains no reinfection states (unreachable refined species are dropped)
    (:sis_L2, with_reinfection_counting(sis_model(), 2), [:S_0, :S_1, :S_2],
     vcat(fill(:contact, 6), fill(:resus, 2)), :T_net, EB_NO,
     [:resus, :resus, :multiple_sus, :multiple_sus]),
    (:sir_L3, with_reinfection_counting(sir_model(), 3), [:S_0], [:contact, :progress], :T_EB,
     NONE, Symbol[]),
    # 14: stratified SIR (two strata, one susceptible class each): admissible without a network
    (:sir_ab, M(:sir_ab; contacts = [C(:S_a, :I_a, :I_a, :τ), C(:S_a, :I_b, :I_a, :τ),
                                     C(:S_b, :I_a, :I_b, :τ), C(:S_b, :I_b, :I_b, :τ)],
                transitions = [T(:I_a, :R_a, :γ), T(:I_b, :R_b, :γ)],
                labels = Dict(:S_a => SpeciesLabel(:S; stratum = :a),
                              :S_b => SpeciesLabel(:S; stratum = :b),
                              :I_a => SpeciesLabel(:I; stratum = :a),
                              :I_b => SpeciesLabel(:I; stratum = :b),
                              :R_a => SpeciesLabel(:R; stratum = :a),
                              :R_b => SpeciesLabel(:R; stratum = :b))),
     [:S_a, :S_b], [:contact, :contact, :contact, :contact, :progress, :progress], :T_EB, NONE,
     Symbol[]),
    # 15: heterogeneous susceptibility (two unstratified susceptible classes): T_EB, but EB needs
    # one susceptible class per node type
    (:hetsus, M(:hetsus; contacts = [C(:S1, :I, :I, :τ1), C(:S2, :I, :I, :τ2)],
                transitions = [T(:I, :R, :γ)]),
     [:S1, :S2], [:contact, :contact, :progress], :T_EB, EB_NO, [:multiple_sus]),
    # 16: a move between susceptible classes
    (:susmove, M(:susmove; contacts = [C(:S1, :I, :I, :τ), C(:S2, :I, :I, :τ)],
                 transitions = [T(:I, :R, :γ), T(:S1, :S2, :ω)]),
     [:S1, :S2], [:contact, :contact, :progress, :sus_move], :T_net, EB_NO,
     [:sus_move, :multiple_sus]),
    # 17: a contact into a susceptible class (the user fixes Σ = {S1, S2})
    (:suscontact, M(:suscontact; contacts = [C(:S1, :I, :S2, :κ), C(:S2, :I, :I, :τ)],
                    transitions = [T(:I, :R, :γ)], susceptible = [:S1, :S2]),
     [:S1, :S2], [:sus_contact, :contact, :progress], :T_net, EB_NO,
     [:sus_contact, :multiple_sus]),
    # 18: a susceptible infector
    (:susinfector, M(:susinfector; contacts = [C(:S, :I, :I, :τ), C(:U, :S, :E, :κ)],
                     transitions = [T(:E, :I, :σ), T(:I, :R, :γ)]),
     [:S, :U], [:contact, :sus_contact, :progress, :progress], :T_net, EB_NO,
     [:sus_contact, :multiple_sus]),
    # 19-20: removals and a death of susceptibles (S → ∅ is an exit)
    (:sird, M(:sird; contacts = [C(:S, :I, :I, :τ)], transitions = [T(:I, nothing, :μ)]),
     [:S], [:contact, :remove], :T_EB, NONE, Symbol[]),
    (:sdeath, M(:sdeath; contacts = [C(:S, :I, :I, :τ)],
                transitions = [T(:I, :R, :γ), T(:S, nothing, :μ)]),
     [:S], [:contact, :progress, :exit], :T_EB, NONE, Symbol[]),
    # 21: a time-dependent rate: NetworkOutbreaks refuses it (interventions instead)
    (:sir_t, M(:sir_t; contacts = [C(:S, :I, :I, :(τ0 * exp(-a * t)))],
               transitions = [T(:I, :R, :γ)]),
     [:S], [:contact, :progress], :T_EB, Set([:stochastic]), [:time_dependent]),
    # 22: bypass after latency (E14: branching progression)
    (:bypass, M(:bypass; contacts = [C(:S, :I, :E, :τ)],
                transitions = [T(:E, :I, :(p * σ)), T(:E, :R, :((1 - p) * σ)), T(:I, :R, :γ)]),
     [:S], [:contact, :progress, :progress, :progress], :T_EB, NONE, Symbol[]),
    # 23-24: branching at infection and infector-dependent entry (E25)
    (:branch_inf, M(:branch_inf; contacts = [C(:S, :I, :E, :τ1), C(:S, :I, :A, :τ2)],
                    transitions = [T(:E, :I, :σ), T(:A, :R, :γA), T(:I, :R, :γ)]),
     [:S], [:contact, :contact, :progress, :progress, :progress], :T_EB, NONE, Symbol[]),
    (:entry_by_inf, M(:entry_by_inf; contacts = [C(:S, :I, :E, :τI), C(:S, :A, :F, :τA)],
                      transitions = [T(:E, :I, :σ), T(:F, :A, :σ), T(:I, :R, :γ),
                                     T(:A, :R, :γ)]),
     [:S], [:contact, :contact, :progress, :progress, :progress, :progress], :T_EB, NONE,
     Symbol[]),
    # 25: Erlang-staged SIR
    (:sir_erl3, erlang_stages(sir_model(), :I, 3), [:S],
     [:contact, :contact, :contact, :progress, :progress, :progress], :T_EB, NONE, Symbol[]),
    # 26: frequency-dependent SEIR
    (:seir_fd, M(:seir_fd; contacts = [C(:S, :I, :E, :β)],
                 transitions = [T(:E, :I, :σ), T(:I, :R, :γ)], convention = FrequencyDependent()),
     [:S], [:contact, :progress, :progress], :T_EB, NONE, Symbol[]),
    # 27: layer-labelled contacts (admissible; the network is checked in ir_networks.jl)
    (:sir_mpx, M(:sir_mpx; contacts = [C(:S, :I, :I, :τh; layer = :home),
                                       C(:S, :I, :I, :τc; layer = :comm)],
                 transitions = [T(:I, :R, :γ)]),
     [:S], [:contact, :contact, :progress], :T_EB, NONE, Symbol[]),
    # 28: SIRS with vaccination and waning of vaccine immunity
    (:sirvs, M(:sirvs; contacts = [C(:S, :I, :I, :τ)],
               transitions = [T(:I, :R, :γ), T(:S, :V, :ν), T(:V, :S, :ω)]),
     [:S], [:contact, :progress, :exit, :resus], :T_net, EB_NO, [:resus]),
    # 29: SEIRS
    (:seirs, M(:seirs; contacts = [C(:S, :I, :E, :τ)],
               transitions = [T(:E, :I, :σ), T(:I, :R, :γ), T(:R, :S, :ε)]),
     [:S], [:contact, :progress, :progress, :resus], :T_net, EB_NO, [:resus]),
    # 30: no contacts at all: no susceptible class
    (:nocontact, M(:nocontact; transitions = [T(:E, :I, :σ), T(:I, :R, :γ)]),
     Symbol[], [:progress, :progress], :T_EB, EB_NO, [:no_susceptible]),
]

@testset "typing corpus ($(length(corpus)) models)" begin
    @test length(corpus) >= 25
    for (id, cm, Σ, types, theory, refused, vtypes) in corpus
        @testset "$id" begin
            tp = typing(cm)
            @test susceptible_species(cm) == Σ
            @test all(tp.species_types[x] === (x in Σ ? :sus : :node) for x in species_names(cm))
            @test last.(tp.reaction_types) == types
            @test first.(tp.reaction_types) ==
                  [r.name for r in vcat(contacts(cm), node_transitions(cm))]
            @test tp.theory === theory
            @test all(v -> v.type in NEC.REACTION_TYPES, tp.violations)
            rep = admissibility(cm)
            @test Set(b for b in NEC.BACKENDS if !rep.backends[b]) == refused
            @test [v.type for v in rep.violations] == vtypes
            for b in NEC.BACKENDS
                @test is_admissible(cm, b) == !(b in refused)
                if b in refused
                    @test_throws AdmissibilityError require_admissible(cm, b)
                else
                    @test require_admissible(cm, b) === nothing
                end
            end
            # mass action and the node-based back ends are total on T_net
            @test rep.backends[:mass_action] && rep.backends[:pairwise]
            @test rep.backends[:individual] && rep.backends[:pair]
        end
    end
end

@testset "T_EB and the transition types" begin
    @test NEC.T_EB_TYPES == (:contact, :exit, :progress, :remove)
    @test issubset(NEC.T_EB_TYPES, NEC.REACTION_TYPES) && length(NEC.REACTION_TYPES) == 8
    @test NEC.BACKENDS == (:edge_based, :s_anchored, :pairwise, :individual, :pair, :stochastic,
                           :mass_action)
    @test_throws ArgumentError is_admissible(sir_model(), :pairwiseish)
    @test_throws ArgumentError require_admissible(sir_model(), :edge)
    @test_throws ArgumentError Violation(:r, :bogus, "x", "y")
    @test blocked_backends(Violation(:r, :resus, "x", "y")) == (:edge_based, :s_anchored)
    @test blocked_backends(Violation(:r, :time_dependent, "x", "y")) == (:stochastic,)
    @test blocked_backends(Violation(nothing, :explicit_graph, "x", "y")) == (:edge_based,)
    # typing depends only on Σ: overriding Σ changes the types
    cm = ContactModel(:x; contacts = [Contact(:S, :I, :I, :τ)], transitions = [NodeTransition(:I, :R, :γ)],
                      susceptible = [:S, :R])
    @test last.(typing(cm).reaction_types) == [:contact, :resus]
end

# §B.7, the error texts (tested verbatim). The first uses the network of the design example.
@testset "error texts (§B.7)" begin
    err = try
        require_admissible(sis_model(), :edge_based;
                           network = ConfigurationNetwork(RegularDegree(3)))
    catch e
        e
    end
    @test err isa AdmissibilityError
    @test sprint(showerror, err) == """
        AdmissibilityError: edge_based(:sis, ConfigurationNetwork(RegularDegree(3))):
          `γ, I --> S` (type resus: node → sus) produces the susceptible species S.
          The edge-based model is exact only when no reaction produces a susceptible class
          (Miller, Slim & Volz 2012, Part I). Back ends that accept this model: node_based
          (pairwise, individual, pair, motif, neighbourhood), simulate, mass_action.
          Try: NodeBasedModels.node_based(model, net; closure = KeelingClosure())."""
    @test err.backend === :edge_based && err.accepted == [:pairwise, :individual, :pair,
                                                           :stochastic, :mass_action]

    # partial immunity: one sentence joins the two reasons, then the same tail
    partial = corpus[findfirst(c -> c[1] === :partial, corpus)][2]
    err2 = try
        require_admissible(partial, :edge_based)
    catch e
        e
    end
    txt = sprint(showerror, err2)
    flat = replace(txt, r"\s+" => " ")
    @test startswith(txt, "AdmissibilityError: edge_based(:partial):\n  ")
    @test occursin("`ε*τ2, R1 + I2 --> I12 + I2`: R1 is a second susceptible class " *
                   "(multiple_sus) and is produced by `γ, I1 --> R1` (resus).", flat)
    @test occursin("The edge-based model is exact only when no reaction produces a susceptible " *
                   "class (Miller, Slim & Volz 2012, Part I). Back ends that accept this model: " *
                   "node_based (pairwise, individual, pair, motif, neighbourhood), simulate, " *
                   "mass_action. Try: NodeBasedModels.node_based(model, net; closure = " *
                   "KeelingClosure()).", flat)
    @test count("resus", flat) == 1                      # the resus reason is not repeated
    @test all(l -> textwidth(l) <= 82, split(txt, '\n')[2:end])

    # the lifted SIS of E19 (the old name-based guard missed it): both reasons, one sentence
    err3 = try
        require_admissible(with_reinfection_counting(sis_model(), 1), :edge_based)
    catch e
        e
    end
    flat3 = replace(sprint(showerror, err3), r"\s+" => " ")
    @test occursin("`τ, S_1 + I_1 --> 2I_1`: S_1 is a second susceptible class (multiple_sus) " *
                   "and is produced by `γ, I_1 --> S_1` (resus).", flat3)
    @test count("(resus)", flat3) == 1

    # other back ends and other reasons
    err4 = try
        require_admissible(M(:sir_t; contacts = [C(:S, :I, :I, :(τ0 * exp(-a * t)))],
                             transitions = [T(:I, :R, :γ)]), :stochastic)
    catch e
        e
    end
    flat4 = replace(sprint(showerror, err4), r"\s+" => " ")
    @test startswith(flat4, "AdmissibilityError: simulate(:sir_t): `τ0*exp(-a*t), S + I --> 2I` " *
                            "has a time-dependent rate")
    @test occursin("Back ends that accept this model: edge_based, node_based (s_anchored, " *
                   "pairwise, individual, pair, motif, neighbourhood), mass_action.", flat4)
    err5 = try
        require_admissible(corpus[findfirst(c -> c[1] === :scat, corpus)][2], :s_anchored)
    catch e
        e
    end
    flat5 = replace(sprint(showerror, err5), r"\s+" => " ")
    @test startswith(flat5, "AdmissibilityError: node_based(:scat; level = :s_anchored): " *
                            "`δ, I + S --> R + S` (type node_contact: node → node, infector sus) " *
                            "changes the state of the non-susceptible species I through a contact.")
    @test occursin("The S-anchored pairwise model is exact only when every contact converts a " *
                   "susceptible node", flat5)
    err6 = try
        require_admissible(corpus[findfirst(c -> c[1] === :hetsus, corpus)][2], :edge_based)
    catch e
        e
    end
    flat6 = replace(sprint(showerror, err6), r"\s+" => " ")
    @test occursin("`τ2, S2 + I --> 2I`: S2 is a second susceptible class (multiple_sus).", flat6)
    @test occursin("needs exactly one susceptible class per node type", flat6)
end

@testset "steward-2: the back-end suggestion for layer contacts, and the multiple_sus hints" begin
    layered = ContactModel(:home_only; contacts = [Contact(:S, :I, :I, :τ; layer = :home)],
                           transitions = [NodeTransition(:I, :R, :γ)])
    net = ConfigurationNetwork(PoissonDegree(5))
    msg = try
        require_admissible(layered, :edge_based; network = net); ""
    catch e
        replace(sprint(showerror, e), r"\s+" => " ")          # the message is word-wrapped
    end
    @test occursin("no layers", msg)
    @test !occursin("Back ends that accept this model: mass_action", msg)
    @test occursin("No network back end accepts a contact on a layer that the network does not have", msg)
    @test occursin("MultiplexNetwork", msg)
    # a failure that is not about layers still lists the back ends that accept the model
    msg2 = try
        require_admissible(sis_model(), :edge_based; network = net); ""
    catch e
        sprint(showerror, e)
    end
    @test occursin("Back ends that accept this model:", msg2)
    # several susceptible classes on an untyped network: the hint names heterogeneous
    # susceptibility (strata on the classes, unstructured(net, st)); on a degree-correlated
    # network it names the degree classes of MultitypeNetwork(net)
    two = ContactModel(:two_sus; contacts = [Contact(:S1, :I, :I, :τ1), Contact(:S2, :I, :I, :τ2)],
                       transitions = [NodeTransition(:I, :R, :γ)])
    v = only(v for v in admissibility(two, net).violations if v.type === :multiple_sus)
    @test occursin("heterogeneous susceptibility", v.suggestion) && occursin("unstructured(net, st)", v.suggestion)
    dc = degree_correlated(EmpiricalDegree(2 => 5 / 6, 10 => 1 / 6); r = 0.5)
    vd = only(v for v in admissibility(two, dc).violations if v.type === :multiple_sus)
    @test occursin("degree classes on MultitypeNetwork(net)", vd.suggestion)
end
