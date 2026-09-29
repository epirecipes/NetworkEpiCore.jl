# Owner: WP6. The IR types of DESIGN §B.1: reactions, labels, provenance, conventions, the
# validating ContactModel constructor, queries and printing.

using NetworkEpiCore
const NEC = NetworkEpiCore

@testset "Contact" begin
    c = Contact(:S, :I, :I, :τ)
    @test (c.recipient, c.infector, c.product, c.rate) == (:S, :I, :I, :τ)
    @test c.layer === :all
    @test c.name === :S_I_to_I
    @test Contact(:S, :I, :E, 0.3; layer = :home).name === :S_I_to_E_home
    @test Contact(:S, :I, :E, :τ; name = :infect).name === :infect
    @test Contact(:S, :I, :I, :(2τ)) == Contact(:S, :I, :I, :(2τ))          # structural ==
    @test hash(Contact(:S, :I, :I, :(2τ))) == hash(Contact(:S, :I, :I, :(2τ)))
    @test Contact(:S, :I, :I, :τ) != Contact(:S, :I, :I, :β)
    @test_throws ArgumentError Contact(:S, :S, :I, :τ)          # recipient = infector
    @test_throws ArgumentError Contact(:S, :I, :S, :τ)          # product = recipient
    @test_throws ArgumentError Contact(:S, :I, :I, -0.1)        # negative numeric rate
    @test_throws ArgumentError Contact(:S, :I, :I, NaN)
    # an infinite rate would give NaN downstream, and a Bool is not a rate (WP6 review)
    @test_throws ArgumentError Contact(:S, :I, :I, Inf)
    @test_throws ArgumentError NodeTransition(:I, :R, true)
    @test_throws ArgumentError NodeTransition(:I, :R, Expr(:call, :*, Inf, :γ))   # the value Inf
    @test NodeTransition(:I, :R, :(Inf * γ)).rate == :(Inf * γ)      # a parameter named Inf
    @test_throws ArgumentError Contact(:S, :I, :I, x -> 2x)     # a Function is not a rate
    @test_throws ArgumentError Contact(:S, :I, :I, "τ")
    @test_throws ArgumentError Contact(:S, :I, :I, :(sin(τ)))   # outside RATE_OPS
    err = try
        Contact(:S, :I, :I, sin)
    catch e
        e
    end
    @test err isa ArgumentError && occursin("Function", err.msg) &&
          occursin("cannot be lowered, hashed or run in NetworkOutbreaks", err.msg)
end

@testset "NodeTransition" begin
    t = NodeTransition(:I, :R, :γ)
    @test (t.from, t.to, t.rate, t.name) == (:I, :R, :γ, :I_to_R)
    r = NodeTransition(:I, nothing, :μ)
    @test r.to === nothing && r.name === Symbol("I_to_∅")
    @test NodeTransition(:E, :I, :(p * σ); name = :onset).name === :onset
    @test_throws ArgumentError NodeTransition(:I, :I, :γ)
    @test_throws ArgumentError NodeTransition(:I, :R, sin)
    @test_throws ArgumentError NodeTransition(:I, :R, -1)
    @test NodeTransition(:I, :R, :γ) == NodeTransition(:I, :R, :γ)
end

@testset "SpeciesLabel, Provenance, RateConvention" begin
    l = SpeciesLabel(:S; stratum = :y, count = 2)
    @test (l.base, l.stratum, l.count, l.stage) == (:S, :y, 2, 0)
    @test SpeciesLabel(:I) == SpeciesLabel(:I, :all, 0, 0)
    p = Provenance(:catalyst; method = :stoichiometry, assumptions = ["a"], reaction_map = [2, 1])
    @test (p.source, p.method, p.assumptions, p.reaction_map) == (:catalyst, :stoichiometry, ["a"], [2, 1])
    @test PerContact() isa RateConvention && FrequencyDependent() isa RateConvention
    @test DensityDependent(:N) == DensityDependent(:N)
    @test DensityDependent(1000) == DensityDependent(1000.0)
    @test DensityDependent(:N) != DensityDependent(:M)
    @test sprint(show, DensityDependent(:N)) == "DensityDependent(:N)"
    @test sprint(show, PerContact()) == "PerContact()"
end

seir_direct() = ContactModel(:seir; contacts = [Contact(:S, :I, :E, :τ)],
                             transitions = [NodeTransition(:E, :I, :σ), NodeTransition(:I, :R, :γ)])

@testset "ContactModel: species and susceptible inference" begin
    cm = seir_direct()
    @test species_names(cm) == [:S, :E, :I, :R]           # Sus first, then first appearance
    @test susceptible_species(cm) == [:S]
    @test nameof(cm) === :seir
    @test contact_model(cm) === cm
    @test rate_parameters(cm) == Any[:τ, :σ, :γ]
    @test rate_convention(cm) == PerContact()
    @test isempty(species_labels(cm)) && isempty(parameter_defaults(cm))
    pv = provenance(cm)
    @test pv.source === :direct && pv.method === :explicit && pv.reaction_map == [1, 2, 3]
    @test any(occursin("Sus inferred as recipients \\ contact products = {S}", a) for a in pv.assumptions)

    # explicit species: Sus still first, isolated species allowed
    cm2 = ContactModel(:x; contacts = [Contact(:S, :I, :I, :τ)], species = [:I, :R, :S, :V])
    @test species_names(cm2) == [:S, :I, :R, :V]
    @test_throws ArgumentError ContactModel(:x; contacts = [Contact(:S, :I, :I, :τ)], species = [:S])
    @test_throws ArgumentError ContactModel(:x; contacts = [Contact(:S, :I, :I, :τ)],
                                            species = [:S, :I, :I])

    # user-set susceptible set, recorded as an assumption
    cm3 = ContactModel(:x; contacts = [Contact(:S, :I, :I, :τ)], susceptible = :S)
    @test susceptible_species(cm3) == [:S]
    @test any(occursin("Sus set by the user = {S}", a) for a in provenance(cm3).assumptions)
    @test_throws ArgumentError ContactModel(:x; contacts = [Contact(:S, :I, :I, :τ)],
                                            susceptible = [:Q])

    # recipients that are also products are not susceptible
    rs = ContactModel(:x; contacts = [Contact(:S, :I, :I, :τ), Contact(:I, :S, :R, :δ)])
    @test susceptible_species(rs) == [:S]

    # no contacts at all
    pr = ContactModel(:pr; transitions = [NodeTransition(:E, :I, :σ), NodeTransition(:I, :R, :γ)])
    @test species_names(pr) == [:E, :I, :R] && isempty(susceptible_species(pr))
end

@testset "ContactModel: validation" begin
    two = [Contact(:S, :I, :I, :τ1), Contact(:S, :I, :I, :τ2)]
    @test_throws ArgumentError ContactModel(:x; contacts = two)      # identical reactions
    m = ContactModel(:x; contacts = two, merge_duplicates = true)    # rates add (gluing)
    @test length(contacts(m)) == 1 && only(contacts(m)).rate == :(τ1 + τ2)
    m2 = ContactModel(:x; contacts = [Contact(:S, :I, :I, 0.25), Contact(:S, :I, :I, 0.5)],
                      transitions = [NodeTransition(:I, :R, 0.1), NodeTransition(:I, :R, 0.2)],
                      merge_duplicates = true)
    @test only(contacts(m2)).rate ≈ 0.75 && only(node_transitions(m2)).rate ≈ 0.3
    @test provenance(m2).reaction_map == [1, 3]
    # the same shape on different layers is not a duplicate
    lay = ContactModel(:x; contacts = [Contact(:S, :I, :I, :τh; layer = :home),
                                       Contact(:S, :I, :I, :τc; layer = :comm)])
    @test length(contacts(lay)) == 2
    @test_throws ArgumentError ContactModel(:x; transitions = [NodeTransition(:I, :R, :γ),
                                                                NodeTransition(:I, :R, :μ)])
    # reaction names must be unique (E26)
    @test_throws ArgumentError ContactModel(:x; contacts = [Contact(:S, :I, :I, :τ; name = :r)],
                                            transitions = [NodeTransition(:I, :R, :γ; name = :r)])
    # names that would collide in the back ends (E26)
    @test_throws ArgumentError ContactModel(:x; contacts = [Contact(:S, :I, :I, :τ)],
                                            transitions = [NodeTransition(:I, :γ, :γ)])
    @test_throws ArgumentError ContactModel(:x; contacts = [Contact(:S, :I, :I, :τ)],
                                            transitions = [NodeTransition(:I, :t, :γ)])
    err = try
        ContactModel(:x; contacts = [Contact(:S, :I, :I, :τ)],
                     transitions = [NodeTransition(:I, :R, :seed_I)])
    catch e
        e
    end
    @test err isa ArgumentError && occursin("seed_I", err.msg) && occursin("reserved", err.msg)
    @test_throws ArgumentError ContactModel(:x; contacts = [Contact(:S, :I, :I, :τ)],
                                            rate_params = Any[:τ, :S])
    # a parameter named like the old EBM seed (ρ) is an ordinary parameter now
    @test rate_parameters(ContactModel(:x; contacts = [Contact(:S, :I, :I, :τ)],
                                       transitions = [NodeTransition(:I, :R, :ρ)])) == Any[:τ, :ρ]
    # labels must refer to species
    @test_throws ArgumentError ContactModel(:x; contacts = [Contact(:S, :I, :I, :τ)],
                                            labels = Dict(:Q => SpeciesLabel(:Q)))
    # defaults are stored by name as Float64
    d = ContactModel(:x; contacts = [Contact(:S, :I, :I, :τ)], defaults = Dict(:τ => 1))
    @test parameter_defaults(d) == Dict(:τ => 1.0) && parameter_defaults(d)[:τ] isa Float64
    # ... and are parameter values only: a default named like a species or t is an error, not an
    # initial state that the back ends and reverse maps would drop (WP9fix request to the NEC
    # steward); a default for a parameter that no rate uses is kept
    for bad in (Dict(:τ => 0.2, :R => 1.0), Dict(:S => 0.99), Dict(:t => 0.0))
        err = try
            ContactModel(:x; contacts = [Contact(:S, :I, :I, :τ)],
                         transitions = [NodeTransition(:I, :R, :γ)], defaults = bad)
            nothing
        catch e
            e
        end
        @test err isa ArgumentError && occursin("`defaults` are parameter values by name", err.msg)
    end
    @test parameter_defaults(ContactModel(:x; contacts = [Contact(:S, :I, :I, :τ)],
                                          defaults = Dict(:τ => 0.2, :N => 1e4))) ==
          Dict(:τ => 0.2, :N => 1e4)
    @test_throws ArgumentError ContactModel(:x, [:S, :I], [:S], [Contact(:S, :I, :I, :τ)],
                                            NodeTransition[], Any[:τ], Dict(:I => 0.1),
                                            PerContact(), Dict{Symbol,SpeciesLabel}(),
                                            Provenance(:direct))
    @test_throws ArgumentError ReactionNetworkData(:d, [:X, :Y],
                                                   [GeneralReaction([:X], [:Y], :k)];
                                                   defaults = Dict(:k => 0.1, :X => 1.0))
    # edge_doubling keeps parameter defaults (its species include the edge copies Φ_X)
    ed = edge_doubling(ContactModel(:x; contacts = [Contact(:S, :I, :I, :τ)],
                                    transitions = [NodeTransition(:I, :R, :γ)],
                                    defaults = Dict(:τ => 0.2)), 5.0)
    @test ed.defaults == Dict(:τ => 0.2)
    # the positional (inner) constructor validates too
    @test_throws ArgumentError ContactModel(:x, [:S], Symbol[], [Contact(:S, :I, :I, :τ)],
                                            NodeTransition[], Any[], Dict{Symbol,Float64}(),
                                            PerContact(), Dict{Symbol,SpeciesLabel}(),
                                            Provenance(:direct))
end

@testset "ContactModel: queries" begin
    seair = ContactModel(:seair; contacts = [Contact(:S, :I, :E, :τI), Contact(:S, :A, :E, :τA)],
                         transitions = [NodeTransition(:E, :I, :(p * σ)),
                                        NodeTransition(:E, :A, :((1 - p) * σ)),
                                        NodeTransition(:I, :R, :γ), NodeTransition(:A, :R, :γ)])
    @test species_names(seair) == [:S, :E, :I, :A, :R]
    @test infectious_species(seair) == [:I, :A]
    @test entry_species(seair) == [:E]
    @test rate_parameters(seair) == Any[:τI, :τA, :p, :σ, :γ]
    trace = ContactModel(:trace; contacts = [Contact(:S, :I, :I, :τ), Contact(:S, :D, :Q, :α)],
                         transitions = [NodeTransition(:I, :D, :γ), NodeTransition(:D, :R, :δ)])
    @test infectious_species(trace) == [:I, :D]     # a tracer is an infector of a contact
    @test entry_species(trace) == [:I, :Q]
    # branching at infection and infector-dependent entry are expressible (E25)
    br = ContactModel(:br; contacts = [Contact(:S, :I, :E, :τ1), Contact(:S, :I, :A, :τ2)],
                      transitions = [NodeTransition(:E, :I, :σ), NodeTransition(:A, :R, :γ),
                                     NodeTransition(:I, :R, :γ)])
    @test entry_species(br) == [:E, :A] && infectious_species(br) == [:I]
    dep = ContactModel(:dep; contacts = [Contact(:S, :I, :E, :τI), Contact(:S, :A, :F, :τA)],
                       transitions = [NodeTransition(:E, :I, :σ), NodeTransition(:F, :A, :σ)])
    @test entry_species(dep) == [:E, :F] && infectious_species(dep) == [:I, :A]
    # rate expressions are copied: mutating the caller's Expr does not change the model
    ex = :(2 * γ)
    held = ContactModel(:held; contacts = [Contact(:S, :I, :I, :τ)],
                        transitions = [NodeTransition(:I, :R, ex)])
    ex.args[2] = 3
    @test only(node_transitions(held)).rate == :(2 * γ)
    # accessors return copies
    sp = species_names(seair)
    push!(sp, :Z)
    @test species_names(seair) == [:S, :E, :I, :A, :R]
    cs = contacts(seair)
    empty!(cs)
    @test length(contacts(seair)) == 2
    @test length(node_transitions(seair)) == 4
    # ... and so are their rate expressions (WP6 review: the accessors shared the Exprs, so
    # mutating one changed the model), also between a model and one built from its reactions
    only_t = first(node_transitions(seair))
    only_t.rate.args[2] = :q
    @test first(node_transitions(seair)).rate == :(p * σ)
    other = ContactModel(:other; contacts = contacts(seair), transitions = node_transitions(seair))
    @test first(node_transitions(other)).rate !== first(seair.transitions).rate
    first(other.transitions).rate.args[2] = :q
    @test first(seair.transitions).rate == :(p * σ)
end

@testset "infected_species: the §J.8 typing rule" begin
    C, T = Contact, NodeTransition
    sup = ContactModel(:superinf;
                       contacts = [C(:S, :I1, :I1, :τ1), C(:S, :I2, :I2, :τ2), C(:I1, :I2, :I12, :τs)],
                       transitions = [T(:I1, :R, :γ), T(:I2, :R, :γ), T(:I12, :R, :γ)])
    imp = ContactModel(:seir_import; contacts = [C(:S, :I, :E, :τ)],
                       transitions = [T(:S, :E, :η), T(:E, :I, :σ), T(:I, :R, :γ)])
    trm = ContactModel(:sir_trace; contacts = [C(:S, :I, :I, :τ), C(:S, :I, :Q, :κ)],
                       transitions = [T(:I, :R, :γ), T(:Q, :S, :ω)])
    rem = ContactModel(:sir_removal; contacts = [C(:S, :I, :I, :τ)],
                       transitions = [T(:I, nothing, :γ), T(:S, :V, :ν)])
    # quarantine of latents: E + I → Eq + I, Eq → I (E and Eq are infected)
    qm = ContactModel(:seir_q; contacts = [C(:S, :I, :E, :τ), C(:E, :I, :Eq, :κ)],
                      transitions = [T(:E, :I, :σ), T(:Eq, :I, :σ), T(:I, :R, :γ)])
    # a dead-end product (A never infects and never becomes infectious) is not an infection
    br = ContactModel(:br; contacts = [C(:S, :I, :E, :τ1), C(:S, :I, :A, :τ2)],
                      transitions = [T(:E, :I, :σ), T(:A, :R, :γ), T(:I, :R, :γ)])
    # the same expectations as NodeBasedModels' adopt suite (which cross-checks them against
    # NetworkOutbreaks' _infected_mask), whose rule this is
    expected = Dict(:sir => [:I], :seir => [:E, :I], :sis => [:I], :sirs => [:I],
                    :sirv => [:I], :seair => [:E, :I, :A], :twostrain => [:I1, :I2],
                    :sis_reinf_L3 => [:I_1, :I_2, :I_3], :superinf => [:I1, :I2],
                    :seir_import => [:E, :I], :sir_trace => [:I], :sir_removal => [:I],
                    :seir_q => [:E, :I, :Eq], :br => [:E, :I])
    for cm in (sir_model(), seir_model(), sis_model(), sirs_model(), sirv_model(), seair_model(),
               twostrain_model(), with_reinfection_counting(sis_model(), 3), sup, imp, trm, rem,
               qm, br)
        @test infected_species(cm) == expected[nameof(cm)]
        # never a susceptible class, always every infector, in model order
        inf = infected_species(cm)
        @test isempty(intersect(inf, susceptible_species(cm)))
        @test issubset(setdiff(infectious_species(cm), susceptible_species(cm)), inf)
        @test inf == [X for X in species_names(cm) if X in inf]
    end
    # an infected compartment that only progresses: E of SEIR after Erlang staging of E
    @test infected_species(erlang_stages(seir_model(), :E, 2)) == [:E_1, :E_2, :I]
end

@testset "show" begin
    cm = seir_direct()
    @test sprint(show, cm) == "ContactModel(:seir; 4 species, 1 contact, 2 transitions)"
    txt = sprint(show, MIME"text/plain"(), cm)
    lines = split(txt, '\n')
    @test lines[1] == "ContactModel :seir  (source: ContactModel constructor; method: explicit; rates: PerContact)"
    @test lines[2] == "  species       S (Sus)   E   I   R"
    @test occursin(r"^  contacts      \[1\] S \+ I → E \+ I +τ +contact +infector I, entry E$", lines[3])
    @test occursin(r"^  transitions   \[2\] E → I +σ +progress$", lines[4])
    @test occursin(r"^  +\[3\] I → R +γ +progress$", lines[5])
    @test lines[6] == "  typing        T_EB  ⇒  edge_based ✓  s_anchored ✓  pairwise ✓  individual ✓  " *
                      "pair ✓  stochastic ✓  mass_action ✓"
    @test lines[7] == "  assumptions   Sus inferred as recipients \\ contact products = {S}"
    sis = ContactModel(:sis; contacts = [Contact(:S, :I, :I, :τ)],
                       transitions = [NodeTransition(:I, :S, :γ)])
    t2 = sprint(show, MIME"text/plain"(), sis)
    @test occursin("typing        T_net  ⇒  edge_based ✗  s_anchored ✗  pairwise ✓", t2)
    @test occursin("violations    `γ, I --> S` (type resus: node → sus) produces the susceptible species S.", t2)
    @test sprint(show, Contact(:S, :I, :I, :τ; layer = :home)) == "Contact(:S, :I, :I, :τ; layer = :home)"
    @test sprint(show, NodeTransition(:I, nothing, 0.5)) == "NodeTransition(:I, nothing, 0.5)"
    @test sprint(show, MIME"text/plain"(), Contact(:S, :I, :E, :(ε * τ2))) == "Contact S + I → E + I at ε*τ2"
end
