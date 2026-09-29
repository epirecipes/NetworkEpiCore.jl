# Owner: WP9. The Catalyst front end (DESIGN §B.4, §B.7, §B.8) and the reverse maps
# Catalyst.ReactionSystem(::ContactModel; κ) and Catalyst.ReactionSystem(::ReactionNetworkData)
# of NetworkEpiCoreCatalystExt.

using NetworkEpiCore, Catalyst, Symbolics, Random
const NEC = NetworkEpiCore
const MTKB = Catalyst.ModelingToolkitBase

@test Base.get_extension(NetworkEpiCore, :NetworkEpiCoreCatalystExt) isa Module

C(s, J, X, r; kw...) = Contact(s, J, X, r; kw...)
T(X, Y, r; kw...) = NodeTransition(X, Y, r; kw...)
M(name; kw...) = ContactModel(name; kw...)

errtext(f) = try
    f()
    "no error"
catch e
    sprint(showerror, e)
end
flat(s) = replace(s, r"\s+" => " ")

# ---------------------------------------------------------------------------------------------
# Numeric helpers: the mass-action vector field of a Catalyst system (through ode_model) and the
# independent reference MA(c_κ P) computed from a ContactModel
# ---------------------------------------------------------------------------------------------

_nm(x) = Symbol(Symbolics.getname(x))
function _num(x)
    v = Symbolics.unwrap(x)
    v isa Number && return Float64(v)
    return Float64(Symbolics.SymbolicUtils.unwrap_const(v))
end

function _lhs_state(eq)
    lhs = Symbolics.unwrap(eq.lhs)
    return _nm(only(Symbolics.arguments(lhs)))
end

# d/dt of every unknown of ode_model(rs) at the state u and parameters p (by name).
function catalyst_rhs(rs, u::AbstractDict, p::AbstractDict; t = 0.3)
    osys = ode_model(rs)
    vals = Dict{Any,Any}()
    for x in MTKB.unknowns(osys)
        vals[x] = u[_nm(x)]
    end
    for q in MTKB.parameters(osys)
        vals[q] = p[_nm(q)]
    end
    vals[Catalyst.get_iv(rs)] = t
    return Dict{Symbol,Float64}(_lhs_state(eq) =>
                                    _num(Symbolics.substitute(eq.rhs, vals; fold = Val(true)))
                                for eq in MTKB.equations(osys))
end

# The mass-action ODE of c_κ P on population fractions, with the contact rates of the rate
# convention on WellMixed(κ): κτ (PerContact), β (FrequencyDependent), βN (DensityDependent).
function ma_reference(cm::ContactModel, κ, u, p; t = 0.3)
    du = Dict{Symbol,Float64}(x => 0.0 for x in species_names(cm))
    conv = rate_convention(cm)
    for c in contacts(cm)
        r = rate_value(c.rate, p; t)
        k = conv isa PerContact ? κ * r : conv isa FrequencyDependent ? r :
            r * (conv.N isa Symbol ? p[conv.N] : conv.N)
        f = k * u[c.recipient] * u[c.infector]
        du[c.recipient] -= f
        du[c.product] += f
    end
    for tr in node_transitions(cm)
        f = rate_value(tr.rate, p; t) * u[tr.from]
        du[tr.from] -= f
        tr.to === nothing || (du[tr.to] += f)
    end
    return du
end

function random_point(cm::ContactModel, rng; extra = Symbol[])
    u = Dict{Symbol,Float64}(x => 0.05 + 0.4 * rand(rng) for x in species_names(cm))
    names = union(Symbol[NEC._parameter_name(q) for q in rate_parameters(cm)], extra)
    conv = rate_convention(cm)
    conv isa DensityDependent && conv.N isa Symbol && push!(names, conv.N)
    p = Dict{Symbol,Float64}(n => 0.2 + 0.6 * rand(rng) for n in names)
    return u, p
end

approx_dicts(a, b; rtol = 1e-10) =
    keys(a) == keys(b) && all(isapprox(a[k], b[k]; rtol, atol = 1e-13) for k in keys(a))

# ---------------------------------------------------------------------------------------------
# The corpus (the models of WP6's ir_typing.jl) written as @reaction_network
# ---------------------------------------------------------------------------------------------

sir_ab_contacts = [C(:S_a, :I_a, :I_a, :τ), C(:S_a, :I_b, :I_a, :τ), C(:S_b, :I_a, :I_b, :τ),
                   C(:S_b, :I_b, :I_b, :τ)]
sir_ab_transitions = [T(:I_a, :R_a, :γ), T(:I_b, :R_b, :γ)]

# (id, direct model, Catalyst network, keywords of contact_model)
corpus = [
    (:sir, sir_model(),
     @reaction_network(sir, begin
         τ, S + I --> 2I
         γ, I --> R
     end), (;)),
    (:seir, seir_model(),
     @reaction_network(seir, begin
         τ, S + I --> E + I
         σ, E --> I
         γ, I --> R
     end), (;)),
    (:sis, sis_model(),
     @reaction_network(sis, begin
         τ, S + I --> 2I
         γ, I --> S
     end), (;)),
    (:sirs, sirs_model(),
     @reaction_network(sirs, begin
         τ, S + I --> 2I
         γ, I --> R
         ε, R --> S
     end), (;)),
    (:seair, seair_model(),
     @reaction_network(seair, begin
         τI, S + I --> E + I
         τA, S + A --> E + A
         p * σ, E --> I
         (1 - p) * σ, E --> A
         γ, (I, A) --> R
     end), (;)),
    (:twostrain, twostrain_model(),
     @reaction_network(twostrain, begin
         τ1, S + I1 --> 2I1
         τ2, S + I2 --> 2I2
         γ, I1 --> R
         γ, I2 --> R
     end), (;)),
    (:partial, M(:partial; contacts = [C(:S, :I1, :I1, :τ1), C(:S, :I2, :I2, :τ2),
                                       C(:R1, :I2, :I12, :(ε * τ2))],
                 transitions = [T(:I1, :R1, :γ), T(:I2, :R2, :γ), T(:I12, :R, :γ)]),
     @reaction_network(partial, begin
         τ1, S + I1 --> 2I1
         τ2, S + I2 --> 2I2
         ε * τ2, R1 + I2 --> I12 + I2
         γ, I1 --> R1
         γ, I2 --> R2
         γ, I12 --> R
     end), (;)),
    (:sirv, sirv_model(),
     @reaction_network(sirv, begin
         τ, S + I --> 2I
         γ, I --> R
         ν, S --> V
     end), (;)),
    (:importation, M(:importation; contacts = [C(:S, :I, :E, :τ)],
                transitions = [T(:E, :I, :σ), T(:I, :R, :γ), T(:S, :E, :η)]),
     @reaction_network(importation, begin
         τ, S + I --> E + I
         σ, E --> I
         γ, I --> R
         η, S --> E
     end), (;)),
    (:trace, M(:trace; contacts = [C(:S, :I, :I, :τ), C(:S, :D, :Q, :α)],
               transitions = [T(:I, :D, :γ), T(:D, :R, :δ)]),
     @reaction_network(trace, begin
         τ, S + I --> 2I
         α, S + D --> Q + D
         γ, I --> D
         δ, D --> R
     end), (;)),
    (:scat, M(:scat; contacts = [C(:S, :I, :I, :τ), C(:I, :S, :R, :δ)],
              transitions = [T(:I, :R, :γ)]),
     @reaction_network(scat, begin
         τ, S + I --> 2I
         δ, I + S --> R + S
         γ, I --> R
     end), (;)),
    (:sis_L2, with_reinfection_counting(sis_model(), 2),
     @reaction_network(sis_L2, begin
         τ, S_0 + I_1 --> 2I_1
         τ, S_0 + I_2 --> I_1 + I_2
         τ, S_1 + I_1 --> I_2 + I_1
         τ, S_1 + I_2 --> 2I_2
         τ, S_2 + I_1 --> I_2 + I_1
         τ, S_2 + I_2 --> 2I_2
         γ, I_1 --> S_1
         γ, I_2 --> S_2
     end), (;)),
    (:sir_L3, with_reinfection_counting(sir_model(), 3),
     @reaction_network(sir_L3, begin
         τ, S_0 + I_1 --> 2I_1
         γ, I_1 --> R_1
     end), (;)),
    # species labels are not written in Catalyst; the unlabelled direct model is the reference
    (:sir_ab, M(:sir_ab; contacts = sir_ab_contacts, transitions = sir_ab_transitions),
     @reaction_network(sir_ab, begin
         τ, S_a + I_a --> 2I_a
         τ, S_a + I_b --> I_a + I_b
         τ, S_b + I_a --> I_b + I_a
         τ, S_b + I_b --> 2I_b
         γ, I_a --> R_a
         γ, I_b --> R_b
     end), (;)),
    (:hetsus, M(:hetsus; contacts = [C(:S1, :I, :I, :τ1), C(:S2, :I, :I, :τ2)],
                transitions = [T(:I, :R, :γ)]),
     @reaction_network(hetsus, begin
         τ1, S1 + I --> 2I
         τ2, S2 + I --> 2I
         γ, I --> R
     end), (;)),
    (:susmove, M(:susmove; contacts = [C(:S1, :I, :I, :τ), C(:S2, :I, :I, :τ)],
                 transitions = [T(:I, :R, :γ), T(:S1, :S2, :ω)]),
     @reaction_network(susmove, begin
         τ, S1 + I --> 2I
         τ, S2 + I --> 2I
         γ, I --> R
         ω, S1 --> S2
     end), (;)),
    (:suscontact, M(:suscontact; contacts = [C(:S1, :I, :S2, :κ), C(:S2, :I, :I, :τ)],
                    transitions = [T(:I, :R, :γ)], susceptible = [:S1, :S2]),
     @reaction_network(suscontact, begin
         κ, S1 + I --> S2 + I
         τ, S2 + I --> 2I
         γ, I --> R
     end), (; susceptible = [:S1, :S2])),
    (:susinfector, M(:susinfector; contacts = [C(:S, :I, :I, :τ), C(:U, :S, :E, :κ)],
                     transitions = [T(:E, :I, :σ), T(:I, :R, :γ)]),
     @reaction_network(susinfector, begin
         τ, S + I --> 2I
         κ, U + S --> E + S
         σ, E --> I
         γ, I --> R
     end), (;)),
    (:sird, M(:sird; contacts = [C(:S, :I, :I, :τ)], transitions = [T(:I, nothing, :μ)]),
     @reaction_network(sird, begin
         τ, S + I --> 2I
         μ, I --> ∅
     end), (;)),
    (:sdeath, M(:sdeath; contacts = [C(:S, :I, :I, :τ)],
                transitions = [T(:I, :R, :γ), T(:S, nothing, :μ)]),
     @reaction_network(sdeath, begin
         τ, S + I --> 2I
         γ, I --> R
         μ, S --> ∅
     end), (;)),
    (:sir_t, M(:sir_t; contacts = [C(:S, :I, :I, :(τ0 * exp(-a * t)))],
               transitions = [T(:I, :R, :γ)]),
     @reaction_network(sir_t, begin
         τ0 * exp(-a * t), S + I --> 2I
         γ, I --> R
     end), (;)),
    (:bypass, M(:bypass; contacts = [C(:S, :I, :E, :τ)],
                transitions = [T(:E, :I, :(p * σ)), T(:E, :R, :((1 - p) * σ)), T(:I, :R, :γ)]),
     @reaction_network(bypass, begin
         τ, S + I --> E + I
         p * σ, E --> I
         (1 - p) * σ, E --> R
         γ, I --> R
     end), (;)),
    (:branch_inf, M(:branch_inf; contacts = [C(:S, :I, :E, :τ1), C(:S, :I, :A, :τ2)],
                    transitions = [T(:E, :I, :σ), T(:A, :R, :γA), T(:I, :R, :γ)]),
     @reaction_network(branch_inf, begin
         τ1, S + I --> E + I
         τ2, S + I --> A + I
         σ, E --> I
         γA, A --> R
         γ, I --> R
     end), (;)),
    (:entry_by_inf, M(:entry_by_inf; contacts = [C(:S, :I, :E, :τI), C(:S, :A, :F, :τA)],
                      transitions = [T(:E, :I, :σ), T(:F, :A, :σ), T(:I, :R, :γ),
                                     T(:A, :R, :γ)]),
     @reaction_network(entry_by_inf, begin
         τI, S + I --> E + I
         τA, S + A --> F + A
         σ, E --> I
         σ, F --> A
         γ, I --> R
         γ, A --> R
     end), (;)),
    (:sir_erl3, erlang_stages(sir_model(), :I, 3),
     @reaction_network(sir_erl3, begin
         τ, S + I_1 --> 2I_1
         τ, S + I_2 --> I_1 + I_2
         τ, S + I_3 --> I_1 + I_3
         3γ, I_1 --> I_2
         3γ, I_2 --> I_3
         3γ, I_3 --> R
     end), (;)),
    (:seir_fd, M(:seir_fd; contacts = [C(:S, :I, :E, :β)],
                 transitions = [T(:E, :I, :σ), T(:I, :R, :γ)], convention = FrequencyDependent()),
     @reaction_network(seir_fd, begin
         @parameters β σ γ N
         β / N, S + I --> E + I
         σ, E --> I
         γ, I --> R
     end), (; rates = :frequency, population = :N)),
    (:sir_mpx, M(:sir_mpx; contacts = [C(:S, :I, :I, :τh; layer = :home),
                                       C(:S, :I, :I, :τc; layer = :comm)],
                 transitions = [T(:I, :R, :γ)]),
     @reaction_network(sir_mpx, begin
         τh, S + I --> 2I, [layer = :home]
         τc, S + I --> 2I, [layer = :comm]
         γ, I --> R
     end), (;)),
    (:sirvs, M(:sirvs; contacts = [C(:S, :I, :I, :τ)],
               transitions = [T(:I, :R, :γ), T(:S, :V, :ν), T(:V, :S, :ω)]),
     @reaction_network(sirvs, begin
         τ, S + I --> 2I
         γ, I --> R
         ν, S --> V
         ω, V --> S
     end), (;)),
    (:seirs, M(:seirs; contacts = [C(:S, :I, :E, :τ)],
               transitions = [T(:E, :I, :σ), T(:I, :R, :γ), T(:R, :S, :ε)]),
     @reaction_network(seirs, begin
         τ, S + I --> E + I
         σ, E --> I
         γ, I --> R
         ε, R --> S
     end), (;)),
    (:nocontact, M(:nocontact; transitions = [T(:E, :I, :σ), T(:I, :R, :γ)]),
     @reaction_network(nocontact, begin
         σ, E --> I
         γ, I --> R
     end), (;)),
]

shape_c(c) = (c.recipient, c.infector, c.product, c.layer, c.name)
shape_t(t) = (t.from, t.to, t.name)

@testset "corpus: @reaction_network gives the direct ContactModel ($(length(corpus)) models)" begin
    @test length(corpus) >= 25
    for (id, direct, rn, kw) in corpus
        @testset "$id" begin
            cm = contact_model(rn; kw...)
            @test cm isa ContactModel
            @test nameof(cm) === id
            @test isequivalent(cm, direct)
            @test species_names(cm) == species_names(direct)
            @test susceptible_species(cm) == susceptible_species(direct)
            @test rate_convention(cm) == rate_convention(direct)
            @test shape_c.(contacts(cm)) == shape_c.(contacts(direct))
            @test shape_t.(node_transitions(cm)) == shape_t.(node_transitions(direct))
            @test all(NEC._rates_equal(a.rate, b.rate)
                      for (a, b) in zip(contacts(cm), contacts(direct)))
            @test all(NEC._rates_equal(a.rate, b.rate)
                      for (a, b) in zip(node_transitions(cm), node_transitions(direct)))
            # rates are plain Symbol/Expr/number rates, not symbolic ones
            @test all(r -> r isa Union{Symbol,Expr,Real} && !(r isa Symbolics.Num),
                      [x.rate for x in vcat(contacts(cm), node_transitions(cm))])
            @test Set(rate_parameters(cm)) == Set(rate_parameters(direct))
            tc, td = typing(cm), typing(direct)
            @test tc.reaction_types == td.reaction_types
            @test tc.theory === td.theory
            ac, ad = admissibility(cm), admissibility(direct)
            @test ac.backends == ad.backends
            @test [v.type for v in ac.violations] == [v.type for v in ad.violations]
            pv = provenance(cm)
            @test pv.source === :catalyst && pv.method === :stoichiometry
            nr = length(contacts(cm)) + length(node_transitions(cm))
            @test pv.reaction_map == collect(1:nr)
        end
    end
end

@testset "worked examples (§B.8)" begin
    sir_rn = @reaction_network sir begin
        @parameters τ γ
        τ, S + I --> 2I
        γ, I --> R
    end
    sir_dir = ContactModel(:sir; contacts = [Contact(:S, :I, :I, :τ)],
                           transitions = [NodeTransition(:I, :R, :γ)])
    @test isequivalent(contact_model(sir_rn), sir_dir, sir_model())
    # the canonical first cell
    txt = sprint(show, MIME"text/plain"(), contact_model(sir_rn))
    @test startswith(txt, "ContactModel :sir  (source: Catalyst.ReactionSystem; method: " *
                          "stoichiometry; rates: PerContact)\n  species       S (Sus)   I   R\n")
    @test occursin("assumptions   Sus inferred as recipients \\ contact products = {S}", txt)

    seir_rn = @reaction_network seir begin
        @parameters β σ γ N
        β / N, S + I --> E + I
        σ, E --> I
        γ, I --> R
    end
    cm = contact_model(seir_rn; rates = :frequency, population = :N)
    @test contacts(cm) == [Contact(:S, :I, :E, :β)]
    @test rate_convention(cm) == FrequencyDependent()
    @test rate_parameters(cm) == [:β, :σ, :γ]            # N is consumed by the reading
    p = Dict(:β => 0.9, :σ => 0.2, :γ => 0.25)
    @test rate_value(only(per_contact_rates(cm, WellMixed(5.0))), p) ≈ 0.9 / 5
    @test rate_value(only(per_contact_rates(cm, ConfigurationNetwork(RegularDegree(6)))), p) ≈
          0.9 / 6
    @test any(a -> occursin("frequency-dependent", a), provenance(cm).assumptions)

    sis = @reaction_network sis begin
        τ, S + I --> 2I
        γ, I --> S
    end
    cms = contact_model(sis)
    @test typing(cms).theory === :T_net
    @test !is_admissible(cms, :edge_based) && is_admissible(cms, :pairwise)

    seair = @reaction_network seair begin
        τI, S + I --> E + I; τA, S + A --> E + A
        p*σ, E --> I;  (1-p)*σ, E --> A;  γ, (I, A) --> R
    end
    @test isequivalent(contact_model(seair), seair_model())

    vax = @reaction_network begin; τ, S + I --> 2I; γ, I --> R; ν, S --> V; end
    @test isequivalent(contact_model(vax), sirv_model())
    @test last.(typing(contact_model(vax)).reaction_types) == [:contact, :progress, :exit]
    trace = @reaction_network begin
        τ, S + I --> 2I; γ, I --> D; δ, D --> R; α, S + D --> Q + D
    end
    @test typing(contact_model(trace)).theory === :T_EB
    @test entry_species(contact_model(trace)) == [:I, :Q]
end

# ---------------------------------------------------------------------------------------------
# Errors (§B.4, §B.7)
# ---------------------------------------------------------------------------------------------

@testset "error texts (§B.7)" begin
    bad = @reaction_network begin
        β, S + I --> E + R
        γ, I --> R
    end
    @test_throws ArgumentError contact_model(bad)
    @test errtext(() -> contact_model(bad)) ==
          "ArgumentError: `β, S + I --> E + R`: the infector changes state on transmission; a " *
          "network contact must leave the infector unchanged. Split it into `β, S + I --> E + " *
          "I` and a transition `I --> R`."
    nb = @reaction_network begin
        β*S*I/(1 + a*I), S + I => E + I
    end
    @test_throws ArgumentError contact_model(nb)
    @test startswith(errtext(() -> contact_model(nb)),
                     "ArgumentError: rate law of `β*S*I/(1 + a*I), S + I => E + I` depends on " *
                     "species (non-bilinear incidence).")
    @test occursin("species-dependent or non-mass-action rate law; the IR supports mass-action " *
                   "contacts and first-order transitions only", errtext(() -> contact_model(nb)))
    births = @reaction_network begin
        μ, ∅ --> S
        τ, S + I --> 2I
    end
    @test_throws ArgumentError contact_model(births)
    @test errtext(() -> contact_model(births)) ==
          "ArgumentError: `μ, ∅ --> S`: births change the node set; use Catalyst's own ODE for " *
          "mass action."

    # the AdmissibilityError of a Catalyst SIS is the text of §B.7, verbatim
    sis = @reaction_network sis begin
        τ, S + I --> 2I
        γ, I --> S
    end
    err = try
        require_admissible(contact_model(sis), :edge_based;
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
    partial = @reaction_network partial begin
        τ1, S + I1 --> 2I1;  τ2, S + I2 --> 2I2;  γ, I1 --> R1;  γ, I2 --> R2
        ε*τ2, R1 + I2 --> I12 + I2;  γ, I12 --> R
    end
    err2 = try
        require_admissible(contact_model(partial), :edge_based)
    catch e
        e
    end
    @test err2 isa AdmissibilityError
    @test occursin("`ε*τ2, R1 + I2 --> I12 + I2`: R1 is a second susceptible class " *
                   "(multiple_sus) and is produced by `γ, I1 --> R1` (resus).",
                   flat(sprint(showerror, err2)))
end

@testset "every error category (§B.4)" begin
    cases = [
        # species in a `-->` rate
        ("rate law of `β*I, S + I --> 2I` depends on species (non-bilinear incidence)",
         @reaction_network(begin β * I, S + I --> 2I end)),
        ("rate law of `β/(S + I + R), S + I --> 2I` depends on species",
         @reaction_network(begin β / (S + I + R), S + I --> 2I; γ, I --> R end)),
        # a `=>` law that is not mass action, for a transition and for a contact
        ("rate law of `k*I^2, I => R` depends on species (not a first-order transition)",
         @reaction_network(begin k * I^2, I => R end)),
        ("rate law of `β*I, S + I => 2I` depends on species (non-bilinear incidence)",
         @reaction_network(begin β * I, S + I => 2I end)),
        # splitting and higher order
        ("`k, I --> R + D`: splitting (one node becomes 2 nodes)",
         @reaction_network(begin k, I --> R + D end)),
        ("`k, I --> 2R`: splitting", @reaction_network(begin k, I --> 2R end)),
        ("`β, 2S + I --> S + 2I`: higher order (2S + I)",
         @reaction_network(begin β, 2S + I --> S + 2I end)),
        ("`β, S + 2I --> 3I`: higher order (S + 2I)",
         @reaction_network(begin β, S + 2I --> 3I end)),
        ("`k, 2I --> I`: higher order (2I)",
         @reaction_network(begin k, 2I --> I; β, S + I --> 2I end)),
        ("`k, S + I + R --> 2I + R`: higher order",
         @reaction_network(begin k, S + I + R --> 2I + R end)),
        # contacts that are not s + J → X + J
        ("`β, S + I --> E + R`: the infector changes state on transmission",
         @reaction_network(begin β, S + I --> E + R end)),
        ("`β, S + I --> E`: the infector is consumed on transmission",
         @reaction_network(begin β, S + I --> E end)),
        ("`β, S + I --> ∅`: not a pairwise contact: neither substrate survives",
         @reaction_network(begin β, S + I --> ∅ end)),
        ("`β, S + I --> 3I`: not a pairwise contact: besides the infector I it produces 2I",
         @reaction_network(begin β, S + I --> 3I end)),
        ("`β, S + I --> I`: the recipient S disappears",
         @reaction_network(begin β, S + I --> I end)),
        ("`β, S + I --> S + 2I`: not a pairwise contact: both substrates survive",
         @reaction_network(begin β, S + I --> S + 2I end)),
        ("`β, S + I --> I + E + R`: not a pairwise contact",
         @reaction_network(begin β, S + I --> I + E + R end)),
        # births
        ("`μ, ∅ --> S`: births change the node set", @reaction_network(begin μ, 0 --> S end)),
        # reversible reactions give a higher-order reverse reaction
        ("`k₂, 2I --> S + I`: higher order (2I)",
         @reaction_network(begin (β, k₂), S + I <--> 2I end)),
    ]
    for (msg, rn) in cases
        @test_throws ArgumentError contact_model(rn)
        @test occursin(msg, errtext(() -> contact_model(rn)))
    end

    # the suggested split of a non-catalytic contact takes the recipient from the other
    # reactions when they tell the substrates apart, whatever the order they are written in
    split_msg = "Split it into `β, S + I --> E + I` and a transition `I --> R`."
    for rn in (@reaction_network(begin            # S is the recipient of another contact
                   τ, S + I --> 2I
                   β, I + S --> R + E
                   γ, I --> R
               end),
               @reaction_network(begin            # I is produced by a reaction, S never is
                   β, I + S --> R + E
                   σ, E --> I
                   γ, I --> R
               end),
               @reaction_network(begin            # I is the infector of another contact
                   β, I + S --> R + E
                   α, V + I --> W + I
               end))
        @test endswith(errtext(() -> contact_model(rn)), split_msg)
    end
    # ... or from the declared susceptible species
    lone = @reaction_network begin; β, I + S --> R + E; end
    @test endswith(errtext(() -> contact_model(lone; susceptible = :S)), split_msg)
    @test endswith(errtext(() -> contact_model(@reaction_network(begin
                       β, I + S --> E
                       σ, E --> I
                   end))), "Write it as `β, S + I --> E + I`, with any change of I as a transition.")
    # without evidence the first substrate is the recipient (as in §B.7, `β, S + I --> E + R`)
    @test endswith(errtext(() -> contact_model(lone)),
                   "Split it into `β, I + S --> R + S` and a transition `S --> E`.")

    # §B.1: a rate may depend on parameters and time only. (a) A non-species unknown V(t) in a
    # rate is an error, not a parameter V.
    rnV = @reaction_network begin
        @variables V(t)
        β * V, S + I --> 2I
        γ, I --> R
    end
    @test any(u -> _nm(u) === :V, MTKB.unknowns(rnV)) && !(:V in _nm.(Catalyst.species(rnV)))
    @test_throws ArgumentError contact_model(rnV)
    # (the rate reads as written, β*V: other variables come after the parameters)
    @test occursin("`β*V, S + I --> 2I`: the rate depends on V(t), which is a non-species " *
                   "unknown of the reaction system (reaction 1). A network rate is species-free " *
                   "and may depend on parameters and the independent variable t only",
                   errtext(() -> contact_model(rnV)))
    # (b) an observable is expanded first: β/Ntot with Ntot ~ S + I + R is the frequency-dependent
    # incidence β/(S + I + R), which depends on species, not β over a constant Ntot
    tt = Catalyst.default_t()
    @species S(tt) I(tt) R(tt)
    @parameters β γ a
    @variables Ntot(tt) M(tt)
    rnO = complete(ReactionSystem([Reaction(β / Ntot, [S, I], [I], [1, 1], [2]),
                                   Reaction(γ, [I], [R])], tt, [S, I, R], [β, γ];
                                  name = :obsN, observed = [Ntot ~ S + I + R]))
    @test length(MTKB.observed(rnO)) == 1
    @test_throws ArgumentError contact_model(rnO)
    @test startswith(errtext(() -> contact_model(rnO)),
                     "ArgumentError: rate law of `β/Ntot, S + I --> 2I` depends on species " *
                     "(non-bilinear incidence) through the observable Ntot = S + I + R. Reaction " *
                     "1 has a species-dependent or non-mass-action rate law")
    # observables defined through other observables, and in a `=>` law
    rnM = complete(ReactionSystem([Reaction(β / M, [S, I], [I], [1, 1], [2]),
                                   Reaction(γ, [I], [R])], tt, [S, I, R], [β, γ];
                                  name = :obsM, observed = [Ntot ~ S + I + R, M ~ 2Ntot]))
    @test occursin("depends on species (non-bilinear incidence) through the observables " *
                   "M = 2*(S + I + R), Ntot = S + I + R", errtext(() -> contact_model(rnM)))
    rnL = complete(ReactionSystem([Reaction(β * S * I / Ntot, [S, I], [I], [1, 1], [2];
                                            only_use_rate = true),
                                   Reaction(γ, [I], [R])], tt, [S, I, R], [β, γ];
                                  name = :obsL, observed = [Ntot ~ S + I + R]))
    @test startswith(errtext(() -> contact_model(rnL)),
                     "ArgumentError: rate law of `β*S*I/Ntot, S + I => 2I` depends on species " *
                     "(non-bilinear incidence) through the observable Ntot = S + I + R.")
    # a species-free observable is replaced by its definition, with a note
    rnP = complete(ReactionSystem([Reaction(β * M, [S, I], [I], [1, 1], [2]),
                                   Reaction(γ, [I], [R])], tt, [S, I, R], [β, γ, a];
                                  name = :obsP, observed = [M ~ 2a]))
    cmP = contact_model(rnP)
    @test isequivalent(cmP, sir_model(; τ = :(2 * a * β)))
    # messages print a rate as written: the observable after the parameters (β*M, not M*β)
    rnQ = complete(ReactionSystem([Reaction(β * M, [S, I], [I], [1, 1], [2]),
                                   Reaction(γ, [I], [R])], tt, [S, I, R], [β, γ];
                                  name = :obsQ, observed = [M ~ 2S]))
    @test startswith(errtext(() -> contact_model(rnQ)),
                     "ArgumentError: rate law of `β*M, S + I --> 2I` depends on species " *
                     "(non-bilinear incidence) through the observable M = 2S.")
    @test Set(rate_parameters(cmP)) == Set([:a, :β, :γ])
    @test any(s -> occursin("the observable M in the rate replaced by its definition", s),
              provenance(cmP).assumptions)
    # an element of an array parameter is an error (E25): the IR names every rate parameter by a
    # Symbol, and k[1] and k[2] would both be k, so the reverse map would bind both rates to one
    # scalar parameter k (dI/dt = k*S*I - k*I instead of k1*S*I - k2*I)
    rnk = @reaction_network begin
        @parameters k[1:2] = [0.3, 0.1]
        k[1], S + I --> 2I
        k[2], I --> R
    end
    @test_throws ArgumentError contact_model(rnk)
    @test errtext(() -> contact_model(rnk)) ==
          "ArgumentError: `k[1], S + I --> 2I`: the rate uses k[1], an element of the array " *
          "parameter k (reaction 1). A ContactModel names each rate parameter by a Symbol and " *
          "has scalar parameters only; declare scalar parameters instead, for example " *
          "@parameters k1 k2."
    # ... in any reaction (Catalyst lists k and k[2] as parameters here), and in a matrix
    rnk2 = @reaction_network begin
        @parameters k[1:2]
        τ, S + I --> 2I
        k[2], I --> R
    end
    @test occursin("`k[2], I --> R`: the rate uses k[2], an element of the array parameter k " *
                   "(reaction 2)", errtext(() -> contact_model(rnk2)))
    rnK = @reaction_network begin
        @parameters K[1:2, 1:3]
        K[1, 2], S + I --> 2I
    end
    @test occursin("`K[1, 2], S + I --> 2I`: the rate uses K[1, 2], an element of the array " *
                   "parameter K (reaction 1). A ContactModel names each rate parameter by a " *
                   "Symbol and has scalar parameters only; declare scalar parameters instead, " *
                   "for example @parameters K1_1 K1_2 K1_3 K2_1 …",
                   errtext(() -> contact_model(rnK)))
    # the same network with scalar parameters is the model the array version meant
    rnk1 = @reaction_network begin
        @parameters k1 = 0.3 k2 = 0.1
        k1, S + I --> 2I
        k2, I --> R
    end
    cmk1 = contact_model(rnk1)
    @test isequivalent(cmk1, sir_model(; τ = :k1, γ = :k2))
    @test rate_parameters(cmk1) == [:k1, :k2]
    @test parameter_defaults(cmk1) == Dict(:k1 => 0.3, :k2 => 0.1)
    # an array parameter that no rate uses is harmless; its default is not recorded, with a note
    rnw = @reaction_network begin
        @parameters τ = 0.2 γ = 0.25 w[1:2] = [1.0, 2.0]
        τ, S + I --> 2I
        γ, I --> R
    end
    cmw = contact_model(rnw)
    @test isequivalent(cmw, sir_model()) && rate_parameters(cmw) == [:τ, :γ]
    @test parameter_defaults(cmw) == Dict(:τ => 0.2, :γ => 0.25)
    @test any(a -> occursin("the defaults of the array parameter w are not recorded", a),
              provenance(cmw).assumptions)

    # constant and boundary-condition species
    cons = @reaction_network begin
        @parameters X [isconstantspecies = true]
        k, X + I --> R + X
    end
    @test occursin("X is a constant species (a parameter)", errtext(() -> contact_model(cons)))
    bc = @reaction_network begin
        @species B(t) [isbcspecies = true]
        k, B + I --> B + R
    end
    @test occursin("B is a boundary-condition species", errtext(() -> contact_model(bc)))
    # parametric stoichiometry
    pst = @reaction_network begin
        @parameters n::Int
        k, n * I --> R
    end
    @test occursin("is not a positive integer", errtext(() -> contact_model(pst)))
    # non-reaction equations and events
    eqs = @reaction_network begin
        @equations D(V) ~ -V
        τ, S + I --> 2I
    end
    @test occursin("non-reaction equation", errtext(() -> contact_model(eqs)))
    ev = @reaction_network begin
        @parameters τ
        @discrete_events 1.0 => [τ => 0.3]
        τ, S + I --> 2I
    end
    @test occursin("event(s); a ContactModel cannot represent events",
                   errtext(() -> contact_model(ev)))

    # keyword errors
    sir = @reaction_network begin; τ, S + I --> 2I; γ, I --> R; end
    @test occursin("rates = :mass_action must be one of",
                   errtext(() -> contact_model(sir; rates = :mass_action)))
    @test occursin("rates = :density needs population",
                   errtext(() -> contact_model(sir; rates = :density)))
    @test occursin("population must be nothing, a parameter name",
                   errtext(() -> contact_model(sir; rates = :frequency, population = -1)))
    @test occursin("population = :N is not a parameter of the reaction system",
                   errtext(() -> contact_model(sir; rates = :frequency, population = :N)))
    @test occursin("susceptible must be :infer, a Symbol or a vector of Symbols",
                   errtext(() -> contact_model(sir; susceptible = "S")))
    @test occursin("transmission = :bogus is not supported",
                   errtext(() -> contact_model(sir; transmission = :bogus)))
    @test occursin("transmission must be", errtext(() -> contact_model(sir; transmission = 3.0)))
    @test occursin("one flag per reaction (2)",
                   errtext(() -> contact_model(sir; transmission = [true])))
    @test occursin("out of range 1:2", errtext(() -> contact_model(sir; transmission = [3])))
    # merged duplicates: an error unless merge_duplicates = true (the rates then add)
    dup = @reaction_network begin; τ, S + I --> 2I; τ, S + I --> 2I; γ, I --> R; end
    @test occursin("are identical (S + I → I + I); pass merge_duplicates = true",
                   errtext(() -> contact_model(dup)))
    md = contact_model(dup; merge_duplicates = true)
    @test length(contacts(md)) == 1
    @test isequivalent(md, sir_model(; τ = :(2τ)))
    @test provenance(md).reaction_map == [1, 3]
end

@testset "no-ops are dropped with a warning" begin
    rn = @reaction_network begin
        γ, I --> R
        k, S + I --> S + I
        τ, S + I --> 2I
    end
    cm = @test_logs (:warn, r"reaction 2 .* does nothing and is dropped") contact_model(rn)
    @test isequivalent(cm, sir_model())
    @test provenance(cm).reaction_map == [3, 1]          # IR order: contacts, then transitions
    @test any(a -> occursin("dropped reaction 2", a), provenance(cm).assumptions)
    t = Catalyst.default_t()
    @species X(t) Y(t)
    @parameters k
    selfloop = complete(ReactionSystem([Reaction(k, [X], [X]),
                                        Reaction(k, [X], [Y])], t; name = :selfloop))
    cm2 = @test_logs (:warn, r"does nothing") contact_model(selfloop)
    @test node_transitions(cm2) == [NodeTransition(:X, :Y, :k)]
end

# The defects of the old EBM `progression_from_catalyst` (VERIFIED_ISSUES.md, E25): the entry was
# the first species gained in Dict order, the infector was never checked to be a catalyst,
# branching at infection kept only the first entry, stoichiometry was ignored and species inside
# rates bound silently.
@testset "E25: catalysis-checking classifier" begin
    rn1 = @reaction_network begin
        β, S + I --> 2I
        γ, I --> R
    end
    @test only(contacts(contact_model(rn1))).rate === :β          # per contact, unchanged
    # the product order does not matter
    fwd = @reaction_network begin; β, S + I --> E + I; σ, E --> I; end
    rev = @reaction_network begin; β, I + S --> I + E; σ, E --> I; end
    @test contacts(contact_model(fwd)) == contacts(contact_model(rev)) ==
          [Contact(:S, :I, :E, :β)]
    # branching at infection keeps every entry, in either listing order
    b1 = @reaction_network begin
        β1, S + I --> E + I
        β2, S + I --> A + I
        σ, E --> I; γA, A --> R; γ, I --> R
    end
    b2 = @reaction_network begin
        β2, S + I --> A + I
        β1, S + I --> E + I
        σ, E --> I; γA, A --> R; γ, I --> R
    end
    cb1, cb2 = contact_model(b1), contact_model(b2)
    @test isequivalent(cb1, cb2)
    @test Set(entry_species(cb1)) == Set([:E, :A])
    @test is_admissible(cb1, :edge_based)
    # infector-dependent entry
    idep = @reaction_network begin
        βI, S + I --> 2I; βA, S + A --> 2A; γ, I --> R; γA, A --> R
    end
    @test entry_species(contact_model(idep)) == [:I, :A]
    # non-catalytic, non-unit or higher-order reactions are errors
    for rn in (@reaction_network(begin β, S + I --> E + R; σ, E --> I end),
               @reaction_network(begin β, S + I --> 3I; γ, I --> R end),
               @reaction_network(begin β, 2S + I --> S + 2I; γ, I --> R end),
               @reaction_network(begin k, 2I --> I; β, S + I --> 2I; γ, I --> R end),
               @reaction_network(begin β / (S + I + R), S + I --> 2I; γ, I --> R end))
        @test_throws ArgumentError contact_model(rn)
    end
    # `=>` laws are reduced to their constant instead of binding S(t) and I(t) silently
    rex = @reaction_network begin; β*S*I, S + I => 2I; γ, I --> R; end
    @test only(contacts(contact_model(rex))).rate === :β
end

# ---------------------------------------------------------------------------------------------
# Overrides: metadata, transmission flags, susceptible
# ---------------------------------------------------------------------------------------------

@testset "metadata overrides and layers" begin
    rn = @reaction_network mpx begin
        τh, S + I --> 2I, [layer = :household, contact = true]
        τc, S + I --> 2I, [layer = :community]
        γ, I --> R, [contact = false]
    end
    cm = contact_model(rn)
    @test [c.layer for c in contacts(cm)] == [:household, :community]
    @test [c.name for c in contacts(cm)] == [:S_I_to_I_household, :S_I_to_I_community]
    @test count(a -> occursin("acts on the layer", a), provenance(cm).assumptions) == 2
    mnet = MultiplexNetwork(:household => ConfigurationNetwork(RegularDegree(3)),
                            :community => ConfigurationNetwork(PoissonDegree(4.0)))
    @test is_admissible(cm, :edge_based; network = mnet)
    @test !is_admissible(cm, :edge_based; network = ConfigurationNetwork(RegularDegree(3)))

    # [contact = …] is checked against the stoichiometry
    wrong1 = @reaction_network begin; τ, S + I --> 2I, [contact = false]; end
    @test occursin("is marked as not a contact (reaction metadata [contact = false])",
                   errtext(() -> contact_model(wrong1)))
    wrong2 = @reaction_network begin; γ, I --> R, [contact = true]; τ, S + I --> 2I; end
    @test occursin("is marked as a contact (reaction metadata [contact = true]), but it is a " *
                   "node transition", errtext(() -> contact_model(wrong2)))
    notbool = @reaction_network begin; τ, S + I --> 2I, [contact = :yes]; end
    @test occursin("[contact = :yes] must be true or false", errtext(() -> contact_model(notbool)))
    laytr = @reaction_network begin; τ, S + I --> 2I; γ, I --> R, [layer = :home]; end
    @test occursin("[layer = :home] applies to contacts only", errtext(() -> contact_model(laytr)))
    badlayer = @reaction_network begin; τ, S + I --> 2I, [layer = 3]; end
    @test occursin("[layer = 3] must be a Symbol", errtext(() -> contact_model(badlayer)))

    # transmission = :metadata: the contacts are exactly the reactions marked [contact = true]
    marked = @reaction_network begin
        τ, S + I --> 2I, [contact = true]
        γ, I --> R
    end
    cmm = contact_model(marked; transmission = :metadata)
    @test isequivalent(cmm, sir_model()) && provenance(cmm).method === :metadata
    unmarked = @reaction_network begin; τ, S + I --> 2I; γ, I --> R; end
    @test occursin("is marked as not a contact (reaction metadata [contact = …])",
                   errtext(() -> contact_model(unmarked; transmission = :metadata)))

    # predicates, Vector{Bool} and indices (as in ReproductiveNumbers.jl)
    for tr in (rx -> length(rx.substrates) == 2, [true, false], [1])
        cmp = contact_model(unmarked; transmission = tr)
        @test isequivalent(cmp, sir_model()) && provenance(cmp).method === :predicate
    end
    @test occursin("is marked as a contact (transmission = …), but it is a node transition",
                   errtext(() -> contact_model(unmarked; transmission = [true, true])))
    @test occursin("the predicate must return true or false",
                   errtext(() -> contact_model(unmarked; transmission = rx -> 1)))
    # with flags, [contact = …] metadata is still checked against the stoichiometry
    flagged = @reaction_network begin; τ, S + I --> 2I, [contact = false]; γ, I --> R; end
    for tr in (rx -> length(rx.substrates) == 2, [true, false], [1])
        @test occursin("is marked as not a contact (reaction metadata [contact = false])",
                       errtext(() -> contact_model(flagged; transmission = tr)))
    end
    consistent = @reaction_network begin
        τ, S + I --> 2I, [contact = true]
        γ, I --> R, [contact = false]
    end
    @test isequivalent(contact_model(consistent; transmission = [1]), sir_model())
    # overrides never make an unrepresentable reaction representable
    nonpair = @reaction_network begin; β, S + I --> E + R, [contact = true]; end
    @test occursin("the infector changes state",
                   errtext(() -> contact_model(nonpair; transmission = :metadata)))

    # [susceptible = …] declares Σ; the keyword and the metadata must agree
    sm = @reaction_network begin
        κ, S1 + I --> S2 + I, [susceptible = [:S1, :S2]]
        τ, S2 + I --> 2I
        γ, I --> R
    end
    cms = contact_model(sm)
    @test susceptible_species(cms) == [:S1, :S2]
    @test last.(typing(cms).reaction_types) == [:sus_contact, :contact, :progress]
    @test any(a -> occursin("[susceptible = …]", a), provenance(cms).assumptions)
    @test susceptible_species(contact_model(sm; susceptible = [:S2, :S1])) == [:S2, :S1]
    @test occursin("contradicts the reaction metadata [susceptible = …]",
                   errtext(() -> contact_model(sm; susceptible = :S1)))
    badsus = @reaction_network begin; τ, S + I --> 2I, [susceptible = :Z]; end
    @test occursin("names Z, which is not a species", errtext(() -> contact_model(badsus)))
    # the keyword alone (partial immunity with Σ = {S} forced)
    partial = @reaction_network begin
        τ1, S + I1 --> 2I1;  τ2, S + I2 --> 2I2;  γ, I1 --> R1;  γ, I2 --> R2
        ε*τ2, R1 + I2 --> I12 + I2;  γ, I12 --> R
    end
    cmS = contact_model(partial; susceptible = :S)
    @test susceptible_species(cmS) == [:S]
    @test :node_contact in last.(typing(cmS).reaction_types)
end

# ---------------------------------------------------------------------------------------------
# Rates: conventions, `=>` laws, defaults, symbolic fallback
# ---------------------------------------------------------------------------------------------

@testset "rate conventions (the frequency reading of β/N)" begin
    seir = @reaction_network seir begin
        @parameters β σ γ N
        β / N, S + I --> E + I
        σ, E --> I
        γ, I --> R
    end
    # per contact (the default) warns once that β/N looks frequency-dependent
    cmp = @test_logs (:warn, "rate β/N looks frequency-dependent; pass rates = :frequency, " *
                             "population = :N") contact_model(seir)
    @test rate_convention(cmp) == PerContact()
    @test rate_value(only(contacts(cmp)).rate, Dict(:β => 1.0, :N => 4.0)) ≈ 0.25
    # the warning names the population parameter
    seirP = @reaction_network begin; β / Pop, S + I --> E + I; γ, E --> R; end
    @test_logs (:warn, r"pass rates = :frequency, population = :Pop") contact_model(
        seirP; population = :Pop)
    # frequency with a population parameter: rate k/N, k stored
    cmf = contact_model(seir; rates = :frequency, population = :N)
    @test only(contacts(cmf)).rate === :β && rate_convention(cmf) == FrequencyDependent()
    two = @reaction_network begin; 2β / (3N), S + I --> E + I; end
    @test rate_value(only(contacts(contact_model(two; rates = :frequency, population = :N))).rate,
                     Dict(:β => 0.9)) ≈ 0.6
    # a rate that is not k/N is an error
    notfreq = @reaction_network begin
        @parameters β N
        β, S + I --> E + I
    end
    @test occursin("must have the form k/N with k independent of N",
                   errtext(() -> contact_model(notfreq; rates = :frequency, population = :N)))
    sq = @reaction_network begin; β / N^2, S + I --> E + I; end
    @test occursin("must have the form k/N",
                   errtext(() -> contact_model(sq; rates = :frequency, population = :N)))
    # the population is a scalar parameter, never an array
    arrN = @reaction_network begin
        @parameters β Nv[1:2]
        β, S + I --> E + I
    end
    for (r, what) in ((:frequency, "rates = :frequency"), (:density, "rates = :density"))
        @test occursin("$(what): population = :Nv is an array parameter",
                       errtext(() -> contact_model(arrN; rates = r, population = :Nv)))
    end
    # a numeric population: β = N·rate is stored, and the provenance says so
    num = @reaction_network begin; β / 1000, S + I --> E + I; end
    cmn = contact_model(num; rates = :frequency, population = 1000)
    @test rate_value(only(contacts(cmn)).rate, Dict(:β => 0.7)) ≈ 0.7
    @test any(a -> occursin("with the number N = 1000: each rate is taken to be β/N and " *
                            "β = 1000·rate is stored", a), provenance(cmn).assumptions)
    # frequency without a population: the rate is β on population fractions
    fr = @reaction_network begin; β, S + I --> E + I; σ, E --> I; end
    cmfr = @test_logs contact_model(fr; rates = :frequency)       # no warning
    @test only(contacts(cmfr)).rate === :β && rate_convention(cmfr) == FrequencyDependent()
    # ... but a rate that contains N then is stored as it is (β/N as β), with a warning
    cmfN = @test_logs (:warn, "rate β/N contains N, but rates = :frequency was given without a " *
                              "population, so β/N itself is stored as the β of β S I/N; pass " *
                              "population = :N to read the rate as β/N and store β") contact_model(
        seir; rates = :frequency)
    @test rate_value(only(contacts(cmfN)).rate, Dict(:β => 1.0, :N => 4.0)) ≈ 0.25
    # a population has no effect with rates = :per_contact unless a rate uses it
    @test_logs (:warn, r"population = :N has no effect with rates = :per_contact") contact_model(
        fr; population = :N)
    @test_logs (:warn, r"population = 1000 has no effect with rates = :per_contact") contact_model(
        fr; population = 1000)
    @test_logs contact_model(fr)
    # density: β S I in counts, population recorded; the population need not be a parameter of
    # the network (the rate is β itself, and N is supplied at lift time), whereas :frequency
    # reads the rate as k/N and so needs the parameter N
    @test !(:N in _nm.(Catalyst.parameters(fr)))
    @test occursin("population = :N is not a parameter of the reaction system",
                   errtext(() -> contact_model(fr; rates = :frequency, population = :N)))
    cmd = contact_model(fr; rates = :density, population = :N)
    @test rate_convention(cmd) == DensityDependent(:N) && only(contacts(cmd)).rate === :β
    @test :N in rate_parameters(cmd)
    τd = only(per_contact_rates(cmd, WellMixed(5.0)))
    @test rate_value(τd, Dict(:β => 0.001, :N => 1000.0)) ≈ 0.001 * 1000 / 5
    @test rate_convention(contact_model(fr; rates = :density, population = 500)) ==
          DensityDependent(500)
    # transitions are never converted
    @test node_transitions(cmf) == node_transitions(cmp)
end

@testset "rate laws, time, numbers and symbolic rates" begin
    # `=>` with a mass-action law is reduced to its constant
    ex = @reaction_network begin
        β*S*I, S + I => 2I
        γ*I, I => R
    end
    cm = contact_model(ex)
    @test isequivalent(cm, sir_model(; τ = :β))
    @test only(contacts(cm)).rate === :β && only(node_transitions(cm)).rate === :γ
    @test count(a -> occursin("reduced to its mass-action constant", a),
                provenance(cm).assumptions) == 2
    # numeric rates stay numbers; Expr rates use RATE_OPS only
    nums = @reaction_network begin
        0.5, S + I --> 2I
        1, I --> R
        min(a, b) + log(c) - d, R --> V
        sqrt(k), V --> W
    end
    cmn = contact_model(nums)
    @test only(contacts(cmn)).rate == 0.5
    rs = [t.rate for t in node_transitions(cmn)]
    @test rs[1] == 1
    p = Dict(:a => 0.3, :b => 0.7, :c => 2.0, :d => 0.1, :k => 0.49)
    @test rate_value(rs[2], p) ≈ min(0.3, 0.7) + log(2.0) - 0.1
    @test rate_value(rs[3], p) ≈ 0.7
    @test all(r -> r isa Union{Real,Expr}, rs)
    # time-dependent rates become Exprs in :t
    tdep = @reaction_network begin; τ0 * exp(-a * t), S + I --> 2I; end
    r = only(contacts(contact_model(tdep))).rate
    @test r isa Expr && NEC._uses_time(r)
    @test rate_value(r, Dict(:τ0 => 2.0, :a => 0.5); t = 1.0) ≈ 2exp(-0.5)
    @test occursin("exp(-a*t)", NEC._rate_string(r))
    # a rate outside RATE_OPS is kept symbolic, with a note
    sy = @reaction_network begin; β * sin(ω * t), S + I --> 2I; end
    cms = contact_model(sy)
    @test only(contacts(cms)).rate isa Symbolics.Num
    @test Set(rate_parameters(cms)) == Set([:β, :ω])
    @test any(a -> occursin("kept symbolic", a), provenance(cms).assumptions)
    # ... and it evaluates (NetworkEpiCoreSymbolicsExt) and survives the reverse map
    rsy = only(contacts(cms)).rate
    @test rate_value(rsy, Dict(:β => 2.0, :ω => 1.0); t = 0.5) ≈ 2sin(0.5)
    @test isequivalent(contact_model(Catalyst.ReactionSystem(cms)), cms)
    @test !is_admissible(cms, :stochastic)                 # time-dependent: NO needs constants
    # the rate parameters come in order of first appearance and exclude t
    @test Set(rate_parameters(contact_model(tdep))) == Set([:τ0, :a])
    # a rate whose species cancel is species-free: it is replaced by its simplified form
    canc = @reaction_network canc begin
        β * (I + 1) - β * I, S + I --> 2I
        γ, I --> R
    end
    cmc = contact_model(canc)
    @test isequivalent(cmc, sir_model(; τ = :β)) && only(contacts(cmc)).rate === :β
    @test any(a -> occursin("reaction 1 (`-β*I + β*(1 + I), S + I --> 2I`): the species in the " *
                            "rate cancel; the rate is β", a), provenance(cmc).assumptions)
    # ... but a rate that depends on species after simplification is still an error
    @test occursin("rate law of `β*(1 + I), S + I --> 2I` depends on species",
                   errtext(() -> contact_model(@reaction_network(begin
                       β * (I + 1), S + I --> 2I
                   end))))
end

# ---------------------------------------------------------------------------------------------
# Time is the network's own independent variable, whatever its name (§J.4, the E25 failure
# class): a rate in `s` of an `@ivs s` network is time-dependent, never frozen as a parameter s
# ---------------------------------------------------------------------------------------------

# d/dt of the mass-action ODE of mass_action(cm) (NetworkEpiCoreSymbolicsExt) at u, p and time t;
# the variables are matched by name, time is every variable named t.
function mass_action_rhs(cm, u, p; t)
    ma = mass_action(cm)
    vals = Dict{Any,Any}()
    for x in ma.states
        vals[x] = u[_nm(x)]
    end
    for q in ma.parameters
        vals[q] = p[_nm(q)]
    end
    for f in ma.rhs, v in Symbolics.get_variables(f)
        _nm(v) === :t && (vals[v] = t)
    end
    return Dict{Symbol,Float64}(_nm(x) => _num(Symbolics.substitute(f, vals; fold = Val(true)))
                                for (x, f) in zip(ma.states, ma.rhs))
end

# A system in the independent variable s with a parameter named t (Catalyst reserves t, so its
# check is disabled), built in a function so that the names s and t stay local.
function system_with_parameter_t()
    s = only(@independent_variables s)
    @species S(s) I(s)
    @parameters β t
    return complete(ReactionSystem([Reaction(β * t, [S, I], [I], [1, 1], [2])], s, [S, I], [β, t];
                                   name = :pt, disable_forbidden_symbol_check = true))
end

# ... and one with a species named t.
function system_with_species_t()
    s = only(@independent_variables s)
    @species S(s) t(s)
    @parameters β
    return complete(ReactionSystem([Reaction(β, [S, t], [t], [1, 1], [2])], s, [S, t], [β];
                                   name = :st, disable_forbidden_symbol_check = true))
end

@testset "the independent variable is time t, whatever its name (§J.4)" begin
    rns = @reaction_network sir_s begin
        @ivs s
        β * sin(ω * s), S + I --> 2I
        γ, I --> R
    end
    rnt = @reaction_network sir_s begin
        β * sin(ω * t), S + I --> 2I
        γ, I --> R
    end
    @test _nm(Catalyst.get_iv(rns)) === :s
    cms, cmt = contact_model(rns), contact_model(rnt)
    r = only(contacts(cms)).rate
    @test r isa Symbolics.Num                              # sin is not in RATE_OPS
    # the rate depends on time: it is not admissible for NO, like the same network in t
    @test NEC._uses_time(r)
    @test !is_admissible(cms, :stochastic) && !is_admissible(cmt, :stochastic)
    @test :time_dependent in [v.type for v in admissibility(cms).violations]
    @test isequivalent(cms, cmt)
    # s is not a parameter: the parameters are those of the t network, in the same order
    @test rate_parameters(cms) == [:β, :ω, :γ] == rate_parameters(cmt)
    @test Set(_nm.(NEC.rate_parameters(r))) == Set([:β, :ω])
    p = Dict(:β => 2.0, :ω => 1.0, :γ => 0.25)
    for τt in (0.5, 2.0)
        @test rate_value(r, p; t = τt) ≈ 2sin(τt)
        @test rate_value(r, p; t = τt) ≈ rate_value(only(contacts(cmt)).rate, p; t = τt)
    end
    # instantiate refuses a time-dependent rate, instead of asking for a value of s
    @test occursin("depends on time t, so it has no constant value",
                   errtext(() -> instantiate(cms, p)))
    @test any(a -> occursin("the independent variable s of the ReactionSystem is the time t of " *
                            "the model", a), provenance(cms).assumptions)
    @test !any(a -> occursin("independent variable", a), provenance(cmt).assumptions)
    # the reverse map: t is the independent variable and s is not a constant parameter, so the
    # mass-action ODE changes with time and is that of the t network
    rs = Catalyst.ReactionSystem(cms)
    @test _nm(Catalyst.get_iv(rs)) === :t
    @test Set(_nm.(Catalyst.parameters(rs))) == Set([:β, :ω, :γ])
    u = Dict(:S => 0.6, :I => 0.3, :R => 0.1)
    for τt in (0.5, 2.0)
        ref = ma_reference(cmt, 1, u, p; t = τt)
        @test approx_dicts(catalyst_rhs(rs, u, p; t = τt), ref)
        @test approx_dicts(mass_action_rhs(cms, u, p; t = τt), ref)
    end
    @test !approx_dicts(catalyst_rhs(rs, u, p; t = 0.5), catalyst_rhs(rs, u, p; t = 2.0))
    # ... and the round trip reads it back with the parameters β, ω, γ
    rt = contact_model(rs)
    @test rate_parameters(rt) == [:β, :ω, :γ]
    @test isequivalent(rt, cms) && isequivalent(rt, cmt)

    # the same in the Expr path (RATE_OPS) and in a `=>` law
    ex_s = @reaction_network begin
        @ivs s
        τ0 * exp(-a * s), S + I --> 2I
    end
    @test only(contacts(contact_model(ex_s))).rate == :(τ0 * exp(-a * t))
    law_s = @reaction_network law begin
        @ivs s
        β * sin(ω * s) * S * I, S + I => 2I
        γ, I --> R
    end
    cml = contact_model(law_s)
    @test NEC._uses_time(only(contacts(cml)).rate) && isequivalent(cml, cmt)
    @test rate_parameters(cml) == [:β, :ω, :γ]
    # a transition rate in s, and a network whose rates do not use s
    tr_s = @reaction_network begin
        @ivs s
        τ, S + I --> 2I
        γ * (2 + sin(s)), I --> R
    end
    cmr = contact_model(tr_s)
    γr = only(node_transitions(cmr)).rate
    @test NEC._uses_time(γr) && rate_value(γr, Dict(:γ => 0.5); t = 1.0) ≈ 0.5 * (2 + sin(1.0))
    @test rate_parameters(cmr) == [:τ, :γ]
    plain_s = @reaction_network begin
        @ivs s
        τ, S + I --> 2I
        γ, I --> R
    end
    @test isequivalent(contact_model(plain_s), sir_model())
    @test is_admissible(contact_model(plain_s), :stochastic)

    # messages print the rate as written, in s (a function of s keeps its argument)
    @test occursin("rate law of `β*sin(s)*I, S + I --> 2I` depends on species",
                   errtext(() -> contact_model(@reaction_network(begin
                       @ivs s
                       β * sin(s) * I, S + I --> 2I
                   end))))
    @test occursin("rate law of `β*sin(t)*I, S + I --> 2I` depends on species",
                   errtext(() -> contact_model(@reaction_network(begin
                       β * sin(t) * I, S + I --> 2I
                   end))))

    # a parameter named t would be read as time (Catalyst reserves t, unless the check is off)
    rpt = system_with_parameter_t()
    @test _nm(Catalyst.get_iv(rpt)) === :s && :t in _nm.(Catalyst.parameters(rpt))
    @test_throws ArgumentError contact_model(rpt)
    @test errtext(() -> contact_model(rpt)) ==
          "ArgumentError: the ReactionSystem pt has a parameter named t, but a ContactModel reads " *
          "t as time (the independent variable s of the system becomes t); rename the parameter"
    @test occursin("the ReactionSystem st has a species named t, but a ContactModel reads t as time",
                   errtext(() -> contact_model(system_with_species_t())))
    # spatial independent variables: Catalyst lists x among the parameters, and a rate in x
    # would be read as a rate with a constant parameter x
    rnx = @reaction_network spatial begin
        @ivs t x
        @species S(t, x) I(t, x)
        β * exp(-x), S + I --> 2I
    end
    @test :x in _nm.(Catalyst.parameters(rnx))
    @test_throws ArgumentError contact_model(rnx)
    @test occursin("the ReactionSystem spatial has the spatial independent variable x; a " *
                   "ContactModel is a model in time only", errtext(() -> contact_model(rnx)))
    # a time-dependent parameter is not a constant of the model
    rnd = @reaction_network begin
        @discretes βd(t)
        βd, S + I --> 2I
    end
    @test_throws ArgumentError contact_model(rnd)
    @test occursin("`βd, S + I --> 2I`: the rate uses the time-dependent parameter βd(t) " *
                   "(reaction 1). The parameters of a ContactModel are constants",
                   errtext(() -> contact_model(rnd)))
end

@testset "defaults are read through initial_conditions" begin
    rn = @reaction_network sir begin
        @parameters τ = 0.2 γ = 0.25 ω
        @species S(t) = 0.99 I(t) = 0.01
        τ, S + I --> 2I
        γ, I --> R
    end
    @test length(MTKB.initial_conditions(rn)) >= 2     # the MTK source of the defaults
    cm = contact_model(rn)
    @test parameter_defaults(cm) == Dict(:τ => 0.2, :γ => 0.25)
    @test any(a -> occursin("initial values of S, I in the ReactionSystem are not used", a),
              provenance(cm).assumptions)
    # instantiate uses them
    @test [c.rate for c in contacts(instantiate(cm))] == [0.2]
    # defaults given in terms of other parameters (bindings) are resolved numerically
    rb = @reaction_network begin
        @parameters τ = 0.2 γ = 2τ
        τ, S + I --> 2I
        γ, I --> R
    end
    @test parameter_defaults(contact_model(rb)) == Dict(:τ => 0.2, :γ => 0.4)
    # defaults that are not numbers are left out, with a note
    ru = @reaction_network begin
        @parameters τ γ = 2τ
        τ, S + I --> 2I
        γ, I --> R
    end
    cmu = contact_model(ru)
    @test isempty(parameter_defaults(cmu))
    @test any(a -> occursin("defaults of γ do not evaluate to numbers", a),
              provenance(cmu).assumptions)
    # no defaults
    @test isempty(parameter_defaults(contact_model(@reaction_network(begin τ, S + I --> 2I end))))
end

# ---------------------------------------------------------------------------------------------
# Namespacing
# ---------------------------------------------------------------------------------------------

@testset "namespaced species survive" begin
    t = Catalyst.default_t()
    pop1 = @network_component pop1 begin
        @parameters τ = 0.3
        τ, S + I --> 2I
        γ, I --> R
    end
    pop2 = @network_component pop2 begin
        τ, S + I --> 2I
        γ, I --> R
    end
    @parameters τx
    cross = Reaction(τx, [pop1.S, pop2.I], [pop1.I, pop2.I])
    @named two = ReactionSystem([cross], t; systems = [pop1, pop2])
    two = complete(two)
    cm = contact_model(two)
    s(x) = Symbol(x)
    @test Set(species_names(cm)) == Set(s.(["pop1₊S", "pop1₊I", "pop1₊R", "pop2₊S", "pop2₊I",
                                             "pop2₊R"]))
    @test susceptible_species(cm) == [s("pop1₊S"), s("pop2₊S")]
    @test Contact(s("pop1₊S"), s("pop2₊I"), s("pop1₊I"), :τx) in contacts(cm)
    @test Contact(s("pop1₊S"), s("pop1₊I"), s("pop1₊I"), s("pop1₊τ")) in contacts(cm)
    @test Set(rate_parameters(cm)) == Set([:τx, s("pop1₊τ"), s("pop1₊γ"), s("pop2₊τ"),
                                           s("pop2₊γ")])
    @test parameter_defaults(cm) == Dict(s("pop1₊τ") => 0.3)
    # two susceptible classes on an untyped network: EB needs strata; T_EB otherwise
    @test typing(cm).theory === :T_EB
    @test !is_admissible(cm, :edge_based) && is_admissible(cm, :pairwise)
    # and they survive the reverse map
    rt = contact_model(Catalyst.ReactionSystem(cm))
    @test isequivalent(rt, cm) && species_names(rt) == species_names(cm)
    @test Symbol.(Symbolics.getname.(Catalyst.species(Catalyst.ReactionSystem(cm)))) ==
          species_names(cm)
end

# ---------------------------------------------------------------------------------------------
# Reverse maps
# ---------------------------------------------------------------------------------------------

@testset "round trip contact_model(ReactionSystem(cm)) ≅ cm" begin
    extra = [
        (:sir_def, ContactModel(:sir_def; contacts = [Contact(:S, :I, :I, :τ)],
                                transitions = [NodeTransition(:I, :R, :γ)],
                                defaults = Dict(:τ => 0.2, :γ => 0.25, :unused => 3.0))),
        (:seir_dd, ContactModel(:seir_dd; contacts = [Contact(:S, :I, :E, :β)],
                                transitions = [NodeTransition(:E, :I, :σ),
                                               NodeTransition(:I, :R, :γ)],
                                convention = DensityDependent(:N), defaults = Dict(:N => 1e4))),
        (:seir_dd_num, ContactModel(:seir_dd_num; contacts = [Contact(:S, :I, :E, :β)],
                                    transitions = [NodeTransition(:E, :I, :σ)],
                                    convention = DensityDependent(2500.0))),
        (:numbers, ContactModel(:numbers; contacts = [Contact(:S, :I, :I, 0.4)],
                                transitions = [NodeTransition(:I, :R, 0.25)])),
        (:susR, ContactModel(:susR; contacts = [Contact(:S, :I, :I, :τ)],
                             transitions = [NodeTransition(:I, :R, :γ)], susceptible = [:S, :R])),
        (:idle, ContactModel(:idle; contacts = [Contact(:S, :I, :I, :τ)],
                             transitions = [NodeTransition(:I, :R, :γ)],
                             species = [:S, :I, :R, :Z])),
        # no contacts: the convention is kept in the system metadata (the reactions carry none)
        (:nc_fd, ContactModel(:nc_fd; transitions = [NodeTransition(:E, :I, :σ),
                                                     NodeTransition(:I, :R, :γ)],
                              convention = FrequencyDependent())),
        (:nc_dd, ContactModel(:nc_dd; transitions = [NodeTransition(:E, :I, :σ)],
                              convention = DensityDependent(:N), defaults = Dict(:N => 100.0))),
        # a DensityDependent(:N) contact rate that contains N: the written rate (β/N)·N is
        # simplified to β by Symbolics, and β/N is recovered as rate/N
        (:dd_betaN, ContactModel(:dd_betaN; contacts = [Contact(:S, :I, :I, :(β / N))],
                                 transitions = [NodeTransition(:I, :R, :γ)],
                                 convention = DensityDependent(:N))),
    ]
    models = vcat([(id, direct) for (id, direct, _, _) in corpus], extra)
    for (id, cm) in models
        @testset "$id" begin
            rs = Catalyst.ReactionSystem(cm)
            @test rs isa Catalyst.ReactionSystem && nameof(rs) === nameof(cm)
            @test MTKB.iscomplete(rs)
            rt = contact_model(rs)
            @test isequivalent(rt, cm)
            @test species_names(rt) == species_names(cm)
            @test susceptible_species(rt) == susceptible_species(cm)
            @test rate_convention(rt) == rate_convention(cm)
            @test [c.layer for c in contacts(rt)] == [c.layer for c in contacts(cm)]
            @test parameter_defaults(rt) == parameter_defaults(cm)
            @test species_labels(rt) == species_labels(cm)
            @test typing(rt).reaction_types == typing(cm).reaction_types
        end
    end
    @test any(m -> !isempty(species_labels(last(m))), models)     # labels are exercised

    # SpeciesLabels are carried as species metadata, so admissibility on a typed network is kept
    st = strata([:a, :b]; sizes = [0.5, 0.5])
    sa = stratify(sir_model(), st)
    @test !isempty(species_labels(sa))
    net = unstructured(ConfigurationNetwork(RegularDegree(6)), st)
    rsa = Catalyst.ReactionSystem(sa)
    Sa = first(s for s in Catalyst.species(rsa) if _nm(s) === first(species_names(sa)))
    @test Symbolics.getmetadata(Symbolics.unwrap(Sa), SpeciesLabel, nothing) ==
          species_labels(sa)[first(species_names(sa))]
    rta = contact_model(rsa)
    @test isequivalent(rta, sa) && species_labels(rta) == species_labels(sa)
    @test is_admissible(sa, :edge_based; network = net)
    @test is_admissible(rta, :edge_based; network = net)
    @test admissibility(rta, net).backends == admissibility(sa, net).backends
    @test any(a -> occursin("read from the species metadata SpeciesLabel", a),
              provenance(rta).assumptions)

    # an explicit species order survives (the system metadata); IR order is the fallback
    ord = ContactModel(:ord; contacts = [Contact(:S, :I, :E, :τ)],
                       transitions = [NodeTransition(:E, :I, :σ), NodeTransition(:I, :R, :γ)],
                       species = [:S, :I, :E, :R])
    @test species_names(ord) == [:S, :I, :E, :R]
    rso = Catalyst.ReactionSystem(ord)
    @test Symbol.(Symbolics.getname.(Catalyst.species(rso))) == [:S, :I, :E, :R]
    rto = contact_model(rso)
    @test species_names(rto) == [:S, :I, :E, :R] && isequivalent(rto, ord)
    @test any(a -> occursin("species order read from the system metadata", a),
              provenance(rto).assumptions)
    # written without the metadata (a DSL network) or composed, the IR order is used
    @test species_names(contact_model(@reaction_network(ord, begin
        τ, S + I --> E + I; σ, E --> I; γ, I --> R
    end))) == [:S, :E, :I, :R]
    @named outer = ReactionSystem(Catalyst.Reaction[], Catalyst.default_t();
                                  systems = [Catalyst.ReactionSystem(ord; complete = false)])
    @test species_names(contact_model(complete(outer))) == Symbol.(["ord₊S", "ord₊E", "ord₊I",
                                                                    "ord₊R"])
    # the metadata written by the reverse map
    rs = Catalyst.ReactionSystem(corpus[findfirst(c -> c[1] === :sir_mpx, corpus)][2])
    rx1 = first(Catalyst.reactions(rs))
    @test Catalyst.getmetadata(rx1, :contact) === true
    @test Catalyst.getmetadata(rx1, :layer) === :home
    dd = extra[2][2]
    rxd = first(Catalyst.reactions(Catalyst.ReactionSystem(dd)))
    @test Catalyst.getmetadata(rxd, :rate_convention) === :density
    @test Catalyst.getmetadata(rxd, :population) === :N
    # conventions in the metadata and the keywords must agree
    rsf = Catalyst.ReactionSystem(corpus[findfirst(c -> c[1] === :seir_fd, corpus)][2])
    @test rate_convention(contact_model(rsf; rates = :frequency)) == FrequencyDependent()
    @test occursin("rates = :density contradicts the reaction metadata [rate_convention = " *
                   ":frequency]",
                   errtext(() -> contact_model(rsf; rates = :density, population = :N)))
    mdpop = @reaction_network begin
        β, S + I --> E + I, [rate_convention = :frequency, population = :N]
    end
    @test occursin("[rate_convention = :frequency] takes no [population = …]",
                   errtext(() -> contact_model(mdpop)))
    mdmix = @reaction_network begin
        β, S + I --> E + I, [rate_convention = :frequency]
        β, S + A --> E + A
    end
    @test occursin("the contacts carry different [rate_convention = …, population = …] metadata",
                   errtext(() -> contact_model(mdmix)))
    mdbad = @reaction_network begin
        β, S + I --> E + I, [rate_convention = :density, population = :N]
        @parameters N
    end
    @test occursin("is not of that form", errtext(() -> contact_model(mdbad)))
    # the system metadata records the convention; it decides only for a model without contacts
    # and default keywords (hand-written density metadata is still checked for its form above)
    rsnc = Catalyst.ReactionSystem(extra[findfirst(e -> e[1] === :nc_fd, extra)][2])
    @test rate_convention(contact_model(rsnc)) == FrequencyDependent()
    @test any(a -> occursin("rate convention FrequencyDependent() read from the system metadata",
                            a), provenance(contact_model(rsnc)).assumptions)
    @test rate_convention(contact_model(rsnc; rates = :density, population = :N)) ==
          DensityDependent(:N)
    rsdd = Catalyst.ReactionSystem(extra[findfirst(e -> e[1] === :dd_betaN, extra)][2])
    # (the written rate is (β/N)·N, which Symbolics simplifies to β)
    @test _nm.(collect(Symbolics.get_variables(Catalyst.reactions(rsdd)[1].rate))) == [:β]
    @test only(contacts(contact_model(rsdd))).rate == :(β / N)
    # a hand-written system (no system metadata) with the same reactions: its rate β is not of
    # the declared form β'·N, which catches a rate written in counts by mistake
    nometa = complete(ReactionSystem(Catalyst.reactions(rsdd), Catalyst.get_iv(rsdd),
                                     Catalyst.species(rsdd), Catalyst.parameters(rsdd);
                                     name = :nometa))
    @test occursin("β is not of that form", errtext(() -> contact_model(nometa)))

    # the reverse map recreates parameters by name, so a symbolic rate may use only scalar
    # parameters and time: an element of an array, a function of time, or two variables with one
    # name would be bound to the wrong parameter (E25). The first two are rejected by the
    # ContactModel constructor itself (the NEC steward's change on the WP9fix request), so no
    # model with such a rate reaches a back end
    @parameters karr[1:2]
    @test errtext(() -> ContactModel(:arr; contacts = [Contact(:S, :I, :I, karr[1])],
                                     transitions = [NodeTransition(:I, :R, karr[2])])) ==
          "ArgumentError: ContactModel :arr: the rate of `S_I_to_I` uses karr[1] (an element of " *
          "the array karr); a symbolic rate may use only scalar parameters and time t (write " *
          "k[1] as a scalar parameter such as k1, and a time-dependent rate as an expression in " *
          "t, e.g. β0*exp(-a*t))"
    tt = Catalyst.default_t()
    βt = only(@variables βt(tt))
    @test occursin("the rate of `S_I_to_I` uses βt(t) (a function of t); a symbolic rate may " *
                   "use only scalar parameters and time t",
                   errtext(() -> ContactModel(:ft; contacts = [Contact(:S, :I, :I, 2 * βt)],
                                              transitions = [NodeTransition(:I, :R, :γ)])))
    @test occursin("the DensityDependent population size uses karr[1]",
                   errtext(() -> ContactModel(:ddarr; contacts = [Contact(:S, :I, :I, :β)],
                                              convention = DensityDependent(karr[1]))))
    # time itself and scalar parameters are fine, also inside a time-dependent rate
    cmtd = ContactModel(:td; contacts = [Contact(:S, :I, :I, 2 * only(@parameters kt) * exp(-tt))],
                        transitions = [NodeTransition(:I, :R, :γ)])
    @test NEC._uses_time(only(contacts(cmtd)).rate)
    βr = only(@parameters β)
    βi = only(@variables β::Int)
    @test !isequal(βr, βi)
    cmdup = ContactModel(:dup; contacts = [Contact(:S, :I, :I, βr + 2βi)],
                         transitions = [NodeTransition(:I, :R, :γ)])
    @test occursin("uses two different variables named β (Int64 and Real)",
                   errtext(() -> Catalyst.ReactionSystem(cmdup)))
    # a scalar symbolic rate is rebound to the new parameter of that name
    @parameters ksc
    cmsc = ContactModel(:sc; contacts = [Contact(:S, :I, :I, 2 * ksc)],
                        transitions = [NodeTransition(:I, :R, :γ)])
    rtsc = contact_model(Catalyst.ReactionSystem(cmsc))
    @test isequivalent(rtsc, cmsc) && Set(rate_parameters(rtsc)) == Set([:ksc, :γ])

    # κ = 5 on a PerContact model reads back as the scaled model c_5 P
    rt5 = contact_model(Catalyst.ReactionSystem(sir_model(); κ = 5))
    @test isequivalent(rt5, scale_contact_rates(sir_model(), 5))
    @test !MTKB.iscomplete(Catalyst.ReactionSystem(sir_model(); complete = false))
    @test nameof(Catalyst.ReactionSystem(sir_model(); name = :other)) === :other
    @test_throws ArgumentError Catalyst.ReactionSystem(sir_model(); κ = -1)
    @test occursin("names a species", errtext(() -> Catalyst.ReactionSystem(sir_model(); κ = :S)))
    @test_throws ArgumentError Catalyst.ReactionSystem(sir_model(); κ = "5")
    # κ must be a new name: κ = :τ would square τ (and a default-only parameter would bind κ)
    @test_throws ArgumentError Catalyst.ReactionSystem(sir_model(); κ = :τ)
    @test occursin("κ = :τ is already a parameter of :sir",
                   errtext(() -> Catalyst.ReactionSystem(sir_model(); κ = :τ)))
    @test occursin("κ = :unused is already a parameter",
                   errtext(() -> Catalyst.ReactionSystem(extra[1][2]; κ = :unused)))
    @test occursin("κ = :N is already a parameter",
                   errtext(() -> Catalyst.ReactionSystem(dd; κ = :N)))

    # DensityDependent(N) with a number N: the written rate β·N is rounded (0.1·3.0 =
    # 0.30000000000000004), and the recorded [ir_rate = β] reads β back exactly
    for (r, back) in ((0.1, 0.1), (0.3, 0.3), (1, 1), (:(0.1 * β), :(0.1 * β)))
        cmn = ContactModel(:ddn; contacts = [Contact(:S, :I, :I, r)],
                           transitions = [NodeTransition(:I, :R, :γ)],
                           convention = DensityDependent(3.0))
        rsn = Catalyst.ReactionSystem(cmn)
        @test Catalyst.getmetadata(first(Catalyst.reactions(rsn)), :ir_rate) == r
        rtn = contact_model(rsn)
        @test only(contacts(rtn)).rate == back
        @test isequivalent(rtn, cmn) && rate_convention(rtn) == DensityDependent(3.0)
    end
    @test 0.1 * 3.0 / 3.0 != 0.1                  # (why the metadata is needed)
    # the recorded rate is used only when it reproduces the rate of the reaction: after the
    # rate is edited, rate/N is read
    rsn = Catalyst.ReactionSystem(ContactModel(:ddn; contacts = [Contact(:S, :I, :I, 0.1)],
                                               convention = DensityDependent(3.0)))
    rx = only(Catalyst.reactions(rsn))
    edited = Catalyst.Reaction(0.6, rx.substrates, rx.products, rx.substoich, rx.prodstoich;
                               metadata = rx.metadata)
    rse = complete(ReactionSystem([edited], Catalyst.get_iv(rsn), Catalyst.species(rsn),
                                  Catalyst.parameters(rsn); name = :ddn,
                                  metadata = MTKB.get_metadata(rsn)))
    @test Catalyst.getmetadata(only(Catalyst.reactions(rse)), :ir_rate) == 0.1
    @test only(contacts(contact_model(rse))).rate ≈ 0.2
    # PerContact and FrequencyDependent contacts, and a symbolic N, need no such record
    @test !Catalyst.hasmetadata(first(Catalyst.reactions(Catalyst.ReactionSystem(dd))), :ir_rate)
    @test !Catalyst.hasmetadata(first(Catalyst.reactions(Catalyst.ReactionSystem(sir_model()))),
                                :ir_rate)

    # a default named like a species or t is not a parameter value: the reverse maps would drop
    # it silently, so it is an error, and since the NEC steward's change (WP9fix request) already
    # at construction, for ContactModel and ReactionNetworkData alike
    @test errtext(() -> ContactModel(:defR; contacts = [Contact(:S, :I, :I, :τ)],
                                     transitions = [NodeTransition(:I, :R, :γ)],
                                     defaults = Dict(:τ => 0.2, :R => 1.0))) ==
          "ArgumentError: ContactModel :defR: `defaults` are parameter values by name, but R (a " *
          "species) is not a parameter; initial states come from a SeedSpec (e.g. " *
          "SeedFraction(:I => 0.01)), so remove it"
    @test occursin("ContactModel :defSt: `defaults` are parameter values by name, but S (a " *
                   "species), t (time) are not a parameter",
                   errtext(() -> ContactModel(:defSt; contacts = [Contact(:S, :I, :I, :τ)],
                                              defaults = Dict(:τ => 0.2, :t => 1.0, :S => 0.9))))
    @test occursin("ReactionNetworkData :dR: `defaults` are parameter values by name, but Y (a " *
                   "species) is not a parameter",
                   errtext(() -> ReactionNetworkData(:dR, [:X, :Y],
                                                     [GeneralReaction([:X => 1], [:Y => 1], :k)];
                                                     defaults = Dict(:k => 0.3, :Y => 1.0))))
    # parameter defaults (also of parameters no rate uses) are kept and written
    cmP = ContactModel(:defP; contacts = [Contact(:S, :I, :I, :τ)],
                       transitions = [NodeTransition(:I, :R, :γ)],
                       defaults = Dict(:τ => 0.2, :γ => 0.25))
    @test parameter_defaults(contact_model(Catalyst.ReactionSystem(cmP))) ==
          Dict(:τ => 0.2, :γ => 0.25)
end

@testset "ReactionSystem(cm; κ) is the mass-action model MA(c_κ P)" begin
    rng = Random.Xoshiro(20260926)
    extra = [ContactModel(:seir_dd; contacts = [Contact(:S, :I, :E, :β)],
                          transitions = [NodeTransition(:E, :I, :σ), NodeTransition(:I, :R, :γ)],
                          convention = DensityDependent(:N)),
             ContactModel(:dd_betaN; contacts = [Contact(:S, :I, :I, :(β / N))],
                          transitions = [NodeTransition(:I, :R, :γ)],
                          convention = DensityDependent(:N))]
    models = vcat([direct for (_, direct, _, _) in corpus], extra)
    # mass_action(::ContactModel) is NetworkEpiCoreSymbolicsExt's (WP10)
    has_ma = applicable(mass_action, sir_model())
    @test has_ma
    # a symbolic κ must be a new parameter name (suscontact and susinfector have a rate κ)
    @test occursin("κ = :κ is already a parameter of :suscontact",
                   errtext(() -> Catalyst.ReactionSystem(
                       corpus[findfirst(c -> c[1] === :suscontact, corpus)][2]; κ = :κ)))
    for cm in models, κ in (1, 5.0, :κnet)
        @testset "$(nameof(cm)), κ = $(κ)" begin
            rs = Catalyst.ReactionSystem(cm; κ)
            u, p = random_point(cm, rng; extra = κ isa Symbol ? [κ] : Symbol[])
            κv = κ isa Symbol ? p[κ] : κ
            ref = ma_reference(cm, κv, u, p)
            @test approx_dicts(catalyst_rhs(rs, u, p), ref)
            # the Catalyst ODE of the reverse map agrees with NEC's mass_action (Symbolics ext)
            if has_ma
                ma = mass_action(cm; κ)
                vals = Dict{Any,Any}()
                for x in ma.states
                    vals[x] = u[_nm(x)]
                end
                for q in ma.parameters
                    vals[q] = p[_nm(q)]
                end
                for f in ma.rhs, v in Symbolics.get_variables(f)   # time, by name
                    _nm(v) === :t && (vals[v] = 0.3)
                end
                got = Dict{Symbol,Float64}(_nm(x) => _num(Symbolics.substitute(f, vals;
                                                                             fold = Val(true)))
                                           for (x, f) in zip(ma.states, ma.rhs))
                @test approx_dicts(got, ref)
            end
        end
    end
    # the frequency-dependent model is the same mass-action model for every κ
    fd = corpus[findfirst(c -> c[1] === :seir_fd, corpus)][2]
    u, p = random_point(fd, rng)
    @test approx_dicts(catalyst_rhs(Catalyst.ReactionSystem(fd; κ = 1), u, p),
                       catalyst_rhs(Catalyst.ReactionSystem(fd; κ = 8.0), u, p))
end

@testset "ReactionSystem(::ReactionNetworkData)" begin
    rng = Random.Xoshiro(7)
    # the edge doubling D_μ of SEAIR (branching, two infectors)
    d = edge_doubling(seair_model(), 5.0)
    rs = Catalyst.ReactionSystem(d)
    @test Set(Symbol.(Symbolics.getname.(Catalyst.species(rs)))) == Set(species_names(d))
    @test length(Catalyst.reactions(rs)) == length(d.reactions)
    @test MTKB.iscomplete(rs) && nameof(rs) === nameof(d)
    u = Dict{Symbol,Float64}(x => 0.05 + 0.4 * rand(rng) for x in species_names(d))
    p = Dict{Symbol,Float64}(n => 0.2 + 0.6 * rand(rng)
                             for n in NEC._parameter_name.(rate_parameters(d)))
    ref = Dict{Symbol,Float64}(x => 0.0 for x in species_names(d))
    for r in d.reactions
        a = rate_value(r.rate, p) * prod(u[x]^n for (x, n) in r.substrates; init = 1.0)
        for (x, n) in r.substrates
            ref[x] -= n * a
        end
        for (x, n) in r.products
            ref[x] += n * a
        end
    end
    @test approx_dicts(catalyst_rhs(rs, u, p), ref)
    # a power-law (`=>`) rate law, stoichiometry 2, a birth and an observable
    d2 = ReactionNetworkData(:plaw, [:X, :Y],
                             [GeneralReaction([:X => 1], [:Y => 2], :(k * X^0.5 * Y);
                                              only_use_rate = true),
                              GeneralReaction(Pair{Symbol,Int}[], [:X => 1], :b),
                              GeneralReaction([:Y => 1], Pair{Symbol,Int}[], :δ)];
                             defaults = Dict(:k => 0.3), observables = Dict(:Tot => [:X, :Y]))
    rs2 = Catalyst.ReactionSystem(d2)
    u2 = Dict(:X => 0.4, :Y => 0.3)
    p2 = Dict(:k => 0.3, :b => 0.1, :δ => 0.2)
    law = 0.3 * 0.4^0.5 * 0.3
    @test approx_dicts(catalyst_rhs(rs2, u2, p2), Dict(:X => -law + 0.1, :Y => 2law - 0.2 * 0.3))
    @test Catalyst.reactions(rs2)[1].only_use_rate
    @test length(MTKB.observed(rs2)) == 1
    @test Symbol(Symbolics.getname(MTKB.observed(rs2)[1].lhs)) === :Tot
    @test Dict(Symbol(Symbolics.getname(k)) => _num(v)
               for (k, v) in MTKB.initial_conditions(rs2)) == Dict(:k => 0.3)
    bad = ReactionNetworkData(:bad, [:X], [GeneralReaction([:X => 1], Pair{Symbol,Int}[], :δ)];
                              observables = Dict(:X => [:X, :X]))
    @test_throws ArgumentError Catalyst.ReactionSystem(bad)
    # a symbolic rate law may use species X(t) and scalar parameters, but not array elements
    tt = Catalyst.default_t()
    Xs = only(@species X(tt))
    kx = only(@parameters kx)
    d3 = ReactionNetworkData(:sym, [:X, :Y],
                             [GeneralReaction([:X => 1], [:Y => 1], kx * Xs^0.5;
                                              only_use_rate = true)])
    rs3 = Catalyst.ReactionSystem(d3)
    @test approx_dicts(catalyst_rhs(rs3, Dict(:X => 0.49, :Y => 0.2), Dict(:kx => 0.3)),
                       Dict(:X => -0.3 * 0.7, :Y => 0.3 * 0.7))
    @parameters ka[1:2]
    d4 = ReactionNetworkData(:arr, [:X, :Y],
                             [GeneralReaction([:X => 1], [:Y => 1], ka[1] * Xs;
                                              only_use_rate = true)])
    @test occursin("uses ka[1], an element of the array ka",
                   errtext(() -> Catalyst.ReactionSystem(d4)))
    Zs = only(@species Z(tt))
    d5 = ReactionNetworkData(:other, [:X, :Y],
                             [GeneralReaction([:X => 1], [:Y => 1], kx * Xs * Zs;
                                              only_use_rate = true)])
    @test occursin("uses Z(t), which is not a species, a scalar parameter or time",
                   errtext(() -> Catalyst.ReactionSystem(d5)))
end
