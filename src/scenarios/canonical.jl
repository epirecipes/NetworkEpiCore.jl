# Owner: WP12 (DESIGN_NetworkEpiCore.md §E.3; work package in §G.2).
#
# The canonical scenario list of §E.3, plus the derived variants it calls for (Erlang n = 2, 5;
# the N-scaling sizes N = 10³ and 10⁵) and the stretch scenarios (degree-correlated networks,
# dormant contacts / DVD, MFSH, clustered SEIR and SEAIR, population multitype pairwise), each
# tagged so that later work packages can generate and use their summaries.
#
# Anchors (§E.2): γ = 1/4 and τ = 1/6, so T = 0.4; with excess degree 5, R₀ = 2 and
# r = τ(κ_ex − 1) − γ = 5/12. The time grid is t0:0.25:t1 (§E.2), except for the long SEIR/SEAIR
# (step 0.5), SIRS (step 1) and small-seed (step 0.5: their aligned and unaligned summaries are
# written side by side) spans, which keep the committed summaries under 200 kB, and the fast
# (γ = 1) scenarios (step 0.1). Every expected value is computed here by NetworkEpiCore functions
# (see EXPECTED_QUANTITIES), never typed. Parameters obtained with `calibrate` are rounded to 10
# significant digits, so that a last-bit difference in a transcendental function on another
# platform or Julia version cannot change the scenario hash.
#
# The list is built on first access to the registry (scenarios/registry.jl).

const _ANCHOR_τ = 1 / 6
const _ANCHOR_γ = 1 / 4

# Expected quantities by family.
const _EXPECT_CONFIG = (:R0, :T, :r, :final_size, :mean_degree, :excess_degree, :closure_constant)
const _EXPECT_TYPED = (:R0, :r, :final_size, :mean_degree)
const _EXPECT_CLUSTERED = (:mean_degree, :excess_degree, :clustering)
const _EXPECT_NE = (:R0, :T, :r, :mean_degree, :excess_degree)

_calibrated(x::Real) = round(Float64(x); sigdigits = 10)

# The canonical conditioning rule: SIR-type (T_EB) models are conditioned on a major outbreak,
# models with an arrow back into Sus (SIS, SIRS) on survival.
_canonical_condition(cm::ContactModel) =
    typing(cm).theory === :T_EB ? MajorOutbreak(0.05) : Survival()

function _canonical(id::Symbol, title::AbstractString; model, network, params, initial, tspan,
                    backends, tags, expected, notes::AbstractString = "", tstep::Real = 0.25,
                    N::Integer = 10_000,
                    nsims::Integer = 200, graphs = :per_run, algorithm::Symbol = :next_reaction,
                    align = NoAlignment())
    cm = contact_model(model)
    sim = SimConfig(; N, nsims, graphs, algorithm, condition = _canonical_condition(cm), align)
    return Scenario(id; title, model = cm, network, params, initial, tspan, tstep, sim,
                    backends = Dict{Symbol,Symbol}(backends), tags = vcat([:canonical], tags),
                    expected, notes)
end

# A derived variant registered under an explicit id, with a title suffix.
_variant(sc::Scenario, id::Symbol, suffix::AbstractString, tags; kw...) =
    derive(sc; id, title = string(sc.title, " ", suffix),
           tags = unique!(vcat(sc.tags, tags, [:derived])), kw...)

const _EXACT_PT = (:edge_based => :exact_limit, :pairwise_const => :exact_limit,
                   :pgf_closure => :exact_limit)
const _EXACT_NON_PT = (:edge_based => :exact_limit, :pgf_closure => :exact_limit,
                       :pairwise_const => :biased)

"""
    _canonical_scenarios() -> Vector{Scenario}

Build the canonical list (§E.3) in registry order. Called once, by the registry.
"""
function _canonical_scenarios()
    out = Scenario[]
    add!(sc) = (push!(out, sc); sc)
    sir = sir_model()
    anchor = Dict(:τ => _ANCHOR_τ, :γ => _ANCHOR_γ)
    seedI = SeedFraction(:I => 0.01)
    both = [:ebm, :nbm]

    # ---- configuration networks with excess degree 5 (R₀ = 2, r = 5/12) ----------------------
    add!(_canonical(:sir_reg6, "SIR on a 6-regular configuration network";
        model = sir, network = ConfigurationNetwork(RegularDegree(6)), params = anchor,
        initial = seedI, tspan = (0, 60),
        backends = (_EXACT_PT..., :pairwise_bernoulli => :exact_limit),
        tags = vcat(both, [:sir, :configuration, :pt]), expected = _EXPECT_CONFIG,
        notes = "Poisson type with closure constant K = 5/6, so the Bernoulli / constant-K " *
                "pairwise model equals the edge-based model. Same R₀ and r as :sir_pois5 and " *
                ":sir_nb4, larger final size."))
    pois5 = add!(_canonical(:sir_pois5, "SIR on a Poisson(5) configuration network";
        model = sir, network = ConfigurationNetwork(PoissonDegree(5)), params = anchor,
        initial = seedI, tspan = (0, 60), backends = _EXACT_PT,
        tags = vcat(both, [:sir, :configuration, :pt, :n_scaling]), expected = _EXPECT_CONFIG,
        notes = "The Poisson isomorphism (EB ≅ MA(5τ, γ + τ) on (S, φ_I), Rempała's quotient) " *
                "and constant-K pairwise with K = 1. Also run at N = 10³ and 10⁵ (N-scaling)."))
    add!(_canonical(:sir_nb4, "SIR on a negative binomial (mean 4, variance 8) configuration network";
        model = sir, network = ConfigurationNetwork(NegBinDegree(mean = 4, var = 8)),
        params = anchor, initial = seedI, tspan = (0, 60), backends = _EXACT_PT,
        tags = vcat(both, [:sir, :configuration, :pt]), expected = _EXPECT_CONFIG,
        notes = "Poisson type with K = 5/4; P(k = 0) = 0.0625."))
    bim = add!(_canonical(:sir_bim, "SIR on a bimodal {2, 10} configuration network";
        model = sir, network = ConfigurationNetwork(EmpiricalDegree(2 => 5 / 6, 10 => 1 / 6)),
        params = anchor, initial = seedI, tspan = (0, 60), backends = _EXACT_NON_PT,
        tags = vcat(both, [:sir, :configuration, :non_pt, :n_scaling]), expected = _EXPECT_CONFIG,
        notes = "The non-Poisson-type demonstration: constant-K pairwise (K = 3/2) is biased " *
                "(|ΔR∞| ≈ 0.034, pinned), the PGF closure is exact. N-scaling."))
    pl_net = ConfigurationNetwork(PowerLawDegree(2.5; kmin = 2, kmax = 60))
    τ_pl = _calibrated(calibrate(sir, pl_net, anchor; target = :R0 => 2.0, vary = :τ)[:τ])
    pl = add!(_canonical(:sir_pl, "SIR on a truncated power-law (α = 2.5, k = 2…60) configuration network";
        model = sir, network = pl_net, params = Dict(:τ => τ_pl, :γ => _ANCHOR_γ),
        initial = seedI, tspan = (0, 80), backends = _EXACT_NON_PT,
        tags = vcat(both, [:sir, :configuration, :non_pt, :n_scaling]), expected = _EXPECT_CONFIG,
        notes = "Heavy tail (mean 3.985, excess 8.663); τ calibrated to R₀ = 2. Constant-K " *
                "pairwise (K = 2.17) is biased (|ΔR∞| ≈ 0.068, pinned); N-scaling shows the " *
                "plateau. kmax = 60 stays below the simple-graph cutoff √(N⟨k⟩) (≈ 200 at " *
                "N = 10⁴, ≈ 63 at N = 10³)."))

    # ---- well mixed: the unit of the lift ---------------------------------------------------
    add!(_canonical(:sir_wm5, "SIR, well mixed with κ = 5 (mass action β = 1/2)";
        model = sir, network = WellMixed(5), params = Dict(:τ => 1 / 10, :γ => _ANCHOR_γ),
        initial = seedI, tspan = (0, 60), algorithm = :mass_action,
        backends = (:edge_based => :exact_limit, :mean_field => :exact_limit,
                    :individual => :exact_limit, :mass_action => :exact_limit),
        tags = vcat(both, [:sir, :well_mixed, :unit_law]), expected = _EXPECT_TYPED,
        notes = "EB on WellMixed(κ) is mass action MA(κτ, γ) (unit law M1), as are the " *
                "mean-field closure and the individual-based model on K_N; simulated with " *
                "MassActionSSA. The hub for every road back to mass action (dense ladder, " *
                "neighbour exchange on a regular base)."))

    # ---- disease structure on Poisson(5) ----------------------------------------------------
    add!(_canonical(:seir_pois5, "SEIR on a Poisson(5) configuration network";
        model = seir_model(), network = ConfigurationNetwork(PoissonDegree(5)),
        params = Dict(:τ => _ANCHOR_τ, :σ => 1 / 5, :γ => _ANCHOR_γ),
        initial = SeedFraction(:E => 0.01), tspan = (0, 150), tstep = 0.5, backends = _EXACT_PT,
        tags = vcat(both, [:seir, :configuration, :pt]), expected = _EXPECT_CONFIG,
        notes = "Seeded in the entry state E (the default seeding rule). R₀ = 2."))
    erl3 = add!(_canonical(:sir_erl3_pois5, "SIR with a 3-stage Erlang infectious period on Poisson(5)";
        model = erlang_stages(sir, :I, 3), network = ConfigurationNetwork(PoissonDegree(5)),
        params = anchor, initial = SeedFraction(:I_1 => 0.01), tspan = (0, 60),
        backends = _EXACT_PT, tags = vcat(both, [:sir, :erlang, :configuration, :pt]),
        expected = _EXPECT_CONFIG,
        notes = "Stage rate 3γ, same mean infectious period 1/γ; T₃ = 1 − (3γ/(τ + 3γ))³ = 0.4523 " *
                "and R₀ = 2.26 (more than the exponential period's 2). Variants n = 2 and 5."))
    add!(_canonical(:seair_pois5, "SEAIR (branching after latency, two infectors) on Poisson(5)";
        model = seair_model(), network = ConfigurationNetwork(PoissonDegree(5)),
        params = Dict(:τI => _ANCHOR_τ, :τA => 1 / 12, :p => 0.6, :σ => 1 / 5, :γ => _ANCHOR_γ),
        initial = SeedFraction(:E => 0.01), tspan = (0, 200), tstep = 0.5, backends = _EXACT_PT,
        tags = vcat(both, [:seair, :configuration, :pt]), expected = _EXPECT_CONFIG,
        notes = "T = 0.6·0.4 + 0.4·0.25 = 0.34, R₀ = 1.70. Needs the per-reaction assembler " *
                "(EBM) and one-transition-per-infector simulation (NO M2)."))
    add!(_canonical(:twostrain_pois5, "Two competing strains with full cross-immunity on Poisson(5)";
        model = twostrain_model(), network = ConfigurationNetwork(PoissonDegree(5)),
        params = Dict(:τ1 => _ANCHOR_τ, :τ2 => 1 / 5, :γ => _ANCHOR_γ),
        initial = SeedFraction(:I1 => 0.005, :I2 => 0.005), tspan = (0, 60),
        backends = _EXACT_PT, tags = vcat(both, [:twostrain, :configuration, :pt]),
        expected = (:R0, :r, :mean_degree, :excess_degree, :closure_constant),
        notes = "Competition: two entry states, so the seeding is explicit and there is no " *
                "single-entry final-size equation."))
    add!(_canonical(:sir_vax_pois5, "SIR with vaccination S → V (an exit) on Poisson(5)";
        model = sirv_model(), network = ConfigurationNetwork(PoissonDegree(5)),
        params = Dict(:τ => _ANCHOR_τ, :γ => _ANCHOR_γ, :ν => 0.02), initial = seedI,
        tspan = (0, 60),
        backends = (:edge_based => :exact_limit, :s_anchored => :exact_limit,
                    :pgf_closure => :exact_limit),
        tags = vcat(both, [:sir, :vaccination, :configuration, :pt]),
        expected = (:R0, :T, :r, :mean_degree, :excess_degree, :closure_constant),
        notes = "The exit type: EB with the survival factor ξ = e^{−νt}; PW^S (M6 with exits). " *
                "R₀ and r are those of the initial state (ξ = 1)."))

    # ---- arrows back into Sus: SIS and SIRS -------------------------------------------------
    add!(_canonical(:sis_reg3, "SIS on a 3-regular configuration network";
        model = sis_model(), network = ConfigurationNetwork(RegularDegree(3)),
        params = Dict(:τ => 1 / 2, :γ => _ANCHOR_γ), initial = seedI, tspan = (0, 80),
        backends = (:edge_based => :inadmissible, :pgf_closure => :inadmissible,
                    :pairwise_bernoulli => :approximate, :pairwise_const => :approximate,
                    :reinfection => :approximate, :motif => :approximate,
                    :neighbourhood => :approximate),
        tags = vcat(both, [:sis, :configuration, :pt]),
        expected = (:mean_degree, :excess_degree, :closure_constant),
        notes = "Conditioned on survival. The homogeneous pairwise threshold is τ_c = γ/(k − 1) " *
                "= 0.125 (τ/τ_c = 4), computed by NodeBasedModels' epidemic_threshold. " *
                "Approximations: pairwise, reinfection counting (L), motif m = 2, 3, 4, " *
                "neighbourhood n = 2."))
    add!(_canonical(:sirs_pois5, "SIRS (waning immunity ε = 1/50) on Poisson(5)";
        model = sirs_model(), network = ConfigurationNetwork(PoissonDegree(5)),
        params = Dict(:τ => _ANCHOR_τ, :γ => _ANCHOR_γ, :ε => 1 / 50), initial = seedI,
        tspan = (0, 300), tstep = 1.0,
        backends = (:edge_based => :inadmissible, :pairwise_const => :approximate),
        tags = vcat(both, [:sirs, :configuration, :pt]),
        expected = (:mean_degree, :excess_degree, :closure_constant),
        notes = "The resus type R → S; conditioned on survival."))

    # ---- clustering -------------------------------------------------------------------------
    clust = add!(_canonical(:sir_clust_s2t2, "SIR on a clustered network (2 single edges, 2 triangles per node)";
        model = sir, network = ClusteredNetwork(RegularDegree(2), RegularDegree(2)),
        params = anchor, initial = seedI, tspan = (0, 60),
        backends = (:edge_based => :exact_limit, :pairwise_keeling => :approximate),
        tags = vcat(both, [:sir, :clustered, :n_scaling]), expected = _EXPECT_CLUSTERED,
        notes = "Degree 6 as :sir_reg6, clustering C = 2/15. EB is Volz et al. (2011); Keeling's " *
                "closure with ϕ = 2/15 is approximate. N-scaling."))
    add!(_canonical(:sir_clust_pois12, "SIR on a clustered network (Poisson(1) single edges, Poisson(2) triangles)";
        model = sir, network = ClusteredNetwork(PoissonDegree(1), PoissonDegree(2)),
        params = Dict(:τ => 0.6, :γ => 1.0), initial = seedI, tspan = (0, 20), tstep = 0.1,
        backends = (:edge_based => :exact_limit,), tags = vcat(both, [:sir, :clustered]),
        expected = _EXPECT_CLUSTERED,
        notes = "The w1 reference setting (at ρ = 10⁻³: SSA 0.7121 ± 0.0018, Volz 0.7125, the " *
                "0.1 code 0.7293); here with the canonical 1% seeds."))

    # ---- typed (multitype) networks ---------------------------------------------------------
    ab = strata([:a, :b]; sizes = [0.5, 0.5])
    sir_ab = stratify(sir, ab)
    sbm = sbm_network(ab; mean_contacts = [6.0 2.0; 2.0 4.0])
    τ_sbm = _calibrated(calibrate(sir_ab, sbm, anchor; target = :R0 => 2.0, vary = :τ)[:τ])
    seed_ab = SeedFraction(:I_a => 0.005, :I_b => 0.005)
    add!(_canonical(:sir_sbm2, "Stratified SIR on a two-block Poisson SBM (means [6 2; 2 4])";
        model = sir_ab, network = sbm, params = Dict(:τ => τ_sbm, :γ => _ANCHOR_γ),
        initial = seed_ab, tspan = (0, 60),
        backends = (:edge_based => :exact_limit, :individual => :approximate,
                    :pairwise_multitype => :exact_limit),
        tags = vcat(both, [:sir, :stratified, :multitype]), expected = _EXPECT_TYPED,
        notes = "Typed stratification: stratify(sir, [:a, :b]) on a MultitypeNetwork; ρ(M) = " *
                "7.236, τ calibrated to R₀ = 2. Seeds: 1% of each block. The population " *
                "multitype pairwise model (stretch) is exact on Poisson blocks (K_a(c, b) = 1; " *
                "it matches the edge-based multitype lift to < 1e-8, WP36e)."))
    add!(_canonical(:sir_unstr2, "Stratified SIR on an unstructured two-type 6-regular network";
        model = sir_ab, network = unstructured(ConfigurationNetwork(RegularDegree(6)), ab),
        params = anchor, initial = seed_ab, tspan = (0, 60),
        backends = (:edge_based => :exact_limit,),
        tags = vcat(both, [:sir, :stratified, :multitype, :unit_law]), expected = _EXPECT_TYPED,
        notes = "The unit law M10: types independent of the network reproduce :sir_reg6."))

    # ---- multiplex --------------------------------------------------------------------------
    mpx_model = ContactModel(:sir_mpx;
        contacts = [Contact(:S, :I, :I, :(3c); layer = :home), Contact(:S, :I, :I, :c; layer = :comm)],
        transitions = [NodeTransition(:I, :R, :γ)])
    mpx_net = MultiplexNetwork(:home => RegularDegree(3), :comm => PoissonDegree(5))
    c_mpx = _calibrated(calibrate(mpx_model, mpx_net, Dict(:c => 0.05, :γ => _ANCHOR_γ);
                                  target = :R0 => 2.0, vary = :c)[:c])
    add!(_canonical(:sir_mpx, "SIR on a two-layer multiplex (household 3-regular, community Poisson(5))";
        model = mpx_model, network = mpx_net, params = Dict(:c => c_mpx, :γ => _ANCHOR_γ),
        initial = seedI, tspan = (0, 80), backends = (:edge_based => :exact_limit,),
        tags = vcat(both, [:sir, :multiplex]),
        expected = (:R0, :R0_additive, :r, :final_size, :mean_degree),
        notes = "τ_home = 3c, τ_comm = c with c calibrated to R₀ = ρ(K) = 2 over (layer, entry) " *
                "blocks; the additive R₀ (sum of the layer R₀s) is wrong (≈ 1.80)."))

    # ---- dynamic networks: neighbour exchange on a 6-regular base ---------------------------
    for (η, tag) in ((0.1, "01"), (1.0, "1"), (10.0, "10"))
        add!(_canonical(Symbol("sir_ne_reg6_eta", tag), "SIR on a 6-regular network with neighbour exchange η = $(η)";
            model = sir, network = DynamicNetwork(RegularDegree(6), NeighbourExchange(η)),
            params = Dict(:τ => 1 / 12, :γ => _ANCHOR_γ), initial = seedI, tspan = (0, 100),
            N = 5000, nsims = 100, backends = (:edge_based => :exact_limit,),
            tags = vcat(both, [:sir, :dynamic, :neighbour_exchange]), expected = _EXPECT_NE,
            notes = "Dynamic fixed degree (Miller–Slim–Volz DFD). Interpolates from the static " *
                    "network (R₀ = 1.25, R∞ = 0.533) to the η → ∞ limit MA(6τ, γ) = MA(1/2, 1/4) " *
                    "= :sir_wm5 (a regular base: Λ3). N = 5000, 100 runs."))
    end

    # ---- the dense ladder Λ1 (EBM only) -----------------------------------------------------
    for μ in (5, 20, 100)
        add!(_canonical(Symbol("sir_dense_pois", μ), "SIR on Poisson($(μ)) with μτ = 1/2";
            model = sir, network = ConfigurationNetwork(PoissonDegree(μ)),
            params = Dict(:τ => 1 / (2μ), :γ => _ANCHOR_γ), initial = seedI, tspan = (0, 60),
            backends = (:edge_based => :exact_limit,),
            tags = [:ebm, :sir, :configuration, :pt, :dense_ladder], expected = _EXPECT_CONFIG,
            notes = "Λ1: as μ → ∞ with μτ = 1/2 the edge-based model tends to :sir_wm5; the error " *
                    "decreases as O(1/μ)."))
    end

    # ---- small seeds and a quenched graph ---------------------------------------------------
    add!(_canonical(:sir_pois5_5seeds, "SIR on Poisson(5) from 5 seeds";
        model = sir, network = ConfigurationNetwork(PoissonDegree(5)), params = anchor,
        initial = SeedFraction(:I => 5 / 10_000), tspan = (0, 100), tstep = 0.5, nsims = 1000,
        align = CumulativeCrossing(0.02), backends = (:edge_based => :exact_limit,),
        tags = vcat(both, [:sir, :configuration, :pt, :small_seed]), expected = _EXPECT_CONFIG,
        notes = "Extinction and random delays: runs aligned at 2% cumulative incidence (the " *
                "shifts are stored); aligned and unaligned summaries side by side (time step " *
                "0.5, which keeps each under 200 kB). 1000 runs."))
    add!(_canonical(:sir_pois5_1seed, "SIR on Poisson(5) from a single seed";
        model = sir, network = ConfigurationNetwork(PoissonDegree(5)), params = anchor,
        initial = SeedFraction(:I => 1 / 10_000), tspan = (0, 100), tstep = 0.5, nsims = 2000,
        align = CumulativeCrossing(0.02), backends = (:edge_based => :exact_limit,),
        tags = [:ebm, :sir, :configuration, :pt, :small_seed], expected = _EXPECT_CONFIG,
        notes = "P(major) against the infector-side epidemic_probability (EBM); 2000 runs; " *
                "time step 0.5, as :sir_pois5_5seeds."))
    add!(_canonical(:sir_reg6_fixed, "SIR on one fixed 6-regular graph (N = 1000)";
        model = sir, network = ConfigurationNetwork(RegularDegree(6)), params = anchor,
        initial = seedI, tspan = (0, 60), N = 1000, graphs = :fixed,
        backends = (:individual => :approximate, :pair => :approximate),
        tags = [:nbm, :sir, :configuration, :pt, :quenched], expected = _EXPECT_CONFIG,
        notes = "Quenched: every run on the same graph (scenario_graph(sc)), for the individual- " *
                "and pair-based models on that graph."))

    # ---- derived variants: Erlang n = 2, 5 and the N-scaling sizes ---------------------------
    for n in (2, 5)
        # the variants carry their own title and notes; Erlang staging keeps the model Poisson
        # type-exact for the same back ends as n = 3
        Tn = 1 - (n * _ANCHOR_γ / (_ANCHOR_τ + n * _ANCHOR_γ))^n
        add!(derive(erl3; id = Symbol("sir_erl", n, "_pois5"),
                    title = "SIR with a $(n)-stage Erlang infectious period on Poisson(5)",
                    model = erlang_stages(sir, :I, n), initial = SeedFraction(:I_1 => 0.01),
                    backends = erl3.backends, tags = unique!(vcat(erl3.tags, [:derived])),
                    notes = "Variant of :sir_erl3_pois5 with n = $(n) stages: stage rate " *
                            "$(n)γ, same mean infectious period 1/γ; T_$(n) = 1 − ($(n)γ/(τ + " *
                            "$(n)γ))^$(n) = $(round(Tn; digits = 4)) and R₀ = 5T_$(n) = " *
                            "$(round(5Tn; digits = 2))."))
    end
    for base in (pois5, bim, pl, clust)
        add!(_variant(base, Symbol(base.id, "_N1000"), "(N = 10³, 2000 runs)", [:n_scaling];
                      N = 1000, nsims = 2000))
        add!(_variant(base, Symbol(base.id, "_N100000"), "(N = 10⁵, 20 runs)", [:n_scaling];
                      N = 100_000, nsims = 20))
    end

    # ---- stretch: degree-correlated (joint-degree) networks ---------------------------------
    bimodal = EmpiricalDegree(2 => 5 / 6, 10 => 1 / 6)
    for (r, tag) in ((0.0, "r0"), (0.5, "r05"), (-0.5, "rn05"))
        add!(_canonical(Symbol("sir_dc_bim_", tag), "SIR on the bimodal {2, 10} network with degree assortativity r = $(r)";
            model = sir, network = degree_correlated(bimodal; r), params = anchor,
            initial = seedI, tspan = (0, 60), backends = (:edge_based => :exact_limit,),
            tags = [:ebm, :sir, :degree_correlated, :non_pt, :stretch],
            expected = (:R0, :r, :final_size, :mean_degree, :excess_degree, :assortativity),
            notes = "Stretch (WP36): Newman r-mixing on the degree classes of :sir_bim; r = 0 is " *
                    ":sir_bim itself. EdgeBasedModels lifts it with its degree-class closure (the " *
                    "exact quotient of the multitype form); NetworkOutbreaks samples it with its " *
                    "joint-degree (2K) generator (validated: D∞ ≤ 0.0046 at N = 10⁴, WP36a)."))
    end

    # ---- stretch: dormant contacts (Miller–Slim–Volz Part II §3.2.4, Fig. 5) ---------------
    msv_degrees = EmpiricalDegree(2 => 0.5, 8 => 0.5)
    msv = Dict(:τ => 1.0, :γ => 1.0)
    dormant = [:ebm, :sir, :dynamic, :dormant_contacts, :stretch]
    add!(_canonical(:sir_dormant_msv, "SIR with dormant contacts (η_form = η_break = 1, k_m ∈ {2, 8})";
        model = sir, network = DynamicNetwork(msv_degrees, DormantContacts(η_form = 1, η_break = 1)),
        params = msv, initial = seedI, tspan = (0, 20), tstep = 0.1, backends = (:edge_based => :exact_limit,),
        tags = dormant, expected = (:mean_degree,),
        notes = "Stretch (WP36): the dormant-contact (DC) model of Miller, Slim & Volz Part II, " *
                "Fig. 5 (β = γ = 1, η₁ = η₂ = 1, ψ = (x² + x⁸)/2): the curve shared by its three " *
                "panels. Lifted by EdgeBasedModels edge_based (expanded form) and simulated by " *
                "NetworkOutbreaks' DormantContactProcess (validated: D∞ < 0.01, WP36b)."))
    add!(_canonical(:sir_dormant_dvd, "SIR with dormant contacts in the DVD limit (η_form = 0.1, η_break = 1, k_m ∈ {11, 44})";
        model = sir,
        network = DynamicNetwork(EmpiricalDegree(11 => 0.5, 44 => 0.5), DormantContacts(η_form = 0.1, η_break = 1)),
        params = msv, initial = seedI, tspan = (0, 20), tstep = 0.1, backends = (:edge_based => :exact_limit,),
        tags = dormant, expected = (:mean_degree,),
        notes = "Stretch (WP36): MSV Part II Fig. 5 (middle) with η₁ = 0.1, ψ = (x^{1/ξ} + " *
                "x^{4/ξ})/2, ξ = 1/11: close to the dynamic variable-degree (DVD) model with " *
                "η = 1 and Ψ(x) = (e^{−(1−x)} + e^{−4(1−x)})/2. Validated against " *
                "DormantContactProcess (WP36b)."))
    add!(_canonical(:sir_dormant_fast, "SIR with fast dormant contacts (η_form = η_break = 10, k_m ∈ {2, 8})";
        model = sir, network = DynamicNetwork(msv_degrees, DormantContacts(η_form = 10, η_break = 10)),
        params = msv, initial = seedI, tspan = (0, 20), tstep = 0.1, backends = (:edge_based => :exact_limit,),
        tags = vcat(dormant, [:mfsh]), expected = (:mean_degree,),
        notes = "Stretch (WP36): MSV Part II Fig. 5 (bottom): as η₁ = η₂ → ∞ the DC model tends " *
                "to MFSH with τξ = 1/2, i.e. :sir_mfsh_msv. Validated against " *
                "DormantContactProcess (WP36b)."))

    # ---- stretch: mean-field social heterogeneity -------------------------------------------
    mfsh = [:ebm, :sir, :mfsh, :stretch]
    add!(_canonical(:sir_mfsh_pois5, "SIR with mean-field social heterogeneity, Poisson(5) activity";
        model = sir, network = MFSHNetwork(PoissonDegree(5)), params = Dict(:τ => 1 / 12, :γ => _ANCHOR_γ),
        initial = seedI, tspan = (0, 100), backends = (:edge_based => :exact_limit,),
        algorithm = :fleeting, tags = mfsh, expected = _EXPECT_TYPED,
        notes = "Stretch (WP36): the η → ∞ limit of neighbour exchange on a Poisson(5) base " *
                "(:sir_ne_pois5_eta10), which is MFSH with the base's degrees, not mass action " *
                "(Λ3): R₀ = τ(κ_ex + 1)/γ = 2 as for :sir_wm5, final size 0.669 vs 0.800. " *
                "Simulated by NetworkOutbreaks' FleetingContactSSA (algorithm :fleeting)."))
    add!(_canonical(:sir_mfsh_msv, "SIR with mean-field social heterogeneity, k ∈ {2, 8}";
        model = sir, network = MFSHNetwork(msv_degrees), params = Dict(:τ => 0.5, :γ => 1.0),
        initial = seedI, tspan = (0, 20), tstep = 0.1, backends = (:edge_based => :exact_limit,),
        algorithm = :fleeting, tags = mfsh, expected = _EXPECT_TYPED,
        notes = "Stretch (WP36): the MFSH limit of :sir_dormant_fast (MSV Part II Fig. 5, " *
                "bottom: τξ = 1/2). Simulated by FleetingContactSSA (algorithm :fleeting)."))
    add!(_canonical(:sir_ne_pois5_eta10, "SIR on a Poisson(5) network with neighbour exchange η = 10";
        model = sir, network = DynamicNetwork(PoissonDegree(5), NeighbourExchange(10.0)),
        params = Dict(:τ => 1 / 12, :γ => _ANCHOR_γ), initial = seedI, tspan = (0, 100),
        N = 5000, nsims = 100, backends = (:edge_based => :exact_limit,),
        tags = [:ebm, :sir, :dynamic, :neighbour_exchange, :mfsh, :stretch], expected = _EXPECT_NE,
        notes = "Λ3 on a Poisson base: fast neighbour exchange approaches :sir_mfsh_pois5, not " *
                "mass action. N = 5000, 100 runs."))

    # ---- stretch: clustered SEIR and SEAIR (Volz beyond SIR) --------------------------------
    s2t2 = ClusteredNetwork(RegularDegree(2), RegularDegree(2))
    general = vcat(both, [:clustered, :clustered_general, :stretch])
    add!(_canonical(:seir_clust_s2t2, "SEIR on the clustered (2, 2) network";
        model = seir_model(), network = s2t2, params = Dict(:τ => _ANCHOR_τ, :σ => 1 / 5, :γ => _ANCHOR_γ),
        initial = SeedFraction(:E => 0.01), tspan = (0, 150), tstep = 0.5,
        backends = (:edge_based => :exact_limit, :pairwise_keeling => :approximate),
        tags = vcat(general, [:seir]), expected = _EXPECT_CLUSTERED,
        notes = "Stretch (WP20 SEIR): the Volz clustered lift beyond SIR; compare :seir_pois5 " *
                "and :sir_clust_s2t2."))
    add!(_canonical(:seair_clust_s2t2, "SEAIR on the clustered (2, 2) network";
        model = seair_model(), network = s2t2,
        params = Dict(:τI => _ANCHOR_τ, :τA => 1 / 12, :p => 0.6, :σ => 1 / 5, :γ => _ANCHOR_γ),
        initial = SeedFraction(:E => 0.01), tspan = (0, 200), tstep = 0.5,
        backends = (:edge_based => :exact_limit, :pairwise_keeling => :approximate),
        tags = vcat(general, [:seair]), expected = _EXPECT_CLUSTERED,
        notes = "Stretch (WP36 general-P clustered): branching and two infectors on triangles."))

    # ---- stretch: population-level multitype pairwise ---------------------------------------
    age = strata([:y, :o]; sizes = [0.4, 0.6])
    sir_age = stratify(sir, age; contact_rates = (a, b) -> a == b ? :τ : :(τ / 2))
    age_net = sbm_network(age; mean_contacts = [6.0 3.0; 2.0 4.0])
    τ_age = _calibrated(calibrate(sir_age, age_net, Dict(:τ => 0.1, :γ => _ANCHOR_γ);
                                  target = :R0 => 2.0, vary = :τ)[:τ])
    add!(_canonical(:sir_age2, "Age-stratified SIR (sizes 0.4/0.6, between-group rate τ/2) on a Poisson SBM";
        model = sir_age, network = age_net, params = Dict(:τ => τ_age, :γ => _ANCHOR_γ),
        initial = SeedFraction(:I_y => 0.004, :I_o => 0.006), tspan = (0, 60),
        backends = (:edge_based => :exact_limit, :pairwise_multitype => :exact_limit,
                    :individual => :approximate),
        tags = vcat(both, [:sir, :stratified, :multitype, :multitype_pairwise, :stretch]),
        expected = _EXPECT_TYPED,
        notes = "Stretch (WP36 population multitype pairwise): unequal strata, asymmetric mean " *
                "contacts [6 3; 2 4] (0.4·3 = 0.6·2) and a halved between-group rate; τ " *
                "calibrated to R₀ = 2; 1% seeds in each group."))

    # ---- stretch: heterogeneous susceptibility (WP36f) ---------------------------------------
    # Two susceptibility classes, the strata of unstructured(net, st), sharing the other
    # compartments (unlabelled species are shared by the node types; the shared seeds of I are
    # placed on the nodes of every type, §J.6). EdgeBasedModels lifts them with its
    # heterogeneous closure (edge_based(model, net, st) or edge_based(sc)).
    hs = strata([:lo, :hi]; sizes = [0.4, 0.6])
    lab(x, a) = SpeciesLabel(x; stratum = a)
    het_sir = ContactModel(:sir_het;
        contacts = [Contact(:S_lo, :I, :I, :τ_lo), Contact(:S_hi, :I, :I, :τ_hi)],
        transitions = [NodeTransition(:I, :R, :γ)],
        labels = Dict(:S_lo => lab(:S, :lo), :S_hi => lab(:S, :hi)))
    hetsus = [:ebm, :heterogeneous_susceptibility, :multitype, :stretch]
    add!(_canonical(:sir_hetsus_bim, "SIR with heterogeneous susceptibility (40% at τ = 0.05, 60% at τ = 0.3) on the bimodal {2, 10} network";
        model = het_sir, network = unstructured(bim.network, hs),
        params = Dict(:τ_lo => 0.05, :τ_hi => 0.3, :γ => _ANCHOR_γ), initial = seedI,
        tspan = (0, 60), tstep = 0.5, backends = (:edge_based => :exact_limit,),
        tags = vcat(hetsus, [:sir, :non_pt]), expected = _EXPECT_TYPED,
        notes = "Stretch (WP36f): susceptibility classes S_lo, S_hi (the strata of " *
                "unstructured(net, st), sizes 0.4/0.6) with a shared I and R; 1% shared seeds " *
                "in I. The homogeneous model with the mean τ̄ = 0.2 misses it."))
    het_seirv = ContactModel(:seirv_het;
        contacts = [Contact(:S_lo, :I, :E_lo, :τ_lo), Contact(:S_hi, :I, :E_hi, :τ_hi)],
        transitions = [NodeTransition(:E_lo, :I, :σ_lo), NodeTransition(:E_hi, :I, :σ_hi),
                       NodeTransition(:I, :R, :γ), NodeTransition(:S_hi, :V, :ν),
                       NodeTransition(:V, nothing, :μ)],
        labels = Dict(:S_lo => lab(:S, :lo), :S_hi => lab(:S, :hi), :E_lo => lab(:E, :lo),
                      :E_hi => lab(:E, :hi)))
    add!(_canonical(:seirv_hetsus_pois5, "SEIR with heterogeneous susceptibility, class-specific latency and vaccination of one class on Poisson(5)";
        model = het_seirv, network = unstructured(ConfigurationNetwork(PoissonDegree(5)), hs),
        params = Dict(:τ_lo => 0.08, :τ_hi => 0.3, :σ_lo => 0.5, :σ_hi => 0.2, :γ => _ANCHOR_γ,
                      :ν => 0.01, :μ => 0.05),
        initial = seedI, tspan = (0, 120), tstep = 1.0, backends = (:edge_based => :exact_limit,),
        tags = vcat(hetsus, [:seir, :vaccination, :pt]), expected = (:R0, :r, :mean_degree),
        notes = "Stretch (WP36f): class-specific latent stages E_lo, E_hi, a shared I and R, " *
                "vaccination S_hi → V (shared) at ν and removal of the vaccinated at μ; 1% " *
                "shared seeds in I. The exit from S_hi leaves no final-size fixed point. Time " *
                "step 1 keeps the summary small."))
    return out
end
