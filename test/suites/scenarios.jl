# Owner: WP12. The scenario registry (DESIGN §E.3, §E.4): every canonical scenario instantiates
# and is admissible for the back ends it declares; ρN is an integer; golden hashes and canonical
# text, stable across sessions; `derive` changes the hash; expected values are computed (and
# agree with independent closed forms, fixed points and ODE solutions); validation errors;
# stretch scenarios are tagged.

using NetworkEpiCore, Test
using LinearAlgebra: eigvals
import Symbolics

const NEC = NetworkEpiCore

# The E.3 table (ids as in the design; brace groups expanded).
const E3_IDS = [:sir_reg6, :sir_pois5, :sir_nb4, :sir_bim, :sir_pl, :sir_wm5, :seir_pois5,
                :sir_erl3_pois5, :seair_pois5, :twostrain_pois5, :sir_vax_pois5, :sis_reg3,
                :sirs_pois5, :sir_clust_s2t2, :sir_clust_pois12, :sir_sbm2, :sir_unstr2, :sir_mpx,
                :sir_ne_reg6_eta01, :sir_ne_reg6_eta1, :sir_ne_reg6_eta10, :sir_dense_pois5,
                :sir_dense_pois20, :sir_dense_pois100, :sir_pois5_5seeds, :sir_pois5_1seed,
                :sir_reg6_fixed]
const VARIANT_IDS = [:sir_erl2_pois5, :sir_erl5_pois5,
                     :sir_pois5_N1000, :sir_pois5_N100000, :sir_bim_N1000, :sir_bim_N100000,
                     :sir_pl_N1000, :sir_pl_N100000, :sir_clust_s2t2_N1000, :sir_clust_s2t2_N100000]
const STRETCH_IDS = [:sir_dc_bim_r0, :sir_dc_bim_r05, :sir_dc_bim_rn05, :sir_dormant_msv,
                     :sir_dormant_dvd, :sir_dormant_fast, :sir_mfsh_pois5, :sir_mfsh_msv,
                     :sir_ne_pois5_eta10, :seir_clust_s2t2, :seair_clust_s2t2, :sir_age2,
                     :sir_hetsus_bim, :seirv_hetsus_pois5]

@testset "registry" begin
    ids = scenario_ids()
    @test ids[1:length(E3_IDS)] == E3_IDS                     # E.3 order first
    @test Set(ids) == Set(vcat(E3_IDS, VARIANT_IDS, STRETCH_IDS))
    @test allunique(ids)
    @test all(sc -> sc.id in ids, scenarios())
    @test [sc.id for sc in scenarios()] == ids
    @test all(sc -> :canonical in sc.tags, scenarios())
    @test scenario(:sir_pois5) === scenario(:sir_pois5)
    sc = scenario(:sir_pois5)
    @test scenario(sc) === sc
    err = try
        scenario(:sir_pois6); nothing
    catch e
        e
    end
    @test err isa ArgumentError && occursin(":sir_pois5", err.msg)
    # tag selection: all of `tags`, none of `exclude`
    @test Set(scenario_ids(; tags = [:n_scaling])) ==
          Set([:sir_pois5, :sir_bim, :sir_pl, :sir_clust_s2t2, :sir_pois5_N1000, :sir_pois5_N100000,
               :sir_bim_N1000, :sir_bim_N100000, :sir_pl_N1000, :sir_pl_N100000,
               :sir_clust_s2t2_N1000, :sir_clust_s2t2_N100000])
    @test scenario_ids(; tags = [:n_scaling, :non_pt], exclude = [:derived]) == [:sir_bim, :sir_pl]
    # (steward-2) nothing is deferred: NetworkOutbreaks has the 2K sampler (WP36a), the dormant-
    # contact process (WP36b) and the fleeting-contact sampler (WP36c)
    @test isempty(scenario_ids(; tags = [:deferred]))
    # vignette sets (§E.3): EBM-only and NBM-only scenarios
    ebm_only = [id for id in E3_IDS if :ebm in scenario(id).tags && !(:nbm in scenario(id).tags)]
    nbm_only = [id for id in E3_IDS if :nbm in scenario(id).tags && !(:ebm in scenario(id).tags)]
    @test Set(ebm_only) == Set([:sir_dense_pois5, :sir_dense_pois20, :sir_dense_pois100, :sir_pois5_1seed])
    @test nbm_only == [:sir_reg6_fixed]
    # user registration
    mine = derive(scenario(:sir_reg6); id = :wp12_test_reg6, nsims = 10, tags = [:user])
    @test register_scenario!(mine) === mine
    @test scenario(:wp12_test_reg6) === mine
    @test last(scenario_ids()) === :wp12_test_reg6
    @test_throws ArgumentError register_scenario!(mine)
    other = derive(mine; nsims = 11, id = :wp12_test_reg6, tags = [:user])
    @test register_scenario!(other; replace = true) === other
    @test scenario(:wp12_test_reg6).sim.nsims == 11
    @test count(==(:wp12_test_reg6), scenario_ids()) == 1
    @test scenario_ids(; tags = [:user]) == [:wp12_test_reg6]
    @test !(:wp12_test_reg6 in scenario_ids(; tags = [:canonical]))
end

@testset "every scenario instantiates and is admissible for its declared back ends" begin
    for sc in scenarios(; tags = [:canonical])
        @testset "$(sc.id)" begin
            cm = sc.model
            inst = instantiate(cm, sc.params)
            @test all(c -> c.rate isa Float64 && c.rate >= 0, contacts(inst))
            @test all(t -> t.rate isa Float64 && t.rate >= 0, node_transitions(inst))
            @test Set(keys(sc.params)) == Set(NEC._parameter_names(cm))
            @test is_admissible(cm, :stochastic; network = sc.network)
            @test !isempty(sc.backends)
            for (key, verdict) in sc.backends
                @test verdict in BACKEND_VERDICTS
                ok = is_admissible(cm, SCENARIO_BACKENDS[key]; network = sc.network)
                @test ok == (verdict !== :inadmissible)
            end
            # grid, observables, conditioning
            @test first(sc.tgrid) == sc.tspan[1] && last(sc.tgrid) ≈ sc.tspan[2]
            @test sc.observables[end - 1:end] == [:infectious, :cumulative]
            @test sc.observables[1:end - 2] == species_names(cm)
            @test sc.sim.condition isa (typing(cm).theory === :T_EB ? MajorOutbreak : Survival)
        end
    end
    # spot checks of the E.3 back-end column
    @test scenario(:sir_bim).backends[:pairwise_const] === :biased
    @test scenario(:sir_pl).backends[:pairwise_const] === :biased
    @test scenario(:sir_pois5).backends[:pairwise_const] === :exact_limit
    @test scenario(:sis_reg3).backends[:edge_based] === :inadmissible
    @test scenario(:sirs_pois5).backends[:edge_based] === :inadmissible
    @test scenario(:sir_clust_s2t2).backends[:pairwise_keeling] === :approximate
    @test scenario(:sir_vax_pois5).backends[:s_anchored] === :exact_limit
    @test !is_admissible(scenario(:sis_reg3).model, :edge_based; network = scenario(:sis_reg3).network)
    @test scenario(:sis_reg3).sim.condition isa Survival
    @test scenario(:sirs_pois5).sim.condition isa Survival
    @test scenario(:sir_wm5).sim.algorithm === :mass_action
    @test scenario(:sir_reg6_fixed).sim.graphs === :fixed && scenario(:sir_reg6_fixed).sim.N == 1000
    @test all(id -> (scenario(id).sim.N, scenario(id).sim.nsims) == (5000, 100),
              [:sir_ne_reg6_eta01, :sir_ne_reg6_eta1, :sir_ne_reg6_eta10, :sir_ne_pois5_eta10])
    @test scenario(:sir_pois5_5seeds).sim.align == CumulativeCrossing(0.02)
    @test scenario(:sir_pois5_1seed).sim.nsims == 2000
    @test scenario(:sir_pois5).sim == SimConfig()
end

@testset "ρN is an integer; seeds are explicit and in entry states" begin
    for sc in scenarios(; tags = [:canonical])
        counts = Dict(seed_counts(sc.initial, sc.sim.N; exact = true))
        for (X, ρ) in sc.initial.fractions
            @test counts[X] ≥ 1
            @test counts[X] ≈ ρ * sc.sim.N rtol = 1e-12
        end
        @test sc.initial isa SeedFraction
        @test all(((X, ρ),) -> !(X in susceptible_species(sc.model)), sc.initial.fractions)
    end
    # the default seeding rule: the unique entry state (E for SEIR, I_1 after staging)
    @test scenario(:seir_pois5).initial == SeedFraction(:E => 0.01)
    @test only(entry_species(scenario(:sir_erl3_pois5).model)) === :I_1
    @test scenario(:sir_erl3_pois5).initial == SeedFraction(:I_1 => 0.01)
    @test seed_counts(scenario(:sir_pois5_1seed).initial, 10_000; exact = true) == [:I => 1]
    @test seed_counts(scenario(:sir_pois5_5seeds).initial, 10_000; exact = true) == [:I => 5]
    @test seed_counts(scenario(:sir_sbm2).initial, 10_000; exact = true) == [:I_a => 50, :I_b => 50]
    @test seed_counts(scenario(:sir_age2).initial, 10_000; exact = true) == [:I_y => 40, :I_o => 60]
    # a non-integer ρN is refused, also after derive
    base = scenario(:sir_pois5)
    @test_throws ArgumentError derive(base; initial = SeedFraction(:I => 0.00015))    # ρN = 1.5
    # the wrapped message is not nested ("ArgumentError: … ArgumentError: …"; WP12 review)
    nerr = try derive(base; initial = SeedFraction(:I => 0.00015)) catch e; e end
    @test length(findall("ArgumentError", sprint(showerror, nerr))) == 1 &&
          occursin("not a whole number of nodes", nerr.msg)
    @test_throws ArgumentError derive(base; N = 150)                                  # ρN = 1.5
    @test_throws ArgumentError derive(scenario(:sir_sbm2); N = 999)                   # n_a N = 499.5
end

# Golden hashes (SHA-256 of the canonical text) and the canonical text of :sir_pois5. These values
# were computed identically on Julia 1.11.9 and 1.12.7 (aarch64) and 1.12.6 (x86_64); a change
# means that committed summaries become stale, so it must be deliberate (bump SCENARIO_FORMAT or
# regenerate the summaries).
const GOLDEN_TEXT_POIS5 = """
scenario_format = 1
initial = SeedFraction(fractions=[:I => 0.01], default=nothing)
model = ContactModel(species=[:S, :I, :R], susceptible=[:S], convention=PerContact(), contacts=[Contact(recipient=:S, infector=:I, product=:I, rate=:τ, layer=:all)], transitions=[NodeTransition(from=:I, to=:R, rate=:γ)], labels=[])
network = ConfigurationNetwork(degrees=PoissonDegree(mean=5))
observables = [:S, :I, :R, :infectious, :cumulative]
params = [:γ => 0.25, :τ => 0.16666666666666666]
sim.N = 10000
sim.algorithm = :next_reaction
sim.align = NoAlignment()
sim.base_seed = 20260926
sim.condition = MajorOutbreak(threshold=0.050000000000000003)
sim.graphs = :per_run
sim.nsims = 200
tgrid = StepRangeLen(start=0, step=0.25, length=241)
tspan = (0, 60)
"""

const GOLDEN_HASHES = Dict(
    :sir_pois5 => "34c89792c3f7f8c0e0f9d4b2ce83aaafac299e4c50c06a7a435e42ec746a421f",
    :sir_bim => "094656d5c5902fe687d163f13b07618be10dfda5990d6b185a22497f717304c0",
    :sir_pl => "3c83d5096d2ca6454be74a378a4f191eca274b00ee8aaafe8faf880d0deb8915",
    :sir_wm5 => "6e8fb963f17089c416665f2b06af0dbe1a329ca34292affcda61943328d812a2",
    :sir_erl3_pois5 => "3f15dbe7b3c1b588af787b128278f20e5ac9e6fef6083caa42b914c33bef45f0",
    :seair_pois5 => "f939d0281de79ba483cdda19e3a169ec41f835b843e9656eab57d7341c6bcd2d",
    :sir_sbm2 => "f8e96436100120c0f8d829e09d6ceb9935e97999c34c337ba26fd295b068e7ef",
    :sir_mpx => "688c01dd57a427e73640a85af1e0e6ecdf9c2b78da43c5a3def1483f91db67c3",
    :sir_ne_reg6_eta1 => "c77453d75902c89c0f8cc93603626a8b0f622598eb7f14c69a4db01ecbf9d353",
    :sir_clust_s2t2 => "b86d7ecb83a0d623e63fc1a4a7fa16f60e8b05d090fcabda82989516346810e7",
    :sir_pois5_N1000 => "6b2f75c6b35ddb37577afa02d3d35e6e94d406be5e25d5c0b2e3ef92505532a6",
    :sir_age2 => "7ccd6a9b92d8e78bf1ce16c81be208c8c9d44ab5c3a861243b66c6e50c1f79aa",
    :sir_dc_bim_r05 => "6efbd6f882bfeb6517f9e7c22a158dc3acbf3c253e7ad724949be77f507a0de6",
    :sir_dormant_msv => "10d932b9d62adf890d5bc8315e07191beacf6cf4ab90dd4acecafbdecb2d647f",
)

@testset "golden canonical text and hashes" begin
    @test canonical_text(scenario(:sir_pois5)) == GOLDEN_TEXT_POIS5
    for (id, h) in GOLDEN_HASHES
        @test scenario_hash(scenario(id)) == h
    end
    hashes = [scenario_hash(sc) for sc in scenarios(; tags = [:canonical])]
    @test all(h -> occursin(r"^[0-9a-f]{64}$", h), hashes)
    @test allunique(hashes)
    @test allunique(first.(hashes, 8))                       # the file names are unique too
    for sc in scenarios(; tags = [:canonical])
        txt = canonical_text(sc)
        lines = split(chomp(txt), '\n')
        @test lines[1] == "scenario_format = 1"
        keys_ = [first(split(l, " = "; limit = 2)) for l in lines[2:end]]
        @test issorted(keys_) && allunique(keys_)
        @test !occursin("0x", txt) && !occursin("Ptr", txt) && !occursin("#", txt)
    end
    # rates as canonical text: Expr in prefix form, numbers in %.17g
    @test canonical_text(:(3γ)) == "(* 3 :γ)"
    @test canonical_text(:((1 - p) * σ)) == "(* (- 1 :p) :σ)"
    @test canonical_text(:(τ / 2)) == canonical_text(:(τ / 2.0))
    @test occursin("rate=(* 3 :c), layer=:home", canonical_text(scenario(:sir_mpx).model))
    @test canonical_text(SimConfig(; graphs = (:pool, 4))) ==
          "SimConfig(N=10000, nsims=200, graphs=(:pool, 4), algorithm=:next_reaction, " *
          "base_seed=20260926, condition=MajorOutbreak(threshold=0.050000000000000003), align=NoAlignment())"
end

@testset "hashes are stable across Julia sessions" begin
    ids = scenario_ids(; tags = [:canonical])
    code = """
    using NetworkEpiCore
    for id in $(repr(ids))
        println(id, " ", scenario_hash(scenario(id)))
    end
    """
    cmd = `$(Base.julia_cmd()) --startup-file=no --project=$(Base.active_project()) -e $code`
    out = readlines(cmd)
    @test out == ["$(id) $(scenario_hash(scenario(id)))" for id in ids]
end

@testset "what enters the hash" begin
    sc = scenario(:sir_pois5)
    h = scenario_hash(sc)
    base = (title = sc.title, model = sc.model, network = sc.network, params = sc.params,
            initial = sc.initial, tspan = sc.tspan, tgrid = sc.tgrid, observables = sc.observables,
            sim = sc.sim, backends = sc.backends, tags = sc.tags,
            expected = collect(keys(sc.expected)), notes = sc.notes)
    same(; kw...) = Scenario(sc.id; merge(base, NamedTuple(kw))...)
    # annotations do not enter
    @test scenario_hash(same()) == h
    @test scenario_hash(same(; title = "another title", notes = "n", tags = [:x],
                             backends = Dict(:edge_based => :exact_limit), expected = ())) == h
    @test scenario_hash(Scenario(:another_id; title = sc.title, model = sc.model,
                                 network = sc.network, params = sc.params, initial = sc.initial,
                                 tspan = sc.tspan, sim = sc.sim)) == h
    # reaction and model names do not enter (they change nothing the back ends compute)
    renamed = ContactModel(:other; contacts = [Contact(:S, :I, :I, :τ; name = :infect)],
                           transitions = [NodeTransition(:I, :R, :γ; name = :recover)])
    @test scenario_hash(same(; model = renamed)) == h
    # everything the simulation reads does (a new model or network must restate the back-end
    # verdicts and tags; here they are kept deliberately)
    keep = (; backends = sc.backends, tags = sc.tags)
    variants = [
        derive(sc; N = 20_000), derive(sc; nsims = 100), derive(sc; graphs = :fixed),
        derive(sc; graphs = (:pool, 10)), derive(sc; algorithm = :direct),
        derive(sc; base_seed = 1), derive(sc; condition = MajorOutbreak(0.1)),
        derive(sc; condition = Unconditioned()), derive(sc; align = CumulativeCrossing(0.02)),
        derive(sc; params = Dict(:τ => 0.2)), derive(sc; params = Dict(:γ => 0.25 + 1e-15)),
        derive(sc; initial = SeedFraction(:I => 0.02)), derive(sc; tspan = (0, 80)),
        derive(sc; tstep = 0.5), derive(sc; observables = [:S, :I, :R]),
        derive(sc; network = ConfigurationNetwork(PoissonDegree(5.000000000000001)), keep...),
        derive(sc; network = MFSHNetwork(PoissonDegree(5)), expected = (:R0,), keep...),
        derive(sc; model = ContactModel(:sir; contacts = [Contact(:S, :I, :I, :τ)],
                                        transitions = [NodeTransition(:I, :R, :γ)],
                                        species = [:S, :R, :I]), keep...),       # species order
        derive(sc; model = ContactModel(:sir; contacts = [Contact(:S, :I, :I, :(1 * τ))],
                                        transitions = [NodeTransition(:I, :R, :γ)]), keep...),
        derive(sc; model = ContactModel(:sir; contacts = [Contact(:S, :I, :I, :τ)],
                                        transitions = [NodeTransition(:I, :R, :γ)],
                                        convention = FrequencyDependent()), keep...),
    ]
    hs = scenario_hash.(variants)
    @test all(!=(h), hs)
    @test allunique(hs)
end

@testset "derive" begin
    sc = scenario(:sir_pois5)
    d = derive(sc; N = 1000, nsims = 2000)
    @test d.id === :sir_pois5_N1000_nsims2000
    @test scenario_hash(d) != scenario_hash(sc)
    @test (d.sim.N, d.sim.nsims) == (1000, 2000)
    @test d.model === sc.model && d.network == sc.network && d.params == sc.params
    @test :derived in d.tags && all(t -> t in d.tags, sc.tags)
    @test d.expected == sc.expected                         # same content, recomputed
    @test derive(sc; graphs = :fixed).id === :sir_pois5_graphs_fixed
    @test derive(sc; graphs = (:pool, 4)).id === :sir_pois5_graphs_pool4
    # parameters are merged; expected values are recomputed, never copied
    d2 = derive(sc; params = Dict(:τ => 0.2))
    @test startswith(string(d2.id), "sir_pois5_d") &&
          string(d2.id) == "sir_pois5_d" * first(scenario_hash(d2), 8)
    @test d2.params == Dict(:τ => 0.2, :γ => 0.25)
    T = 0.2 / (0.2 + 0.25)
    @test d2.expected[:T] ≈ T rtol = 1e-14
    @test d2.expected[:R0] ≈ 5T rtol = 1e-14
    @test d2.expected[:r] ≈ 0.2 * 4 - 0.25 rtol = 1e-12
    @test d2.expected[:final_size] == final_size(d2.model, d2.network, d2.params; initial = d2.initial)
    @test d2.expected[:final_size] > sc.expected[:final_size]
    @test_throws ArgumentError derive(sc; params = Dict(:σ => 1.0))   # not a parameter of SIR
    # a new model resets the observables; params replaced wholesale with replace_params
    d3 = derive(sc; id = :wp12_seir, model = seir_model(), initial = SeedFraction(:E => 0.01),
                params = Dict(:τ => 1 / 6, :σ => 1 / 5, :γ => 1 / 4), replace_params = true,
                backends = Dict(:edge_based => :exact_limit), tags = [:seir, :derived])
    @test d3.observables == [:S, :E, :I, :R, :infectious, :cumulative]
    @test d3.backends == Dict(:edge_based => :exact_limit) && d3.tags == [:seir, :derived]
    # a new model or network must restate the back-end verdicts and tags (WP12 review: derive
    # kept :pairwise_const => :exact_limit and the tag :pt on a non-Poisson-type network)
    bim = ConfigurationNetwork(EmpiricalDegree(2 => 5 / 6, 10 => 1 / 6))
    for kw in ((; network = bim), (; network = bim, backends = sc.backends),
               (; network = bim, tags = [:x]),
               (; model = seir_model(), initial = SeedFraction(:E => 0.01),
                  params = Dict(:τ => 1 / 6, :σ => 1 / 5, :γ => 1 / 4), replace_params = true))
        @test_throws ArgumentError derive(sc; kw...)
    end
    msg = sprint(showerror, try derive(sc; network = bim) catch e; e end)
    @test occursin("a new network needs `backends` and `tags`", msg)
    dbim = derive(sc; network = bim, backends = Dict(:edge_based => :exact_limit,
                                                      :pairwise_const => :biased),
                  tags = [:sir, :configuration, :non_pt])
    @test dbim.backends[:pairwise_const] === :biased && !(:pt in dbim.tags)
    @test scenario_hash(dbim) == scenario_hash(scenario(:sir_bim))
    @test d3.expected[:R0] ≈ 2 rtol = 1e-12
    @test length(d3.tgrid) == length(sc.tgrid)
    d4 = derive(sc; tspan = (0, 100))
    @test step(d4.tgrid) == step(sc.tgrid) && last(d4.tgrid) == 100 && length(d4.tgrid) == 401
    # errors
    @test_throws ArgumentError derive(sc)                          # nothing changed
    @test_throws ArgumentError derive(sc; title = "only a title")  # still nothing the SSA reads
    @test_throws ArgumentError derive(sc; bogus = 1)
    @test_throws ArgumentError derive(sc; sim = SimConfig(), N = 5)
    # the registered variants are derived from their bases
    @test scenario(:sir_pl_N1000).params == scenario(:sir_pl).params
    @test scenario(:sir_pl_N1000).sim.N == 1000 && scenario(:sir_pl_N100000).sim.nsims == 20
    @test :derived in scenario(:sir_erl5_pois5).tags
    @test species_names(scenario(:sir_erl5_pois5).model) == [:S, :I_1, :I_2, :I_3, :I_4, :I_5, :R]
    # the Erlang variants have their own title and notes (WP12 review: they read "3-stage")
    for n in (2, 5)
        v = scenario(Symbol("sir_erl", n, "_pois5"))
        @test v.title == "SIR with a $(n)-stage Erlang infectious period on Poisson(5)"
        Tn = 1 - (n * 0.25 / (1 / 6 + n * 0.25))^n
        @test v.expected[:T] ≈ Tn rtol = 1e-12
        @test occursin("T_$(n) = ", v.notes) && occursin(string(round(Tn; digits = 4)), v.notes)
        @test !occursin("3-stage", v.title) && !occursin("T₃", v.notes)
        @test v.backends == scenario(:sir_erl3_pois5).backends
    end
end

# Independent final-size solve for single-type SIR on a configuration network:
# θ = 1 − T + T q ψ'(θ)/ψ'(1), R∞ = 1 − q ψ(θ) (bisection; ψ written out by hand).
function fs_config(ψ, dψratio, T, ρ)
    q = 1 - ρ
    g(θ) = 1 - T + T * q * dψratio(θ) - θ
    lo, hi = 0.0, 1.0 - 1e-15          # g(lo) > 0 > g(hi)
    for _ in 1:200
        mid = (lo + hi) / 2
        g(mid) > 0 ? (lo = mid) : (hi = mid)
    end
    return 1 - q * ψ((lo + hi) / 2)
end

@testset "expected values are computed, and agree with independent calculations" begin
    # 1. computed by the NEC functions from the scenario's own data (never typed)
    for sc in scenarios(; tags = [:canonical])
        for (q, v) in sc.expected
            @test v == NEC._expected_value(q, sc.model, sc.network, sc.params, sc.initial, sc.sim.N)
        end
    end
    @test Set(keys(scenario(:sir_pois5).expected)) ==
          Set([:R0, :T, :r, :final_size, :mean_degree, :excess_degree, :closure_constant])
    # 2. the anchors: T = 0.4, R₀ = T κ_ex = 2, r = τ(κ_ex − 1) − γ = 5/12 for excess degree 5
    for id in (:sir_reg6, :sir_pois5, :sir_nb4, :sir_bim, :sir_unstr2)
        ex = scenario(id).expected
        @test ex[:R0] ≈ 2 rtol = 1e-12
        @test ex[:r] ≈ 5 / 12 rtol = 1e-12
        haskey(ex, :T) && @test ex[:T] ≈ 0.4 rtol = 1e-14
    end
    # 3. final sizes: an independent fixed point (bisection, hand-written PGFs) ...
    T = 0.4
    @test scenario(:sir_reg6).expected[:final_size] ≈ fs_config(x -> x^6, x -> x^5, T, 0.01) rtol = 1e-10
    @test scenario(:sir_pois5).expected[:final_size] ≈
          fs_config(x -> exp(5(x - 1)), x -> exp(5(x - 1)), T, 0.01) rtol = 1e-10
    @test scenario(:sir_nb4).expected[:final_size] ≈
          fs_config(x -> (0.5 / (1 - 0.5x))^4, x -> (0.5 / (1 - 0.5x))^5, T, 0.01) rtol = 1e-10
    @test scenario(:sir_bim).expected[:final_size] ≈
          fs_config(x -> 5 / 6 * x^2 + 1 / 6 * x^10, x -> (x + x^9) / 2, T, 0.01) rtol = 1e-10
    for μ in (5, 20, 100)
        τ = 1 / (2μ); Tμ = τ / (τ + 0.25)
        ex = scenario(Symbol("sir_dense_pois", μ)).expected
        @test ex[:R0] ≈ μ * Tμ rtol = 1e-12
        @test ex[:final_size] ≈ fs_config(x -> exp(μ * (x - 1)), x -> exp(μ * (x - 1)), Tμ, 0.01) rtol = 1e-9
    end
    # ... and the edge-based / mass-action ODEs integrated to t = 600 with scipy (LSODA,
    # rtol 1e-11; scratchpad/wp12/check_expected.py), an independent implementation
    scipy = Dict(:sir_reg6 => 0.929510221928986, :sir_pois5 => 0.8002039676752573,
                 :sir_nb4 => 0.6408330164023218, :sir_bim => 0.4955556229978496,
                 :sir_pl => 0.28979068328137114, :sir_wm5 => 0.8002039676768438,
                 :seir_pois5 => 0.8002039676783662, :sir_erl3_pois5 => 0.8576758051888291,
                 :seair_pois5 => 0.697578653438247, :sir_dense_pois5 => 0.5465059395399643,
                 :sir_dense_pois20 => 0.7440956406859746, :sir_dense_pois100 => 0.7894354359654722,
                 :sir_sbm2 => 0.7749320343143647, :sir_mfsh_pois5 => 0.6686540105280259,
                 :sir_mpx => 0.878063310131922)
    for (id, v) in scipy
        @test scenario(id).expected[:final_size] ≈ v atol = 1e-8
    end
    # 4. the indicative values of the E.3 table (4 decimals)
    for (id, v) in (:sir_reg6 => 0.9295, :sir_pois5 => 0.8002, :sir_nb4 => 0.6408,
                    :sir_bim => 0.4956, :sir_wm5 => 0.8002)
        @test scenario(id).expected[:final_size] ≈ v atol = 5e-5
    end
    @test scenario(:sir_pl).expected[:final_size] ≈ 0.2898 atol = 5e-5      # τ calibrated to R₀ = 2
    @test scenario(:sir_pl).params[:τ] ≈ 0.0750 atol = 5e-5
    @test scenario(:sir_pl).expected[:R0] ≈ 2 rtol = 1e-9
    @test scenario(:sir_pl).expected[:mean_degree] ≈ 3.985 atol = 5e-4
    @test scenario(:sir_pl).expected[:excess_degree] ≈ 8.663 atol = 5e-4
    @test scenario(:sir_pl).expected[:closure_constant] ≈ 2.17 atol = 5e-3
    @test scenario(:sir_reg6).expected[:closure_constant] ≈ 5 / 6 rtol = 1e-14
    @test scenario(:sir_nb4).expected[:closure_constant] ≈ 5 / 4 rtol = 1e-14
    @test scenario(:sir_bim).expected[:closure_constant] ≈ 3 / 2 rtol = 1e-12
    @test scenario(:sir_wm5).expected[:R0] ≈ 2 && scenario(:sir_wm5).expected[:r] ≈ 0.25
    # Erlang: T_n = 1 − (nγ/(τ + nγ))ⁿ, R₀ = 5 T_n (3 stages: 0.4523, 2.26)
    for n in (2, 3, 5)
        ex = scenario(Symbol("sir_erl", n, "_pois5")).expected
        Tn = 1 - (n * 0.25 / (1 / 6 + n * 0.25))^n
        @test ex[:T] ≈ Tn rtol = 1e-12
        @test ex[:R0] ≈ 5Tn rtol = 1e-12
    end
    @test scenario(:sir_erl3_pois5).expected[:T] ≈ 0.4523 atol = 5e-5
    # SEAIR T = 0.6·0.4 + 0.4·0.25 = 0.34, R₀ = 1.70; SEIR r is the root of (r + σ)(r + τ + γ) = στκ_ex
    @test scenario(:seair_pois5).expected[:T] ≈ 0.34 rtol = 1e-12
    @test scenario(:seair_pois5).expected[:R0] ≈ 1.70 rtol = 1e-12
    r = scenario(:seir_pois5).expected[:r]
    @test (r + 0.2) * (r + 1 / 6 + 0.25) ≈ 0.2 * (1 / 6) * 5 rtol = 1e-12
    # two strains: K = diag(κ_ex T1, κ_ex T2); SIS/SIRS have no NEC threshold quantities
    @test scenario(:twostrain_pois5).expected[:R0] ≈ 5 * 0.2 / 0.45 rtol = 1e-12
    @test !haskey(scenario(:sis_reg3).expected, :R0)
    # typed networks: SBM ρ(M) = 7.236 ⇒ τ = 0.0955; unstructured = the 6-regular network (M10)
    ρM = (10 + sqrt(20)) / 2                                  # eigenvalues of [6 2; 2 4]
    @test ρM ≈ 7.236 atol = 5e-4
    Tsbm = 2 / ρM
    @test scenario(:sir_sbm2).params[:τ] ≈ Tsbm * 0.25 / (1 - Tsbm) rtol = 1e-9
    @test scenario(:sir_sbm2).params[:τ] ≈ 0.0955 atol = 5e-5
    @test scenario(:sir_unstr2).expected[:final_size] ≈ scenario(:sir_reg6).expected[:final_size] rtol = 1e-10
    # multiplex: K = [2T_h 3T_h; 5T_c 5T_c], ρ(K) = 2; the additive R₀ is the trace 2T_h + 5T_c
    c = scenario(:sir_mpx).params[:c]
    Th, Tc = 3c / (3c + 0.25), c / (c + 0.25)
    K = [2Th 3Th; 5Tc 5Tc]
    @test maximum(abs, eigvals(K)) ≈ 2 rtol = 1e-9
    @test scenario(:sir_mpx).expected[:R0_additive] ≈ 2Th + 5Tc rtol = 1e-12
    @test scenario(:sir_mpx).expected[:R0_additive] ≈ 1.80 atol = 5e-3
    # neighbour exchange (MSV DFD): R₀ = τ[(γ + η)κ_ex + η]/(γ(γ + η + τ)); static 1.25 at η = 0
    for (η, tag) in ((0.1, "01"), (1.0, "1"), (10.0, "10"))
        τ, γ = 1 / 12, 0.25
        @test scenario(Symbol("sir_ne_reg6_eta", tag)).expected[:R0] ≈
              τ * ((γ + η) * 5 + η) / (γ * (γ + η + τ)) rtol = 1e-12
    end
    # clustering: C = 2E[t]/E[k(k − 1)] = 2/15 for (2, 2)
    @test scenario(:sir_clust_s2t2).expected[:clustering] ≈ 2 / 15 rtol = 1e-14
    @test scenario(:sir_clust_s2t2).expected[:mean_degree] == 6
    # stretch: r = 0 degree correlation is :sir_bim; MFSH R₀ = τ(κ_ex + 1)/γ
    @test scenario(:sir_dc_bim_r0).expected[:final_size] ≈ scenario(:sir_bim).expected[:final_size] rtol = 1e-10
    @test scenario(:sir_dc_bim_r05).expected[:assortativity] ≈ 0.5 rtol = 1e-10
    @test scenario(:sir_dc_bim_r05).expected[:R0] > 2 > scenario(:sir_dc_bim_rn05).expected[:R0]
    @test scenario(:sir_mfsh_pois5).expected[:R0] ≈ (1 / 12) * 6 / 0.25 rtol = 1e-12
    @test scenario(:sir_mfsh_msv).expected[:R0] ≈ 0.5 * (68 / 2 / 5) / 1 rtol = 1e-12
    @test scenario(:sir_dormant_msv).expected[:mean_degree] ≈ 0.5 * 5      # ξ⟨k_m⟩
    @test scenario(:sir_age2).expected[:R0] ≈ 2 rtol = 1e-9
end

@testset "stretch scenarios are tagged" begin
    for fam in (:degree_correlated, :dormant_contacts, :mfsh, :clustered_general, :multitype_pairwise)
        ids = scenario_ids(; tags = [fam, :stretch])
        @test !isempty(ids)
    end
    for sc in scenarios(; tags = [:deferred])
        @test :stretch in sc.tags                      # only stretch scenarios are deferred
        @test !(:nbm in sc.tags)
    end
    @test isempty(scenario_ids(; tags = [:stretch], exclude = [:canonical]))
    @test scenario(:sir_dc_bim_r0).network isa DegreeCorrelatedNetwork
    @test scenario(:sir_dormant_dvd).network.process == DormantContacts(0.1, 1.0)
    @test scenario(:sir_mfsh_pois5).network isa MFSHNetwork
    @test scenario(:seir_clust_s2t2).network isa ClusteredNetwork
    @test :pairwise_multitype in keys(scenario(:sir_age2).backends)
    # the canonical (non-stretch) list has no deferred scenario: WP30 can simulate all of it
    @test isempty(scenario_ids(; tags = [:deferred], exclude = [:stretch]))
end

@testset "SimConfig" begin
    s = SimConfig()
    @test (s.N, s.nsims, s.graphs, s.algorithm, s.base_seed) == (10_000, 200, :per_run, :next_reaction, UInt64(20260926))
    @test s.condition == MajorOutbreak(0.05) && s.align == NoAlignment()
    @test SimConfig(; graphs = (:pool, 3)).graphs == (:pool, 3)
    @test SimConfig(; N = 5) != s && SimConfig() == s && hash(SimConfig()) == hash(s)
    @test_throws ArgumentError SimConfig(; N = 0)
    @test_throws ArgumentError SimConfig(; nsims = 0)
    @test_throws ArgumentError SimConfig(; graphs = :sometimes)
    @test_throws ArgumentError SimConfig(; graphs = (:pool, 0))
    @test_throws ArgumentError SimConfig(; algorithm = :gillespie)
    @test_throws ArgumentError SimConfig(; base_seed = -1)
    @test_throws ArgumentError MajorOutbreak(1.5)
    @test_throws ArgumentError CumulativeCrossing(0)
    @test MajorOutbreak() == MajorOutbreak(0.05)
    @test all(a -> a in SIM_ALGORITHMS, (:next_reaction, :direct, :has, :mass_action))
end

@testset "Scenario validation" begin
    sir = sir_model()
    net = ConfigurationNetwork(PoissonDegree(5))
    p = Dict(:τ => 1 / 6, :γ => 1 / 4)
    mk(; kw...) = Scenario(:wp12_probe; model = sir, network = net, params = p,
                           initial = SeedFraction(:I => 0.01), tspan = (0, 60), kw...)
    @test mk() isa Scenario
    @test mk(; model = sir_model()).observables == [:S, :I, :R, :infectious, :cumulative]
    @test_throws ArgumentError mk(; params = Dict(:τ => 1 / 6))                  # missing γ
    @test_throws ArgumentError mk(; params = Dict(:τ => 1 / 6, :γ => 0.25, :σ => 1.0))
    @test_throws ArgumentError mk(; params = Dict(:τ => NaN, :γ => 0.25))
    @test_throws ArgumentError mk(; params = Dict(:τ => -1.0, :γ => 0.25))      # rates ≥ 0
    Symbolics.@variables β
    @test_throws ArgumentError mk(; model = sir_model(; τ = β), params = Dict(:γ => 0.25))
    @test_throws ArgumentError mk(; initial = SeedFraction(:S => 0.01))       # seeds must be infected
    @test_throws ArgumentError mk(; initial = SeedFraction(:X => 0.01))
    @test_throws ArgumentError mk(; initial = SeedCount(:I => 100))            # SeedFraction only
    @test_throws ArgumentError mk(; initial = SeedFraction(:I => 0.01; default = :R))
    @test mk(; initial = SeedFraction(:I => 0.01; default = :S)) isa Scenario
    @test_throws ArgumentError mk(; observables = [:S, :Q])
    @test_throws ArgumentError mk(; observables = [:S, :S])
    @test_throws ArgumentError mk(; tspan = (0, -1))
    @test_throws ArgumentError mk(; tstep = 0.7)                                # does not divide 60
    @test_throws ArgumentError mk(; tgrid = 0.0:0.5:50.0)                       # ends before tspan[2]
    @test mk(; tgrid = 0:0.5:60).tgrid == 0.0:0.5:60.0
    @test_throws ArgumentError mk(; backends = Dict(:edge_bsaed => :exact_limit))
    @test_throws ArgumentError mk(; backends = Dict(:edge_based => :perfect))
    @test_throws ArgumentError mk(; backends = Dict(:edge_based => :inadmissible))   # SIR is admissible
    @test_throws ArgumentError mk(; model = sis_model(), backends = Dict(:edge_based => :exact_limit))
    @test mk(; model = sis_model(), backends = Dict(:edge_based => :inadmissible)) isa Scenario
    @test_throws ArgumentError mk(; expected = (:R00,))
    @test_throws ArgumentError mk(; expected = Dict(:R0 => 2.0))    # values cannot be typed in
    @test mk(; expected = (:R0, :T)).expected ==
          Dict(:R0 => basic_reproduction_number(sir, net, p), :T => transmissibility(sir, net, p))
    @test_throws ArgumentError mk(; model = twostrain_model(), params = Dict(:τ1 => 0.1, :τ2 => 0.2, :γ => 0.25),
                                  initial = SeedFraction(:I1 => 0.01), expected = (:final_size,))
    @test_throws ArgumentError Scenario(Symbol("bad id"); model = sir, network = net, params = p,
                                        initial = SeedFraction(:I => 0.01), tspan = (0, 60))
    # a time-dependent rate cannot be simulated by NetworkOutbreaks: no reference ensemble
    @test_throws ArgumentError mk(; model = sir_model(; γ = :(γ * (1 + t))))
    # symbolic parameters in the network cannot be hashed
    s = mk()
    @test s.expected == Dict{Symbol,Float64}()
    @test sprint(show, s) == "Scenario(:wp12_probe)"
    txt = sprint(show, MIME"text/plain"(), scenario(:sir_mpx))
    @test occursin("R0_additive", txt) && occursin(scenario_hash(scenario(:sir_mpx)), txt)
end

@testset "steward-2: stretch scenarios that NetworkOutbreaks now simulates" begin
    # MFSH is simulated by FleetingContactSSA (:fleeting); nothing is deferred any more
    @test :fleeting in SIM_ALGORITHMS
    @test SimConfig(; algorithm = :fleeting).algorithm === :fleeting
    for id in (:sir_mfsh_pois5, :sir_mfsh_msv)
        sc = scenario(id)
        @test sc.sim.algorithm === :fleeting
        @test !(:deferred in sc.tags) && :stretch in sc.tags
        @test occursin("sim.algorithm = :fleeting", canonical_text(sc))
    end
    for id in (:sir_dc_bim_r0, :sir_dc_bim_r05, :sir_dc_bim_rn05, :sir_dormant_msv,
               :sir_dormant_dvd, :sir_dormant_fast)
        sc = scenario(id)
        @test !(:deferred in sc.tags) && !occursin("Deferred", sc.notes)
        @test sc.sim.algorithm === :next_reaction
    end
    @test occursin("is exact on Poisson blocks", scenario(:sir_sbm2).notes)
    # the small-seed scenarios use a 0.5 time step (their aligned and unaligned summaries are
    # stored side by side and must stay under 200 kB)
    for id in (:sir_pois5_5seeds, :sir_pois5_1seed)
        @test step(scenario(id).tgrid) == 0.5 && length(scenario(id).tgrid) == 201
    end
end

@testset "steward-2: heterogeneous-susceptibility scenarios (shared seeds on a MultitypeNetwork)" begin
    st = strata([:lo, :hi]; sizes = [0.4, 0.6])
    for (id, fam) in ((:sir_hetsus_bim, :sir), (:seirv_hetsus_pois5, :seir))
        sc = scenario(id)
        @test sc.network isa MultitypeNetwork && sc.network.types == [:lo, :hi]
        @test sc.network.sizes == [0.4, 0.6]
        @test sc.backends == Dict(:edge_based => :exact_limit)
        @test all(t -> t in sc.tags, (:stretch, :ebm, :heterogeneous_susceptibility, fam))
        @test !(:nbm in sc.tags)
        @test sc.initial.fractions == [:I => 0.01]            # a shared seeded species
        @test !haskey(species_labels(sc.model), :I)
        @test is_admissible(sc.model, :stochastic; network = sc.network)
    end
    bim = scenario(:sir_hetsus_bim)
    @test bim.network == unstructured(ConfigurationNetwork(EmpiricalDegree(2 => 5 / 6, 10 => 1 / 6)), st)
    T = [0.05 / 0.3, 0.3 / 0.55]
    @test bim.expected[:R0] ≈ 5 * (0.4 * T[1] + 0.6 * T[2]) rtol = 1e-12
    strat = stratify(sir_model(), st; contact_rates = (a, b) -> a === :lo ? :τ_lo : :τ_hi)
    @test bim.expected[:final_size] ≈
          final_size(strat, bim.network, bim.params; initial = SeedFraction(:I_lo => 0.004, :I_hi => 0.006)) rtol = 1e-10
    @test bim.expected[:r] ≈ early_growth_rate(strat, bim.network, bim.params) rtol = 1e-10
    sv = scenario(:seirv_hetsus_pois5)
    @test sv.expected[:R0] ≈ 5 * (0.4 * 0.08 / 0.33 + 0.6 * 0.3 / 0.55) rtol = 1e-12
    @test !haskey(sv.expected, :final_size)                  # the exit S_hi → V: no fixed point
    @test step(sv.tgrid) == 1.0 && step(bim.tgrid) == 0.5
    # shared seeds count against the nodes left free by the stratum seeds
    @test derive(bim; initial = SeedFraction(:I => 0.5)) isa Scenario
    lab(x, a) = SpeciesLabel(x; stratum = a)
    labelled = ContactModel(:sir_het_l; contacts = contacts(bim.model), transitions = node_transitions(bim.model),
                            species = [:S_lo, :S_hi, :I, :R, :Q_lo],
                            labels = Dict(:S_lo => lab(:S, :lo), :S_hi => lab(:S, :hi), :Q_lo => lab(:Q, :lo)))
    mk(init) = Scenario(:hetsus_seed_test; model = labelled, network = bim.network, params = bim.params,
                        initial = init, tspan = (0, 10), tstep = 1.0)
    @test mk(SeedFraction(:Q_lo => 0.3, :I => 0.69)) isa Scenario             # free: 0.1 + 0.6
    @test_throws ArgumentError mk(SeedFraction(:Q_lo => 0.3, :I => 0.71))            # more than N
    @test_throws ArgumentError mk(SeedFraction(:Q_lo => 0.41, :I => 0.01))           # type lo overfull
end
