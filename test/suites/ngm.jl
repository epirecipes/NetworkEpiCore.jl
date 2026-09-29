# Owner: WP11. Numeric next-generation matrix, transmissibility, early growth rate, final size
# and calibration (DESIGN §B.6, §C.3, §D.4, §E.2, §G.2 WP11), including the w1 counterexamples
# (ebm-analysis §2.1: bypass, A/I split, two 3-regular layers) and verified issues E12, E14, E18.
#
# Expected values are computed independently here: closed forms, hand-derived matrices, value
# iteration, Monte Carlo paths of one infector, and the edge-based ODEs of §D.4 and of
# Miller–Slim–Volz (DFD, MFSH) written out and integrated with a test-only RK4.

using NetworkEpiCore
using LinearAlgebra
using Random
const NEC = NetworkEpiCore

# ---------------------------------------------------------------------------------------------
# Test-only numerics
# ---------------------------------------------------------------------------------------------

function rk4_final(f, u0::Vector{Float64}, h, nsteps)
    u = copy(u0)
    for _ in 1:nsteps
        k1 = f(u)
        k2 = f(u .+ (h / 2) .* k1)
        k3 = f(u .+ (h / 2) .* k2)
        k4 = f(u .+ h .* k3)
        u = u .+ (h / 6) .* (k1 .+ 2k2 .+ 2k3 .+ k4)
    end
    return u
end

function fd_jacobian(f, u::Vector{Float64}; h = 1e-6)
    n = length(u)
    J = zeros(n, n)
    for j in 1:n
        e = zeros(n)
        e[j] = h
        J[:, j] = (f(u .+ e) .- f(u .- e)) ./ (2h)
    end
    return J
end

function bisect(g, lo, hi; iters = 200)
    glo = g(lo)
    for _ in 1:iters
        mid = (lo + hi) / 2
        gm = g(mid)
        if sign(gm) == sign(glo)
            lo, glo = mid, gm
        else
            hi = mid
        end
    end
    return (lo + hi) / 2
end

# The edge-based field of §D.4 for an exit-free T_EB ContactModel on ConfigurationNetwork(d),
# written out independently: u = [θ; φ_X...; pop_X...] over the non-susceptible species.
function eb_field(cm::ContactModel, d, p, q)
    S = only(susceptible_species(cm))
    X = [x for x in species_names(cm) if x != S]
    ix = Dict(x => i for (i, x) in enumerate(X))
    n = length(X)
    cs = [(rate_value(c.rate, p), ix[c.infector], ix[c.product]) for c in contacts(cm)]
    ts = [(rate_value(t.rate, p), ix[t.from], t.to === nothing ? 0 : ix[t.to])
          for t in node_transitions(cm)]
    k1 = pgf_derivative(d, 1.0, 1)
    function f(u)
        θ = u[1]
        φ = u[2:(n + 1)]
        pop = u[(n + 2):(2n + 1)]
        dθ = 0.0
        dφ = zeros(n)
        dpop = zeros(n)
        for (τ, J, P) in cs
            flux = τ * φ[J]
            dθ -= flux
            dφ[J] -= flux
            dφ[P] += flux * q * pgf_derivative(d, θ, 2) / k1
            dpop[P] += flux * q * pgf_derivative(d, θ, 1)
        end
        for (a, from, to) in ts
            dφ[from] -= a * φ[from]
            dpop[from] -= a * pop[from]
            if to != 0
                dφ[to] += a * φ[from]
                dpop[to] += a * pop[from]
            end
        end
        return vcat(dθ, dφ, dpop)
    end
    return f, X
end

# R∞ from the edge-based ODE with seeds ρ (a Dict species ⇒ fraction), integrated to large t.
function eb_final_size(cm, d, p, ρ::AbstractDict; tmax = 500.0, h = 0.01)
    q = 1 - sum(values(ρ))
    f, X = eb_field(cm, d, p, q)
    seeds = [get(ρ, x, 0.0) for x in X]
    u = rk4_final(f, vcat(1.0, seeds, seeds), h, round(Int, tmax / h))
    return 1 - q * pgf(d, u[1])
end

# The leading eigenvalue of the edge-based field linearised at the disease-free state (q = 1).
function eb_growth(cm, d, p)
    f, X = eb_field(cm, d, p, 1.0)
    n = length(X)
    return maximum(real, eigvals(fd_jacobian(f, vcat(1.0, zeros(2n)))))
end

# Probability that one infector, starting in `from`, transmits across one edge: a Monte Carlo
# walk over the model's transitions with the edge's transmission as a competing exit.
const Exits = Vector{Tuple{Float64,Union{Symbol,Nothing}}}

function mc_transmissibility(cm, p, from; n = 200_000, rng = MersenneTwister(20260926))
    tr = Dict{Symbol,Float64}()
    for c in contacts(cm)
        tr[c.infector] = get(tr, c.infector, 0.0) + rate_value(c.rate, p)
    end
    outs = Dict{Symbol,Exits}()
    for t in node_transitions(cm)
        push!(get!(outs, t.from, Exits()), (rate_value(t.rate, p), t.to))
    end
    hits = 0
    for _ in 1:n
        x = from
        while x !== nothing
            β = get(tr, x, 0.0)
            os = get(outs, x, Exits())
            total = β + sum(first, os; init = 0.0)
            total == 0 && break
            u = rand(rng) * total
            if u < β
                hits += 1
                break
            end
            u -= β
            nxt = nothing
            for (a, y) in os
                if u < a
                    nxt = y
                    break
                end
                u -= a
            end
            x = nxt
        end
    end
    return hits / n
end

mc_tol(T) = 4 * sqrt(T * (1 - T) / 200_000)                          # 4 standard errors
spectral_radius(K) = maximum(abs, eigvals(K))
rho2(a, b, c, d) = (a + d) / 2 + sqrt(((a - d) / 2)^2 + b * c)       # ρ([a b; c d]), b c ≥ 0

# Models of the w1 counterexamples (ebm-analysis §2.1).
bypass_model() = ContactModel(:bypass; contacts = [Contact(:S, :I, :E, :τ)],
                              transitions = [NodeTransition(:E, :I, :(p * σ)),
                                             NodeTransition(:E, :R, :((1 - p) * σ)),
                                             NodeTransition(:I, :R, :γ)])
split_model() = ContactModel(:ai_split;
                             contacts = [Contact(:S, :A, :E, :τA), Contact(:S, :I, :E, :τI)],
                             transitions = [NodeTransition(:E, :A, :(p * σ)),
                                            NodeTransition(:E, :I, :((1 - p) * σ)),
                                            NodeTransition(:A, :R, :γA),
                                            NodeTransition(:I, :R, :γI)])

# A two-stratum SIR written out by hand (labels give the strata; contacts S_a + I_b → I_a + I_b).
function strat_sir(; τ = :τ, γ = :γ, types = (:a, :b))
    lab = Dict{Symbol,SpeciesLabel}()
    for a in types, (base, nm) in ((:S, :S_), (:I, :I_), (:R, :R_))
        lab[Symbol(nm, a)] = SpeciesLabel(base; stratum = a)
    end
    cs = [Contact(Symbol(:S_, a), Symbol(:I_, b), Symbol(:I_, a), τ) for a in types for b in types]
    ts = [NodeTransition(Symbol(:I_, a), Symbol(:R_, a), γ) for a in types]
    return ContactModel(:sir_strat; contacts = cs, transitions = ts, labels = lab)
end

# A layered SIR: one contact per layer, each with its own rate.
layered_sir(pairs...) =
    ContactModel(:layered; contacts = [Contact(:S, :I, :I, τ; layer = ℓ) for (ℓ, τ) in pairs],
                 transitions = [NodeTransition(:I, :R, :γ)])

struct NotAGraph end                       # an explicit graph that no back end can analyse
struct WrappedSIR end                      # a foreign model description
NEC.contact_model(::WrappedSIR) = sir_model()

function caught(f)
    try
        f()
    catch e
        return e
    end
    return nothing
end

const P0 = Dict(:τ => 1 / 6, :γ => 1 / 4)
const POIS5 = ConfigurationNetwork(PoissonDegree(5))
const ANCHORS = (RegularDegree(6), PoissonDegree(5), NegBinDegree(mean = 4, var = 8),
                 EmpiricalDegree(Dict(2 => 5 / 6, 10 => 1 / 6)))
const PSEAIR = Dict(:τI => 1 / 6, :τA => 1 / 12, :p => 0.6, :σ => 1 / 5, :γ => 1 / 4)

# =============================================================================================

@testset "transmissibility: the absorption formula (E14)" begin
    @testset "SIR and Erlang stages" begin
        for (τ, γ) in ((1 / 6, 1 / 4), (0.3, 0.1), (2.0, 0.5))
            T = transmissibility(sir_model(), POIS5, Dict(:τ => τ, :γ => γ))
            @test T ≈ τ / (τ + γ) rtol = 1e-14
        end
        τ, γ = 1 / 6, 1 / 4
        for n in 1:6
            cm = erlang_stages(sir_model(), :I, n)
            Tn = 1 - (n * γ / (τ + n * γ))^n
            @test transmissibility(cm, POIS5, P0) ≈ Tn rtol = 1e-12
            @test basic_reproduction_number(cm, POIS5, P0) ≈ 5Tn rtol = 1e-12
        end
        erl3 = erlang_stages(sir_model(), :I, 3)
        @test round(transmissibility(erl3, POIS5, P0); digits = 4) == 0.4523   # :sir_erl3_pois5
        @test round(basic_reproduction_number(erl3, POIS5, P0); digits = 2) == 2.26
    end

    @testset "SEAIR: T = 0.34, R0 = 1.70" begin
        T = 0.6 * (1 / 6) / (1 / 6 + 1 / 4) + 0.4 * (1 / 12) / (1 / 12 + 1 / 4)
        @test T ≈ 0.34
        @test transmissibility(seair_model(), POIS5, PSEAIR) ≈ 0.34 rtol = 1e-12
        @test basic_reproduction_number(seair_model(), POIS5, PSEAIR) ≈ 1.70 rtol = 1e-12
        byc = transmissibility(seair_model(), POIS5, PSEAIR; by_contact = true)
        @test byc isa Dict{Symbol,Float64}
        @test byc[:S_I_to_E] ≈ 0.24 rtol = 1e-12
        @test byc[:S_A_to_E] ≈ 0.10 rtol = 1e-12
        @test transmissibility(seair_model(), POIS5, PSEAIR; from = :I) ≈ (1 / 6) / (1 / 6 + 1 / 4)
        @test transmissibility(seair_model(), POIS5, PSEAIR; from = :R) == 0.0
        @test mc_transmissibility(seair_model(), PSEAIR, :E) ≈ 0.34 atol = mc_tol(0.34)
    end

    @testset "w1 counterexamples: bypass and A/I split" begin
        # (a) E → I at pσ, E → R at (1-p)σ: T = pτ/(τ+γ); p = 1/2, τ = γ = σ = 1: T = 1/4, R0 = 1.25
        pb = Dict(:τ => 1.0, :γ => 1.0, :σ => 1.0, :p => 0.5)
        @test transmissibility(bypass_model(), POIS5, pb) ≈ 0.25 rtol = 1e-14
        @test basic_reproduction_number(bypass_model(), POIS5, pb) ≈ 1.25 rtol = 1e-14   # old: 2.5
        @test mc_transmissibility(bypass_model(), pb, :E) ≈ 0.25 atol = mc_tol(0.25)
        for (p, τ) in ((0.3, 1.0), (0.8, 0.4))
            pp = Dict(:τ => τ, :γ => 1.0, :σ => 2.0, :p => p)
            @test transmissibility(bypass_model(), POIS5, pp) ≈ p * τ / (τ + 1) rtol = 1e-13
        end
        # (b) E → A with p, E → I with 1-p: T = 1 − [p γA/(τA+γA) + (1-p) γI/(τI+γI)]
        ps = Dict(:τA => 1.0, :τI => 1.0, :γA => 1.0, :γI => 1.0, :σ => 1.0, :p => 0.5)
        @test transmissibility(split_model(), POIS5, ps) ≈ 0.5 rtol = 1e-14            # old: 0.75
        @test basic_reproduction_number(split_model(), POIS5, ps) ≈ 2.5 rtol = 1e-14   # old: 3.75
        ps2 = Dict(:τA => 0.5, :τI => 2.0, :γA => 1.0, :γI => 1.0, :σ => 1.0, :p => 0.3)
        T2 = 1 - (0.3 * 1 / 1.5 + 0.7 * 1 / 3)
        @test transmissibility(split_model(), POIS5, ps2) ≈ T2 rtol = 1e-13
        @test basic_reproduction_number(split_model(), POIS5, ps2) ≈ 5T2 rtol = 1e-13  # E14: 2.8333
        @test mc_transmissibility(split_model(), ps2, :E) ≈ T2 atol = mc_tol(T2)
    end

    @testset "cycles: value iteration" begin
        # I1 ⇄ I2 → R with both stages infectious: u_i = (τ_i + Σ_j r_ij u_j)/(τ_i + out_i)
        cm = ContactModel(:cycle;
                          contacts = [Contact(:S, :I1, :I1, :τ1), Contact(:S, :I2, :I1, :τ2)],
                          transitions = [NodeTransition(:I1, :I2, :a), NodeTransition(:I2, :I1, :b),
                                         NodeTransition(:I2, :R, :γ)])
        p = Dict(:τ1 => 0.3, :τ2 => 0.7, :a => 1.0, :b => 0.5, :γ => 0.8)
        u1 = u2 = 0.0
        for _ in 1:10_000
            u1, u2 = (0.3 + 1.0 * u2) / (0.3 + 1.0), (0.7 + 0.5 * u1) / (0.7 + 0.5 + 0.8)
        end
        @test transmissibility(cm, POIS5, p) ≈ u1 rtol = 1e-12
        @test transmissibility(cm, POIS5, p; from = :I2) ≈ u2 rtol = 1e-12
        @test basic_reproduction_number(cm, POIS5, p) ≈ 5u1 rtol = 1e-12
    end

    @testset "keywords and refusals" begin
        pse = Dict(:τ => 0.2, :σ => 0.5, :γ => 0.3)
        @test transmissibility(seir_model(), POIS5, pse) ≈ 0.4
        @test transmissibility(seir_model(), POIS5, pse; from = :I) ≈ 0.4
        two = twostrain_model()
        p2 = Dict(:τ1 => 1 / 6, :τ2 => 1 / 5, :γ => 1 / 4)
        @test_throws ArgumentError transmissibility(two, POIS5, p2)          # two entry states
        @test transmissibility(two, POIS5, p2; from = :I2) ≈ (1 / 5) / (1 / 5 + 1 / 4)
        @test_throws ArgumentError transmissibility(sir_model(), POIS5, P0; from = :S)
        @test_throws ArgumentError transmissibility(sir_model(), POIS5, P0; from = :Z)
        err = caught(() -> transmissibility(sir_model(), WellMixed(5), P0))
        @test err isa ArgumentError && occursin("fleeting", err.msg)
        # the per-partnership transmissibility of neighbour exchange: the partnership ends at η
        dyn = DynamicNetwork(RegularDegree(6), NeighbourExchange(0.5))
        @test transmissibility(sir_model(), dyn, P0) ≈ (1 / 6) / (1 / 6 + 1 / 4 + 0.5)
        mpx = MultiplexNetwork(:home => RegularDegree(3), :comm => PoissonDegree(5))
        lay = layered_sir(:home => :τh, :comm => :τc)
        pl = Dict(:τh => 0.5, :τc => 0.1, :γ => 0.25)
        @test_throws ArgumentError transmissibility(lay, mpx, pl)            # which layer?
        @test transmissibility(lay, mpx, pl; layer = :home) ≈ 0.5 / 0.75
        @test transmissibility(lay, mpx, pl; layer = :comm) ≈ 0.1 / 0.35
        @test_throws ArgumentError transmissibility(lay, mpx, pl; layer = :work)
        @test_throws ArgumentError transmissibility(sir_model(), POIS5, P0; layer = :home)
    end
end

@testset "next-generation matrix and R0 on configuration networks" begin
    @testset "anchors: excess degree 5, τ = 1/6, γ = 1/4" begin
        for d in ANCHORS
            net = ConfigurationNetwork(d)
            @test basic_reproduction_number(sir_model(), net, P0) ≈ 2.0 rtol = 1e-12
            @test early_growth_rate(sir_model(), net, P0) ≈ 5 / 12 rtol = 1e-12
            K = next_generation_matrix(sir_model(), net, P0)
            @test size(K) == (1, 1) && K[1, 1] ≈ 2.0
        end
        @test next_generation_labels(sir_model(), POIS5) == [(entry = :I,)]
        @test next_generation_labels(seir_model(), POIS5) == [(entry = :E,)]
    end

    @testset "several entry states: two strains" begin
        p2 = Dict(:τ1 => 1 / 6, :τ2 => 1 / 5, :γ => 1 / 4)
        K = next_generation_matrix(twostrain_model(), POIS5, p2)
        T1, T2 = (1 / 6) / (1 / 6 + 1 / 4), (1 / 5) / (1 / 5 + 1 / 4)
        @test K ≈ [5T1 0; 0 5T2] rtol = 1e-13
        @test basic_reproduction_number(twostrain_model(), POIS5, p2) ≈ 5T2
        @test next_generation_labels(twostrain_model(), POIS5) == [(entry = :I1,), (entry = :I2,)]
    end

    @testset "rate conventions (§B.6) and parameters" begin
        # FrequencyDependent on WellMixed(κ): τ = β/κ, so R0 = β/γ for every κ (the unit law M1)
        fd = ContactModel(:sir_fd; contacts = [Contact(:S, :I, :I, :β)],
                          transitions = [NodeTransition(:I, :R, :γ)],
                          convention = FrequencyDependent())
        pβ = Dict(:β => 0.5, :γ => 0.25)
        for κ in (2.0, 5.0, 20.0)
            @test basic_reproduction_number(fd, WellMixed(κ), pβ) ≈ 2.0
            @test early_growth_rate(fd, WellMixed(κ), pβ) ≈ 0.25
        end
        # on a configuration network τ = β/⟨k⟩: Regular(6), β = 1 ⇒ τ = 1/6
        @test basic_reproduction_number(fd, ConfigurationNetwork(RegularDegree(6)),
                                        Dict(:β => 1.0, :γ => 0.25)) ≈ 2.0
        dd = ContactModel(:sir_dd; contacts = [Contact(:S, :I, :I, :β)],
                          transitions = [NodeTransition(:I, :R, :γ)],
                          convention = DensityDependent(:N))
        @test basic_reproduction_number(dd, WellMixed(5.0),
                                        Dict(:β => 1e-4, :N => 5000.0, :γ => 0.25)) ≈ 2.0
        # defaults, NamedTuples, missing parameters
        withdef = ContactModel(:sird; contacts = [Contact(:S, :I, :I, :τ)],
                               transitions = [NodeTransition(:I, :R, :γ)],
                               defaults = Dict(:τ => 1 / 6, :γ => 1 / 4))
        @test basic_reproduction_number(withdef, POIS5) ≈ 2.0
        @test basic_reproduction_number(sir_model(), POIS5, (τ = 1 / 6, γ = 1 / 4)) ≈ 2.0
        @test basic_reproduction_number(sir_model(; τ = 1 / 6, γ = 0.25), POIS5) ≈ 2.0
        err = caught(() -> basic_reproduction_number(sir_model(), POIS5, Dict(:τ => 0.1)))
        @test err isa ArgumentError && occursin("γ", err.msg)
    end

    @testset "admissibility and descriptors" begin
        # the network NGM is the edge-based linearisation: SIS and SIRS are refused on networks
        @test_throws AdmissibilityError basic_reproduction_number(
            sis_model(), ConfigurationNetwork(RegularDegree(3)), Dict(:τ => 0.5, :γ => 0.25))
        @test_throws AdmissibilityError final_size(sirs_model(), POIS5,
                                                   Dict(:τ => 0.5, :γ => 0.25, :ε => 0.1))
        clustered = ClusteredNetwork(RegularDegree(2), RegularDegree(2))
        err = caught(() -> basic_reproduction_number(sir_model(), clustered, P0))
        @test err isa ArgumentError && occursin("EdgeBasedModels", err.msg)
        @test_throws ArgumentError basic_reproduction_number(sir_model(),
                                                             ExplicitGraph(NotAGraph()), P0)
        dormant = DynamicNetwork(RegularDegree(4), DormantContacts(1.0, 1.0))
        @test_throws ArgumentError basic_reproduction_number(sir_model(), dormant, P0)
        # any model that contact_model accepts
        @test basic_reproduction_number(WrappedSIR(), POIS5, P0) ≈ 2.0
        @test final_size(WrappedSIR(), POIS5, P0) ≈ final_size(sir_model(), POIS5, P0)
        # no edges: no transmission
        noedges = ConfigurationNetwork(PoissonDegree(0.0))
        @test basic_reproduction_number(sir_model(), noedges, P0) == 0.0
        @test final_size(sir_model(), noedges, P0; initial = SeedFraction(:I => 0.01)) ≈ 0.01
    end
end

@testset "fleeting contacts: WellMixed and MFSH" begin
    pw = Dict(:τ => 1 / 10, :γ => 1 / 4)                       # :sir_wm5, β = κτ = 1/2
    @test basic_reproduction_number(sir_model(), WellMixed(5), pw) ≈ 2.0
    @test early_growth_rate(sir_model(), WellMixed(5), pw) ≈ 0.5 - 0.25
    @test next_generation_labels(sir_model(), WellMixed(5)) == [(entry = :I,)]
    # SEIR mass action: R0 = κτ/γ, r the dominant root of (r + σ)(r + γ) = σκτ
    ps = Dict(:τ => 0.1, :σ => 0.2, :γ => 0.25)
    rr = (-(0.2 + 0.25) + sqrt((0.2 - 0.25)^2 + 4 * 0.2 * 0.5)) / 2
    @test basic_reproduction_number(seir_model(), WellMixed(5), ps) ≈ 2.0
    @test early_growth_rate(seir_model(), WellMixed(5), ps) ≈ rr rtol = 1e-12
    # arrows back into S are fine for the mass-action NGM
    @test basic_reproduction_number(sis_model(), WellMixed(4), Dict(:τ => 0.2, :γ => 0.25)) ≈ 3.2
    @test basic_reproduction_number(sirs_model(), WellMixed(4),
                                    Dict(:τ => 0.2, :γ => 0.25, :ε => 0.01)) ≈ 3.2
    # an infinite infectious period has an infinite well-mixed R0
    si = ContactModel(:si; contacts = [Contact(:S, :I, :I, :τ)])
    err = caught(() -> basic_reproduction_number(si, WellMixed(5), Dict(:τ => 0.1)))
    @test err isa ArgumentError && occursin("infinite", err.msg)
    @test basic_reproduction_number(si, POIS5, Dict(:τ => 0.1)) ≈ 5.0   # T = 1 on persistent edges
    # MFSH (the η → ∞ limit of DFD): R0 = τE[k²]/(γE[k]) = 4 on Poisson(5) (judge check, Λ3)
    mfsh = MFSHNetwork(PoissonDegree(5))
    @test basic_reproduction_number(sir_model(), mfsh, P0) ≈ 4.0
    @test early_growth_rate(sir_model(), mfsh, P0) ≈ 6 / 6 - 1 / 4
    for κ in (3, 6)
        for f in (basic_reproduction_number, early_growth_rate)
            @test f(seir_model(), MFSHNetwork(RegularDegree(κ)), ps) ≈
                  f(seir_model(), WellMixed(κ), ps)
        end
        @test final_size(sir_model(), MFSHNetwork(RegularDegree(κ)), P0) ≈
              final_size(sir_model(), WellMixed(κ), P0) rtol = 1e-10
    end
end

@testset "multiplex: R0 = ρ(K), not the sum of layer R0s (E12)" begin
    γ = 1.0
    τof(T) = T * γ / (1 - T)
    # two 3-regular layers at T = 0.22: K = T[2 3; 3 2], ρ = 5T = 1.10 (additive: 0.88)
    T = 0.22
    mpx = MultiplexNetwork(:a => RegularDegree(3), :b => RegularDegree(3))
    R0 = basic_reproduction_number(sir_model(), mpx, Dict(:τ => τof(T), :γ => γ))
    @test R0 ≈ rho2(2T, 3T, 3T, 2T) rtol = 1e-12
    @test R0 ≈ 1.10 rtol = 1e-12
    @test !isapprox(R0, 2T + 2T; rtol = 0.1)
    @test next_generation_labels(sir_model(), mpx) ==
          [(layer = :a, entry = :I), (layer = :b, entry = :I)]
    # the same as two layer-labelled contacts with the same τ
    lay = layered_sir(:a => :τ, :b => :τ)
    @test basic_reproduction_number(lay, mpx, Dict(:τ => τof(T), :γ => γ)) ≈ R0 rtol = 1e-12
    # 4-regular + 3-regular at T = 0.3: ρ([0.9 1.2; 0.9 0.6]) = 1.8 (additive 1.5)
    mpx43 = MultiplexNetwork(:a => RegularDegree(4), :b => RegularDegree(3))
    @test basic_reproduction_number(sir_model(), mpx43, Dict(:τ => τof(0.3), :γ => γ)) ≈ 1.8 rtol =
        1e-12
    # over-dispersed layers ψ = (x + x⁷)/2 at T = 0.1: 0.925, although the sum says 1.05
    bim = EmpiricalDegree(Dict(1 => 0.5, 7 => 0.5))
    mb = MultiplexNetwork(:a => bim, :b => bim)
    p01 = Dict(:τ => τof(0.1), :γ => γ)
    @test basic_reproduction_number(sir_model(), mb, p01) ≈ 0.925 rtol = 1e-12
    @test early_growth_rate(sir_model(), mb, p01) < 0
    # heterogeneous T by layer: 3-regular at T = 0.3 and 5-regular at T = 0.1 (E12 skeptic: 1.1782)
    het = layered_sir(:a => :τa, :b => :τb)
    m35 = MultiplexNetwork(:a => RegularDegree(3), :b => RegularDegree(5))
    ph = Dict(:τa => τof(0.3), :τb => τof(0.1), :γ => γ)
    # offspring of a node infected along layer m, infecting along layer ℓ: T_ℓ × (excess or mean)
    @test basic_reproduction_number(het, m35, ph) ≈ rho2(0.3 * 2, 0.3 * 3, 0.1 * 5, 0.1 * 4) rtol =
        1e-12
    @test round(basic_reproduction_number(het, m35, ph); digits = 4) == 1.1782
    # Poisson layers: the sum is exact
    mp = MultiplexNetwork(:home => PoissonDegree(3.0), :work => PoissonDegree(2.0))
    hw = layered_sir(:home => :τa, :work => :τb)
    phw = Dict(:τa => 0.3, :τb => 0.2, :γ => 0.1)
    @test basic_reproduction_number(hw, mp, phw) ≈ 0.75 * 3 + (2 / 3) * 2 rtol = 1e-12
    # growth rate: two 3-regular layers behave as one 6-regular network
    p6 = Dict(:τ => 0.2, :γ => 0.25)
    reg6 = ConfigurationNetwork(RegularDegree(6))
    @test early_growth_rate(sir_model(), mpx, p6) ≈ early_growth_rate(sir_model(), reg6, p6)
    @test early_growth_rate(sir_model(), mpx, p6) ≈ 0.2 * 4 - 0.25
end

@testset "typed networks: SBM, unstructured strata, degree correlations" begin
    sbm = sbm_network([:a, :b], [0.5, 0.5]; mean_contacts = [6.0 2.0; 2.0 4.0])
    cm = strat_sir()
    @testset "Poisson SBM: R0 = T ρ(M), ρ(M) = 7.236 ⇒ τ = 0.0955" begin
        ρM = 5 + sqrt(5)
        @test round(ρM; digits = 3) == 7.236
        @test basic_reproduction_number(cm, sbm, P0) ≈ 0.4 * ρM rtol = 1e-12
        @test early_growth_rate(cm, sbm, P0) ≈ (1 / 6) * ρM - 1 / 6 - 1 / 4 rtol = 1e-12
        cal = calibrate(cm, sbm, P0; target = :R0 => 2.0, vary = :τ)
        T = 2 / ρM
        @test cal[:τ] ≈ T * 0.25 / (1 - T) rtol = 1e-10
        @test round(cal[:τ]; digits = 4) == 0.0955
        @test cal[:γ] == 0.25
        @test length(next_generation_labels(cm, sbm)) == 4
        @test (type = :a, from = :b, entry = :I_a) in next_generation_labels(cm, sbm)
        # structural zeros make no blocks
        blocks = sbm_network([:a, :b], [0.5, 0.5]; mean_contacts = [3.0 0.0; 0.0 5.0])
        @test length(next_generation_labels(cm, blocks)) == 2
        @test basic_reproduction_number(cm, blocks, P0) ≈ 0.4 * 5
        # an unstratified model does not fit a typed network
        @test_throws AdmissibilityError basic_reproduction_number(sir_model(), sbm, P0)
    end

    @testset "regular blocks: the edge-type NGM (hand-derived)" begin
        # a-nodes: 2 edges to a, 1 to b; b-nodes: 1 to a, 3 to b (sizes 1/2: 1/2·1 = 1/2·1)
        rb = MultitypeNetwork([:a, :b], [0.5, 0.5],
                              [IndependentDegrees(:a => RegularDegree(2), :b => RegularDegree(1)),
                               IndependentDegrees(:a => RegularDegree(1), :b => RegularDegree(3))])
        T = 0.4
        # types of infected nodes: a-by-a, a-by-b, b-by-a, b-by-b (columns: parent; rows: child)
        K = [T 2T 0 0;       # child a infected by a: parent a-by-a has 1 other a-edge, a-by-b 2
             0 0 0 T;        # child a infected by b: parent b-by-a has no other a-edge, b-by-b 1
             T 0 0 0;        # child b infected by a: parent a-by-a has its b-edge, a-by-b none
             0 0 3T 2T]      # child b infected by b: parent b-by-a has 3 b-edges, b-by-b 2
        R0 = basic_reproduction_number(cm, rb, P0)
        @test R0 ≈ spectral_radius(K) rtol = 1e-12
        # the (type, entry) shortcut T ρ(mean contacts) is wrong here
        @test !isapprox(R0, T * spectral_radius([2.0 1.0; 1.0 3.0]); rtol = 1e-3)
    end

    @testset "unstructured strata reproduce the unstratified model (M10)" begin
        for d in (RegularDegree(6), PoissonDegree(5), last(ANCHORS))
            base = ConfigurationNetwork(d)
            un = unstructured(base, [:a, :b], [0.3, 0.7])
            @test basic_reproduction_number(cm, un, P0) ≈
                  basic_reproduction_number(sir_model(), base, P0) rtol = 1e-10
            @test early_growth_rate(cm, un, P0) ≈ early_growth_rate(sir_model(), base, P0) rtol =
                1e-10
            @test final_size(cm, un, P0) ≈ final_size(sir_model(), base, P0) rtol = 1e-10
            @test final_size(cm, un, P0; initial = SeedFraction(:I_a => 0.003, :I_b => 0.007)) ≈
                  final_size(sir_model(), base, P0; initial = SeedFraction(:I => 0.01)) rtol = 1e-10
        end
    end

    @testset "strata inferred without labels on the infected species" begin
        lab = Dict(:S_a => SpeciesLabel(:S; stratum = :a), :S_b => SpeciesLabel(:S; stratum = :b))
        cs = [Contact(Symbol(:S_, a), Symbol(:I_, b), Symbol(:I_, a), :τ) for a in (:a, :b)
              for b in (:a, :b)]
        ts = [NodeTransition(Symbol(:I_, a), Symbol(:R_, a), :γ) for a in (:a, :b)]
        bare = ContactModel(:bare; contacts = cs, transitions = ts, labels = lab)
        @test basic_reproduction_number(bare, sbm, P0) ≈ basic_reproduction_number(cm, sbm, P0)
    end

    @testset "degree-correlated networks (E20): T ρ(C), C_kl = (k−1) Q(l|k)" begin
        bim = EmpiricalDegree(Dict(2 => 5 / 6, 10 => 1 / 6))
        for r in (0.0, 0.3, 0.6)
            dc = degree_correlated(bim; r)
            Q = dc.edge_ends ./ sum(dc.edge_ends; dims = 2)
            k = dc.degrees
            C = [(k[i] - 1) * Q[i, j] for i in eachindex(k), j in eachindex(k)]
            @test basic_reproduction_number(sir_model(), dc, P0) ≈ 0.4 * spectral_radius(C) rtol =
                1e-10
        end
        neutral = degree_correlated(bim; r = 0.0)
        @test basic_reproduction_number(sir_model(), neutral, P0) ≈ 2.0 rtol = 1e-10
        # a 2-regular network is 2-regular whatever the mixing: R0 = T (no spurious r(k−1) roots)
        @test basic_reproduction_number(sir_model(), degree_correlated(RegularDegree(2); r = 0.5),
                                        Dict(:τ => 1e6, :γ => 1e-6)) ≈ 1.0 rtol = 1e-8
        # neutral mixing gives the uncorrelated final size
        @test final_size(sir_model(), neutral, P0) ≈
              final_size(sir_model(), ConfigurationNetwork(bim), P0) rtol = 1e-10
        @test transmissibility(sir_model(), degree_correlated(bim; r = 0.4), P0) ≈ 0.4
    end
end

@testset "early growth rate: linearised edge-based field" begin
    # SIR: r = τ(κ_ex − 1) − γ; SEIR: the dominant root of (r + σ)(r + τ + γ) = στκ_ex
    for (τ, γ) in ((1 / 6, 1 / 4), (0.5, 0.2), (0.05, 0.3))
        @test early_growth_rate(sir_model(), POIS5, Dict(:τ => τ, :γ => γ)) ≈ τ * 4 - γ rtol = 1e-12
    end
    τ, σ, γ = 1 / 6, 1 / 5, 1 / 4
    b = σ + τ + γ
    c = σ * (τ + γ) - σ * τ * 5
    @test early_growth_rate(seir_model(), POIS5, Dict(:τ => τ, :σ => σ, :γ => γ)) ≈
          (-b + sqrt(b^2 - 4c)) / 2 rtol = 1e-12
    # branching models against the finite-difference Jacobian of the §D.4 field written out here
    for d in (PoissonDegree(5), EmpiricalDegree(Dict(2 => 5 / 6, 10 => 1 / 6)), RegularDegree(6))
        @test early_growth_rate(seair_model(), ConfigurationNetwork(d), PSEAIR) ≈
              eb_growth(seair_model(), d, PSEAIR) rtol = 1e-6
    end
    ps2 = Dict(:τA => 0.5, :τI => 2.0, :γA => 1.0, :γI => 1.0, :σ => 1.0, :p => 0.3)
    @test early_growth_rate(split_model(), POIS5, ps2) ≈
          eb_growth(split_model(), PoissonDegree(5), ps2) rtol = 1e-6
    # r > 0 exactly when R0 > 1
    for τI in (0.02, 0.05, 0.08, 0.12, 0.3)
        q = merge(PSEAIR, Dict(:τI => τI, :τA => τI / 2))
        @test sign(early_growth_rate(seair_model(), POIS5, q)) ==
              sign(basic_reproduction_number(seair_model(), POIS5, q) - 1)
    end
end

@testset "neighbour exchange (DFD)" begin
    pd = Dict(:τ => 1 / 12, :γ => 1 / 4)
    base = RegularDegree(6)
    κex, τ, γ = 5.0, 1 / 12, 1 / 4
    static = DynamicNetwork(base, NeighbourExchange(0.0))
    @test basic_reproduction_number(sir_model(), static, pd) ≈
          basic_reproduction_number(sir_model(), ConfigurationNetwork(base), pd)
    @test basic_reproduction_number(sir_model(), static, pd) ≈ 1.25
    # the Miller–Slim–Volz DFD SIR field (Part II §3.2.3), linearised by finite differences here
    function dfd_field(η)
        ψ1(x) = pgf_derivative(base, x, 1)
        ψ2(x) = pgf_derivative(base, x, 2)
        return function (u)
            θ, φS, φI, πR = u
            πS = θ * ψ1(θ) / ψ1(1.0)
            πI = 1 - πR - πS
            [-τ * φI,
             -τ * φI * φS * ψ2(θ) / ψ1(θ) + η * θ * πS - η * φS,
             τ * φI * φS * ψ2(θ) / ψ1(θ) + η * θ * πI - (τ + γ + η) * φI,
             γ * πI]
        end
    end
    for η in (0.1, 1.0, 10.0)
        net = DynamicNetwork(base, NeighbourExchange(η))
        R0 = τ * ((γ + η) * κex + η) / (γ * (γ + η + τ))
        @test basic_reproduction_number(sir_model(), net, pd) ≈ R0 rtol = 1e-12
        r_msv = maximum(real, eigvals(fd_jacobian(dfd_field(η), [1.0, 1.0, 0.0, 0.0])))
        @test early_growth_rate(sir_model(), net, pd) ≈ r_msv rtol = 1e-6
        @test next_generation_labels(sir_model(), net) == [(entry = :I,)]
    end
    # η → ∞ on a regular base: MA(6τ) = WellMixed(6) (Λ3): R0 → 2, r → 6τ − γ
    fast = DynamicNetwork(base, NeighbourExchange(1e7))
    @test basic_reproduction_number(sir_model(), fast, pd) ≈ 2.0 rtol = 1e-6
    @test early_growth_rate(sir_model(), fast, pd) ≈
          early_growth_rate(sir_model(), WellMixed(6), pd) rtol = 1e-5
    # SEIR: monotone in η between the static and the MFSH values
    pse = Dict(:τ => 1 / 12, :σ => 0.5, :γ => 1 / 4)
    vals = [basic_reproduction_number(seir_model(), DynamicNetwork(base, NeighbourExchange(η)), pse)
            for η in (0.0, 0.1, 1.0, 10.0, 1e6)]
    @test issorted(vals)
    @test vals[end] ≈ basic_reproduction_number(seir_model(), MFSHNetwork(base), pse) rtol = 1e-5
    @test_throws ArgumentError final_size(sir_model(), DynamicNetwork(base, NeighbourExchange(1.0)),
                                          pd)
end

@testset "final size (E18: brackets, convergence, exact zero)" begin
    @testset "ρ → 0 and near threshold" begin
        # Poisson(κ): R∞ = 1 − exp(−R0 R∞)
        R = bisect(r -> r - (1 - exp(-2r)), 1e-3, 1.0)
        @test final_size(sir_model(), POIS5, P0) ≈ R rtol = 1e-12
        @test round(final_size(sir_model(), POIS5, P0); digits = 6) == 0.796812      # E15 anchor
        mk(R0) = (T = R0 / 5; Dict(:τ => T / (1 - T), :γ => 1.0))
        for (R0, Rref) in ((1.001, 1.997336441e-3), (1.005, 9.933720086e-3), (1.01, 1.973641044e-2))
            fs = final_size(sir_model(), POIS5, mk(R0))
            @test fs ≈ Rref rtol = 1e-6                     # the old iteration: 1.35e-5 at 1.001
            @test fs ≈ 1 - exp(-R0 * fs) rtol = 1e-8
        end
        for R0 in (0.5, 0.6, 0.9, 0.99, 0.999, 1.0)
            @test final_size(sir_model(), POIS5, mk(R0)) === 0.0
        end
        # a polynomial degree law near threshold, against a BigFloat bisection of the same equation
        dpoly = EmpiricalDegree([0.05, 0.15, 0.2, 0.2, 0.2, 0.1, 0.1])
        T = 1.001 / excess_degree(dpoly)
        ψ1(x) = sum(k * dpoly.p[k + 1] * x^(k - 1) for k in 1:6)
        ψ(x) = sum(dpoly.p[k + 1] * x^k for k in 0:6)
        g(u) = let θ = 1 - u
            1 - BigFloat(T) + BigFloat(T) * ψ1(θ) / ψ1(big(1.0)) - θ
        end
        u = bisect(g, big(1e-6), big(0.5); iters = 300)
        pnear = Dict(:τ => T / (1 - T), :γ => 1.0)
        Rnear = Float64(1 - ψ(1 - u))
        @test final_size(sir_model(), ConfigurationNetwork(dpoly), pnear) ≈ Rnear rtol = 1e-6
    end

    @testset "seeds, against the edge-based ODE" begin
        ρ = Dict(:I => 0.01)
        seed = SeedFraction(:I => 0.01)
        indicative = (0.9295, 0.8002, 0.6408, 0.4956)            # §E.3, ρ = 0.01
        for (d, ref) in zip(ANCHORS, indicative)
            fs = final_size(sir_model(), ConfigurationNetwork(d), P0; initial = seed)
            @test fs ≈ eb_final_size(sir_model(), d, P0, ρ) atol = 2e-8
            @test round(fs; digits = 4) ≈ ref atol = 1.5e-4
        end
        @test final_size(seair_model(), POIS5, PSEAIR; initial = SeedFraction(:E => 0.01)) ≈
              eb_final_size(seair_model(), PoissonDegree(5), PSEAIR, Dict(:E => 0.01)) atol = 2e-8
        # seeds in several states, including pre-immune R and a later infectious stage
        mixed = Dict(:E => 0.004, :I => 0.003, :R => 0.05)
        @test final_size(seair_model(), POIS5, PSEAIR; initial = SeedFraction(mixed...)) ≈
              eb_final_size(seair_model(), PoissonDegree(5), PSEAIR, mixed) atol = 2e-8
        # a background compartment named in the seeding is ignored; SeedCount needs N
        named = SeedFraction(:S => 0.99, :I => 0.01; default = :S)
        @test final_size(sir_model(), POIS5, P0; initial = named) ≈
              final_size(sir_model(), POIS5, P0; initial = seed)
        @test final_size(sir_model(), POIS5, P0; initial = SeedCount(:I => 100), N = 10_000) ≈
              final_size(sir_model(), POIS5, P0; initial = seed)
        @test_throws ArgumentError final_size(sir_model(), POIS5, P0;
                                              initial = SeedFraction(:Z => 0.01))
        # seeds that cannot transmit (pre-immune only): the large-outbreak limit plus the seeds
        fsR = final_size(sir_model(), POIS5, P0; initial = SeedFraction(:R => 0.3))
        q = 0.7
        θ = bisect(t -> 1 - 0.4 + 0.4 * 0.3 + 0.4 * q * exp(5 * (t - 1)) - t, 0.0, 1 - 1e-3)
        @test fsR ≈ 1 - q * exp(5 * (θ - 1)) rtol = 1e-10
        @test final_size(sir_model(), POIS5, Dict(:τ => 0.02, :γ => 0.25);
                         initial = SeedFraction(:R => 0.3)) ≈ 0.3
    end

    @testset "w1 counterexamples and T-only dependence" begin
        pb = Dict(:τ => 1.0, :γ => 1.0, :σ => 1.0, :p => 0.5)
        @test final_size(bypass_model(), POIS5, pb) ≈ 0.371370 atol = 2e-6      # E14; old 0.8926
        @test final_size(bypass_model(), POIS5, merge(pb, Dict(:p => 0.3))) === 0.0   # R0 = 0.75
        ps = Dict(:τA => 1.0, :τI => 1.0, :γA => 1.0, :γI => 1.0, :σ => 1.0, :p => 0.5)
        @test final_size(split_model(), POIS5, ps) ≈ 0.892645 atol = 2e-6       # E14; old 0.974082
        # the final size depends on the sojourn only through T (not so P(major), E15)
        erl = erlang_stages(sir_model(), :I, 3)
        τ3 = bisect(t -> transmissibility(erl, POIS5, Dict(:τ => t, :γ => 0.25)) - 0.4, 0.01, 1.0)
        @test final_size(erl, POIS5, Dict(:τ => τ3, :γ => 0.25)) ≈
              final_size(sir_model(), POIS5, P0) rtol = 1e-10
    end

    @testset "well mixed, MFSH, multiplex and typed networks" begin
        pw = Dict(:τ => 1 / 10, :γ => 1 / 4)
        seed = SeedFraction(:I => 0.01)
        R = bisect(r -> r - (1 - exp(-2r)), 1e-3, 1.0)
        @test final_size(sir_model(), WellMixed(5), pw) ≈ R rtol = 1e-12
        # the Poisson configuration model with the same T has the same final size, seeds included
        @test final_size(sir_model(), WellMixed(5), pw; initial = seed) ≈
              final_size(sir_model(), POIS5, P0; initial = seed) rtol = 1e-12
        @test final_size(sir_model(), WellMixed(5), Dict(:τ => 0.04, :γ => 0.25)) === 0.0
        # mass-action SEIR with seeds, against RK4
        pse = Dict(:τ => 0.1, :σ => 0.2, :γ => 0.25)
        seir_ma(u) = [-0.5 * u[1] * u[3], 0.5 * u[1] * u[3] - 0.2 * u[2], 0.2 * u[2] - 0.25 * u[3]]
        ma = rk4_final(seir_ma, [0.99, 0.01, 0.0], 0.02, 40_000)
        @test final_size(seir_model(), WellMixed(5), pse; initial = SeedFraction(:E => 0.01)) ≈
              1 - ma[1] atol = 1e-8
        # MFSH on Poisson(5) with 1% seeds, against the degree-class ODE (judge check: 0.905)
        μ = 5.0
        ks = 0:60
        pk = Float64.([exp(-big(μ)) * big(μ)^k / factorial(big(k)) for k in ks])
        pk ./= sum(pk)
        ρ, q, τ, γ = 0.01, 0.99, 1 / 6, 1 / 4
        function mfsh_field(u)
            θ, Ik = u[1], u[2:end]
            πI = sum(ks .* pk .* Ik) / μ
            return vcat(-τ * θ * πI, ks .* τ .* πI .* (q .* θ .^ ks) .- γ .* Ik)
        end
        u = rk4_final(mfsh_field, vcat(1.0, fill(ρ, length(ks))), 0.01, 30_000)
        ref = 1 - sum(pk .* q .* u[1] .^ ks)
        fsm = final_size(sir_model(), MFSHNetwork(PoissonDegree(5)), P0; initial = seed)
        @test fsm ≈ ref atol = 1e-7
        @test round(fsm; digits = 3) == 0.905
        v = bisect(v -> (τ / γ) * (1 - exp(-v) * exp(μ * (exp(-v) - 1))) - v, 1e-3, 10.0)
        @test final_size(sir_model(), MFSHNetwork(PoissonDegree(5)), P0) ≈
              1 - exp(μ * (exp(-v) - 1)) rtol = 1e-10
        # multiplex: two 3-regular layers = one 6-regular layer (E12: 0.254041)
        T = 0.22
        p22 = Dict(:τ => T / (1 - T), :γ => 1.0)
        mpx = MultiplexNetwork(:a => RegularDegree(3), :b => RegularDegree(3))
        θ = bisect(t -> 1 - T + T * t^5 - t, 0.0, 0.99)
        @test final_size(sir_model(), mpx, p22) ≈ 1 - θ^6 rtol = 1e-10
        @test round(final_size(sir_model(), mpx, p22); digits = 6) == 0.254041
        reg6 = ConfigurationNetwork(RegularDegree(6))
        @test final_size(sir_model(), mpx, p22; initial = seed) ≈
              final_size(sir_model(), reg6, p22; initial = seed) rtol = 1e-10
        @test final_size(sir_model(), mpx, Dict(:τ => 0.19 / 0.81, :γ => 1.0)) === 0.0  # ρ(K) 0.95
        # Poisson SBM with seeds, against a plain fixed-point iteration of the typed equations
        sbm = sbm_network([:a, :b], [0.4, 0.6]; mean_contacts = [6.0 3.0; 2.0 4.0])
        cm = strat_sir()
        M = [6.0 3.0; 2.0 4.0]
        n = [0.4, 0.6]
        Tt = 0.4
        f = [0.004 / 0.4, 0.006 / 0.6]
        qq = 1 .- f
        θk = ones(2, 2)            # θk[b, a]: an a-node's edge to a b-partner has not transmitted
        ψ(b, θk) = exp(sum(M[b, c] * (θk[c, b] - 1) for c in 1:2))
        for _ in 1:20_000
            θk = [f[b] * (1 - Tt) + qq[b] * (1 - Tt + Tt * ψ(b, θk)) for b in 1:2, a in 1:2]
        end
        ref = 1 - sum(n[b] * qq[b] * ψ(b, θk) for b in 1:2)
        @test final_size(cm, sbm, P0; initial = SeedFraction(:I_a => 0.004, :I_b => 0.006)) ≈
              ref rtol = 1e-10
        @test final_size(cm, sbm, Dict(:τ => 0.01, :γ => 0.25)) === 0.0
        # the seeds of a stratum cannot exceed its size
        @test_throws ArgumentError final_size(cm, sbm, P0; initial = SeedFraction(:I_a => 0.5))
    end

    @testset "refusals: exits, several entries, SIS" begin
        pv = Dict(:τ => 1 / 6, :γ => 1 / 4, :ν => 0.02)
        err = caught(() -> final_size(sirv_model(), POIS5, pv))
        @test err isa ArgumentError && occursin("exits", err.msg)
        # R0 of the vaccination model is taken at ξ = 1
        @test basic_reproduction_number(sirv_model(), POIS5, pv) ≈ 2.0
        p2 = Dict(:τ1 => 1 / 6, :τ2 => 1 / 5, :γ => 1 / 4)
        err = caught(() -> final_size(twostrain_model(), POIS5, p2))
        @test err isa ArgumentError && occursin("several entry states", err.msg)
        # SIS and SIRS have no final size, even where their NGM is defined (well mixed)
        err = caught(() -> final_size(sis_model(), WellMixed(4), Dict(:τ => 0.2, :γ => 0.25)))
        @test err isa ArgumentError && occursin("endemic", err.msg)
        @test_throws ArgumentError final_size(sirs_model(), MFSHNetwork(PoissonDegree(5)),
                                              Dict(:τ => 0.2, :γ => 0.25, :ε => 0.01))
    end
end

@testset "calibrate" begin
    @testset "round trips" begin
        R0 = basic_reproduction_number(sir_model(), POIS5, P0)
        cal = calibrate(sir_model(), POIS5, Dict(:τ => 0.5, :γ => 0.25); target = :R0 => R0)
        @test cal isa Dict{Symbol,Float64}
        @test cal[:τ] ≈ 1 / 6 rtol = 1e-10
        @test cal[:γ] == 0.25
        r = early_growth_rate(seair_model(), POIS5, PSEAIR)
        cal = calibrate(seair_model(), POIS5, merge(PSEAIR, Dict(:τI => 1.0));
                        target = :growth => r, vary = :τI)
        @test cal[:τI] ≈ 1 / 6 rtol = 1e-10
        reg6 = ConfigurationNetwork(RegularDegree(6))
        seed = SeedFraction(:I => 0.01)
        z = final_size(sir_model(), reg6, P0; initial = seed)
        cal = calibrate(sir_model(), reg6, Dict(:τ => 0.05, :γ => 0.25);
                        target = :final_size => z, initial = seed)
        @test cal[:τ] ≈ 1 / 6 rtol = 1e-9
        # a decreasing relation: vary the recovery rate
        cal = calibrate(sir_model(), POIS5, Dict(:τ => 1 / 6, :γ => 2.0); target = :R0 => 2.0,
                        vary = :γ)
        @test cal[:γ] ≈ 0.25 rtol = 1e-10
        @test calibrate(sir_model(), POIS5, P0; target = :r => 5 / 12)[:τ] ≈ 1 / 6 rtol = 1e-10
        @test calibrate(sir_model(), POIS5, P0; target = :R0 => 2.0, bracket = (0.01, 1.0))[:τ] ≈
              1 / 6 rtol = 1e-10
    end

    @testset "the multiplex scenario: τ_home = 3c, τ_comm = c (NGM R0 = 2)" begin
        mpx = MultiplexNetwork(:home => RegularDegree(3), :comm => PoissonDegree(5))
        lay = layered_sir(:home => :(3 * c), :comm => :c)
        cal = calibrate(lay, mpx, Dict(:c => 0.1, :γ => 0.25); target = :R0 => 2.0, vary = :c)
        @test basic_reproduction_number(lay, mpx, cal) ≈ 2.0 rtol = 1e-10
        c = cal[:c]
        Th, Tc = 3c / (3c + 0.25), c / (c + 0.25)
        # rows: infecting along home, comm; columns: infected along home, comm
        @test 2.0 ≈ rho2(2Th, 3Th, 5Tc, 5Tc) rtol = 1e-9
        # the wrong additive R0 would have asked for a different c
        cadd = bisect(x -> 2 * (3x / (3x + 0.25)) + 5 * (x / (x + 0.25)) - 2, 1e-4, 1.0)
        @test !isapprox(c, cadd; rtol = 1e-2)
    end

    @testset "refusals" begin
        err = caught(() -> calibrate(sir_model(), POIS5, P0; target = :R0 => 10.0))  # R0 < κ_ex = 5
        @test err isa ArgumentError && occursin("not attained", err.msg)
        @test_throws ArgumentError calibrate(sir_model(), POIS5, P0; vary = :β)
        @test_throws ArgumentError calibrate(sir_model(), POIS5, P0; target = :peak => 0.2)
        # a bracket without a sign change
        @test_throws ArgumentError calibrate(sir_model(), POIS5, P0; bracket = (0.5, 1.0))
    end
end

@testset "early_growth_rate: only the states an infection reaches (WP11 review)" begin
    # an infector X that nothing produces (S + X → I + X, X → R): its exit eigenvalue −(ρ + τX)
    # is not a growth rate of any epidemic; below threshold r is the SIR decay τ(κ_ex − 1) − γ
    ph = ContactModel(:phantom; contacts = [Contact(:S, :I, :I, :τ), Contact(:S, :X, :I, :τX)],
                      transitions = [NodeTransition(:I, :R, :γ), NodeTransition(:X, :R, :ρ)])
    reg6 = ConfigurationNetwork(RegularDegree(6))
    pp = Dict(:τ => 0.04, :γ => 0.25, :τX => 0.001, :ρ => 0.001)
    @test basic_reproduction_number(ph, reg6, pp) < 1
    @test early_growth_rate(ph, reg6, pp) ≈ 0.04 * 4 - 0.25 rtol = 1e-12     # not −0.002
    @test early_growth_rate(ph, reg6, pp) ≈ early_growth_rate(sir_model(), reg6, pp) rtol = 1e-12
    # above threshold the same (the phantom state never dominated there)
    pa = merge(pp, Dict(:τ => 1 / 6))
    @test early_growth_rate(ph, reg6, pa) ≈ 5 / 12 rtol = 1e-12
    # on WellMixed and on the neighbour-exchange network as well
    @test early_growth_rate(ph, WellMixed(5), pp) ≈ 5 * 0.04 - 0.25 rtol = 1e-12
    dfd = DynamicNetwork(RegularDegree(6), NeighbourExchange(1.0))
    @test early_growth_rate(ph, dfd, pp) ≈ early_growth_rate(sir_model(), dfd, pp) rtol = 1e-12
end

# ---------------------------------------------------------------------------------------------
# steward-2 (WP36f request a): a species without a stratum on a MultitypeNetwork is shared by the
# node types (heterogeneous susceptibility), i.e. implicitly stratified X ↦ X_a
# ---------------------------------------------------------------------------------------------

@testset "shared (unlabelled) species on a MultitypeNetwork: heterogeneous susceptibility" begin
    st = strata([:lo, :hi]; sizes = [0.4, 0.6])
    lab(x, a) = SpeciesLabel(x; stratum = a)
    het = ContactModel(:sir_het; contacts = [Contact(:S_lo, :I, :I, :τ_lo), Contact(:S_hi, :I, :I, :τ_hi)],
                       transitions = [NodeTransition(:I, :R, :γ)],
                       labels = Dict(:S_lo => lab(:S, :lo), :S_hi => lab(:S, :hi)))
    p = Dict(:τ_lo => 0.05, :τ_hi => 0.3, :γ => 0.25)
    bimd = EmpiricalDegree(2 => 5 / 6, 10 => 1 / 6)
    net = unstructured(ConfigurationNetwork(bimd), st)
    n = [0.4, 0.6]
    τ = [0.05, 0.3]
    T = τ ./ (τ .+ 0.25)
    κex = 5.0
    # R₀ by hand: an infected node reached along an edge has κ_ex further edges, each to a type-a
    # node with probability n_a, transmitting with probability T_a (the next-generation matrix
    # has rank one)
    @test basic_reproduction_number(het, net, p) ≈ κex * sum(n .* T) rtol = 1e-12
    # r by hand: y_b' = n_b κ_ex Σ_a τ_a y_a − (τ_b + γ) y_b, so 1 = κ_ex Σ_b n_b τ_b/(r + τ_b + γ)
    g(r) = κex * sum(n .* τ ./ (r .+ τ .+ 0.25)) - 1
    lo, hi = 0.0, 5.0
    for _ in 1:200
        mid = (lo + hi) / 2
        g(mid) > 0 ? (lo = mid) : (hi = mid)
    end
    @test early_growth_rate(het, net, p) ≈ (lo + hi) / 2 rtol = 1e-9
    # final size by hand (Miller & Volz 2013 with susceptibility classes): with ρ seeds in I
    # placed uniformly and q = 1 − ρ, θ_a = 1 − T_a + T_a q Σ_b n_b ψ'(θ_b)/ψ'(1) and
    # R∞ = 1 − q Σ_a n_a ψ(θ_a)
    ψ(x) = 5 / 6 * x^2 + 1 / 6 * x^10
    dψ(x) = 5 / 3 * x + 10 / 6 * x^9
    for ρ in (0.01, 0.0)
        q = 1 - ρ
        θ = fill(1e-3, 2)
        for _ in 1:20_000
            θ = 1 .- T .+ T .* q .* sum(n .* dψ.(θ)) ./ dψ(1.0)
        end
        R∞ = 1 - q * sum(n .* ψ.(θ))
        init = ρ > 0 ? SeedFraction(:I => ρ) : nothing
        @test final_size(het, net, p; initial = init) ≈ R∞ rtol = 1e-8
    end
    # the explicit stratification gives the same numbers (shared seeds spread over all nodes:
    # 0.4·1% on lo, 0.6·1% on hi)
    strat = stratify(sir_model(), st; contact_rates = (a, b) -> a === :lo ? :τ_lo : :τ_hi)
    @test basic_reproduction_number(het, net, p) ≈ basic_reproduction_number(strat, net, p) rtol = 1e-12
    @test early_growth_rate(het, net, p) ≈ early_growth_rate(strat, net, p) rtol = 1e-10
    @test final_size(het, net, p; initial = SeedFraction(:I => 0.01)) ≈
          final_size(strat, net, p; initial = SeedFraction(:I_lo => 0.004, :I_hi => 0.006)) rtol = 1e-10
    # on a structured SBM too (types are fixed node attributes, so the implicit stratification is
    # exact there as well)
    sbm = sbm_network(st; mean_contacts = [4.0 2.0; 4 / 3 5.0])
    @test basic_reproduction_number(het, sbm, p) ≈ basic_reproduction_number(strat, sbm, p) rtol = 1e-12
    @test final_size(het, sbm, p; initial = SeedFraction(:I => 0.01)) ≈
          final_size(strat, sbm, p; initial = SeedFraction(:I_lo => 0.004, :I_hi => 0.006)) rtol = 1e-10

    # class-specific latent stages E_a with a shared I and R, and seeds of both kinds: the shared
    # seeds go on the nodes left free by the stratum seeds, uniformly (§J.6): with E_lo 0.1 the
    # free nodes are 0.3 (lo) and 0.6 (hi), so I = 0.009 puts 0.003 on lo and 0.006 on hi
    seir = ContactModel(:seir_het; contacts = [Contact(:S_lo, :I, :E_lo, :τ_lo), Contact(:S_hi, :I, :E_hi, :τ_hi)],
                        transitions = [NodeTransition(:E_lo, :I, :σ_lo), NodeTransition(:E_hi, :I, :σ_hi),
                                       NodeTransition(:I, :R, :γ)],
                        labels = Dict(:S_lo => lab(:S, :lo), :S_hi => lab(:S, :hi), :E_lo => lab(:E, :lo),
                                      :E_hi => lab(:E, :hi)))
    ps = Dict(:τ_lo => 0.08, :τ_hi => 0.3, :σ_lo => 0.5, :σ_hi => 0.2, :γ => 0.25)
    full = ContactModel(:seir_full;
        contacts = [Contact(Symbol(:S_, a), Symbol(:I_, b), Symbol(:E_, a), Symbol(:τ_, a); name = Symbol(:c_, a, b))
                    for a in (:lo, :hi) for b in (:lo, :hi)],
        transitions = vcat([NodeTransition(Symbol(:E_, a), Symbol(:I_, a), Symbol(:σ_, a)) for a in (:lo, :hi)],
                           [NodeTransition(Symbol(:I_, a), Symbol(:R_, a), :γ) for a in (:lo, :hi)]),
        labels = Dict(Symbol(x, :_, a) => lab(x, a) for x in (:S, :E, :I, :R) for a in (:lo, :hi)))
    pnet = unstructured(ConfigurationNetwork(PoissonDegree(5)), st)
    @test basic_reproduction_number(seir, pnet, ps) ≈
          5 * (0.4 * 0.08 / 0.33 + 0.6 * 0.3 / 0.55) rtol = 1e-12
    @test basic_reproduction_number(seir, pnet, ps) ≈ basic_reproduction_number(full, pnet, ps) rtol = 1e-12
    @test early_growth_rate(seir, pnet, ps) ≈ early_growth_rate(full, pnet, ps) rtol = 1e-10
    @test final_size(seir, pnet, ps; initial = SeedFraction(:E_lo => 0.1, :I => 0.009)) ≈
          final_size(full, pnet, ps; initial = SeedFraction(:E_lo => 0.1, :I_lo => 0.003, :I_hi => 0.006)) rtol = 1e-10
    @test_throws ArgumentError final_size(seir, pnet, ps; initial = SeedFraction(:E_lo => 0.3, :I => 0.65, :R => 0.1))
    # a reaction may not move a node between strata, nor nodes of every type into one stratum
    bad = ContactModel(:bad; contacts = contacts(het), transitions = [NodeTransition(:I, :R_lo, :γ)],
                       labels = Dict(:S_lo => lab(:S, :lo), :S_hi => lab(:S, :hi), :R_lo => lab(:R, :lo)))
    e = try
        basic_reproduction_number(bad, net, p); nothing
    catch x
        x
    end
    @test e isa ArgumentError && occursin("moves nodes of every node type from I", e.msg)
    cross = ContactModel(:cross; contacts = [Contact(:S_lo, :I, :E_hi, :τ_lo), Contact(:S_hi, :I, :E_hi, :τ_hi)],
                         transitions = [NodeTransition(:E_hi, :I, :σ_hi), NodeTransition(:I, :R, :γ)],
                         labels = Dict(:S_lo => lab(:S, :lo), :S_hi => lab(:S, :hi), :E_hi => lab(:E, :hi)))
    @test_throws ArgumentError basic_reproduction_number(cross, pnet, ps)
end
