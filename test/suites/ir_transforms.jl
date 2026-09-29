# Owner: WP6. Syntax-side transforms (DESIGN §B.9): relabel, erlang_stages, reinfection counting
# (with its exact mass-action lumping, M12), and the Poisson reverse-map targets D_μ (M2) and
# E_μ (M3), checked against the edge-based field of §D.4 written out independently here.

using NetworkEpiCore
using LinearAlgebra
using Random
const NEC = NetworkEpiCore

# ---------------------------------------------------------------------------------------------
# Test-only numerics: the mass-action field of a ContactModel or ReactionNetworkData (κ = 1) and
# a classical RK4 integrator.
# ---------------------------------------------------------------------------------------------

function ma_field(cm::ContactModel, x::AbstractDict, p = Dict{Symbol,Float64}())
    dx = Dict{Symbol,Float64}(s => 0.0 for s in species_names(cm))
    for c in contacts(cm)
        f = rate_value(c.rate, p) * x[c.recipient] * x[c.infector]
        dx[c.recipient] -= f
        dx[c.product] += f
    end
    for t in node_transitions(cm)
        f = rate_value(t.rate, p) * x[t.from]
        dx[t.from] -= f
        t.to === nothing || (dx[t.to] += f)
    end
    return dx
end

function ma_field(d::ReactionNetworkData, x::AbstractDict, p = Dict{Symbol,Float64}())
    dx = Dict{Symbol,Float64}(s => 0.0 for s in species_names(d))
    for r in d.reactions
        prop = rate_value(r.rate, p)
        for (s, n) in r.substrates
            prop *= x[s]^n
        end
        for (s, n) in r.substrates
            dx[s] -= n * prop
        end
        for (s, n) in r.products
            dx[s] += n * prop
        end
    end
    return dx
end

function rk4(f, u0::Vector{Float64}, h, nsteps)
    u = copy(u0)
    traj = [copy(u)]
    for _ in 1:nsteps
        k1 = f(u)
        k2 = f(u .+ (h / 2) .* k1)
        k3 = f(u .+ (h / 2) .* k2)
        k4 = f(u .+ h .* k3)
        u = u .+ (h / 6) .* (k1 .+ 2k2 .+ 2k3 .+ k4)
        push!(traj, copy(u))
    end
    return traj
end

ma_vector_field(cm, p = Dict{Symbol,Float64}()) =
    u -> (x = Dict(zip(species_names(cm), u)); dx = ma_field(cm, x, p);
          [dx[s] for s in species_names(cm)])

# Phase-type moments of the sojourn in the block `states` (entered in states[1]).
function sojourn_moments(cm::ContactModel, states)
    idx = Dict(s => i for (i, s) in enumerate(states))
    Q = zeros(length(states), length(states))
    for t in node_transitions(cm)
        haskey(idx, t.from) || continue
        i = idx[t.from]
        Q[i, i] -= t.rate
        (t.to !== nothing && haskey(idx, t.to)) && (Q[i, idx[t.to]] += t.rate)
    end
    N = inv(-Q)
    m1 = sum(N[1, :])
    m2 = 2 * sum((N * N)[1, :])
    return m1, m2 - m1^2
end

# ---------------------------------------------------------------------------------------------
# relabel
# ---------------------------------------------------------------------------------------------

@testset "relabel" begin
    r = relabel(sir_model(), Dict(:I => :J))
    @test species_names(r) == [:S, :J, :R]
    @test only(contacts(r)).name === :S_J_to_J                 # default names follow the species
    @test isequivalent(r, sir_model(I = :J))
    @test provenance(r).source === :transform
    # a merge of two infectors (same type) concatenates and merges reactions: rates add
    two = ContactModel(:two; contacts = [Contact(:S, :I1, :I1, :τ1), Contact(:S, :I2, :I2, :τ2)],
                       transitions = [NodeTransition(:I1, :R, :γ), NodeTransition(:I2, :R, :γ)])
    m = relabel(two, Dict(:I1 => :I, :I2 => :I))
    @test species_names(m) == [:S, :I, :R]
    @test only(contacts(m)).rate == :(τ1 + τ2)
    @test only(node_transitions(m)).rate == :(γ + γ)
    @test isequivalent(m, sir_model(τ = :(τ1 + τ2), γ = :(2γ)))
    # susceptible merged with susceptible is fine; with a node species it is not
    hs = ContactModel(:hs; contacts = [Contact(:S1, :I, :I, :τ), Contact(:S2, :I, :I, :τ)],
                      transitions = [NodeTransition(:I, :R, :γ)])
    @test susceptible_species(relabel(hs, Dict(:S1 => :S, :S2 => :S))) == [:S]
    @test only(contacts(relabel(hs, Dict(:S1 => :S, :S2 => :S)))).rate == :(τ + τ)
    @test_throws ArgumentError relabel(sir_model(), Dict(:S => :R))
    @test_throws ArgumentError relabel(sir_model(), Dict(:I => :R))    # I → R collapses
    @test_throws ArgumentError relabel(sir_model(), Dict(:Q => :R))    # unknown species
    # labels travel with a bijection
    staged = erlang_stages(sir_model(), :I, 2)
    rl = relabel(staged, Dict(:I_1 => :Ia, :I_2 => :Ib))
    @test species_labels(rl)[:Ib] == SpeciesLabel(:I, :all, 0, 2)
    # naturality in species maps (the mass-action form of Lean `lift_map`): the field of the
    # relabelled model at u is the pushforward of the field of the model at the pullback f*u
    p = Dict(:τ1 => 0.3, :τ2 => 0.7, :γ => 0.25)
    f = Dict(:I1 => :I, :I2 => :I)
    u = Dict(:S => 0.6, :I => 0.3, :R => 0.1)
    pulled = Dict(x => u[get(f, x, x)] for x in species_names(two))
    fx = ma_field(two, pulled, p)
    pushed = Dict(y => sum(fx[x] for x in species_names(two) if get(f, x, x) === y)
                  for y in species_names(m))
    fm = ma_field(m, u, p)
    @test all(isapprox(fm[y], pushed[y]; atol = 1e-15) for y in species_names(m))
end

# ---------------------------------------------------------------------------------------------
# erlang_stages (fixes the exit-rate defect E09)
# ---------------------------------------------------------------------------------------------

@testset "erlang_stages" begin
    e = erlang_stages(sir_model(), :I, 3)
    @test species_names(e) == [:S, :I_1, :I_2, :I_3, :R]
    @test [(c.recipient, c.infector, c.product, c.rate) for c in contacts(e)] ==
          [(:S, :I_1, :I_1, :τ), (:S, :I_2, :I_1, :τ), (:S, :I_3, :I_1, :τ)]
    @test [(t.from, t.to, t.rate) for t in node_transitions(e)] ==
          [(:I_1, :I_2, :(3γ)), (:I_2, :I_3, :(3γ)), (:I_3, :R, :(3γ))]
    @test entry_species(e) == [:I_1] && infectious_species(e) == [:I_1, :I_2, :I_3]
    @test species_labels(e)[:I_2] == SpeciesLabel(:I, :all, 0, 2)
    @test base_compartment_of(e, :I_3) === :I
    @test typing(e).theory === :T_EB

    # E09 regression: exit rate n·γ, mean 1/γ and variance 1/(nγ²) for every n
    for n in (1, 2, 3, 5), γ in (0.1, 0.25)
        m = instantiate(erlang_stages(sir_model(), :I, n), Dict(:τ => 0.5, :γ => γ))
        ex = only(t for t in node_transitions(m) if t.to === :R)
        @test ex.from === Symbol(:I_, n)
        @test ex.rate ≈ n * γ
        mean, var = sojourn_moments(m, [Symbol(:I_, i) for i in 1:n])
        @test mean ≈ 1 / γ
        @test var ≈ 1 / (n * γ^2)
    end
    @test only(node_transitions(erlang_stages(sir_model(), :I, 1))).rate === :γ
    # all-zero exit rates give zero rates, never NaN (the division guard of the E09 fix)
    z = erlang_stages(ContactModel(:z; contacts = [Contact(:S, :I, :I, 0.5)],
                                   transitions = [NodeTransition(:I, :R, 0.0),
                                                  NodeTransition(:I, :D, 0.0)]), :I, 3)
    @test all(t -> t.rate == 0 && !isnan(t.rate), node_transitions(z))

    # competing exits keep the total n·a_tot and the branching a_j/a_tot
    cmp = ContactModel(:cmp; contacts = [Contact(:S, :I, :I, :τ)],
                       transitions = [NodeTransition(:I, :R, 0.2), NodeTransition(:I, :D, 0.05)])
    e4 = erlang_stages(cmp, :I, 4)
    rR = only(t.rate for t in node_transitions(e4) if t.from === :I_4 && t.to === :R)
    rD = only(t.rate for t in node_transitions(e4) if t.from === :I_4 && t.to === :D)
    @test rR + rD ≈ 1.0 && rR / (rR + rD) ≈ 0.8
    @test all(t.rate ≈ 1.0 for t in node_transitions(e4) if t.to in (:I_2, :I_3, :I_4))
    @test sojourn_moments(e4, [:I_1, :I_2, :I_3, :I_4])[1] ≈ 4.0
    sym = erlang_stages(ContactModel(:x; contacts = [Contact(:S, :I, :I, :τ)],
                                     transitions = [NodeTransition(:I, :R, :γR),
                                                    NodeTransition(:I, :D, :μ)]), :I, 2)
    @test [(t.from, t.to, t.rate) for t in node_transitions(sym)] ==
          [(:I_1, :I_2, :(2 * (γR + μ))), (:I_2, :R, :(2γR)), (:I_2, :D, :(2μ))]

    # SEIR: staging both E and I; the bypass of E14 keeps its branching probability
    se = erlang_stages(erlang_stages(seir_model(), :E, 2), :I, 3)
    @test species_names(se) == [:S, :E_1, :E_2, :I_1, :I_2, :I_3, :R]
    @test entry_species(se) == [:E_1] && length(contacts(se)) == 3
    by = ContactModel(:bypass; contacts = [Contact(:S, :I, :E, :τ)],
                      transitions = [NodeTransition(:E, :I, :(p * σ)),
                                     NodeTransition(:E, :R, :((1 - p) * σ)),
                                     NodeTransition(:I, :R, :γ)])
    b2 = instantiate(erlang_stages(by, :E, 2), Dict(:τ => 1.0, :p => 0.3, :σ => 0.5, :γ => 1.0))
    @test sojourn_moments(b2, [:E_1, :E_2])[1] ≈ 2.0
    eI = only(t.rate for t in node_transitions(b2) if t.from === :E_2 && t.to === :I)
    eR = only(t.rate for t in node_transitions(b2) if t.from === :E_2 && t.to === :R)
    @test eI / (eI + eR) ≈ 0.3

    # a contact whose recipient is staged is copied to every stage
    sc = ContactModel(:scat; contacts = [Contact(:S, :I, :I, :τ), Contact(:I, :S, :R, :δ)],
                      transitions = [NodeTransition(:I, :R, :γ)])
    es = erlang_stages(sc, :I, 2)
    @test Set((c.recipient, c.infector, c.product) for c in contacts(es)) ==
          Set([(:S, :I_1, :I_1), (:S, :I_2, :I_1), (:I_1, :S, :R), (:I_2, :S, :R)])

    # errors: susceptible, absorbing, n < 1, already staged, name collisions (E26)
    @test_throws ArgumentError erlang_stages(sir_model(), :S, 3)
    @test_throws ArgumentError erlang_stages(sir_model(), :R, 3)
    @test_throws ArgumentError erlang_stages(sir_model(), :I, 0)
    @test_throws ArgumentError erlang_stages(e, :I_2, 2)
    @test_throws ArgumentError erlang_stages(sir_model(), :Q, 2)
    clash = ContactModel(:clash; contacts = [Contact(:S, :I, :I, :τ)],
                         transitions = [NodeTransition(:I, :I_1, :γ), NodeTransition(:I_1, :R, :γ)])
    err = try
        erlang_stages(clash, :I, 2)
    catch e
        e
    end
    @test err isa ArgumentError && occursin("I_1", err.msg) && occursin("collide", err.msg)
end

# ---------------------------------------------------------------------------------------------
# Reinfection counting (M12) and the label queries
# ---------------------------------------------------------------------------------------------

tracing_sis() = ContactModel(:trace; contacts = [Contact(:S, :I, :I, :τ), Contact(:S, :D, :Q, :α)],
                             transitions = [NodeTransition(:I, :D, :γ), NodeTransition(:D, :S, :δ),
                                            NodeTransition(:Q, :S, :ω)])

@testset "with_reinfection_counting: structure" begin
    L2 = with_reinfection_counting(sis_model(), 2)
    @test nameof(L2) === :sis_reinf_L2
    @test species_names(L2) == [:S_0, :S_1, :S_2, :I_1, :I_2]     # as NodeBasedModels 0.1
    @test susceptible_species(L2) == [:S_0, :S_1, :S_2]
    shapes = Set((c.recipient, c.infector, c.product) for c in contacts(L2))
    @test shapes == Set([(Symbol(:S_, p), Symbol(:I_, q), Symbol(:I_, min(p + 1, 2)))
                         for p in 0:2 for q in 1:2])
    @test Set((t.from, t.to) for t in node_transitions(L2)) == Set([(:I_1, :S_1), (:I_2, :S_2)])
    @test all(c.rate === :τ for c in contacts(L2)) && all(t.rate === :γ for t in node_transitions(L2))
    @test infection_count_of(L2, :S_2) == 2 && infection_count_of(L2, :S_0) == 0
    @test base_compartment_of(L2, :I_1) === :I
    @test typing(L2).theory === :T_net
    # E19: the lifted SIS/SIRS are refused by the edge-based back end through the typing
    for m in (with_reinfection_counting(sis_model(), 1), L2,
              with_reinfection_counting(sirs_model(), 2))
        @test !is_admissible(m, :edge_based)
        @test is_admissible(m, :pairwise) && is_admissible(m, :stochastic)
        @test_throws AdmissibilityError require_admissible(m, :edge_based)
    end
    # SIR: nothing to reinfect, so no reinfection states; still admissible everywhere
    sL = with_reinfection_counting(sir_model(), 3)
    @test species_names(sL) == [:S_0, :I_1, :R_1]
    @test is_admissible(sL, :edge_based)
    # SIRS and SEIRS
    @test species_names(with_reinfection_counting(sirs_model(), 2)) ==
          [:S_0, :S_1, :S_2, :I_1, :I_2, :R_1, :R_2]
    seirs = ContactModel(:seirs; contacts = [Contact(:S, :I, :E, :τ)],
                         transitions = [NodeTransition(:E, :I, :σ), NodeTransition(:I, :R, :γ),
                                        NodeTransition(:R, :S, :ε)])
    @test species_names(with_reinfection_counting(seirs, 2)) ==
          [:S_0, :S_1, :S_2, :E_1, :E_2, :I_1, :I_2, :R_1, :R_2]
    # L = 0 is isomorphic to the base model
    L0 = with_reinfection_counting(sis_model(), 0)
    @test species_names(L0) == [:S_0, :I_0]
    @test infection_count_of(L0, :I_0) == 0
    @test isequivalent(relabel(L0, Dict(:S_0 => :S, :I_0 => :I)), sis_model())
    # a tracing contact is not an infection: it keeps the count
    tr = with_reinfection_counting(tracing_sis(), 2)
    trace_shapes = Set((c.recipient, c.infector, c.product) for c in contacts(tr)
                       if c.product in (:Q_0, :Q_1, :Q_2))
    @test (:S_0, :D_1, :Q_0) in trace_shapes && (:S_2, :D_2, :Q_2) in trace_shapes
    @test all(infection_count_of(tr, c.product) == infection_count_of(tr, c.recipient)
              for c in contacts(tr) if base_compartment_of(tr, c.product) === :Q)
    # errors
    @test_throws ArgumentError with_reinfection_counting(sis_model(), -1)
    @test_throws ArgumentError with_reinfection_counting(L2, 2)
    @test_throws ArgumentError infection_count_of(L2, :S)
    # models that are not counted
    @test infection_count_of(sir_model(), :I) === nothing
    @test base_compartment_of(sir_model(), :I) === :I
    # the legacy name parsers of EBM/NBM 0.1
    @test base_compartment_of(:S_3) === :S && base_compartment_of(:S) === :S
    @test infection_count_of(:S_3) == 3 && infection_count_of(:S) === nothing
end

@testset "with_reinfection_counting: exact mass-action lumping (M12)" begin
    rng = Random.Xoshiro(20260926)
    cases = [(sis_model(), Dict(:τ => 0.5, :γ => 0.25), 3),
             (sirs_model(), Dict(:τ => 0.5, :γ => 0.25, :ε => 0.1), 2),
             (ContactModel(:seirs; contacts = [Contact(:S, :I, :E, :τ)],
                           transitions = [NodeTransition(:E, :I, :σ), NodeTransition(:I, :R, :γ),
                                          NodeTransition(:R, :S, :ε)]),
              Dict(:τ => 0.8, :σ => 0.3, :γ => 0.25, :ε => 0.05), 4),
             (tracing_sis(), Dict(:τ => 0.6, :α => 0.2, :γ => 0.3, :δ => 0.1, :ω => 0.5), 2),
             (seair_model(), Dict(:τI => 0.5, :τA => 0.25, :p => 0.6, :σ => 0.2, :γ => 0.25), 2)]
    for (base, p, L) in cases
        lift = with_reinfection_counting(base, L)
        # the lumped field is closed: L f_lift(x) == f_base(L x) at random states
        for _ in 1:5
            x = Dict(s => rand(rng) for s in species_names(lift))
            lumped = reinfection_totals(lift, x)
            fl = reinfection_totals(lift, ma_field(lift, x, p))
            fb = ma_field(base, lumped, p)
            @test Set(keys(fl)) == Set(species_names(base))
            @test all(isapprox(fl[s], fb[s]; atol = 1e-13) for s in species_names(base))
        end
        # and the trajectories agree (RK4 in both coordinates)
        seed = first(infectious_species(base))
        u0b = [s === seed ? 0.01 : s in susceptible_species(base) ? 0.99 : 0.0
               for s in species_names(base)]
        u0l = [base_compartment_of(lift, s) === seed && infection_count_of(lift, s) == 1 ? 0.01 :
               s === Symbol(first(susceptible_species(base)), :_0) ? 0.99 : 0.0
               for s in species_names(lift)]
        tb = rk4(ma_vector_field(base, p), u0b, 0.05, 400)
        tl = rk4(ma_vector_field(lift, p), u0l, 0.05, 400)
        err = maximum(maximum(abs(reinfection_totals(lift, ul)[s] - ub[i])
                              for (i, s) in enumerate(species_names(base)))
                      for (ub, ul) in zip(tb, tl))
        @test err < 1e-12
    end
    # reinfection_totals on time series and on a model that is not counted (identity)
    L2 = with_reinfection_counting(sis_model(), 2)
    ts = Dict(:S_0 => [0.5, 0.4], :S_1 => [0.1, 0.1], :S_2 => [0.0, 0.1], :I_1 => [0.3, 0.2],
              :I_2 => [0.1, 0.2])
    tot = reinfection_totals(L2, ts)
    @test tot[:S] ≈ [0.6, 0.6] && tot[:I] ≈ [0.4, 0.4]
    @test reinfection_totals(sir_model(), Dict(:S => 1.0, :I => 2.0, :R => 3.0)) ==
          Dict(:S => 1.0, :I => 2.0, :R => 3.0)
    @test_throws ArgumentError reinfection_totals(L2, [1.0, 2.0])
    # stage first, then count: staging a counted model is refused (WP6 review: the stages of I_1
    # lumped to I_1 and I inconsistently), while count-after-stage lumps every stage by count
    err = try erlang_stages(L2, :I_1, 2); nothing catch e; e end
    @test err isa ArgumentError && occursin("stage first, then count", err.msg)
    sc = with_reinfection_counting(erlang_stages(sis_model(), :I, 2), 2)
    tot = reinfection_totals(sc, Dict(X => 1.0 for X in species_names(sc)))
    @test Set(keys(tot)) == Set([:S, :I_1, :I_2])
    @test tot[:I_1] == tot[:I_2] == 2.0 && tot[:S] == 3.0
end

# ---------------------------------------------------------------------------------------------
# D_μ (M2) and E_μ (M3), against the edge-based field of §D.4 on Poisson(μ)
# ---------------------------------------------------------------------------------------------

# EB field of a T_EB model with one susceptible class on Poisson(μ):
# S = qξψ(θ), φ_S = qξψ'(θ)/ψ'(1), with ψ(x) = e^{μ(x−1)}.
function eb_field(cm, τ::Vector{Float64}, p, μ, q, θ, ξ, φ::Dict, pop::Dict)
    s = only(susceptible_species(cm))
    E = exp(μ * (θ - 1))
    S, φS = q * ξ * E, q * ξ * E
    dθ, dξ = 0.0, 0.0
    dφ = Dict(x => 0.0 for x in keys(φ))
    dpop = Dict(x => 0.0 for x in keys(pop))
    for (c, τr) in zip(contacts(cm), τ)
        h = τr * φ[c.infector]
        dθ -= h
        dφ[c.infector] -= h
        dφ[c.product] += h * q * ξ * μ^2 * E / μ           # ψ''(θ)/ψ'(1)
        dpop[c.product] += h * q * ξ * μ * E               # ψ'(θ)
    end
    for t in node_transitions(cm)
        a = rate_value(t.rate, p)
        if t.from === s
            dξ -= a * ξ
            t.to === nothing || (dφ[t.to] += a * φS; dpop[t.to] += a * S)
        else
            dφ[t.from] -= a * φ[t.from]
            dpop[t.from] -= a * pop[t.from]
            t.to === nothing || (dφ[t.to] += a * φ[t.from]; dpop[t.to] += a * pop[t.from])
        end
    end
    return S, dθ, dξ, dφ, dpop
end

vax_seair() = ContactModel(:vseair; contacts = [Contact(:S, :I, :E, :τI), Contact(:S, :A, :E, :τA),
                                                Contact(:S, :I, :F, :τF)],
                           transitions = [NodeTransition(:E, :I, :(p * σ)),
                                          NodeTransition(:E, :A, :((1 - p) * σ)),
                                          NodeTransition(:F, :I, :σ), NodeTransition(:I, :R, :γ),
                                          NodeTransition(:A, nothing, :γ),
                                          NodeTransition(:S, :V, :ν)])

@testset "edge_doubling (D_μ, M2) and rempala_reduction (E_μ, M3)" begin
    # shapes for SIR
    d = edge_doubling(sir_model(), :μ)
    @test species_names(d) == [:S, :Φ_I, :Φ_R, :I, :R]
    rs = [(r.substrates, r.products, r.rate) for r in d.reactions]
    @test ([:S => 1, :Φ_I => 1], [:Φ_I => 2, :I => 1], :(μ * τ)) in rs
    @test ([:Φ_I => 1], Pair{Symbol,Int}[], :τ) in rs
    @test ([:Φ_I => 1], [:Φ_R => 1], :γ) in rs && ([:I => 1], [:R => 1], :γ) in rs
    @test length(rs) == 4
    # Rempała for SIR: MA(β = μτ, γ_MA = γ + τ) on (S, φ_I)
    rr = rempala_reduction(sir_model(), :μ)
    @test isequivalent(rr, ContactModel(:x; contacts = [Contact(:S, :I, :I, :(μ * τ))],
                                        transitions = [NodeTransition(:I, :R, :γ),
                                                       NodeTransition(:I, nothing, :τ)]))
    @test rate_convention(rr) == PerContact()
    num = instantiate(rempala_reduction(sir_model(), 5.0), Dict(:τ => 1 / 6, :γ => 1 / 4))
    x = Dict(:S => 0.7, :I => 0.2, :R => 0.1)
    @test ma_field(num, x)[:I] ≈ 5 / 6 * 0.7 * 0.2 - (1 / 4 + 1 / 6) * 0.2

    # the semiconjugacy identities at random points, for a model with branching at infection,
    # two infectors, infector-dependent entry, a removal and an exit (vaccination)
    rng = Random.Xoshiro(7)
    for (conv, μ) in ((PerContact(), 5.0), (PerContact(), 2.5), (FrequencyDependent(), 4.0))
        base = vax_seair()
        cm = ContactModel(:vseair; contacts = contacts(base), transitions = node_transitions(base),
                          convention = conv)
        p = Dict(:τI => 0.3, :τA => 0.15, :τF => 0.05, :p => 0.6, :σ => 0.2, :γ => 0.25,
                 :ν => 0.02)
        τ = [rate_value(r, p) for r in per_contact_rates(cm, ConfigurationNetwork(PoissonDegree(μ)))]
        conv isa FrequencyDependent && @test τ ≈ [0.3, 0.15, 0.05] ./ μ
        D = edge_doubling(cm, μ)
        Eμ = rempala_reduction(cm, μ)
        nodes = [x for x in species_names(cm) if x !== :S]
        q = 0.99
        for _ in 1:6
            θ, ξ = 0.3 + 0.7rand(rng), 0.5 + 0.5rand(rng)
            φ = Dict(x => 0.5rand(rng) for x in nodes)
            pop = Dict(x => 0.5rand(rng) for x in nodes)
            S, dθ, dξ, dφ, dpop = eb_field(cm, τ, p, μ, q, θ, ξ, φ, pop)
            dS = S * (μ * dθ + dξ / ξ)                       # Dπ·F for S = qξe^{μ(θ−1)}
            # M2: MA(D_μ P) at π(u) = (S, Φ = φ, X = pop)
            xD = Dict{Symbol,Float64}(:S => S)
            for x in nodes
                xD[Symbol("Φ_", x)] = φ[x]
                xD[x] = pop[x]
            end
            G = ma_field(D, xD, p)
            @test G[:S] ≈ dS rtol = 1e-12
            @test all(isapprox(G[Symbol("Φ_", x)], dφ[x]; rtol = 1e-12, atol = 1e-15) for x in nodes)
            @test all(isapprox(G[x], dpop[x]; rtol = 1e-12, atol = 1e-15) for x in nodes)
            # M3: MA(E_μ P) at (S, φ)
            xE = Dict{Symbol,Float64}(:S => S)
            for x in nodes
                xE[x] = φ[x]
            end
            H = ma_field(Eμ, xE, p)
            @test H[:S] ≈ dS rtol = 1e-12
            @test all(isapprox(H[x], dφ[x]; rtol = 1e-12, atol = 1e-15) for x in nodes)
        end
    end

    # requirements: T_EB, one susceptible class, no layers, no name clashes
    @test_throws AdmissibilityError edge_doubling(sis_model(), 5.0)
    @test_throws AdmissibilityError rempala_reduction(sirs_model(), 5.0)
    hs = ContactModel(:hs; contacts = [Contact(:S1, :I, :I, :τ), Contact(:S2, :I, :I, :τ)],
                      transitions = [NodeTransition(:I, :R, :γ)],
                      labels = Dict(:S1 => SpeciesLabel(:S; stratum = :a),
                                    :S2 => SpeciesLabel(:S; stratum = :b)))
    @test_throws ArgumentError edge_doubling(hs, 5.0)
    lay = ContactModel(:lay; contacts = [Contact(:S, :I, :I, :τ; layer = :home)],
                       transitions = [NodeTransition(:I, :R, :γ)])
    @test_throws ArgumentError rempala_reduction(lay, 5.0)
    clash = ContactModel(:clash; contacts = [Contact(:S, :I, :I, :τ)],
                         transitions = [NodeTransition(:I, :Φ_I, :γ)])
    @test_throws ArgumentError edge_doubling(clash, 5.0)
    # an existing removal of an infector is merged with the edge removal (rates add)
    sird = ContactModel(:sird; contacts = [Contact(:S, :I, :I, :τ)],
                        transitions = [NodeTransition(:I, nothing, :μd)])
    @test only(node_transitions(rempala_reduction(sird, 5.0))).rate == :(μd + τ)
end
