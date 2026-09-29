# Owner: WP10. Morphism objects and the Symbolics extension (DESIGN §D.3, §D.5, §D.7, §B.6):
# symbolic rates (rate_value by name with fold, as_parameter, rate arithmetic on Num), the
# mass-action ODE of a model and of a general reaction network, SymbolicODE / Semiconjugacy /
# Evidence / VerificationResult, `verify` (Rempała's quotient M3 verifies, the old
# `to_mass_action` map with γ in place of γ + τ fails and reports its residual, issue E08; the
# Poisson isomorphism M2 verifies against `edge_doubling`), `pushforward`, `vector_fields_equal`
# with renaming, the NaturalTransformation registry and `check_naturality`; zero tests are exact
# (a difference or residual that is 0 at every probe point is never read as 0, §J.3), time has its
# own probe box, and rate_value needs a value for every parameter.
#
# The edge-based fields on Poisson(μ) below are written out by hand from the per-reaction field
# of §D.4 (ψ(x) = e^{μ(x−1)}, ψ'(1) = μ), independently of any package code.

using NetworkEpiCore
using Symbolics
using Random
const NEC = NetworkEpiCore

# ---------------------------------------------------------------------------------------------
# Test-only helpers
# ---------------------------------------------------------------------------------------------

function rk4(f, u0::Vector{Float64}, h, nsteps)
    u = copy(u0)
    traj = [copy(u)]
    for _ in 1:nsteps
        k1 = f(u)
        k2 = f(u .+ (h / 2) .* k1)
        k3 = f(u .+ (h / 2) .* k2)
        k4 = f(u .+ h .* k3)
        u = u .+ (h / 6) .* (k1 .+ 2 .* k2 .+ 2 .* k3 .+ k4)
        push!(traj, copy(u))
    end
    return traj
end

symzero(x) = iszero(Symbolics.simplify(Symbolics.expand(x); expand = true))

err(f) = try
    f()
    "no error"
catch e
    sprint(showerror, e)
end

# The edge-based field of a T_EB model on Poisson(μ), per reaction (§D.4), for models with at most
# one susceptible class S and no exits: coordinates θ (if the model has contacts) and φ_X, pop_X
# for every other species. Rates are Symbols; μ and q are symbolic parameters.
function eb_poisson(cm::ContactModel; μ, q)
    Σ = susceptible_species(cm)
    others = [x for x in species_names(cm) if !(x in Σ)]
    p(n) = as_parameter(n)
    @variables θ
    φ = Dict(x => Symbolics.variable(Symbol(:φ_, x)) for x in others)
    pop = Dict(x => Symbolics.variable(Symbol(:pop_, x)) for x in others)
    ψ(x) = exp(μ * (x - 1))
    dψ(x) = μ * exp(μ * (x - 1))
    d2ψ(x) = μ^2 * exp(μ * (x - 1))
    dψ1 = μ
    F = Dict{Any,Any}()
    add!(k, v) = (F[k] = get(F, k, 0) + v)
    for c in contacts(cm)
        τ = p(c.rate)
        add!(θ, -τ * φ[c.infector])
        add!(φ[c.infector], -τ * φ[c.infector])
        add!(φ[c.product], τ * φ[c.infector] * q * d2ψ(θ) / dψ1)
        add!(pop[c.product], τ * φ[c.infector] * q * dψ(θ))
    end
    for t in node_transitions(cm)
        a = as_parameter(t.rate)
        add!(φ[t.from], -a * φ[t.from])
        add!(pop[t.from], -a * pop[t.from])
        if t.to !== nothing
            add!(φ[t.to], a * φ[t.from])
            add!(pop[t.to], a * pop[t.from])
        end
    end
    states = Any[]
    isempty(contacts(cm)) || push!(states, θ)
    append!(states, [φ[x] for x in others])
    append!(states, [pop[x] for x in others])
    rhs = Any[get(F, x, Symbolics.Num(0)) for x in states]
    return SymbolicODE(Symbol(:eb_pois_, cm.name); states, rhs,
                       domain = [θ => (0.05, 1.0)]), θ, φ, pop
end

# ---------------------------------------------------------------------------------------------

@testset "symbolic rates: rate_value by name with fold" begin
    @variables κ a
    r = exp(κ * (a - 1))
    v = rate_value(r, Dict(:a => 1, :κ => 5))
    @test v isa Float64 && v == 1.0                 # exp(0) folded to 1.0 (fold = Val(true))
    # every parameter needs a value, as for Symbol and Expr rates (WP9 review): a missing one is an
    # error that names it, never a partly evaluated expression; binding a parameter to a symbolic
    # value (the variable itself) keeps it free
    @test endswith(err(() -> rate_value(r, Dict(:κ => 5.0))), ": no value for the parameter a")
    @test startswith(err(() -> rate_value(r, Dict(:κ => 5.0))), "ArgumentError: rate `")
    half = rate_value(r, Dict(:κ => 5.0, :a => a))
    @test half isa Symbolics.Num
    @test rate_value(half, Dict(:a => 1.2)) ≈ exp(1.0)
    # by name: a variable made elsewhere (different metadata) is substituted by its name
    τ = as_parameter(:τ)
    τ2 = Symbolics.variable(:τ)
    @test rate_value(2τ2, Dict(:τ => 0.3)) ≈ 0.6
    @test rate_value(τ * τ2, Dict(:τ => 0.5)) ≈ 0.25
    # symbolic keys are accepted too
    @test rate_value(3τ, Dict(τ => 0.1)) ≈ 0.3
    # parameters (names, no time) and time dependence
    @variables t
    rt = τ * exp(-t)
    @test Set(NEC._parameter_name.(rate_parameters(rt))) == Set([:τ])
    @test NEC._uses_time(rt) && !NEC._uses_time(τ * κ)
    @test rate_value(rt, Dict(:τ => 2.0); t = 0.0) == 2.0
    @test Set(NEC._parameter_name.(rate_parameters(τ * exp(κ)))) == Set([:τ, :κ])
    # the WP9 reviewer's cases: β sin(ωt) without ω, an array element bound through its array, a
    # time-dependent rate without t, and two missing parameters
    @variables β ω k[1:2]
    @test endswith(err(() -> rate_value(β * sin(ω * t), Dict(:β => 1.0); t = 0.5)),
                   ": no value for the parameter ω")
    @test rate_value(β * sin(ω * t), Dict(:β => 1.0, :ω => 2.0); t = 0.5) ≈ sin(1.0)
    @test endswith(err(() -> rate_value(k[1], Dict(:k => [0.3, 0.1]))),
                   ": no value for the parameter k[1] (an array element is a parameter of its " *
                   "own, named by its full name: pass Symbol(\"k[1]\") => value)")
    @test rate_value(k[1], Dict(Symbol("k[1]") => 0.3)) == 0.3
    @test endswith(err(() -> rate_value(β * sin(t), Dict(:β => 1.0))),
                   " depends on time t; pass `t = …` (time-dependent rates are for the ODE back " *
                   "ends only)")
    msg2 = err(() -> rate_value(β * ω * κ, Dict(:β => 1.0)))
    @test occursin(": no value for the parameters ", msg2) && occursin("ω", msg2) &&
          occursin("κ", msg2)
    # a called parameter βt(t) is time-dependent (_uses_time), so it needs t like any other
    # time-dependent rate, even when βt is given by name (WP10fix review: it was substituted
    # without t); with t, the value by name is used
    @variables βt(t)
    @test NEC._uses_time(βt)
    @test endswith(err(() -> rate_value(βt, Dict(:βt => 0.3))),
                   "rate `βt(t)` depends on time t; pass `t = …` (time-dependent rates are for " *
                   "the ODE back ends only)")
    @test rate_value(βt, Dict(:βt => 0.3); t = 1.0) == 0.3
    @test rate_value(2βt * exp(-t), Dict(:βt => 0.3); t = 0.0) ≈ 0.6
    # the same rule as for Expr rates
    @test_throws ArgumentError rate_value(:(β * ω), Dict(:β => 1.0))
    # an unwrapped SymbolicUtils term is a valid rate, and so is a Num
    c = Contact(:S, :I, :I, Symbolics.unwrap(τ))
    @test NEC._is_symbolic_rate(c.rate)
    cm = ContactModel(:sir_sym; contacts = [Contact(:S, :I, :I, τ)],
                      transitions = [NodeTransition(:I, :R, as_parameter(:γ))])
    @test Set(NEC._parameter_name.(rate_parameters(cm))) == Set([:τ, :γ])
    @test isequivalent(cm, sir_model())
    inst = instantiate(cm, Dict(:τ => 0.2, :γ => 0.1))
    @test only(contacts(inst)).rate === 0.2 && only(node_transitions(inst)).rate === 0.1
    @test_throws ArgumentError instantiate(cm, Dict(:τ => 0.2))
    timed = ContactModel(:timed; contacts = [Contact(:S, :I, :I, rt)])
    @test_throws ArgumentError instantiate(timed, Dict(:τ => 0.2))
end

@testset "as_parameter and rate arithmetic on Num" begin
    τ = as_parameter(:τ)
    @test τ isa Symbolics.Num
    @test isequal(τ, Symbolics.variable(:τ))
    @test Symbolics.getname(τ) === :τ
    @test Symbolics.getmetadata(Symbolics.unwrap(τ), Symbolics.VariableSource, nothing) ==
          (:parameters, :τ)
    @test isequal(as_parameter(:τ), as_parameter(:τ))
    @test as_parameter(0.5) === 0.5
    @test as_parameter(τ) === τ
    @test isequal(as_parameter(Symbolics.unwrap(τ)), τ)
    pσ = as_parameter(:(p * σ))
    @test symzero(pσ - as_parameter(:p) * as_parameter(:σ))
    @test_throws ArgumentError as_parameter(:t)
    @test_throws ArgumentError as_parameter(:(τ * exp(-t)))
    tt = Symbolics.variable(:t)
    @test symzero(as_parameter(:(τ * exp(-t)); t = tt) - τ * exp(-tt))
    @test_throws ArgumentError as_parameter(:(foo(τ)))
    # rate_mul / rate_add / rate_div combine a Num with Symbol and Expr rates (ir/rates.jl)
    γ = as_parameter(:γ)
    @test symzero(rate_mul(τ, :γ) - τ * γ)
    @test symzero(rate_mul(:γ, τ) - τ * γ)
    @test symzero(rate_mul(2, τ) - 2τ)
    @test symzero(rate_add(τ, :(p * σ)) - (τ + pσ))
    @test symzero(rate_div(τ, 5) - τ / 5)
    @test symzero(rate_div(:β, τ) - as_parameter(:β) / τ)
    @test rate_mul(1, τ) === τ
end

@testset "mass_action and symbolic_ode of a ContactModel" begin
    @variables t S(t) I(t) R(t) E(t) V(t)
    τ, γ, σ, ν = as_parameter.((:τ, :γ, :σ, :ν))
    ma = mass_action(sir_model())
    @test ma isa SymbolicODE
    @test state_names(ma) == [:S, :I, :R]
    @test Set(NEC._parameter_name.(ma.parameters)) == Set([:τ, :γ])
    hand = SymbolicODE(:hand; states = [S, I, R],
                       rhs = [-τ * S * I, τ * S * I - γ * I, γ * I])
    @test all(symzero(a - b) for (a, b) in zip(ma.rhs, hand.rhs))
    @test vector_fields_equal(ma, hand; rename = :none)
    @test vector_fields_equal(symbolic_ode(sir_model()), ma)
    # c_κ: every contact at κ τ
    ma5 = mass_action(sir_model(); κ = 5)
    @test symzero(ma5.rhs[1] + 5τ * S * I)
    @test !vector_fields_equal(ma5, ma)
    @test vector_fields_equal(symbolic_ode(sir_model(); κ = 5), ma5)
    κ = as_parameter(:κ)
    maκ = mass_action(sir_model(); κ = :κ)
    @test symzero(maκ.rhs[2] - (κ * τ * S * I - γ * I))
    @test :κ in NEC._parameter_name.(maκ.parameters)
    # FrequencyDependent: MA(c_κ P) has the written β for every κ (the unit law M1)
    β = as_parameter(:β)
    freq = ContactModel(:seirf; contacts = [Contact(:S, :I, :E, :β)],
                        transitions = [NodeTransition(:E, :I, :σ), NodeTransition(:I, :R, :γ)],
                        convention = FrequencyDependent())
    @test vector_fields_equal(mass_action(freq; κ = 5), mass_action(freq; κ = 2))
    @test symzero(mass_action(freq; κ = 5).rhs[1] + β * S * I)
    # DensityDependent(N): the fraction ODE has β N
    N = as_parameter(:N)
    dens = ContactModel(:sird; contacts = [Contact(:S, :I, :I, :β)],
                        transitions = [NodeTransition(:I, :R, :γ)],
                        convention = DensityDependent(:N))
    @test symzero(mass_action(dens; κ = 7).rhs[1] + β * N * S * I)
    # exits and removals
    mv = mass_action(sirv_model())
    @test state_names(mv) == [:S, :I, :R, :V]
    @test symzero(mv.rhs[1] - (-τ * S * I - ν * S)) && symzero(mv.rhs[4] - ν * S)
    rem = ContactModel(:sirm; contacts = [Contact(:S, :I, :I, :τ)],
                       transitions = [NodeTransition(:I, nothing, :γ)])
    @test symzero(mass_action(rem).rhs[2] - (τ * S * I - γ * I))
    # Expr rates (SEAIR branching) and numbers
    msea = mass_action(seair_model())
    p = as_parameter(:p)
    A = only(Symbolics.@variables A(t))
    @test symzero(msea.rhs[findfirst(==(:A), state_names(msea))] -
                  ((1 - p) * σ * E - γ * A))
    num = mass_action(sir_model(; τ = 0.25, γ = 0.1); κ = 4)
    @test isempty(num.parameters)
    @test symzero(num.rhs[1] + 1.0 * S * I)
end

@testset "SymbolicODE, Semiconjugacy and Evidence validation" begin
    @variables x y a
    @test_throws ArgumentError SymbolicODE(:bad, [x, y], [x], Any[], [])
    @test_throws ArgumentError SymbolicODE(:bad, [x, x], [x, y], Any[], [])
    @test_throws ArgumentError SymbolicODE(:bad, [x, y], [a * x, y], Any[x], [])
    @test_throws ArgumentError SymbolicODE(:bad; states = [x], rhs = [a * x],
                                           domain = [x => (1.0, 0.5)])
    ode = SymbolicODE(:lin; states = [x, y], rhs = [-a * x, a * x])
    @test NEC._parameter_name.(ode.parameters) == [:a]           # inferred
    @test state_names(ode) == [:x, :y]
    @test symbolic_ode(ode) === ode
    @test occursin("dx/dt", sprint(show, MIME"text/plain"(), ode))
    ode2 = SymbolicODE(:sym; states = [:x, :y], rhs = [-a * x, a * x], parameters = [:a])
    @test state_names(ode2) == [:x, :y]
    @variables u
    tgt = SymbolicODE(:one; states = [u], rhs = [Symbolics.Num(0)])
    m = Semiconjugacy(:sum, ode, tgt, [u => x + y]; kind = :lumping,
                      evidence = [Evidence(:symbolic, "test/suites/morphisms.jl")])
    @test m.kind === :lumping && m.exactness === :exact
    @test verify(m).ok                                      # x + y is conserved
    @test_throws ArgumentError Semiconjugacy(:bad, ode, tgt, [x => x])          # not a target state
    @test_throws ArgumentError Semiconjugacy(:bad, ode, tgt, Pair{Any,Any}[])   # u missing
    @test_throws ArgumentError Semiconjugacy(:bad, ode, tgt, [u => x, :u => y]) # twice
    @test_throws ArgumentError Semiconjugacy(:bad, ode, tgt, [u => x + y]; kind = :iso)
    @test_throws ArgumentError Semiconjugacy(:bad, ode, tgt, [u => x + y]; exactness = :approx)
    @test_throws ArgumentError Semiconjugacy(:bad, ode, tgt, [u => x + y]; parameter_map = [u => a])
    # map entries are stored in target-state order, keys may be names
    tgt2 = SymbolicODE(:two; states = [:p, :q], rhs = [Symbolics.Num(0), Symbolics.Num(0)],
                       parameters = [])
    m2 = Semiconjugacy(:perm, ode, tgt2, Dict(:q => x, :p => y))
    @test NEC._coordinate_name.(first.(m2.map)) == [:p, :q]
    @test_throws ArgumentError Evidence(:proof, "x")
    @test Evidence(:lean, "NEP.rempala") == Evidence(:lean, "NEP.rempala")
    @test occursin("NEP.rempala", sprint(show, Evidence(:lean, "NEP.rempala")))
    @test occursin("Semiconjugacy", sprint(show, MIME"text/plain"(), m))
    r = VerificationResult(true, :symbolic, 0.0, 0, "fine")
    @test sprint(show, r) == "VerificationResult(ok = true, method = :symbolic, residual = 0.0)"
    @test MORPHISM_KINDS == (:conjugacy, :semiconjugacy, :restriction, :lumping)
    @test EXACTNESS_LEVELS == (:exact, :limit, :calibration)
    @test_throws ArgumentError verify(m; method = :magic)
end

@testset "verify: Rempała's quotient (M3) on SIR; the old map (γ for γ + τ) fails (E08)" begin
    μ, q, τ, γ = as_parameter.((:μ, :q, :τ, :γ))
    @variables θ φ_I φ_R pop_I pop_R
    # EB SIR on Poisson(μ), D.4 field with ψ''(θ)/ψ'(1) = μ² e^{μ(θ−1)}/μ, written out by hand
    ψ = exp(μ * (θ - 1))
    F = [-τ * φ_I,
         -τ * φ_I + τ * φ_I * q * μ^2 * ψ / μ - γ * φ_I,
         γ * φ_I,
         τ * φ_I * q * μ * ψ - γ * pop_I,
         γ * pop_I]
    src = SymbolicODE(:eb_pois_sir; states = [θ, φ_I, φ_R, pop_I, pop_R], rhs = F,
                      domain = [θ => (0.05, 1.0)])
    @variables S I
    β, γMA = as_parameter.((:β, :γMA))
    tgt = SymbolicODE(:ma_sir; states = [S, I], rhs = [-β * S * I, β * S * I - γMA * I])
    rempala = Semiconjugacy(:rempala, src, tgt, [S => q * ψ, I => φ_I];
                            parameter_map = [β => μ * τ, γMA => γ + τ],
                            evidence = [Evidence(:lean, "NEP.rempala"),
                                        Evidence(:paper, "Rempała 2023, Thm 1")])
    # a parameter-map key must be a parameter of the target (a misspelt γ_MA for γMA is an error,
    # not an unbound parameter found later by verify)
    msg = try
        Semiconjugacy(:typo, src, tgt, [S => q * ψ, I => φ_I];
                      parameter_map = [β => μ * τ, as_parameter(:γ_MA) => γ + τ])
        "no error"
    catch e
        sprint(showerror, e)
    end
    @test msg == "ArgumentError: Semiconjugacy :typo: the parameter map assigns γ_MA, which is " *
                 "not a parameter of the target :ma_sir (parameters: β, γMA)"
    rs = verify(rempala; method = :symbolic)
    @test rs.ok && rs.method === :symbolic && rs.max_residual == 0.0
    rn = verify(rempala; method = :numeric)
    @test rn.ok && rn.method === :numeric && rn.max_residual < 1e-10 && rn.probes == 16
    ra = verify(rempala)
    @test ra.ok && ra.method === :symbolic
    # the old to_mass_action map keeps γ as the MA recovery rate: it is not a semiconjugacy
    old = Semiconjugacy(:old_to_mass_action, src, tgt, [S => q * ψ, I => φ_I];
                        parameter_map = [β => μ * τ, γMA => γ])
    rb = verify(old)
    @test !rb.ok && rb.method === :numeric
    @test rb.max_residual > 1e-2
    @test occursin("worst in component I", rb.details)
    @test occursin("residual of dI/dt: -τ*φ_I", rb.details)     # exactly the missing τ φ_I
    rbs = verify(old; method = :symbolic)
    @test !rbs.ok && rbs.method === :symbolic && rbs.max_residual > 1e-2
    @test occursin("does not simplify to 0 in component(s) I", rbs.details)
    @test !verify(old; method = :numeric).ok
    # the same quotient onto NEC's E_μ P (rempala_reduction) needs no parameter map;
    # I = φ_I, R = φ_R
    mE = mass_action(rempala_reduction(sir_model(), :μ))
    @test state_names(mE) == [:S, :I, :R]
    SE, IE, RE = mE.states
    mm = Semiconjugacy(:rempala_E, src, mE, [SE => q * ψ, IE => φ_I, RE => φ_R])
    @test verify(mm).ok && verify(mm).method === :symbolic
    @test verify(mm; method = :numeric).ok
    # the prevalence pop_I is not the MA "I": mapping I => pop_I fails
    @test !verify(Semiconjugacy(:prevalence, src, mE,
                                [SE => q * ψ, IE => pop_I, RE => pop_R])).ok
end

@testset "verify: Rempała on SEIR and SEAIR, and the Poisson isomorphism M2 (edge_doubling)" begin
    μ, q = as_parameter.((:μ, :q))
    for cm in (seir_model(), seair_model(), twostrain_model())
        src, θ, φ, pop = eb_poisson(cm; μ, q)
        # M3: onto MA(E_μ P), non-susceptible species ↦ φ_X
        tgt = mass_action(rempala_reduction(cm, :μ))
        s = only(susceptible_species(cm))
        map3 = Pair{Any,Any}[x => (n === s ? q * exp(μ * (θ - 1)) : φ[n])
                             for (x, n) in zip(tgt.states, state_names(tgt))]
        r3 = verify(Semiconjugacy(:rempala, src, tgt, map3))
        @test r3.ok && r3.method === :symbolic
        # M2: onto MA(D_μ P) with Φ_X = φ_X and X = pop_X
        d = edge_doubling(cm, :μ)
        tgt2 = mass_action(d)
        map2 = Pair{Any,Any}[]
        for (x, n) in zip(tgt2.states, state_names(tgt2))
            sn = string(n)
            v = n === s ? q * exp(μ * (θ - 1)) :
                startswith(sn, "Φ_") ? φ[Symbol(chop(sn; head = 2, tail = 0))] : pop[n]
            push!(map2, x => v)
        end
        m2 = Semiconjugacy(:poisson_iso, src, tgt2, map2; kind = :conjugacy)
        r2 = verify(m2)
        @test r2.ok && r2.method === :symbolic
        @test verify(m2; method = :numeric).ok
    end
end

@testset "pushforward along a trajectory (Rempała: exact S(t); the old map is far off)" begin
    μ, q, τ, γ = as_parameter.((:μ, :q, :τ, :γ))
    @variables θ φ_I pop_I
    ψ = exp(μ * (θ - 1))
    src = SymbolicODE(:eb; states = [θ, φ_I, pop_I],
                      rhs = [-τ * φ_I, -τ * φ_I + τ * φ_I * q * μ * ψ - γ * φ_I,
                             τ * φ_I * q * μ * ψ - γ * pop_I])
    @variables S I
    β, γMA = as_parameter.((:β, :γMA))
    tgt = SymbolicODE(:ma; states = [S, I], rhs = [-β * S * I, β * S * I - γMA * I])
    m = Semiconjugacy(:rempala, src, tgt, [S => q * ψ, I => φ_I];
                      parameter_map = [β => μ * τ, γMA => γ + τ])
    # vignette parameters of E08: Poisson(5), τ = 1/6, γ = 1/4, ρ = 0.01, T = 40
    μv, τv, γv, ρ = 5.0, 1 / 6, 1 / 4, 0.01
    qv = 1 - ρ
    h, nsteps = 0.01, 4000
    feb(u) = [-τv * u[2],
              -τv * u[2] + τv * u[2] * qv * μv * exp(μv * (u[1] - 1)) - γv * u[2],
              τv * u[2] * qv * μv * exp(μv * (u[1] - 1)) - γv * u[3]]
    traj = rk4(feb, [1.0, ρ, ρ], h, nsteps)
    tg = collect(0:h:(h * nsteps))
    pf = pushforward(m, traj, tg; p = Dict(:q => qv, :μ => μv))
    @test Set(keys(pf)) == Set([:S, :I])
    fma(β_, γ_) = u -> [-β_ * u[1] * u[2], β_ * u[1] * u[2] - γ_ * u[2]]
    ma = rk4(fma(μv * τv, γv + τv), [qv, ρ], h, nsteps)
    @test maximum(abs.(pf[:S] .- first.(ma))) < 1e-10          # measured 5e-14
    @test maximum(abs.(pf[:I] .- last.(ma))) < 1e-10
    # E08 (VERIFIED_ISSUES.md): the old map MA(μτ, γ) has max|ΔS| = 0.2777 and S(40) = 0.0406
    # against 0.2000; and the MA "I" is φ_I, which differs from the prevalence by up to 0.084
    old = rk4(fma(μv * τv, γv), [qv, ρ], h, nsteps)
    @test maximum(abs.(pf[:S] .- first.(old))) ≈ 0.2777 atol = 5e-4
    @test pf[:S][end] ≈ 0.2000 atol = 5e-4
    @test first(old[end]) ≈ 0.0406 atol = 5e-4
    @test maximum(abs.(pf[:I] .- getindex.(traj, 3))) ≈ 0.084 atol = 1e-3
    # every accepted form of the source trajectory gives the same result
    d = Dict(:θ => getindex.(traj, 1), :φ_I => getindex.(traj, 2), :pop_I => getindex.(traj, 3))
    M = permutedims(reduce(hcat, traj))
    @test pushforward(m, d, tg; p = Dict(:q => qv, :μ => μv))[:S] == pf[:S]
    @test pushforward(m, M, tg; p = Dict(:q => qv, :μ => μv))[:S] ≈ pf[:S]
    k(t) = traj[round(Int, t / h) + 1]
    @test pushforward(m, k, tg; p = Dict(:q => qv, :μ => μv))[:I] ≈ pf[:I]
    @test_throws ArgumentError pushforward(m, traj, tg; p = Dict(:q => qv))      # μ missing
    @test_throws ArgumentError pushforward(m, traj[1:10], tg; p = Dict(:q => qv, :μ => μv))
    @test_throws ArgumentError pushforward(m, M', tg; p = Dict(:q => qv, :μ => μv))
end

@testset "vector_fields_equal handles renaming" begin
    a = mass_action(sir_model())
    b = mass_action(sir_model(; S = :x, I = :y, R = :z))
    @test vector_fields_equal(a, b)                                  # bijection search
    @test !vector_fields_equal(a, b; rename = :none)
    @test vector_fields_equal(a, b; rename = Dict(:S => :x, :I => :y, :R => :z))
    @test !vector_fields_equal(a, b; rename = Dict(:S => :y, :I => :x, :R => :z))
    # order of the states does not matter; x(t) and plain x are the same coordinate
    τ, γ = as_parameter.((:τ, :γ))
    @variables S I R
    perm = SymbolicODE(:perm; states = [R, S, I], rhs = [γ * I, -τ * S * I, τ * S * I - γ * I])
    @test vector_fields_equal(a, perm; rename = :none)
    @test vector_fields_equal(perm, a)
    # MTK namespaces are stripped by :auto
    @variables sir₊S sir₊I sir₊R
    ns = SymbolicODE(:ns; states = [sir₊S, sir₊I, sir₊R],
                     rhs = [-τ * sir₊S * sir₊I, τ * sir₊S * sir₊I - γ * sir₊I, γ * sir₊I])
    @test vector_fields_equal(ns, a)
    # parameters are matched by name; an explicit rename covers them
    c = mass_action(sir_model(; τ = :β))
    @test !vector_fields_equal(c, a)
    @test vector_fields_equal(c, a; rename = Dict(:β => :τ))
    # a shuffled, renamed SEIR is found; different fields are not equal
    seir = mass_action(seir_model())
    @variables A B C D
    σ = as_parameter(:σ)
    shuffled = SymbolicODE(:shuffled; states = [C, A, D, B],
                           rhs = [σ * B - γ * C, -τ * A * C, γ * C, τ * A * C - σ * B])
    @test vector_fields_equal(shuffled, seir)
    wrong = SymbolicODE(:wrong; states = [C, A, D, B],
                        rhs = [σ * B - γ * C, -τ * A * C, γ * C, τ * A * C - γ * B])
    @test !vector_fields_equal(wrong, seir)
    @test !vector_fields_equal(a, mass_action(sirs_model()))
    @test !vector_fields_equal(a, mass_action(sir_model(); κ = 5))
    @test !vector_fields_equal(a, seir)
    # identities that the simplifier may not prove are decided by the numeric probes
    @variables x
    @test vector_fields_equal(SymbolicODE(:trig; states = [x], rhs = [sin(x)^2 + cos(x)^2 - 1 + x]),
                              SymbolicODE(:id; states = [x], rhs = [x]))
    # the same state names are trusted: S and I swapped is a different field under :auto, and
    # rename = :search looks for a bijection even then
    sw = SymbolicODE(:swapped; states = [I, S, R], rhs = [-τ * I * S, τ * I * S - γ * S, γ * S])
    @test !vector_fields_equal(a, sw)
    @test vector_fields_equal(a, sw; rename = :search)
    @test vector_fields_equal(a, perm; rename = :search)
    @test !vector_fields_equal(a, mass_action(sirs_model()); rename = :search)
    # a small term is a difference however large the other terms are (the tolerance is relative
    # to the terms that do not cancel), while floating-point netting is not
    @test !vector_fields_equal(SymbolicODE(:u; states = [S, I], rhs = [0, -0.1 * I]),
                               SymbolicODE(:w; states = [S, I], rhs = [0, 2e-13 * S * I - 0.1 * I]))
    tiny = SymbolicODE(:tiny; states = [S, I, R],
                       rhs = [-2e-13 * S * I, 2e-13 * S * I - 0.1 * I, 0.1 * I])
    @test !vector_fields_equal(SymbolicODE(:rec; states = [S, I, R], rhs = [0, -0.1 * I, 0.1 * I]),
                               tiny)
    @test vector_fields_equal(tiny, mass_action(sir_model(; τ = 2e-13, γ = 0.1)))
    @test 0.1 + 0.2 != 0.3
    @test vector_fields_equal(SymbolicODE(:u; states = [x], rhs = [0.3 * x]),
                              SymbolicODE(:w; states = [x], rhs = [0.1 * x + 0.2 * x]))
    @test !vector_fields_equal(SymbolicODE(:u; states = [x], rhs = [0.3 * x]),
                               SymbolicODE(:w; states = [x], rhs = [(0.3 + 1e-9) * x]))
    @test !vector_fields_equal(SymbolicODE(:u; states = [x], rhs = [x + 1e-14]),
                               SymbolicODE(:w; states = [x], rhs = [x]))
    # models are converted through symbolic_ode
    @test vector_fields_equal(sir_model(), a)
    @test_throws ArgumentError vector_fields_equal(a, b; rename = :sometimes)
    # fields that the diagonal signature cannot tell apart: a 6-cycle x_i' = x_{i+1} − x_i
    # against two 3-cycles (not a renaming of it; all 6! = 720 bijections are candidates)
    xs = [Symbolics.variable(Symbol(:x, i)) for i in 1:6]
    ys = [Symbolics.variable(Symbol(:y, i)) for i in 1:6]
    cyc6 = SymbolicODE(:cyc6; states = xs, rhs = [xs[mod1(i + 1, 6)] - xs[i] for i in 1:6])
    nxt = [2, 3, 1, 5, 6, 4]
    cyc33 = SymbolicODE(:cyc33; states = ys, rhs = [ys[nxt[i]] - ys[i] for i in 1:6])
    @test !vector_fields_equal(cyc6, cyc33)                       # the full search: no renaming
    # a search cut short is an error, not a false negative
    msg = try
        vector_fields_equal(cyc6, cyc33; max_renamings = 100)
        "no error"
    catch e
        sprint(showerror, e)
    end
    @test msg == "vector_fields_equal(:cyc6, :cyc33): gave up the search for a renaming of the " *
                 "6 states after 100 candidate bijections (the fields are too symmetric to tell " *
                 "the states apart); the answer is unknown, not false: pass rename = Dict(…) " *
                 "with the correspondence of the states, or raise max_renamings"
    # a relabelled 6-cycle is found
    perm6 = [4, 1, 6, 2, 5, 3]                                     # y_{perm6[i]} plays x_i
    inv6 = invperm(perm6)
    relab = SymbolicODE(:relab; states = ys,
                        rhs = [ys[perm6[mod1(inv6[j] + 1, 6)]] - ys[j] for j in 1:6])
    @test vector_fields_equal(cyc6, relab)
    @test_throws ArgumentError vector_fields_equal(cyc6, relab; max_renamings = 0)
    # a difference that is 0 at every probe point is never read as equality (WP10 review: t was
    # probed in (0.1, 1.0), so these fields were "equal"). Time t has its own box, (0.1, 1000) on
    # a log scale and stratified, so a vaccination switched on at t = 150 and a contact switched
    # on at t = 2 are seen
    @variables t
    ν = as_parameter(:ν)
    vax = SymbolicODE(:vax; states = [S, I],
                      rhs = [-τ * S * I - ν * ifelse(t > 150, 1, 0) * S, τ * S * I])
    novax = SymbolicODE(:novax; states = [S, I], rhs = [-τ * S * I, τ * S * I])
    @test !vector_fields_equal(vax, novax)
    @test !vector_fields_equal(novax, vax; rename = :search)
    @test vector_fields_equal(vax, vax)
    late = SymbolicODE(:late; states = [S, I],
                       rhs = [-τ * max(t - 2, 0) * S * I, τ * max(t - 2, 0) * S * I])
    @test !vector_fields_equal(late, SymbolicODE(:none; states = [S, I], rhs = [0 * S, 0 * I]))
    # where the probes cannot see the difference, the answer is unknown, not false: an error
    early = SymbolicODE(:early; states = [S, I], rhs = vax.rhs, domain = [t => (0.1, 100.0)])
    @test err(() -> vector_fields_equal(early, novax)) ==
          "vector_fields_equal(:early, :novax): cannot decide dS/dt: the difference " *
          "`-S*ν*ifelse(t > 150, 1, 0)` does not cancel: its term `-S*ν*ifelse(t > 150, 1, 0)` " *
          "is 0 at all 8 probe points, so they are no evidence that the difference is 0 (a term " *
          "that vanishes on the probe box but not everywhere, such as ν*ifelse(t > 150, 1, 0) " *
          "or max(x - 2, 0), or one too small to evaluate); the answer is unknown, not false: " *
          "give the variables of the difference a `domain` box where the term is not 0 (time t " *
          "is probed in (0.1, 1000) on a log scale by default), or raise probes"
    @test startswith(err(() -> vector_fields_equal(early, novax; rename = :search)),
                     "vector_fields_equal(:early, :novax): cannot decide dS/dt")
    # terms that are not 0 but cancel on the box are decided by the probes only through analytic
    # operations: max(x, 0) = x holds for x ≥ 0 only, so it is undecided (it used to be true;
    # WP10fix), and an exact 0 is decided without the probes, after folding:
    # (exp(0) − 1)·max(y − 2, 0) is 0 at every probe point, and would be undecided if exp(0) were
    # not folded
    @variables y
    @test startswith(err(() -> vector_fields_equal(SymbolicODE(:m; states = [x], rhs = [max(x, 0)]),
                                                   SymbolicODE(:id; states = [x], rhs = [x]))),
                     "vector_fields_equal(:m, :id): cannot decide dx/dt: the difference " *
                     "`-x + max(x, 0)` is 0 at all 8 probe points only through the values that " *
                     "`max(x, 0)` takes there")
    e0 = exp(x - x)
    @test string(Symbolics.simplify(Symbolics.expand((e0 - 1) * max(y - 2, 0)))) != "0"
    @test vector_fields_equal(SymbolicODE(:f; states = [x, y], rhs = [x, (e0 - 1) * max(y - 2, 0)]),
                              SymbolicODE(:g; states = [x, y], rhs = [x, 0 * y]))
end

@testset "verify: a residual that vanishes on the probe box is no evidence of 0" begin
    @variables x y t
    a, ν = as_parameter.((:a, :ν))
    src = SymbolicODE(:src; states = [x], rhs = [-a * x])
    kink = SymbolicODE(:kink; states = [y], rhs = [-a * y + max(a - 2, 0) * y])
    m = Semiconjugacy(:kink, src, kink, [y => x])
    # the residual −max(a − 2, 0)·x is 0 for every a in the parameter box (0.1, 1.0): it used to
    # verify numerically
    for method in (:auto, :numeric)
        r = verify(m; method)
        @test !r.ok && r.method === :numeric && r.max_residual == 0.0
        @test startswith(r.details, "Dπ·F − G∘π cannot be decided in component(s) y: it is 0 to " *
                                    "rtol = 1.0e-10 at 16 probes, but they are no evidence that " *
                                    "it is 0")
        @test occursin("residual of dy/dt: -x*max(-2 + a, 0): it does not cancel: its term " *
                       "`-x*max(-2 + a, 0)` is 0 at all 16 probe points", r.details)
    end
    @test !verify(m; method = :symbolic).ok
    # a domain on which the kink is not 0 decides it
    wide = SymbolicODE(:src; states = [x], rhs = [-a * x], domain = [a => (0.1, 5.0)])
    rw = verify(Semiconjugacy(:kink, wide, kink, [y => x]))
    @test !rw.ok && rw.max_residual > 0.1 && startswith(rw.details, "Dπ·F − G∘π ≠ 0")
    # time has its own box, so a term switched on at t = 150 is seen (t was probed in (0.1, 1.0));
    # t is time, not an unbound target parameter
    tv = SymbolicODE(:tv; states = [y], rhs = [-a * y + ν * ifelse(t > 150, 1, 0) * y])
    rt = verify(Semiconjugacy(:late, src, tv, [y => x]))
    @test !rt.ok && rt.max_residual > 0.1
    @test occursin("target parameter(s) ν are determined neither", rt.details)
    # an exact 0 after folding (exp(0) = 1) is symbolic, and terms that cancel pass numerically
    e0 = SymbolicODE(:e0; states = [y], rhs = [-a * y * exp(x - x)])
    @test verify(Semiconjugacy(:fold, src, e0, [y => x])).method === :symbolic
    @test verify(Semiconjugacy(:fold, src, e0, [y => x]); method = :numeric).ok
end

@testset "the probes decide term by term, and only through analytic operations (WP10fix)" begin
    # WP10fix review (scratchpad/wp10fix_review/probe1.jl, probe2.jl). Each case below differs
    # for a > 2 (or t > 2000) but used to be accepted: verify skipped the check when rounding
    # made the two sides differ in the last bit, and every check was per component, so a term
    # that is 0 at every probe point was hidden by other terms of its component that cancel.
    @variables x y t
    a, b, ω, ν, τ = as_parameter.((:a, :b, :ω, :ν, :τ))
    idx = SymbolicODE(:g1; states = [x], rhs = [x])
    # (verify, blocking issue 1) −(a + b)x against −ay − by + max(a − 2, 0)y: the residual rounds
    # to 2e-16, not 0, so the check was skipped and the map verified
    src = SymbolicODE(:src; states = [x], rhs = [-(a + b) * x])
    tgt = SymbolicODE(:tgt; states = [y], rhs = [-a * y - b * y + max(a - 2, 0) * y])
    for method in (:auto, :numeric)
        r = verify(Semiconjugacy(:m, src, tgt, [y => x]); method)
        @test !r.ok && r.method === :numeric
        @test 0 < r.max_residual < 1e-15                   # not bitwise 0: rounding
        @test occursin("residual of dy/dt: -x*max(-2 + a, 0): it does not cancel: its term " *
                       "`-x*max(-2 + a, 0)` is 0 at all 16 probe points", r.details)
    end
    # and its variant, −(a + b + ω)(a + 0.3)x against its expansion plus max(a − 2, 0)y
    src3 = SymbolicODE(:src3; states = [x], rhs = [-(a + b + ω) * x * (a + 0.3)])
    tgt3 = SymbolicODE(:tgt3; states = [y],
                       rhs = [Symbolics.expand(-(a + b + ω) * y * (a + 0.3)) + max(a - 2, 0) * y])
    for method in (:auto, :numeric)
        @test !verify(Semiconjugacy(:m3, src3, tgt3, [y => x]); method).ok
    end
    # (blocking issue 2) a term that is 0 at every probe point, next to terms that cancel
    # numerically in the same component: (3) in verify
    srcb = SymbolicODE(:src; states = [x], rhs = [-a * x])
    tgtb = SymbolicODE(:tgt; states = [y],
                       rhs = [-a * y * (sin(b)^2 + cos(b)^2) + max(a - 2, 0) * y])
    rb = verify(Semiconjugacy(:m, srcb, tgtb, [y => x]))
    @test !rb.ok &&
          occursin("its term `-x*max(-2 + a, 0)` is 0 at all 16 probe points", rb.details)
    # (1) in vector_fields_equal, with the names trusted and with the bijection search
    f2 = SymbolicODE(:f2; states = [x], rhs = [sin(x)^2 + cos(x)^2 - 1 + x + max(a - 2, 0) * x])
    for rename in (:auto, :search)
        @test startswith(err(() -> vector_fields_equal(f2, idx; rename)),
                         "vector_fields_equal(:f2, :g1): cannot decide dx/dt: the difference " *
                         "`x*max(-2 + a, 0)` does not cancel: its term `x*max(-2 + a, 0)` is 0 " *
                         "at all 8 probe points")
    end
    # (2) a vaccination switched on after t = 2000, beyond the time box, next to max(x, 0) − x
    f1 = SymbolicODE(:f1; states = [x], rhs = [max(x, 0) + ν * ifelse(t > 2000, 1, 0) * x])
    @test occursin("its term `x*ν*ifelse(t > 2000, 1, 0)` is 0 at all 8 probe points",
                   err(() -> vector_fields_equal(f1, idx)))
    # a term too small to evaluate (exp(−10⁴a) underflows) is not seen either
    fu = SymbolicODE(:fu; states = [x], rhs = [sin(x)^2 + cos(x)^2 - 1 + exp(-1e4 * a) * x + x])
    @test occursin("its term `x*exp(-10000.0a)` is 0 at all 8 probe points",
                   err(() -> vector_fields_equal(fu, idx)))
    # the same failure class, with no term that is 0 at the probe points: a cancellation that
    # holds only through the value a non-analytic part takes on the probe box (inside a quotient,
    # inside exp, or between switches at t = 150 and t = 151) is undecided
    piecewise = "only through the values that `max(-2 + a, 0)` takes there"
    fq = SymbolicODE(:fq; states = [x], rhs = [x / (1 + max(a - 2, 0))])
    @test occursin(piecewise, err(() -> vector_fields_equal(fq, idx)))
    fe = SymbolicODE(:fe; states = [x], rhs = [exp(max(a - 2, 0)) * x])
    @test occursin(piecewise, err(() -> vector_fields_equal(fe, idx)))
    k1 = SymbolicODE(:k1; states = [x], rhs = [ν * ifelse(t > 150, 1, 0) * x])
    k2 = SymbolicODE(:k2; states = [x], rhs = [ν * ifelse(t > 151, 1, 0) * x])
    @test occursin("only through the values that `ifelse(t > 150, 1, 0)` and " *
                   "`ifelse(t > 151, 1, 0)` take there", err(() -> vector_fields_equal(k1, k2)))
    rq = verify(Semiconjugacy(:q, SymbolicODE(:s; states = [x], rhs = [x]),
                              SymbolicODE(:q; states = [y], rhs = [y / (1 + max(a - 2, 0))]),
                              [y => x]))
    @test !rq.ok && occursin(piecewise, rq.details)
    # a domain on which the parts are not constant shows the difference: false, not an error
    fqw = SymbolicODE(:fq; states = [x], rhs = fq.rhs, domain = [a => (0.1, 5.0)])
    @test !vector_fields_equal(fqw, idx)
    # an identity that holds whatever value the non-analytic part takes is confirmed, and so is
    # an analytic identity multiplied by a switch
    @test vector_fields_equal(
        SymbolicODE(:p; states = [x], rhs = [max(a - 2, 0) * (sin(x)^2 + cos(x)^2) * x]),
        SymbolicODE(:q; states = [x], rhs = [max(a - 2, 0) * x]))
    @test vector_fields_equal(
        SymbolicODE(:p; states = [x], rhs = [ifelse(t > 150, 0.5, 1) * τ * exp(x) * exp(a)]),
        SymbolicODE(:q; states = [x], rhs = [ifelse(t > 150, 0.5, 1) * τ * exp(x + a)]))
    @test verify(Semiconjugacy(:w, SymbolicODE(:s; states = [x], rhs = [-a * x]),
                               SymbolicODE(:w; states = [y],
                                           rhs = [-a * y + max(a - 2, 0) * (sin(b)^2 +
                                                                            cos(b)^2 - 1) * y]),
                               [y => x])).ok
    @test vector_fields_equal(SymbolicODE(:m; states = [x], rhs = [x * (sin(a)^2 + cos(a)^2)]), idx)
    # a difference that is not finite at a probe point is no longer "different" (it was false):
    # an ArgumentError asking for a domain on which both fields are defined
    lg = SymbolicODE(:u; states = [x], rhs = [log(x - 0.5) + log(2.0)])
    lw = SymbolicODE(:w; states = [x], rhs = [log(2x - 1)])
    msg = err(() -> vector_fields_equal(lg, lw))
    @test startswith(msg, "ArgumentError: vector_fields_equal(:u, :w): cannot decide dx/dt")
    @test occursin("is not finite at the probe point x = ", msg) &&
          endswith(msg, "restrict the probe boxes with a `domain` on which both fields are " *
                        "defined")
    @test vector_fields_equal(SymbolicODE(:u; states = [x], rhs = lg.rhs,
                                          domain = [x => (0.6, 0.9)]), lw)
    # a finite probe point that shows a difference still decides it
    @test !vector_fields_equal(lg, SymbolicODE(:w; states = [x], rhs = [log(2x - 1) + x]))
end

@testset "the bijection search: no false from a value that is not finite, or from rounding" begin
    # WP10fix2 review (scratchpad/wp10fix2_review/probe.jl, probe2.jl): the leaf test compared
    # against NaN and rejected every bijection, so equal fields were `false` for rng_seed 1, 2, 6
    # and 8, also for the same field compared with itself under rename = :search, and a domain on
    # a's state did not help (the leaf points were drawn by b's state names)
    @variables x y
    a = as_parameter(:a)
    for f in (z -> log(z - 0.2), z -> sqrt(z - 0.2)), seed in 1:8
        u = SymbolicODE(:u; states = [x], rhs = [f(x)])
        @test vector_fields_equal(u, SymbolicODE(:w; states = [y], rhs = [f(y)]); rng_seed = seed)
        @test vector_fields_equal(u, SymbolicODE(:v; states = [x], rhs = [f(x)]);
                                  rename = :search, rng_seed = seed)
        ud = SymbolicODE(:u; states = [x], rhs = [f(x)], domain = [x => (0.3, 0.9)])
        @test vector_fields_equal(ud, SymbolicODE(:w; states = [y], rhs = [f(y)]); rng_seed = seed)
    end
    # a difference is still found where the fields are finite, whatever the seed
    for seed in 1:4
        @test !vector_fields_equal(SymbolicODE(:u; states = [x], rhs = [log(x - 0.2)]),
                                   SymbolicODE(:w; states = [y], rhs = [log(y - 0.2) + y]);
                                   rng_seed = seed)
    end
    # a renaming that no finite value rules out is decided by comparing the renamed fields: here
    # that is undecided (log(x − 0.5) is NaN for x < 0.5), the ArgumentError of the trusted path,
    # not `false`; it used to be an ArgumentError about the diagonal. A domain on either side
    # decides it, since the boxes follow the renaming
    lg = SymbolicODE(:u; states = [x], rhs = [log(x - 0.5) + log(2.0)])
    lw = SymbolicODE(:w; states = [y], rhs = [log(2y - 1)])
    msg = err(() -> vector_fields_equal(lg, lw))
    @test startswith(msg, "ArgumentError: vector_fields_equal(:u, :w): cannot decide dy/dt") &&
          occursin("is not finite at the probe point y = ", msg)
    lgd = SymbolicODE(:u; states = [x], rhs = lg.rhs, domain = [x => (0.6, 0.9)])
    @test vector_fields_equal(lgd, lw)
    @test vector_fields_equal(lg, SymbolicODE(:w; states = [y], rhs = lw.rhs,
                                              domain = [y => (0.6, 0.9)]))
    # so does a's box with an explicit renaming (it was keyed by a's name, and ignored)
    @test vector_fields_equal(lgd, lw; rename = Dict(:x => :y))
    # a's box also bounds the diagonal: max(x, 0.5) = x on x ∈ (0.6, 0.9), and the answer is the
    # trusted path's (undecided: the identity holds only through the value of the max), not a
    # `false` from the diagonal point 0.23 outside the box
    ma = SymbolicODE(:ma; states = [x], rhs = [max(x, 0.5)], domain = [x => (0.6, 0.9)])
    piecewise = "is 0 at all 8 probe points only through the values that `max(y, 0.5)` takes there"
    @test occursin(piecewise, err(() -> vector_fields_equal(ma, SymbolicODE(:mb; states = [y],
                                                                            rhs = [y]))))
    @test occursin("only through the values that `max(x, 0.5)` takes there",
                   err(() -> vector_fields_equal(ma, SymbolicODE(:mb; states = [x], rhs = [x]))))
    # boxes that the two domains give one coordinate are intersected; disjoint ones cannot be
    # compared (by name, and through the renaming)
    @test vector_fields_equal(SymbolicODE(:p; states = [x], rhs = [log(x - 0.5)],
                                          domain = [x => (0.3, 0.9)]),
                              SymbolicODE(:q; states = [x], rhs = [log(x - 0.5)],
                                          domain = [x => (0.55, 1.5)]))
    @test err(() -> vector_fields_equal(SymbolicODE(:p; states = [x], rhs = [a * x],
                                                    domain = [a => (0.1, 0.2)]),
                                        SymbolicODE(:q; states = [x], rhs = [a * x],
                                                    domain = [a => (0.3, 0.4)]))) ==
          "ArgumentError: vector_fields_equal(:p, :q): the domains give disjoint probe boxes, " *
          "a ∈ (0.1, 0.2) in :p and a ∈ (0.3, 0.4) in :q, so the fields cannot be compared there"
    @test startswith(err(() -> vector_fields_equal(
                         SymbolicODE(:p; states = [x], rhs = [log(x - 0.5)],
                                     domain = [x => (0.6, 0.9)]),
                         SymbolicODE(:q; states = [y], rhs = [log(y - 0.5)],
                                     domain = [y => (0.1, 0.2)]))),
                     "ArgumentError: vector_fields_equal(:p, :q): the domains give disjoint " *
                     "probe boxes, x ∈ (0.6, 0.9) in :p and y ∈ (0.1, 0.2) in :q")
    # rounding is compared with the size of the terms, not of the value: sin²x + cos²x − 1 rounds
    # to 1e-16, which is more than 1e-8 of the value 1e-9x, and the leaf test rejected the
    # renaming (false, while the same field under trusted names was true)
    tr = SymbolicODE(:u; states = [x], rhs = [sin(x)^2 + cos(x)^2 - 1 + 1e-9 * x])
    @test vector_fields_equal(tr, SymbolicODE(:w; states = [y], rhs = [1e-9 * y]))
    @test vector_fields_equal(tr, SymbolicODE(:w; states = [x], rhs = [1e-9 * x]))
    @test !vector_fields_equal(tr, SymbolicODE(:w; states = [y], rhs = [2e-9 * y]))
end

@testset "a non-analytic part takes values of both signs, small and large (WP10fix2 review)" begin
    # each case differs for a > 2, and was accepted (true / ok) because the unknown standing for
    # the non-analytic part was drawn from (0.1, 1.0), where sqrt(w²) = w and sqrt((2 − w)²) = 2 − w
    @variables x y t
    a, ν = as_parameter.((:a, :ν))
    SX = Base.get_extension(NetworkEpiCore, :NetworkEpiCoreSymbolicsExt)
    g = ifelse(a > 2, -1, 1)
    sq = SymbolicODE(:sq; states = [x], rhs = [sqrt(g^2) * x])
    gx = SymbolicODE(:gx; states = [x], rhs = [g * x])
    @test occursin("only through the values that `ifelse(a > 2, -1, 1)` takes there",
                   err(() -> vector_fields_equal(sq, gx)))
    r = verify(Semiconjugacy(:sg, SymbolicODE(:s; states = [x], rhs = [g * x]),
                             SymbolicODE(:q; states = [y], rhs = [sqrt(g^2) * y]), [y => x]))
    @test !r.ok && r.max_residual == 0.0 &&
          occursin("only through the values that `ifelse(a > 2, -1, 1)` takes there", r.details)
    m2 = SymbolicODE(:m2; states = [x], rhs = [sqrt((2 - max(a, 0))^2) * x])
    l2 = SymbolicODE(:l2; states = [x], rhs = [(2 - max(a, 0)) * x])
    @test occursin("only through the values that `max(a, 0)` takes there",
                   err(() -> vector_fields_equal(m2, l2)))
    # they do differ: on a ∈ (0.1, 5) all are false
    wide = [a => (0.1, 5.0)]
    @test !vector_fields_equal(SymbolicODE(:sq; states = [x], rhs = sq.rhs, domain = wide), gx)
    @test !vector_fields_equal(SymbolicODE(:m2; states = [x], rhs = m2.rhs, domain = wide), l2)
    rw = verify(Semiconjugacy(:sg, SymbolicODE(:s; states = [x], rhs = [g * x], domain = wide),
                              SymbolicODE(:q; states = [y], rhs = [sqrt(g^2) * y]), [y => x]))
    @test !rw.ok && rw.max_residual > 0.1
    # identities that hold for every value of the part are still confirmed, also where a large
    # value overflows (exp(10w) at w ≥ 71: that probe is redrawn with a small value); verify
    # does not prove this one symbolically, so the probes decide
    e = exp(10 * max(a - 2, 0))
    re = verify(Semiconjugacy(:e, SymbolicODE(:s; states = [x], rhs = [e * x]),
                              SymbolicODE(:q; states = [y], rhs = [e * (sin(y)^2 + cos(y)^2) * y]),
                              [y => x]))
    @test re.ok && re.method === :numeric
    @test vector_fields_equal(
        SymbolicODE(:p; states = [x], rhs = [max(a - 2, 0) * (sin(x)^2 + cos(x)^2) * x]),
        SymbolicODE(:q; states = [x], rhs = [max(a - 2, 0) * x]))
    # the conservative side: sqrt(max(u, 0)²) = max(u, 0) is true, but not for a negative
    # stand-in, so it is undecided
    @test occursin("only through the values that `max(a, 0)` takes there",
                   err(() -> vector_fields_equal(
                       SymbolicODE(:p; states = [x], rhs = [sqrt(max(a, 0)^2) * x]),
                       SymbolicODE(:q; states = [x], rhs = [max(a, 0) * x]))))
    # the draws: for every unknown, half of the probes of each sign, with magnitudes in
    # [0.1, 1000] both below 1 and above 100 in each sign
    for seed in 1:3, n in (8, 16)
        W = SX._stand_in_values(Random.Xoshiro(seed), 3, n)
        for c in 1:3
            w = W[:, c]
            @test count(>(0), w) == n ÷ 2 && all(v -> 0.1 <= abs(v) <= 1000, w)
            @test any(>(100), w) && any(<(-100), w) && any(v -> 0 < v < 1, w) &&
                  any(v -> -1 < v < 0, w)
        end
    end
    # the documented limit: an analytic identity is confirmed on the probe box, not across a
    # branch point outside it (sqrt((2 − a)²) = 2 − a only for a ≤ 2; the default box of a is
    # (0.1, 1.0)); a domain that covers a > 2 shows it
    br = SymbolicODE(:br; states = [x], rhs = [sqrt((2 - a)^2) * x])
    lin = SymbolicODE(:lin; states = [x], rhs = [(2 - a) * x])
    @test vector_fields_equal(br, lin)
    @test !vector_fields_equal(SymbolicODE(:br; states = [x], rhs = br.rhs, domain = wide), lin)
    # the same rule for single expressions (for the rate comparisons of other front ends)
    τ, γ = as_parameter.((:τ, :γ))
    v(x, y; kw...) = SX._expressions_verdict(x, y; kw...).verdict
    @test v(:(τ * exp(0)), τ) === :equal
    @test v(:(τ + γ), :(γ + τ)) === :equal
    @test v(sin(a)^2 + cos(a)^2, 1) === :equal
    @test v(τ, 2τ) === :different
    @test v(max(a, 0), a) === :undecided
    @test v(sqrt(g^2), g) === :undecided
    @test v(ν * ifelse(t > 2000, 1, 0), 0) === :undecided
    @test v(ν * ifelse(t > 150, 1, 0), 0) === :different
    @test v(sqrt((2 - a)^2), 2 - a; domain = wide) === :different
end

@testset "NaturalTransformation registry" begin
    net5 = ConfigurationNetwork(PoissonDegree(5.0))
    μ, q = as_parameter.((:μ, :q))
    function rempala_component(cm, net)
        src, θ, φ, pop = eb_poisson(cm; μ, q)
        tgt = mass_action(rempala_reduction(cm, :μ))
        s = only(susceptible_species(cm))
        mp = Pair{Any,Any}[x => (n === s ? q * exp(μ * (θ - 1)) : φ[n])
                           for (x, n) in zip(tgt.states, state_names(tgt))]
        return Semiconjugacy(:rempala, src, tgt, mp)
    end
    ispois(cm, net) = net isa ConfigurationNetwork && net.degrees isa PoissonDegree
    η = NaturalTransformation(:wp10_test_rempala; source = :edge_based, target = :mass_action,
                              applies = ispois, component = rempala_component,
                              evidence = [Evidence(:lean, "NEP.rempala")])
    @test register_transformation!(η) === η
    @test η in transformations()
    @test η in transformations(; source = :edge_based)
    @test !(η in transformations(; target = :s_anchored))
    @test η in transformations(sir_model(), net5)
    @test !(η in transformations(sir_model(), ConfigurationNetwork(RegularDegree(4))))
    @test transformation(:wp10_test_rempala) === η
    @test_throws ArgumentError transformation(:wp10_no_such_transformation)
    m = η(sir_model(), net5)
    @test m isa Semiconjugacy && verify(m).ok
    @test_throws ArgumentError η(sir_model(), ConfigurationNetwork(RegularDegree(4)))
    # re-registering a name replaces the entry
    η2 = NaturalTransformation(:wp10_test_rempala; source = :edge_based, target = :mass_action,
                               applies = ispois, component = rempala_component,
                               kind = :semiconjugacy)
    register_transformation!(η2)
    @test transformation(:wp10_test_rempala) === η2
    @test count(x -> x.name === :wp10_test_rempala, transformations()) == 1
    bad = NaturalTransformation(:wp10_test_bad; source = :edge_based, target = :mass_action,
                                applies = (cm, net) -> true, component = (cm, net) -> 42)
    @test_throws ArgumentError bad(sir_model(), net5)
    @test_throws ArgumentError NaturalTransformation(:x; source = :a, target = :b,
                                                     applies = (c, n) -> true,
                                                     component = (c, n) -> nothing, kind = :iso)
    @test occursin("edge_based ⇒ mass_action", sprint(show, η))
end

@testset "check_naturality: the Rempała quotient commutes with gluing (H1 for E_μ)" begin
    net5 = ConfigurationNetwork(PoissonDegree(5.0))
    μ, q = as_parameter.((:μ, :q))
    # the component on any T_EB part (with or without a susceptible class), per reaction
    function part_target(cm)
        Σ = susceptible_species(cm)
        @variables t
        X = Dict(x => only(Symbolics.@variables $x(t)) for x in species_names(cm))
        G = Dict{Symbol,Any}(x => Symbolics.Num(0) for x in species_names(cm))
        for c in contacts(cm)
            τ = as_parameter(c.rate)
            f = μ * τ * X[c.recipient] * X[c.infector]
            G[c.recipient] -= f
            G[c.product] += f
            G[c.infector] -= τ * X[c.infector]          # J → ∅ at τ on the edge copy
        end
        for tr in node_transitions(cm)
            f = as_parameter(tr.rate) * X[tr.from]
            G[tr.from] -= f
            tr.to === nothing || (G[tr.to] += f)
        end
        sp = species_names(cm)
        return SymbolicODE(Symbol(:E_, cm.name); states = [X[x] for x in sp],
                           rhs = [G[x] for x in sp])
    end
    function component(cm, net; scale = 1)
        src, θ, φ, pop = eb_poisson(cm; μ, q)
        tgt = part_target(cm)
        Σ = susceptible_species(cm)
        mp = Pair{Any,Any}[x => (n in Σ ? q * exp(μ * (θ - 1)) : φ[n])
                           for (x, n) in zip(tgt.states, state_names(tgt))]
        scale == 1 && return Semiconjugacy(:rempala, src, tgt, mp)
        # a model-dependent time change: every component still verifies, but it is not natural
        c = scale(cm)
        src2 = SymbolicODE(src.name, src.states, src.rhs ./ c, src.parameters, src.domain)
        tgt2 = SymbolicODE(tgt.name, tgt.states, tgt.rhs ./ c, tgt.parameters, tgt.domain)
        return Semiconjugacy(:rescaled, src2, tgt2, mp)
    end
    η = NaturalTransformation(:wp10_test_rempala_parts; source = :edge_based,
                              target = :mass_action, applies = (cm, net) -> true,
                              component = component)
    tr = ContactModel(:tr; contacts = [Contact(:S, :I, :E, :τ)])
    pr = ContactModel(:pr; transitions = [NodeTransition(:E, :I, :σ), NodeTransition(:I, :R, :γ)])
    r = check_naturality(η, tr, pr; glued = seir_model(), network = net5)
    @test r.ok && r.method === :symbolic
    @test occursin("commutes with this gluing", r.details)
    # through glue itself (WP8), on open models
    ta = open_model(tr; legs = [[:S], [:E, :I]])
    pa = open_model(pr; legs = [[:E, :I, :R]])
    rg = check_naturality(η, ta, pa; on = [:E, :I], network = net5)
    @test rg.ok
    # on = nothing is glue's own default (the species on legs of both parts: E and I)
    @test check_naturality(η, ta, pa; network = net5).ok
    # a wrong glued model is detected
    wrong = ContactModel(:seir2; contacts = [Contact(:S, :I, :E, :τ)],
                         transitions = [NodeTransition(:E, :I, :σ)])
    rw = check_naturality(η, tr, pr; glued = wrong, network = net5)
    @test !rw.ok && occursin("source", rw.details)
    # so is one whose extra reaction vanishes on the probe box (E → R at max(σ − 2, 0)): the
    # comparison is undecided, a failed check (it used to pass)
    extra = ContactModel(:seir3; contacts = [Contact(:S, :I, :E, :τ)],
                         transitions = [NodeTransition(:E, :I, :σ), NodeTransition(:I, :R, :γ),
                                        NodeTransition(:E, :R, :(max(σ - 2, 0)))])
    rx = check_naturality(η, tr, pr; glued = extra, network = net5)
    @test !rx.ok && !occursin("fails verify", rx.details)
    @test occursin("source: cannot decide whether dφ_E/dt of the glued model is the sum over the " *
                   "parts: the difference", rx.details)
    # and one whose extra rate is max(σ − 2, 0) plus terms that cancel only numerically
    # (e^{σ+1} − e^σ·e): the vanishing term was hidden by the others of its component, and the
    # check passed (WP10fix review, blocking issue 2)
    hidden = ContactModel(:seir4; contacts = [Contact(:S, :I, :E, :τ)],
                          transitions = [NodeTransition(:E, :I, :σ), NodeTransition(:I, :R, :γ),
                                         NodeTransition(:E, :R,
                                                        :(exp(σ + 1) - exp(σ) * exp(1) +
                                                          max(σ - 2, 0)))])
    rh = check_naturality(η, tr, pr; glued = hidden, network = net5)
    @test !rh.ok && !occursin("fails verify", rh.details)
    @test occursin("source: cannot decide whether dφ_E/dt of the glued model is the sum over the " *
                   "parts: the difference", rh.details)
    @test occursin("is 0 at all 16 probe points", rh.details)
    # a model-dependent time change (1/number of reactions) verifies componentwise but is lax
    nr(cm) = length(contacts(cm)) + length(node_transitions(cm))
    ηlax = NaturalTransformation(:wp10_test_lax; source = :edge_based, target = :mass_action,
                                 applies = (cm, net) -> true,
                                 component = (cm, net) -> component(cm, net; scale = nr))
    rl = check_naturality(ηlax, tr, pr; glued = seir_model(), network = net5)
    @test !rl.ok
    @test !occursin("fails verify", rl.details)
    @test occursin("sum over the parts", rl.details)
end

@testset "steward-2: stand-ins at ≥ 8 points, ifelse(c, x, x), a budgeted zero test" begin
    @variables x y
    a = as_parameter(:a)
    SX = Base.get_extension(NetworkEpiCore, :NetworkEpiCoreSymbolicsExt)
    g = ifelse(a > 2, -1, 1)
    # (WP10fix2 review) with probes = 1 or 2 the unknown standing for g was drawn at 1 or 2 points
    # only (all positive with probes = 1), so sqrt(g²)x = gx was confirmed; the unknowns are now
    # drawn at 8 points (cycling through the probe points) whatever `probes` is
    for pr in (1, 2, 3)
        r = verify(Semiconjugacy(:sg, SymbolicODE(:s; states = [x], rhs = [g * x]),
                                 SymbolicODE(:q; states = [y], rhs = [sqrt(g^2) * y]), [y => x]);
                   probes = pr)
        @test !r.ok
        @test occursin("only through the values that `ifelse(a > 2, -1, 1)` takes there",
                       err(() -> vector_fields_equal(
                           SymbolicODE(:sq; states = [x], rhs = [sqrt(g^2) * x]),
                           SymbolicODE(:gx; states = [x], rhs = [g * x]); probes = pr)))
    end
    for seed in 1:20
        v = SX._expressions_verdict(sqrt((2 - max(a, 0))^2), 2 - max(a, 0); probes = 2,
                                    rng_seed = seed).verdict
        @test v === :undecided
    end
    # (WP18) ifelse(c, x, x) is x: neither an opaque part nor an undecided residual
    same = ifelse(a > 2, x, x)
    rs = verify(Semiconjugacy(:ie, SymbolicODE(:s; states = [x], rhs = [a * x]),
                              SymbolicODE(:q; states = [y], rhs = [a * ifelse(a > 2, y, y)]),
                              [y => x]))
    @test rs.ok
    @test vector_fields_equal(SymbolicODE(:p; states = [x], rhs = [exp(a) * same]),
                              SymbolicODE(:q; states = [x], rhs = [exp(a) * x]))
    @test SX._expressions_verdict(ifelse(a > 2, a^2, a^2), a^2).verdict === :equal
    @test isequal(SX._fold_ifelse(Symbolics.unwrap(ifelse(a > 1, ifelse(a > 2, x, x), x) + 1)),
                  Symbolics.unwrap(x + 1))
    # a branch that differs is still opaque
    @test SX._expressions_verdict(ifelse(a > 2, a, 2a), a).verdict !== :equal
    # (WP18 review) the zero test is a budgeted shortcut: this residual of the M6 map on the
    # bimodal {2, 10} network (floating-point coefficients 5/6) made SymbolicUtils'
    # simplify_fractions recurse until the stack overflowed (the error was swallowed); its
    # floating-point constants are now rationalised first (exact GCDs), and the identity (the
    # residual without its 1e-16 rounding terms) is shown to be 0
    @variables q γ τ θ
    e = (1.6666666666666667q * γ^2 * θ) / τ + (-13.333333333333332q * γ * (-γ + γ * θ) * θ^9) / τ +
        (1.6666666666666665q * γ^2 * θ^9) / τ + (1.6666666666666667q * γ * (-γ + γ * θ)) / τ +
        (14.999999999999998q * γ * (-γ + γ * θ) * θ^8) / τ + (-1.6666666666666667q * γ^2 * θ^2) / τ +
        (-1.6666666666666665q * γ^2 * θ^10) / τ + 3.3333333333333335q * γ * θ +
        1.6666666666666667(((-γ + γ * θ) / τ)^2) * q * τ - 1.6666666666666672q^2 * γ * θ -
        3.3333333333333335q * γ * θ^2 + 3.3333333333333335q * (-γ + γ * θ) * θ +
        1.6666666666666672q^2 * γ * θ^2 - 1.6666666666666674q^2 * (-γ + γ * θ) * θ +
        16.666666666666664q * γ * θ^9 + 15.0(((-γ + γ * θ) / τ)^2) * q * τ * θ^8 -
        16.666666666666668q^2 * γ * θ^9 - 16.666666666666664q * γ * θ^10 +
        16.666666666666668q * (-γ + γ * θ) * θ^9 + 16.666666666666668q^2 * γ * θ^10 -
        16.66666666666667q^2 * (-γ + γ * θ) * θ^9 - 14.999999999999998q^2 * γ * θ^17 +
        14.999999999999998q^2 * γ * θ^18 - 15.0q^2 * (-γ + γ * θ) * θ^17
    t0 = time()
    @test SX._symbolic_zero(e) === true
    @test time() - t0 < 60
    @test SX._symbolic_zero(e + 0.1q * θ^3) === false
    # constants are rationalised before any arithmetic on them: 6·(5/6) is 5 (in floating point
    # 6·0.8333333333333334 = 5.000000000000001), and fractions combine exactly
    @test SX._symbolic_zero(6 * (0.8333333333333334θ^2 + θ) - 5θ^2 - 6θ)
    @test SX._symbolic_zero((0.5q * θ + 0.25θ) / (2q + 1) - 0.25θ)
    @test !SX._symbolic_zero(6 * (0.8333333333333334θ^2 + θ) - 5.1θ^2 - 6θ)
    @test !SX._symbolic_zero(1e-16 * θ + 0.5θ - 0.5θ)             # a rounding residue is kept
    @test SX._rationalize_float(0.8333333333333334) == 5 // 6 && SX._rationalize_float(4.0) === 4
    # exact expressions are still simplified: fractions combine, and exp(0) folds
    @test SX._symbolic_zero((a * x + x) / (a + 1) - x)
    @test SX._symbolic_zero(exp(0) * a - a)
    @test SX._symbolic_zero(0.5a + 0.5a - a)            # cancels on expansion
    @test !SX._symbolic_zero(a - 2a)
    @test SX._has_float(Symbolics.unwrap(0.5a)) && !SX._has_float(Symbolics.unwrap(2a + x^3))
    @test SX._node_count(Symbolics.unwrap(a + x), 100) == 3
end
