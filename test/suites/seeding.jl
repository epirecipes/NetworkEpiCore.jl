# Owner: WP7. Seeding specifications (DESIGN §E.2, §A.5; verified issue N01): validation,
# RoundNearestTiesAway counts that error instead of silently seeding 0 nodes or overfilling N,
# the background compartment, the exact (scenario) mode, fractions, the default seeding rule
# (the unique entry state), equality and canonical text.

using NetworkEpiCore, Test
const NEC = NetworkEpiCore

counts(s, N; kw...) = Dict(seed_counts(s, N; kw...))

@testset "construction and validation" begin
    s = SeedFraction(:I => 0.01)
    @test s.fractions == [:I => 0.01]
    @test s.default === nothing
    @test SeedFraction([:I => 0.01]) == s                        # NO's vector form
    @test SeedFraction(Pair{Symbol,Float64}[:I => 0.01]) == s
    @test SeedFraction([:I => 1 // 100], nothing) == s
    @test SeedFraction(:I => 0.01; default = :S).default === :S
    @test SeedFraction().fractions == Pair{Symbol,Float64}[]
    @test_throws ArgumentError SeedFraction(:I => 0.5, :I => 0.5)   # duplicate (N01: unwritten state)
    @test_throws ArgumentError SeedFraction(:I => NaN)
    @test_throws ArgumentError SeedFraction(:I => -0.1)             # N01: out-of-bounds write
    @test_throws ArgumentError SeedFraction(:I => 1.2)
    @test_throws ArgumentError SeedFraction(:S => 0.9, :I => 0.3)   # sum 1.2 (N01 D)
    @test SeedFraction(:S => 0.9, :I => 0.1 + 1e-12) isa SeedFraction  # floating-point noise
    @test_throws ArgumentError SeedFraction(:S => 0.5, :I => 0.01; default = :S)  # named background ⇒ Σ = 1
    @test SeedCount(:E => 50).counts == [:E => 50]
    @test SeedCount([:E => 50]; default = :S).default === :S
    @test_throws ArgumentError SeedCount(:E => -1)
    @test_throws ArgumentError SeedCount(:E => 1, :E => 2)
    n = SeedNodes(:I => [1, 17, 42])
    @test n.assignments == [:I => [1, 17, 42]]
    @test SeedNodes([:I => [1, 17, 42]], nothing) == n            # NO's positional form
    @test SeedNodes(:I => 1:2; default = :S).default === :S
    @test_throws ArgumentError SeedNodes(:I => [1, 1])
    @test_throws ArgumentError SeedNodes(:I => [1, 2], :E => [2])
    @test_throws ArgumentError SeedNodes(:I => [0])
    @test_throws ArgumentError SeedNodes(:I => [1], :I => [2])
    @test s isa SeedSpec && n isa SeedSpec && SeedCount(:I => 1) isa SeedSpec
    @test hash(SeedFraction(:I => 0.01)) == hash(SeedFraction([:I => 0.01]))
end

@testset "SeedFraction counts: RoundNearestTiesAway, never a silent zero (N01)" begin
    @test seed_counts(SeedFraction(:I => 0.001), 500) == [:I => 1]       # ρN = 0.5 → 1 (ties away)
    @test_throws ArgumentError seed_counts(SeedFraction(:I => 0.001), 499)   # 0.499 → 0: error
    @test_throws ArgumentError seed_counts(SeedFraction(:I => 0.01), 40)     # 0.4 → 0: error
    @test seed_counts(SeedFraction(:I => 0.001), 2500) == [:I => 3]      # 2.5 → 3 (not 2, ties to even)
    @test seed_counts(SeedFraction(:I => 0.001), 1500) == [:I => 2]
    @test seed_counts(SeedFraction(:I => 0.001), 3500) == [:I => 4]
    @test seed_counts(SeedFraction(:I => 0.01), 10_000) == [:I => 100]
    @test seed_counts(SeedFraction(:I => 0.015), 100) == [:I => 2]       # a floating-point near-tie
    @test seed_counts(SeedFraction(:I => 0.035), 100) == [:I => 4]
    @test seed_counts(SeedFraction(:I => 0.0), 100) == [:I => 0]         # zero is allowed
    @test seed_counts(SeedFraction(:I => 0.3), 0) == [:I => 0]           # N = 0 is allowed
    err = try seed_counts(SeedFraction(:I => 0.001), 400); nothing catch e; e end
    @test err isa ArgumentError && occursin("gives 0 nodes", err.msg) && occursin("N = 400", err.msg)
    # order of the specification is kept
    @test seed_counts(SeedFraction(:I => 0.004, :E => 0.006), 1000) == [:I => 4, :E => 6]
    # every named count within 1/2 of its quota: ρN for many N
    within_half = [abs(counts(SeedFraction(:I => ρ), N)[:I] - ρ * N) <= 0.5 + 1e-9
                   for N in 1:600, ρ in (0.01, 0.05, 0.1, 0.3) if ρ * N >= 0.5]
    @test length(within_half) > 2000 && all(within_half)
end

@testset "the background compartment absorbs the rounding (N01 B, C)" begin
    # the pattern :I => p, :S => 1 − p with S as background: no false error, no leak into R/E
    @test seed_counts(SeedFraction(:S => 0.7, :I => 0.3), 5; background = :S) == [:I => 2, :S => 3]
    @test seed_counts(SeedFraction(:S => 0.9, :I => 0.1), 25; background = :S) == [:I => 3, :S => 22]
    @test seed_counts(SeedFraction(:S => 0.9, :I => 0.1; default = :S), 15) == [:I => 2, :S => 13]
    ok = Bool[]
    for N in 1:400, p in (0.1, 0.3)
        p * N < 0.5 && continue
        c = counts(SeedFraction(:I => p, :S => 1 - p), N; background = :S)
        push!(ok, c[:I] + c[:S] == N && abs(c[:I] - p * N) <= 0.5 + 1e-9 && keys(c) == Set([:I, :S]))
    end
    @test length(ok) > 700 && all(ok)
    # without a background, fractions summing to 1 can round above N: an error that says why
    err = try seed_counts(SeedFraction(:S => 0.7, :I => 0.3), 5); nothing catch e; e end
    @test err isa ArgumentError && occursin("more than N", err.msg) && occursin("background", err.msg)
    @test_throws ArgumentError seed_counts(SeedFraction(:E => 0.5, :I => 0.5), 5)
    # with the background unnamed and given, the overflow comes from the seeds alone, and the
    # advice says so rather than "pass the background" (WP7 review)
    err = try seed_counts(SeedFraction(:I => 0.5, :R => 0.5), 5; background = :S); nothing catch e; e end
    @test err isa ArgumentError && occursin("more than N", err.msg) &&
          occursin("the seeds alone round to more than N", err.msg) &&
          !occursin("pass the background", err.msg)
    # a constructed specification does not change when the caller's vector does (WP7 review)
    v = [:I => 0.01]
    sf = SeedFraction(v)
    push!(v, :I => 0.5)
    @test sf.fractions == [:I => 0.01]
    vc = [:I => 3]
    sc = SeedCount(vc)
    vc[1] = :I => 7
    @test sc.counts == [:I => 3]
    nodes = [1, 2]
    sn = SeedNodes(Pair{Symbol,Vector{Int}}[:I => nodes], nothing)
    push!(nodes, 1)
    @test sn.assignments == [:I => [1, 2]]
    # the remainder goes to the background only
    @test seed_counts(SeedFraction(:I => 0.01), 1000; background = :S) == [:I => 10, :S => 990]
    @test seed_counts(SeedFraction(:I => 0.01; default = :S), 1000; background = :R) == [:I => 10, :S => 990]
    # a background named with too small a share must not round to 0
    @test_throws ArgumentError seed_counts(SeedFraction(:S => 0.01, :I => 0.99), 10; background = :S)
    # a named background forces Σ = 1
    @test_throws ArgumentError seed_counts(SeedFraction(:S => 0.5, :I => 0.01), 100; background = :S)
    # the small remainder of the N01 skeptic's cases is fine
    @test counts(SeedFraction(:S => 0.95, :I => 0.049), 100; background = :R)[:I] == 5
end

@testset "exact mode: ρN must be an integer (scenarios)" begin
    @test seed_counts(SeedFraction(:I => 0.01), 10_000; exact = true) == [:I => 100]
    @test seed_counts(SeedFraction(:I_a => 0.01, :I_b => 0.01), 10_000; exact = true) == [:I_a => 100, :I_b => 100]
    err = try seed_counts(SeedFraction(:I => 0.0015), 1000; exact = true); nothing catch e; e end
    @test err isa ArgumentError && occursin("not a whole number", err.msg)
    @test_throws ArgumentError seed_counts(SeedFraction(:I => 0.3, :S => 0.7), 5; background = :S, exact = true)
end

@testset "SeedCount and SeedNodes counts" begin
    @test seed_counts(SeedCount(:E => 50), 1000) == [:E => 50]
    @test seed_counts(SeedCount(:E => 50), 1000; background = :S) == [:E => 50, :S => 950]
    @test seed_counts(SeedCount(:E => 50, :S => 950), 1000; background = :S) == [:E => 50, :S => 950]
    @test_throws ArgumentError seed_counts(SeedCount(:E => 50, :S => 900), 1000; background = :S)
    @test_throws ArgumentError seed_counts(SeedCount(:E => 1001), 1000)
    n = SeedNodes(:I => [1, 17, 42], :R => [3])
    @test seed_counts(n, 50) == [:I => 3, :R => 1]
    @test seed_counts(n, 50; background = :S) == [:I => 3, :R => 1, :S => 46]
    @test seed_counts(SeedNodes(:I => [1], :S => [2]; default = :S), 10) == [:I => 1, :S => 9]
    @test_throws ArgumentError seed_counts(n, 41)                  # node 42 out of range
    @test_throws ArgumentError seed_counts(SeedFraction(:I => 0.1), -1)
end

@testset "seed_fractions" begin
    @test seed_fractions(SeedFraction(:I => 0.01)) == [:I => 0.01]
    @test seed_fractions(SeedFraction(:I => 0.01); background = :S) == [:I => 0.01, :S => 0.99]
    @test seed_fractions(SeedFraction(:S => 0.9, :I => 0.1); background = :S) == [:I => 0.1, :S => 0.9]
    @test seed_fractions(SeedFraction(:I => 0.0015); N = 1000) == [:I => 0.0015]   # ρ itself, not rounded
    @test seed_fractions(SeedCount(:E => 50); N = 1000) == [:E => 0.05]
    @test seed_fractions(SeedNodes(:I => [1, 2]); N = 10, background = :S) == [:I => 0.2, :S => 0.8]
    @test_throws ArgumentError seed_fractions(SeedCount(:E => 50))              # N needed
    @test_throws ArgumentError seed_fractions(SeedFraction(:S => 0.5, :I => 0.01); background = :S)
end

@testset "default seeding: the unique entry state (E.2, H7)" begin
    mk(; kw...) = NEC.ContactModel(:m; kw...)
    C, T = NEC.Contact, NEC.NodeTransition
    sir = mk(contacts = [C(:S, :I, :I, :τ)], transitions = [T(:I, :R, :γ)])
    seir = mk(contacts = [C(:S, :I, :E, :τ)], transitions = [T(:E, :I, :σ), T(:I, :R, :γ)])
    seair = mk(contacts = [C(:S, :I, :E, :τI), C(:S, :A, :E, :τA)],
               transitions = [T(:E, :I, :σ), T(:E, :A, :σ), T(:I, :R, :γ), T(:A, :R, :γ)])
    two = mk(contacts = [C(:S, :I1, :I1, :τ1), C(:S, :I2, :I2, :τ2)],
             transitions = [T(:I1, :R, :γ), T(:I2, :R, :γ)])
    @test default_seed_state(sir) === :I
    @test default_seed_state(seir) === :E                        # the entry state, not I
    @test default_seed_state(seair) === :E                       # two infectors, one entry
    err = try default_seed_state(two); nothing catch e; e end
    @test err isa ArgumentError && occursin("several entry states", err.msg) && occursin("I1", err.msg)
    @test default_seed(seir, 0.01) == SeedFraction(:E => 0.01; default = :S)
    @test seed_counts(default_seed(seir, 0.01), 1000) == [:E => 10, :S => 990]
    @test_throws ArgumentError default_seed(two, 0.01)
    if isdefined(NEC, :seir_model)                               # WP6's canned models, when present
        @test default_seed_state(NEC.seir_model()) === :E
        @test default_seed_state(NEC.sir_model()) === :I
    end
    # only entries into infection count (§J.8; WP15 request to the NEC steward): the product of
    # a tracing contact is not infected, so the tracing model has one entry state, I (it used to
    # throw "several entry states (I, Q)")
    trace = mk(contacts = [C(:S, :I, :I, :τ), C(:S, :I, :Q, :κ)],
               transitions = [T(:I, :R, :γ), T(:Q, :S, :ω)])
    @test NEC.entry_species(trace) == [:I, :Q]                   # the typing-level definition
    @test default_seed_state(trace) === :I
    @test default_seed(trace, 0.01) == SeedFraction(:I => 0.01; default = :S)
    # a contact between susceptible classes (S₁ + I → S₂ + I) is not an entry into infection
    sus2 = mk(contacts = [C(:S1, :I, :I, :τ), C(:S1, :I, :S2, :α), C(:S2, :I, :I, :τ2)],
              transitions = [T(:I, :R, :γ)], susceptible = [:S1, :S2])
    @test Set(NEC.susceptible_species(sus2)) == Set([:S1, :S2]) &&
          default_seed_state(sus2) === :I
    @test default_seed(sus2, 0.01) == SeedFraction(:I => 0.01)   # two classes: no background
    # a model with no infection at all has no default
    notrans = mk(contacts = [C(:S, :D, :Q, :κ)], transitions = [T(:Q, :S, :ω)],
                 susceptible = [:S])
    err = try default_seed_state(notrans); nothing catch e; e end
    @test err isa ArgumentError && occursin("has no infection", err.msg)
    # a reinfection-counted model starts uninfected: the entry from the count-0 class (WP6
    # request to WP7), with that class as the background
    rc = NEC.with_reinfection_counting(NEC.sis_model(), 3)
    @test NEC.entry_species(rc) == [:I_1, :I_2, :I_3]
    @test default_seed_state(rc) === :I_1
    @test default_seed(rc, 0.01) == SeedFraction(:I_1 => 0.01; default = :S_0)
    @test seed_counts(default_seed(rc, 0.01), 1000) == [:I_1 => 10, :S_0 => 990]
    rc2 = NEC.with_reinfection_counting(NEC.sirs_model(), 2)
    @test default_seed_state(rc2) === :I_1
    rc0 = NEC.with_reinfection_counting(NEC.seir_model(), 1)
    @test default_seed_state(rc0) === :E_1
    # stratified models keep several entry states
    st = NEC.stratify(NEC.sir_model(), NEC.strata([:a, :b]))
    @test_throws ArgumentError default_seed_state(st)
end

@testset "canonical text" begin
    @test canonical_text(SeedFraction(:I => 0.01)) == "SeedFraction(fractions=[:I => 0.01], default=nothing)"
    @test canonical_text(SeedFraction(:I_a => 0.005, :I_b => 0.005; default = :S)) ==
          "SeedFraction(fractions=[:I_a => 0.0050000000000000001, :I_b => 0.0050000000000000001], default=:S)"
    @test canonical_text(SeedCount(:E => 50)) == "SeedCount(counts=[:E => 50], default=nothing)"
    @test canonical_text(SeedNodes(:I => [1, 17]; default = :S)) ==
          "SeedNodes(assignments=[:I => [1, 17]], default=:S)"
    @test canonical_text(SeedFraction(:I => 0.01)) == canonical_text(SeedFraction([:I => 1 // 100]))
    @test canonical_text(SeedFraction(:I => 0.01, :E => 0.02)) != canonical_text(SeedFraction(:E => 0.02, :I => 0.01))
end
