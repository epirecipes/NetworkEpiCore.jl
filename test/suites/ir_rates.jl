# Owner: WP6. Rates (DESIGN §B.1, §B.6): validation, the Expr interpreter over RATE_OPS, rate
# arithmetic, parameters, instantiate, rate conventions and the endofunctor c_λ.

using NetworkEpiCore
const NEC = NetworkEpiCore

@testset "RATE_OPS interpreter" begin
    p = Dict(:a => 2.0, :b => 0.5, :c => 3.0)
    @test RATE_OPS == (:+, :-, :*, :/, :^, :exp, :log, :min, :max)
    @test rate_value(0.25, p) === 0.25
    @test rate_value(3, p) === 3
    @test rate_value(:a, p) == 2.0
    @test rate_value(:(a + b + c), p) ≈ 5.5
    @test rate_value(:(a - b), p) ≈ 1.5
    @test rate_value(:(-a), p) ≈ -2.0
    @test rate_value(:(a * b * c), p) ≈ 3.0
    @test rate_value(:(a / c), p) ≈ 2 / 3
    @test rate_value(:(a^c), p) ≈ 8.0
    @test rate_value(:(exp(b)), p) ≈ exp(0.5)
    @test rate_value(:(log(c)), p) ≈ log(3.0)
    @test rate_value(:(min(a, b, c)), p) ≈ 0.5
    @test rate_value(:(max(a, b)), p) ≈ 2.0
    @test rate_value(:((1 - b) * a / (c + 1)^2), p) ≈ (1 - 0.5) * 2 / 16
    @test rate_value(:(3a), p) ≈ 6.0
    # an integer base with a negative integer exponent is a real power, not Julia's DomainError
    # for Int^negative Int (WP6 review)
    @test rate_value(:(2^(-1) * a), p) == 1.0
    @test rate_value(:(N^-1), Dict(:N => 4)) == 0.25
    @test rate_value(:(N^2), Dict(:N => 3)) === 9
    # time: only through the keyword t
    @test rate_value(:(a * exp(-b * t)), p; t = 2.0) ≈ 2 * exp(-1.0)
    @test rate_value(:t, p; t = 1.5) == 1.5
    @test_throws ArgumentError rate_value(:(a * t), p)
    # missing parameter, invalid operators and leaves
    err = try
        rate_value(:(a * d), p)
    catch e
        e
    end
    @test err isa ArgumentError && occursin("no value for the parameter d", err.msg)
    @test_throws ArgumentError rate_value(:(sin(a)), p)
    @test_throws ArgumentError rate_value(:(a[1]), p)
    @test_throws ArgumentError rate_value(:(a > b ? a : b), p)
    @test_throws ArgumentError rate_value(:(a .+ b), p)
    @test_throws ArgumentError rate_value(:(exp(a, b)), p)
    @test rate_value(:((a / b) / c), p) ≈ 4 / 3
    @test_throws ArgumentError rate_value(sin, p)             # Functions are rejected
    @test_throws ArgumentError rate_value("a", p)
    # generic in the number type
    @test rate_value(:(a * b), Dict(:a => 2 // 3, :b => 3)) == 2 // 1
    @test rate_value(:(a * b), Dict{Symbol,Any}(:a => big"2.0", :b => 1)) isa BigFloat
end

@testset "rate validation in reactions" begin
    # an infinite rate gives NaN in the ODE back ends and a Bool is not a rate: both are refused
    # since the NEC steward's change (WP6 review), in a rate and as a leaf of an Expr rate
    for bad in (:(sin(τ)), :(f(τ)), :(τ[1]), :(τ.x), :(τ; γ), :(τ == γ), :(τ && γ),
                :(exp(τ, γ)), :((τ, γ)), "τ", sin, x -> x, [1.0], (1, 2), Inf, -Inf, NaN, true,
                Expr(:call, :*, Inf, :τ), Expr(:call, :+, :τ, NaN), Expr(:call, :*, true, :τ))
        @test_throws ArgumentError Contact(:S, :I, :I, bad)
    end
    for good in (0, 0.0, 1 // 3, 1e300, :τ, :(2τ), :((1 - p) * σ), :(τ0 * exp(-a * t)),
                 :(min(τ, 1)), :(max(τ, γ, 0.1)), :(τ / N), :(-(-τ)), :(log(1 + τ)))
        @test Contact(:S, :I, :I, good).rate == good
    end
end

@testset "rate arithmetic" begin
    @test rate_mul(2, 3) == 6
    @test rate_mul(1, :γ) === :γ && rate_mul(:γ, 1) === :γ
    @test rate_mul(0, :γ) == 0
    @test rate_mul(3, :γ) == :(3 * γ)
    @test rate_mul(3, :(2 * γ)) == :(6 * γ)
    @test rate_mul(:ε, :τ2) == :(ε * τ2)
    @test rate_mul(:(ε * τ), :μ) == :(ε * τ * μ)
    @test rate_mul(:μ, :(2 * γ)) == :(2 * μ * γ)
    @test rate_mul(:(1 - p), :σ) == :((1 - p) * σ)
    @test rate_add(0.1, 0.2) ≈ 0.3
    @test rate_add(0, :γ) === :γ && rate_add(:γ, 0) === :γ
    @test rate_add(:γ, :μ) == :(γ + μ)
    @test rate_add(:(γ + μ), :ν) == :(γ + μ + ν)
    @test rate_div(1.0, 4) == 0.25
    @test rate_div(:β, 1) === :β
    @test rate_div(:β, 5.0) == :(β / 5.0)
    @test rate_div(:β, :N) == :(β / N)
    @test_throws ArgumentError rate_mul(sin, :γ)
    p = Dict(:γ => 0.2, :μ => 0.05, :β => 0.5, :N => 10.0, :σ => 0.3, :p => 0.25)
    @test rate_value(rate_mul(3, rate_add(:γ, :μ)), p) ≈ 0.75
    @test rate_value(rate_div(rate_mul(:β, :N), 5.0), p) ≈ 1.0
    @test rate_value(rate_mul(NEC._rate_sub(1, :p), :σ), p) ≈ 0.225
end

@testset "rate printing (RN style)" begin
    rs = NEC._rate_string
    @test rs(:τ) == "τ"
    @test rs(0.25) == "0.25" && rs(3.0) == "3" && rs(2) == "2"
    @test rs(:(ε * τ2)) == "ε*τ2"
    @test rs(:((1 - p) * σ)) == "(1 - p)*σ"
    @test rs(:(3 * γ)) == "3γ"
    @test rs(rate_mul(3, :γ)) == "3γ"
    @test rs(:(β / N)) == "β/N"
    @test rs(:(β * S * I / (1 + a * I))) == "β*S*I/(1 + a*I)"
    @test rs(:(τ0 * exp(-a * t))) == "τ0*exp(-a*t)"
    @test rs(:(a - (b + c))) == "a - (b + c)"
    @test rs(:((a + b)^2)) == "(a + b)^2"
    @test rs(:(a / (b * c))) == "a/(b*c)"
    @test rs(:(min(a, b))) == "min(a, b)"
end

@testset "rate_parameters" begin
    @test rate_parameters(0.3) == Symbol[]
    @test rate_parameters(:τ) == [:τ]
    @test rate_parameters(:t) == Symbol[]
    @test rate_parameters(:(ε * τ2 + ε)) == [:ε, :τ2]
    @test rate_parameters(:(τ0 * exp(-a * t))) == [:τ0, :a]           # time is not a parameter
    @test_throws ArgumentError rate_parameters(sin)
    cm = ContactModel(:x; contacts = [Contact(:S, :I, :I, :(τ * c))],
                      transitions = [NodeTransition(:I, :R, :γ), NodeTransition(:R, :S, :(c * ε))],
                      convention = DensityDependent(:N))
    @test rate_parameters(cm) == Any[:τ, :c, :γ, :ε, :N]
end

@testset "instantiate" begin
    cm = ContactModel(:seir; contacts = [Contact(:S, :I, :E, :τ)],
                      transitions = [NodeTransition(:E, :I, :σ), NodeTransition(:I, :R, :(2γ))],
                      defaults = Dict(:σ => 0.2))
    m = instantiate(cm, Dict(:τ => 0.5, :γ => 0.125))
    @test [c.rate for c in contacts(m)] == [0.5]
    @test [t.rate for t in node_transitions(m)] == [0.2, 0.25]      # σ from the defaults
    @test all(r -> r isa Float64, [t.rate for t in node_transitions(m)])
    @test isempty(rate_parameters(m))
    @test species_names(m) == species_names(cm) && susceptible_species(m) == [:S]
    @test instantiate(cm, Dict(:τ => 0.5, :γ => 1, :σ => 0.3)).transitions[1].rate == 0.3  # p wins
    err = try
        instantiate(cm, Dict(:τ => 0.5))
    catch e
        e
    end
    @test err isa ArgumentError
    @test err.msg == "instantiate(:seir): missing parameter values for γ (pass them in p or set " *
                     "model defaults)"
    err2 = try
        instantiate(ContactModel(:x; contacts = [Contact(:S, :I, :I, :τ)],
                                 transitions = [NodeTransition(:I, :R, :(γ + μ))]), Dict())
    catch e
        e
    end
    @test err2 isa ArgumentError && occursin("missing parameter values for τ, γ, μ", err2.msg)
    neg = ContactModel(:x; contacts = [Contact(:S, :I, :I, :(τ - 1))])
    @test_throws ArgumentError instantiate(neg, Dict(:τ => 0.5))
    tdep = ContactModel(:x; contacts = [Contact(:S, :I, :I, :(τ * exp(-t)))])
    err3 = try
        instantiate(tdep, Dict(:τ => 0.5))
    catch e
        e
    end
    @test err3 isa ArgumentError && occursin("depends on time t", err3.msg)
    dd = ContactModel(:x; contacts = [Contact(:S, :I, :I, :β)], convention = DensityDependent(:N))
    @test_throws ArgumentError instantiate(dd, Dict(:β => 0.001))
    mdd = instantiate(dd, Dict(:β => 0.001, :N => 1000))
    @test rate_convention(mdd) == DensityDependent(1000.0)
end

@testset "per_contact_rates and scale_contact_rates" begin
    cm = ContactModel(:x; contacts = [Contact(:S, :I, :I, :τ), Contact(:S, :A, :I, 0.1)],
                      transitions = [NodeTransition(:I, :R, :γ), NodeTransition(:A, :R, :γ)])
    @test per_contact_rates(cm) == Any[:τ, 0.1]                     # PerContact: no network
    fd = ContactModel(:x; contacts = [Contact(:S, :I, :I, :β)], convention = FrequencyDependent())
    @test_throws ArgumentError per_contact_rates(fd)                # needs ⟨k⟩
    sc = scale_contact_rates(cm, 5)
    @test [c.rate for c in contacts(sc)] == Any[:(5τ), 0.5]
    @test node_transitions(sc) == node_transitions(cm)
    @test rate_parameters(scale_contact_rates(cm, :κ)) == Any[:κ, :τ, :γ]
    @test provenance(sc).source === :transform
end
