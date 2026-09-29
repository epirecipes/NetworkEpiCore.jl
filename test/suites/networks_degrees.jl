# Owner: WP7. Degree distributions (DESIGN §C.1): PGFs and derivatives against the power series
# Σ pₖ xᵏ, against finite differences and against symbolic differentiation; probabilities
# against Distributions.jl; moments; the Poisson-type test; sampling moments; validation.

using NetworkEpiCore, Test, Random, StableRNGs, Statistics
import Distributions, Symbolics

const FAMILIES = [
    "Poisson(5)" => PoissonDegree(5),
    "Poisson(0.7)" => PoissonDegree(0.7),
    "Regular(6)" => RegularDegree(6),
    "Regular(1)" => RegularDegree(1),
    "Binomial(10, 0.3)" => BinomialDegree(10, 0.3),
    "NegBin(mean 4, var 8)" => NegBinDegree(mean = 4, var = 8),
    "NegBin(2.5, 0.3)" => NegBinDegree(2.5, 0.3),
    "Geometric(3)" => GeometricDegree(3),
    "PowerLaw(2.5; 2..60)" => PowerLawDegree(2.5; kmin = 2, kmax = 60),
    "Empirical {2: 5/6, 10: 1/6}" => EmpiricalDegree(2 => 5 / 6, 10 => 1 / 6),
    "Mixture Poisson/NegBin" => MixtureDegree(0.3 => PoissonDegree(2), 0.7 => NegBinDegree(3.0, 0.4)),
    "Mixture Regular/Empirical" => MixtureDegree([0.5, 0.5], [RegularDegree(3), EmpiricalDegree([0.2, 0.3, 0.5])]),
]

# Independent reference probabilities p[k+1], k = 0:K (Distributions.jl or the definition).
function reference_pmf(d, K)
    ks = 0:K
    if d isa PoissonDegree
        return Distributions.pdf.(Distributions.Poisson(d.mean), ks)
    elseif d isa RegularDegree
        return [k == d.k ? 1.0 : 0.0 for k in ks]
    elseif d isa BinomialDegree
        return Distributions.pdf.(Distributions.Binomial(d.n, d.p), ks)
    elseif d isa NegBinDegree
        return Distributions.pdf.(Distributions.NegativeBinomial(d.r, d.p), ks)
    elseif d isa PowerLawDegree
        w = [d.kmin <= k <= d.kmax ? float(k)^(-d.α) : 0.0 for k in ks]
        return w ./ sum(float(k)^(-d.α) for k in d.kmin:d.kmax)
    elseif d isa EmpiricalDegree
        return [k + 1 <= length(d.p) ? d.p[k + 1] : 0.0 for k in ks]
    elseif d isa MixtureDegree
        return sum(w .* reference_pmf(c, K) for (w, c) in zip(d.weights, d.components))
    end
    error("no reference for $d")
end
const KREF = 400
falling(k, n) = n == 0 ? 1.0 : prod(float(k - i) for i in 0:(n - 1))
series(p, x, n) = sum(p[j] * falling(j - 1, n) * x^(j - 1 - n) for j in eachindex(p) if j - 1 >= n; init = 0.0)

@testset "pgf and derivatives agree with the power series Σ pₖ xᵏ" begin
    for (name, d) in FAMILIES
        p = reference_pmf(d, KREF)
        @test sum(p) ≈ 1 atol = 1e-12
        for x in (0.0, 0.25, 0.5, 0.9, 1.0), n in 0:4
            ref = series(p, x, n)
            val = n == 0 ? pgf(d, x) : pgf_derivative(d, x, n)
            @test isapprox(val, ref; rtol = 1e-10, atol = 1e-12)
        end
        @test pgf(d, 1.0) ≈ 1 atol = 1e-12
        @test pgf_derivative(d, 0.4, 0) == pgf(d, 0.4)
    end
end

@testset "derivatives agree with central finite differences (rtol 1e-7)" begin
    h = 1e-5
    for (name, d) in FAMILIES, x in (0.2, 0.5, 0.9), n in 1:4
        lower(y) = n == 1 ? pgf(d, y) : pgf_derivative(d, y, n - 1)
        fd = (lower(x + h) - lower(x - h)) / (2h)
        @test isapprox(pgf_derivative(d, x, n), fd; rtol = 1e-7, atol = 1e-9)
    end
end

@testset "derivatives agree with symbolic differentiation (generic in x)" begin
    Symbolics.@variables x
    for (name, d) in FAMILIES
        ψ = pgf(d, x)
        dψ = ψ
        for n in 1:3
            dψ = Symbolics.expand_derivatives(Symbolics.Differential(x)(dψ))
            closed = pgf_derivative(d, x, n)
            for xv in (0.1, 0.6)
                a = Symbolics.value(Symbolics.substitute(dψ, Dict(x => xv); fold = Val(true)))
                b = Symbolics.value(Symbolics.substitute(closed, Dict(x => xv); fold = Val(true)))
                @test isapprox(Float64(a), Float64(b); rtol = 1e-10, atol = 1e-12)
            end
        end
    end
end

@testset "symbolic parameters give exact closed forms" begin
    Symbolics.@variables μ x r q
    d = PoissonDegree(μ)
    @test isequal(pgf(d, x), exp(μ * (x - 1)))
    @test isequal(mean_degree(d), μ)
    @test isequal(excess_degree(d), μ)
    @test closure_constant(d) == 1.0
    @test isequal(is_poisson_type(d).α, μ) && is_poisson_type(d).κ == 1.0
    nb = NegBinDegree(r, q)
    mnb = Symbolics.substitute(mean_degree(nb), Dict(r => 4.0, q => 0.5); fold = Val(true))
    @test Float64(Symbolics.value(mnb)) ≈ 4.0
    knb = Symbolics.substitute(is_poisson_type(nb).κ, Dict(r => 4.0); fold = Val(true))
    @test Float64(Symbolics.value(knb)) ≈ 1.25
    e = pgf(EmpiricalDegree(2 => 5 / 6, 10 => 1 / 6), x)
    @test Float64(Symbolics.value(Symbolics.substitute(e, Dict(x => 0.5); fold = Val(true)))) ≈
          5 / 6 * 0.25 + 1 / 6 * 0.5^10
end

@testset "degree_probabilities against Distributions.jl" begin
    for (name, d) in FAMILIES
        p = degree_probabilities(d)
        ref = reference_pmf(d, length(p) - 1)
        @test p ≈ ref atol = 1e-13
        @test 1 - sum(p) <= 1e-12
        @test p[end] > 0                                     # no trailing zeros
        q = degree_probabilities(d; kmax = 80)
        @test length(q) == 81
        @test q ≈ reference_pmf(d, 80) atol = 1e-13
    end
    @test degree_probabilities(PoissonDegree(5); tol = 1e-6) |> p -> 1 - sum(p) <= 1e-6
    @test degree_probabilities(RegularDegree(3)) == [0.0, 0.0, 0.0, 1.0]
    @test degree_probabilities(BinomialDegree(4, 1.0)) == [0.0, 0.0, 0.0, 0.0, 1.0]
    @test degree_probabilities(PoissonDegree(0.0)) == [1.0]
    @test degree_probabilities(PoissonDegree(900.0)) ≈ reference_pmf(PoissonDegree(900.0),
                                                                    length(degree_probabilities(PoissonDegree(900.0))) - 1) atol = 1e-13
    @test degree_probabilities(NegBinDegree(mean = 4, var = 8))[1] ≈ 0.0625
    @test_throws ArgumentError degree_probabilities(PoissonDegree(5); tol = 0)
    Symbolics.@variables μ
    @test_throws ArgumentError degree_probabilities(PoissonDegree(μ))
end

@testset "moments" begin
    # (mean, excess, closure constant) from the definitions; the E.2 anchors have excess 5.
    known = [
        PoissonDegree(5) => (5.0, 5.0, 1.0),
        RegularDegree(6) => (6.0, 5.0, 5 / 6),
        NegBinDegree(mean = 4, var = 8) => (4.0, 5.0, 5 / 4),
        EmpiricalDegree(2 => 5 / 6, 10 => 1 / 6) => (10 / 3, 5.0, 3 / 2),
        BinomialDegree(10, 0.3) => (3.0, 2.7, 0.9),
        GeometricDegree(3) => (3.0, 6.0, 2.0),
    ]
    for (d, (m, ex, K)) in known
        @test mean_degree(d) ≈ m rtol = 1e-12
        @test excess_degree(d) ≈ ex rtol = 1e-12
        @test closure_constant(d) ≈ K rtol = 1e-12
    end
    pl = PowerLawDegree(2.5; kmin = 2, kmax = 60)
    @test mean_degree(pl) ≈ 3.9851951500582476 rtol = 1e-12        # numpy, from the definition
    @test excess_degree(pl) ≈ 8.663206165912431 rtol = 1e-12
    @test closure_constant(pl) ≈ excess_degree(pl) / mean_degree(pl) rtol = 1e-12
    for (name, d) in FAMILIES
        p = reference_pmf(d, KREF)
        for j in 0:4
            @test degree_moment(d, j) ≈ sum(p[k + 1] * float(k)^j for k in 0:KREF) rtol = 1e-10
        end
        @test excess_degree(d) ≈ (degree_moment(d, 2) - degree_moment(d, 1)) / degree_moment(d, 1) rtol = 1e-10
    end
    @test degree_moment(PoissonDegree(5), 3) ≈ 125 + 3 * 25 + 5
    @test_throws ArgumentError excess_degree(PoissonDegree(0))
    @test_throws ArgumentError closure_constant(RegularDegree(0))
    @test_throws ArgumentError degree_moment(PoissonDegree(1), -1)
end

@testset "is_poisson_type" begin
    pt(d) = is_poisson_type(d)
    @test pt(PoissonDegree(5)) == (α = 5.0, κ = 1.0)
    @test pt(BinomialDegree(10, 0.3)).α ≈ 3.0 && pt(BinomialDegree(10, 0.3)).κ ≈ 0.9
    @test pt(RegularDegree(6)) == (α = 6.0, κ = 5 / 6)
    @test pt(NegBinDegree(mean = 4, var = 8)).α ≈ 4.0 && pt(NegBinDegree(mean = 4, var = 8)).κ ≈ 1.25
    @test pt(GeometricDegree(3)).κ ≈ 2.0
    @test pt(EmpiricalDegree(2 => 5 / 6, 10 => 1 / 6)) === nothing          # bimodal
    @test pt(PowerLawDegree(2.5; kmin = 2, kmax = 60)) === nothing           # power law
    @test pt(MixtureDegree(0.5 => PoissonDegree(2), 0.5 => PoissonDegree(8))) === nothing
    # the numeric test recognises hidden PT laws
    bin = EmpiricalDegree(Distributions.pdf.(Distributions.Binomial(10, 0.3), 0:10))
    @test pt(bin).κ ≈ 0.9 rtol = 1e-9
    @test pt(bin).α ≈ 3.0 rtol = 1e-12
    @test pt(EmpiricalDegree(6 => 1.0)).κ ≈ 5 / 6
    @test pt(PowerLawDegree(2.5, 4, 4)).κ ≈ 3 / 4
    @test pt(MixtureDegree([1.0], [PoissonDegree(3)])).κ ≈ 1.0 rtol = 1e-9
    # degenerate: no edges
    @test pt(PoissonDegree(0)) === nothing
    @test pt(RegularDegree(0)) === nothing
    # the PT identity ψ' = α ψ^κ and κ = closure constant, for every PT answer
    for (name, d) in FAMILIES
        r = pt(d)
        r === nothing && continue
        @test r.κ ≈ closure_constant(d) rtol = 1e-12
        for x in (0.05, 0.37, 0.81)
            @test pgf_derivative(d, x, 1) ≈ r.α * pgf(d, x)^r.κ rtol = 1e-10
        end
    end
    @test pt(ConfigurationNetwork(RegularDegree(3))).κ ≈ 2 / 3
end

@testset "rand: moments within 4 SE (10⁵ draws)" begin
    ndraw = 100_000
    rng = StableRNG(20260926)
    extra = ["Poisson(800) (split)" => PoissonDegree(800.0),
             "NegBin(r = 2000, p = 1/2) (split)" => NegBinDegree(2000.0, 0.5),
             "Binomial(5000, 0.7) (chunks, p > 1/2)" => BinomialDegree(5000, 0.7)]
    for (name, d) in vcat(FAMILIES, extra)
        K = max(KREF, round(Int, mean_degree(d) + 60 * sqrt(max(1.0, degree_moment(d, 2) - mean_degree(d)^2))))
        p = reference_pmf(d, K)
        m1 = sum(p[k + 1] * k for k in 0:K)
        c2 = sum(p[k + 1] * (k - m1)^2 for k in 0:K)
        c4 = sum(p[k + 1] * (k - m1)^4 for k in 0:K)
        xs = rand(rng, d, ndraw)
        @test eltype(xs) == Int
        @test abs(mean(xs) - m1) <= 4 * sqrt(c2 / ndraw) + 1e-12
        @test abs(var(xs) - c2) <= 4 * sqrt(max(c4 - c2^2, 0.0) / ndraw) + 1e-12
        @test all(x -> p[x + 1] > 0, xs)                     # never a zero-probability degree
    end
    @test rand(StableRNG(1), RegularDegree(4)) == 4
    @test rand(StableRNG(1), PoissonDegree(3)) isa Int
    @test length(rand(PoissonDegree(3), 7)) == 7
    @test rand(StableRNG(3), PoissonDegree(5), 10) == rand(StableRNG(3), PoissonDegree(5), 10)
    @test_throws ArgumentError rand(StableRNG(1), PoissonDegree(3), -1)
end

@testset "validation" begin
    @test_throws ArgumentError PoissonDegree(-1)
    @test_throws ArgumentError PoissonDegree(NaN)
    @test_throws ArgumentError PoissonDegree(Inf)
    @test_throws ArgumentError RegularDegree(-1)
    @test_throws ArgumentError RegularDegree(2.5)
    @test RegularDegree(6.0) == RegularDegree(6)
    @test_throws ArgumentError BinomialDegree(-1, 0.5)
    @test_throws ArgumentError BinomialDegree(3, 1.2)
    @test_throws ArgumentError NegBinDegree(0, 0.5)
    @test_throws ArgumentError NegBinDegree(1, 0)
    @test_throws ArgumentError NegBinDegree(mean = 4, var = 4)
    @test_throws ArgumentError NegBinDegree(mean = 4, var = 3)
    @test_throws ArgumentError GeometricDegree(-1)
    @test_throws ArgumentError PowerLawDegree(2.5; kmin = 0, kmax = 10)
    @test_throws ArgumentError PowerLawDegree(2.5; kmin = 5, kmax = 4)
    @test_throws ArgumentError PowerLawDegree(Inf, 1, 3)
    @test_throws ArgumentError EmpiricalDegree([0.5, 0.4])
    @test_throws ArgumentError EmpiricalDegree([-0.1, 1.1])
    @test_throws ArgumentError EmpiricalDegree(Float64[])
    @test_throws ArgumentError EmpiricalDegree(Dict(-1 => 1.0))
    @test_throws ArgumentError EmpiricalDegree(2 => 0.5, 2 => 0.5)
    @test_throws ArgumentError MixtureDegree([0.5], [PoissonDegree(1), PoissonDegree(2)])
    @test_throws ArgumentError MixtureDegree([0.6, 0.6], [PoissonDegree(1), PoissonDegree(2)])
    @test_throws ArgumentError pgf_derivative(PoissonDegree(1), 0.5, -1)
    # normalisation and equality
    @test EmpiricalDegree([0, 0, 1, 0]) == EmpiricalDegree(2 => 1.0)
    @test hash(EmpiricalDegree([0, 0, 1, 0])) == hash(EmpiricalDegree(2 => 1.0))
    @test EmpiricalDegree(Dict(2 => 5 / 6, 10 => 1 / 6)) == EmpiricalDegree(2 => 5 / 6, 10 => 1 / 6)
    @test PoissonDegree(5) == PoissonDegree(5.0)
    @test PoissonDegree(5).mean isa Float64
    @test MixtureDegree(0.5 => PoissonDegree(1), 0.5 => RegularDegree(2)) ==
          MixtureDegree([0.5, 0.5], [PoissonDegree(1), RegularDegree(2)])
    @test NegBinDegree(mean = 4, var = 8) == NegBinDegree(4.0, 0.5)
end
