# Owner: WP7. Multivariate degree laws (DESIGN §C.2): joint PGFs and partial derivatives against
# their definitions and finite differences, moments, sampling, validation.

using NetworkEpiCore, Test, Random, StableRNGs, Statistics
import Symbolics

const IND = IndependentDegrees(:a => PoissonDegree(3), :b => NegBinDegree(mean = 2, var = 5))
const SPL = SplitDegrees(EmpiricalDegree(2 => 5 / 6, 10 => 1 / 6), :a => 0.25, :b => 0.75)

@testset "joint pgf: definitions" begin
    x = Dict(:a => 0.3, :b => 0.8)
    @test pgf(IND, x) ≈ pgf(PoissonDegree(3), 0.3) * pgf(NegBinDegree(mean = 2, var = 5), 0.8)
    @test pgf(SPL, x) ≈ pgf(EmpiricalDegree(2 => 5 / 6, 10 => 1 / 6), 0.25 * 0.3 + 0.75 * 0.8)
    # NamedTuple and function arguments
    @test pgf(IND, (a = 0.3, b = 0.8)) == pgf(IND, x)
    @test pgf(SPL, b -> x[b]) == pgf(SPL, x)
    @test pgf(IND, Dict(:a => 1.0, :b => 1.0)) ≈ 1
    @test pgf(SPL, Dict(:a => 1.0, :b => 1.0)) ≈ 1
    @test pgf(IndependentDegrees(), x) == 1.0
    @test partner_types(IND) == [:a, :b]
    @test partner_types(SPL) == [:a, :b]
end

@testset "partial derivatives against finite differences" begin
    h = 1e-5
    x0 = Dict(:a => 0.4, :b => 0.7)
    shift(x, b, δ) = merge(x, Dict(b => x[b] + δ))
    for m in (IND, SPL)
        for b in (:a, :b)
            fd = (pgf(m, shift(x0, b, h)) - pgf(m, shift(x0, b, -h))) / (2h)
            @test pgf_derivative(m, x0, b) ≈ fd rtol = 1e-7
            for c in (:a, :b)
                fd2 = (pgf_derivative(m, shift(x0, c, h), b) - pgf_derivative(m, shift(x0, c, -h), b)) / (2h)
                @test pgf_derivative(m, x0, b, c) ≈ fd2 rtol = 1e-7
                @test pgf_derivative(m, x0, b, c) ≈ pgf_derivative(m, x0, c, b)
            end
        end
        @test pgf_derivative(m, x0) == pgf(m, x0)
        @test pgf_derivative(m, x0, :zz) == 0.0              # a type m does not mention
    end
    # SplitDegrees keeps the degree law: ∂_b∂_c ψ_a(1) = w_b w_c ψ''(1)
    ψ = EmpiricalDegree(2 => 5 / 6, 10 => 1 / 6)
    @test pgf_derivative(SPL, Dict(:a => 1.0, :b => 1.0), :a, :b) ≈ 0.25 * 0.75 * pgf_derivative(ψ, 1.0, 2)
end

@testset "moments" begin
    @test mean_degree(IND, :a) ≈ 3
    @test mean_degree(IND, :b) ≈ 2
    @test mean_degree(IND, :c) == 0.0
    @test mean_degree(IND) ≈ 5
    @test mean_degree(SPL, :a) ≈ 0.25 * 10 / 3
    @test mean_degree(SPL, :b) ≈ 0.75 * 10 / 3
    @test mean_degree(SPL) ≈ 10 / 3
    @test mean_degree(IndependentDegrees()) == 0.0
    # symbolic parameters stay exact
    Symbolics.@variables κab κbb
    m = IndependentDegrees(:a => PoissonDegree(κab), :b => PoissonDegree(κbb))
    @test isequal(mean_degree(m, :a), κab)
end

@testset "rand: counts per partner type" begin
    rng = StableRNG(7)
    n = 100_000
    draws = [rand(rng, IND) for _ in 1:n]
    @test all(d -> length(d) == 2, draws)
    @test abs(mean(first.(draws)) - 3) <= 4 * sqrt(3 / n)
    @test abs(mean(last.(draws)) - 2) <= 4 * sqrt(5 / n)
    @test abs(cor(first.(draws), last.(draws))) <= 4 / sqrt(n)             # independent
    sdraws = [rand(rng, SPL) for _ in 1:n]
    tot = sum.(sdraws)
    ψ = EmpiricalDegree(2 => 5 / 6, 10 => 1 / 6)
    @test all(t -> t in (2, 10), tot)                                        # degree law kept
    @test abs(mean(tot .== 10) - 1 / 6) <= 4 * sqrt(1 / 6 * 5 / 6 / n)
    # multinomial split: E[k_a | k] = w_a k
    ka10 = [d[1] for d in sdraws if sum(d) == 10]
    @test abs(mean(ka10) - 2.5) <= 4 * sqrt(10 * 0.25 * 0.75 / length(ka10))
    z = SplitDegrees(RegularDegree(4), :a => 1.0, :b => 0.0)
    @test all(rand(rng, z) == [4, 0] for _ in 1:100)                          # zero weight ⇒ 0 edges
end

@testset "validation and equality" begin
    @test_throws ArgumentError IndependentDegrees(:a => PoissonDegree(1), :a => PoissonDegree(2))
    @test_throws ArgumentError SplitDegrees(PoissonDegree(3), :a => 0.5, :a => 0.5)
    @test_throws ArgumentError SplitDegrees(PoissonDegree(3), :a => 0.5, :b => 0.4)
    @test_throws ArgumentError SplitDegrees(PoissonDegree(3), :a => -0.5, :b => 1.5)
    @test_throws ArgumentError SplitDegrees(PoissonDegree(3))
    @test SplitDegrees(RegularDegree(0)) isa SplitDegrees                     # no edges, no partners
    @test SplitDegrees(RegularDegree(3), :a => 1, :b => 1 // 1 - 1) == SplitDegrees(RegularDegree(3), [:a => 1.0, :b => 0.0])
    @test IND == IndependentDegrees([:a => PoissonDegree(3), :b => NegBinDegree(mean = 2, var = 5)])
    @test hash(IND) == hash(IndependentDegrees([:a => PoissonDegree(3), :b => NegBinDegree(mean = 2, var = 5)]))
    @test SPL != SplitDegrees(EmpiricalDegree(2 => 5 / 6, 10 => 1 / 6), :a => 0.75, :b => 0.25)
end
