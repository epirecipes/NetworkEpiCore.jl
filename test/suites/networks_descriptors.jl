# Owner: WP7. Network descriptors (DESIGN §C.2, §C.3): constructors, validation, summaries,
# reciprocity (the error lists the mismatches), structural zeros (E11), the typed-network
# constructors (E24), the clustering coefficient (E03) and the dynamic and multiplex descriptors.

using NetworkEpiCore, Test, LinearAlgebra
import Symbolics
const NEC = NetworkEpiCore

@testset "WellMixed and ConfigurationNetwork" begin
    @test mean_degree(WellMixed(5)) == 5.0
    @test WellMixed(5).κ isa Float64
    @test_throws ArgumentError WellMixed(0)
    @test_throws ArgumentError WellMixed(-1.0)
    Symbolics.@variables κ
    @test isequal(mean_degree(WellMixed(κ)), κ)
    net = ConfigurationNetwork(PoissonDegree(5))
    @test mean_degree(net) == 5.0
    @test excess_degree(net) == 5.0
    @test closure_constant(ConfigurationNetwork(RegularDegree(6))) ≈ 5 / 6
    @test is_poisson_type(ConfigurationNetwork(EmpiricalDegree(2 => 5 / 6, 10 => 1 / 6))) === nothing
    @test pgf(net, 0.5) == pgf(PoissonDegree(5), 0.5)
    @test pgf_derivative(net, 0.5, 2) == pgf_derivative(PoissonDegree(5), 0.5, 2)
    @test degree_probabilities(ConfigurationNetwork(RegularDegree(2))) == [0.0, 0.0, 1.0]
    @test clustering_coefficient(net) == 0.0
    @test ConfigurationNetwork(EmpiricalDegree([0, 1.0])) == ConfigurationNetwork(EmpiricalDegree(1 => 1.0))
    # the four E.2 anchors all have excess degree 5
    for d in (RegularDegree(6), PoissonDegree(5), NegBinDegree(mean = 4, var = 8),
              EmpiricalDegree(2 => 5 / 6, 10 => 1 / 6))
        @test excess_degree(ConfigurationNetwork(d)) ≈ 5 rtol = 1e-12
    end
end

@testset "MultitypeNetwork: reciprocity accepted" begin
    age = sbm_network([:y, :o], [0.4, 0.6]; mean_contacts = [6.0 3.0; 2.0 4.0])   # 0.4·3 == 0.6·2
    @test age isa MultitypeNetwork
    @test age.types == [:y, :o]
    @test age.sizes == [0.4, 0.6]
    @test mean_contacts(age) == [6.0 3.0; 2.0 4.0]
    @test isempty(structural_zeros(age))
    @test mean_degree(age) ≈ 0.4 * 9 + 0.6 * 6
    @test age.degrees[1] == IndependentDegrees(:y => PoissonDegree(6), :o => PoissonDegree(3))
    # the canonical SBM scenario: sizes ½/½, means [6 2; 2 4], ρ(M) = 5 + √5 = 7.236
    sbm = sbm_network([:a, :b], [0.5, 0.5]; mean_contacts = [6.0 2.0; 2.0 4.0])
    @test maximum(eigvals(Symmetric(mean_contacts(sbm)))) ≈ 5 + sqrt(5)
    # other families
    reg = sbm_network([:a, :b], [0.5, 0.5]; mean_contacts = [2.0 1.0; 1.0 3.0], family = RegularDegree)
    @test reg.degrees[2] == IndependentDegrees(:a => RegularDegree(1), :b => RegularDegree(3))
    nb = sbm_network([:a, :b], [0.5, 0.5]; mean_contacts = [2.0 1.0; 1.0 3.0],
                     family = m -> NegBinDegree(mean = m, var = 2m))
    @test mean_contacts(nb) ≈ [2.0 1.0; 1.0 3.0]
    @test_throws ArgumentError sbm_network([:a, :b], [0.5, 0.5]; mean_contacts = [2.5 1.0; 1.0 3.0],
                                           family = RegularDegree)
    # keyword and Dict forms
    m2 = MultitypeNetwork(; types = [:a, :b], sizes = [0.5, 0.5],
                          degrees = Dict(:a => IndependentDegrees(:b => PoissonDegree(2)),
                                         :b => IndependentDegrees(:a => PoissonDegree(2))))
    @test mean_contacts(m2) == [0.0 2.0; 2.0 0.0]
    # sizes are normalised
    @test MultitypeNetwork([:a], [1.0 + 1e-10], [IndependentDegrees(:a => PoissonDegree(3))]).sizes == [1.0]
end

@testset "MultitypeNetwork: reciprocity errors list the mismatches" begin
    err = try
        sbm_network([:y, :o], [0.5, 0.5]; mean_contacts = [6.0 3.0; 2.0 4.0])
        nothing
    catch e
        e
    end
    @test err isa ArgumentError
    @test occursin("edge reciprocity", err.msg)
    @test occursin("y ↔ o", err.msg)
    @test occursin("n_y·E[k_{y→o}] = 0.5 × 3 = 1.5", err.msg)
    @test occursin("n_o·E[k_{o→y}] = 0.5 × 2 = 1", err.msg)
    # three types, two bad pairs: both listed, the good one not
    three = try
        sbm_network([:a, :b, :c], [0.5, 0.25, 0.25]; mean_contacts = [1.0 1.0 1.0; 2.0 1.0 5.0; 3.0 1.0 1.0])
        nothing
    catch e
        e
    end
    @test three isa ArgumentError
    @test occursin("a ↔ c", three.msg) && occursin("b ↔ c", three.msg)
    @test !occursin("a ↔ b", three.msg)                          # 0.5·1 == 0.25·2
    # one-sided structural zero: no network realises it (E24 skeptic (c))
    one = try
        sbm_network([:a, :b], [0.5, 0.5]; mean_contacts = [4.0 0.0; 1.0 3.0])
        nothing
    catch e
        e
    end
    @test one isa ArgumentError && occursin("one-sided zero", one.msg)
    # ... also when the other side is tiny: exactly one side exactly 0 is refused whatever the
    # tolerance, so structural zeros stay symmetric (WP7 review: 1e-15 against 0 passed)
    tiny = try
        sbm_network([:a, :b], [0.5, 0.5]; mean_contacts = [4.0 1e-15; 0.0 3.0])
        nothing
    catch e
        e
    end
    @test tiny isa ArgumentError && occursin("one-sided zero", tiny.msg)
    # IndependentDegrees keeps its own copy of the parts (WP7 review: aliasing)
    parts = Pair{Symbol,DegreeDistribution}[:a => PoissonDegree(2.0)]
    ind = IndependentDegrees(parts)
    push!(parts, :a => PoissonDegree(1.0))
    @test length(ind.parts) == 1
    # the check can be skipped explicitly
    @test MultitypeNetwork([:a, :b], [0.5, 0.5],
                           [IndependentDegrees(:b => PoissonDegree(3)), IndependentDegrees(:a => PoissonDegree(2))];
                           check_reciprocity = false) isa MultitypeNetwork
    # symbolic means cannot be checked and are not
    Symbolics.@variables kab kba
    @test MultitypeNetwork([:a, :b], [0.5, 0.5],
                           [IndependentDegrees(:b => PoissonDegree(kab)), IndependentDegrees(:a => PoissonDegree(kba))]) isa
          MultitypeNetwork
end

@testset "MultitypeNetwork: structural zeros are recorded (E11)" begin
    bip = sbm_network([:a, :b], [1 / 3, 2 / 3]; mean_contacts = [0.0 4.0; 2.0 0.0])   # bipartite
    @test Set(structural_zeros(bip)) == Set([(:a, :a), (:b, :b)])
    @test bip.structural_zero == BitMatrix([1 0; 0 1])
    X = excess_contacts(bip)
    @test all(isfinite, X)                                      # no 0/0
    @test X[1, 1, :] == [0.0, 0.0] && X[2, 2, :] == [0.0, 0.0]
    @test X[1, 2, 1] ≈ 2.0                                       # Poisson: excess = mean
    @test X[2, 1, 2] ≈ 4.0
    diag = sbm_network([:a, :b], [0.5, 0.5]; mean_contacts = [3.0 0.0; 0.0 5.0])
    @test Set(structural_zeros(diag)) == Set([(:a, :b), (:b, :a)])
    @test mean_degree(MultitypeNetwork([:a, :b], [0.5, 0.5],
                                       [IndependentDegrees(:a => RegularDegree(0)), IndependentDegrees()])) == 0.0
end

@testset "MultitypeNetwork: validation" begin
    iA = IndependentDegrees(:a => PoissonDegree(1))
    @test_throws ArgumentError MultitypeNetwork(Symbol[], Float64[], MultivariateDegree[])
    @test_throws ArgumentError MultitypeNetwork([:a, :a], [0.5, 0.5], [iA, iA])
    @test_throws ArgumentError MultitypeNetwork([:a, :b], [0.5], [iA, iA])
    @test_throws ArgumentError MultitypeNetwork([:a, :b], [0.5, 0.5], [iA])
    @test_throws ArgumentError MultitypeNetwork([:a, :b], [0.6, 0.6], [iA, iA])
    @test_throws ArgumentError MultitypeNetwork([:a, :b], [1.0, 0.0], [iA, iA])
    @test_throws ArgumentError MultitypeNetwork([:a], [1.0], [IndependentDegrees(:z => PoissonDegree(1))])
    @test_throws ArgumentError MultitypeNetwork([:a, :b], [0.5, 0.5], Dict(:a => iA))
    @test_throws ArgumentError sbm_network([:a, :b], [0.5, 0.5]; mean_contacts = [1.0 2.0])
    @test_throws ArgumentError sbm_network([:a, :b], [0.5, 0.5]; mean_contacts = [1.0 -1.0; -1.0 1.0])
end

@testset "unstructured: types independent of the network (M10, E24)" begin
    base = ConfigurationNetwork(RegularDegree(6))
    un = unstructured(base, [:a, :b], [0.5, 0.5])
    @test un.degrees[1] == SplitDegrees(RegularDegree(6), :a => 0.5, :b => 0.5)
    @test mean_contacts(un) ≈ [3.0 3.0; 3.0 3.0]
    @test mean_degree(un) ≈ 6
    # thinning keeps the base degree law (not a Poisson with the same mean, E24)
    x = Dict(:a => 0.3, :b => 0.3)
    @test pgf(un.degrees[1], x) ≈ pgf(RegularDegree(6), 0.3)
    un3 = unstructured(ConfigurationNetwork(EmpiricalDegree(2 => 5 / 6, 10 => 1 / 6)), [:a, :b, :c], [0.2, 0.3, 0.5])
    M = mean_contacts(un3)
    n = un3.sizes
    @test all(isapprox(n[i] * M[i, j], n[j] * M[j, i]) for i in 1:3, j in 1:3)
    # excess contacts: w_c κ_ex for every (a, b)
    X = excess_contacts(un3)
    @test all(isapprox(X[i, j, k], n[k] * 5.0; rtol = 1e-12) for i in 1:3, j in 1:3, k in 1:3)
    @test unstructured(RegularDegree(6), [:a, :b], [0.5, 0.5]) == un
    @test_throws ArgumentError unstructured(base, [:a, :b], [0.5])
    @test_throws ArgumentError unstructured(base, [:a, :b], [0.5, -0.5])
end

@testset "sbm_network / unstructured over strata" begin
    age = strata([:y, :o]; sizes = [0.4, 0.6])
    net = sbm_network(age; mean_contacts = [6.0 3.0; 2.0 4.0], family = PoissonDegree)
    @test net == sbm_network([:y, :o], [0.4, 0.6]; mean_contacts = [6.0 3.0; 2.0 4.0])
    st = strata([:a, :b]; sizes = [0.5, 0.5])
    @test unstructured(ConfigurationNetwork(RegularDegree(6)), st) ==
          unstructured(ConfigurationNetwork(RegularDegree(6)), [:a, :b], [0.5, 0.5])
    @test unstructured(RegularDegree(6), st) == unstructured(ConfigurationNetwork(RegularDegree(6)), st)
    # the strata forms take a `Strata` (WP8), not anything with names and sizes (steward: the
    # duck-typed forms were narrowed once `Strata` existed)
    @test_throws MethodError sbm_network((; names = [:x], sizes = [1.0]); mean_contacts = [1.0;;])
    @test_throws MethodError unstructured(ConfigurationNetwork(RegularDegree(6)),
                                          (; names = [:a, :b], sizes = [0.5, 0.5]))
end

@testset "ClusteredNetwork: clustering coefficient = transitivity (E03)" begin
    net = ClusteredNetwork(RegularDegree(2), RegularDegree(2))
    @test clustering_coefficient(net) == 2 / 15                  # 2·E[t]/E[k(k−1)] = 4/30
    @test mean_degree(net) == 6.0
    @test excess_degree(net) ≈ 5.0
    # Poisson (κs, κt): C = 2κt/((κs + 2κt)² + 2κt) (E03 sympy)
    Cpois(ks, kt) = 2kt / ((ks + 2kt)^2 + 2kt)
    for (ks, kt) in ((3.0, 1.0), (1.0, 2.0), (0.5, 1.5), (2.0, 1.5), (4.0, 0.5))
        @test clustering_coefficient(ClusteredNetwork(PoissonDegree(ks), PoissonDegree(kt))) ≈ Cpois(ks, kt) rtol = 1e-12
        @test triangle_edge_fraction(ClusteredNetwork(PoissonDegree(ks), PoissonDegree(kt))) ≈ 2kt / (ks + 2kt) rtol = 1e-12
    end
    @test clustering_coefficient(ClusteredNetwork(PoissonDegree(3.0), PoissonDegree(1.0))) ≈ 2 / 27
    @test clustering_coefficient(ClusteredNetwork(PoissonDegree(1.0), PoissonDegree(2.0))) ≈ 4 / 29
    @test triangle_edge_fraction(ClusteredNetwork(PoissonDegree(3.0), PoissonDegree(1.0))) ≈ 0.4
    # fixed s = 2, t = 1 (k = 4): 1/6; joint table [0.1 0.2; 0.3 0.4]: 3/7; disjoint triangles: 1
    P = zeros(3, 2); P[3, 2] = 1.0
    @test clustering_coefficient(ClusteredNetwork(P)) ≈ 1 / 6
    @test clustering_coefficient(ClusteredNetwork([0.1 0.2; 0.3 0.4])) ≈ 3 / 7
    @test clustering_coefficient(ClusteredNetwork(reshape([0.0, 1.0], 1, 2))) ≈ 1.0
    @test clustering_coefficient(ClusteredNetwork(PoissonDegree(5.0), PoissonDegree(0.0))) == 0.0
    # C = p_t G'(1)/G''(1)
    for n in (ClusteredNetwork(PoissonDegree(2.0), PoissonDegree(1.5)), ClusteredNetwork([0.1 0.2; 0.3 0.4]))
        @test clustering_coefficient(n) ≈ triangle_edge_fraction(n) * mean_degree(n) / (excess_degree(n) * mean_degree(n))
    end
    # bivariate PGF and derivatives: matrix form ≡ independent form
    ind = ClusteredDegree(BinomialDegree(2, 0.5), BinomialDegree(1, 0.4))
    mat = ClusteredDegree([0.25 * 0.6 0.25 * 0.4; 0.5 * 0.6 0.5 * 0.4; 0.25 * 0.6 0.25 * 0.4])
    for (x, y) in ((0.3, 0.7), (1.0, 1.0)), i in 0:2, j in 0:2
        @test pgf_derivative(ind, x, y, i, j) ≈ pgf_derivative(mat, x, y, i, j) atol = 1e-14
    end
    @test pgf(mat, 0.3, 0.7) ≈ pgf(ind, 0.3, 0.7)
    @test clustering_coefficient(ind) ≈ clustering_coefficient(mat)
    # the degree PGF G(z) = g(z, z²): G'(1) = mean degree
    h = 1e-6
    G(z) = pgf(mat, z, z^2)
    @test (G(1 + h) - G(1 - h)) / (2h) ≈ mean_degree(mat) rtol = 1e-8
    h2 = 1e-4
    @test (G(1 + h2) - 2G(1) + G(1 - h2)) / h2^2 ≈ excess_degree(mat) * mean_degree(mat) rtol = 1e-6
    # validation
    @test_throws ArgumentError ClusteredDegree([0.5 0.4])
    @test_throws ArgumentError ClusteredDegree([-0.5 1.5])
    @test ClusteredDegree([0.5 0.5 0.0; 0.0 0.0 0.0]) == ClusteredDegree([0.5 0.5])
end

@testset "DynamicNetwork, NeighbourExchange, MultiplexNetwork" begin
    dyn = DynamicNetwork(RegularDegree(6), NeighbourExchange(1))
    @test dyn.base == ConfigurationNetwork(RegularDegree(6))
    @test dyn.process.η === 1.0
    @test mean_degree(dyn) == 6.0
    @test excess_degree(dyn) == 5.0
    @test NeighbourExchange(0).η == 0.0                          # η = 0: the static model
    @test_throws ArgumentError NeighbourExchange(-1)
    @test_throws ArgumentError NeighbourExchange(Inf)
    @test dyn == DynamicNetwork(ConfigurationNetwork(RegularDegree(6)), NeighbourExchange(1.0))
    mpx = MultiplexNetwork(:home => RegularDegree(3), :comm => ConfigurationNetwork(PoissonDegree(5)))
    @test layer_names(mpx) == [:home, :comm]
    @test mpx[:home] == ConfigurationNetwork(RegularDegree(3))
    @test mean_degree(mpx) == 8.0
    @test mean_degree(mpx, :comm) == 5.0
    @test mean_degree(mpx, :all) == 8.0
    @test_throws KeyError mpx[:work]
    @test_throws ArgumentError MultiplexNetwork(:home => RegularDegree(3), :home => RegularDegree(2))
    @test_throws ArgumentError MultiplexNetwork(:all => RegularDegree(3))
    @test_throws ArgumentError MultiplexNetwork(Pair{Symbol,ConfigurationNetwork}[])
    @test mpx == MultiplexNetwork([:home => ConfigurationNetwork(RegularDegree(3)), :comm => PoissonDegree(5)])
end

@testset "ExplicitGraph: generic container and validation hook" begin
    @test ExplicitGraph([1 => 2]).graph == [1 => 2]
    @test_throws ArgumentError ExplicitGraph(ConfigurationNetwork(RegularDegree(3)))
    @test_throws ArgumentError ExplicitGraph(PoissonDegree(3))
end
