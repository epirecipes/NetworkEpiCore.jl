# Owner: WP7. Stretch descriptors (DESIGN §C.3, WP36): the degree-correlated (joint-degree)
# network with its support restriction (verified issue E20), dormant contacts and MFSH. Their
# lifts, samplers and processes come later; here the data, validation and summaries are tested.

using NetworkEpiCore, Test, LinearAlgebra

# ρ(C) with C[b, c] = (k_b − 1) Q(c | b), read off the multitype form through excess_contacts.
function degree_class_radius(net::DegreeCorrelatedNetwork)
    X = excess_contacts(MultitypeNetwork(net))
    C = [maximum(X[:, j, k]) for j in axes(X, 2), k in axes(X, 3)]
    return maximum(abs, eigvals(C))
end
newman_e(q, r) = [r * (i == j) * q[i] + (1 - r) * q[i] * q[j] for i in eachindex(q), j in eachindex(q)]

@testset "degree_correlated: bimodal {3, 7} with Newman r-mixing (E20)" begin
    p = zeros(8); p[4] = 0.5; p[8] = 0.5                          # P(3) = P(7) = 1/2, mean 5
    ρex(r) = 12 / 5 + 8r / 5 + 2sqrt(16r^2 - 27r + 36) / 5          # E20 sympy: support-block radius
    for r in (0.0, 0.3, 0.8, 1.0)
        e = zeros(8, 8)
        e[[4, 8], [4, 8]] .= newman_e([0.3, 0.7], r)                  # q_k = k pₖ/⟨k⟩
        net = degree_correlated(p, e)
        @test net.degrees == [3, 7]                                   # absent classes dropped
        @test net.probabilities == [0.5, 0.5]
        @test mean_degree(net) ≈ 5
        @test excess_degree(net) ≈ 4.8
        @test degree_class_radius(net) ≈ ρex(r) rtol = 1e-10
        @test degree_assortativity(net) ≈ r atol = 1e-10
        # zero-padding to K = 15 changes nothing (the spurious r(k − 1) eigenvalues are gone)
        ep = zeros(16, 16); ep[1:8, 1:8] .= e
        padded = degree_correlated(vcat(p, zeros(8)), ep)
        @test padded == net
        @test degree_class_radius(padded) ≈ ρex(r) rtol = 1e-10
        # the same through the keyword constructor
        @test degree_class_radius(degree_correlated(EmpiricalDegree(3 => 0.5, 7 => 0.5); r)) ≈ ρex(r) rtol = 1e-10
    end
    @test ρex(0.3) ≈ 5.0466564 rtol = 1e-7
    # R₀ never falls with assortativity in this family (E20)
    radii = [degree_class_radius(degree_correlated(EmpiricalDegree(3 => 0.5, 7 => 0.5); r)) for r in 0:0.1:1]
    @test all(diff(radii) .>= -1e-12)
end

@testset "degree_correlated: padded 2-regular stays a ring (E20)" begin
    for r in (0.0, 0.5, 1.0)
        net = degree_correlated(RegularDegree(2); r)
        @test net.degrees == [2]
        @test degree_class_radius(net) ≈ 1.0                          # T·ρ = T: a ring is critical at T = 1
        e = zeros(6, 6); e[3, 3] = 1.0
        @test degree_correlated([0, 0, 1.0, 0, 0, 0], e) == net
        @test isnan(degree_assortativity(net))                        # regular: r undefined
    end
end

@testset "degree_correlated: multitype form and validation" begin
    net = degree_correlated(PoissonDegree(3.0); r = 0.4, tol = 1e-10)
    @test all(>(0), net.probabilities)
    @test net.degrees[1] == 0                                         # isolated nodes are a class
    mt = MultitypeNetwork(net)                                        # reciprocity holds by symmetry
    @test mt.types[1:3] == [:k0, :k1, :k2]
    @test mt.sizes ≈ net.probabilities
    @test mt.degrees[1] == IndependentDegrees()
    @test mt.degrees[3].total == RegularDegree(2)
    @test mean_degree(mt) ≈ mean_degree(net)
    @test mean_degree(net) ≈ 3 rtol = 1e-8
    @test degree_assortativity(net) ≈ 0.4 rtol = 1e-8
    Q = mean_contacts(mt) ./ net.degrees                              # rows Q(· | k), k ≥ 1
    @test all(isapprox(sum(Q[i, :]), 1) for i in 2:length(net.degrees))
    # validation
    p = [0.0, 0.5, 0.5]
    bad = [0.0 0.0 0.0; 0.0 0.5 0.0; 0.0 0.0 0.5]                   # row sums 1/2, 1/2 ≠ 1/3, 2/3
    @test_throws ArgumentError degree_correlated(p, bad)              # marginal ≠ k pₖ/⟨k⟩
    q = [1 / 3, 2 / 3]
    e = zeros(3, 3); e[2:3, 2:3] .= newman_e(q, 0.2)
    @test degree_correlated(p, e) isa DegreeCorrelatedNetwork
    asym = copy(e); asym[2, 3] += 0.05; asym[3, 2] -= 0.05
    @test_throws ArgumentError degree_correlated(p, asym)
    ghost = copy(e); ghost[1, 2] = ghost[2, 1] = 0.01; ghost ./= sum(ghost)
    @test_throws ArgumentError degree_correlated(p, ghost)            # edges to an empty class
    @test_throws ArgumentError degree_correlated(p, zeros(2, 2))
    @test_throws ArgumentError degree_correlated(EmpiricalDegree(3 => 1.0), zeros(2, 2))
    @test_throws ArgumentError degree_correlated(EmpiricalDegree(1 => 0.5, 9 => 0.5); r = -0.9)
    # r > 1 names the upper bound (WP7 review: the message named only the lower bound)
    err = try degree_correlated(EmpiricalDegree(2 => 5 / 6, 10 => 1 / 6); r = 1.5); nothing catch e; e end
    @test err isa ArgumentError && occursin("≤ r ≤ 1", err.msg) && occursin("r = 1.5", err.msg)
    @test degree_correlated(EmpiricalDegree(2 => 5 / 6, 10 => 1 / 6); r = 1.0) isa DegreeCorrelatedNetwork
    @test_throws ArgumentError degree_correlated(EmpiricalDegree(2 => 5 / 6, 10 => 1 / 6); r = NaN)
    @test_throws ArgumentError DegreeCorrelatedNetwork([2, 1], [0.5, 0.5], [0.5 0; 0 0.5])
    @test_throws ArgumentError DegreeCorrelatedNetwork([0], [1.0], zeros(1, 1))   # no edges
end

@testset "DormantContacts" begin
    dc = DormantContacts(η_form = 1, η_break = 3)
    @test dc == DormantContacts(1.0, 3.0)
    @test dc.η_form === 1.0
    net = DynamicNetwork(RegularDegree(10), dc)
    @test mean_degree(net) ≈ 10 * 1 / 4                               # ξ⟨k_m⟩, ξ = η₁/(η₁ + η₂)
    @test mean_degree(DynamicNetwork(RegularDegree(10), DormantContacts(1e9, 1.0))) ≈ 10 rtol = 1e-8
    @test_throws ArgumentError DormantContacts(-1, 1)
    @test_throws ArgumentError DormantContacts(1, Inf)
    @test_throws ArgumentError DormantContacts(0, 0)
    @test net.process isa NetworkProcess
end

@testset "MFSHNetwork" begin
    m = MFSHNetwork(PoissonDegree(5))
    @test mean_degree(m) == 5.0
    @test m == MFSHNetwork(PoissonDegree(5.0))
    @test m != MFSHNetwork(RegularDegree(5))
    @test hash(MFSHNetwork(EmpiricalDegree([0, 1.0]))) == hash(MFSHNetwork(EmpiricalDegree(1 => 1.0)))
end
