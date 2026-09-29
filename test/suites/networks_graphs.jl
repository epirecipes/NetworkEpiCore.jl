# Owner: WP7. NetworkEpiCoreGraphsExt (DESIGN §A.2, §C.1): EmpiricalDegree(g), ExplicitGraph
# queries and canonical text; and the E03 regression: the clustering coefficient of a
# ClusteredNetwork equals the transitivity of Newman–Miller graphs sampled from it.

using NetworkEpiCore, Test, Graphs, StableRNGs, Random, Statistics

@testset "EmpiricalDegree(g)" begin
    g = star_graph(5)                                            # centre degree 4, leaves degree 1
    @test EmpiricalDegree(g) == EmpiricalDegree(1 => 0.8, 4 => 0.2)
    @test EmpiricalDegree(ExplicitGraph(g)) == EmpiricalDegree(g)
    @test EmpiricalDegree(cycle_graph(7)) == EmpiricalDegree(2 => 1.0)
    @test EmpiricalDegree(SimpleGraph(3)) == EmpiricalDegree(0 => 1.0)
    @test_throws ArgumentError EmpiricalDegree(SimpleDiGraph(3))
    @test_throws ArgumentError EmpiricalDegree(SimpleGraph(0))
    rr = random_regular_graph(200, 4; rng = StableRNG(1))
    @test is_poisson_type(EmpiricalDegree(rr)).κ ≈ 3 / 4
end

@testset "ExplicitGraph queries" begin
    k4 = ExplicitGraph(complete_graph(4))
    @test mean_degree(k4) == 3.0
    @test excess_degree(k4) == 2.0
    @test clustering_coefficient(k4) == 1.0
    cyc = ExplicitGraph(cycle_graph(10))
    @test mean_degree(cyc) == 2.0
    @test clustering_coefficient(cyc) == 0.0
    h = SimpleGraph(4)
    for (a, b) in ((1, 2), (2, 3), (1, 3), (3, 4))
        add_edge!(h, a, b)
    end
    @test clustering_coefficient(ExplicitGraph(h)) ≈ 3 * 1 / 5          # one triangle, five triples
    @test excess_degree(ExplicitGraph(h)) ≈ (2 + 2 + 6 + 0) / 8
    g = erdos_renyi(300, 0.02; rng = StableRNG(2))
    @test mean_degree(ExplicitGraph(g)) ≈ mean_degree(ConfigurationNetwork(EmpiricalDegree(g)))
    @test excess_degree(ExplicitGraph(g)) ≈ excess_degree(EmpiricalDegree(g))
    @test_throws ArgumentError ExplicitGraph(SimpleDiGraph(3))
    @test_throws ArgumentError ExplicitGraph(path_digraph(3))
    @test_throws ArgumentError excess_degree(ExplicitGraph(SimpleGraph(3)))
end

@testset "ExplicitGraph canonical text: the sorted edge list" begin
    @test canonical_text(ExplicitGraph(path_graph(3))) == "ExplicitGraph(nv=3, edges=[(1, 2), (2, 3)])"
    a = SimpleGraph(4); add_edge!(a, 3, 1); add_edge!(a, 4, 2); add_edge!(a, 1, 2)
    b = SimpleGraph(4); add_edge!(b, 1, 2); add_edge!(b, 2, 4); add_edge!(b, 1, 3)
    @test canonical_text(ExplicitGraph(a)) == canonical_text(ExplicitGraph(b)) ==
          "ExplicitGraph(nv=4, edges=[(1, 2), (1, 3), (2, 4)])"
    @test canonical_text(ExplicitGraph(SimpleGraph(2))) == "ExplicitGraph(nv=2, edges=[])"
end

# Newman–Miller lines + triangles: s single stubs paired uniformly, t triangle corners grouped in
# threes; self-loops and repeated edges are erased (O(1/N) effects).
function newman_miller(rng, cd::ClusteredDegree, N::Int)
    st = [rand(rng, cd) for _ in 1:N]
    singles = shuffle!(rng, reduce(vcat, [fill(i, s) for (i, (s, _)) in enumerate(st)]; init = Int[]))
    corners = shuffle!(rng, reduce(vcat, [fill(i, t) for (i, (_, t)) in enumerate(st)]; init = Int[]))
    g = SimpleGraph(N)
    for j in 1:2:(length(singles) - 1)
        a, b = singles[j], singles[j + 1]
        a != b && add_edge!(g, a, b)
    end
    for j in 1:3:(length(corners) - 2)
        a, b, c = corners[j], corners[j + 1], corners[j + 2]
        a != b && add_edge!(g, a, b)
        b != c && add_edge!(g, b, c)
        a != c && add_edge!(g, a, c)
    end
    return g
end

@testset "clustering_coefficient = transitivity of Newman–Miller graphs (E03)" begin
    rng = StableRNG(20260926)
    cases = [ClusteredNetwork(RegularDegree(2), RegularDegree(2)),           # 2/15
             ClusteredNetwork(PoissonDegree(3.0), PoissonDegree(1.0)),       # 2/27
             ClusteredNetwork(PoissonDegree(1.0), PoissonDegree(2.0)),       # 4/29
             ClusteredNetwork([0.1 0.2; 0.3 0.4])]                           # 3/7
    for net in cases
        g = newman_miller(rng, net.joint, 30_000)
        C = global_clustering_coefficient(g)
        @test C ≈ clustering_coefficient(net) atol = 0.005
        @test abs(C - triangle_edge_fraction(net)) > 0.05               # the legacy quantity is not C
        @test mean_degree(ExplicitGraph(g)) ≈ mean_degree(net) rtol = 0.02
    end
end
