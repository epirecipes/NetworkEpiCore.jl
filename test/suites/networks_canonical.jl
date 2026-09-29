# Owner: WP7. Canonical text of degree distributions, multivariate laws and descriptors (§E.4):
# golden strings (explicit field names, `%.17g` numbers), invariance under equivalent
# constructions, sensitivity to every value, refusal of symbolic values, and stability across
# Julia sessions.

using NetworkEpiCore, Test
import Symbolics

const GOLDEN = [
    PoissonDegree(5) => "PoissonDegree(mean=5)",
    PoissonDegree(0.1) => "PoissonDegree(mean=0.10000000000000001)",
    RegularDegree(6) => "RegularDegree(k=6)",
    BinomialDegree(10, 0.3) => "BinomialDegree(n=10, p=0.29999999999999999)",
    NegBinDegree(mean = 4, var = 8) => "NegBinDegree(r=4, p=0.5)",
    GeometricDegree(3) => "NegBinDegree(r=1, p=0.25)",
    PowerLawDegree(2.5; kmin = 2, kmax = 60) => "PowerLawDegree(α=2.5, kmin=2, kmax=60)",
    EmpiricalDegree(2 => 5 / 6, 10 => 1 / 6) =>
        "EmpiricalDegree(p=[0, 0, 0.83333333333333337, 0, 0, 0, 0, 0, 0, 0, 0.16666666666666666])",
    MixtureDegree(0.5 => PoissonDegree(2), 0.5 => RegularDegree(3)) =>
        "MixtureDegree(weights=[0.5, 0.5], components=[PoissonDegree(mean=2), RegularDegree(k=3)])",
    IndependentDegrees() => "IndependentDegrees(parts=[])",
    SplitDegrees(PoissonDegree(3), :a => 0.25, :b => 0.75) =>
        "SplitDegrees(total=PoissonDegree(mean=3), weights=[:a => 0.25, :b => 0.75])",
    WellMixed(5) => "WellMixed(κ=5)",
    ConfigurationNetwork(PoissonDegree(5)) => "ConfigurationNetwork(degrees=PoissonDegree(mean=5))",
    ConfigurationNetwork(RegularDegree(6)) => "ConfigurationNetwork(degrees=RegularDegree(k=6))",
    sbm_network([:y, :o], [0.4, 0.6]; mean_contacts = [6.0 3.0; 2.0 4.0]) =>
        "MultitypeNetwork(types=[:y, :o], sizes=[0.40000000000000002, 0.59999999999999998], " *
        "degrees=[IndependentDegrees(parts=[:y => PoissonDegree(mean=6), :o => PoissonDegree(mean=3)]), " *
        "IndependentDegrees(parts=[:y => PoissonDegree(mean=2), :o => PoissonDegree(mean=4)])])",
    unstructured(ConfigurationNetwork(RegularDegree(6)), [:a, :b], [0.5, 0.5]) =>
        "MultitypeNetwork(types=[:a, :b], sizes=[0.5, 0.5], " *
        "degrees=[SplitDegrees(total=RegularDegree(k=6), weights=[:a => 0.5, :b => 0.5]), " *
        "SplitDegrees(total=RegularDegree(k=6), weights=[:a => 0.5, :b => 0.5])])",
    ClusteredNetwork(RegularDegree(2), RegularDegree(2)) =>
        "ClusteredNetwork(joint=ClusteredDegree(singles=RegularDegree(k=2), triangles=RegularDegree(k=2)))",
    ClusteredNetwork([0.125 0.25; 0.375 0.25]) =>
        "ClusteredNetwork(joint=ClusteredDegree(p_st=[[0.125, 0.25], [0.375, 0.25]]))",
    DynamicNetwork(RegularDegree(6), NeighbourExchange(0.1)) =>
        "DynamicNetwork(base=ConfigurationNetwork(degrees=RegularDegree(k=6)), " *
        "process=NeighbourExchange(η=0.10000000000000001))",
    MultiplexNetwork(:home => RegularDegree(3), :comm => PoissonDegree(5)) =>
        "MultiplexNetwork(layers=[:home => ConfigurationNetwork(degrees=RegularDegree(k=3)), " *
        ":comm => ConfigurationNetwork(degrees=PoissonDegree(mean=5))])",
    MFSHNetwork(PoissonDegree(5)) => "MFSHNetwork(degrees=PoissonDegree(mean=5))",
    DynamicNetwork(RegularDegree(10), DormantContacts(1, 3)) =>
        "DynamicNetwork(base=ConfigurationNetwork(degrees=RegularDegree(k=10)), " *
        "process=DormantContacts(η_form=1, η_break=3))",
    degree_correlated(EmpiricalDegree(1 => 0.5, 3 => 0.5); r = 0) =>
        "DegreeCorrelatedNetwork(degrees=[1, 3], probabilities=[0.5, 0.5], " *
        "edge_ends=[[0.0625, 0.1875], [0.1875, 0.5625]])",
]

@testset "golden canonical text" begin
    for (x, text) in GOLDEN
        @test canonical_text(x) == text
        @test sprint(canonical_text, x) == text
        @test !occursin('\n', canonical_text(x))
    end
end

@testset "equivalent constructions give identical text; every value matters" begin
    same = [
        (PoissonDegree(5), PoissonDegree(5.0), PoissonDegree(5 // 1)),
        (RegularDegree(6), RegularDegree(6.0)),
        (EmpiricalDegree([0, 0, 1, 0, 0]), EmpiricalDegree(2 => 1.0), EmpiricalDegree(Dict(2 => 1))),
        (WellMixed(5), WellMixed(5.0)),
        (NegBinDegree(mean = 4, var = 8), NegBinDegree(4, 1 // 2)),
        (ClusteredNetwork([0.125 0.25 0.0; 0.375 0.25 0.0]), ClusteredNetwork([0.125 0.25; 0.375 0.25])),
        (MultiplexNetwork(:h => RegularDegree(3)), MultiplexNetwork(:h => ConfigurationNetwork(RegularDegree(3)))),
    ]
    for group in same
        texts = canonical_text.(group)
        @test all(==(first(texts)), texts)
    end
    different = [
        PoissonDegree(5), PoissonDegree(5.000000000000001), RegularDegree(5), WellMixed(5),
        ConfigurationNetwork(PoissonDegree(5)), MFSHNetwork(PoissonDegree(5)),
        BinomialDegree(10, 0.5), BinomialDegree(11, 0.5),
        sbm_network([:y, :o], [0.4, 0.6]; mean_contacts = [6.0 3.0; 2.0 4.0]),
        sbm_network([:o, :y], [0.6, 0.4]; mean_contacts = [4.0 2.0; 3.0 6.0]),     # type order matters
        DynamicNetwork(RegularDegree(6), NeighbourExchange(0.1)),
        DynamicNetwork(RegularDegree(6), NeighbourExchange(1.0)),
        ClusteredNetwork(RegularDegree(2), RegularDegree(2)), ClusteredNetwork(RegularDegree(2), RegularDegree(1)),
    ]
    texts = canonical_text.(different)
    @test allunique(texts)
    @test canonical_text(PoissonDegree(-0.0)) == canonical_text(PoissonDegree(0.0))
end

@testset "symbolic values are refused" begin
    Symbolics.@variables μ η
    @test_throws ArgumentError canonical_text(PoissonDegree(μ))
    @test_throws ArgumentError canonical_text(ConfigurationNetwork(PoissonDegree(μ)))
    @test_throws ArgumentError canonical_text(NeighbourExchange(η))
end

@testset "stable across Julia sessions" begin
    probe = [PoissonDegree(0.1), EmpiricalDegree(2 => 5 / 6, 10 => 1 / 6),
             sbm_network([:y, :o], [0.4, 0.6]; mean_contacts = [6.0 3.0; 2.0 4.0]),
             DynamicNetwork(RegularDegree(6), NeighbourExchange(0.1)),
             PowerLawDegree(2.5; kmin = 2, kmax = 60)]
    code = """
    using NetworkEpiCore
    for x in (PoissonDegree(0.1), EmpiricalDegree(2 => 5 / 6, 10 => 1 / 6),
              sbm_network([:y, :o], [0.4, 0.6]; mean_contacts = [6.0 3.0; 2.0 4.0]),
              DynamicNetwork(RegularDegree(6), NeighbourExchange(0.1)),
              PowerLawDegree(2.5; kmin = 2, kmax = 60))
        println(canonical_text(x))
    end
    """
    cmd = `$(Base.julia_cmd()) --startup-file=no --project=$(Base.active_project()) -e $code`
    out = readlines(cmd)
    @test out == canonical_text.(probe)
end
