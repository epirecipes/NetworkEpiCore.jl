# Owner: WP7 (DESIGN_NetworkEpiCore.md §A.2, §C.1, §C.2; work package in §G.2).
# Triggered by Graphs.
#
# EmpiricalDegree(g) (the degree histogram of a graph) and the ExplicitGraph queries: validation
# (undirected graphs only), mean and excess degree, clustering coefficient (transitivity) and
# canonical text (the sorted edge list).
module NetworkEpiCoreGraphsExt

import NetworkEpiCore
import NetworkEpiCore: EmpiricalDegree, ExplicitGraph, mean_degree, excess_degree,
                       clustering_coefficient, canonical_text
import Graphs

function _undirected(g::Graphs.AbstractGraph, what)
    Graphs.is_directed(g) &&
        throw(ArgumentError("$what needs an undirected graph; got a directed $(typeof(g))"))
    return g
end

NetworkEpiCore._net_check_explicit_graph(g::Graphs.AbstractGraph) = (_undirected(g, "ExplicitGraph"); nothing)

"""
    EmpiricalDegree(g::Graphs.AbstractGraph)
    EmpiricalDegree(net::ExplicitGraph)

The degree distribution of an undirected graph: pₖ = (number of nodes of degree k)/N, with
degrees from `Graphs.degree` (a self-loop counts once). `ConfigurationNetwork(EmpiricalDegree(g))`
is the annealed (configuration-model) approximation of `g`.
"""
function EmpiricalDegree(g::Graphs.AbstractGraph)
    _undirected(g, "EmpiricalDegree")
    n = Graphs.nv(g)
    n > 0 || throw(ArgumentError("EmpiricalDegree: the graph has no nodes"))
    ds = Graphs.degree(g)
    counts = zeros(Int, maximum(ds) + 1)
    for d in ds
        counts[d + 1] += 1
    end
    return EmpiricalDegree(counts ./ n)
end
EmpiricalDegree(net::ExplicitGraph{<:Graphs.AbstractGraph}) = EmpiricalDegree(net.graph)

"""
    mean_degree(net::ExplicitGraph)

The realised mean degree Σᵥ kᵥ/N of the graph.
"""
function mean_degree(net::ExplicitGraph{<:Graphs.AbstractGraph})
    n = Graphs.nv(net.graph)
    n > 0 || throw(ArgumentError("mean_degree: the graph has no nodes"))
    return sum(Graphs.degree(net.graph)) / n
end

"""
    excess_degree(net::ExplicitGraph)

The realised mean excess degree Σᵥ kᵥ(kᵥ − 1)/Σᵥ kᵥ of the graph.
"""
function excess_degree(net::ExplicitGraph{<:Graphs.AbstractGraph})
    ds = Graphs.degree(net.graph)
    s = sum(ds; init = 0)
    s > 0 || throw(ArgumentError("excess_degree: the graph has no edges"))
    return sum(d * (d - 1) for d in ds) / s
end

"""
    clustering_coefficient(net::ExplicitGraph)

The transitivity 3 × (number of triangles)/(number of connected triples) of the graph
(`Graphs.global_clustering_coefficient`), the same quantity as the clustering coefficient of a
`ClusteredNetwork`.
"""
clustering_coefficient(net::ExplicitGraph{<:Graphs.AbstractGraph}) =
    Graphs.global_clustering_coefficient(net.graph)

function canonical_text(io::IO, net::ExplicitGraph{<:Graphs.AbstractGraph})
    g = net.graph
    es = sort!([minmax(Graphs.src(e), Graphs.dst(e)) for e in Graphs.edges(g)])
    return NetworkEpiCore._netct_struct(io, "ExplicitGraph", :nv => Graphs.nv(g), :edges => es)
end

end # module NetworkEpiCoreGraphsExt
