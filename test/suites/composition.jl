# Owner: WP8. Composition on the syntax side (DESIGN §B.9, §D.2, §D.6): open models, `glue` (the
# pushout of species with concatenated reactions), `disjoint_union` (the monoidal product),
# `strata` and `stratify` (the typed product over T_net). The laws are checked on the models
# themselves and, where a semantics is needed, on the mass-action vector field written out
# independently below (H1′ for MA; the lumping of a typed product; H8 block diagonal).
# Regressions for the EdgeBasedModels 0.1 defects E22 (compose), E23 (tensor) and E24 (stratify).

using NetworkEpiCore
using Random
import Catalyst            # only to show that Catalyst's `extend` is a union (F7)
import Symbolics           # symbolic rates in stratify (structural zeros)
const NEC = NetworkEpiCore

# ---------------------------------------------------------------------------------------------
# Test-only semantics: the mass-action field of a ContactModel (κ = 1), species by name.
# ---------------------------------------------------------------------------------------------

function ma_field(cm, x::AbstractDict, p::AbstractDict)
    cm = contact_model(cm)
    dx = Dict{Symbol,Float64}(s => 0.0 for s in species_names(cm))
    for c in contacts(cm)
        f = rate_value(c.rate, p) * x[c.recipient] * x[c.infector]
        dx[c.recipient] -= f
        dx[c.product] += f
    end
    for t in node_transitions(cm)
        f = rate_value(t.rate, p) * x[t.from]
        dx[t.from] -= f
        t.to === nothing || (dx[t.to] += f)
    end
    return dx
end

random_state(rng, species) = Dict{Symbol,Float64}(s => rand(rng) for s in species)
random_params(rng, names) = Dict{Symbol,Float64}(n => 0.1 + rand(rng) for n in names)
param_names(cms...) = unique!(Symbol[NEC._parameter_name(q) for cm in cms
                                     for q in rate_parameters(contact_model(cm))])

# H1′ for mass action: the field of a glued model is the sum of the parts' fields pushed forward
# along the inclusions, each part evaluated on the pulled-back state (open systems add fields).
function glued_field_residual(G::OpenContactModel, parts, rng; probes = 5)
    worst = 0.0
    names = param_names(G, parts...)
    for _ in 1:probes
        p = random_params(rng, names)
        x = random_state(rng, species_names(G.model))
        lhs = ma_field(G, x, p)
        rhs = Dict{Symbol,Float64}(s => 0.0 for s in species_names(G.model))
        for (P, ι) in zip(parts, G.inclusions)
            xP = Dict{Symbol,Float64}(s => x[ι[s]] for s in species_names(contact_model(P)))
            for (s, v) in ma_field(P, xP, p)
                rhs[ι[s]] += v
            end
        end
        worst = max(worst, maximum(abs(lhs[s] - rhs[s]) for s in keys(lhs); init = 0.0))
    end
    return worst
end

# the reaction of `cm` with this shape (contacts: (s, J, X, layer); transitions: (X, Y))
function rate_of(cm, shape)
    cm = contact_model(cm)
    for r in Iterators.flatten((contacts(cm), node_transitions(cm)))
        NEC._shape(r) == shape && return r.rate
    end
    return nothing
end

# composite species map (apply `f` then `g`)
compose_maps(f, g) = Dict(k => g[v] for (k, v) in f)

# ---------------------------------------------------------------------------------------------
# Parts used throughout (§B.8)
# ---------------------------------------------------------------------------------------------

tr_model() = ContactModel(:tr; contacts = [Contact(:S, :I, :E, :τ)])
pr_model() = ContactModel(:pr; transitions = [NodeTransition(:E, :I, :σ),
                                              NodeTransition(:I, :R, :γ)])
tr_open() = open_model(tr_model(); legs = [[:S], [:E, :I]])
pr_open() = open_model(pr_model(); legs = [[:E, :I, :R]])

# ---------------------------------------------------------------------------------------------

@testset "Strata" begin
    age = strata([:y, :o]; sizes = [0.4, 0.6])
    @test age isa Strata
    @test age.names == [:y, :o] && age.sizes == [0.4, 0.6]
    @test length(age) == 2
    @test strata([:a, :b, :c]).sizes ≈ fill(1 / 3, 3)                  # default: equal sizes
    @test sum(strata([:a, :b, :c]).sizes) ≈ 1.0
    @test strata(["a", "b"]).names == [:a, :b]
    st = strata([:a, :b]; sizes = [0.3, 0.7 + 1e-10])                    # within 1e-8: renormalised
    @test sum(st.sizes) == 1.0 && st.sizes ≈ [0.3, 0.7]
    @test age == strata([:y, :o]; sizes = [0.4, 0.6])
    @test hash(age) == hash(strata([:y, :o]; sizes = [0.4, 0.6]))
    @test age != strata([:o, :y]; sizes = [0.6, 0.4])
    @test sprint(show, age) == "strata([:y, :o]; sizes = [0.4, 0.6])"
    @test canonical_text(age) ==
          "Strata(names=[:y, :o], sizes=[0.40000000000000002, 0.59999999999999998])"
    @test canonical_text(age) == canonical_text(strata([:y, :o]; sizes = [0.4, 0.6]))

    @test_throws ArgumentError strata(Symbol[])
    err(f) = try f(); "" catch e; e isa ArgumentError ? e.msg : rethrow() end
    @test occursin("not unique: a", err(() -> strata([:a, :a])))
    @test occursin(":all is reserved", err(() -> strata([:all, :b])))
    @test occursin("2 sizes for the 3 strata", err(() -> strata([:a, :b, :c]; sizes = [0.5, 0.5])))
    @test occursin("finite and > 0", err(() -> strata([:a, :b]; sizes = [0.0, 1.0])))
    @test occursin("finite and > 0", err(() -> strata([:a, :b]; sizes = [-0.5, 1.5])))
    @test occursin("must sum to 1", err(() -> strata([:a, :b]; sizes = [0.4, 0.5])))
    @test occursin("sizes ./ sum(sizes)", err(() -> strata([:a, :b]; sizes = [4000, 6000])))

    # the typed-network constructors read names and sizes from a Strata (WP7's descriptors)
    net = sbm_network(age; mean_contacts = [6.0 3.0; 2.0 4.0])            # 0.4·3 == 0.6·2
    @test net.types == [:y, :o] && net.sizes == [0.4, 0.6]
    @test_throws ArgumentError sbm_network(strata([:y, :o]); mean_contacts = [6.0 3.0; 2.0 4.0])
    un = unstructured(ConfigurationNetwork(RegularDegree(6)),
                      strata([:a, :b]; sizes = [0.25, 0.75]))
    @test un.types == [:a, :b] && un.sizes == [0.25, 0.75]
end

@testset "open_model: legs are validated" begin
    cm = seir_model()
    om = open_model(cm)
    @test om isa OpenContactModel
    # default: one leg, all species
    @test om.legs == [species_names(cm)]
    @test om.inclusions == [Dict(x => x for x in species_names(cm))]
    @test contact_model(om) === cm
    @test nameof(om) === :seir
    # a flat vector is one leg
    @test open_model(cm; legs = [:S, :I]).legs == [[:S, :I]]
    @test open_model(cm; legs = [[:S], [:E, :I], Symbol[]]).legs == [[:S], [:E, :I], Symbol[]]
    @test open_model(cm; legs = Vector{Symbol}[]).legs == Vector{Symbol}[]
    # re-legging keeps the model
    @test open_model(om; legs = [[:R]]).legs == [[:R]]
    @test open_model(om; legs = [[:R]]).model === cm

    err(f) = try f(); "" catch e; e isa ArgumentError ? e.msg : rethrow() end
    m = err(() -> open_model(cm; legs = [[:S], [:X, :Y]]))
    @test occursin("leg 2 exposes X, Y, which are not species of the model", m)
    @test occursin("species: S, E, I, R", m)
    @test occursin("leg 1 exposes Q, which is not a species",
                   err(() -> open_model(cm; legs = [:Q])))
    @test occursin("leg 1 lists I twice", err(() -> open_model(cm; legs = [[:I, :I]])))
    @test occursin("legs must be a vector of legs", err(() -> open_model(cm; legs = [[:S], :E])))
    @test occursin("legs must be a vector of legs", err(() -> open_model(cm; legs = :S)))

    # an OpenContactModel goes wherever a model goes, through contact_model
    @test typing(om).theory === :T_EB
    @test is_admissible(om, :edge_based; network = ConfigurationNetwork(PoissonDegree(5)))
    @test isequivalent(om, seir_model())
    @test occursin("legs          [[S, E, I, R]]", sprint(show, MIME("text/plain"), om))
    @test sprint(show, om) == "OpenContactModel(:seir; 4 species, legs [[S, E, I, R]])"
end

@testset "glue(tr, pr) gives seir_model() (B.8)" begin
    tr, pr = tr_open(), pr_open()
    seir2 = glue(tr, pr; on = [:E, :I])
    @test seir2 isa OpenContactModel
    @test isequivalent(seir2.model, seir_model())
    @test isequivalent(seir2, seir_model())
    # default on = shared exposed names
    @test isequivalent(glue(tr, pr), seir_model())
    @test species_names(seir2.model) == [:S, :E, :I, :R]
    @test susceptible_species(seir2.model) == [:S]
    @test entry_species(seir2.model) == [:E]
    @test typing(seir2).theory === :T_EB
    # the parts' legs, pushed forward
    @test seir2.legs == [[:S], [:E, :I], [:E, :I, :R]]
    @test seir2.inclusions == [Dict(:S => :S, :E => :E, :I => :I),
                               Dict(:E => :E, :I => :I, :R => :R)]
    @test nameof(seir2) === :tr_pr
    @test nameof(glue(tr, pr; name = :seir2)) === :seir2
    pv = provenance(seir2.model)
    @test pv.source === :transform
    @test pv.reaction_map == [1, 2, 3]            # tr's contact, then pr's two transitions
    @test any(occursin("glue of :tr, :pr along E, I", a) for a in pv.assumptions)
    @test any(occursin("Sus = the union of the parts' susceptible classes = {S}", a)
              for a in pv.assumptions)
    @test glue(tr, pr; legs = [[:S, :R]]).legs == [[:S, :R]]
    # the Symbol/Pair forms of `on`
    @test isequivalent(glue(tr, pr; on = [:E => :E, :I => :I]), seir_model())
    # plain ContactModels are open on all their species
    @test isequivalent(glue(tr_model(), pr_model()), seir_model())
    # H1′ (mass action): the field of the glued model is the sum of the parts' fields
    @test glued_field_residual(seir2, (tr, pr), Xoshiro(1)) < 1e-14
    # a model with an exit, glued from SIR and a vaccination-only part (S is not typed in that part)
    vax = ContactModel(:vax; transitions = [NodeTransition(:S, :V, :ν)])
    sirv = glue(sir_model(), vax)
    @test isequivalent(sirv, sirv_model())
    @test susceptible_species(sirv.model) == [:S]
    @test last(typing(sirv).reaction_types[end]) === :exit
    @test glued_field_residual(sirv, (sir_model(), vax), Xoshiro(2)) < 1e-14
end

@testset "glue(A, A) doubles rates, unlike Catalyst's extend (F7)" begin
    A = open_model(sir_model())
    AA = glue(A, A)                                   # default: identify every exposed species
    @test species_names(AA.model) == [:S, :I, :R]
    @test length(contacts(AA.model)) == 1 && length(node_transitions(AA.model)) == 1
    @test rate_of(AA, (:S, :I, :I, :all)) == :(2 * τ)
    @test rate_of(AA, (:I, :R)) == :(2 * γ)
    @test isequivalent(AA, sir_model(τ = :(2τ), γ = :(2γ)))
    @test !isequivalent(AA, sir_model())
    rng = Xoshiro(3)
    for _ in 1:3
        p = random_params(rng, [:τ, :γ])
        @test rate_value(rate_of(AA, (:S, :I, :I, :all)), p) ≈ 2p[:τ]
        @test rate_value(rate_of(AA, (:I, :R)), p) ≈ 2p[:γ]
    end
    AAA = glue(A, A, A)
    @test isequivalent(AAA, sir_model(τ = :(3τ), γ = :(3γ)))
    @test any(occursin("identical reactions merged: S + I → I + I (2 copies); I → R (2 copies)", a)
              for a in provenance(AA.model).assumptions)
    # different rates of an identical reaction are added
    B = sir_model(τ = :κ, γ = :μ)
    AB = glue(A, B)
    @test isequivalent(AB, sir_model(τ = :(τ + κ), γ = :(γ + μ)))
    @test glued_field_residual(AB, (A, B), Xoshiro(4)) < 1e-14
    @test glued_field_residual(AA, (A, A), Xoshiro(5)) < 1e-14
    # numeric rates
    N = sir_model(τ = 0.3, γ = 0.1)
    NN = glue(N, N)
    @test rate_of(NN, (:S, :I, :I, :all)) ≈ 0.6 && rate_of(NN, (:I, :R)) ≈ 0.2

    # Catalyst's extend is a union: extend(rn, rn) has the reactions of rn with unchanged rates,
    # so it is not the pushout (whose mass-action field doubles)
    rn = Catalyst.@network_component sir begin      # extend needs systems that are not complete
        τ, S + I --> 2I
        γ, I --> R
    end
    ext = Catalyst.extend(rn, rn)
    @test length(Catalyst.reactions(ext)) == length(Catalyst.reactions(rn)) == 2
    @test Set(string.(Catalyst.reactions(ext))) == Set(string.(Catalyst.reactions(rn)))
    # the Catalyst front end (WP9) is always loaded here, so this runs unconditionally (WP8
    # review: an `applicable` guard could skip it silently)
    @test applicable(contact_model, rn)
    G = glue(rn, rn)
    @test isequivalent(G, sir_model(τ = :(2τ), γ = :(2γ)))
    @test isequivalent(contact_model(ext), sir_model())
end

@testset "glue is associative (up to relabelling)" begin
    # three parts with differently named infectious states: A's I, B's Inf, C's Y
    A = open_model(ContactModel(:a; contacts = [Contact(:S, :I, :E, :τ)]))
    B = open_model(ContactModel(:b; transitions = [NodeTransition(:E, :Inf, :σ),
                                                   NodeTransition(:Inf, :R, :γ)]))
    C = open_model(ContactModel(:c; transitions = [NodeTransition(:Y, :R, :γ2),
                                                   NodeTransition(:R, :W, :ω)]))
    G1 = glue(glue(A, B; on = [:E, :I => :Inf]), C; on = [:I => :Y, :R])
    G2 = glue(A, glue(B, C; on = [:Inf => :Y, :R]); on = [:E, :I => :Inf])
    G3 = glue(A, B, C; identify = [(1, :E) => (2, :E), (1, :I) => (2, :Inf),
                                   (2, :Inf) => (3, :Y), (2, :R) => (3, :R)])
    @test isequivalent(G1, G2) && isequivalent(G2, G3)
    @test Set(species_names(G1.model)) == Set([:S, :E, :I, :R, :W])
    # B's and C's recoveries add
    @test rate_of(G1, (:I, :R)) == :(γ + γ2)
    @test Set(G1.legs) == Set(G2.legs) == Set(G3.legs)
    # the composite inclusions agree: every part's species lands on the same species
    inner1 = glue(A, B; on = [:E, :I => :Inf])
    inner2 = glue(B, C; on = [:Inf => :Y, :R])
    @test compose_maps(inner1.inclusions[1], G1.inclusions[1]) == G2.inclusions[1] ==
          G3.inclusions[1]
    @test compose_maps(inner1.inclusions[2], G1.inclusions[1]) ==
          compose_maps(inner2.inclusions[1], G2.inclusions[2]) == G3.inclusions[2]
    @test G1.inclusions[2] == compose_maps(inner2.inclusions[2], G2.inclusions[2]) ==
          G3.inclusions[3]
    @test glued_field_residual(G3, (A, B, C), Xoshiro(6)) < 1e-14
    # same-name gluing is strictly associative
    P = open_model(tr_model())
    Q = open_model(ContactModel(:q; transitions = [NodeTransition(:E, :I, :σ)]))
    R = open_model(ContactModel(:r; transitions = [NodeTransition(:I, :R, :γ)]))
    @test isequivalent(glue(glue(P, Q), R), glue(P, glue(Q, R)))
    @test isequivalent(glue(glue(P, Q), R), glue(P, Q, R))
    @test isequivalent(glue(P, Q, R), seir_model())
    # the n-ary `on` identifies a name across every part that has it
    @test isequivalent(glue(P, Q, R; on = [:E, :I]), seir_model())
    # symmetry up to relabelling: the identified class takes the earlier part's name
    AB, BA = glue(A, B; on = [:E, :I => :Inf]), glue(B, A; on = [:E, :Inf => :I])
    @test Set(species_names(BA.model)) == Set([:S, :E, :Inf, :R])
    @test !isequivalent(AB, BA)
    @test isequivalent(relabel(BA.model, Dict(:Inf => :I)), AB.model)
end

@testset "glue is unital (up to relabelling)" begin
    tr = tr_open()
    X = [:E, :I]
    id = open_model(ContactModel(:id; species = X); legs = [X, X])       # identity cospan on X
    @test isequivalent(glue(tr, id; on = X), tr)
    @test isequivalent(glue(id, tr; on = X), tr)
    @test glue(tr, id; on = X).legs == vcat(tr.legs, [X, X])
    @test isequivalent(glue(glue(tr, id; on = X), pr_open()), glue(tr, pr_open()))
    # the empty model is the unit of glue and of disjoint_union
    unit = open_model(ContactModel(:unit); legs = Vector{Symbol}[])
    @test isequivalent(glue(tr, unit), tr) && isequivalent(glue(unit, tr), tr)
    D = disjoint_union(:t => tr, :u => unit)
    untag = Dict(Symbol(x, :_t) => x for x in species_names(tr.model))
    @test isequivalent(relabel(D.model, untag), tr)
    # glue of one model is that model
    @test isequivalent(glue(tr), tr) && glue(tr).legs == tr.legs
end

@testset "glue validates legs, names and types (E22)" begin
    err(f) = try f(); "" catch e; e isa ArgumentError ? e.msg : rethrow() end
    tr, pr = tr_open(), pr_open()
    # an identified species must be a species of its part, exposed on a leg
    m = err(() -> glue(tr, pr; on = [:S]))
    @test occursin("S is not a species of :pr", m)
    m = err(() -> glue(open_model(tr_model(); legs = [[:S], [:E]]), pr; on = [:E, :I]))
    @test occursin("I is not exposed by a leg of :tr (legs [[S], [E]])", m)
    @test occursin("expose it with open_model", m)
    m = err(() -> glue(tr, pr; on = [:E => :X]))
    @test occursin("X is not a species of :pr", m)
    # a name clash of species that are not identified is an error ...
    m = err(() -> glue(tr, pr; on = [:E]))
    @test occursin("the species I of :tr and :pr are not identified", m)
    @test occursin("namespace = true", m)
    # I shared but not exposed
    m = err(() -> glue(open_model(tr_model(); legs = [[:S], [:E]]), pr))
    @test occursin("the species I of :tr and :pr are not identified", m)
    # ... unless namespaced: every non-identified species X of part i becomes X_<namespace>
    G = glue(tr, pr; on = [:E], namespace = true)
    @test Set(species_names(G.model)) == Set([:S_tr, :E, :I_tr, :I_pr, :R_pr])
    @test G.inclusions == [Dict(:S => :S_tr, :E => :E, :I => :I_tr),
                           Dict(:E => :E, :I => :I_pr, :R => :R_pr)]
    @test glued_field_residual(G, (tr, pr), Xoshiro(7)) < 1e-14
    G2 = glue(:x => tr, :y => pr; on = [:E], namespace = true)
    @test Set(species_names(G2.model)) == Set([:S_x, :E, :I_x, :I_y, :R_y])
    m = err(() -> glue(tr, tr; on = [:S], namespace = true))
    @test occursin("the namespaces tr are used by more than one part", m)
    # the typing is preserved: I is an infector in SIR but a susceptible recipient in B
    B = ContactModel(:b; contacts = [Contact(:I, :X, :Y, :κ)])
    @test susceptible_species(B) == [:I]
    m = err(() -> glue(sir_model(), B; on = [:I]))
    @test occursin("I of :b is susceptible but I of :sir is not", m)
    @test occursin("gluing must preserve the susceptible class", m)
    # two species of one part cannot be identified (that is a merge: relabel)
    m = err(() -> glue(tr, pr; identify = [(1, :E) => (2, :E), (1, :I) => (2, :E)]))
    @test occursin("the identifications join E, I of :tr", m)
    @test occursin("relabel", m)
    # malformed identifications
    @test occursin("part index 3 is out of range",
                   err(() -> glue(tr, pr; identify = [(1, :E) => (3, :E)])))
    @test occursin("identify entries are (i, :X) => (j, :Y)",
                   err(() -> glue(tr, pr; identify = [:E => :E])))
    @test occursin("pairs are for two parts",
                   err(() -> glue(tr, pr, pr_open(); on = [:E => :E])))
    @test occursin("E (in `on`) is a species of only :pr",
                   err(() -> glue(pr_open(), open_model(sir_model()),
                                  open_model(sir_model(); legs = [[:S]]); on = [:E])))
    @test occursin("glue needs at least one model", err(() -> glue()))
    # custom legs of the result are validated too
    @test occursin("leg 1 exposes Z", err(() -> glue(tr, pr; legs = [[:Z]])))
    # rate conventions must agree between parts with contacts (a part without contacts is neutral)
    F = ContactModel(:f; contacts = [Contact(:S, :I, :I, :β)], convention = FrequencyDependent())
    m = err(() -> glue(F, sir_model(); on = [:S, :I]))
    @test occursin("the rate conventions differ (FrequencyDependent in :f, PerContact in :sir)", m)
    rec = ContactModel(:rec; transitions = [NodeTransition(:I, :R, :γ)])
    FR = glue(F, rec)
    @test rate_convention(FR.model) == FrequencyDependent()
    @test per_contact_rates(FR.model, WellMixed(4.0)) == Any[:(β / 4.0)]
    # parameter defaults are shared by name and must agree
    d1 = ContactModel(:d1; contacts = [Contact(:S, :I, :I, :τ)], defaults = Dict(:τ => 0.2))
    d2 = ContactModel(:d2; transitions = [NodeTransition(:I, :R, :γ)], defaults = Dict(:γ => 0.1))
    @test parameter_defaults(glue(d1, d2).model) == Dict(:τ => 0.2, :γ => 0.1)
    d3 = ContactModel(:d3; transitions = [NodeTransition(:I, :R, :τ)], defaults = Dict(:τ => 0.5))
    m = err(() -> glue(d1, d3))
    @test occursin("different default values to the parameter τ (0.2 in :d1, 0.5 in :d3)", m)
    # labels of identified species must agree
    l1 = ContactModel(:l1; contacts = [Contact(:S, :I, :I, :τ)],
                      labels = Dict(:S => SpeciesLabel(:S; stratum = :a)))
    l2 = ContactModel(:l2; transitions = [NodeTransition(:S, :V, :ν)],
                      labels = Dict(:S => SpeciesLabel(:S; stratum = :b)))
    @test occursin("the identified species S has different labels", err(() -> glue(l1, l2)))
    l3 = ContactModel(:l3; transitions = [NodeTransition(:S, :V, :ν)])
    @test species_labels(glue(l1, l3).model)[:S] == SpeciesLabel(:S; stratum = :a)
    # reaction names: custom names are kept; two different reactions with one name are suffixed
    n1 = ContactModel(:n1; contacts = [Contact(:S, :I, :I, :τ; name = :infect)])
    n2 = ContactModel(:n2; contacts = [Contact(:S, :J, :J, :κ; name = :infect)])
    N12 = glue(n1, n2)
    @test [c.name for c in contacts(N12.model)] == [:infect, :infect_2]
end

@testset "disjoint_union: namespaced, typed over the parts, block diagonal (H8, E23)" begin
    city, rural = sir_model(τ = :τc, γ = :γc), sir_model(τ = :τr, γ = :γr)
    D = disjoint_union(:city => city, :rural => rural)
    @test D isa OpenContactModel
    @test Set(species_names(D.model)) ==
          Set([:S_city, :I_city, :R_city, :S_rural, :I_rural, :R_rural])
    @test susceptible_species(D.model) == [:S_city, :S_rural]
    @test nameof(D) === :city_rural
    @test D.legs == [[:S_city, :I_city, :R_city], [:S_rural, :I_rural, :R_rural]]
    @test species_labels(D.model)[:I_rural] == SpeciesLabel(:I; stratum = :rural)
    @test base_compartment_of(D.model, :S_city) === :S
    # block diagonal: no reaction mixes the parts
    for r in Iterators.flatten((contacts(D.model), node_transitions(D.model)))
        sp = r isa Contact ? (r.recipient, r.infector, r.product) :
             filter(!isnothing, (r.from, r.to))
        @test all(endswith(string(x), "_city") for x in sp) ||
              all(endswith(string(x), "_rural") for x in sp)
    end
    @test glued_field_residual(D, (city, rural), Xoshiro(8)) < 1e-14
    # the edge-based model accepts it on a MultitypeNetwork whose types are the parts, with zero
    # cross blocks; an untyped network has one node type, so two susceptible classes are refused
    blocks = sbm_network(strata([:city, :rural]; sizes = [0.5, 0.5]);
                         mean_contacts = [5.0 0.0; 0.0 3.0])
    @test is_admissible(D, :edge_based; network = blocks)
    # distinct strata, no network
    @test is_admissible(D, :edge_based)
    rep = admissibility(D, ConfigurationNetwork(PoissonDegree(5)))
    @test !rep.backends[:edge_based] && any(v -> v.type === :multiple_sus, rep.violations)
    # duplicate namespaces are refused with a clear error (the old tensor(a, a) failed inside MTK)
    err(f) = try f(); "" catch e; e isa ArgumentError ? e.msg : rethrow() end
    m = err(() -> disjoint_union(sir_model(), sir_model()))
    @test occursin("the namespaces sir are used by more than one part", m)
    @test occursin("disjoint_union(:a => model, :b => model)", m)
    @test length(species_names(disjoint_union(:a => sir_model(), :b => sir_model()).model)) == 6
    @test occursin("disjoint_union needs at least one model", err(() -> disjoint_union()))
    # an already stratified part: the strata are combined with the namespace
    st = stratify(sir_model(), strata([:y, :o]))
    Ds = disjoint_union(:u => st, :v => sir_model())
    @test species_labels(Ds.model)[:S_y_u] == SpeciesLabel(:S; stratum = :y_u)
    @test species_labels(Ds.model)[:S_v] == SpeciesLabel(:S; stratum = :v)
    # closed and associative up to relabelling (the old tensor was neither)
    a, b, c = sir_model(), seir_model(), sis_model()
    D1 = disjoint_union(:ab => disjoint_union(:a => a, :b => b), :c => c)
    D2 = disjoint_union(:a => a, :bc => disjoint_union(:b => b, :c => c))
    D3 = disjoint_union(:a => a, :b => b, :c => c)
    ab = disjoint_union(:a => a, :b => b)
    bc = disjoint_union(:b => b, :c => c)
    # to_D3(m, i): the names in the bracketed union (via the map m of part i) ↦ the names in D3
    to_D3(m, i) = Dict(v => D3.inclusions[i][k] for (k, v) in m)
    to3_1 = merge(to_D3(compose_maps(ab.inclusions[1], D1.inclusions[1]), 1),
                  to_D3(compose_maps(ab.inclusions[2], D1.inclusions[1]), 2),
                  to_D3(D1.inclusions[2], 3))
    to3_2 = merge(to_D3(D2.inclusions[1], 1),
                  to_D3(compose_maps(bc.inclusions[1], D2.inclusions[2]), 2),
                  to_D3(compose_maps(bc.inclusions[2], D2.inclusions[2]), 3))
    @test isequivalent(relabel(D1.model, to3_1), D3.model)
    @test isequivalent(relabel(D2.model, to3_2), D3.model)
    @test length(species_names(D3.model)) == 3 + 4 + 2
end

@testset "rate conventions and scale_contact_rates commute with glue (§D.2)" begin
    tr, pr = tr_open(), pr_open()
    for c in (3, :λ, 0.5)
        lhs = scale_contact_rates(glue(tr, pr).model, c)
        rhs = glue(scale_contact_rates(tr.model, c), scale_contact_rates(pr.model, c))
        @test isequivalent(lhs, rhs)
    end
    F1 = ContactModel(:f1; contacts = [Contact(:S, :I, :E, :β)], convention = FrequencyDependent())
    F2 = ContactModel(:f2; contacts = [Contact(:S, :A, :E, :βA)],
                      convention = FrequencyDependent())
    FF = glue(F1, F2)
    net = ConfigurationNetwork(PoissonDegree(4.0))
    @test per_contact_rates(FF.model, net) ==
          vcat(per_contact_rates(F1, net), per_contact_rates(F2, net))
end

@testset "stratify: species, labels and rates (two age groups, B.8)" begin
    age = strata([:y, :o]; sizes = [0.4, 0.6])
    sir_age = stratify(sir_model(), age; contact_rates = (a, b) -> a == b ? :τw : :τb)
    @test species_names(sir_age) == [:S_y, :S_o, :I_y, :I_o, :R_y, :R_o]
    @test susceptible_species(sir_age) == [:S_y, :S_o]
    @test nameof(sir_age) === :sir_strat
    labs = species_labels(sir_age)
    @test labs[:S_y] == SpeciesLabel(:S; stratum = :y)
    @test labs[:R_o] == SpeciesLabel(:R; stratum = :o)
    @test base_compartment_of(sir_age, :I_o) === :I
    # contacts (s,a) + (J,b) → (X,a) + (J,b): the recipient keeps its stratum, the infector its own
    expected = Dict((:S_y, :I_y, :I_y, :all) => :τw, (:S_y, :I_o, :I_y, :all) => :τb,
                    (:S_o, :I_y, :I_o, :all) => :τb, (:S_o, :I_o, :I_o, :all) => :τw)
    @test Dict(NEC._shape(c) => c.rate for c in contacts(sir_age)) == expected
    # transitions (X,a) → (Y,a): none between strata
    @test Dict(NEC._shape(t) => t.rate for t in node_transitions(sir_age)) ==
          Dict((:I_y, :R_y) => :γ, (:I_o, :R_o) => :γ)
    @test rate_parameters(sir_age) == [:τw, :τb, :γ]
    @test provenance(sir_age).reaction_map == [1, 1, 1, 1, 2, 2]
    @test any(occursin("typed product over T_net with the strata y, o (sizes 0.4, 0.6)", a)
              for a in provenance(sir_age).assumptions)
    # the typed product keeps every reaction's type: one Sus per stratum, T_EB
    tp = typing(sir_age)
    @test tp.theory === :T_EB
    @test [last(x) for x in tp.reaction_types] ==
          [:contact, :contact, :contact, :contact, :progress, :progress]
    # it lifts on a network typed over the same strata, never on an untyped one
    agenet = sbm_network(age; mean_contacts = [6.0 3.0; 2.0 4.0], family = PoissonDegree)
    @test is_admissible(sir_age, :edge_based; network = agenet)
    @test is_admissible(sir_age, :edge_based;
                        network = unstructured(ConfigurationNetwork(RegularDegree(6)), age))
    rep = admissibility(sir_age, ConfigurationNetwork(PoissonDegree(5)))
    @test !rep.backends[:edge_based] && rep.backends[:pairwise]
    @test any(v -> v.type === :multiple_sus, rep.violations)
    rep2 = admissibility(sir_age, sbm_network(strata([:a, :b]); mean_contacts = [2.0 1.0; 1.0 2.0]))
    @test !rep2.backends[:edge_based]                                    # strata ≠ node types

    # the other forms of contact_rates give the same model
    D = Dict((:y, :y) => :τw, (:y, :o) => :τb, (:o, :y) => :τb, (:o, :o) => :τw)
    @test isequivalent(stratify(sir_model(), age; contact_rates = D), sir_age)
    D3 = Dict((:S_I_to_I, a, b) => (a == b ? :τw : :τb) for a in (:y, :o), b in (:y, :o))
    @test isequivalent(stratify(sir_model(), age; contact_rates = D3), sir_age)
    @test isequivalent(stratify(sir_model(), age; contact_rates = (c, a, b) -> a == b ? :τw : :τb),
                       sir_age)
    # a matrix of multipliers: rate M[a, b]·τ
    M = [1.0 0.5; 0.25 2.0]
    sm = stratify(sir_model(), age; contact_rates = M)
    @test rate_of(sm, (:S_y, :I_o, :I_y, :all)) == :(0.5τ)
    @test rate_of(sm, (:S_o, :I_y, :I_o, :all)) == :(0.25τ)
    @test rate_of(sm, (:S_y, :I_y, :I_y, :all)) === :τ
    # a numeric 0 is a structural zero: the contact is not created
    sz = stratify(sir_model(), age; contact_rates = [1.0 0.0; 0.0 1.0])
    @test length(contacts(sz)) == 2
    @test all(c -> c.recipient === :S_y ? c.infector === :I_y : c.infector === :I_o, contacts(sz))
    @test any(occursin("2 zero-rate reaction(s) not created", a)
              for a in provenance(sz).assumptions)
    # ... also with symbolic rates, where rate_mul(0.0, τ) is a symbolic 0 (WP8 review: a
    # contact with rate 0 was created)
    Symbolics.@variables τs γs
    symsir = ContactModel(:a; contacts = [Contact(:S, :I, :I, τs)],
                          transitions = [NodeTransition(:I, :R, γs)])
    szs = stratify(symsir, age; contact_rates = [1.0 0.5; 0.5 0.0])
    @test length(contacts(szs)) == 3
    @test !any(c -> c.recipient === :S_o && c.infector === :I_o, contacts(szs))
    szt = stratify(symsir, age; transition_rates = (t, a) -> a === :o ? rate_mul(0, t.rate) : t.rate)
    @test [NEC._shape(t) for t in node_transitions(szt)] == [(:I_y, :R_y)]
    # a symbolic rate with a parameter is never taken for 0
    @test !NEC._is_zero_rate(0 * τs + γs) && NEC._is_zero_rate(rate_mul(0.0, τs))
    # transition rates by stratum
    st2 = stratify(sir_model(), age; transition_rates = a -> Symbol(:γ_, a))
    @test Dict(NEC._shape(t) => t.rate for t in node_transitions(st2)) ==
          Dict((:I_y, :R_y) => :γ_y, (:I_o, :R_o) => :γ_o)
    @test isequivalent(stratify(sir_model(), age; transition_rates = Dict(:y => :γ_y, :o => :γ_o)),
                       st2)
    byname = Dict((:I_to_R, :y) => :γ_y, (:I_to_R, :o) => :γ_o)
    @test isequivalent(stratify(sir_model(), age; transition_rates = byname), st2)
    # SEIR: counts are |species|·K, |contacts|·K², |transitions|·K
    se = stratify(seir_model(), strata([:a, :b, :c]))
    @test length(species_names(se)) == 12
    @test length(contacts(se)) == 9 && length(node_transitions(se)) == 6
    @test entry_species(se) == [:E_a, :E_b, :E_c]
    @test susceptible_species(se) == [:S_a, :S_b, :S_c]
    # multi-contact and multi-transition models need the per-reaction forms
    two = twostrain_model()
    sw = stratify(two, age; contact_rates = (c, a, b) -> a == b ? c.rate : rate_mul(0.5, c.rate),
                  transition_rates = (t, a) -> a === :o ? rate_mul(2, t.rate) : t.rate)
    @test rate_of(sw, (:S_y, :I2_o, :I2_y, :all)) == :(0.5τ2)
    @test rate_of(sw, (:S_o, :I1_o, :I1_o, :all)) === :τ1
    @test rate_of(sw, (:I1_o, :R_o)) == :(2γ) && rate_of(sw, (:I1_y, :R_y)) === :γ
    @test typing(sw).theory === :T_EB
    # a T_net model stays T_net, reaction by reaction (the typed product is over T_net)
    ss = stratify(sis_model(), age)
    @test typing(ss).theory === :T_net
    @test [last(x) for x in typing(ss).reaction_types] ==
          [:contact, :contact, :contact, :contact, :resus, :resus]
    # layers, removals and exits are stratified too
    lay = ContactModel(:lay; contacts = [Contact(:S, :I, :I, :τ; layer = :home)],
                       transitions = [NodeTransition(:I, nothing, :μ), NodeTransition(:S, :V, :ν)])
    sl = stratify(lay, age)
    @test all(c -> c.layer === :home, contacts(sl))
    @test Set(NEC._shape(t) for t in node_transitions(sl)) ==
          Set([(:I_y, nothing), (:I_o, nothing), (:S_y, :V_y), (:S_o, :V_o)])
    @test [last(x) for x in typing(sl).reaction_types][5:end] == [:remove, :remove, :exit, :exit]
    # the convenience form with names (equal sizes) and custom names
    @test isequivalent(stratify(sir_model(), [:y, :o]), stratify(sir_model(), strata([:y, :o])))
    @test nameof(stratify(sir_model(), age; name = :sir_age)) === :sir_age
    nm = ContactModel(:nm; contacts = [Contact(:S, :I, :I, :τ; name = :infect)])
    @test Set(c.name for c in contacts(stratify(nm, age))) ==
          Set([:infect_y_y, :infect_y_o, :infect_o_y, :infect_o_o])
end

@testset "stratify: one stratum is the identity (M10, syntax)" begin
    corpus = (sir_model(), seir_model(), sis_model(), sirs_model(), seair_model(),
              twostrain_model(), sirv_model(), erlang_stages(seir_model(), :I, 3),
              with_reinfection_counting(sis_model(), 2),
              ContactModel(:trace; contacts = [Contact(:S, :I, :I, :τ), Contact(:S, :D, :Q, :α)],
                           transitions = [NodeTransition(:I, :D, :γ), NodeTransition(:D, :R, :δ)]))
    for cm in corpus
        s1 = stratify(cm, strata([:a]))
        @test isequivalent(s1, cm)
        @test species_names(s1) == species_names(cm)
        @test all(l -> l.stratum === :a, values(species_labels(s1)))
        @test [c.name for c in contacts(s1)] == [c.name for c in contacts(cm)]
    end
    # labels of refined species keep their base, count and stage
    er = stratify(erlang_stages(seir_model(), :I, 3), strata([:a]))
    @test species_labels(er)[:I_2] == SpeciesLabel(:I; stratum = :a, stage = 2)
    rc = stratify(with_reinfection_counting(sis_model(), 2), strata([:a]))
    @test species_labels(rc)[:S_1] == SpeciesLabel(:S; stratum = :a, count = 1)
    @test infection_count_of(rc, :S_1) == 1
    # a T_EB model with one stratum lifts on the one-type unstructured network (the M10 set-up)
    one = strata([:a])
    s1 = stratify(sir_model(), one)
    @test is_admissible(s1, :edge_based;
                        network = unstructured(ConfigurationNetwork(RegularDegree(6)), one))
end

@testset "stratify: the typed product lumps back to the model under mass action" begin
    # with :same rates, Σ_a x_{X,a} evolves exactly as the unstratified model (every back end that
    # is additive over reactions inherits this; it is the mass-action shadow of M10)
    rng = Xoshiro(9)
    st = strata([:a, :b, :c]; sizes = [0.2, 0.3, 0.5])
    for cm in (sir_model(), seair_model(), twostrain_model(), sis_model(), sirv_model())
        S = stratify(cm, st)
        for _ in 1:3
            p = random_params(rng, param_names(cm))
            x = random_state(rng, species_names(S))
            dS = ma_field(S, x, p)
            xb = Dict(X => sum(x[Symbol(X, :_, a)] for a in st.names) for X in species_names(cm))
            dP = ma_field(cm, xb, p)
            @test maximum(abs(sum(dS[Symbol(X, :_, a)] for a in st.names) - dP[X])
                          for X in species_names(cm)) < 1e-13
        end
    end
end

@testset "stratify: associative and commutative up to relabelling (Libkind et al. 2022)" begin
    age, sex = strata([:y, :o]), strata([:m, :f])
    AS = stratify(stratify(sir_model(), age), sex)
    SA = stratify(stratify(sir_model(), sex), age)
    @test length(species_names(AS)) == 12 && length(contacts(AS)) == 16
    swap = Dict(Symbol(X, :_, a, :_, s) => Symbol(X, :_, s, :_, a)
                for X in (:S, :I, :R), a in age.names, s in sex.names)
    @test isequivalent(relabel(AS, swap), SA)
    @test species_labels(AS)[:S_y_m] == SpeciesLabel(:S; stratum = :y_m)   # the product of strata
    # stratify commutes with glue (pullback along a fixed typing preserves pushouts)
    tr, pr = tr_open(), pr_open()
    lhs = stratify(glue(tr, pr).model, age)
    rhs = glue(stratify(tr, age), stratify(pr, age))
    @test isequivalent(lhs, rhs)
    @test stratify(tr, age).legs == [[:S_y, :S_o], [:E_y, :E_o, :I_y, :I_o]]
    @test stratify(tr, [:y, :o]).legs == stratify(tr, age).legs
    # and with the rate endofunctor c_λ
    @test isequivalent(scale_contact_rates(stratify(seir_model(), age), 3),
                       stratify(scale_contact_rates(seir_model(), 3), age))
end

@testset "stratify: validation" begin
    err(f) = try f(); "" catch e; e isa ArgumentError ? e.msg : rethrow() end
    age = strata([:y, :o])
    @test occursin("contact_rates must be :same, a Dict",
                   err(() -> stratify(sir_model(), age; contact_rates = :diag)))
    @test occursin("contact_rates must be :same, a Dict",
                   err(() -> stratify(sir_model(), age; contact_rates = 3)))
    @test occursin("contact_rates is a 3×3 matrix; it must be 2×2",
                   err(() -> stratify(sir_model(), age; contact_rates = ones(3, 3))))
    @test occursin("multipliers must be finite and ≥ 0; got -1.0",
                   err(() -> stratify(sir_model(), age; contact_rates = [1.0 -1.0; 1.0 1.0])))
    @test occursin("numeric rates must be ≥ 0",
                   err(() -> stratify(sir_model(), age; contact_rates = (a, b) -> a == b ? 1.0 : -0.5)))
    m = err(() -> stratify(sir_model(), age; contact_rates = Dict((:y, :y) => :τ)))
    @test occursin("no rate for the contact `S_I_to_I` from stratum o to stratum y", m)
    @test occursin("give every pair, with 0 for no contact", m)
    m = err(() -> stratify(sir_model(), age; contact_rates = Dict((:y, :x) => :τ)))
    @test occursin("contact_rates has the key(s) (:y, :x)", m)
    m = err(() -> stratify(twostrain_model(), age; contact_rates = (a, b) -> :τ))
    @test occursin("ambiguous for a model with 2 contacts", m) && occursin("(c, a, b) -> rate", m)
    m = err(() -> stratify(twostrain_model(), age; contact_rates = Dict((:y, :y) => :τ)))
    @test occursin("keys (a, b) are ambiguous for a model with 2 contacts", m)
    @test occursin("must accept (c::Contact, a, b) or (a, b)",
                   err(() -> stratify(sir_model(), age; contact_rates = x -> x)))
    @test occursin("transition_rates must be :same, a Dict or a function",
                   err(() -> stratify(sir_model(), age; transition_rates = :per_stratum)))
    m = err(() -> stratify(seir_model(), age; transition_rates = a -> :γ))
    @test occursin("ambiguous for a model with 2 transitions", m)
    m = err(() -> stratify(seir_model(), age; transition_rates = Dict((:I_to_R, :y) => :γ)))
    @test occursin("transition_rates has no rate for the transition `E_to_I` in stratum y", m)
    @test occursin("transition_rates has the key(s) :z",
                   err(() -> stratify(sir_model(), age; transition_rates = Dict(:z => :γ))))
    # generated names must be unique (species and strata with underscores)
    odd = ContactModel(:odd; contacts = [Contact(:S, :I, :I, :τ)], species = [:S, :I, :S_y])
    m = err(() -> stratify(odd, strata([:y_o, :o])))
    @test occursin("the stratified species names S_y_o are generated twice", m)
end

@testset "E24 regression: the degree law lives in the typed network, not in stratify" begin
    # EBM 0.1 replaced every base degree distribution by a Poisson law of the same mean. Here
    # stratify is syntax only, and `unstructured` keeps the base law: ψ_a(x) = ψ(Σ_b n_b x_b).
    st = strata([:a, :b]; sizes = [0.3, 0.7])
    net = unstructured(ConfigurationNetwork(RegularDegree(5)), st)
    for x in (0.2, 0.5, 0.9)
        # regular, not exp(5(x−1))
        @test pgf(net.degrees[1], Dict(:a => x, :b => x)) ≈ x^5
    end
    @test excess_contacts(net)[1, 1, 1] + excess_contacts(net)[1, 1, 2] ≈ 4.0      # regular: k − 1
    @test is_admissible(stratify(sir_model(), st), :edge_based; network = net)
    # sizes are part of Strata and checked (EBM 0.1 had none)
    @test_throws ArgumentError strata([:a, :b]; sizes = [0.5, 0.6])
    # an unrealisable mixing is refused by the typed network (reciprocity), not silently lifted
    @test_throws ArgumentError sbm_network(strata([:a, :b]); mean_contacts = [1.0 0.0; 0.5 0.5])
end

@testset "E22/E23 regressions: identified species are kept once, parts are checked" begin
    # E22: the old compose dropped wired ports, accepted unknown ports and any port types
    tr, pr = tr_open(), pr_open()
    G = glue(tr, pr)
    @test count(==(:E), species_names(G.model)) == 1 && count(==(:I), species_names(G.model)) == 1
    # identified species stay exposed
    @test any(l -> :E in l, G.legs)
    @test_throws ArgumentError glue(tr, pr; on = [:X])
    Ib = ContactModel(:b; contacts = [Contact(:I, :X, :Y, :κ)])
    @test_throws ArgumentError glue(sir_model(), Ib; on = [:I])
    # E23: the old tensor was not closed under nesting and accepted duplicate names
    a, b, c = sir_model(τ = :τa), sir_model(τ = :τb), sir_model(τ = :τc)
    nested = disjoint_union(:ab => disjoint_union(:a => a, :b => b), :c => c)
    @test nested isa OpenContactModel
    @test length(species_names(nested.model)) == 9
    @test_throws ArgumentError disjoint_union(a, a)
    @test glued_field_residual(nested, (disjoint_union(:a => a, :b => b), c), Xoshiro(10)) < 1e-14
end

@testset "stratify and disjoint_union through the numeric NGM (M10 unit law, H8)" begin
    # The next-generation matrix (WP11) reads the strata from the labels that stratify and
    # disjoint_union write. For SIR on a configuration network R₀ = T κ_ex with
    # T = τ/(τ + γ) and κ_ex = ψ''(1)/ψ'(1), computed by hand here.
    p = Dict(:τ => 1 / 6, :γ => 1 / 4)
    T = p[:τ] / (p[:τ] + p[:γ])
    base_net = ConfigurationNetwork(RegularDegree(6))
    @test applicable(basic_reproduction_number, sir_model(), base_net, p)   # WP11 is in-tree
    st = strata([:a, :b, :c]; sizes = [0.2, 0.3, 0.5])
    for (d, κex) in ((RegularDegree(6), 5.0), (PoissonDegree(5.0), 5.0),
                     # bimodal {2: 5/6, 10: 1/6}: ψ''(1) = Σ k(k−1)p_k, ψ'(1) = Σ k p_k
                     (EmpiricalDegree(Dict(2 => 5 / 6, 10 => 1 / 6)),
                      (5 / 6 * 2 + 1 / 6 * 90) / (5 / 6 * 2 + 1 / 6 * 10)))
        base = ConfigurationNetwork(d)
        @test basic_reproduction_number(sir_model(), base, p) ≈ T * κex
        # unit law: types assigned independently of the network change nothing
        @test basic_reproduction_number(stratify(sir_model(), st), unstructured(base, st), p) ≈
              T * κex rtol = 1e-12
        one = strata([:a])
        @test basic_reproduction_number(stratify(sir_model(), one), unstructured(base, one), p) ≈
              T * κex rtol = 1e-12
    end
    # H8: a disjoint union on a block-diagonal network has the larger block's R₀
    D = disjoint_union(:a => sir_model(), :b => sir_model())
    blocks = sbm_network(strata([:a, :b]); mean_contacts = [5.0 0.0; 0.0 3.0])
    @test basic_reproduction_number(D, blocks, p) ≈ T * 5.0 rtol = 1e-12
end
