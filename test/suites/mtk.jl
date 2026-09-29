# Owner: WP10. The ModelingToolkit front end (DESIGN §B.5): contact_model(::System) by flux
# pairing on SIR, SEIR, SIRS, SEAIR (branching after latency, two infectors) and β·S·I/N
# (frequency dependence, with a population parameter or a conserved sum of unknowns); the
# ambiguity error, the births error and the other error texts (tested verbatim); the signs of
# coefficients (a sign that depends on the parameters is an error, as in S-catalysed recovery;
# zero, positive and negative defaults; the node-catalysed reading of numeric rates); scale
# (small rates such as the per-pair rate of a counts ODE are kept; floating-point netting
# cancels); the provenance strings; the explicit escape hatches and their checks against the
# ODE; parameter defaults; as_parameter under MTK; exact zeros (a coefficient that vanishes on
# the probe box is never dropped, §J.3) and non-negative rates; time as t whatever the independent
# variable is called; and the round trip contact_model(System(mass_action(cm))) ≅ cm, including
# WP6's tracing and S-catalysed recovery models.

using NetworkEpiCore
using ModelingToolkit
using ModelingToolkit: t_nounits as t, D_nounits as D
import ModelingToolkitBase
using Symbolics
const NEC = NetworkEpiCore
const MB = ModelingToolkitBase

err(f) = try
    f()
    "no error"
catch e
    sprint(showerror, e)
end

# An MTK System from a SymbolicODE (states X(t)), for round trips.
ode_system(ode::SymbolicODE; name = ode.name) =
    complete(System([D(x) ~ f for (x, f) in zip(ode.states, ode.rhs)], t; name))

# The vector field of a list of equations D(X) ~ f, and whether a model's mass action is it.
field(eqs) = SymbolicODE(:ode; states = [only(Symbolics.SymbolicUtils.arguments(
                                             Symbolics.unwrap(eq.lhs))) for eq in eqs],
                         rhs = [eq.rhs for eq in eqs])
same_field(cm, eqs) = vector_fields_equal(mass_action(cm), field(eqs); rename = :none)

@parameters τ γ σ β N p ε μ ν a
@variables S(t) E(t) I(t) R(t) A(t) C(t) V(t) R1(t) R2(t)

@testset "SIR, SEIR, SIRS, SIS from a System; provenance strings" begin
    @test ModelingToolkit.System === MB.System
    sir_sys = complete(System([D(S) ~ -τ * S * I, D(I) ~ τ * S * I - γ * I, D(R) ~ γ * I], t;
                              name = :sir))
    cm = contact_model(sir_sys)
    sir_dir = ContactModel(:sir; contacts = [Contact(:S, :I, :I, :τ)],
                           transitions = [NodeTransition(:I, :R, :γ)])
    @test isequivalent(cm, sir_dir, sir_model())            # DESIGN §B.8, "four routes"
    @test species_names(cm) == [:S, :I, :R] && susceptible_species(cm) == [:S]
    @test only(contacts(cm)).rate === :τ && only(node_transitions(cm)).rate === :γ
    pv = provenance(cm)
    @test pv.source === :mtk && pv.method === :flux_pairing
    @test pv.assumptions == [
        "flux pairing: the ODE fixes one network compatible with it, not a unique one (F3); " *
        "Catalyst is the canonical front end",
        "τ*S*I leaves D(S) and enters D(I); I is gained, so I is the infector: contact " *
        "S + I → I + I at τ",
        "γ*I leaves D(I) and enters D(R): transition I → R at γ",
        "Sus inferred as recipients \\ contact products = {S}"]
    @test pv.reaction_map == [1, 2]                  # the equations that lose each flux
    shown = sprint(show, MIME"text/plain"(), cm)
    @test occursin("ContactModel :sir  (source: ModelingToolkit.System; method: flux_pairing; " *
                   "rates: PerContact)", shown)
    @test occursin("I is gained, so I is the infector", shown)
    @test is_admissible(cm, :edge_based)
    # an uncompleted system and a name override
    raw = System([D(S) ~ -τ * S * I, D(I) ~ τ * S * I - γ * I, D(R) ~ γ * I], t; name = :raw)
    @test isequivalent(contact_model(raw), sir_model())
    @test nameof(contact_model(raw; name = :renamed)) === :renamed
    # SEIR: entry E, the infector I is not gained by the contact term
    seir = complete(System([D(S) ~ -τ * S * I, D(E) ~ τ * S * I - σ * E,
                            D(I) ~ σ * E - γ * I, D(R) ~ γ * I], t; name = :seir))
    cs = contact_model(seir)
    @test isequivalent(cs, seir_model())
    @test entry_species(cs) == [:E]
    @test provenance(cs).assumptions[2] ==
          "τ*S*I leaves D(S) and enters D(E); D(I) does not lose it, so I is the infector: " *
          "contact S + I → E + I at τ"
    @test provenance(cs).reaction_map == [1, 2, 3]
    # SIRS and SIS: valid T_net models that the edge-based model refuses
    sirs = complete(System([D(S) ~ -τ * S * I + ε * R, D(I) ~ τ * S * I - γ * I,
                            D(R) ~ γ * I - ε * R], t; name = :sirs))
    cr = contact_model(sirs)
    @test isequivalent(cr, sirs_model())
    @test typing(cr).theory === :T_net && !is_admissible(cr, :edge_based)
    @test "ε*R leaves D(R) and enters D(S): transition R → S at ε" in provenance(cr).assumptions
    sis = complete(System([D(S) ~ -τ * S * I + γ * I, D(I) ~ τ * S * I - γ * I], t; name = :sis))
    @test isequivalent(contact_model(sis), sis_model())
    # a composed (namespaced) system keeps its names
    @named inner = System([D(S) ~ -τ * S * I, D(I) ~ τ * S * I - γ * I, D(R) ~ γ * I], t)
    outer = complete(System(Equation[], t; systems = [inner], name = :outer))
    co = contact_model(outer)
    @test species_names(co) == [Symbol("inner₊S"), Symbol("inner₊I"), Symbol("inner₊R")]
    @test only(contacts(co)).rate === Symbol("inner₊τ")
end

@testset "branching, removal, several gains, exits" begin
    # SEAIR: E → I at pσ and E → A at (1 − p)σ; expansion splits (1 − p)σE into σE − pσE,
    # which pairing by monomial handles
    seair = complete(System([D(S) ~ -τ * S * I - τ * S * A,
                             D(E) ~ τ * S * I + τ * S * A - σ * E,
                             D(I) ~ p * σ * E - γ * I, D(A) ~ (1 - p) * σ * E - γ * A,
                             D(R) ~ γ * I + γ * A], t; name = :seair))
    c7 = contact_model(seair)
    @test isequivalent(c7, seair_model(; τI = :τ, τA = :τ))
    @test [(c.recipient, c.infector, c.product) for c in contacts(c7)] ==
          [(:S, :I, :E), (:S, :A, :E)]                   # ordered by the unknowns
    @test "(σ - p*σ)*E leaves D(E) and enters D(A): transition E → A at (σ - p*σ)" in
          provenance(c7).assumptions
    # −(γ + μ)I: a transition to R and a removal
    rem = complete(System([D(S) ~ -τ * S * I, D(I) ~ τ * S * I - (γ + μ) * I, D(R) ~ γ * I], t;
                          name = :rem))
    cm = contact_model(rem)
    @test isequivalent(cm, ContactModel(:x; contacts = [Contact(:S, :I, :I, :τ)],
                                        transitions = [NodeTransition(:I, :R, :γ),
                                                       NodeTransition(:I, nothing, :μ)]))
    @test "μ*I leaves D(I) and no other unknown gains it: removal I → ∅ at μ" in
          provenance(cm).assumptions
    # −2γI split between R1 and R2: two transitions (unambiguous in the IR)
    two = complete(System([D(S) ~ -τ * S * I, D(I) ~ τ * S * I - 2γ * I, D(R1) ~ γ * I,
                           D(R2) ~ γ * I], t; name = :two))
    ct = contact_model(two)
    @test sort([(tr.from, tr.to) for tr in node_transitions(ct)]) == [(:I, :R1), (:I, :R2)]
    @test all(tr.rate === :γ for tr in node_transitions(ct))
    # exits (vaccination S → V) and numeric rates
    vax = complete(System([D(S) ~ -τ * S * I - ν * S, D(I) ~ τ * S * I - γ * I, D(R) ~ γ * I,
                           D(V) ~ ν * S], t; name = :vax))
    @test isequivalent(contact_model(vax), sirv_model())
    num = complete(System([D(S) ~ -0.5 * S * I, D(I) ~ 0.5 * S * I - 0.25 * I, D(R) ~ 0.25 * I],
                          t; name = :num))
    cn = contact_model(num)
    @test only(contacts(cn)).rate == 0.5 && only(node_transitions(cn)).rate == 0.25
    @test isequivalent(cn, sir_model(; τ = 0.5, γ = 0.25))
end

@testset "β·S·I/N: rate conventions" begin
    seirN = complete(System([D(S) ~ -β * S * I / N, D(E) ~ β * S * I / N - σ * E,
                             D(I) ~ σ * E - γ * I, D(R) ~ γ * I], t; name = :seirN))
    cf = contact_model(seirN; rates = :frequency, population = :N)
    @test rate_convention(cf) == FrequencyDependent()
    @test only(contacts(cf)).rate === :β
    ref = ContactModel(:seir; contacts = [Contact(:S, :I, :E, :β)],
                       transitions = [NodeTransition(:E, :I, :σ), NodeTransition(:I, :R, :γ)],
                       convention = FrequencyDependent())
    @test isequivalent(cf, ref)
    @test !(:N in NEC._parameter_name.(rate_parameters(cf)))
    @test provenance(cf).assumptions[2] ==
          "β*S*I/N leaves D(S) and enters D(E); D(I) does not lose it, so I is the infector: " *
          "contact S + I → E + I at β"
    @test "contact rates of the form β/N read as frequency-dependent with population N: the " *
          "stored constant is β (FrequencyDependent)" in provenance(cf).assumptions
    # per-contact reading of β/N warns once (the same text as the Catalyst front end)
    cp = @test_logs (:warn, "rate β/N looks frequency-dependent; pass rates = :frequency, " *
                            "population = :N") contact_model(seirN)
    @test rate_convention(cp) == PerContact()
    @test isequal(only(contacts(cp)).rate, :(β / N))
    # N = S + E + I + R conserved, written into the equations
    seirC = complete(System([D(S) ~ -β * S * I / (S + E + I + R),
                             D(E) ~ β * S * I / (S + E + I + R) - σ * E,
                             D(I) ~ σ * E - γ * I, D(R) ~ γ * I], t; name = :seirC))
    cc = contact_model(seirC; rates = :frequency)
    @test isequivalent(cc, ref)
    @test "N = S + E + I + R is conserved (its equations sum to 0), so contact terms divided by " *
          "N are read on fractions (N = 1): FrequencyDependent" in provenance(cc).assumptions
    # the same with an algebraic equation for N (eliminated by mtkcompile)
    @variables Ntot(t)
    alg = System([D(S) ~ -β * S * I / Ntot, D(E) ~ β * S * I / Ntot - σ * E,
                  D(I) ~ σ * E - γ * I, D(R) ~ γ * I, Ntot ~ S + E + I + R], t; name = :alg)
    ca = contact_model(alg; rates = :frequency)
    @test isequivalent(ca, ref)
    @test "algebraic and observed equations eliminated with mtkcompile (full_equations)" in
          provenance(ca).assumptions
    # a population that is not conserved, or no population at all
    notcons = complete(System([D(S) ~ -β * S * I / (S + I) + μ * R,
                               D(I) ~ β * S * I / (S + I) - γ * I, D(R) ~ γ * I - μ * R], t;
                              name = :nc))
    @test err(() -> contact_model(notcons; rates = :frequency)) ==
          "ArgumentError: contact_model(:nc): rates = :frequency: the population `I + S` is not " *
          "conserved (the sum of its equations is not 0), so the contact rates cannot be read on " *
          "fractions"
    sir = complete(System([D(S) ~ -τ * S * I, D(I) ~ τ * S * I - γ * I, D(R) ~ γ * I], t;
                          name = :sir))
    @test err(() -> contact_model(sir; rates = :frequency)) ==
          "ArgumentError: contact_model(:sir): rates = :frequency needs population = :N (the " *
          "parameter that divides the contact rates), or contact terms divided by a conserved " *
          "sum of unknowns such as S + I + R"
    sq = complete(System([D(S) ~ -β * S * I / N^2, D(I) ~ β * S * I / N^2 - γ * I, D(R) ~ γ * I],
                         t; name = :sq))
    @test_throws ArgumentError contact_model(sq; rates = :frequency, population = :N)
    # density dependence
    cd = contact_model(sir; rates = :density, population = :N)
    @test rate_convention(cd) == DensityDependent(:N) && only(contacts(cd)).rate === :τ
    @test_throws ArgumentError contact_model(sir; rates = :density)
    @test_throws ArgumentError contact_model(sir; rates = :massaction)
end

@testset "ambiguity error, births error and other error texts" begin
    # S + I → E + R written as an ODE: lost by both S and I
    amb = complete(System([D(S) ~ -β * S * I, D(I) ~ -β * S * I, D(E) ~ β * S * I,
                           D(R) ~ β * S * I], t; name = :amb))
    @test err(() -> contact_model(amb)) ==
          "ArgumentError: contact_model(:amb): the term `β*S*I` is lost by both D(S) and D(I): " *
          "either the infector changes state on transmission (not a network contact) or several " *
          "contacts share this flux (e.g. S + I → E + I and I + S → R + S), and the ODE cannot " *
          "tell which. Pass contacts = [flux => (from, to, infector), …] to say which"
    # resolved with the escape hatch: one network compatible with this ODE (F3)
    res = contact_model(amb; contacts = [β * S * I => (:S, :E, :I)], susceptible = [:S])
    @test [(c.recipient, c.infector, c.product) for c in contacts(res)] ==
          [(:S, :I, :E), (:I, :S, :R)]
    @test last.(typing(res).reaction_types) == [:contact, :node_contact]
    @test "contact S + I → E + I at β: from the `contacts` keyword" in provenance(res).assumptions
    # births
    births = complete(System([D(S) ~ μ - τ * S * I, D(I) ~ τ * S * I - γ * I, D(R) ~ γ * I], t;
                             name = :births))
    @test err(() -> contact_model(births)) ==
          "ArgumentError: contact_model(:births): the term `μ` of D(S) involves no unknown: " *
          "births change the node set; use the ODE itself for mass action (a network model has " *
          "a fixed set of nodes)"
    grow = complete(System([D(S) ~ -τ * S * I, D(I) ~ τ * S * I + γ * I], t; name = :grow))
    @test err(() -> contact_model(grow)) ==
          "ArgumentError: contact_model(:grow): D(I) gains `γ*I`, growth in proportion to I " *
          "itself: births change the node set; use the ODE itself for mass action"
    # an accumulator (cumulative incidence) is not a node state
    acc = complete(System([D(S) ~ -τ * S * I, D(I) ~ τ * S * I - γ * I, D(R) ~ γ * I,
                           D(C) ~ τ * S * I], t; name = :acc))
    @test err(() -> contact_model(acc)) ==
          "ArgumentError: contact_model(:acc): the gains of `2τ*S*I` exceed the loss `τ*S*I` in " *
          "D(S): births change the node set; use the ODE itself for mass action (an accumulator " *
          "such as cumulative incidence is not a node state; remove it from the system)"
    # a loss without a product
    lost = complete(System([D(S) ~ -τ * S * I, D(I) ~ -γ * I], t; name = :lost))
    @test err(() -> contact_model(lost)) ==
          "ArgumentError: contact_model(:lost): D(S) loses `τ*S*I` but its products gain only " *
          "`0*S*I`: a contact moves the recipient to a product state (s + J → X + J); there is " *
          "no contact with product ∅"
    # non-bilinear incidence, higher order
    nb = complete(System([D(S) ~ -β * S * I / (1 + a * I), D(I) ~ β * S * I / (1 + a * I) - γ * I,
                          D(R) ~ γ * I], t; name = :nb))
    msg = err(() -> contact_model(nb))
    @test startswith(msg, "ArgumentError: contact_model(:nb): the term `")
    @test occursin("of D(S) is not mass action in the unknowns (non-bilinear incidence); the IR " *
                   "supports first-order transitions a*X and bilinear contacts τ*X*J only", msg)
    ho = complete(System([D(S) ~ -τ * S * I * R, D(I) ~ τ * S * I * R, D(R) ~ 0], t; name = :ho))
    @test occursin("(higher order: 3 unknowns in one term)", err(() -> contact_model(ho)))
    # a loss in another unknown's equation
    odd = complete(System([D(S) ~ -τ * S * I, D(I) ~ τ * S * I - γ * I, D(R) ~ -γ * I], t;
                          name = :odd))
    @test occursin("D(R) loses `γ*I`, a term proportional to I", err(() -> contact_model(odd)))
    # non-autonomous systems
    nonaut = complete(System([D(S) ~ -τ * exp(-t) * S * I, D(I) ~ τ * exp(-t) * S * I - γ * I,
                              D(R) ~ γ * I], t; name = :nonaut))
    @test startswith(err(() -> contact_model(nonaut)),
                     "ArgumentError: contact_model(:nonaut): the right-hand side of D(S) depends " *
                     "on t explicitly")
    ct = contact_model(nonaut; allow_t = true)
    @test NEC._uses_time(only(contacts(ct)).rate)
    @test rate_value(only(contacts(ct)).rate, Dict(:τ => 2.0); t = 0.0) ≈ 2.0
    @test "the rates depend on t (allow_t = true): time-dependent rates are for the ODE back " *
          "ends only" in provenance(ct).assumptions
    @test_throws ArgumentError instantiate(ct, Dict(:τ => 2.0, :γ => 1.0))
end

@testset "signs of coefficients: parameter-dependent signs, defaults, node-catalysed readings" begin
    # S-catalysed recovery (WP6 corpus model 11: S + I → 2I at τ, I + S → R + S at δ, a T_net
    # model): D(I) nets τSI − δSI into (τ − δ)SI, whose sign depends on the parameters. It must
    # not be read as the T_EB contacts S + I → I + I at τ − δ and S + I → R + I at δ.
    @parameters δ
    msg_scat(nm) =
        "ArgumentError: contact_model(:$(nm)): the sign of the coefficient `-δ + τ` of S*I in " *
        "D(I) depends on the parameters (0.4 at δ = 0.1, τ = 0.5 but -0.4 at δ = 0.5, τ = 0.1): " *
        "the ODE may net several reactions into one term (for example a contact and a " *
        "node-catalysed transition such as I + S → R + S); pass the reactions explicitly with " *
        "contacts = [flux => (from, to, infector), …] and transitions = [flux => (from, to), …], " *
        "listing every reaction whose flux is proportional to S*I"
    scat2 = complete(System([D(S) ~ -τ * S * I, D(I) ~ τ * S * I - δ * S * I, D(R) ~ δ * S * I],
                            t; name = :scat2))
    @test err(() -> contact_model(scat2)) == msg_scat(:scat2)
    scat3 = complete(System([D(S) ~ -τ * S * I, D(I) ~ τ * S * I - δ * S * I - γ * I,
                             D(R) ~ δ * S * I + γ * I], t; name = :scat3))
    @test err(() -> contact_model(scat3)) == msg_scat(:scat3)
    # the verdict does not depend on the names of the parameters or their number
    for (n1, n2) in ((:τ, :δ), (:τ, :a), (:β, :a), (:x1, :x2), (:tau, :alpha), (:k, :c),
                     (:z, :a), (:a, :z))
        p1 = only(@parameters $n1)
        p2 = only(@parameters $n2)
        for extra in (false, true)
            eqs = [D(S) ~ -p1 * S * I, D(I) ~ p1 * S * I - p2 * S * I - (extra ? γ * I : 0),
                   D(R) ~ p2 * S * I + (extra ? γ * I : 0)]
            @test startswith(err(() -> contact_model(complete(System(eqs, t; name = :v)))),
                             "ArgumentError: contact_model(:v): the sign of the coefficient ")
        end
    end
    # the escape hatch gives the T_net model
    scat = ContactModel(:scat; contacts = [Contact(:S, :I, :I, :τ), Contact(:I, :S, :R, :δ)],
                        transitions = [NodeTransition(:I, :R, :γ)])
    cs3 = contact_model(scat3; contacts = [δ * I * S => (:I, :R, :S)])
    @test isequivalent(cs3, scat)
    @test typing(cs3).theory === :T_net && !is_admissible(cs3, :edge_based)
    @test last.(typing(cs3).reaction_types) == [:contact, :node_contact, :progress]
    @test "contact I + S → R + S at δ: from the `contacts` keyword" in provenance(cs3).assumptions
    @test "τ*S*I leaves D(S) and enters D(I); I is gained, so I is the infector: contact " *
          "S + I → I + I at τ" in provenance(cs3).assumptions
    # with numeric rates the netted coefficient 0.3 has a sign: the ODE is read as the contacts
    # S + I → I + I and S + I → R + I (same ODE, T_EB), and the node-catalysed reading is named
    num = complete(System([D(S) ~ -0.5 * S * I, D(I) ~ 0.5 * S * I - 0.2 * S * I,
                           D(R) ~ 0.2 * S * I], t; name = :num))
    cn = contact_model(num)
    @test [(c.recipient, c.infector, c.product) for c in contacts(cn)] ==
          [(:S, :I, :I), (:S, :I, :R)]
    @test [c.rate for c in contacts(cn)] ≈ [0.3, 0.2]
    @test typing(cn).theory === :T_EB
    @test "the terms in S*I are also those of S + I → I + I at 0.5 with the node-catalysed " *
          "I + S → R + S at 0.2 (a T_net reading; F3): the contacts are kept; pass contacts = " *
          "[flux => (from, to, infector), …] for the other reading" in provenance(cn).assumptions
    cnt = contact_model(num; contacts = [0.2 * I * S => (:I, :R, :S)])
    @test isequivalent(cnt, ContactModel(:x; contacts = [Contact(:S, :I, :I, 0.5),
                                                         Contact(:I, :S, :R, 0.2)]))
    # (1 − p)σ = σ − pσ has no sign by its form, but is positive on the probe box: accepted, and
    # the numeric decision is in the provenance
    seair = complete(System([D(S) ~ -τ * S * I, D(E) ~ τ * S * I - σ * E,
                             D(I) ~ p * σ * E - γ * I, D(A) ~ (1 - p) * σ * E - γ * A,
                             D(R) ~ γ * I + γ * A], t; name = :seair))
    ce = contact_model(seair)
    @test (:E, :A, :(σ - p * σ)) in [(tr.from, tr.to, tr.rate) for tr in node_transitions(ce)]
    @test "the sign of the coefficient `σ - p*σ` of E in D(A) is read numerically: positive at " *
          "all 41 probe points with p, σ ∈ [0.1, 0.9] (its form alone does not fix it)" in
          provenance(ce).assumptions
    # a default of 0 switches a flux off; it is not a sign probe (vaccination ν = 0)
    @parameters τd = 0.2 γd = 0.1 νd = 0.0
    sv = complete(System([D(S) ~ -τd * S * I - νd * S, D(I) ~ τd * S * I - γd * I,
                          D(R) ~ γd * I, D(V) ~ νd * S], t; name = :sirv0))
    cv = contact_model(sv)
    @test isequivalent(cv, sirv_model(; τ = :τd, γ = :γd, ν = :νd))
    @test parameter_defaults(cv) == Dict(:τd => 0.2, :γd => 0.1, :νd => 0.0)
    # positive defaults are one more probe: p = 1 (all to I) makes (1 − p)σ zero, which is
    # allowed; p = 2 makes it negative, which is an error
    @parameters p1d = 1.0 p2d = 2.0
    seairp(pp, nm) = complete(System([D(S) ~ -τ * S * I, D(E) ~ τ * S * I - σ * E,
                                      D(I) ~ pp * σ * E - γ * I,
                                      D(A) ~ (1 - pp) * σ * E - γ * A, D(R) ~ γ * I + γ * A], t;
                                     name = nm))
    c1 = contact_model(seairp(p1d, :p1))
    @test (:E, :A) in [(tr.from, tr.to) for tr in node_transitions(c1)]
    @test "the sign of the coefficient `σ - p1d*σ` of E in D(A) is read numerically: positive " *
          "at all 41 probe points with p1d, σ ∈ [0.1, 0.9], and 0 at the parameter defaults " *
          "(p1d = 1.0; σ at 0.5, with no positive default) (its form alone does not fix it)" in
          provenance(c1).assumptions
    @test err(() -> contact_model(seairp(p2d, :p2))) ==
          "ArgumentError: contact_model(:p2): the sign of the coefficient `σ - p2d*σ` of E in " *
          "D(A) cannot be fixed: it is positive for p2d, σ ∈ [0.1, 0.9] but -0.5 at the " *
          "parameter defaults (p2d = 2.0; σ at 0.5, with no positive default), and a rate " *
          "cannot change sign; check the defaults, or pass the reactions explicitly with " *
          "contacts = [flux => (from, to, infector), …] and transitions = [flux => (from, to), " *
          "…], listing every reaction whose flux is proportional to E"
    # many parameters in one coefficient: the vertices of the probe box (7-10 parameters) and
    # seeded random vertices (more than 10)
    q = [only(@parameters $(Symbol(:q, k))) for k in 1:12]
    many(c, nm) = complete(System([D(S) ~ -τ * S * I, D(I) ~ τ * S * I - σ * I,
                                   D(R) ~ c * I, D(A) ~ (σ - c) * I], t; name = nm))
    cm8 = contact_model(many(σ * prod(q[1:7]), :m8))            # σ(1 − q1⋯q7) > 0 on the box
    @test (:I, :A) in [(tr.from, tr.to) for tr in node_transitions(cm8)]
    # 8 variables (σ, q1, …, q7): 2^8 vertices, the centre and 32 interior points
    @test any(a -> occursin("positive at all 289 probe points", a), provenance(cm8).assumptions)
    @test startswith(err(() -> contact_model(many(σ * sum(q) / 6, :m12))),
                     "ArgumentError: contact_model(:m12): the sign of the coefficient ")
    # time (allow_t) is probed over [0.1, 1000] on a log scale: τ·cos(t) changes sign,
    # τ·(2 + cos(t)) does not
    osc = complete(System([D(S) ~ -τ * cos(t) * S * I, D(I) ~ τ * cos(t) * S * I - γ * I,
                           D(R) ~ γ * I], t; name = :osc))
    @test startswith(err(() -> contact_model(osc; allow_t = true)),
                     "ArgumentError: contact_model(:osc): the sign of the coefficient ")
    pos = complete(System([D(S) ~ -τ * (2 + cos(t)) * S * I,
                           D(I) ~ τ * (2 + cos(t)) * S * I - γ * I, D(R) ~ γ * I], t; name = :pos))
    cpos = contact_model(pos; allow_t = true)
    @test NEC._uses_time(only(contacts(cpos)).rate)
    @test "the sign of the coefficient `2τ + τ*cos(t)` of S*I in D(I) is read numerically: " *
          "positive at all 41 probe points with t ∈ [0.1, 1000.0] (log scale) and τ ∈ [0.1, 0.9] " *
          "(its form alone does not fix it)" in provenance(cpos).assumptions
    # the ambiguity error names each loss when they differ, and the actual products
    amb2 = complete(System([D(S) ~ -τ * S * I, D(I) ~ -2τ * S * I, D(R) ~ 3τ * S * I], t;
                           name = :amb2))
    @test err(() -> contact_model(amb2)) ==
          "ArgumentError: contact_model(:amb2): the term in S*I is lost by both D(S) (`τ*S*I`) " *
          "and D(I) (`2τ*S*I`): either the infector changes state on transmission (not a network " *
          "contact) or several contacts share this flux (e.g. S + I → R + I and I + S → R + S), " *
          "and the ODE cannot tell which. Pass contacts = [flux => (from, to, infector), …] to " *
          "say which"
    gone = complete(System([D(S) ~ -τ * S * I, D(I) ~ -τ * S * I], t; name = :gone))
    @test err(() -> contact_model(gone)) ==
          "ArgumentError: contact_model(:gone): the term `τ*S*I` is lost by both D(S) and D(I), " *
          "and no unknown gains it: a contact moves the recipient to a product state " *
          "(s + J → X + J); there is no contact with product ∅"
    # a bilinear term lost by a third unknown (neither node of the edge)
    msg_w(nm) = "ArgumentError: contact_model(:$(nm)): D(W) loses `τ*S*I`, although W is " *
                "neither S nor I: a contact changes only the state of its recipient, one of the " *
                "two nodes of the edge"
    @variables W(t)
    w1 = complete(System([D(S) ~ -γ * S, D(I) ~ τ * S * I + γ * S, D(W) ~ -τ * S * I], t;
                         name = :w1))
    @test err(() -> contact_model(w1)) == msg_w(:w1)
    w2 = complete(System([D(S) ~ -τ * S * I, D(I) ~ τ * S * I, D(W) ~ -τ * S * I,
                          D(R) ~ τ * S * I], t; name = :w2))
    @test err(() -> contact_model(w2)) == msg_w(:w2)
end

@testset "scale: small rates are kept, floating-point netting cancels" begin
    # An SIR ODE in counts (N = 8e9 people, time in hours, γ = 1/336, R0 = 1.5): the per-pair rate
    # β = R0·γ/N ≈ 5.6e-13 is a real flux, which rates = :density reads as a contact
    Nw = 8e9
    γw = 1 / (14 * 24)
    βw = 1.5 * γw / Nw
    @test 5e-13 < βw < 6e-13
    eqw = [D(S) ~ -βw * S * I, D(I) ~ βw * S * I - γw * I, D(R) ~ γw * I]
    cw = contact_model(complete(System(eqw, t; name = :world)); rates = :density, population = Nw)
    @test [(c.recipient, c.infector, c.product, c.rate) for c in contacts(cw)] ==
          [(:S, :I, :I, βw)]
    @test [(tr.from, tr.to, tr.rate) for tr in node_transitions(cw)] == [(:I, :R, γw)]
    @test rate_convention(cw) == DensityDependent(Nw) && susceptible_species(cw) == [:S]
    # its mass action is the ODE on fractions S/N: the contact at βN = R0·γ
    @test same_field(cw, [D(S) ~ -βw * Nw * S * I, D(I) ~ βw * Nw * S * I - γw * I,
                          D(R) ~ γw * I])
    @test !same_field(ContactModel(:nocontact; species = [:S, :I, :R],
                                   transitions = [NodeTransition(:I, :R, γw)]), eqw)
    # per-contact rates of 2e-13 and 1e-13·τ are kept too
    eqt = [D(S) ~ -2e-13 * S * I, D(I) ~ 2e-13 * S * I - 0.1 * I, D(R) ~ 0.1 * I]
    ct = contact_model(complete(System(eqt, t; name = :tiny)))
    @test isequivalent(ct, sir_model(; τ = 2e-13, γ = 0.1)) && same_field(ct, eqt)
    eqs = [D(S) ~ -1e-13 * τ * S * I, D(I) ~ 1e-13 * τ * S * I - γ * I, D(R) ~ γ * I]
    cs = contact_model(complete(System(eqs, t; name = :tinysym)))
    @test rate_value(only(contacts(cs)).rate, Dict(:τ => 2.0)) ≈ 2e-13 && same_field(cs, eqs)
    # signs read on the probes are scale-free: (1 − p)σ·1e-13 is positive, (τ − δ)·1e-13 is not
    @parameters δ
    seair = [D(S) ~ -τ * S * I, D(E) ~ τ * S * I - 1e-13 * σ * E,
             D(I) ~ 1e-13 * p * σ * E - γ * I, D(A) ~ 1e-13 * (1 - p) * σ * E - γ * A,
             D(R) ~ γ * I + γ * A]
    ce = contact_model(complete(System(seair, t; name = :seair13)))
    @test (:E, :A) in [(tr.from, tr.to) for tr in node_transitions(ce)] && same_field(ce, seair)
    @test any(a -> occursin("of E in D(A) is read numerically: positive at all 41 probe points",
                            a), provenance(ce).assumptions)
    scat = [D(S) ~ -1e-13 * τ * S * I, D(I) ~ 1e-13 * τ * S * I - 1e-13 * δ * S * I,
            D(R) ~ 1e-13 * δ * S * I]
    @test startswith(err(() -> contact_model(complete(System(scat, t; name = :scat13)))),
                     "ArgumentError: contact_model(:scat13): the sign of the coefficient " *
                     "`-1.0e-13δ + 1.0e-13τ` of S*I in D(I) depends on the parameters")
    # floating-point netting cancels: 0.1 + 0.2 − 0.3 = 5.6e-17 in Float64, and the loss 0.3·S·I
    # of D(S) against the gain (0.1 + 0.2)·S·I of D(I) leaves no gain in excess of the loss
    @test 0.1 + 0.2 - 0.3 != 0
    eqn = [D(S) ~ -0.3 * S * I, D(I) ~ 0.1 * S * I + 0.2 * S * I - 0.1 * I, D(R) ~ 0.1 * I]
    cn = contact_model(complete(System(eqn, t; name = :net)))
    @test [(c.recipient, c.infector, c.product, c.rate) for c in contacts(cn)] ==
          [(:S, :I, :I, 0.1 + 0.2)]
    @test [(tr.from, tr.to) for tr in node_transitions(cn)] == [(:I, :R)]
    # and so it does against explicit reactions
    eqr = [D(S) ~ -τ * S * I, D(I) ~ τ * S * I - 0.3 * I, D(R) ~ 0.3 * I]
    cr = contact_model(complete(System(eqr, t; name = :rec));
                       transitions = [(0.1 + 0.2) * I => (:I, :R)])
    @test [(tr.from, tr.to, tr.rate) for tr in node_transitions(cr)] == [(:I, :R, 0.1 + 0.2)]
    # a population whose equations sum to a netting residue is conserved
    eqc = [D(S) ~ -β * S * I / (S + I + R), D(I) ~ β * S * I / (S + I + R) - 0.3 * I,
           D(R) ~ 0.1 * I + 0.2 * I]
    cc = contact_model(complete(System(eqc, t; name = :cons)); rates = :frequency)
    @test rate_convention(cc) == FrequencyDependent() && only(contacts(cc)).rate === :β
end

@testset "explicit reactions must be fluxes of the ODE; negative defaults" begin
    sir = complete(System([D(S) ~ -τ * S * I, D(I) ~ τ * S * I - γ * I, D(R) ~ γ * I], t;
                          name = :sir))
    tail = ": an explicit reaction must be a flux of the ODE, a term that the equation of the " *
           "unknown that makes it loses and that of its product gains"
    head = "ArgumentError: contact_model(:sir): the explicit reactions make "
    # a monomial that the ODE does not have: without the check, S + R → R + R would be paired
    # with an invented reverse contact R + S → S + S that cancels it
    @test err(() -> contact_model(sir; contacts = [τ * S * R => (:S, :R, :R)])) ==
          head * "D(S) lose `τ*S*R`, but D(S) has no term in S*R" * tail
    @test err(() -> contact_model(sir; contacts = [τ * S * I => (:S, :R, :I)])) ==
          head * "D(R) gain `τ*S*I`, but D(R) has no term in S*I" * tail
    # more than the ODE has
    @test err(() -> contact_model(sir; contacts = [2τ * S * I => (:S, :I, :I)])) ==
          head * "D(S) lose `2τ*S*I`, but D(S) loses only `τ*S*I`" * tail
    @test err(() -> contact_model(sir; transitions = [2γ * I => (:I, :R)])) ==
          head * "D(I) lose `2γ*I`, but D(I) loses only `γ*I`" * tail
    # the reactions of the ODE pass, and so does a flux that the ODE nets with another (D(I) =
    # τSI − δSI, tested with S-catalysed recovery above)
    @test isequivalent(contact_model(sir; contacts = [τ * S * I => (:S, :I, :I)],
                                     transitions = [γ * I => (:I, :R)]), sir_model())
    # the rate of an explicit reaction must be positive
    @test err(() -> contact_model(sir; contacts = [-τ * S * I => (:S, :I, :I)])) ==
          "ArgumentError: contact_model(:sir): the explicit contact S + I → I + I has the rate " *
          "`-τ`, which is not positive"
    @test err(() -> contact_model(sir; transitions = [-0.5 * I => (:I, :R)])) ==
          "ArgumentError: contact_model(:sir): the explicit transition I → R has the rate " *
          "`-0.5`, which is not positive"
    # fractions constrained jointly, (1 − q1 − q2)σ, have no sign on the probe box: an error
    # that asks for the reactions of the monomial E; given explicitly, the rate is taken as given
    @parameters q1 q2 m
    @variables I1(t) I2(t) W(t)
    eqf = [D(S) ~ -τ * S * I1, D(E) ~ τ * S * I1 - σ * E, D(I1) ~ q1 * σ * E - γ * I1,
           D(I2) ~ q2 * σ * E - γ * I2, D(A) ~ (1 - q1 - q2) * σ * E - γ * A,
           D(R) ~ γ * I1 + γ * I2 + γ * A]
    cf = complete(System(eqf, t; name = :cf))
    @test err(() -> contact_model(cf)) ==
          "ArgumentError: contact_model(:cf): the sign of the coefficient `σ - q1*σ - q2*σ` of E " *
          "in D(A) depends on the parameters (0.08 at q1 = 0.1, q2 = 0.1, σ = 0.1 but -0.04 at " *
          "q1 = 0.9, q2 = 0.5, σ = 0.1): a rate written as a difference of parameters, such as " *
          "γ − m or (1 − q1 − q2)σ, has no sign on the probe box; pass the reactions explicitly " *
          "with contacts = [flux => (from, to, infector), …] and transitions = [flux => (from, " *
          "to), …], listing every reaction whose flux is proportional to E"
    ccf = contact_model(cf; transitions = [(1 - q1 - q2) * σ * E => (:E, :A)])
    @test sort([(tr.from, tr.to) for tr in node_transitions(ccf)]) ==
          [(:A, :R), (:E, :A), (:E, :I1), (:E, :I2), (:I1, :R), (:I2, :R)]
    @test same_field(ccf, eqf)
    @test "the rate `σ - q1*σ - q2*σ` of the explicit transition E → A is taken as given: its " *
          "sign is not fixed on the probe box" in provenance(ccf).assumptions
    # such a rate is still checked against the ODE
    @test err(() -> contact_model(cf; transitions = [(1 - q1 - q2) * σ * S => (:S, :A)])) ==
          "ArgumentError: contact_model(:cf): the explicit reactions make D(S) lose " *
          "`(σ - q1*σ - q2*σ)*S`, but D(S) has no term in S" * tail
    # a branching written as D(R) = (γ − m)I, D(W) = mI needs both reactions of I
    eqb = [D(S) ~ -τ * S * I, D(I) ~ τ * S * I - γ * I, D(R) ~ (γ - m) * I, D(W) ~ m * I]
    br = complete(System(eqb, t; name = :br))
    @test startswith(err(() -> contact_model(br)),
                     "ArgumentError: contact_model(:br): the sign of the coefficient `-m + γ` of " *
                     "I in D(R) depends on the parameters")
    @test err(() -> contact_model(br; transitions = [m * I => (:I, :W)])) ==
          "ArgumentError: contact_model(:br): the sign of the coefficient `-m + γ` of I in D(I) " *
          "depends on the parameters (0.4 at m = 0.1, γ = 0.5 but -0.4 at m = 0.5, γ = 0.1): a " *
          "rate written as a difference of parameters, such as γ − m or (1 − q1 − q2)σ, has no " *
          "sign on the probe box; pass the reactions explicitly with contacts = [flux => (from, " *
          "to, infector), …] and transitions = [flux => (from, to), …], listing every reaction " *
          "whose flux is proportional to I"
    cb = contact_model(br; transitions = [m * I => (:I, :W), (γ - m) * I => (:I, :R)])
    @test sort([(tr.from, tr.to) for tr in node_transitions(cb)]) == [(:I, :R), (:I, :W)]
    @test same_field(cb, eqb)
    # every parameter is read as positive: a negative default is an error (as p = 2 in (1 − p)σ is)
    @parameters τn = -0.2
    neg = complete(System([D(S) ~ -τn * S * I, D(I) ~ τn * S * I - γ * I, D(R) ~ γ * I], t;
                          name = :neg))
    @test err(() -> contact_model(neg)) ==
          "ArgumentError: contact_model(:neg): the parameter τn has the negative default -0.2: " *
          "the signs of the coefficients are decided for positive parameters (rates, and " *
          "fractions such as p in (1 − p)σ), so a negative rate or fraction cannot be read"
end

@testset "explicit transitions; defaults; as_parameter under MTK" begin
    two = complete(System([D(S) ~ -τ * S * I, D(I) ~ τ * S * I - 2γ * I, D(R1) ~ γ * I,
                           D(R2) ~ γ * I], t; name = :two))
    ce = contact_model(two; transitions = [γ * I => (:I, :R1)])
    @test isequivalent(ce, contact_model(two))
    @test "transition I → R1 at γ: from the `transitions` keyword" in provenance(ce).assumptions
    # an explicit removal that the ODE contradicts leaves D(R2)'s gain unmatched
    @test err(() -> contact_model(two; transitions = [γ * I => (:I, :R1),
                                                      γ * I => (I, nothing)])) ==
          "ArgumentError: contact_model(:two): D(R2) gains `γ*I` but D(I) does not lose it: " *
          "births change the node set; use the ODE itself for mass action (an accumulator such " *
          "as cumulative incidence is not a node state; remove it from the system)"
    @test_throws ArgumentError contact_model(two; transitions = [γ * I => (:I, :Q)])
    @test_throws ArgumentError contact_model(two; transitions = [γ * S * I => (:I, :R1)])
    # defaults from @parameters and from initial_conditions
    @parameters τd = 0.2 γd = 0.25
    sd = complete(System([D(S) ~ -τd * S * I, D(I) ~ τd * S * I - γd * I, D(R) ~ γd * I], t;
                         name = :sd))
    @test parameter_defaults(contact_model(sd)) == Dict(:τd => 0.2, :γd => 0.25)
    si = complete(System([D(S) ~ -τ * S * I, D(I) ~ τ * S * I - γ * I, D(R) ~ γ * I], t;
                         name = :si, initial_conditions = [τ => 0.3]))
    @test parameter_defaults(contact_model(si)) == Dict(:τ => 0.3)
    @test only(contacts(instantiate(contact_model(si), Dict(:γ => 0.1)))).rate == 0.3
    # as_parameter is an MTK parameter once ModelingToolkitBase is loaded (fixes ebm-core #10)
    τp = as_parameter(:τ)
    @test MB.isparameter(τp)
    @test isequal(τp, τ)
    sys = complete(System([D(S) ~ -τp * S * I, D(I) ~ τp * S * I - as_parameter(:γ) * I,
                           D(R) ~ as_parameter(:γ) * I], t; name = :asp))
    @test Set(Symbolics.getname.(MB.parameters(sys))) == Set([:τ, :γ])
    @test Set(Symbolics.getname.(MB.unknowns(sys))) == Set([:S, :I, :R])
end

@testset "zero is exact: a coefficient that vanishes on the probe box is never dropped (§J.3)" begin
    # WP10 review (scratchpad/wp10rev3/probe1-3.jl): a coefficient that is 0 at every probe point
    # but not identically 0 was read as 0 and dropped, with no error and no note.
    # (a) a vaccination switched on at t = 150, when time was probed only up to t = 100: the model
    # had no transition S → V. Time is now probed on [0.1, 1000] (log scale), and a rate that is 0
    # at some probe points and positive at the others is a rate (non-negative)
    eqa = [D(S) ~ -τ * S * I - ν * ifelse(t > 150, 1, 0) * S, D(I) ~ τ * S * I - γ * I,
           D(R) ~ γ * I, D(V) ~ ν * ifelse(t > 150, 1, 0) * S]
    sa = complete(System(eqa, t; name = :sa))
    ca = contact_model(sa; allow_t = true)
    @test [(tr.from, tr.to) for tr in node_transitions(ca)] == [(:S, :V), (:I, :R)]
    va = first(tr.rate for tr in node_transitions(ca) if tr.to === :V)
    @test NEC._uses_time(va)
    @test rate_value(va, Dict(:ν => 0.5); t = 200.0) == 0.5
    @test rate_value(va, Dict(:ν => 0.5); t = 100.0) == 0
    @test same_field(ca, eqa)
    @test "the sign of the coefficient `ν*ifelse(t > 150, 1, 0)` of S in D(V) is read " *
          "numerically: positive at 11 of the 41 probe points and 0 at the other 30, with " *
          "t ∈ [0.1, 1000.0] (log scale) and ν ∈ [0.1, 0.9] (its form alone does not fix it)" in
          provenance(ca).assumptions
    # on a time box that ends before the switch, the coefficient is 0 at every probe point: an
    # error that names it, never a silent 0
    @test err(() -> contact_model(sa; allow_t = true, time_box = (0.1, 100.0))) ==
          "ArgumentError: contact_model(:sa): the coefficient `ν*ifelse(t > 150, 1, 0)` of S in " *
          "D(S) is not provably 0, but it is 0 at all 41 probe points with t ∈ [0.1, 100.0] " *
          "(log scale) and ν ∈ [0.1, 0.9], so its sign cannot be read (a rate that is switched " *
          "on outside the probe box, such as ν*ifelse(t > 150, 1, 0) for t ≤ 100 or " *
          "max(p - 1, 0)*ν for p ≤ 1, is 0 there); a coefficient is read as 0 only when it is " *
          "exactly 0. Pass a time_box (for time-dependent rates) or parameter defaults at which " *
          "it is not 0, simplify it if it is 0, or pass the reactions explicitly with contacts = " *
          "[flux => (from, to, infector), …] and transitions = [flux => (from, to), …], listing " *
          "every reaction whose flux is proportional to S"
    # given explicitly, such a rate is taken as given, and noted
    cx = contact_model(sa; allow_t = true, time_box = (0.1, 100.0),
                       transitions = [ν * ifelse(t > 150, 1, 0) * S => (:S, :V)])
    @test [(tr.from, tr.to) for tr in node_transitions(cx)] == [(:S, :V), (:I, :R)]
    @test same_field(cx, eqa)
    @test "the rate `ν*ifelse(t > 150, 1, 0)` of the explicit transition S → V is taken as " *
          "given: it is not provably 0, but it is 0 at all 41 probe points with " *
          "t ∈ [0.1, 100.0] (log scale) and ν ∈ [0.1, 0.9]" in provenance(cx).assumptions
    # a positive sign read from the probes is noted for an explicit rate as well (WP10fix
    # review: only the rates taken as given were noted)
    cy = contact_model(sa; allow_t = true,
                       transitions = [ν * ifelse(t > 150, 1, 0) * S => (:S, :V)])
    @test "the sign of the rate `ν*ifelse(t > 150, 1, 0)` of the explicit transition S → V is " *
          "read numerically: positive at 11 of the 41 probe points and 0 at the other 30, with " *
          "t ∈ [0.1, 1000.0] (log scale) and ν ∈ [0.1, 0.9] (its form alone does not fix it)" in
          provenance(cy).assumptions
    # a rate positive by its form needs no note
    cz0 = contact_model(sa; allow_t = true, transitions = [γ * I => (:I, :R)])
    @test !any(n -> occursin("of the explicit transition I → R", n), provenance(cz0).assumptions)
    # a coefficient that is identically 0 for p > 0 but that the simplifier cannot prove to be 0
    # is refused, as not provably 0 (WP10fix review: the message said "not identically 0")
    eqg = [D(S) ~ -τ * S * I + (exp(log(p)) - p) * ν * S, D(I) ~ τ * S * I - γ * I, D(R) ~ γ * I]
    @test startswith(err(() -> contact_model(complete(System(eqg, t; name = :sg)))),
                     "ArgumentError: contact_model(:sg): the coefficient `p*ν - ν*exp(log(p))` " *
                     "of S in D(S) is not provably 0, but it is 0 at all 41 probe points")
    @test_throws ArgumentError contact_model(sa; allow_t = true, time_box = (100.0, 10.0))
    @test_throws ArgumentError contact_model(sa; allow_t = true, time_box = (-1.0, 10.0))
    # (b) a contact switched on after t = 200: the model had no contacts at all
    eqb = [D(S) ~ -τ * max(t - 200, 0) * S * I, D(I) ~ τ * max(t - 200, 0) * S * I - γ * I,
           D(R) ~ γ * I]
    sb = complete(System(eqb, t; name = :sb))
    cb = contact_model(sb; allow_t = true)
    @test only(contacts(cb)).rate == :(τ * max(t - 200, 0)) && same_field(cb, eqb)
    @test startswith(err(() -> contact_model(sb; allow_t = true, time_box = (0.1, 100.0))),
                     "ArgumentError: contact_model(:sb): the coefficient `-τ*max(-200 + t, 0)` " *
                     "of S*I in D(S) is not provably 0, but it is 0 at all 41 probe points " *
                     "with t ∈ [0.1, 100.0] (log scale) and τ ∈ [0.1, 0.9], so its sign cannot " *
                     "be read")
    # (c) 0 on the parameter box but positive at its default (the default probe was skipped on
    # this path): the default gives the sign, and the decision is noted
    @parameters νv = 2.0 νw
    eqc(nu) = [D(S) ~ -τ * S * I - max(nu - 1, 0) * S, D(I) ~ τ * S * I - γ * I, D(R) ~ γ * I,
               D(V) ~ max(nu - 1, 0) * S]
    cc = contact_model(complete(System(eqc(νv), t; name = :sc)))
    @test (:S, :V, :(max(νv - 1, 0))) in [(tr.from, tr.to, tr.rate) for tr in node_transitions(cc)]
    @test same_field(cc, eqc(νv))
    @test "the sign of the coefficient `max(-1 + νv, 0)` of S in D(V) is read numerically: 0 at " *
          "all 35 probe points with νv ∈ [0.1, 0.9] but 1.0 at the parameter defaults " *
          "(νv = 2.0) (its form alone does not fix it)" in provenance(cc).assumptions
    # without a default nothing gives it a sign: an error
    @test startswith(err(() -> contact_model(complete(System(eqc(νw), t; name = :sw)))),
                     "ArgumentError: contact_model(:sw): the coefficient `max(-1 + νw, 0)` of S " *
                     "in D(S) is not provably 0, but it is 0 at all 35 probe points with " *
                     "νw ∈ [0.1, 0.9], so its sign cannot be read")
    # an exact 0 is still 0, after folding: (exp(0) − 1)γ·S is no flux (simplify alone leaves
    # (−1 + exp(0))γ, which the probes used to read as 0)
    z = exp(τ - τ)
    @test string(Symbolics.simplify(Symbolics.expand((z - 1) * γ))) != "0"
    eqz = [D(S) ~ -τ * S * I + (z - 1) * γ * S, D(I) ~ τ * S * I - γ * I, D(R) ~ γ * I,
           D(V) ~ (1 - z) * γ * S]
    cz = contact_model(complete(System(eqz, t; name = :sz)))
    @test isequivalent(cz, ContactModel(:x; species = [:S, :I, :R, :V],
                                        contacts = [Contact(:S, :I, :I, :τ)],
                                        transitions = [NodeTransition(:I, :R, :γ)]))
    # a rate need only be non-negative: (τ − δ)² is 0 on the diagonal of the box, positive off it
    @parameters δ
    eqq = [D(S) ~ -(τ - δ)^2 * S * I, D(I) ~ (τ - δ)^2 * S * I - γ * I, D(R) ~ γ * I]
    cq = contact_model(complete(System(eqq, t; name = :sq)))
    @test length(contacts(cq)) == 1 && same_field(cq, eqq)
    @test "the sign of the coefficient `δ^2 - 2δ*τ + τ^2` of S*I in D(I) is read numerically: " *
          "positive at 38 of the 41 probe points and 0 at the other 3, with δ, τ ∈ [0.1, 0.9] " *
          "(its form alone does not fix it)" in provenance(cq).assumptions
    # a seasonal rate that is negative for t in (182.5, 365) was accepted as positive (the box
    # stopped at 100); on the default time box it is an error, and on half a year a rate
    season = complete(System([D(S) ~ -τ * sin(2π * t / 365) * S * I,
                              D(I) ~ τ * sin(2π * t / 365) * S * I - γ * I, D(R) ~ γ * I], t;
                             name = :season))
    msg = err(() -> contact_model(season; allow_t = true))
    @test startswith(msg, "ArgumentError: contact_model(:season): the sign of the coefficient ")
    @test occursin("depends on the parameters", msg)
    @test occursin("a time-dependent rate cannot change sign on the time box t ∈ [0.1, 1000.0] " *
                   "(pass time_box = the time span of the solution if it is shorter)", msg)
    chalf = contact_model(season; allow_t = true, time_box = (0.1, 180.0))
    @test NEC._uses_time(only(contacts(chalf)).rate)
end

@testset "time is t whatever the independent variable is called; residues; numeric population" begin
    # the E25 failure class: with an independent variable s, the rate τ*exp(-s) was read with s as
    # a constant parameter (not time-dependent, and s in rate_parameters)
    @independent_variables s
    @variables Ss(s) Is(s) Rs(s)
    Ds = Differential(s)
    eqs_ = [Ds(Ss) ~ -τ * exp(-s) * Ss * Is, Ds(Is) ~ τ * exp(-s) * Ss * Is - γ * Is,
            Ds(Rs) ~ γ * Is]
    sys_s = complete(System(eqs_, s; name = :ivs))
    @test startswith(err(() -> contact_model(sys_s)),
                     "ArgumentError: contact_model(:ivs): the right-hand side of D(Ss) " *
                     "depends on t explicitly")
    cs = contact_model(sys_s; allow_t = true)
    r = only(contacts(cs)).rate
    @test r == :(τ * exp(-t)) && NEC._uses_time(r)
    @test Set(NEC._parameter_name.(rate_parameters(cs))) == Set([:τ, :γ])
    @test rate_value(r, Dict(:τ => 2.0); t = log(2.0)) ≈ 1.0
    @test_throws ArgumentError instantiate(cs, Dict(:τ => 2.0, :γ => 1.0))
    @test "the rates depend on t (allow_t = true): time-dependent rates are for the ODE back " *
          "ends only; the independent variable s is written t" in provenance(cs).assumptions
    fs = SymbolicODE(:ivs; states = [Ss, Is, Rs], rhs = [eq.rhs for eq in eqs_])
    @test vector_fields_equal(fs, mass_action(cs); rename = Dict(:s => :t))
    # a parameter may not then be called t
    tp = ModelingToolkit.toparam(Symbolics.variable(:t))
    @test err(() -> contact_model(complete(System([Ds(Ss) ~ -tp * Ss * Is, Ds(Is) ~ tp * Ss * Is],
                                                  s; name = :tp)))) ==
          "ArgumentError: contact_model(:tp): the system's independent variable is s and a " *
          "parameter is called t; in the IR, t is time (the independent variable), so rename " *
          "the parameter"
    # a floating-point residue read as 0 is noted (a removal 1e-14·I next to 0.1·I, within 1e-12
    # of the gross coefficient, is read as netting)
    eqf = [D(S) ~ -τ * S * I, D(I) ~ τ * S * I - 0.1 * I - 1e-14 * I, D(R) ~ 0.1 * I]
    cf = contact_model(complete(System(eqf, t; name = :resid)))
    @test [(tr.from, tr.to) for tr in node_transitions(cf)] == [(:I, :R)]
    @test any(a -> startswith(a, "floating-point netting: the loss of I less its gains is `1.0") &&
                   endswith(a, "e-14*I`, at most 1.0e-12 of the sum 0.2 of the absolute values " *
                               "of its terms, and is read as 0"), provenance(cf).assumptions)
    # rates = :frequency with a numeric population (the error said "not of the form β/1000")
    eqh = [D(S) ~ -β * S * I / 1000, D(I) ~ β * S * I / 1000 - γ * I, D(R) ~ γ * I]
    sh = complete(System(eqh, t; name = :fh))
    for pop in (1000, 1000.0)
        ch = contact_model(sh; rates = :frequency, population = pop)
        @test rate_convention(ch) == FrequencyDependent() && only(contacts(ch)).rate === :β
        @test "contact rates of the form β/1000 read as frequency-dependent with population " *
              "1000: the stored constant is β (FrequencyDependent)" in provenance(ch).assumptions
    end
    @test_throws ArgumentError contact_model(sh; rates = :frequency, population = -1)
end

@testset "round trip contact_model(System(mass_action(cm))) ≅ cm" begin
    for cm in (sir_model(), seir_model(), sis_model(), sirs_model(), seair_model(),
               twostrain_model(), sirv_model())
        back = contact_model(ode_system(mass_action(cm)))
        @test isequivalent(back, cm)
        @test provenance(back).method === :flux_pairing
    end
    # WP6 corpus: contact tracing (a contact whose product is not infectious) comes back as it
    # is; S-catalysed recovery (node_contact) is refused without the escape hatch, since D(I)
    # nets τSI − δSI, and comes back with it
    trace = ContactModel(:trace; contacts = [Contact(:S, :I, :I, :τ), Contact(:S, :D, :Q, :α)],
                         transitions = [NodeTransition(:I, :D, :γ), NodeTransition(:D, :R, :δ)])
    bt = contact_model(ode_system(mass_action(trace)))
    @test isequivalent(bt, trace)
    @test typing(bt).theory === :T_EB
    scat = ContactModel(:scat; contacts = [Contact(:S, :I, :I, :τ), Contact(:I, :S, :R, :δ)],
                        transitions = [NodeTransition(:I, :R, :γ)])
    ms = mass_action(scat)
    ss = ode_system(ms)
    @test startswith(err(() -> contact_model(ss)),
                     "ArgumentError: contact_model(:scat_mass_action): the sign of the " *
                     "coefficient `-δ + τ` of S*I in D(I) depends on the parameters")
    st = Dict(zip(state_names(ms), ms.states))
    bs = contact_model(ss; contacts = [as_parameter(:δ) * st[:I] * st[:S] => (:I, :R, :S)])
    @test isequivalent(bs, scat)
    @test last.(typing(bs).reaction_types) == [:contact, :node_contact, :progress]
    # κ: MA(c_κ P) comes back with κ τ as the per-contact rate
    back5 = contact_model(ode_system(mass_action(sir_model(); κ = 5)))
    @test isequivalent(back5, scale_contact_rates(sir_model(), 5))
    # the equations of an MTK system are a SymbolicODE whose field is the model's mass action
    sir = complete(System([D(S) ~ -τ * S * I, D(I) ~ τ * S * I - γ * I, D(R) ~ γ * I], t;
                          name = :sir))
    eqs = MB.equations(sir)
    ode = SymbolicODE(:from_mtk; states = MB.unknowns(sir), rhs = [eq.rhs for eq in eqs])
    @test vector_fields_equal(ode, mass_action(sir_model()); rename = :none)
end
