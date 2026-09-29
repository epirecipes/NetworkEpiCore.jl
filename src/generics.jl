# Owner: WP5 (DESIGN_NetworkEpiCore.md §A.2, "Generic functions owned by NEC").
#
# Function stubs shared by NetworkEpiCore (NEC), EdgeBasedModels (EBM), NodeBasedModels (NBM)
# and NetworkOutbreaks (NO). A function is stubbed here only if at least two packages implement
# methods on their own types (§A.2, decision H2); single-package verbs stay in their package.
#
# Rules for everyone else:
# - Never redeclare these names (`function f end`) or re-`export` them from another NEC file;
#   add methods, optionally with a docstring on the method signature.
# - EBM, NBM and NO `import NetworkEpiCore: f` (or `using NetworkEpiCore: f`), add methods on their
#   own types, and re-export the same binding. Two packages must never define the same method
#   signature on an NEC binding (that is method overwriting across packages). Today EBM and NBM
#   both define `base_compartment_of(::Symbol)` and `infection_count_of(::Symbol)`: at most one
#   such method may exist, and it belongs in NEC (ir/transforms.jl), not in either package.
# - Nothing in this file has methods: stubs only. Method definitions here would collide with the
#   owning work packages (method overwriting is an error during precompilation).

export basic_reproduction_number, next_generation_matrix, transmissibility
export final_size, epidemic_probability
export epidemic_threshold, early_growth_rate, disease_free_equilibrium
export default_initial_conditions, solve_epidemic, model_curves, symbolic_ode
export compartment, compartments, population_fraction
export mean_degree, excess_degree, pgf, pgf_derivative, clustering_coefficient
export contact_model, mass_action, stratify
export with_reinfection_counting, reinfection_totals, base_compartment_of, infection_count_of
export reinfection_histogram
export verify, pushforward
export canonical_text

# ---------------------------------------------------------------------------------------------
# Threshold quantities and final size
# ---------------------------------------------------------------------------------------------

"""
    basic_reproduction_number(cm::ContactModel, net::NetworkDescriptor, p) -> Float64
    basic_reproduction_number(sys)

Basic reproduction number R₀, the spectral radius ρ(K) of the next-generation matrix
(see [`next_generation_matrix`](@ref)).

- NEC: numeric `(cm, net, p)` for any T_EB model on a configuration, well-mixed, MFSH,
  multitype, degree-correlated, multiplex or neighbour-exchange (DFD) descriptor, with parameter
  values `p` (a `Dict{Symbol}` or `NamedTuple`; model defaults fill the gaps) and rates converted
  to per-contact τ by the model's rate convention. On a configuration network with a single
  entry state, R₀ = T·κ_ex, where T is the per-edge [`transmissibility`](@ref) and
  κ_ex = ψ''(1)/ψ'(1) the mean excess degree.
- EBM: `(sys::EdgeModelSystem; p)`, computed from the lifted edge-based field (symbolic where it
  has a closed form, e.g. with `p = nothing`; parameters are a keyword); NBM: `(::PairwiseSystem)`;
  legacy methods are kept.

For a multiplex network R₀ = ρ(K) over (layer, entry) blocks, never the sum of layer R₀'s. For a
multitype network the blocks are (edge kind b→a, entry state) (§J.5), which reduce to
(type, entry) blocks only for Poisson or `SplitDegrees` blocks.
"""
function basic_reproduction_number end

"""
    next_generation_matrix(cm::ContactModel, net::NetworkDescriptor, p) -> Matrix{Float64}
    next_generation_matrix(sys)

Next-generation matrix K whose rows and columns are the types of a newly infected node: its
entry state (the product of a Sus-recipient contact) and, on structured descriptors, the kind
of edge it was infected along, as listed by `next_generation_labels(cm, net)`:

- configuration and well-mixed descriptors: one row per entry state X;
- `MultiplexNetwork`: (layer, entry) blocks;
- `MultitypeNetwork` and `DegreeCorrelatedNetwork`: (edge kind b→a, entry) blocks, with the
  offspring factor X[c,b,a] = `excess_contacts(net)[c,b,a]` = ∂_c∂_aψ_b(1)/∂_cψ_b(1) (§J.5).
  They reduce to (type, entry) blocks only when X[c,b,a] does not depend on c (Poisson or
  `SplitDegrees` blocks); for other blocks the (type, entry) shortcut is wrong.

Two cases:

- Configuration network: K_{X←Y} = κ_ex Σ_{r: entry X} T_r(Y), with T_r(Y) from
  [`transmissibility`](@ref).
- `WellMixed(κ)`: K_{X←Y} = κ Σ_{r: entry X} τ_r [V⁻¹ e_Y]_{J_r}.

Here V is the **outflow matrix** of the node transitions restricted to the non-susceptible
species, in the sign convention of van den Driessche & Watmough (2002): V = −Q, where Q is the
generator (so V has the positive total exit rates on its diagonal and minus the transition
rates off it). For SIR, V = γ and τ[V⁻¹]_{II} = τ/γ.

NEC implements the numeric `(cm, net, p)` form; EBM (`(sys::EdgeModelSystem; p)`, from the
lifted field, symbolic where closed-form) and NBM add methods on their system types.
"""
function next_generation_matrix end

"""
    transmissibility(cm::ContactModel, net::NetworkDescriptor, p)
    transmissibility(sys)

Per-edge transmissibility: the probability that a node entering state Y eventually transmits
across one given edge through contact r, T_r(Y) = τ_r [(V + B)⁻¹ e_Y]_{J_r}, where V is the
outflow matrix of the node transitions on the non-susceptible species (V = −Q for the generator
Q: positive exit rates on the diagonal, the convention of van den Driessche & Watmough 2002)
and B = diag(Σ_{r: J_r = J} τ_r) is the rate at which transmission along the edge ends the
edge's infectious period. For SIR, T = τ/(τ + γ); for n Erlang stages (diagonal nγ),
T_n = 1 − (nγ/(τ + nγ))ⁿ.

NEC implements the numeric `(cm, net, p)` form; EBM (`(sys::EdgeModelSystem; p)`, from the
lifted field, symbolic where closed-form) and NBM add methods on their system types.
"""
function transmissibility end

"""
    final_size(cm::ContactModel, net::NetworkDescriptor, p; initial = nothing, N = nothing)
        -> Float64
    final_size(sys, ...)
    final_size(traj::OutbreakTrajectory)   # NetworkOutbreaks
    final_size(ens::OutbreakEnsemble)      # NetworkOutbreaks

Final size: the fraction of nodes **ever infected, including the seeds** (§E.2); the limit of
the `:cumulative` observable. Infection status is structural (§J.8,
[`infected_species`](@ref)): seeds count when they are placed in an infected compartment (not
R, a vaccinated V or a traced Q), and tracing, quarantine and awareness transitions keep a
node's status.

- NEC: numeric `(cm, net, p)` for T_EB models with a single entry state (per node type) and no
  exits from the susceptible class, on configuration, well-mixed, MFSH, multiplex, multitype
  and degree-correlated descriptors. On a configuration network it solves
  θ∞ = Σ_X ρ_X(1 − T(X)) + q[1 − T + T ψ'(θ∞)/ψ'(1)] and R∞ = 1 − q ψ(θ∞), where
  q = 1 − Σ_X ρ_X. `initial` is a `SeedSpec` (`SeedCount`/`SeedNodes` need `N`); with
  `initial = nothing` the result is the large-outbreak limit of a vanishing seed, exactly 0 at
  or below threshold. Several entry states, exits and neighbour exchange are refused: solve the
  edge-based ODE.
- EBM: `(sys::EdgeModelSystem; p, initial, method)`, by NEC's fixed point where it applies
  and otherwise by integrating the edge-based ODE to large t; legacy methods are kept.
- NO: `(::OutbreakTrajectory)` and `(::OutbreakEnsemble)` give the fraction of nodes ever
  infected (structural, including the seeds; §J.8), not the fraction that ever left the
  susceptible class.
"""
function final_size end

"""
    epidemic_probability(sys, ...)
    epidemic_probability(ens::OutbreakEnsemble)   # NetworkOutbreaks

Probability that an outbreak started by a single seed becomes a major epidemic.

- EBM: `(sys::EdgeModelSystem; p, from)`, the infector-side mixed-binomial branching-process
  formula (Ball 2021, §2.4), on configuration and well-mixed systems only.
- NO: the empirical fraction of major outbreaks in an ensemble (with a Wilson interval where
  the method documents it).

NEC defines no method.
"""
function epidemic_probability end

"""
    epidemic_threshold(sys, ...)

Critical per-contact rate τ_c at which the disease-free state loses stability, for example
τ_c = γ/(k − 1) for the homogeneous SIS pairwise model on a k-regular network. EBM and NBM add
methods on their model and system types; NEC defines no method.
"""
function epidemic_threshold end

"""
    early_growth_rate(cm::ContactModel, net::NetworkDescriptor, p) -> Float64
    early_growth_rate(sys, ...)

Initial exponential growth rate r: the leading eigenvalue of the system linearised at the
disease-free state. For SIR on a configuration network, r = τ(κ_ex − 1) − γ.

NEC implements the numeric `(cm, net, p)` form; EBM (`(sys::EdgeModelSystem; p)`, from the
lifted field, symbolic where closed-form) and NBM add methods on their types.
"""
function early_growth_rate end

"""
    disease_free_equilibrium(sys, ...)

The disease-free equilibrium of a lowered system, in that system's coordinates. EBM and NBM add
methods on their model and system types; NEC defines no method.
"""
function disease_free_equilibrium end

# ---------------------------------------------------------------------------------------------
# Solving and observing lowered systems
# ---------------------------------------------------------------------------------------------

"""
    default_initial_conditions(sys; initial = nothing, kw...)

Initial conditions of a lowered system. `initial` is a `SeedSpec` (for example
`SeedFraction(:I => 0.01)`); when it is `nothing`, the **unique entry state** of the
infections is seeded (`default_seed_state`: I for SIR, E for SEIR, I₁ for Erlang staging and
after reinfection counting, I for a tracing model whose traced Q is not infected), and a model
whose entry is not unique (two strains, stratified models) requires an explicit `initial`
(§E.2). On a multitype network `SeedFraction(:I_a => ρ)` is a fraction of **all** N nodes,
placed on type a (the within-type fraction is ρ/n_a; §J.6). EBM uses θ(0) = 1, ξ(0) = 1,
φ_X(0) = pop_X(0) = ρ_X; NBM uses the image of that initial condition under π^PW. EBM and NBM
add methods; NEC defines no method.
"""
function default_initial_conditions end

"""
    solve_epidemic(sys; p, initial, tspan, saveat, kw...)
    solve_epidemic(sys, sc::Scenario; kw...)

Solve a lowered system. The scenario form takes the parameters, seeding, time span and save
grid from `sc`. EBM and NBM add methods; NEC never solves an ODE.
"""
function solve_epidemic end

"""
    model_curves(sys, sol; t, label) -> ModelCurves

Evaluate the observables of a solved system (every species, `:infectious` = the sum of the
infectors, and `:cumulative`, the fraction ever infected including the infected seeds; see
[`Scenario`](@ref)) on the time grid `t`, and return
`ModelCurves(t, Dict(obs => values); label, representation)`, which `compare` and the plot
recipes accept. `representation` is one of `:edge_based`, `:pairwise`, `:pgf_closure`,
`:s_anchored`, `:mass_action`, `:mean_field`, `:individual` or `:pair`, and fixes the plot
style. EBM and NBM add methods; NEC defines the `ModelCurves` type.

The generic is `model_curves`, not `curves` (§J.1): Plots exports `curves`, which would make the
name ambiguous wherever Plots is loaded (§A.8).
"""
function model_curves end

"""
    symbolic_ode(cm::ContactModel; κ = 1) -> SymbolicODE      # NetworkEpiCoreSymbolicsExt
    symbolic_ode(sys) -> SymbolicODE

A closed `SymbolicODE` (an object of the category Dyn, §D.3).

- NEC (Symbolics extension): the mass-action ODE of c_κ P, the model with every contact rate
  multiplied by κ.
- EBM: the uncompiled edge-based vector field of an assembled system (`metadata[:raw]`).
- NBM: the pairwise vector field of a `PairwiseSystem`.
"""
function symbolic_ode end

"""
    compartment(sys, sol, X::Symbol) -> Vector{Float64}
    compartment(result, X::Symbol)

Time series of the population fraction in compartment `X`. Systems use the `(sys, sol, X)`
argument order (the legacy EBM `(sol, sys, X)` order is deprecated); result objects such as NO
trajectories and ensembles use `(result, X)`. EBM, NBM and NO add methods.
"""
function compartment end

"""
    compartments(sys, sol, Xs::AbstractVector{Symbol})
    compartments(result, Xs::AbstractVector{Symbol})

Several compartments at once; see [`compartment`](@ref) for the argument-order convention.
EBM, NBM and NO add methods.
"""
function compartments end

"""
    population_fraction(sys, sol, X::Symbol)
    population_fraction(result, X::Symbol)

Fraction of the population in `X`, summed over any strata, stages or infection counts that
refine `X`; see [`compartment`](@ref) for the argument-order convention. EBM, NBM and NO add
methods.
"""
function population_fraction end

# ---------------------------------------------------------------------------------------------
# Network summaries
# ---------------------------------------------------------------------------------------------

"""
    mean_degree(d::DegreeDistribution)
    mean_degree(net::NetworkDescriptor)

Mean degree ⟨k⟩ = ψ'(1). For `WellMixed(κ)` it is κ; for a configuration network, the mean of
its degree distribution. This is the ⟨k⟩_net that rate conventions divide by (§B.6), and
NO uses the nominal value, never the realised one. NEC implements it for degree distributions
and descriptors; EBM adds `DegreePGF` methods and NBM `NetworkStructure` methods.
"""
function mean_degree end

"""
    excess_degree(d::DegreeDistribution)
    excess_degree(net::NetworkDescriptor)

Mean excess degree κ_ex = ψ''(1)/ψ'(1): the expected number of other edges of a node reached
along a random edge. NEC implements it for degree distributions and descriptors; EBM and NBM add
methods on their legacy network types.
"""
function excess_degree end

"""
    pgf(d::DegreeDistribution, x)

Probability generating function ψ(x) = Σ_k p_k x^k, in closed form for every family and generic
in `x` (a `Real`, a `Symbolics.Num` or a dual number), for example
`pgf(PoissonDegree(μ), x) = exp(μ(x − 1))`. NEC implements it for degree distributions; EBM adds
methods for its legacy PGF types.
"""
function pgf end

"""
    pgf_derivative(d::DegreeDistribution, x, n::Integer)

The n-th derivative ψ⁽ⁿ⁾(x) of the degree PGF, in closed form for each family (polynomial
coefficients for `EmpiricalDegree`), so that NEC never differentiates symbolically. EBM adds
methods for its legacy PGF types.
"""
function pgf_derivative end

"""
    clustering_coefficient(net)

Clustering coefficient. For `ClusteredNetwork` it is 2E[t]/E[k(k − 1)] with k = s + 2t
(s single stubs, t triangle corners): 2/15 for `ClusteredNetwork(RegularDegree(2),
RegularDegree(2))`. The Graphs extension measures it on an `ExplicitGraph`. EBM adds a
`ClusteredPGF` method; NBM networks use it as the Keeling closure's ϕ.
"""
function clustering_coefficient end

# ---------------------------------------------------------------------------------------------
# Models: front ends, reverse maps, syntax transforms
# ---------------------------------------------------------------------------------------------

"""
    contact_model(x; kw...) -> ContactModel

Convert a model description to the intermediate representation `ContactModel`: contacts
s + J → X + J at per-contact rate τ and node transitions X → Y | ∅.

- NEC: the identity on a `ContactModel`.
- `NetworkEpiCoreCatalystExt`: `contact_model(rn::Catalyst.ReactionSystem; susceptible,
  transmission, rates, population, merge_duplicates)` (§B.4).
- `NetworkEpiCoreMTKExt`: `contact_model(sys::ModelingToolkitBase.System; …)` by flux pairing
  (§B.5).
- EBM: legacy `DiseaseProgression` and `StaticConfigurationModel`; NBM: legacy
  `CompartmentalModel`.

Every back end calls `contact_model` implicitly, so `edge_based(rn, net)`,
`node_based(rn, net)` and `simulate(rn, net; …)` accept any of these.
"""
function contact_model end

"""
    mass_action(cm::ContactModel; κ = 1) -> SymbolicODE        # NetworkEpiCoreSymbolicsExt
    mass_action(ebcm; form)                                     # EdgeBasedModels

Mass action ("back to mass action", §D.5).

- NEC (Symbolics extension): the mass-action ODE of c_κ P on the model's own species.
- EBM: the reverse maps of an edge-based system, `form ∈ (:exact, :edge, :general, :limit,
  :calibrated)`, each returned with its semiconjugacy and exactness label (for example
  `form = :edge` is Rempała's quotient MA(μτ, γ + τ), whose "I" is φ_I).
- NBM: `(::PairwiseSystem)` throws an error that points to
  `node_based(cm, WellMixed(κ); closure = MeanFieldClosure())`.
"""
function mass_action end

"""
    stratify(cm::ContactModel, st::Strata; contact_rates = :same, transition_rates = :same)

Stratify a model by fixed node attributes: the typed product P ×_T Q over T_net (Libkind et al.
2022, §3.2). Contacts become (s,a) + (J,b) → (X,a) + (J,b) with rates from `contact_rates`
(`:same`, a `Dict`, or a function `(a, b) -> rate` evaluated at construction), transitions
become (X,a) → (Y,a), and there are no transitions between strata. The network semantics needs
a typed network (`sbm_network`, `unstructured`). One stratum is the identity.

NEC implements the `ContactModel` method; EBM's legacy `stratify(::OpenEBCM, …)` throws a
migration error because it discarded the degree distribution.
"""
function stratify end

"""
    with_reinfection_counting(cm::ContactModel, L::Integer) -> ContactModel

Refine each species X into X_p by infection count p, saturating at `L`, and record the
provenance in the model's labels. The mass-action and CTMC lumpings back to `cm` are exact (M12);
the result has an arrow into a susceptible class, so it is a T_net model for the node-based and
stochastic back ends only. NEC implements the `ContactModel` method; the EBM and NBM methods on
legacy types are deprecated.
"""
function with_reinfection_counting end

"""
    reinfection_totals(sys, sol) -> Dict{Symbol,Vector{Float64}}

Sum a reinfection-counted solution back to the base compartments (the lumping of
[`with_reinfection_counting`](@ref)). NEC implements the `ContactModel`-level bookkeeping; NBM
adds `(::PairwiseSystem, sol)`; the EBM method is deprecated.
"""
function reinfection_totals end

"""
    base_compartment_of(cm::ContactModel, X::Symbol) -> Symbol

The base compartment of a refined species (`:S` for `:S_2`), read from the model's
`SpeciesLabel`s rather than parsed from the name. NEC implements the `ContactModel` method; the
EBM and NBM legacy methods are deprecated.
"""
function base_compartment_of end

"""
    infection_count_of(cm::ContactModel, X::Symbol) -> Union{Int,Nothing}

The infection count of a reinfection-counted species (`2` for `:S_2`), read from the model's
`SpeciesLabel`s; `nothing` if `X` is not reinfection-counted. NEC implements the `ContactModel`
method; the EBM and NBM legacy methods are deprecated.
"""
function infection_count_of end

"""
    reinfection_histogram(traj::OutbreakTrajectory; L)   # NetworkOutbreaks

Distribution of the number of infections per node along a stochastic trajectory. NO implements
it; the NBM method on its legacy SSA result is deprecated. NEC defines no method.
"""
function reinfection_histogram end

# ---------------------------------------------------------------------------------------------
# Morphisms (implemented by NetworkEpiCoreSymbolicsExt)
# ---------------------------------------------------------------------------------------------

"""
    verify(m::Semiconjugacy; method = :auto, probes = 16, rng_seed = 1, rtol = 1e-10)
        -> VerificationResult

Check the semiconjugacy identity Dπ·F = G∘π of a morphism m: F → G.

- `:symbolic`: Jπ·F − G∘π, substituted with `fold = Val(true)`, expanded and simplified, must
  be identically zero.
- `:numeric`: seeded random probes (source states and parameters drawn from the source's
  `domain`, default boxes (0.05, 0.95) for states, (0.1, 1.0) for parameters and (0.1, 1000)
  on a log scale for time t). The result is ok only when the largest relative residual
  ‖Jπ·F − G∘π‖∞ / max(‖Jπ·F‖∞, ‖G∘π‖∞) at the probes is at most `rtol` **and** the probes are
  evidence that every component is 0: in each component that is not exactly 0, every term of
  the residual that does not cancel must be non-zero at some probe point (a term such as
  ν·ifelse(t > 150, 1, 0) on a box of t below 150, or max(a − 2, 0) for a below 2, is not seen),
  and the cancellation must hold when each non-analytic part (max, min, abs, ifelse, …; every
  function other than the arithmetic operations, powers, exp, log, sqrt and the trigonometric
  and hyperbolic functions) is replaced by an unknown of either sign and of magnitude 0.1 to
  1000, drawn afresh at every probe. Otherwise the result is not ok. So −(a + b)x against
  −ax − bx + max(a − 2, 0)x is not ok (both sides agree on the default box of a, but not for
  a > 2), while a residual max(a − 2, 0)·(sin²b + cos²b − 1)x is 0 whatever the value of the max,
  and is ok. The check is conservative: an identity that holds only for the values the part can
  take (sqrt(max(u, 0)²) = max(u, 0)) is not ok either; write it without the part.
- `:auto`: symbolic first; numeric if the residual is not provably zero or the source has more
  than 50 states.

Limitation: the numeric probes confirm an analytic identity on the probe box (and on the
connected region around it where the residual stays analytic), not across a branch point
outside it: sqrt((2 − a)²)y against (2 − a)y is ok on the default box a ∈ (0.1, 1.0), although
the two differ for a > 2. The default parameter box is narrow (rates and κ above 1 are common),
so give the source a `domain` that covers the parameter values the morphism is claimed for.

Implemented by `NetworkEpiCoreSymbolicsExt` (load Symbolics), whose method docstring has the
details.
"""
function verify end

"""
    pushforward(m::Semiconjugacy, sol, tgrid)

Map a source trajectory to the target coordinates of `m` on `tgrid`, so that both sides of a
morphism can be plotted together. Implemented by `NetworkEpiCoreSymbolicsExt` (load Symbolics).
"""
function pushforward end

# ---------------------------------------------------------------------------------------------
# Canonical text (shared by networks/, seeding.jl and scenarios/; not in the cross-package table)
# ---------------------------------------------------------------------------------------------

"""
    canonical_text(io::IO, x)
    canonical_text(x) -> String

A canonical, versioned, line-based text form used for hashing (§E.4): keys sorted, explicit
field names, every real number printed with `@sprintf("%.17g", x)`, rates as their canonical
text, and never `repr` or `Base.hash`. Degree distributions and descriptors (networks/),
seeding specifications (seeding.jl), rates and models, `SimConfig` and `Scenario`
(scenarios/canonical_text.jl) add methods; `scenario_hash` is the SHA-256 of the scenario's
canonical text.
"""
function canonical_text end
