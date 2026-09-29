# NetworkEpiCore.jl

The shared core of three packages for epidemics on networks:

| package | verb | what it does with a model and a network |
|---|---|---|
| [EdgeBasedModels.jl](../EdgeBasedModels.jl) | `edge_based` | lifts the model to an edge-based compartmental ODE (Miller–Slim–Volz), the exact large-N limit on configuration-model networks |
| [NodeBasedModels.jl](../NodeBasedModels.jl) | `node_based` | closes a pairwise, PGF-closure, mean-field, individual-, pair-, motif- or neighbourhood-based ODE over it |
| [NetworkOutbreaks.jl](../NetworkOutbreaks.jl) | `simulate` | samples graphs from the network and runs exact stochastic simulations on them |

NetworkEpiCore (NEC) holds what the three packages share:

- **One model object, `ContactModel`.** It has contacts `s + J → X + J` at a **per-contact
  (per-edge) rate τ** (β is kept for mass-action rates) and node transitions `X → Y | ∅`. It can be
  built directly (`ContactModel`, `Contact`, `NodeTransition`), from `sir_model()`,
  `seir_model()`, `seair_model()`, `sis_model()`, `sirs_model()`, `sirv_model()` or
  `twostrain_model()`, or through `contact_model` from Catalyst and ModelingToolkit models. The
  route does not matter: `isequivalent` compares the results.
- **Typing.** A model is typed over the theories T_EB ⊂ T_net. `typing`, `admissibility` and
  `require_admissible` decide which back ends accept it. The edge-based lift refuses SIS and
  SIRS, for example, and the error names the back ends that accept them.
- **One network object, `NetworkDescriptor`.** The descriptors are:
  - `WellMixed(κ)`;
  - `ConfigurationNetwork(d)`, with any `DegreeDistribution`: `PoissonDegree`, `RegularDegree`,
    `BinomialDegree`, `NegBinDegree`, `GeometricDegree`, `PowerLawDegree`, `EmpiricalDegree`
    or `MixtureDegree`;
  - `MultitypeNetwork` (`sbm_network`, `unstructured`);
  - `ClusteredNetwork`;
  - `DynamicNetwork`;
  - `MultiplexNetwork`;
  - `degree_correlated(d; r)`;
  - `MFSHNetwork`;
  - `ExplicitGraph`.
- **Shared generic functions** that the three packages extend: `basic_reproduction_number`,
  `final_size`, `solve_epidemic`, `model_curves`, `compartment` and others. Loading all four
  packages together never gives an ambiguous name.
- **Numeric thresholds** computed on the model and the network:
  `basic_reproduction_number`, `next_generation_matrix`, `transmissibility`, `early_growth_rate`,
  `final_size`, `epidemic_probability` and `calibrate`.
- **Syntax-side composition.** `open_model` and `glue` give a pushout that concatenates
  reactions. `stratify(model, strata)` gives a typed product. Other transforms are `erlang_stages`,
  `with_reinfection_counting` and `relabel`.
- **Runtime morphism objects.** `SymbolicODE`, `Semiconjugacy`, `verify`, `pushforward`,
  `vector_fields_equal` and the registry of natural transformations (`transformations()`).
- **The shared validation scenarios** (`scenario`, `scenario_ids`, `derive`, `scenario_hash`),
  with ensemble summaries, `compare`, `comparisonplot` and the plot recipes.

NEC depends only on standard libraries and RecipesBase. It never builds a ModelingToolkit system
and never solves an ODE. Lowering is the job of EdgeBasedModels and NodeBasedModels, and
simulation is the job of NetworkOutbreaks. Symbolics, Catalyst, ModelingToolkitBase and Graphs
are weak dependencies:

| extension | loaded with | provides |
|---|---|---|
| `NetworkEpiCoreSymbolicsExt` | Symbolics | symbolic rates; `mass_action(cm; κ)` and `symbolic_ode`; `verify`, `pushforward`, `vector_fields_equal` |
| `NetworkEpiCoreCatalystExt` | Catalyst + Symbolics | `contact_model(::ReactionSystem)` and `Catalyst.ReactionSystem(::ContactModel)` |
| `NetworkEpiCoreMTKExt` | ModelingToolkitBase + Symbolics | `contact_model(::System)`, by pairing fluxes |
| `NetworkEpiCoreGraphsExt` | Graphs | `EmpiricalDegree(g)`, and queries on `ExplicitGraph` |

## Example

```julia
using NetworkEpiCore, Catalyst

sir = @reaction_network sir begin
    @parameters τ γ
    τ, S + I --> 2I        # contact: per-contact (per-edge) rate τ; S converted, I unchanged
    γ, I --> R             # node-local transition
end
model = contact_model(sir)                       # prints the typing report
isequivalent(model, sir_model())                 # true

net = ConfigurationNetwork(PoissonDegree(5))
p   = Dict(:τ => 1/6, :γ => 1/4)
basic_reproduction_number(model, net, p)         # 2.0    (T = 0.4, excess degree 5)
early_growth_rate(model, net, p)                 # 0.41667
final_size(model, net, p)                        # 0.79681 (the ρ → 0 fixed point)

admissibility(sis_model())
# AdmissibilityReport: edge_based ✗  s_anchored ✗  pairwise ✓  individual ✓  pair ✓  stochastic ✓  mass_action ✓
#   resus: I_to_S produces the susceptible species S

closure_constant(NegBinDegree(mean = 4, var = 8))   # 1.25
is_poisson_type(NegBinDegree(mean = 4, var = 8))    # (α = 4.0, κ = 1.25): the constant pairwise closure is exact

# composition: glue two open models along I, then stratify
infect  = open_model(ContactModel(:infect; contacts = [Contact(:S, :I, :I, :τ)]); legs = [[:S, :I]])
recover = open_model(ContactModel(:recover; transitions = [NodeTransition(:I, :R, :γ)]); legs = [[:I, :R]])
sir2 = glue(infect, recover; on = [:I])
isequivalent(sir2, sir_model())                                             # true
isequivalent(stratify(sir2, strata([:a, :b]; sizes = [0.5, 0.5])), scenario(:sir_sbm2).model)   # true
```

The back ends take the same objects:

```julia
using EdgeBasedModels, NodeBasedModels, NetworkOutbreaks
sys = edge_based(model, net)
pw  = node_based(model, net)
ens = simulate(model, net; N = 10_000, p, initial = SeedFraction(:I => 0.01), tspan = (0.0, 60.0), nsims = 10)
```

## Morphisms

A `Semiconjugacy` is a map π from a source `SymbolicODE` to a target, with a `kind`
(`:conjugacy`, `:semiconjugacy`, `:restriction` or `:lumping`), an **exactness** (`:exact`,
`:limit` or `:calibration`) and a list of `Evidence` records (`:lean`, `:symbolic`, `:paper`).
`verify(m)` checks the conjugacy equation Jπ·F = G∘π. It works symbolically first and then at
seeded numeric probes. Every term that does not cancel must be seen at some probe. An
"undecided" result is an error. Limits and calibrations are never called morphisms, and `verify`
rejects them.

EdgeBasedModels registers six natural transformations, listed by `transformations()`:
`:well_mixed_unit` (M1), `:poisson_iso` (M2), `:rempala` (M3), `:power_law` (M4),
`:general_kinetics` (M5) and `:eb_to_pws` (M6). Its README tabulates the verify results. The
Rempała map, for example, carries Lean evidence (including `NEP.rempala_lift`), Rempała 2023
Thm 1 and a symbolic test; the Lean statement of its SIR case is `NEP.rempala_general_sir`, and of
the general case `NEP.rempala_general`.

## Shared scenarios and validation

`scenario_ids()` lists **51 registered scenarios**. They share R₀ = 2 and r = 5/12, while their
final sizes differ: `:sir_reg6` 0.93, `:sir_pois5` 0.80, `:sir_nb4` 0.64, `:sir_bim` 0.50 and
`:sir_pl` 0.29. There are also SEIR, SEAIR, two-strain, vaccination, Erlang, clustered,
multitype, multiplex, dynamic, degree-correlated, dormant-contact, MFSH, dense and N-scaling
variants, and SIS on a 3-regular network. A `Scenario` is pure data: model, network, parameters,
seeding, time grid, a `SimConfig`, a verdict for each back end (`:exact_limit`, `:biased`,
`:approximate`, `:inadmissible`) and expected values that NEC computes. It is hashed from a
versioned canonical text (`canonical_text`, `scenario_hash`), not from `Base.hash`.

NetworkOutbreaks runs the scenarios (N = 10⁴, 200 runs, a fresh graph per run) and commits their
summaries (`NetworkOutbreaks.jl/data/scenarios`, 53 files, none missing). EdgeBasedModels and
NodeBasedModels load them with `scenario_summary` and compare with `compare(ref, curves...)`,
which reports D∞, z∞, ΔR∞ with its 95% CI, Δpeak and coverage. `comparisonplot` draws the same
ribbon and residual figure for both. The **N-scaling protocol** (N = 10³, 10⁴, 10⁵) tells an
exact large-N limit, whose error falls to the Monte Carlo floor, from a structural bias, whose
error levels off. Numbers are in the three package READMEs.

## Lean: the `NetworkEpi` library (`proofs/`)

`proofs/` is a Lake project (package `NetworkEpi`, namespace `NEP`; Lean 4.29.0-rc4, Mathlib
`3a4b36f2`). The **trusted library** is exactly the modules imported by `NetworkEpi.lean`, which
is 18 module files: `Dyn/{Basic,Products}`, `Syntax/Rxn`, `Semantics/{EB,MA,PWS,PoissonSIR,Solutions}`,
`Morphisms/{Common,Rempala,WellMixed,Stoich,Poisson,Pairwise,Compact,NGM,All}` and `Closure/PT`.
This is the genuine library behind the packages. EdgeBasedModels' legacy `EBCMCategory` tree is
never cited.

- **Axiom gate** (`scripts/axiom_gate.sh`). The gate fails on any of the following:
  - a failed build;
  - any `axiom`, `sorry` or `admit`, or an escape hatch (`native_decide`, `implemented_by`, …)
    in a trusted file;
  - a `CITABLE.txt` name that is not a theorem of `NetworkEpi.*`;
  - a `CITABLE.txt` name without a docstring that quotes the design ("Design statement");
  - a `CITABLE.txt` name that depends on an axiom beyond `propext`, `Classical.choice` and
    `Quot.sound`.

  `--self-test` checks that the gate rejects deliberately bad names. The build and the gate pass.
- **`CITABLE.txt`** lists **89** theorem names (`grep -vE '^\s*#|^\s*$' proofs/CITABLE.txt | wc -l`).
  Docs cite only these names. The vignettes of the three model packages use a stricter subset
  of 37 names: each is in `CITABLE.txt`, has SA-PASS = 1 in the run below, and was rated strong
  in the adversarial spot check.
- **Headline results.** They include:
  - `NEP.rempala_general`, the Rempała quotient for every T_EB model (M3);
  - `NEP.poisson_iso` and `NEP.poisson_iso_semiconj` (M2);
  - `NEP.wellmixed_unit` (M1);
  - `NEP.eb_to_pws`, EB → S-anchored pairwise for every PGF (M6);
  - `NEP.pt_iff_const_closure`, Poisson type ⇔ constant closure (M8);
  - `NEP.compact_conj_global` (M9);
  - `NEP.lift_append` and `NEP.lift_glue`, strict gluing (H1);
  - `NEP.conservation_invariant`;
  - `NEP.multiplex_r0_of_entries` and `NEP.spectralRadius_fin_two`, the two-layer R₀ = ρ(K).
- **Alignment (SA-PASS).** SA-PASS checks whether each Lean statement says what its
  natural-language text says. The figures below are from the round-4 run of 2026-09-28
  (`bash scripts/sa_pass.sh`; report in `Alignment/report/sa_pass_report.md`), taken after the
  non-blind owner's remediation and before the checker and blind-shadow updates it calls for.
  - **176 of 194 required claims (90.7%)** have SA-PASS = 1; mean SA-PASS_soft is 0.912.
    `MorphismsCompact.compactSolutionPoisson` now passes (the vacuity guard's normaliser is
    memoised).
  - **18 required claims fail**, all pending follow-up work, not new defects:
    - 16 have a new implementation list (new trusted theorems that close a forward gap, or
      exact-statement theorems where the old one was more general than the text); they report
      `impl_mismatch` until the checker author updates their `sa_claim` and checkers;
    - 2 have new claim text and wait for blind re-shadowing: `DynBasic.semiconjOnMapSolutionWithin`
      and `MorphismsPoisson.poissonIsoSolution`.
  - All 22 trusted-free shadows and all 25 bridges are reviewed.
  - The release gate `scripts/sa_pass_citable.sh` **fails**: `python3 scripts/sa_citable_coverage.py`
    reports **56 of 89** names covered. The other 33 belong to the 18 pending claims (17 have a
    failing claim, 16 new names are not yet in any `sa_claim`).

  So a `CITABLE.txt` name is guaranteed to be a real, axiom-clean theorem whose docstring
  quotes the design. It is not yet guaranteed that its statement has been independently
  aligned with that quote.

Build and check:

```sh
cd NetworkEpiCore.jl/proofs
mkdir -p .lake && cp -Rc ../../EdgeBasedModels.jl/proofs/.lake/packages .lake/   # locally; CI: lake exe cache get
lake build && bash scripts/axiom_gate.sh && bash scripts/axiom_gate.sh --self-test
bash scripts/sa_pass.sh && bash scripts/sa_pass_citable.sh
```

See [`proofs/README.md`](proofs/README.md) for the module table and the exact scope of each
statement.

## Installation

The four packages are developed side by side and are not registered yet. Clone them as siblings
and develop them by path:

```julia
using Pkg
Pkg.develop([PackageSpec(path = "NetworkEpiCore.jl"), PackageSpec(path = "EdgeBasedModels.jl"),
             PackageSpec(path = "NodeBasedModels.jl"), PackageSpec(path = "NetworkOutbreaks.jl")])
```

The migration guides are in the three packages (`EdgeBasedModels.jl/MIGRATION.md`,
`NodeBasedModels.jl/MIGRATION.md` and `NetworkOutbreaks.jl/MIGRATION.md`). NEC itself is new
in 0.1.

## Development

### Tests

`test/runtests.jl` runs every file in `test/suites/` in sorted order, each in its own module.
To select suites, pass a comma-separated list of basenames:

```sh
julia --project=. -e 'using Pkg; Pkg.test()'                                  # everything
NEC_TEST_SUITES=integration julia --project=. -e 'using Pkg; Pkg.test()'      # one suite
julia --project=. -e 'using Pkg; Pkg.test(test_args = ["ir_types", "ngm"])'   # the same via ARGS
```

### The integration workspace

`test/suites/integration.jl` always checks NEC's export hygiene:

- no clash with Catalyst, ModelingToolkit, Symbolics, Graphs, StatsBase, Distributions or Plots;
- no `@enum`;
- every export documented;
- NEC loads with only its hard dependencies.

Its second part loads NEC, EdgeBasedModels, NodeBasedModels and NetworkOutbreaks together. It
checks that every exported name resolves unambiguously, that the packages re-export NEC's
bindings, that there are no method ambiguities, and that a fresh session prints no "both …
export" warning. `NEC_INTEGRATION=force` runs this part and `NEC_INTEGRATION=skip` skips it. Run
it in the root development environment `../dev`, which develops all four packages by path:

```sh
julia --project=../dev -e 'using Pkg; Pkg.resolve()'     # after any sibling Project.toml change
NEC_TEST_SUITES=integration julia --project=../dev test/runtests.jl
```

### Continuous integration

`.github/workflows/CI.yml` tests the package on Julia 1.10, 1.11 and the latest release. It also
runs the integration suite, with the three other packages checked out as siblings. The Lean
library has its own workflow, which has not yet run on GitHub.

## License

MIT; see [LICENSE](LICENSE).
