# NetworkEpiCore.jl

The shared core of three packages for epidemics on networks:

| package | verb | what it does with a model and a network |
|---|---|---|
| [EdgeBasedModels.jl](https://epirecip.es/EdgeBasedModels.jl/) | `edge_based` | lifts the model to an edge-based compartmental ODE (Miller–Slim–Volz), the exact large-N limit on configuration-model networks |
| [NodeBasedModels.jl](https://epirecip.es/NodeBasedModels.jl/) | `node_based` | closes a pairwise, PGF-closure, mean-field, individual-, pair-, motif- or neighbourhood-based ODE over it |
| [NetworkOutbreaks.jl](https://epirecip.es/NetworkOutbreaks.jl/) | `simulate` | samples graphs from the network and runs exact stochastic simulations on them |

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

