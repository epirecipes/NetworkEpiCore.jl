"""
    NetworkEpiCore

Shared core of the network-epidemic packages EdgeBasedModels (EBM), NodeBasedModels (NBM) and
NetworkOutbreaks (NO):

- **one model object**, `ContactModel`: contacts s + J → X + J at a per-contact (per-edge) rate
  τ, and node transitions X → Y | ∅, built directly, from `sir_model()` and friends, or from
  Catalyst / ModelingToolkit through `contact_model` (package extensions), and typed over the
  theories T_EB ⊂ T_net, which decide the admissible back ends;
- **one network object**, `NetworkDescriptor` (`WellMixed`, `ConfigurationNetwork` with any
  degree distribution, `MultitypeNetwork`, `ClusteredNetwork`, `DynamicNetwork`,
  `MultiplexNetwork`, `ExplicitGraph`), which EBM lifts, NBM closes over and NO samples;
- the shared generics that EBM, NBM and NO extend (`basic_reproduction_number`, `final_size`,
  `compartment`, …), syntax-side composition (`glue`, `stratify`), numeric threshold
  quantities, morphism objects (`Semiconjugacy`, `verify`), and the shared validation scenarios,
  ensemble summaries, comparison metrics and plot recipes.

NetworkEpiCore depends only on standard libraries and RecipesBase. It never builds an MTK
`System` and never solves an ODE: lowering is EBM's and NBM's job, simulation is NO's.
Symbolics, Catalyst, ModelingToolkitBase and Graphs are weak dependencies.

The authoritative specification is `DESIGN_NetworkEpiCore.md` (§A.2 lists the files below).
"""
module NetworkEpiCore

# Common imports of the hard dependencies ([deps] of Project.toml). Source files carry their
# own `export` lines and may add narrower imports of these same dependencies at their top
# (e.g. `import LinearAlgebra: eigvals`); a new dependency needs a Project.toml change.
# This file and Project.toml are owned by WP5: later work packages never edit them.
using LinearAlgebra
using Printf
using Random
using RecipesBase
import DelimitedFiles
import SHA
import TOML

# Include order. A file may use the types of every file included before it in signatures and
# struct fields; functions from any file may be called inside function bodies. The order below
# is chosen so that the IR files that dispatch on concrete network descriptors (rates.jl,
# typing.jl) come after the descriptors, and descriptors.jl (sbm_network, unstructured) comes
# after the `Strata` type.

# Shared generic function stubs (WP5).
include("generics.jl")

# IR core types (WP6) and the targets of the reverse maps (WP6).
include("ir/types.jl")
include("ir/reaction_data.jl")

# Degree distributions and multivariate degree laws (WP7): no IR dependencies.
include("networks/degrees.jl")
include("networks/multivariate.jl")

# Strata and stratification (WP8), needed by the typed-network constructors below.
include("composition/stratify.jl")

# Network descriptors and seeding specifications (WP7).
include("networks/descriptors.jl")
include("seeding.jl")

# The rest of the IR (WP6): rates, typing and admissibility, canned models, equivalence,
# syntax transforms.
include("ir/rates.jl")
include("ir/typing.jl")
include("ir/canned.jl")
include("ir/equivalence.jl")
include("ir/transforms.jl")

# Open models and gluing (WP8).
include("composition/open.jl")

# Numeric next-generation matrix, transmissibility, final size, calibration (WP11).
include("analysis/ngm.jl")

# Runtime morphism objects (WP10); `verify`/`pushforward` are implemented by the Symbolics
# extension.
include("morphisms.jl")

# Shared scenarios (WP12).
include("scenarios/types.jl")
include("scenarios/canonical_text.jl")
include("scenarios/registry.jl")
include("scenarios/canonical.jl")

# Ensemble summaries, comparison metrics and plot recipes (WP12).
include("validation/summary.jl")
include("validation/compare.jl")
include("recipes.jl")

end # module NetworkEpiCore
