import Lake
open Lake DSL

/-! Lean library for NetworkEpiCore.jl (package `NetworkEpi`, namespace `NEP`).

The trusted library is `NetworkEpi`: exactly the modules imported by `NetworkEpi.lean`.
See `README.md`, `CITABLE.txt` and `scripts/axiom_gate.sh`. -/

package «NetworkEpi» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require "leanprover-community" / "mathlib"

@[default_target]
lean_lib «NetworkEpi» where
  globs := #[.andSubmodules `NetworkEpi]

/-- Tooling for `scripts/axiom_gate.sh` (not trusted code, not a default target). -/
lean_lib GateTools where
  roots := #[`GateTools.AxiomGate]

/-- SA-PASS alignment library. NOT trusted code: it registers claims, blind shadow sets,
checkers and bridges against the trusted library `NetworkEpi`. Not a default target; build
with `lake build +Alignment.All +Alignment.Audit` (see `Alignment/README.md`). -/
lean_lib Alignment where
  globs := #[.submodules `Alignment]
