import NetworkEpi.Dyn.Basic
import NetworkEpi.Dyn.Products
import NetworkEpi.Syntax.Rxn
import NetworkEpi.Semantics.EB
import NetworkEpi.Semantics.MA
import NetworkEpi.Semantics.PWS
import NetworkEpi.Semantics.PoissonSIR
import NetworkEpi.Semantics.Solutions
import NetworkEpi.Morphisms.All

/-!
# NetworkEpi: the trusted Lean library of NetworkEpiCore.jl (namespace `NEP`)

The trusted library is exactly the modules imported by this file (and their `NetworkEpi.*`
imports); the SA-PASS audit (`Alignment/Audit.lean`) reads this file from disk.

| module | DESIGN_NetworkEpiCore.md | content |
|---|---|---|
| `NetworkEpi.Dyn.Basic` | L1 (§D.3) | `DynSys`, `Semiconj`, `instance : Category DynSys`, `Semiconj.map_solution`, `SemiconjOn`, `SemiconjOn.map_solution_on`, `SemiconjOn.map_solution_within`, `invariant_incl` |
| `NetworkEpi.Dyn.Products` | L1b (§D.3, stretch) | `prod_isLimit`, `hasBinaryProducts`, `hasTerminal` |
| `NetworkEpi.Syntax.Rxn` | L2 (§B.2, §D.1) | `Rxn σ` (T_EB), `NRxn σ` (T_net), typing, `Rxn.map`, decidable `EBAdmissible` |
| `NetworkEpi.Semantics.EB` | L3 (§D.4) | `ebField` (with exits and ξ), `lift_append`, `ebField_map`, `lift_map`, `lift_glue`; on a time interval: `conservation`, `node_conservation`, `xi_const` |
| `NetworkEpi.Semantics.MA` | L3 (§D.4, §D.6 H1′) | `maField`, `maLift_append`, `maLift_map`, `maLift_glue` |
| `NetworkEpi.Semantics.PWS` | L3 stretch (§D.4, §D.6 F2) | `pwSField`, `pwS_glue_not_strict` (PW^S is lax under gluing) |
| `NetworkEpi.Semantics.PoissonSIR` | L4c for SIR (§D.5 M3) | `rempala`, `ebPoisSIR_lift`, `rempala_lift`, `rempala_solution` |
| `NetworkEpi.Semantics.Solutions` | L3 (§D.3, §D.4) | `contDiff_lift` (EB models are objects of Dyn), `exists_local_solution`, `conservation_local`, `seir_conservation_local` |
| `NetworkEpi.Morphisms.Common` | §D.3, §D.5 | per-reaction criterion `clm_list_sum_eq`, `IsConjOn`, `isSemiconjOn_inverse`, EB coordinate maps, `suscD`, the reduced EB model `ebSys1` on ξ = 1 |
| `NetworkEpi.Morphisms.Rempala` | L4c, M3 | `rempala_general` (every T_EB model), `rempala_general_solution`, `rempala_natural`, `rempala_quotient`, `rempala_general_sir`, `rempala_seir_field` |
| `NetworkEpi.Closure.PT` | L4f (§D.7 "L4d `Closure/PT`"), M8 | `pt_iff_const_closure`, `pt_iff_closureK`, `pt_closure_at_one`, `poisson_closureK` |
| `NetworkEpi.Morphisms.WellMixed` | L4a, M1 | `wellmixed_unit` (conjugacy, exit-free), `wellmixed_unit_semiconj` (with exits), `wellmixed_unit_quotient`, `wellmixed_unit_Iic`, `wellmixed_unit_solution` |
| `NetworkEpi.Morphisms.Stoich` | §D.7 (multiset stoichiometry) | mass action `sSys` for multiset reactions; `ma_eq_stoich` (agrees with `maSys`) |
| `NetworkEpi.Morphisms.Poisson` | L4b, M2 | `poisson_iso` (conjugacy, exit-free), `poisson_iso_semiconj` (with exits), `poisson_iso_solution`, `poisson_iso_natural`, `poisson_iso_sir`, `poisson_iso_seir`, `poissonD_sir_field` |
| `NetworkEpi.Morphisms.Pairwise` | L4e, M6 (+ M8) | `eb_to_pws` (every ψ, every T_EB model), `eb_to_pws_solution`, `eb_to_pws_sir`, `eb_to_pws_seir`, `eb_to_pws_const`, `eb_to_pws_pt`, `eb_to_pws_poisson` |
| `NetworkEpi.Morphisms.Compact` | L4g, M9 | `compact_W_invariant`, `compact_conj`, `compact_solution`, `compact_solution_poisson` |
| `NetworkEpi.Morphisms.NGM` | L5 (stretch) | `spectralRadius_vecMulVec`, `r0_single_entry`, `spectralRadius_fin_two`, `multiplex_r0`, `multiplex_r0_eq_sum_iff` |

Citable theorem names are listed in `CITABLE.txt` and checked by `scripts/axiom_gate.sh`.
-/
