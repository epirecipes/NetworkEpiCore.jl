import NetworkEpi.Morphisms.Common
import NetworkEpi.Morphisms.Rempala
import NetworkEpi.Morphisms.WellMixed
import NetworkEpi.Morphisms.Stoich
import NetworkEpi.Morphisms.Poisson
import NetworkEpi.Morphisms.Pairwise
import NetworkEpi.Morphisms.Compact
import NetworkEpi.Morphisms.NGM
import NetworkEpi.Closure.PT

/-!
# L4 and L5: the morphism catalogue (WP28)

Aggregator for the modules of WP28 (DESIGN_NetworkEpiCore.md §D.5, §D.7). A single
`import NetworkEpi.Morphisms.All` in `NetworkEpi.lean` makes all of them part of the trusted
library.

| module | DESIGN | content |
|---|---|---|
| `NetworkEpi.Morphisms.Common` | §D.3, §D.5 | per-reaction criterion `clm_list_sum_eq`, `IsConjOn`, `isSemiconjOn_inverse`, EB coordinate maps, `suscD`, the reduced EB model `ebSys1` on ξ = 1 |
| `NetworkEpi.Morphisms.Rempala` | L4c, M3 | `rempala_general` (every T_EB model), `rempala_general_solution`, `rempala_natural`, `rempala_quotient`, `rempala_general_sir`, `rempala_seir_field` |
| `NetworkEpi.Closure.PT` | L4f (§D.7 "L4d `Closure/PT`"), M8 | `pt_iff_const_closure`, `pt_iff_closureK`, `pt_closure_at_one`, `poisson_closureK` |
| `NetworkEpi.Morphisms.WellMixed` | L4a, M1 | `wellmixed_unit` (conjugacy, exit-free), `wellmixed_unit_semiconj` (with exits), `wellmixed_unit_quotient`, `wellmixed_unit_Iic`, `wellmixed_unit_solution` |
| `NetworkEpi.Morphisms.Stoich` | §D.7 (multiset stoichiometry) | mass action `sSys` for multiset reactions; `ma_eq_stoich` (agrees with `maSys`) |
| `NetworkEpi.Morphisms.Poisson` | L4b, M2 | `poisson_iso` (conjugacy, exit-free), `poisson_iso_semiconj` (with exits), `poisson_iso_solution`, `poisson_iso_natural`, `poisson_iso_sir`, `poisson_iso_seir`, `poissonD_sir_field` |
| `NetworkEpi.Morphisms.Pairwise` | L4e, M6 (+ M8) | `eb_to_pws` (every ψ, every T_EB model), `eb_to_pws_solution`, `eb_to_pws_sir`, `eb_to_pws_seir`, `eb_to_pws_const`, `eb_to_pws_pt`, `eb_to_pws_poisson` |
| `NetworkEpi.Morphisms.Compact` | L4g, M9 | `compact_W_invariant`, `compact_conj`, `compact_solution`, `compact_solution_poisson` |
| `NetworkEpi.Morphisms.NGM` | L5 (stretch) | `spectralRadius_vecMulVec`, `r0_single_entry`, `spectralRadius_fin_two`, `multiplex_r0`, `multiplex_r0_eq_sum_iff` |
-/
