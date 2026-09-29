import Alignment.Registry
import Alignment.Shadows.MorphismsCommon

/-!
# Checkers: group `MorphismsCommon` (trusted module `NetworkEpi.Morphisms.Common`)

Checker author (SA-PASS role 3, non-blind). For each of the twenty `implemented` claims of
`NetworkEpi/Morphisms/Common.lean` that the blind author shadowed, this file holds the `sa_claim`
registration (verbatim registry text, registry `impl` list in registry order), the forward
checkers `sa_impl% → Sᵢ`, the backward checker `S₁ → … → Sₙ → sa_impl%`, and an `sa_fail_*`
record wherever a check is genuinely not derivable. The non-required claim
`MorphismsCommon.isConjOn` (status `missing`, a definition docstring) is not registered, as in
the other groups.

No bridges are declared. The shadows state every claim with the trusted notions themselves
(`IsSemiconj`, `IsSemiconjOn`, `IsConjOn`, `ebTheta`, …) or with alignment helpers that are
definitionally equal to the trusted ones (`inclF` = `EB1.incl`, `dropF` = `EB.drop`,
`sliceXi1 σ` = `{u | u.2.1 = 1}`; `q * v.2.1 * N.ψ v.1` = `N.susc q v.1 v.2.1` by the definition
of `CNet.susc`). Definitional unfolding is free.

Checker pass after the registry remediation. The seven claims `header.perReactionCriterion`,
`hasFDerivAtEbCoordinates`, `suscDApply`, `hasFDerivAtSusc`, `hasFDerivAtIncl`, `ebSys1Incl` and
`header.ebSys1` were re-registered to the remediated impl lists of `claims/MorphismsCommon.yaml`
(`ebSys_F_eq_sum`, `maSys_F_eq_sum`, `isSemiconj_of_perReaction`; `hasFDerivAt_ebCoordinates_any`;
`suscD_apply_left`; `hasFDerivAt_susc_any`; `incl_affine`, `hasFDerivAt_incl_any`;
`ebSys1_incl`, `lift_ξ_eq_zero`, `ebSys_xi_slice_invariant`; `ebSys1_F`, `ebSys1_conj`). The
earlier `SHADOW?` finiteness records, the parenthesisation records and the "text part not stated"
records are gone: every forward check of these claims now passes structurally, and every backward
check passes (`hasFDerivAtIncl` now uses `incl_affine`, the existential "affine" statement, in
place of `incl_eq_inclL_add`, which names the constant). No failures are recorded.
-/

open NEP

/-! ## `MorphismsCommon.header.perReactionCriterion`

The impl is `ebSys_F_eq_sum ∧ maSys_F_eq_sum ∧ isSemiconj_of_perReaction`, one conjunct per
shadow: S1, S2 (the two fields are sums of per-reaction fields) and S3 (the criterion for a
differentiable map whose Fréchet derivative carries each summand to the corresponding one). -/

namespace Alignment.Shadows.MorphismsCommon.HeaderPerReactionCriterion

sa_claim "MorphismsCommon.header.perReactionCriterion" group "MorphismsCommon" required
  text "Every field in this library is a sum of per-reaction fields, and the derivative of a map is linear, so a map is a semiconjugacy as soon as its derivative carries each per-reaction source field to the corresponding per-reaction target field."
  impl NEP.ebSys_F_eq_sum NEP.maSys_F_eq_sum NEP.isSemiconj_of_perReaction

/-- S1 is the first impl conjunct `ebSys_F_eq_sum` (instance order differs only). -/
@[sa_forward "MorphismsCommon.header.perReactionCriterion" 1]
theorem fwd1 (h : sa_impl% "MorphismsCommon.header.perReactionCriterion") : S1 := by
  intro σ _ _ N q rs u
  exact h.1 N q rs u

/-- S2 is the second impl conjunct `maSys_F_eq_sum`. -/
@[sa_forward "MorphismsCommon.header.perReactionCriterion" 2]
theorem fwd2 (h : sa_impl% "MorphismsCommon.header.perReactionCriterion") : S2 := by
  intro σ _ _ rs u
  exact h.2.1 rs u

/-- S3 is the third impl conjunct `isSemiconj_of_perReaction`. -/
@[sa_forward "MorphismsCommon.header.perReactionCriterion" 3]
theorem fwd3 (h : sa_impl% "MorphismsCommon.header.perReactionCriterion") : S3 := by
  intro A B ι l f g π hA hB hπ hfg
  exact h.2.2 A B l f g π hA hB hπ hfg

@[sa_backward "MorphismsCommon.header.perReactionCriterion"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) :
    sa_impl% "MorphismsCommon.header.perReactionCriterion" := by
  refine And.intro ?_ (And.intro ?_ ?_)
  · intro σ _ _ N q rs u
    exact s1 N q rs u
  · intro σ _ _ rs u
    exact s2 rs u
  · intro A B ι l f g π hA hB hπ hc
    exact s3 A B l f g π hA hB hπ hc

end Alignment.Shadows.MorphismsCommon.HeaderPerReactionCriterion

/-! ## `MorphismsCommon.isSemiconjOfHasFDerivAt` -/

namespace Alignment.Shadows.MorphismsCommon.IsSemiconjOfHasFDerivAt

sa_claim "MorphismsCommon.isSemiconjOfHasFDerivAt" group "MorphismsCommon" required
  text "A map with an explicit derivative `D u` at every point is a semiconjugacy if `D u` carries the source field at `u` to the target field at `π u`."
  impl NEP.isSemiconj_of_hasFDerivAt

@[sa_forward "MorphismsCommon.isSemiconjOfHasFDerivAt" 1]
theorem fwd1 (h : sa_impl% "MorphismsCommon.isSemiconjOfHasFDerivAt") : S1 := by
  intro A B π D hD hc
  exact h D hD hc

@[sa_backward "MorphismsCommon.isSemiconjOfHasFDerivAt"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsCommon.isSemiconjOfHasFDerivAt" := by
  intro A B π D hD hc
  exact s1 A B π D hD hc

end Alignment.Shadows.MorphismsCommon.IsSemiconjOfHasFDerivAt

/-! ## `MorphismsCommon.isSemiconjOnOfHasFDerivAt` -/

namespace Alignment.Shadows.MorphismsCommon.IsSemiconjOnOfHasFDerivAt

sa_claim "MorphismsCommon.isSemiconjOnOfHasFDerivAt" group "MorphismsCommon" required
  text "Local version of `isSemiconj_of_hasFDerivAt` on a set `U`. [...] A map with an explicit derivative `D u` at every point is a semiconjugacy if `D u` carries the source field at `u` to the target field at `π u`."
  impl NEP.isSemiconjOn_of_hasFDerivAt

@[sa_forward "MorphismsCommon.isSemiconjOnOfHasFDerivAt" 1]
theorem fwd1 (h : sa_impl% "MorphismsCommon.isSemiconjOnOfHasFDerivAt") : S1 := by
  intro A B U π D hD hc
  exact h D hD hc

/-- S2 (derivative at every point) is the impl with the derivative hypothesis restricted to `U`. -/
@[sa_forward "MorphismsCommon.isSemiconjOnOfHasFDerivAt" 2]
theorem fwd2 (h : sa_impl% "MorphismsCommon.isSemiconjOnOfHasFDerivAt") : S2 := by
  intro A B U π D hD hc
  exact h D (fun u _ => hD u) hc

@[sa_backward "MorphismsCommon.isSemiconjOnOfHasFDerivAt"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "MorphismsCommon.isSemiconjOnOfHasFDerivAt" := by
  intro A B U π D hD hc
  exact s1 A B U π D hD hc

end Alignment.Shadows.MorphismsCommon.IsSemiconjOnOfHasFDerivAt

/-! ## `MorphismsCommon.clmListSum`

The shadow is pure linear algebra (no trusted constant), so it is flagged `shadow_trusted_free`
until an independent `sa_shadow_reviewed` record accepts it; the text is itself arithmetic. -/

namespace Alignment.Shadows.MorphismsCommon.ClmListSum

sa_claim "MorphismsCommon.clmListSum" group "MorphismsCommon" required
  text "A continuous linear map commutes with the sum of a mapped list."
  impl NEP.clm_list_sum

@[sa_forward "MorphismsCommon.clmListSum" 1]
theorem fwd1 (h : sa_impl% "MorphismsCommon.clmListSum") : S1 := by
  intro E F _ _ _ _ L ι l f
  exact h L l f

@[sa_backward "MorphismsCommon.clmListSum"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsCommon.clmListSum" := by
  intro E F ρ _ _ _ _ L rs f
  exact s1 L rs f

end Alignment.Shadows.MorphismsCommon.ClmListSum

/-! ## `MorphismsCommon.clmListSumEq`

`shadow_trusted_free` as `clmListSum` (the text is pure linear algebra). -/

namespace Alignment.Shadows.MorphismsCommon.ClmListSumEq

sa_claim "MorphismsCommon.clmListSumEq" group "MorphismsCommon" required
  text "**The per-reaction criterion.** If a continuous linear map `L` carries each per-reaction source term `f r` to the per-reaction target term `g r`, it carries the sum over the reaction list to the sum."
  impl NEP.clm_list_sum_eq

@[sa_forward "MorphismsCommon.clmListSumEq" 1]
theorem fwd1 (h : sa_impl% "MorphismsCommon.clmListSumEq") : S1 := by
  intro E F _ _ _ _ L ι rs f g hfg
  exact h L rs f g hfg

@[sa_backward "MorphismsCommon.clmListSumEq"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsCommon.clmListSumEq" := by
  intro E F ρ _ _ _ _ L rs f g hfg
  exact s1 L rs f g hfg

end Alignment.Shadows.MorphismsCommon.ClmListSumEq

/-! ## `MorphismsCommon.isSemiconjOnInverse`

S1 is the impl with `g ∘ h = id` for `∀ u, g (h u) = u` (`congrFun` / `funext`). S2 (global
reading) is the impl at `V = U = univ`; membership in `univ` is `True`, and `IsSemiconj`,
`IsSemiconjOn … univ`, `Differentiable` unfold to the same pointwise conditions. -/

namespace Alignment.Shadows.MorphismsCommon.IsSemiconjOnInverse

sa_claim "MorphismsCommon.isSemiconjOnInverse" group "MorphismsCommon" required
  text "**A differentiable inverse of a semiconjugacy is a semiconjugacy.** Let `h` be a local semiconjugacy on `V` from `A` to `B`, and let `g : B.V → A.V` be a global left inverse of `h` (`g ∘ h = id`) that is differentiable at every point of `U`, maps `U` into `V` and is a right inverse on `U` (`h (g v) = v` for `v ∈ U`). Then `g` is a local semiconjugacy on `U` from `B` to `A`. [...] the fact that a differentiable two-sided inverse of a semiconjugacy is one"
  impl NEP.isSemiconjOn_inverse

@[sa_forward "MorphismsCommon.isSemiconjOnInverse" 1]
theorem fwd1 (h : sa_impl% "MorphismsCommon.isSemiconjOnInverse") : S1 := by
  intro A B V U hm g hh hgh hg hgV hhg
  exact h hh hg hgV (congrFun hgh) hhg

@[sa_forward "MorphismsCommon.isSemiconjOnInverse" 2]
theorem fwd2 (h : sa_impl% "MorphismsCommon.isSemiconjOnInverse") : S2 := by
  intro A B hm g hh hg hgh hhg
  have r : IsSemiconjOn B A Set.univ g :=
    h (V := Set.univ) (U := Set.univ) (h := hm)
      (And.intro (fun u _ => hh.1 u) (fun u _ => hh.2 u)) (fun v _ => hg v) (fun _ _ => trivial)
      (congrFun hgh) (fun v _ => congrFun hhg v)
  exact And.intro (fun v => r.1 v trivial) (fun v => r.2 v trivial)

@[sa_backward "MorphismsCommon.isSemiconjOnInverse"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "MorphismsCommon.isSemiconjOnInverse" := by
  intro A B V U hm g hh hg hgV hgh hhg
  exact s1 A B V U hm g hh (funext hgh) hg hgV hhg

/-- Satisfiability witness for the hypothesis `IsSemiconjOn A B V h` (and the others): the zero
field on `ℝ`, with `h = g = id` and `V = U = univ`. -/
@[sa_witness "MorphismsCommon.isSemiconjOnInverse" 1]
theorem witness :
    ∃ (A B : DynSys) (V : Set A.V) (U : Set B.V) (h : A.V → B.V) (g : B.V → A.V)
      (_ : IsSemiconjOn A B V h) (_ : ∀ v ∈ U, DifferentiableAt ℝ g v) (_ : ∀ v ∈ U, g v ∈ V)
      (_ : ∀ u, g (h u) = u) (_ : ∀ v ∈ U, h (g v) = v), True := by
  refine ⟨⟨ℝ, fun _ => 0⟩, ⟨ℝ, fun _ => 0⟩, Set.univ, Set.univ, id, id,
    ⟨fun _ _ => differentiableAt_id, fun _ _ => ?_⟩, fun _ _ => differentiableAt_id,
    fun _ _ => Set.mem_univ _, fun _ => rfl, fun _ _ => rfl, trivial⟩
  simp

end Alignment.Shadows.MorphismsCommon.IsSemiconjOnInverse

/-! ## `MorphismsCommon.isConjOnOfInverse` -/

namespace Alignment.Shadows.MorphismsCommon.IsConjOnOfInverse

sa_claim "MorphismsCommon.isConjOnOfInverse" group "MorphismsCommon" required
  text "A conjugacy with `V = univ` built from a global semiconjugacy `h` and a differentiable inverse `g` on `U`: `IsConjOn A B univ U h g`."
  impl NEP.isConjOn_of_inverse

@[sa_forward "MorphismsCommon.isConjOnOfInverse" 1]
theorem fwd1 (h : sa_impl% "MorphismsCommon.isConjOnOfInverse") : S1 := by
  intro A B U hm g hh hg hU hgh hhg
  exact h hh hg hU hgh hhg

@[sa_backward "MorphismsCommon.isConjOnOfInverse"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsCommon.isConjOnOfInverse" := by
  intro A B U hm g hh hg hU hgh hhg
  exact s1 A B U hm g hh hg hU hgh hhg

/-- Satisfiability witness for the hypothesis `IsSemiconj A B h` (and the others): the zero
field on `ℝ`, with `h = g = id` and `U = univ`. -/
@[sa_witness "MorphismsCommon.isConjOnOfInverse" 1]
theorem witness :
    ∃ (A B : DynSys) (U : Set B.V) (h : A.V → B.V) (g : B.V → A.V)
      (_ : IsSemiconj A B h) (_ : ∀ v ∈ U, DifferentiableAt ℝ g v) (_ : ∀ u, h u ∈ U)
      (_ : ∀ u, g (h u) = u) (_ : ∀ v ∈ U, h (g v) = v), True := by
  refine ⟨⟨ℝ, fun _ => 0⟩, ⟨ℝ, fun _ => 0⟩, Set.univ, id, id,
    ⟨differentiable_id, fun _ => ?_⟩, fun _ _ => differentiableAt_id,
    fun _ => Set.mem_univ _, fun _ => rfl, fun _ _ => rfl, trivial⟩
  simp

end Alignment.Shadows.MorphismsCommon.IsConjOnOfInverse

/-! ## `MorphismsCommon.ebCoordinateApply` -/

namespace Alignment.Shadows.MorphismsCommon.EbCoordinateApply

sa_claim "MorphismsCommon.ebCoordinateApply" group "MorphismsCommon" required
  text "`ebTheta` is the θ-coordinate. [...] `ebXi` is the ξ-coordinate. [...] `ebPhi` is the φ-coordinate. [...] `ebPop` is the pop-coordinate."
  impl NEP.ebTheta_apply NEP.ebXi_apply NEP.ebPhi_apply NEP.ebPop_apply

@[sa_forward "MorphismsCommon.ebCoordinateApply" 1]
theorem fwd1 (h : sa_impl% "MorphismsCommon.ebCoordinateApply") : S1 := by
  intro σ u
  exact h.1 u

@[sa_forward "MorphismsCommon.ebCoordinateApply" 2]
theorem fwd2 (h : sa_impl% "MorphismsCommon.ebCoordinateApply") : S2 := by
  intro σ u
  exact h.2.1 u

@[sa_forward "MorphismsCommon.ebCoordinateApply" 3]
theorem fwd3 (h : sa_impl% "MorphismsCommon.ebCoordinateApply") : S3 := by
  intro σ u
  exact h.2.2.1 u

@[sa_forward "MorphismsCommon.ebCoordinateApply" 4]
theorem fwd4 (h : sa_impl% "MorphismsCommon.ebCoordinateApply") : S4 := by
  intro σ u
  exact h.2.2.2 u

@[sa_backward "MorphismsCommon.ebCoordinateApply"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) :
    sa_impl% "MorphismsCommon.ebCoordinateApply" :=
  And.intro (fun u => s1 u) (And.intro (fun u => s2 u) (And.intro (fun u => s3 u) (fun u => s4 u)))

end Alignment.Shadows.MorphismsCommon.EbCoordinateApply

/-! ## `MorphismsCommon.hasFDerivAtEbCoordinates`

The impl `hasFDerivAt_ebCoordinates_any` is the conjunction of the four reading-B statements
(`HasFDerivAt (fun u => u.1) ebTheta u`, …) for every `σ` (no `[Fintype σ]`), which are S5–S8.
S1–S4 (reading A: `fun v => ebTheta v`, …) are the same statements up to the definitional
unfolding `ebTheta v ≡ v.1` etc. (the `*_apply` lemmas of these maps are `rfl`). -/

namespace Alignment.Shadows.MorphismsCommon.HasFDerivAtEbCoordinates

sa_claim "MorphismsCommon.hasFDerivAtEbCoordinates" group "MorphismsCommon" required
  text "The coordinate projections are their own derivatives."
  impl NEP.hasFDerivAt_ebCoordinates_any

@[sa_forward "MorphismsCommon.hasFDerivAtEbCoordinates" 1]
theorem fwd1 (h : sa_impl% "MorphismsCommon.hasFDerivAtEbCoordinates") : S1 := by
  intro σ u
  exact (h u).1

@[sa_forward "MorphismsCommon.hasFDerivAtEbCoordinates" 2]
theorem fwd2 (h : sa_impl% "MorphismsCommon.hasFDerivAtEbCoordinates") : S2 := by
  intro σ u
  exact (h u).2.1

@[sa_forward "MorphismsCommon.hasFDerivAtEbCoordinates" 3]
theorem fwd3 (h : sa_impl% "MorphismsCommon.hasFDerivAtEbCoordinates") : S3 := by
  intro σ u
  exact (h u).2.2.1

@[sa_forward "MorphismsCommon.hasFDerivAtEbCoordinates" 4]
theorem fwd4 (h : sa_impl% "MorphismsCommon.hasFDerivAtEbCoordinates") : S4 := by
  intro σ u
  exact (h u).2.2.2

@[sa_forward "MorphismsCommon.hasFDerivAtEbCoordinates" 5]
theorem fwd5 (h : sa_impl% "MorphismsCommon.hasFDerivAtEbCoordinates") : S5 := by
  intro σ u
  exact (h u).1

@[sa_forward "MorphismsCommon.hasFDerivAtEbCoordinates" 6]
theorem fwd6 (h : sa_impl% "MorphismsCommon.hasFDerivAtEbCoordinates") : S6 := by
  intro σ u
  exact (h u).2.1

@[sa_forward "MorphismsCommon.hasFDerivAtEbCoordinates" 7]
theorem fwd7 (h : sa_impl% "MorphismsCommon.hasFDerivAtEbCoordinates") : S7 := by
  intro σ u
  exact (h u).2.2.1

@[sa_forward "MorphismsCommon.hasFDerivAtEbCoordinates" 8]
theorem fwd8 (h : sa_impl% "MorphismsCommon.hasFDerivAtEbCoordinates") : S8 := by
  intro σ u
  exact (h u).2.2.2

/-- Backward from reading B (S5–S8); S1–S4 are unused (reading A is the same up to unfolding). -/
@[sa_backward "MorphismsCommon.hasFDerivAtEbCoordinates"]
theorem bwd (_s1 : S1) (_s2 : S2) (_s3 : S3) (_s4 : S4) (s5 : S5) (s6 : S6) (s7 : S7) (s8 : S8) :
    sa_impl% "MorphismsCommon.hasFDerivAtEbCoordinates" := by
  intro σ u
  exact And.intro (s5 u) (And.intro (s6 u) (And.intro (s7 u) (s8 u)))

end Alignment.Shadows.MorphismsCommon.HasFDerivAtEbCoordinates

/-! ## `MorphismsCommon.suscDApply` -/

namespace Alignment.Shadows.MorphismsCommon.SuscDApply

sa_claim "MorphismsCommon.suscDApply" group "MorphismsCommon" required
  text "`suscD N q u v = q (v_ξ ψ(θ) + ξ ψ'(θ) v_θ)` with `(θ, ξ) = (u.1, u.2.1)`."
  impl NEP.suscD_apply_left

@[sa_forward "MorphismsCommon.suscDApply" 1]
theorem fwd1 (h : sa_impl% "MorphismsCommon.suscDApply") : S1 := by
  intro σ N q u v
  exact h N q u v

@[sa_backward "MorphismsCommon.suscDApply"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsCommon.suscDApply" := by
  intro σ N q u v
  exact s1 N q u v

end Alignment.Shadows.MorphismsCommon.SuscDApply

/-! ## `MorphismsCommon.hasFDerivAtSusc`

S2's function `v ↦ q * v.2.1 * N.ψ v.1` is `v ↦ N.susc q v.1 v.2.1` by the definition of
`CNet.susc` (`q * ξ * N.ψ θ`), so S1 and S2 are the same statement up to unfolding. -/

namespace Alignment.Shadows.MorphismsCommon.HasFDerivAtSusc

sa_claim "MorphismsCommon.hasFDerivAtSusc" group "MorphismsCommon" required
  text "`S = qξψ(θ)` has derivative `suscD N q u` at `u` when `ψ'(θ)` is the derivative of `ψ` at `θ = u.1`."
  impl NEP.hasFDerivAt_susc_any

@[sa_forward "MorphismsCommon.hasFDerivAtSusc" 1]
theorem fwd1 (h : sa_impl% "MorphismsCommon.hasFDerivAtSusc") : S1 := by
  intro σ N q u hψ
  exact h N q hψ

/-- S2's function `v ↦ q * v.2.1 * N.ψ v.1` is `v ↦ N.susc q v.1 v.2.1` by unfolding `CNet.susc`. -/
@[sa_forward "MorphismsCommon.hasFDerivAtSusc" 2]
theorem fwd2 (h : sa_impl% "MorphismsCommon.hasFDerivAtSusc") : S2 := by
  intro σ N q u hψ
  exact h N q hψ

/-- Backward from S1; S2 is unused (the same statement up to unfolding `CNet.susc`). -/
@[sa_backward "MorphismsCommon.hasFDerivAtSusc"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "MorphismsCommon.hasFDerivAtSusc" := by
  intro σ N q u hψ
  exact s1 N q u hψ

end Alignment.Shadows.MorphismsCommon.HasFDerivAtSusc

/-! ## `MorphismsCommon.dropLApply` -/

namespace Alignment.Shadows.MorphismsCommon.DropLApply

sa_claim "MorphismsCommon.dropLApply" group "MorphismsCommon" required
  text "`dropL` is `EB.drop`."
  impl NEP.dropL_apply

@[sa_forward "MorphismsCommon.dropLApply" 1]
theorem fwd1 (h : sa_impl% "MorphismsCommon.dropLApply") : S1 := by
  intro σ u
  exact h u

@[sa_backward "MorphismsCommon.dropLApply"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsCommon.dropLApply" := by
  intro σ u
  exact s1 u

end Alignment.Shadows.MorphismsCommon.DropLApply

/-! ## `MorphismsCommon.inclLApply`

The shadow speaks of triples `(θ, φ, pop)`, the impl of `w`; `w = (w.1, w.2.1, w.2.2)` by
structure eta (definitional). -/

namespace Alignment.Shadows.MorphismsCommon.InclLApply

sa_claim "MorphismsCommon.inclLApply" group "MorphismsCommon" required
  text "`inclL (θ, φ, pop) = (θ, 0, φ, pop)`."
  impl NEP.inclL_apply

@[sa_forward "MorphismsCommon.inclLApply" 1]
theorem fwd1 (h : sa_impl% "MorphismsCommon.inclLApply") : S1 := by
  intro σ θ φ pop
  exact h (θ, φ, pop)

@[sa_backward "MorphismsCommon.inclLApply"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsCommon.inclLApply" := by
  intro σ w
  exact s1 w.1 w.2.1 w.2.2

end Alignment.Shadows.MorphismsCommon.InclLApply

/-! ## `MorphismsCommon.dropIncl` -/

namespace Alignment.Shadows.MorphismsCommon.DropIncl

sa_claim "MorphismsCommon.dropIncl" group "MorphismsCommon" required
  text "`EB.drop` is a left inverse of `EB1.incl`."
  impl NEP.drop_incl

@[sa_forward "MorphismsCommon.dropIncl" 1]
theorem fwd1 (h : sa_impl% "MorphismsCommon.dropIncl") : S1 := by
  intro σ w
  exact h w

@[sa_backward "MorphismsCommon.dropIncl"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsCommon.dropIncl" := by
  intro σ w
  exact s1 w

end Alignment.Shadows.MorphismsCommon.DropIncl

/-! ## `MorphismsCommon.inclDrop` -/

namespace Alignment.Shadows.MorphismsCommon.InclDrop

sa_claim "MorphismsCommon.inclDrop" group "MorphismsCommon" required
  text "On `ξ = 1`, `EB1.incl` is a left inverse of `EB.drop`."
  impl NEP.incl_drop

@[sa_forward "MorphismsCommon.inclDrop" 1]
theorem fwd1 (h : sa_impl% "MorphismsCommon.inclDrop") : S1 := by
  intro σ u hu
  exact h hu

@[sa_backward "MorphismsCommon.inclDrop"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsCommon.inclDrop" := by
  intro σ u hu
  exact s1 u hu

end Alignment.Shadows.MorphismsCommon.InclDrop

/-! ## `MorphismsCommon.hasFDerivAtIncl` -/

namespace Alignment.Shadows.MorphismsCommon.HasFDerivAtIncl

sa_claim "MorphismsCommon.hasFDerivAtIncl" group "MorphismsCommon" required
  text "`EB1.incl` is affine with derivative `inclL`."
  impl NEP.incl_affine NEP.hasFDerivAt_incl_any

@[sa_forward "MorphismsCommon.hasFDerivAtIncl" 1]
theorem fwd1 (h : sa_impl% "MorphismsCommon.hasFDerivAtIncl") : S1 := by
  intro σ
  exact h.1

@[sa_forward "MorphismsCommon.hasFDerivAtIncl" 2]
theorem fwd2 (h : sa_impl% "MorphismsCommon.hasFDerivAtIncl") : S2 := by
  intro σ w
  exact h.2 w

@[sa_backward "MorphismsCommon.hasFDerivAtIncl"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "MorphismsCommon.hasFDerivAtIncl" :=
  ⟨fun {σ} => s1 (σ := σ), fun {σ} w => s2 (σ := σ) w⟩

end Alignment.Shadows.MorphismsCommon.HasFDerivAtIncl

/-! ## `MorphismsCommon.ebSys1Incl`

The impl is `ebSys1_incl ∧ lift_ξ_eq_zero ∧ ebSys_xi_slice_invariant`, one conjunct per shadow
(S1 the semiconjugacy, S2 the vanishing ξ-component, S3 the invariance of the slice `ξ = 1`).
`inclF` is `EB1.incl` by definition (same body). -/

namespace Alignment.Shadows.MorphismsCommon.EbSys1Incl

sa_claim "MorphismsCommon.ebSys1Incl" group "MorphismsCommon" required
  text "**For an exit-free model, the EB model on `(θ, φ, pop)` is the restriction of the EB model to the invariant slice `ξ = 1`**: `(θ, φ, pop) ↦ (θ, 1, φ, pop)` is a semiconjugacy from `ebSys1` to `ebSys` (the ξ-component of the EB field vanishes without exits)."
  impl NEP.ebSys1_incl NEP.lift_ξ_eq_zero NEP.ebSys_xi_slice_invariant

@[sa_forward "MorphismsCommon.ebSys1Incl" 1]
theorem fwd1 (h : sa_impl% "MorphismsCommon.ebSys1Incl") : S1 := by
  intro σ _ _ N q rs hrs
  exact h.1 N q rs hrs

@[sa_forward "MorphismsCommon.ebSys1Incl" 2]
theorem fwd2 (h : sa_impl% "MorphismsCommon.ebSys1Incl") : S2 := by
  intro σ _ N q rs hrs u
  exact h.2.1 N q rs hrs u

@[sa_forward "MorphismsCommon.ebSys1Incl" 3]
theorem fwd3 (h : sa_impl% "MorphismsCommon.ebSys1Incl") : S3 := by
  intro σ _ _ N q rs hrs I x hI hx t₀ ht₀ h1
  exact h.2.2 N q rs hrs hI hx ht₀ h1

@[sa_backward "MorphismsCommon.ebSys1Incl"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) : sa_impl% "MorphismsCommon.ebSys1Incl" := by
  refine And.intro ?_ (And.intro ?_ ?_)
  · intro σ _ _ N q rs hrs
    exact s1 N q rs hrs
  · intro σ _ N q rs hrs u
    exact s2 N q rs hrs u
  · intro σ _ _ N q rs hrs I hI x hx t₀ ht₀ h1
    exact s3 N q rs hrs I x hI hx t₀ ht₀ h1

end Alignment.Shadows.MorphismsCommon.EbSys1Incl

/-! ## `MorphismsCommon.ebSys1Drop`

`dropF` is `EB.drop` and `sliceXi1 σ` is `{u | u.2.1 = 1}` by definition. -/

namespace Alignment.Shadows.MorphismsCommon.EbSys1Drop

sa_claim "MorphismsCommon.ebSys1Drop" group "MorphismsCommon" required
  text "The chart `(θ, ξ, φ, pop) ↦ (θ, φ, pop)` is a local semiconjugacy on `{ξ = 1}` from `ebSys` to `ebSys1` (for every T_EB model)."
  impl NEP.ebSys1_drop

@[sa_forward "MorphismsCommon.ebSys1Drop" 1]
theorem fwd1 (h : sa_impl% "MorphismsCommon.ebSys1Drop") : S1 := by
  intro σ _ _ N q rs
  exact h N q rs

@[sa_backward "MorphismsCommon.ebSys1Drop"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsCommon.ebSys1Drop" := by
  intro σ _ _ N q rs
  exact s1 N q rs

end Alignment.Shadows.MorphismsCommon.EbSys1Drop

/-! ## `MorphismsCommon.header.ebSys1`

The impl is `ebSys1_F ∧ ebSys1_conj`: S1 is the first conjunct, S2 the second (with `inclF`,
`dropF`, `sliceXi1 σ` definitionally `EB1.incl`, `EB.drop`, `{u | u.2.1 = 1}`), and S3 is the
first component of the `IsConjOn` (an `IsSemiconjOn … univ`, whose pointwise conditions are those
of `IsSemiconj`; membership in `univ` is `True`). -/

namespace Alignment.Shadows.MorphismsCommon.HeaderEbSys1

sa_claim "MorphismsCommon.header.ebSys1" group "MorphismsCommon" required
  text "the reduced EB system `ebSys1` on `ξ = 1` in coordinates `(θ, φ, pop)`, which is the EB model of an exit-free T_EB model in the design's coordinates"
  impl NEP.ebSys1_F NEP.ebSys1_conj

@[sa_forward "MorphismsCommon.header.ebSys1" 1]
theorem fwd1 (h : sa_impl% "MorphismsCommon.header.ebSys1") : S1 := by
  intro σ _ _ N q rs w
  exact h.1 N q rs w

@[sa_forward "MorphismsCommon.header.ebSys1" 2]
theorem fwd2 (h : sa_impl% "MorphismsCommon.header.ebSys1") : S2 := by
  intro σ _ _ N q rs hrs
  exact h.2 N q rs hrs

@[sa_forward "MorphismsCommon.header.ebSys1" 3]
theorem fwd3 (h : sa_impl% "MorphismsCommon.header.ebSys1") : S3 := by
  intro σ _ _ N q rs hrs
  have c : IsSemiconjOn (ebSys1 N q rs) (ebSys N q rs) Set.univ EB1.incl := (h.2 N q rs hrs).1
  exact And.intro (fun w => c.1 w trivial) (fun w => c.2 w trivial)

/-- Backward from S1 and S2; S3 is unused (it is a component of S2). -/
@[sa_backward "MorphismsCommon.header.ebSys1"]
theorem bwd (s1 : S1) (s2 : S2) (_s3 : S3) : sa_impl% "MorphismsCommon.header.ebSys1" := by
  refine And.intro ?_ ?_
  · intro σ _ _ N q rs w
    exact s1 N q rs w
  · intro σ _ _ N q rs hrs
    exact s2 N q rs hrs

end Alignment.Shadows.MorphismsCommon.HeaderEbSys1

/-! ## `MorphismsCommon.maLiftFlatMap` -/

namespace Alignment.Shadows.MorphismsCommon.MaLiftFlatMap

sa_claim "MorphismsCommon.maLiftFlatMap" group "MorphismsCommon" required
  text "The mass-action field of `rs.flatMap g` is the sum over `r ∈ rs` of the fields of `g r`."
  impl NEP.maLift_flatMap

@[sa_forward "MorphismsCommon.maLiftFlatMap" 1]
theorem fwd1 (h : sa_impl% "MorphismsCommon.maLiftFlatMap") : S1 := by
  intro σ _ α rs g u
  exact h g rs u

@[sa_backward "MorphismsCommon.maLiftFlatMap"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsCommon.maLiftFlatMap" := by
  intro σ ρ _ g rs v
  exact s1 rs g v

end Alignment.Shadows.MorphismsCommon.MaLiftFlatMap
