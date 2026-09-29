import Alignment.Registry
import Alignment.Shadows.MorphismsWellMixed

/-!
# Checkers: group `MorphismsWellMixed` (trusted module `NetworkEpi.Morphisms.WellMixed`)

Checker author (SA-PASS role 3, non-blind). This file covers the ten `implemented` claims of
`NetworkEpi/Morphisms/WellMixed.lean`. For each one it holds the `sa_claim` registration
(verbatim registry text, registry `impl` list), the forward checkers `sa_impl% → Sᵢ`, the
backward checker `S₁ → … → Sₙ → sa_impl%`, and an `sa_fail_*` record wherever a check cannot be
derived. The claims `header.model` (informal) and `wellmixedUnitNaturality` (missing) are not
registered, as in the other groups.

**Bridges.** No checker uses a bridge. The remediated impls of `wellmixedUnitQuotient`
(`wellmixed_unit_submersion`) and `wmFieldEq` (`wm_field_eq_fderiv`) are stated with Mathlib's
`fderiv ℝ (wmMap κ q) u`, as the shadows are. The two copies of `bridge_wmD`
(`wmD κ q u = fderiv ℝ (wmMap κ q) u`, recomputed from Mathlib calculus lemmas without any
implementation theorem) were written for the earlier `wmD`-based impls. They are kept only
because `ReviewedBridges.lean` holds review records for them, and they can be deleted together
with those records.

The shadows state the claims with the trusted notions themselves (`IsSemiconj` unfolded,
`IsConjOn` unfolded, `wmMap`, `wmMap1`, `wmInv`, `wmSys`, `wmSys1`, `maSys`, `fderiv`, …) or with
alignment helpers that are definitionally equal to trusted terms (`inclXi1` =
`fun w => (w.1, 1, w.2)`, `ExitFree rs` = `∀ r ∈ rs, r.isExit = false`, `v.1 ∈ Set.Ioc 0 q` =
`0 < v.1 ∧ v.1 ≤ q`, `w ∈ Set.univ` = `True`).

No failures are recorded. `wellmixedUnitIic` now also lists the preimage equality
`wellmixed_unit_Iic_preimage`, and `wellmixedUnitSolution` the within-`I` versions for the
exit-free map and the inverse (`wellmixed_unit1_solution`, `wellmixed_unit_inv_solution`).
-/

open NEP

/-! ## `MorphismsWellMixed.wellmixedUnitSemiconj`

`IsSemiconj A B π` is by definition `Differentiable ℝ π ∧ ∀ u, fderiv ℝ π u (A.F u) = B.F (π u)`,
and `(wmSys κ q rs).V` is `WM σ` by definition. -/

namespace Alignment.Shadows.MorphismsWellMixed.WellmixedUnitSemiconj

sa_claim "MorphismsWellMixed.wellmixedUnitSemiconj" group "MorphismsWellMixed" required
  text "**The well-mixed unit as a semiconjugacy, with or without exits (M1).** Design statement (DESIGN_NetworkEpiCore.md §D.5, M1): \"With exits, (θ, ξ, x) ↦ (qξe^{κ(θ−1)}, x) is a quotient semiconjugacy\"; §C.3, `WellMixed(κ)`: \"(θ, ξ; x_X): θ̇ = −Σ_r τ_r x_{J_r}, S = qξe^{κ(θ−1)}, x_X gains κτ_r x_{J_r}S; conjugate to MA(c_κ P) (M1)\". [...] for every T_EB model (exits allowed) and all κ, q, `(θ, ξ, x) ↦ (qξe^{κ(θ−1)}, x)` is a global semiconjugacy onto MA(c_κ P);"
  impl NEP.wellmixed_unit_semiconj

@[sa_forward "MorphismsWellMixed.wellmixedUnitSemiconj" 1]
theorem fwd1 (h : sa_impl% "MorphismsWellMixed.wellmixedUnitSemiconj") : S1 := by
  intro σ _ _ κ q P
  exact (h κ q P).1

@[sa_forward "MorphismsWellMixed.wellmixedUnitSemiconj" 2]
theorem fwd2 (h : sa_impl% "MorphismsWellMixed.wellmixedUnitSemiconj") : S2 := by
  intro σ _ _ κ q P u
  exact (h κ q P).2 u

@[sa_backward "MorphismsWellMixed.wellmixedUnitSemiconj"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "MorphismsWellMixed.wellmixedUnitSemiconj" := by
  intro σ _ _ κ q rs
  exact And.intro (s1 κ q rs) (fun u => s2 κ q rs u)

end Alignment.Shadows.MorphismsWellMixed.WellmixedUnitSemiconj

/-! ## The derivative of `wmMap` (shared by the two bridges)

A helper in the alignment library (not a bridge). It recomputes the derivative of `wmMap κ q`
from Mathlib calculus lemmas and does not use `NEP.hasFDerivAt_wmMap`. -/

namespace Alignment.Shadows.MorphismsWellMixed

theorem wmD_eq_fderiv_aux {σ : Type} [Fintype σ] (κ q : ℝ) (u : WM σ) :
    wmD κ q u = fderiv ℝ (wmMap κ q) u := by
  have hθ : HasFDerivAt (fun u : WM σ => u.1) (ContinuousLinearMap.fst ℝ ℝ (ℝ × (σ → ℝ))) u :=
    hasFDerivAt_fst
  have hξ : HasFDerivAt (fun u : WM σ => u.2.1)
      ((ContinuousLinearMap.fst ℝ ℝ (σ → ℝ)).comp (ContinuousLinearMap.snd ℝ ℝ _)) u :=
    ((ContinuousLinearMap.fst ℝ ℝ (σ → ℝ)).comp (ContinuousLinearMap.snd ℝ ℝ _)).hasFDerivAt
  have hE := ((hθ.sub_const 1).const_mul κ).exp
  have hS := (hξ.const_mul q).mul hE
  have hx : HasFDerivAt (fun u : WM σ => u.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ (σ → ℝ)).comp (ContinuousLinearMap.snd ℝ ℝ _)) u :=
    ((ContinuousLinearMap.snd ℝ ℝ (σ → ℝ)).comp (ContinuousLinearMap.snd ℝ ℝ _)).hasFDerivAt
  have hD : HasFDerivAt (wmMap κ q) (wmD κ q u) u := by
    refine (hS.prodMk hx).congr_fderiv ?_
    ext v <;> simp [wmD] <;> ring
  exact hD.fderiv.symm

end Alignment.Shadows.MorphismsWellMixed

/-! ## `MorphismsWellMixed.wellmixedUnitQuotient`

The impl `wellmixed_unit_submersion` is the conjunction of surjectivity (any `σ`),
differentiability (`∀ [Fintype σ]`) and surjectivity of `fderiv` at every point
(`∀ [Fintype σ]`), all for `q ≠ 0`. These are exactly S1, S2 and S3. No bridge is needed.
The bridge `bridge_wmD` is kept only because `ReviewedBridges.lean` holds a review record for it
(the earlier impl was stated with `wmD`). No checker uses it. -/

namespace Alignment.Shadows.MorphismsWellMixed.WellmixedUnitQuotient

sa_claim "MorphismsWellMixed.wellmixedUnitQuotient" group "MorphismsWellMixed" required
  text "**The well-mixed map with exits is a quotient (M1).** Design statement (DESIGN_NetworkEpiCore.md §D.5, M1): \"With exits, (θ, ξ, x) ↦ (qξe^{κ(θ−1)}, x) is a quotient semiconjugacy\". [...] for `q ≠ 0` it is a surjective submersion."
  impl NEP.wellmixed_unit_submersion

/-- Bridge (reviewed earlier; now UNUSED). The trusted definition `wmD κ q u` (docstring: "The
derivative of `wmMap κ q` at `u`") is Mathlib's `fderiv ℝ (wmMap κ q) u` (finite `σ`). The proof
recomputes the derivative from Mathlib calculus lemmas and uses no implementation theorem. It is
kept only so that the existing review record in `ReviewedBridges.lean` still resolves. -/
@[sa_bridge "MorphismsWellMixed.wellmixedUnitQuotient"]
theorem bridge_wmD {σ : Type} [Fintype σ] (κ q : ℝ) (u : WM σ) :
    wmD κ q u = fderiv ℝ (wmMap κ q) u :=
  wmD_eq_fderiv_aux κ q u

@[sa_forward "MorphismsWellMixed.wellmixedUnitQuotient" 1]
theorem fwd1 (h : sa_impl% "MorphismsWellMixed.wellmixedUnitQuotient") : S1 := by
  intro σ κ q hq
  exact (h κ q hq).1

@[sa_forward "MorphismsWellMixed.wellmixedUnitQuotient" 2]
theorem fwd2 (h : sa_impl% "MorphismsWellMixed.wellmixedUnitQuotient") : S2 := by
  intro σ inst κ q hq
  exact (h κ q hq).2.1

@[sa_forward "MorphismsWellMixed.wellmixedUnitQuotient" 3]
theorem fwd3 (h : sa_impl% "MorphismsWellMixed.wellmixedUnitQuotient") : S3 := by
  intro σ inst κ q hq u
  exact (h κ q hq).2.2 u

@[sa_backward "MorphismsWellMixed.wellmixedUnitQuotient"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) :
    sa_impl% "MorphismsWellMixed.wellmixedUnitQuotient" := by
  intro σ κ q hq
  refine And.intro (s1 κ q hq) (And.intro ?_ ?_)
  · intro inst
    exact @s2 σ inst κ q hq
  · intro inst u
    exact @s3 σ inst κ q hq u

end Alignment.Shadows.MorphismsWellMixed.WellmixedUnitQuotient

/-! ## `MorphismsWellMixed.wellmixedUnit`

`IsConjOn A B V U h g` is by definition `IsSemiconjOn A B V h ∧ IsSemiconjOn B A U g ∧
(∀ u ∈ V, h u ∈ U) ∧ (∀ v ∈ U, g v ∈ V) ∧ (∀ u ∈ V, g (h u) = u) ∧ ∀ v ∈ U, h (g v) = v`, and
`IsSemiconjOn A B U π` is `(∀ u ∈ U, DifferentiableAt ℝ π u) ∧ ∀ u ∈ U, fderiv ℝ π u (A.F u) =
B.F (π u)`. Here `V = Set.univ`, where membership is `True` (`trivial`), and
`U = {v | 0 < v.1}`, where membership is `0 < v.1`. -/

namespace Alignment.Shadows.MorphismsWellMixed.WellmixedUnit

sa_claim "MorphismsWellMixed.wellmixedUnit" group "MorphismsWellMixed" required
  text "**The well-mixed unit (M1): a conjugacy for exit-free models.** Design statement (DESIGN_NetworkEpiCore.md §D.5, M1): \"Well-mixed unit | EB_{WM(κ)}(P) on (θ; x) with S = q e^{κ(θ−1)} is conjugate to MA(c_κ P) on S ∈ (0, q], for every exit-free T_EB model P [...] | natural iso (quotient with exits)\". [...] for exit-free P, `κ ≠ 0` and `q > 0`, the model on `(θ; x)` is conjugate to MA(c_κ P) restricted to `S > 0` (inverse `(S, x) ↦ (1 + log(S/q)/κ, x)`)"
  impl NEP.wellmixed_unit

@[sa_forward "MorphismsWellMixed.wellmixedUnit" 1]
theorem fwd1 (h : sa_impl% "MorphismsWellMixed.wellmixedUnit") : S1 := by
  intro σ _ _ κ q P hyp w
  obtain ⟨hP, hκ, hq⟩ := hyp
  exact (h κ q hκ hq P hP).1.1 w trivial

@[sa_forward "MorphismsWellMixed.wellmixedUnit" 2]
theorem fwd2 (h : sa_impl% "MorphismsWellMixed.wellmixedUnit") : S2 := by
  intro σ _ _ κ q P hyp w
  obtain ⟨hP, hκ, hq⟩ := hyp
  exact (h κ q hκ hq P hP).1.2 w trivial

@[sa_forward "MorphismsWellMixed.wellmixedUnit" 3]
theorem fwd3 (h : sa_impl% "MorphismsWellMixed.wellmixedUnit") : S3 := by
  intro σ _ _ κ q P hyp w
  obtain ⟨hP, hκ, hq⟩ := hyp
  exact (h κ q hκ hq P hP).2.2.1 w trivial

@[sa_forward "MorphismsWellMixed.wellmixedUnit" 4]
theorem fwd4 (h : sa_impl% "MorphismsWellMixed.wellmixedUnit") : S4 := by
  intro σ _ _ κ q P hyp v hv
  obtain ⟨hP, hκ, hq⟩ := hyp
  exact (h κ q hκ hq P hP).2.1.1 v hv

@[sa_forward "MorphismsWellMixed.wellmixedUnit" 5]
theorem fwd5 (h : sa_impl% "MorphismsWellMixed.wellmixedUnit") : S5 := by
  intro σ _ _ κ q P hyp v hv
  obtain ⟨hP, hκ, hq⟩ := hyp
  exact (h κ q hκ hq P hP).2.1.2 v hv

@[sa_forward "MorphismsWellMixed.wellmixedUnit" 6]
theorem fwd6 (h : sa_impl% "MorphismsWellMixed.wellmixedUnit") : S6 := by
  intro σ _ _ κ q P hyp w
  obtain ⟨hP, hκ, hq⟩ := hyp
  exact (h κ q hκ hq P hP).2.2.2.2.1 w trivial

@[sa_forward "MorphismsWellMixed.wellmixedUnit" 7]
theorem fwd7 (h : sa_impl% "MorphismsWellMixed.wellmixedUnit") : S7 := by
  intro σ _ _ κ q P hyp v hv
  obtain ⟨hP, hκ, hq⟩ := hyp
  exact (h κ q hκ hq P hP).2.2.2.2.2 v hv

@[sa_backward "MorphismsWellMixed.wellmixedUnit"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) (s7 : S7) :
    sa_impl% "MorphismsWellMixed.wellmixedUnit" := by
  intro σ _ _ κ q hκ hq rs hrs
  have hyp : Hyp κ q rs := And.intro hrs (And.intro hκ hq)
  exact And.intro
    (And.intro (fun w _ => s1 κ q rs hyp w) (fun w _ => s2 κ q rs hyp w))
    (And.intro
      (And.intro (fun v hv => s4 κ q rs hyp v hv) (fun v hv => s5 κ q rs hyp v hv))
      (And.intro (fun w _ => s3 κ q rs hyp w)
        (And.intro (fun _ _ => trivial)
          (And.intro (fun w _ => s6 κ q rs hyp w) (fun v hv => s7 κ q rs hyp v hv)))))

end Alignment.Shadows.MorphismsWellMixed.WellmixedUnit

/-! ## `MorphismsWellMixed.wellmixedUnitIic`

The impl `wellmixed_unit_Iic_image` is the set equality `wmMap1 κ q '' {θ ≤ 1} = {S ∈ (0, q]}`
for `κ, q > 0`. Membership in an image is by definition `∃ w, w ∈ A ∧ wmMap1 κ q w = v`, and
membership in `{v | v.1 ∈ Set.Ioc 0 q}` is `v.1 ∈ Set.Ioc 0 q`. Set equality is proved with
`funext` and `propext` (`Set α` is `α → Prop`), so no library lemma (`Set.ext`) is used. -/

namespace Alignment.Shadows.MorphismsWellMixed.WellmixedUnitIic

sa_claim "MorphismsWellMixed.wellmixedUnitIic" group "MorphismsWellMixed" required
  text "**The half-space θ ≤ 1 corresponds to S ∈ (0, q] (M1).** Design statement (DESIGN_NetworkEpiCore.md §D.5, M1): \"EB_{WM(κ)}(P) on (θ; x) with S = q e^{κ(θ−1)} is conjugate to MA(c_κ P) on S ∈ (0, q]\". [...] for `κ > 0` the half-space `θ ≤ 1` corresponds to `S ∈ (0, q]`"
  impl NEP.wellmixed_unit_Iic_image NEP.wellmixed_unit_Iic_preimage

@[sa_forward "MorphismsWellMixed.wellmixedUnitIic" 1]
theorem fwd1 (h : sa_impl% "MorphismsWellMixed.wellmixedUnitIic") : S1 := by
  intro σ κ q hκ hq w hw
  have m : wmMap1 κ q w ∈ wmMap1 (σ := σ) κ q '' {w | w.1 ≤ 1} :=
    Exists.intro w (And.intro hw rfl)
  exact Eq.mp (congrArg (fun s => wmMap1 κ q w ∈ s) (h.1 κ q hκ hq)) m

@[sa_forward "MorphismsWellMixed.wellmixedUnitIic" 2]
theorem fwd2 (h : sa_impl% "MorphismsWellMixed.wellmixedUnitIic") : S2 := by
  intro σ κ q hκ hq v hv
  have m : v ∈ wmMap1 (σ := σ) κ q '' {w | w.1 ≤ 1} :=
    Eq.mpr (congrArg (fun s => v ∈ s) (h.1 κ q hκ hq)) hv
  obtain ⟨w, hw, e⟩ := m
  exact Exists.intro w (And.intro hw e)

/-- S3: `w` with `(wmMap1 κ q w).1 ∈ (0, q]` lies in the preimage (definitionally), which the
second impl `wellmixed_unit_Iic_preimage` identifies with `{w | w.1 ≤ 1}`. -/
@[sa_forward "MorphismsWellMixed.wellmixedUnitIic" 3]
theorem fwd3 (h : sa_impl% "MorphismsWellMixed.wellmixedUnitIic") : S3 := by
  intro σ κ q hκ hq w hw
  have m : w ∈ wmMap1 (σ := σ) κ q ⁻¹' {v | v.1 ∈ Set.Ioc 0 q} := hw
  exact Eq.mp (congrArg (fun s => w ∈ s) (h.2 κ q hκ hq)) m

@[sa_backward "MorphismsWellMixed.wellmixedUnitIic"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) : sa_impl% "MorphismsWellMixed.wellmixedUnitIic" := by
  refine And.intro ?_ ?_
  · intro σ κ q hκ hq
    exact funext (fun v => propext (Iff.intro
      (fun m => match m with
        | ⟨w, hw, e⟩ => Eq.mp (congrArg (fun y => y ∈ {v : MA σ | v.1 ∈ Set.Ioc 0 q}) e)
            (s1 κ q hκ hq w hw))
      (fun hv => s2 κ q hκ hq v hv)))
  · intro σ κ q hκ hq
    exact funext (fun w => propext (Iff.intro
      (fun hw => s3 κ q hκ hq w hw)
      (fun hw => s1 κ q hκ hq w hw)))

end Alignment.Shadows.MorphismsWellMixed.WellmixedUnitIic

/-! ## `MorphismsWellMixed.wellmixedUnitSolution`

`sa_impl%` is the conjunction, in `sa_claim` order, of `wellmixed_unit_solution_at` (`wmMap`,
two-sided), `wellmixed_unit1_solution_at` (`wmMap1`, exit-free, two-sided),
`wellmixed_unit_inv_solution_at` (`wmInv`, exit-free, `κ ≠ 0`, `q > 0`, `S > 0` on `I`,
two-sided) and `wellmixed_unit_solution` (`wmMap`, within `I`). By definition
`(wmSys κ q P).F = wmLift κ q P`, `(maSys N).F = maLift N`, and `ExitFree P` is
`∀ r ∈ P, r.isExit = false`. -/

namespace Alignment.Shadows.MorphismsWellMixed.WellmixedUnitSolution

sa_claim "MorphismsWellMixed.wellmixedUnitSolution" group "MorphismsWellMixed" required
  text "**The well-mixed unit on trajectories (M1).** Design statement (DESIGN_NetworkEpiCore.md §D.5, M1): \"EB_{WM(κ)}(P) on (θ; x) with S = q e^{κ(θ−1)} is conjugate to MA(c_κ P) [...]. With exits, (θ, ξ, x) ↦ (qξe^{κ(θ−1)}, x) is a quotient semiconjugacy\"; §D.3: \"semiconjugacies map solution curves to solution curves\". [...] solutions are mapped: `(θ, ξ, x) ↦ (qξe^{κ(θ−1)}, x)` (exits allowed) and, for exit-free P, `(θ, x) ↦ (q e^{κ(θ−1)}, x)` map EB solutions to solutions of MA(c_κ P); for exit-free P, `κ ≠ 0` and `q > 0` the inverse maps MA solutions that stay in `S > 0` (which contains `S ∈ (0, q]`) back to solutions on `(θ; x)`."
  impl NEP.wellmixed_unit_solution_at NEP.wellmixed_unit1_solution_at
    NEP.wellmixed_unit_inv_solution_at NEP.wellmixed_unit_solution NEP.wellmixed_unit1_solution
    NEP.wellmixed_unit_inv_solution

@[sa_forward "MorphismsWellMixed.wellmixedUnitSolution" 1]
theorem fwd1 (h : sa_impl% "MorphismsWellMixed.wellmixedUnitSolution") : S1 := by
  intro σ _ _ κ q P I x hx t ht
  exact h.1 κ q P hx t ht

@[sa_forward "MorphismsWellMixed.wellmixedUnitSolution" 2]
theorem fwd2 (h : sa_impl% "MorphismsWellMixed.wellmixedUnitSolution") : S2 := by
  intro σ _ _ κ q P hP I w hw t ht
  exact h.2.1 κ q P hP hw t ht

@[sa_forward "MorphismsWellMixed.wellmixedUnitSolution" 3]
theorem fwd3 (h : sa_impl% "MorphismsWellMixed.wellmixedUnitSolution") : S3 := by
  intro σ _ _ κ q P hP hκ hq I v hpos hv t ht
  exact h.2.2.1 κ q hκ hq P hP hpos hv t ht

@[sa_forward "MorphismsWellMixed.wellmixedUnitSolution" 4]
theorem fwd4 (h : sa_impl% "MorphismsWellMixed.wellmixedUnitSolution") : S4 := by
  intro σ _ _ κ q P I x hx t ht
  exact h.2.2.2.1 κ q P hx t ht

@[sa_forward "MorphismsWellMixed.wellmixedUnitSolution" 5]
theorem fwd5 (h : sa_impl% "MorphismsWellMixed.wellmixedUnitSolution") : S5 := by
  intro σ _ _ κ q P hP I w hw t ht
  exact h.2.2.2.2.1 κ q P hP hw t ht

@[sa_forward "MorphismsWellMixed.wellmixedUnitSolution" 6]
theorem fwd6 (h : sa_impl% "MorphismsWellMixed.wellmixedUnitSolution") : S6 := by
  intro σ _ _ κ q P hP hκ hq I v hpos hv t ht
  exact h.2.2.2.2.2 κ q hκ hq P hP hpos hv t ht

@[sa_backward "MorphismsWellMixed.wellmixedUnitSolution"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) :
    sa_impl% "MorphismsWellMixed.wellmixedUnitSolution" := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ _ _ κ q rs I x hx t ht
    exact s1 κ q rs I x hx t ht
  · intro σ _ _ κ q rs hrs I w hw t ht
    exact s2 κ q rs hrs I w hw t ht
  · intro σ _ _ κ q hκ hq rs hrs I v hpos hv t ht
    exact s3 κ q rs hrs hκ hq I v hpos hv t ht
  · intro σ _ _ κ q rs I x hx t ht
    exact s4 κ q rs I x hx t ht
  · intro σ _ _ κ q rs hrs I w hw t ht
    exact s5 κ q rs hrs I w hw t ht
  · intro σ _ _ κ q hκ hq rs hrs I v hpos hv t ht
    exact s6 κ q rs hrs hκ hq I v hpos hv t ht

end Alignment.Shadows.MorphismsWellMixed.WellmixedUnitSolution

/-! ## `MorphismsWellMixed.wmDApply`

A pair is definitionally the pair of its projections (structure η), so the goal
`wmD κ q u v = (a, b)` can be restated as `((wmD κ q u v).1, (wmD κ q u v).2) = (a, b)` and closed
with `congrArg` on each component (S1, then S2). `rw` is avoided here: both shadows hold by `rfl`,
so the casts it produces would be erased by the vacuity guard's normaliser. -/

namespace Alignment.Shadows.MorphismsWellMixed.WmDApply

sa_claim "MorphismsWellMixed.wmDApply" group "MorphismsWellMixed" required
  text "`wmD κ q u v = (q e^{κ(θ−1)} v_ξ + qξκ e^{κ(θ−1)} v_θ, v_x)`."
  impl NEP.wmD_apply

@[sa_forward "MorphismsWellMixed.wmDApply" 1]
theorem fwd1 (h : sa_impl% "MorphismsWellMixed.wmDApply") : S1 := by
  intro σ κ q u v
  exact congrArg (fun p : MA σ => p.1) (h κ q u v)

@[sa_forward "MorphismsWellMixed.wmDApply" 2]
theorem fwd2 (h : sa_impl% "MorphismsWellMixed.wmDApply") : S2 := by
  intro σ κ q u v
  have e := congrArg (fun p : MA σ => p.2) (h κ q u v)
  exact e

@[sa_backward "MorphismsWellMixed.wmDApply"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "MorphismsWellMixed.wmDApply" := by
  intro σ κ q u v
  show ((wmD κ q u v).1, (wmD κ q u v).2) = _
  exact Eq.trans (congrArg (fun a => (a, (wmD κ q u v).2)) (s1 κ q u v))
    (congrArg (fun b => (q * Real.exp (κ * (u.1 - 1)) * v.2.1 +
      q * u.2.1 * κ * Real.exp (κ * (u.1 - 1)) * v.1, b)) (s2 κ q u v))

end Alignment.Shadows.MorphismsWellMixed.WmDApply

/-! ## `MorphismsWellMixed.hasFDerivAtWmMap` -/

namespace Alignment.Shadows.MorphismsWellMixed.HasFDerivAtWmMap

sa_claim "MorphismsWellMixed.hasFDerivAtWmMap" group "MorphismsWellMixed" required
  text "`wmMap κ q` has derivative `wmD κ q u` at every `u`."
  impl NEP.hasFDerivAt_wmMap

@[sa_forward "MorphismsWellMixed.hasFDerivAtWmMap" 1]
theorem fwd1 (h : sa_impl% "MorphismsWellMixed.hasFDerivAtWmMap") : S1 := by
  intro σ _ κ q u
  exact h κ q u

@[sa_backward "MorphismsWellMixed.hasFDerivAtWmMap"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsWellMixed.hasFDerivAtWmMap" := by
  intro σ _ κ q u
  exact s1 κ q u

end Alignment.Shadows.MorphismsWellMixed.HasFDerivAtWmMap

/-! ## `MorphismsWellMixed.wmFieldEq`

The impl `wm_field_eq_fderiv` is stated with `fderiv ℝ (wmMap κ q) u`, as the shadows are, so no
bridge is needed. The bridge `bridge_wmD` is kept only because `ReviewedBridges.lean` holds a
review record for it (the earlier impl `wm_field_eq` was stated with `wmD`). No checker uses it.
The backward check splits `r : Rxn σ` by cases (a data recursor) into the four T_EB types. -/

namespace Alignment.Shadows.MorphismsWellMixed.WmFieldEq

sa_claim "MorphismsWellMixed.wmFieldEq" group "MorphismsWellMixed" required
  text "**Per-reaction identity behind M1.** The derivative of `wmMap` carries the well-mixed EB field of each T_EB reaction `r` to the mass-action field of `c_κ r`."
  impl NEP.wm_field_eq_fderiv

/-- Bridge (reviewed earlier; now UNUSED). Same identification as
`WellmixedUnitQuotient.bridge_wmD`: the trusted `wmD κ q u` is Mathlib's
`fderiv ℝ (wmMap κ q) u` (finite `σ`). Kept only so that the existing review record in
`ReviewedBridges.lean` still resolves. -/
@[sa_bridge "MorphismsWellMixed.wmFieldEq"]
theorem bridge_wmD {σ : Type} [Fintype σ] (κ q : ℝ) (u : WM σ) :
    wmD κ q u = fderiv ℝ (wmMap κ q) u :=
  wmD_eq_fderiv_aux κ q u

@[sa_forward "MorphismsWellMixed.wmFieldEq" 1]
theorem fwd1 (h : sa_impl% "MorphismsWellMixed.wmFieldEq") : S1 := by
  intro σ _ _ κ q J X τ u
  exact h κ q (Rxn.contact J X τ) u

@[sa_forward "MorphismsWellMixed.wmFieldEq" 2]
theorem fwd2 (h : sa_impl% "MorphismsWellMixed.wmFieldEq") : S2 := by
  intro σ _ _ κ q Y ν u
  exact h κ q (Rxn.exit Y ν) u

@[sa_forward "MorphismsWellMixed.wmFieldEq" 3]
theorem fwd3 (h : sa_impl% "MorphismsWellMixed.wmFieldEq") : S3 := by
  intro σ _ _ κ q X Y a u
  exact h κ q (Rxn.trans X (some Y) a) u

@[sa_forward "MorphismsWellMixed.wmFieldEq" 4]
theorem fwd4 (h : sa_impl% "MorphismsWellMixed.wmFieldEq") : S4 := by
  intro σ _ _ κ q X a u
  exact h κ q (Rxn.trans X none a) u

@[sa_backward "MorphismsWellMixed.wmFieldEq"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) :
    sa_impl% "MorphismsWellMixed.wmFieldEq" := by
  intro σ _ _ κ q r u
  cases r with
  | contact J X τ => exact s1 κ q J X τ u
  | exit Y ν => exact s2 κ q Y ν u
  | trans X Y a =>
    cases Y with
    | some Y => exact s3 κ q X Y a u
    | none => exact s4 κ q X a u

end Alignment.Shadows.MorphismsWellMixed.WmFieldEq

/-! ## `MorphismsWellMixed.wmLiftXiEqZero` -/

namespace Alignment.Shadows.MorphismsWellMixed.WmLiftXiEqZero

sa_claim "MorphismsWellMixed.wmLiftXiEqZero" group "MorphismsWellMixed" required
  text "Without exits the ξ-component of the well-mixed field vanishes."
  impl NEP.wmLift_ξ_eq_zero

@[sa_forward "MorphismsWellMixed.wmLiftXiEqZero" 1]
theorem fwd1 (h : sa_impl% "MorphismsWellMixed.wmLiftXiEqZero") : S1 := by
  intro σ _ κ q rs hrs u
  exact h κ q rs hrs u

@[sa_backward "MorphismsWellMixed.wmLiftXiEqZero"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsWellMixed.wmLiftXiEqZero" := by
  intro σ _ κ q rs hrs u
  exact s1 κ q rs hrs u

end Alignment.Shadows.MorphismsWellMixed.WmLiftXiEqZero

/-! ## `MorphismsWellMixed.wmSys1Incl`

`inclXi1` is `fun w => (w.1, 1, w.2)` by definition, and `IsSemiconj` unfolds to the conjunction
in S1. -/

namespace Alignment.Shadows.MorphismsWellMixed.WmSys1Incl

sa_claim "MorphismsWellMixed.wmSys1Incl" group "MorphismsWellMixed" required
  text "For an exit-free model, `(θ, x) ↦ (θ, 1, x)` is a semiconjugacy from `wmSys1` to `wmSys` (the model on `(θ; x)` is the restriction to the invariant slice ξ = 1)."
  impl NEP.wmSys1_incl

@[sa_forward "MorphismsWellMixed.wmSys1Incl" 1]
theorem fwd1 (h : sa_impl% "MorphismsWellMixed.wmSys1Incl") : S1 := by
  intro σ _ _ κ q rs hrs
  exact h κ q rs hrs

@[sa_backward "MorphismsWellMixed.wmSys1Incl"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsWellMixed.wmSys1Incl" := by
  intro σ _ _ κ q rs hrs
  exact s1 κ q rs hrs

end Alignment.Shadows.MorphismsWellMixed.WmSys1Incl
