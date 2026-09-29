import NetworkEpi.Morphisms.Common

/-!
# L4a: the well-mixed unit EB_{WM(κ)}(P) ≅ MA(c_κ P) (M1)

DESIGN_NetworkEpiCore.md §D.5, row **M1**: "Well-mixed unit | EB_{WM(κ)}(P) on (θ; x) with
S = q e^{κ(θ−1)} is conjugate to MA(c_κ P) on S ∈ (0, q], for every exit-free T_EB model P. With
exits, (θ, ξ, x) ↦ (qξe^{κ(θ−1)}, x) is a quotient semiconjugacy | natural iso (quotient with
exits)"; §C.3, row `WellMixed(κ)`: "(θ, ξ; x_X): θ̇ = −Σ_r τ_r x_{J_r}, S = qξe^{κ(θ−1)}, x_X
gains κτ_r x_{J_r}S; conjugate to MA(c_κ P) (M1)"; §C.2: "The per-capita infection hazard is
κ Σ_r τ_r x_{J_r}, i.e. β_r = κτ_r, which is mass action. It is the **unit** of the lift".

## The EB model on `WellMixed(κ)`

Contacts are fleeting, so a stub meets a uniformly random node: the edge probabilities `φ_X` of a
configuration network are replaced by the node fractions `x_X`. The state is `(θ, ξ, x)` and the
per-reaction field (`wmField`) is, with `S = qξe^{κ(θ−1)}`:

```
contact  s + J → X + J (τ):  θ̇ += −τ x_J;         x_X' += κτ x_J S
exit     s → Y (ν):          ξ̇ += −ν ξ;            x_Y' += ν S
transition X → Y | ∅ (a):    x_X' −= a x_X;  x_Y' += a x_X   (no gain for ∅)
```

## Results

* `wellmixed_unit_semiconj`: for every T_EB model (exits allowed) and all κ, q,
  `(θ, ξ, x) ↦ (qξe^{κ(θ−1)}, x)` is a global semiconjugacy onto MA(c_κ P);
  `wellmixed_unit_quotient`: for `q ≠ 0` it is a surjective submersion.
* `wellmixed_unit`: for exit-free P, `κ ≠ 0` and `q > 0`, the model on `(θ; x)` is conjugate to
  MA(c_κ P) restricted to `S > 0` (inverse `(S, x) ↦ (1 + log(S/q)/κ, x)`), and for `κ > 0` the
  half-space `θ ≤ 1` corresponds to `S ∈ (0, q]` (`wellmixed_unit_Iic`).
* `wellmixed_unit_solution` (and `wellmixed_unit_solution_at`, `wellmixed_unit1_solution_at`,
  `wellmixed_unit_inv_solution_at`): solutions are mapped: `(θ, ξ, x) ↦ (qξe^{κ(θ−1)}, x)`
  (exits allowed) and, for exit-free P, `(θ, x) ↦ (q e^{κ(θ−1)}, x)` map EB solutions to
  solutions of MA(c_κ P); for exit-free P, `κ ≠ 0` and `q > 0` the inverse maps MA solutions that
  stay in `S > 0` (which contains `S ∈ (0, q]`) back to solutions on `(θ; x)`.
-/

open scoped BigOperators

namespace NEP

variable {σ : Type}

/-- EB coordinates `(θ, ξ, x)` on the well-mixed network `WellMixed(κ)`. -/
abbrev WM (σ : Type) := ℝ × ℝ × (σ → ℝ)

/-- The susceptible fraction `S = qξe^{κ(θ−1)}` on `WellMixed(κ)`. -/
noncomputable def wmSusc (κ q : ℝ) (u : WM σ) : ℝ := q * u.2.1 * Real.exp (κ * (u.1 - 1))

section Field
variable [DecidableEq σ]

/-- **The EB field of one reaction on `WellMixed(κ)`** (DESIGN §C.3): for `contact J X τ`,
`θ̇ = −τx_J`, `x_X' += κτx_J S`; for `exit Y ν`, `ξ̇ = −νξ`, `x_Y' += νS`; for `trans X Y a`,
`x_X' −= a x_X`, `x_Y' += a x_X` (no gain when `Y = none`). Here `S = qξe^{κ(θ−1)}`. -/
noncomputable def wmField (κ q : ℝ) : Rxn σ → WM σ → WM σ
  | .contact J X τ, u => (-(τ * u.2.2 J), 0, Pi.single X (κ * τ * u.2.2 J * wmSusc κ q u))
  | .exit Y ν, u => (0, -(ν * u.2.1), Pi.single Y (ν * wmSusc κ q u))
  | .trans X none a, u => (0, 0, -Pi.single X (a * u.2.2 X))
  | .trans X (some Y) a, u => (0, 0, Pi.single Y (a * u.2.2 X) - Pi.single X (a * u.2.2 X))

/-- The EB vector field of a reaction list on `WellMixed(κ)`. -/
noncomputable def wmLift (κ q : ℝ) (rs : List (Rxn σ)) (u : WM σ) : WM σ :=
  (rs.map fun r => wmField κ q r u).sum

/-- The EB model of `rs` on `WellMixed(κ)` as an object of `DynSys`. -/
noncomputable def wmSys [Fintype σ] (κ q : ℝ) (rs : List (Rxn σ)) : DynSys where
  V := WM σ
  F := wmLift κ q rs

/-- The rate convention `c_κ` applied to `rs`, as T_net reactions for mass action. -/
def wmTarget (κ : ℝ) (rs : List (Rxn σ)) : List (NRxn σ) :=
  (rs.map (Rxn.scaleContacts κ)).map Rxn.toNRxn

end Field

/-- The map `(θ, ξ, x) ↦ (S, x) = (qξe^{κ(θ−1)}, x)`. -/
noncomputable def wmMap (κ q : ℝ) (u : WM σ) : MA σ := (wmSusc κ q u, u.2.2)

/-- The derivative of `wmMap κ q` at `u`. -/
noncomputable def wmD (κ q : ℝ) (u : WM σ) : WM σ →L[ℝ] MA σ :=
  ((q * Real.exp (κ * (u.1 - 1))) • ((ContinuousLinearMap.fst ℝ ℝ _).comp
      (ContinuousLinearMap.snd ℝ ℝ _)) +
    (q * u.2.1 * κ * Real.exp (κ * (u.1 - 1))) • ContinuousLinearMap.fst ℝ ℝ _).prod
    ((ContinuousLinearMap.snd ℝ ℝ _).comp (ContinuousLinearMap.snd ℝ ℝ _))

/-- `wmD κ q u v = (q e^{κ(θ−1)} v_ξ + qξκ e^{κ(θ−1)} v_θ, v_x)`. -/
lemma wmD_apply (κ q : ℝ) (u v : WM σ) :
    wmD κ q u v = (q * Real.exp (κ * (u.1 - 1)) * v.2.1 +
      q * u.2.1 * κ * Real.exp (κ * (u.1 - 1)) * v.1, v.2.2) := rfl

/-- `wmMap κ q` has derivative `wmD κ q u` at every `u`. -/
lemma hasFDerivAt_wmMap [Fintype σ] (κ q : ℝ) (u : WM σ) :
    HasFDerivAt (wmMap κ q) (wmD κ q u) u := by
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
  refine (hS.prodMk hx).congr_fderiv ?_
  ext v <;> simp [wmD] <;> ring

section Semiconj
variable [Fintype σ] [DecidableEq σ]

omit [Fintype σ] in
/-- **Per-reaction identity behind M1.** The derivative of `wmMap` carries the well-mixed EB field
of each T_EB reaction `r` to the mass-action field of `c_κ r`. -/
theorem wm_field_eq (κ q : ℝ) (r : Rxn σ) (u : WM σ) :
    wmD κ q u (wmField κ q r u) = maField ((r.scaleContacts κ).toNRxn) (wmMap κ q u) := by
  obtain ⟨θ, ξ, x⟩ := u
  cases r with
  | contact J X τ =>
      simp only [wmD_apply, wmField, Rxn.scaleContacts, Rxn.toNRxn, maField, wmMap, wmSusc]
      refine Prod.ext ?_ ?_
      · ring
      · funext Z
        simp only [Pi.single_apply]
        split_ifs <;> ring
  | exit Y ν =>
      simp only [wmD_apply, wmField, Rxn.scaleContacts, Rxn.toNRxn, maField, wmMap, wmSusc]
      refine Prod.ext ?_ rfl
      ring
  | trans X Y a =>
      cases Y <;>
        simp [wmD_apply, wmField, Rxn.scaleContacts, Rxn.toNRxn, maField, wmMap]

/-- **Per-reaction identity behind M1, with the derivative `fderiv`.** For a finite type of node
species, the derivative `Dπ(u)` of `wmMap` carries the well-mixed EB field of each T_EB reaction
`r` to the mass-action field of `c_κ r` at `π(u)`. -/
theorem wm_field_eq_fderiv (κ q : ℝ) (r : Rxn σ) (u : WM σ) :
    fderiv ℝ (wmMap κ q) u (wmField κ q r u) = maField ((r.scaleContacts κ).toNRxn) (wmMap κ q u) := by
  rw [(hasFDerivAt_wmMap κ q u).fderiv]
  exact wm_field_eq κ q r u

/-- **The well-mixed unit as a semiconjugacy, with or without exits (M1).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M1): "With exits, (θ, ξ, x) ↦ (qξe^{κ(θ−1)}, x)
is a quotient semiconjugacy"; §C.3, `WellMixed(κ)`: "(θ, ξ; x_X): θ̇ = −Σ_r τ_r x_{J_r},
S = qξe^{κ(θ−1)}, x_X gains κτ_r x_{J_r}S; conjugate to MA(c_κ P) (M1)".

Lean statement: let `σ` be a finite type of node species and `rs` any T_EB reaction list over `σ`
(contacts, exits, progressions and removals), and let `κ, q` be real. Let the EB model on
`WellMixed(κ)` have state `(θ, ξ, x)` and field `wmLift κ q rs` (per contact `s + J → X + J` at
τ: `θ̇ += −τx_J`, `x_X' += κτx_J S`; per exit `s → Y` at ν: `ξ̇ += −νξ`, `x_Y' += νS`; transitions
as in mass action; `S = qξe^{κ(θ−1)}`). Then `(θ, ξ, x) ↦ (qξe^{κ(θ−1)}, x)` is a global
semiconjugacy from it to the mass-action model of `c_κ rs` (every contact rate multiplied by κ,
`maSys (wmTarget κ rs)`). -/
theorem wellmixed_unit_semiconj (κ q : ℝ) (rs : List (Rxn σ)) :
    IsSemiconj (wmSys κ q rs) (maSys (wmTarget κ rs)) (wmMap κ q) := by
  refine isSemiconj_of_hasFDerivAt (A := wmSys κ q rs) (B := maSys (wmTarget κ rs)) (wmD κ q)
    (hasFDerivAt_wmMap κ q) fun u => ?_
  change wmD κ q u (wmLift κ q rs u) = maLift (wmTarget κ rs) (wmMap κ q u)
  rw [wmLift, wmTarget, maLift, List.map_map, List.map_map]
  exact clm_list_sum_eq _ rs _ _ fun r _ => wm_field_eq κ q r u

omit [Fintype σ] [DecidableEq σ] in
/-- **The well-mixed map with exits is a quotient (M1).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M1): "With exits, (θ, ξ, x) ↦ (qξe^{κ(θ−1)}, x)
is a quotient semiconjugacy".

Lean statement: for all real `κ` and `q ≠ 0` and every finite type of node species, the map
`(θ, ξ, x) ↦ (qξe^{κ(θ−1)}, x)` is surjective and its derivative is surjective at every point
(a surjective submersion). With `wellmixed_unit_semiconj` it is a quotient semiconjugacy. -/
theorem wellmixed_unit_quotient (κ q : ℝ) (hq : q ≠ 0) :
    Function.Surjective (wmMap (σ := σ) κ q) ∧ ∀ u : WM σ, Function.Surjective (wmD κ q u) := by
  refine ⟨fun v => ⟨(1, v.1 / q, v.2), ?_⟩, fun u v => ⟨(0, v.1 / (q * Real.exp (κ * (u.1 - 1))),
    v.2), ?_⟩⟩
  · refine Prod.ext ?_ rfl
    simp only [wmMap, wmSusc, sub_self, mul_zero, Real.exp_zero, mul_one]
    field_simp
  · rw [wmD_apply]
    refine Prod.ext ?_ rfl
    have he : Real.exp (κ * (u.1 - 1)) ≠ 0 := (Real.exp_pos _).ne'
    simp only [mul_zero, add_zero]
    field_simp

omit [Fintype σ] [DecidableEq σ] in
/-- **The well-mixed map with exits is a surjective submersion (M1).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M1): "With exits, (θ, ξ, x) ↦ (qξe^{κ(θ−1)}, x)
is a quotient semiconjugacy".

Lean statement: for all real `κ` and `q ≠ 0`, the map `(θ, ξ, x) ↦ (qξe^{κ(θ−1)}, x)` is
surjective (for every type of node species), and for a finite type of node species it is
differentiable and its derivative `fderiv` is surjective at every point. -/
theorem wellmixed_unit_submersion (κ q : ℝ) (hq : q ≠ 0) :
    Function.Surjective (wmMap (σ := σ) κ q) ∧
      (∀ [Fintype σ], Differentiable ℝ (wmMap (σ := σ) κ q)) ∧
      (∀ [Fintype σ], ∀ u : WM σ, Function.Surjective (fderiv ℝ (wmMap (σ := σ) κ q) u)) := by
  refine ⟨(wellmixed_unit_quotient κ q hq).1, fun u => (hasFDerivAt_wmMap κ q u).differentiableAt,
    fun u => ?_⟩
  rw [(hasFDerivAt_wmMap κ q u).fderiv]
  exact (wellmixed_unit_quotient κ q hq).2 u

/-! ## The exit-free model on `(θ; x)` and the conjugacy -/

/-- The well-mixed EB model of an exit-free reaction list in the design's coordinates `(θ; x)`
(on the slice ξ = 1). -/
noncomputable def wmSys1 (κ q : ℝ) (rs : List (Rxn σ)) : DynSys where
  V := ℝ × (σ → ℝ)
  F w := let v := wmLift κ q rs (w.1, 1, w.2); (v.1, v.2.2)

/-- `(θ, x) ↦ (q e^{κ(θ−1)}, x)`. -/
noncomputable def wmMap1 (κ q : ℝ) (w : ℝ × (σ → ℝ)) : MA σ := wmMap κ q (w.1, 1, w.2)

/-- The inverse `(S, x) ↦ (1 + log(S/q)/κ, x)` of `wmMap1` on `S > 0`. -/
noncomputable def wmInv (κ q : ℝ) (v : MA σ) : ℝ × (σ → ℝ) := (1 + Real.log (v.1 / q) / κ, v.2)

omit [Fintype σ] in
/-- Without exits the ξ-component of the well-mixed field vanishes. -/
lemma wmLift_ξ_eq_zero (κ q : ℝ) (rs : List (Rxn σ)) (hrs : ∀ r ∈ rs, r.isExit = false)
    (u : WM σ) : (wmLift κ q rs u).2.1 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      have hr := hrs r (by simp)
      have h0 : (wmField κ q r u).2.1 = 0 := by
        cases r with
        | contact J X τ => rfl
        | exit Y ν => simp [Rxn.isExit] at hr
        | trans X Y a => cases Y <;> rfl
      simp only [wmLift, List.map_cons, List.sum_cons, Prod.snd_add, Prod.fst_add] at ih ⊢
      rw [h0, ih (fun r' hr' => hrs r' (by simp [hr'])), add_zero]

/-- For an exit-free model, `(θ, x) ↦ (θ, 1, x)` is a semiconjugacy from `wmSys1` to `wmSys`
(the model on `(θ; x)` is the restriction to the invariant slice ξ = 1). -/
theorem wmSys1_incl (κ q : ℝ) (rs : List (Rxn σ)) (hrs : ∀ r ∈ rs, r.isExit = false) :
    IsSemiconj (wmSys1 κ q rs) (wmSys κ q rs) (fun w => (w.1, 1, w.2)) := by
  let L : (ℝ × (σ → ℝ)) →L[ℝ] WM σ := (ContinuousLinearMap.fst ℝ ℝ _).prod
    ((0 : (ℝ × (σ → ℝ)) →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ _))
  have hL : ∀ w : ℝ × (σ → ℝ), HasFDerivAt (fun w : ℝ × (σ → ℝ) => ((w.1, 1, w.2) : WM σ)) L w := by
    intro w
    have h : (fun w : ℝ × (σ → ℝ) => ((w.1, 1, w.2) : WM σ)) =
        fun w => ((0 : ℝ), (1 : ℝ), (0 : σ → ℝ)) + L w := by
      funext w
      simp [L]
    rw [h]
    exact L.hasFDerivAt.const_add _
  refine isSemiconj_of_hasFDerivAt (A := wmSys1 κ q rs) (B := wmSys κ q rs) (fun _ => L) hL
    fun w => ?_
  change L ((wmLift κ q rs (w.1, 1, w.2)).1, (wmLift κ q rs (w.1, 1, w.2)).2.2) =
    wmLift κ q rs (w.1, 1, w.2)
  have h0 := wmLift_ξ_eq_zero κ q rs hrs (w.1, 1, w.2)
  simp only [L, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.zero_apply]
  exact Prod.ext rfl (Prod.ext h0.symm rfl)

/-- **The well-mixed unit (M1): a conjugacy for exit-free models.**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M1): "Well-mixed unit | EB_{WM(κ)}(P) on (θ; x)
with S = q e^{κ(θ−1)} is conjugate to MA(c_κ P) on S ∈ (0, q], for every exit-free T_EB model P
[...] | natural iso (quotient with exits)".

Lean statement: let `σ` be a finite type of node species, `rs` a T_EB reaction list over `σ` with
**no exits**, `κ ≠ 0` and `q > 0`. Let `A` be the EB model of `rs` on `WellMixed(κ)` in the
coordinates `(θ; x)` (`wmSys1`: `θ̇ = −Σ_contacts τ x_J`, `x_X' += κτ x_J q e^{κ(θ−1)}` per contact
`s + J → X + J`, transitions as in mass action) and `B` the mass-action model of `c_κ rs`. Then
`h(θ, x) = (q e^{κ(θ−1)}, x)` and `g(S, x) = (1 + log(S/q)/κ, x)` form a conjugacy between `A` (on
its whole state space) and `B` restricted to the open set `{S > 0}` (`IsConjOn`: `h` is a
semiconjugacy into `{S > 0}`, `g` a local semiconjugacy on `{S > 0}`, `g ∘ h = id`, `h ∘ g = id`
on `{S > 0}`).

Scope: for `κ > 0` the half-space `θ ≤ 1` is mapped onto `S ∈ (0, q]` (`wellmixed_unit_Iic`), so
this contains the design's "on S ∈ (0, q]". Naturality in P is not proved separately: the
conjugacy is the same formula for every exit-free P. -/
theorem wellmixed_unit (κ q : ℝ) (hκ : κ ≠ 0) (hq : 0 < q) (rs : List (Rxn σ))
    (hrs : ∀ r ∈ rs, r.isExit = false) :
    IsConjOn (wmSys1 κ q rs) (maSys (wmTarget κ rs)) Set.univ {v | 0 < v.1} (wmMap1 κ q)
      (wmInv κ q) := by
  have hh : IsSemiconj (wmSys1 κ q rs) (maSys (wmTarget κ rs)) (wmMap1 κ q) :=
    ((Semiconj.ofIsSemiconj _ (wmSys1_incl κ q rs hrs)).comp
      (Semiconj.ofIsSemiconj _ (wellmixed_unit_semiconj κ q rs))).isSemiconj
  refine isConjOn_of_inverse hh (fun v hv => ?_) (fun w => ?_) (fun w => ?_) (fun v hv => ?_)
  · have hv' : v.1 / q ≠ 0 := (div_pos hv hq).ne'
    change DifferentiableAt ℝ (fun v : MA σ => ((1 + Real.log (v.1 / q) / κ, v.2) :
      ℝ × (σ → ℝ))) v
    fun_prop (disch := exact hv')
  · change 0 < q * 1 * Real.exp (κ * (w.1 - 1))
    positivity
  · obtain ⟨θ, x⟩ := w
    change ((1 + Real.log (q * 1 * Real.exp (κ * (θ - 1)) / q) / κ, x) : ℝ × (σ → ℝ)) = (θ, x)
    have : q * 1 * Real.exp (κ * (θ - 1)) / q = Real.exp (κ * (θ - 1)) := by
      field_simp
    rw [this, Real.log_exp]
    refine Prod.ext ?_ rfl
    field_simp
    ring
  · simp only [Set.mem_setOf_eq] at hv
    obtain ⟨S, x⟩ := v
    change ((q * 1 * Real.exp (κ * (1 + Real.log (S / q) / κ - 1)), x) : MA σ) = (S, x)
    have : κ * (1 + Real.log (S / q) / κ - 1) = Real.log (S / q) := by
      field_simp
      ring
    rw [this, Real.exp_log (div_pos hv hq)]
    refine Prod.ext ?_ rfl
    field_simp

omit [Fintype σ] [DecidableEq σ] in
/-- **The half-space θ ≤ 1 corresponds to S ∈ (0, q] (M1).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M1): "EB_{WM(κ)}(P) on (θ; x) with
S = q e^{κ(θ−1)} is conjugate to MA(c_κ P) on S ∈ (0, q]".

Lean statement: for `κ > 0`, `q > 0` and every `(θ, x)`, the image `S = q e^{κ(θ−1)}` of
`(θ, x)` under the conjugacy of `wellmixed_unit` satisfies `0 < S`, and `S ≤ q ↔ θ ≤ 1`. -/
theorem wellmixed_unit_Iic (κ q : ℝ) (hκ : 0 < κ) (hq : 0 < q) (w : ℝ × (σ → ℝ)) :
    0 < (wmMap1 κ q w).1 ∧ ((wmMap1 κ q w).1 ≤ q ↔ w.1 ≤ 1) := by
  change 0 < q * 1 * Real.exp (κ * (w.1 - 1)) ∧ (q * 1 * Real.exp (κ * (w.1 - 1)) ≤ q ↔ w.1 ≤ 1)
  refine ⟨by positivity, ?_⟩
  rw [mul_one, mul_le_iff_le_one_right hq, Real.exp_le_one_iff]
  constructor
  · intro h
    by_contra h'
    push_neg at h'
    have : 0 < κ * (w.1 - 1) := mul_pos hκ (by linarith)
    linarith
  · intro h
    exact mul_nonpos_of_nonneg_of_nonpos hκ.le (by linarith)

omit [Fintype σ] [DecidableEq σ] in
/-- **The half-space θ ≤ 1 corresponds to S ∈ (0, q], as sets (M1).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M1): "EB_{WM(κ)}(P) on (θ; x) with
S = q e^{κ(θ−1)} is conjugate to MA(c_κ P) on S ∈ (0, q]".

Lean statement: for `κ > 0` and `q > 0`, the image of the half-space `{(θ, x) | θ ≤ 1}` under
`(θ, x) ↦ (q e^{κ(θ−1)}, x)` is exactly `{(S, x) | 0 < S ≤ q}`. -/
theorem wellmixed_unit_Iic_image (κ q : ℝ) (hκ : 0 < κ) (hq : 0 < q) :
    wmMap1 (σ := σ) κ q '' {w | w.1 ≤ 1} = {v | v.1 ∈ Set.Ioc 0 q} := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨h0, h1⟩ := wellmixed_unit_Iic κ q hκ hq w
    exact ⟨h0, h1.2 hw⟩
  · rintro ⟨h0, h1⟩
    refine ⟨(1 + Real.log (v.1 / q) / κ, v.2), ?_, ?_⟩
    · have hl : Real.log (v.1 / q) ≤ 0 :=
        Real.log_nonpos (div_pos h0 hq).le ((div_le_one hq).2 h1)
      change 1 + Real.log (v.1 / q) / κ ≤ 1
      have : Real.log (v.1 / q) / κ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hl hκ.le
      linarith
    · obtain ⟨S, x⟩ := v
      change ((q * 1 * Real.exp (κ * (1 + Real.log (S / q) / κ - 1)), x) : MA σ) = (S, x)
      have : κ * (1 + Real.log (S / q) / κ - 1) = Real.log (S / q) := by
        field_simp
        ring
      rw [this, Real.exp_log (div_pos h0 hq)]
      refine Prod.ext ?_ rfl
      field_simp

omit [Fintype σ] [DecidableEq σ] in
/-- **Only the half-space θ ≤ 1 goes to S ∈ (0, q] (M1).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M1): "EB_{WM(κ)}(P) on (θ; x) with
S = q e^{κ(θ−1)} is conjugate to MA(c_κ P) on S ∈ (0, q]".

Lean statement: for `κ > 0` and `q > 0`, the preimage of `{(S, x) | 0 < S ≤ q}` under
`(θ, x) ↦ (q e^{κ(θ−1)}, x)` is exactly the half-space `{(θ, x) | θ ≤ 1}`. (With
`wellmixed_unit_Iic_image`, the half-space corresponds to `S ∈ (0, q]` as image and as
preimage.) -/
theorem wellmixed_unit_Iic_preimage (κ q : ℝ) (hκ : 0 < κ) (hq : 0 < q) :
    wmMap1 (σ := σ) κ q ⁻¹' {v | v.1 ∈ Set.Ioc 0 q} = {w | w.1 ≤ 1} := by
  ext w
  obtain ⟨h0, h1⟩ := wellmixed_unit_Iic (σ := σ) κ q hκ hq w
  exact ⟨fun hw => h1.1 hw.2, fun hw => ⟨h0, h1.2 hw⟩⟩

/-- **The well-mixed unit on trajectories (M1).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M1): "EB_{WM(κ)}(P) on (θ; x) with
S = q e^{κ(θ−1)} is conjugate to MA(c_κ P) [...]. With exits, (θ, ξ, x) ↦ (qξe^{κ(θ−1)}, x) is a
quotient semiconjugacy"; §D.3: "semiconjugacies map solution curves to solution curves".

Lean statement: let `rs` be any T_EB reaction list (exits allowed) over a finite type of node
species, `κ, q` real and `I` any set of times. If `x : ℝ → WM σ` solves the well-mixed EB model of
`rs` within `I` at every `t ∈ I`, then `t ↦ (qξ(t)e^{κ(θ(t)−1)}, x(t))` solves the mass-action
model of `c_κ rs` within `I` at every `t ∈ I`. -/
theorem wellmixed_unit_solution (κ q : ℝ) (rs : List (Rxn σ)) {I : Set ℝ} {x : ℝ → WM σ}
    (hx : ∀ t ∈ I, HasDerivWithinAt x (wmLift κ q rs (x t)) I t) :
    ∀ t ∈ I, HasDerivWithinAt (fun t => wmMap κ q (x t))
      (maLift (wmTarget κ rs) (wmMap κ q (x t))) I t :=
  (Semiconj.ofIsSemiconj _ (wellmixed_unit_semiconj κ q rs)).map_solution_within
    (A := wmSys κ q rs) hx

/-- **The well-mixed unit on trajectories, two-sided derivatives, with exits (M1).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M1): "EB_{WM(κ)}(P) on (θ; x) with
S = q e^{κ(θ−1)} is conjugate to MA(c_κ P) [...]. With exits, (θ, ξ, x) ↦ (qξe^{κ(θ−1)}, x) is a
quotient semiconjugacy"; §D.3: "semiconjugacies map solution curves to solution curves".

Lean statement: let `rs` be any T_EB reaction list (exits allowed) over a finite type of node
species, `κ, q` real and `I` any set of times. If `x : ℝ → WM σ` has the two-sided derivative
`x'(t) = wmLift κ q rs (x(t))` at every `t ∈ I`, then `t ↦ (qξ(t)e^{κ(θ(t)−1)}, x(t))` has the
derivative given by the mass-action model of `c_κ rs` at every `t ∈ I`. -/
theorem wellmixed_unit_solution_at (κ q : ℝ) (rs : List (Rxn σ)) {I : Set ℝ} {x : ℝ → WM σ}
    (hx : ∀ t ∈ I, HasDerivAt x (wmLift κ q rs (x t)) t) :
    ∀ t ∈ I, HasDerivAt (fun t => wmMap κ q (x t))
      (maLift (wmTarget κ rs) (wmMap κ q (x t))) t :=
  (Semiconj.ofIsSemiconj _ (wellmixed_unit_semiconj κ q rs)).map_solution
    (A := wmSys κ q rs) hx

/-- **The well-mixed unit on trajectories of the exit-free model on `(θ; x)` (M1).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M1): "Well-mixed unit | EB_{WM(κ)}(P) on (θ; x)
with S = q e^{κ(θ−1)} is conjugate to MA(c_κ P) on S ∈ (0, q], for every exit-free T_EB model P";
§D.3: "semiconjugacies map solution curves to solution curves".

Lean statement: let `rs` be a T_EB reaction list with **no exits** over a finite type of node
species, `κ, q` real and `I` any set of times. If `w : ℝ → ℝ × (σ → ℝ)` has the two-sided
derivative given by the well-mixed EB model on `(θ; x)` (`wmSys1`) at every `t ∈ I`, then
`t ↦ (q e^{κ(θ(t)−1)}, x(t))` has the derivative given by the mass-action model of `c_κ rs` at
every `t ∈ I`. -/
theorem wellmixed_unit1_solution_at (κ q : ℝ) (rs : List (Rxn σ))
    (hrs : ∀ r ∈ rs, r.isExit = false) {I : Set ℝ} {w : ℝ → ℝ × (σ → ℝ)}
    (hw : ∀ t ∈ I, HasDerivAt w ((wmSys1 κ q rs).F (w t)) t) :
    ∀ t ∈ I, HasDerivAt (fun t => wmMap1 κ q (w t))
      (maLift (wmTarget κ rs) (wmMap1 κ q (w t))) t :=
  ((Semiconj.ofIsSemiconj _ (wmSys1_incl κ q rs hrs)).comp
    (Semiconj.ofIsSemiconj _ (wellmixed_unit_semiconj κ q rs))).map_solution
    (A := wmSys1 κ q rs) hw

/-- **The inverse of the well-mixed unit on trajectories (M1).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M1): "Well-mixed unit | EB_{WM(κ)}(P) on (θ; x)
with S = q e^{κ(θ−1)} is conjugate to MA(c_κ P) on S ∈ (0, q], for every exit-free T_EB model P";
§D.3: "semiconjugacies map solution curves to solution curves".

Lean statement: let `rs` be a T_EB reaction list with **no exits** over a finite type of node
species, `κ ≠ 0`, `q > 0` and `I` any set of times. If `v : ℝ → MA σ` has the two-sided
derivative given by the mass-action model of `c_κ rs` at every `t ∈ I` and stays in `S > 0` on
`I`, then `t ↦ (1 + log(S(t)/q)/κ, x(t))` has the derivative given by the well-mixed EB model on
`(θ; x)` at every `t ∈ I`. -/
theorem wellmixed_unit_inv_solution_at (κ q : ℝ) (hκ : κ ≠ 0) (hq : 0 < q) (rs : List (Rxn σ))
    (hrs : ∀ r ∈ rs, r.isExit = false) {I : Set ℝ} {v : ℝ → MA σ}
    (hpos : ∀ t ∈ I, 0 < (v t).1)
    (hv : ∀ t ∈ I, HasDerivAt v (maLift (wmTarget κ rs) (v t)) t) :
    ∀ t ∈ I, HasDerivAt (fun t => wmInv κ q (v t)) ((wmSys1 κ q rs).F (wmInv κ q (v t))) t :=
  (SemiconjOn.ofIsSemiconjOn _ (wellmixed_unit κ q hκ hq rs hrs).2.1).map_solution_on
    (A := maSys (wmTarget κ rs)) hv hpos

/-- **The well-mixed unit on trajectories of the exit-free model on `(θ; x)`, within a set of
times (M1).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M1): "Well-mixed unit | EB_{WM(κ)}(P) on (θ; x)
with S = q e^{κ(θ−1)} is conjugate to MA(c_κ P) on S ∈ (0, q], for every exit-free T_EB model P";
§D.3: "semiconjugacies map solution curves to solution curves".

Lean statement: let `rs` be a T_EB reaction list with **no exits** over a finite type of node
species, `κ, q` real and `I` any set of times. If `w : ℝ → ℝ × (σ → ℝ)` solves the well-mixed EB
model on `(θ; x)` (`wmSys1`) within `I` at every `t ∈ I`, then `t ↦ (q e^{κ(θ(t)−1)}, x(t))` solves
the mass-action model of `c_κ rs` within `I` at every `t ∈ I`. (`wellmixed_unit1_solution_at` is
the version with two-sided derivatives.) -/
theorem wellmixed_unit1_solution (κ q : ℝ) (rs : List (Rxn σ))
    (hrs : ∀ r ∈ rs, r.isExit = false) {I : Set ℝ} {w : ℝ → ℝ × (σ → ℝ)}
    (hw : ∀ t ∈ I, HasDerivWithinAt w ((wmSys1 κ q rs).F (w t)) I t) :
    ∀ t ∈ I, HasDerivWithinAt (fun t => wmMap1 κ q (w t))
      (maLift (wmTarget κ rs) (wmMap1 κ q (w t))) I t :=
  ((Semiconj.ofIsSemiconj _ (wmSys1_incl κ q rs hrs)).comp
    (Semiconj.ofIsSemiconj _ (wellmixed_unit_semiconj κ q rs))).map_solution_within
    (A := wmSys1 κ q rs) hw

/-- **The inverse of the well-mixed unit on trajectories, within a set of times (M1).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M1): "Well-mixed unit | EB_{WM(κ)}(P) on (θ; x)
with S = q e^{κ(θ−1)} is conjugate to MA(c_κ P) on S ∈ (0, q], for every exit-free T_EB model P";
§D.3: "semiconjugacies map solution curves to solution curves".

Lean statement: let `rs` be a T_EB reaction list with **no exits** over a finite type of node
species, `κ ≠ 0`, `q > 0` and `I` any set of times. If `v : ℝ → MA σ` solves the mass-action model
of `c_κ rs` within `I` at every `t ∈ I` and stays in `S > 0` on `I`, then
`t ↦ (1 + log(S(t)/q)/κ, x(t))` solves the well-mixed EB model on `(θ; x)` within `I` at every
`t ∈ I`. (`wellmixed_unit_inv_solution_at` is the version with two-sided derivatives.) -/
theorem wellmixed_unit_inv_solution (κ q : ℝ) (hκ : κ ≠ 0) (hq : 0 < q) (rs : List (Rxn σ))
    (hrs : ∀ r ∈ rs, r.isExit = false) {I : Set ℝ} {v : ℝ → MA σ}
    (hpos : ∀ t ∈ I, 0 < (v t).1)
    (hv : ∀ t ∈ I, HasDerivWithinAt v (maLift (wmTarget κ rs) (v t)) I t) :
    ∀ t ∈ I, HasDerivWithinAt (fun t => wmInv κ q (v t))
      ((wmSys1 κ q rs).F (wmInv κ q (v t))) I t :=
  (SemiconjOn.ofIsSemiconjOn _ (wellmixed_unit κ q hκ hq rs hrs).2.1).map_solution_within
    (A := maSys (wmTarget κ rs)) hv hpos

end Semiconj

end NEP
