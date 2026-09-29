import NetworkEpi.Semantics.PoissonSIR
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Regularity of the EB field, local solutions and non-vacuity of `conservation`

DESIGN_NetworkEpiCore.md §D.3: "Objects of **Dyn** are (V, F): V a finite-dimensional real normed
space, F: V → V a C¹ vector field"; §D.4: "Conservation θ = φ_S + Σφ_X holds".

The conservation laws of `NetworkEpi.Semantics.EB` are stated for solutions on a time interval
`I ∋ 0`. This module shows that their hypotheses can be met for every T_EB model:

* `contDiffAt_lift`: the EB field `lift N q rs` is `C^n` at every state whose θ is a point where
  ψ, ψ', ψ'' are `C^n`. `contDiff_lift`: if ψ, ψ', ψ'' are `C¹` everywhere (for example Poisson),
  the EB model `ebSys N q rs` is an object of the design's category **Dyn**.
* `exists_local_solution`: by the Picard–Lindelöf theorem, from every such state there is a
  solution on an open interval `(−ε, ε)`.
* `conservation_local`: for every removal-free T_EB model on a network whose degree data are `C¹`
  near θ = 1, with `ψ''` the derivative of `ψ'` near 1 and `ψ'(1) ≠ 0`, there is a solution on
  some `(−ε, ε)` from the design's initial condition, and `θ = φ_S + Σ_X φ_X` holds along it.
  `conservation_local_poisson` specialises this to Poisson(μ), `μ ≠ 0`, and `seir_conservation_local`
  to EB SEIR on Poisson(5) with τ = 1/6, σ = 1/3, γ = 1/4 and φ_I(0) = 0.01: a model with no
  global solution (numerically, it blows up backward at t ≈ −7.33).
-/

open Filter Topology

namespace NEP

variable {σ : Type} [Fintype σ] [DecidableEq σ]

section Regularity

/-- `Pi.single Y` applied to a `C^n` function is `C^n` (a `fun_prop` rule). -/
@[fun_prop] lemma contDiffAt_pi_single {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} (Y : σ) {g : E → ℝ} {u : E} (hg : ContDiffAt ℝ n g u) :
    ContDiffAt ℝ n (fun u => (Pi.single Y (g u) : σ → ℝ)) u := by
  rw [contDiffAt_pi]
  intro Z
  by_cases h : Z = Y
  · subst h
    simpa using hg
  · simpa [Pi.single_apply, h] using contDiffAt_const

omit [Fintype σ] in
/-- The EB field of a contact `s + J → X + J`, written with the coordinate projections. -/
lemma ebField_contact_eq (N : CNet) (q : ℝ) (J X : σ) (τ : ℝ) :
    ebField N q (.contact J X τ) = fun u : EB σ =>
      (-(τ * u.2.2.1 J), 0,
        Pi.single X (τ * u.2.2.1 J * (q * u.2.1 * N.ψ'' u.1 / N.ψ' 1)) -
          Pi.single J (τ * u.2.2.1 J),
        Pi.single X (τ * u.2.2.1 J * (q * u.2.1 * N.ψ' u.1))) := by
  funext ⟨θ, ξ, φ, p⟩
  rfl

omit [Fintype σ] in
/-- The EB field of an exit `s → Y`, written with the coordinate projections. -/
lemma ebField_exit_eq (N : CNet) (q : ℝ) (Y : σ) (ν : ℝ) :
    ebField N q (.exit Y ν) = fun u : EB σ =>
      (0, -(ν * u.2.1), Pi.single Y (ν * (q * u.2.1 * N.ψ' u.1 / N.ψ' 1)),
        Pi.single Y (ν * (q * u.2.1 * N.ψ u.1))) := by
  funext ⟨θ, ξ, φ, p⟩
  rfl

omit [Fintype σ] in
/-- The EB field of a removal `X → ∅`, written with the coordinate projections. -/
lemma ebField_remove_eq (N : CNet) (q : ℝ) (X : σ) (a : ℝ) :
    ebField N q (.trans X none a) = fun u : EB σ =>
      ((0 : ℝ), (0 : ℝ), -Pi.single X (a * u.2.2.1 X), -Pi.single X (a * u.2.2.2 X)) := by
  funext ⟨θ, ξ, φ, p⟩
  rfl

omit [Fintype σ] in
/-- The EB field of a progression `X → Y`, written with the coordinate projections. -/
lemma ebField_progress_eq (N : CNet) (q : ℝ) (X Y : σ) (a : ℝ) :
    ebField N q (.trans X (some Y) a) = fun u : EB σ =>
      ((0 : ℝ), (0 : ℝ), Pi.single Y (a * u.2.2.1 X) - Pi.single X (a * u.2.2.1 X),
        Pi.single Y (a * u.2.2.2 X) - Pi.single X (a * u.2.2.2 X)) := by
  funext ⟨θ, ξ, φ, p⟩
  rfl

omit [Fintype σ] in
/-- **The contact row of the EB field table (DESIGN §D.4), one summand per table line.** For a
contact `s + J → X + J` at rate `τ`: `θ̇ = −τφ_J`, `ξ̇ = 0`,
`φ̇ = e_J·(−τφ_J) + e_X·(τφ_J·qξψ''(θ)/ψ'(1))` and `pop' = e_X·(τφ_J·qξψ'(θ))`. -/
theorem ebField_contact_table (N : CNet) (q : ℝ) (J X : σ) (τ : ℝ) :
    ebField N q (.contact J X τ) = fun u : EB σ =>
      (-(τ * u.2.2.1 J), 0,
        Pi.single J (-(τ * u.2.2.1 J)) +
          Pi.single X (τ * u.2.2.1 J * (q * u.2.1 * N.ψ'' u.1 / N.ψ' 1)),
        Pi.single X (τ * u.2.2.1 J * (q * u.2.1 * N.ψ' u.1))) := by
  rw [ebField_contact_eq]
  funext u
  simp only [Pi.single_neg, sub_eq_add_neg, add_comm]

omit [Fintype σ] in
/-- **The removal row of the EB field table (DESIGN §D.4).** For a removal `X → ∅` at rate `a`:
`θ̇ = ξ̇ = 0`, `φ̇ = e_X·(−aφ_X)`, `pop' = e_X·(−a pop_X)` (no gains). -/
theorem ebField_remove_table (N : CNet) (q : ℝ) (X : σ) (a : ℝ) :
    ebField N q (.trans X none a) = fun u : EB σ =>
      ((0 : ℝ), (0 : ℝ), Pi.single X (-(a * u.2.2.1 X)), Pi.single X (-(a * u.2.2.2 X))) := by
  rw [ebField_remove_eq]
  funext u
  rw [Pi.single_neg, Pi.single_neg]

omit [Fintype σ] in
/-- **The progression row of the EB field table (DESIGN §D.4), one summand per table term.** For
a progression `X → Y` at rate `a`: `θ̇ = ξ̇ = 0`, `φ̇ = e_X·(−aφ_X) + e_Y·(aφ_X)`,
`pop' = e_X·(−a pop_X) + e_Y·(a pop_X)`. -/
theorem ebField_progress_table (N : CNet) (q : ℝ) (X Y : σ) (a : ℝ) :
    ebField N q (.trans X (some Y) a) = fun u : EB σ =>
      ((0 : ℝ), (0 : ℝ), Pi.single X (-(a * u.2.2.1 X)) + Pi.single Y (a * u.2.2.1 X),
        Pi.single X (-(a * u.2.2.2 X)) + Pi.single Y (a * u.2.2.2 X)) := by
  rw [ebField_progress_eq]
  funext u
  simp only [Pi.single_neg, sub_eq_add_neg, add_comm]

/-- The EB field of one reaction is `C^n` at every state `u` such that ψ, ψ' and ψ'' are `C^n`
at `θ = u.1`. -/
theorem contDiffAt_ebField (N : CNet) (q : ℝ) (r : Rxn σ) {u : EB σ} {n : WithTop ℕ∞}
    (hψ : ContDiffAt ℝ n N.ψ u.1) (hψ' : ContDiffAt ℝ n N.ψ' u.1)
    (hψ'' : ContDiffAt ℝ n N.ψ'' u.1) : ContDiffAt ℝ n (ebField N q r) u := by
  have h0 : ContDiffAt ℝ n (fun u : EB σ => N.ψ u.1) u := hψ.comp u contDiffAt_fst
  have h1 : ContDiffAt ℝ n (fun u : EB σ => N.ψ' u.1) u := hψ'.comp u contDiffAt_fst
  have h2 : ContDiffAt ℝ n (fun u : EB σ => N.ψ'' u.1) u := hψ''.comp u contDiffAt_fst
  cases r with
  | contact J X τ =>
      rw [ebField_contact_eq]
      fun_prop (disch := assumption)
  | exit Y ν =>
      rw [ebField_exit_eq]
      fun_prop (disch := assumption)
  | trans X Y a =>
      cases Y with
      | none =>
          rw [ebField_remove_eq]
          fun_prop
      | some Y =>
          rw [ebField_progress_eq]
          fun_prop

/-- **The EB field of a reaction list is `C^n` where the degree data are.** For every T_EB
reaction list `rs`, the EB field `lift N q rs` is `C^n` at every state `u` such that ψ, ψ' and
ψ'' are `C^n` at `θ = u.1`. -/
theorem contDiffAt_lift (N : CNet) (q : ℝ) (rs : List (Rxn σ)) {u : EB σ} {n : WithTop ℕ∞}
    (hψ : ContDiffAt ℝ n N.ψ u.1) (hψ' : ContDiffAt ℝ n N.ψ' u.1)
    (hψ'' : ContDiffAt ℝ n N.ψ'' u.1) : ContDiffAt ℝ n (lift N q rs) u := by
  induction rs with
  | nil =>
      have : lift N q ([] : List (Rxn σ)) = fun _ => 0 := by
        funext v
        simp [lift]
      rw [this]
      exact contDiffAt_const
  | cons r rs ih =>
      have : lift N q (r :: rs) = fun v => ebField N q r v + lift N q rs v := by
        funext v
        simp [lift]
      rw [this]
      exact (contDiffAt_ebField N q r hψ hψ' hψ'').add ih

/-- **EB models on a network with C¹ degree data are objects of Dyn.**

Design statement (DESIGN_NetworkEpiCore.md §D.3): "Objects of **Dyn** are (V, F): V a
finite-dimensional real normed space, F: V → V a C¹ vector field."; §D.4, the row of the
representation functor **EB_N** with domain "Open(Petri/T_EB), N fixed".

Lean statement: let `σ` be a finite type of node species and `N` a configuration network whose
functions ψ, ψ' and ψ'' are `C^n` on all of ℝ (for example Poisson, `CNet.poisson`, with any
`n`). Then, for every seed factor `q` and every T_EB reaction list `rs` over `σ`, the EB vector
field `lift N q rs` on the finite-dimensional space `EB σ = ℝ × ℝ × (σ → ℝ) × (σ → ℝ)` is `C^n`.
With `n = 1`, the EB model `ebSys N q rs` is an object of the design's **Dyn**.

Scope: the regularity is pointwise in `contDiffAt_lift`, which covers PGFs with a pole (for
example negative binomial) at every state whose θ avoids the pole. -/
theorem contDiff_lift (N : CNet) (q : ℝ) (rs : List (Rxn σ)) {n : WithTop ℕ∞}
    (hψ : ContDiff ℝ n N.ψ) (hψ' : ContDiff ℝ n N.ψ') (hψ'' : ContDiff ℝ n N.ψ'') :
    ContDiff ℝ n (lift N q rs) :=
  contDiff_iff_contDiffAt.2 fun _ =>
    contDiffAt_lift N q rs hψ.contDiffAt hψ'.contDiffAt hψ''.contDiffAt

/-- **EB models on a network with C¹ degree data are objects of Dyn (the two conditions).**

Design statement (DESIGN_NetworkEpiCore.md §D.3): "Objects of **Dyn** are (V, F): V a
finite-dimensional real normed space, F: V → V a C¹ vector field."; §D.4, the row of the
representation functor **EB_N** with domain "Open(Petri/T_EB), N fixed".

Lean statement: let `σ` be a finite type of node species and `N` a configuration network whose
functions ψ, ψ' and ψ'' are `C¹` on all of ℝ (for example Poisson). Then, for every seed factor
`q` and every T_EB reaction list `rs` over `σ`, the EB model `ebSys N q rs` satisfies both
conditions of an object of **Dyn**: its state space `EB σ` is a finite-dimensional real normed
space, and its vector field `lift N q rs` is `C¹`. -/
theorem ebSys_mem_dyn (N : CNet) (q : ℝ) (rs : List (Rxn σ)) (hψ : ContDiff ℝ 1 N.ψ)
    (hψ' : ContDiff ℝ 1 N.ψ') (hψ'' : ContDiff ℝ 1 N.ψ'') :
    FiniteDimensional ℝ (ebSys N q rs).V ∧ ContDiff ℝ 1 (ebSys N q rs).F := by
  refine ⟨?_, contDiff_lift N q rs hψ hψ' hψ''⟩
  show FiniteDimensional ℝ (EB σ)
  infer_instance

end Regularity

section Existence

/-- **Local existence of EB solutions (Picard–Lindelöf).** For every T_EB reaction list `rs` and
every state `u₀` such that ψ, ψ' and ψ'' are `C¹` at `θ = u₀.1`, there are `ε > 0` and a curve
`x` with `x 0 = u₀` that solves the EB field of `rs` (`HasDerivAt`) at every `t ∈ (−ε, ε)`. -/
theorem exists_local_solution (N : CNet) (q : ℝ) (rs : List (Rxn σ)) (u₀ : EB σ)
    (hψ : ContDiffAt ℝ 1 N.ψ u₀.1) (hψ' : ContDiffAt ℝ 1 N.ψ' u₀.1)
    (hψ'' : ContDiffAt ℝ 1 N.ψ'' u₀.1) :
    ∃ ε > (0 : ℝ), ∃ x : ℝ → EB σ, x 0 = u₀ ∧
      ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt x (lift N q rs (x t)) t := by
  obtain ⟨x, hx0, ε, hε, hx⟩ :=
    (contDiffAt_lift N q rs hψ hψ' hψ'').exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  refine ⟨ε, hε, x, hx0, fun t ht => hx t ?_⟩
  simpa using ht

/-- **Edge conservation along a local EB solution from the design's initial condition.**

Design statement (DESIGN_NetworkEpiCore.md §D.4, Evidence): "The exit terms were checked by hand.
Conservation θ = φ_S + Σφ_X holds."

Lean statement: let `N` be a configuration network whose ψ, ψ' and ψ'' are `C¹` at θ = 1, whose
`ψ''` is the derivative of `ψ'` at every θ in a neighbourhood of 1, and with `ψ'(1) ≠ 0`. Let `q`
be the seed factor, let `rs` be a T_EB reaction list (contacts, exits and progressions `X → Y`)
with **no removal `X → ∅`**, and let `φ₀, p₀ : σ → ℝ` with `Σ_X φ₀(X) = 1 − q`. Then there are
`ε > 0` and a curve `x : ℝ → EB σ` with `x(0) = (θ, ξ, φ, pop)(0) = (1, 1, φ₀, p₀)` that solves
the EB field of `rs` (`HasDerivAt`) at every `t ∈ (−ε, ε)`, and along which
`θ(t) = φ_S(t) + Σ_X φ_X(t)`, `φ_S = qξψ'(θ)/ψ'(1)`, for every `t ∈ (−ε, ε)`. The design's
initial condition is the case `φ₀ = p₀ = ρ`, `q = 1 − Σ_X ρ_X`.

Scope: this is existence of a solution on some interval around 0 together with conservation along
it; `NEP.conservation` gives conservation along every solution on every interval. -/
theorem conservation_local (N : CNet) (q : ℝ) (hm : N.ψ' 1 ≠ 0)
    (hψ : ContDiffAt ℝ 1 N.ψ 1) (hψ' : ContDiffAt ℝ 1 N.ψ' 1) (hψ'' : ContDiffAt ℝ 1 N.ψ'' 1)
    (hd : ∀ᶠ θ in 𝓝 (1 : ℝ), HasDerivAt N.ψ' (N.ψ'' θ) θ)
    (rs : List (Rxn σ)) (hrs : ∀ r ∈ rs, r.isRemoval = false)
    (φ₀ p₀ : σ → ℝ) (hφ₀ : ∑ X, φ₀ X = 1 - q) :
    ∃ ε > (0 : ℝ), ∃ x : ℝ → EB σ, x 0 = ((1 : ℝ), (1 : ℝ), φ₀, p₀) ∧
      (∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt x (lift N q rs (x t)) t) ∧
      ∀ t ∈ Set.Ioo (-ε) ε, (x t).1 = N.phiS q (x t).1 (x t).2.1 + ∑ X, (x t).2.2.1 X := by
  obtain ⟨ε, hε, x, hx0, hx⟩ :=
    exists_local_solution N q rs ((1 : ℝ), (1 : ℝ), φ₀, p₀) hψ hψ' hψ''
  have hθ : Tendsto (fun t => (x t).1) (𝓝 0) (𝓝 1) := by
    have hc : ContinuousAt x 0 := (hx 0 ⟨by linarith, hε⟩).continuousAt
    have := (continuous_fst.continuousAt (x := x 0)).tendsto.comp hc.tendsto
    rw [hx0] at this
    exact this
  obtain ⟨δ, hδ, hδd⟩ := Metric.eventually_nhds_iff.1 (hθ.eventually hd)
  set η := min ε δ with hη
  have hηε : η ≤ ε := min_le_left _ _
  have hηδ : η ≤ δ := min_le_right _ _
  have hηpos : 0 < η := lt_min hε hδ
  have hsub : ∀ t ∈ Set.Ioo (-η) η, t ∈ Set.Ioo (-ε) ε := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hsol : ∀ t ∈ Set.Ioo (-η) η, HasDerivAt x (lift N q rs (x t)) t :=
    fun t ht => hx t (hsub t ht)
  refine ⟨η, hηpos, x, hx0, hsol, ?_⟩
  refine conservation N q hm rs hrs (convex_Ioo (-η) η) ⟨by linarith, hηpos⟩
    (fun t ht => (hsol t ht).hasDerivWithinAt) (fun t ht => hδd ?_) ?_ ?_ ?_
  · rw [Real.dist_eq, sub_zero, abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · rw [hx0]
  · rw [hx0]
  · rw [hx0]
    exact hφ₀

/-- **Edge conservation along a local EB solution from the design's initial condition
(derivatives within the interval).**

Design statement (DESIGN_NetworkEpiCore.md §D.4, Evidence): "The exit terms were checked by hand.
Conservation θ = φ_S + Σφ_X holds."

Lean statement: as `conservation_local`, with the solution property written within the open
interval: under the same hypotheses (ψ, ψ', ψ'' `C¹` at 1, `ψ''` the derivative of `ψ'` near 1,
`ψ'(1) ≠ 0`, `rs` with no removal `X → ∅`, `Σ_X φ₀(X) = 1 − q`) there are `ε > 0` and
`x : ℝ → EB σ` with `x(0) = (1, 1, φ₀, p₀)`,
`HasDerivWithinAt x (lift N q rs (x t)) (−ε, ε) t` for every `t ∈ (−ε, ε)`, and
`θ(t) = φ_S(t) + Σ_X φ_X(t)` for every `t ∈ (−ε, ε)`. On an open interval the within-derivative
and the two-sided derivative agree. -/
theorem conservation_local_within (N : CNet) (q : ℝ) (hm : N.ψ' 1 ≠ 0)
    (hψ : ContDiffAt ℝ 1 N.ψ 1) (hψ' : ContDiffAt ℝ 1 N.ψ' 1) (hψ'' : ContDiffAt ℝ 1 N.ψ'' 1)
    (hd : ∀ᶠ θ in 𝓝 (1 : ℝ), HasDerivAt N.ψ' (N.ψ'' θ) θ)
    (rs : List (Rxn σ)) (hrs : ∀ r ∈ rs, r.isRemoval = false)
    (φ₀ p₀ : σ → ℝ) (hφ₀ : ∑ X, φ₀ X = 1 - q) :
    ∃ ε > (0 : ℝ), ∃ x : ℝ → EB σ, x 0 = ((1 : ℝ), (1 : ℝ), φ₀, p₀) ∧
      (∀ t ∈ Set.Ioo (-ε) ε, HasDerivWithinAt x (lift N q rs (x t)) (Set.Ioo (-ε) ε) t) ∧
      ∀ t ∈ Set.Ioo (-ε) ε, (x t).1 = N.phiS q (x t).1 (x t).2.1 + ∑ X, (x t).2.2.1 X := by
  obtain ⟨ε, hε, x, hx0, hx, hc⟩ :=
    conservation_local N q hm hψ hψ' hψ'' hd rs hrs φ₀ p₀ hφ₀
  exact ⟨ε, hε, x, hx0, fun t ht => (hx t ht).hasDerivWithinAt, hc⟩

/-- Edge conservation along a local solution on a Poisson(μ) network, `μ ≠ 0`
(`conservation_local` for `CNet.poisson μ`): for every removal-free T_EB reaction list `rs` and
initial data `φ₀, p₀` with `Σ_X φ₀(X) = 1 − q`, there are `ε > 0` and a solution on `(−ε, ε)`
from `(1, 1, φ₀, p₀)` along which `θ = φ_S + Σ_X φ_X`. -/
theorem conservation_local_poisson (μ : ℝ) (hμ : μ ≠ 0) (q : ℝ) (rs : List (Rxn σ))
    (hrs : ∀ r ∈ rs, r.isRemoval = false) (φ₀ p₀ : σ → ℝ) (hφ₀ : ∑ X, φ₀ X = 1 - q) :
    ∃ ε > (0 : ℝ), ∃ x : ℝ → EB σ, x 0 = ((1 : ℝ), (1 : ℝ), φ₀, p₀) ∧
      (∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt x (lift (CNet.poisson μ) q rs (x t)) t) ∧
      ∀ t ∈ Set.Ioo (-ε) ε,
        (x t).1 = (CNet.poisson μ).phiS q (x t).1 (x t).2.1 + ∑ X, (x t).2.2.1 X := by
  have hm : (CNet.poisson μ).ψ' 1 ≠ 0 := by
    simp [CNet.poisson, hμ]
  have hψ : ContDiffAt ℝ 1 (CNet.poisson μ).ψ 1 := by
    show ContDiffAt ℝ 1 (fun x : ℝ => Real.exp (μ * (x - 1))) 1
    fun_prop
  have hψ' : ContDiffAt ℝ 1 (CNet.poisson μ).ψ' 1 := by
    show ContDiffAt ℝ 1 (fun x : ℝ => μ * Real.exp (μ * (x - 1))) 1
    fun_prop
  have hψ'' : ContDiffAt ℝ 1 (CNet.poisson μ).ψ'' 1 := by
    show ContDiffAt ℝ 1 (fun x : ℝ => μ ^ 2 * Real.exp (μ * (x - 1))) 1
    fun_prop
  exact conservation_local (CNet.poisson μ) q hm hψ hψ' hψ''
    (Eventually.of_forall fun θ => CNet.poisson_hasDerivAt_ψ' μ θ) rs hrs φ₀ p₀ hφ₀

/-- Edge conservation along a local solution on a Poisson(μ) network, `μ ≠ 0`, with the solution
property written within the open interval (`conservation_local_poisson` with
`HasDerivWithinAt x (lift (CNet.poisson μ) q rs (x t)) (−ε, ε) t`). -/
theorem conservation_local_poisson_within (μ : ℝ) (hμ : μ ≠ 0) (q : ℝ) (rs : List (Rxn σ))
    (hrs : ∀ r ∈ rs, r.isRemoval = false) (φ₀ p₀ : σ → ℝ) (hφ₀ : ∑ X, φ₀ X = 1 - q) :
    ∃ ε > (0 : ℝ), ∃ x : ℝ → EB σ, x 0 = ((1 : ℝ), (1 : ℝ), φ₀, p₀) ∧
      (∀ t ∈ Set.Ioo (-ε) ε,
        HasDerivWithinAt x (lift (CNet.poisson μ) q rs (x t)) (Set.Ioo (-ε) ε) t) ∧
      ∀ t ∈ Set.Ioo (-ε) ε,
        (x t).1 = (CNet.poisson μ).phiS q (x t).1 (x t).2.1 + ∑ X, (x t).2.2.1 X := by
  obtain ⟨ε, hε, x, hx0, hx, hc⟩ := conservation_local_poisson μ hμ q rs hrs φ₀ p₀ hφ₀
  exact ⟨ε, hε, x, hx0, fun t ht => (hx t ht).hasDerivWithinAt, hc⟩

end Existence

/-! ## SEIR on a Poisson network: a model with no global solution -/

/-- Node species of SEIR (the susceptible species is implicit). -/
inductive SEIRSp where
  | E | I | R
  deriving DecidableEq, Fintype

/-- SEIR as a T_EB reaction list: `s + I → E + I` at per-contact rate `τ`, `E → I` at rate
`σ` (named `a` here) and `I → R` at rate `γ`. -/
def seirRxns (τ a γ : ℝ) : List (Rxn SEIRSp) :=
  [.contact .I .E τ, .trans .E (some .I) a, .trans .I (some .R) γ]

/-- **Conservation is not vacuous for EB SEIR on Poisson(5).** With τ = 1/6, σ = 1/3, γ = 1/4,
seed φ_I(0) = pop_I(0) = 0.01 and q = 0.99 (so `Σ_X φ_X(0) = 1 − q`), there is a solution on some
interval `(−ε, ε)` from `(θ, ξ, φ, pop)(0) = (1, 1, φ₀, p₀)` along which `θ = φ_S + Σ_X φ_X`.
Integrated numerically, this model blows up backward in time at t ≈ −7.33, so it has no global
solution. -/
theorem seir_conservation_local :
    ∃ ε > (0 : ℝ), ∃ x : ℝ → EB SEIRSp,
      x 0 = ((1 : ℝ), (1 : ℝ), Pi.single SEIRSp.I (1 / 100), Pi.single SEIRSp.I (1 / 100)) ∧
      (∀ t ∈ Set.Ioo (-ε) ε,
        HasDerivAt x (lift (CNet.poisson 5) (99 / 100) (seirRxns (1 / 6) (1 / 3) (1 / 4)) (x t))
          t) ∧
      ∀ t ∈ Set.Ioo (-ε) ε,
        (x t).1 = (CNet.poisson 5).phiS (99 / 100) (x t).1 (x t).2.1 + ∑ X, (x t).2.2.1 X := by
  refine conservation_local_poisson 5 (by norm_num) (99 / 100) _ ?_ _ _ ?_
  · intro r hr
    simp only [seirRxns, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rfl
  · rw [sum_single]
    norm_num

/-- **Conservation is not vacuous for EB SEIR on Poisson(5)** (decimal form, derivatives within
the interval). With τ = 1/6, σ = 1/3, γ = 1/4, seed φ_I(0) = pop_I(0) = 0.01 and q = 0.99, there is
a solution on some interval `(−ε, ε)` (`HasDerivWithinAt` within `(−ε, ε)`) from
`(θ, ξ, φ, pop)(0) = (1, 1, 0.01·e_I, 0.01·e_I)` along which `θ = φ_S + Σ_X φ_X`. The literals
`0.01`, `0.99` are the decimal real numbers of the text. -/
theorem seir_conservation_local_within :
    ∃ ε > (0 : ℝ), ∃ x : ℝ → EB SEIRSp,
      x 0 = ((1 : ℝ), (1 : ℝ), Pi.single SEIRSp.I (0.01 : ℝ), Pi.single SEIRSp.I (0.01 : ℝ)) ∧
      (∀ t ∈ Set.Ioo (-ε) ε,
        HasDerivWithinAt x
          (lift (CNet.poisson 5) (0.99 : ℝ) (seirRxns (1 / 6) (1 / 3) (1 / 4)) (x t))
          (Set.Ioo (-ε) ε) t) ∧
      ∀ t ∈ Set.Ioo (-ε) ε,
        (x t).1 = (CNet.poisson 5).phiS (0.99 : ℝ) (x t).1 (x t).2.1 + ∑ X, (x t).2.2.1 X := by
  have e1 : (0.01 : ℝ) = 1 / 100 := by norm_num
  have e2 : (0.99 : ℝ) = 99 / 100 := by norm_num
  rw [e1, e2]
  obtain ⟨ε, hε, x, hx0, hx, hc⟩ := seir_conservation_local
  exact ⟨ε, hε, x, hx0, fun t ht => (hx t ht).hasDerivWithinAt, hc⟩

end NEP
