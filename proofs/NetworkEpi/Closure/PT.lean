import NetworkEpi.Semantics.PoissonSIR
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# L4f: Poisson type ⇔ constant closure (M8)

DESIGN_NetworkEpiCore.md §D.5, row **M8**: "PT ⇔ constant closure | On an interval I with ψ > 0:
K_ψ ≡ κ ⇔ ψ' = αψ^κ. Proof of ⇒: d/dx(ψ'ψ^{−κ}) = ψ^{−κ−1}(ψψ'' − κψ'²) = 0. So NBM's constant
closure ⟨k(k−1)⟩/⟨k⟩² is exact **iff** the degree distribution is PT | theorem | [P] KKR 2023";
§D.7 table: "`(∀ x ∈ I, ψ x * ψ'' x = κ * ψ' x ^ 2) ↔ ∃ α, ∀ x ∈ I, ψ' x = α * ψ x ^ κ` (with
ψ > 0 on I; `is_const_of_deriv_eq_zero`)"; §0: "A degree PGF ψ is PT if ψ' = αψ^κ".

## Results

* `pt_iff_const_closure` (both directions, product form of the design's §D.7 table);
* `pt_iff_closureK` (the ratio form `K_ψ = ψψ''/ψ'² ≡ κ`, where ψ' ≠ 0);
* `pt_constants_at_one` (and `pt_closure_at_one`): if moreover `1 ∈ I` and `ψ(1) = 1`, the
  constants are `α = ψ'(1)` and `κ = ψ''(1)/ψ'(1)²` (the value of NBM's constant closure,
  `closure_constant(d)`); the value of κ, and `K_ψ(1)` itself, need `ψ'(1) ≠ 0`;
* `poisson_isPT` (and `poisson_closureK`): the Poisson PGF is PT with `α = μ`, `κ = 1`.

Intervals are convex sets with nonempty interior (for example `(0, 1]`, `[a, b]` with `a < b`, or
an open interval), and derivatives are taken within I, so one-sided derivatives at end points
suffice. The exponent `ψ^κ` is the real power `Real.rpow`, defined since ψ > 0.
-/

namespace NEP

/-- The DSA closure coefficient `K_ψ(θ) = ψ(θ)ψ''(θ)/ψ'(θ)²` of a configuration network
(DESIGN §D.5 M6, M8). -/
noncomputable def CNet.closureK (N : CNet) (θ : ℝ) : ℝ := N.ψ θ * N.ψ'' θ / N.ψ' θ ^ 2

section PT
variable {ψ ψ' ψ'' : ℝ → ℝ} {I : Set ℝ}

/-- The derivative of `ψ'ψ^{−κ}` within `I`, when ψ > 0 at `x`:
`ψ''ψ^{−κ} − κψ'²ψ^{−κ−1} = ψ^{−κ−1}(ψψ'' − κψ'²)`. -/
lemma hasDerivWithinAt_pt_quotient (κ : ℝ) {x : ℝ} (hpos : 0 < ψ x)
    (hψ : HasDerivWithinAt ψ (ψ' x) I x) (hψ' : HasDerivWithinAt ψ' (ψ'' x) I x) :
    HasDerivWithinAt (fun y => ψ' y * ψ y ^ (-κ))
      (ψ x ^ (-κ - 1) * (ψ x * ψ'' x - κ * ψ' x ^ 2)) I x := by
  have h := hψ'.mul (hψ.rpow_const (p := -κ) (Or.inl hpos.ne'))
  convert h using 1
  have e : ψ x ^ (-κ) = ψ x ^ (-κ - 1) * ψ x := by
    rw [← Real.rpow_add_one hpos.ne']
    ring_nf
  rw [e]
  ring

/-- The derivative of `ψ'ψ^{−κ}` within `I` in expanded form, when ψ > 0 at `x`:
`ψ''ψ^{−κ} − κψ'²ψ^{−κ−1}` (equal to the factored form of `hasDerivWithinAt_pt_quotient`). -/
lemma hasDerivWithinAt_pt_quotient_expanded (κ : ℝ) {x : ℝ} (hpos : 0 < ψ x)
    (hψ : HasDerivWithinAt ψ (ψ' x) I x) (hψ' : HasDerivWithinAt ψ' (ψ'' x) I x) :
    HasDerivWithinAt (fun y => ψ' y * ψ y ^ (-κ))
      (ψ'' x * ψ x ^ (-κ) - κ * ψ' x ^ 2 * ψ x ^ (-κ - 1)) I x := by
  have h := hasDerivWithinAt_pt_quotient κ hpos hψ hψ'
  convert h using 1
  have e : ψ x ^ (-κ) = ψ x ^ (-κ - 1) * ψ x := by
    rw [← Real.rpow_add_one hpos.ne']
    ring_nf
  rw [e]
  ring

/-- **Poisson type ⇔ constant closure (M8), both directions.**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M8): "PT ⇔ constant closure | On an interval I
with ψ > 0: K_ψ ≡ κ ⇔ ψ' = αψ^κ. Proof of ⇒: d/dx(ψ'ψ^{−κ}) = ψ^{−κ−1}(ψψ'' − κψ'²) = 0. So
NBM's constant closure ⟨k(k−1)⟩/⟨k⟩² is exact **iff** the degree distribution is PT"; §D.7, L4d
`Closure/PT`: "`(∀ x ∈ I, ψ x * ψ'' x = κ * ψ' x ^ 2) ↔ ∃ α, ∀ x ∈ I, ψ' x = α * ψ x ^ κ` (with
ψ > 0 on I; `is_const_of_deriv_eq_zero`)".

Lean statement: let `I ⊆ ℝ` be convex with nonempty interior (an interval with more than one
point, possibly containing end points), and let `ψ, ψ', ψ'' : ℝ → ℝ` satisfy, at every `x ∈ I`,
`ψ(x) > 0`, `ψ'(x)` is the derivative of ψ within I at x, and `ψ''(x)` is the derivative of ψ'
within I at x. Then for every real κ: `ψ(x)ψ''(x) = κψ'(x)²` for all `x ∈ I` if and only if there
is a real α with `ψ'(x) = αψ(x)^κ` for all `x ∈ I` (real power).

Scope: an analytic statement about ψ on I; the ratio form `K_ψ = ψψ''/ψ'² ≡ κ` is
`pt_iff_closureK` (it needs ψ' ≠ 0). That the constant-closure pairwise model is then exact is
`NEP.eb_to_pws_const`; that a non-PT ψ makes it inexact along some trajectory is not formalised. -/
theorem pt_iff_const_closure (hI : Convex ℝ I) (hIi : (interior I).Nonempty)
    (hpos : ∀ x ∈ I, 0 < ψ x) (hψ : ∀ x ∈ I, HasDerivWithinAt ψ (ψ' x) I x)
    (hψ' : ∀ x ∈ I, HasDerivWithinAt ψ' (ψ'' x) I x) (κ : ℝ) :
    (∀ x ∈ I, ψ x * ψ'' x = κ * ψ' x ^ 2) ↔ ∃ α : ℝ, ∀ x ∈ I, ψ' x = α * ψ x ^ κ := by
  obtain ⟨x₀, hx₀⟩ := hIi
  have hx₀I : x₀ ∈ I := interior_subset hx₀
  constructor
  · intro hK
    have hd : ∀ x ∈ I, HasDerivWithinAt (fun y => ψ' y * ψ y ^ (-κ)) 0 I x := by
      intro x hx
      have h := hasDerivWithinAt_pt_quotient κ (hpos x hx) (hψ x hx) (hψ' x hx)
      rwa [hK x hx, sub_self, mul_zero] at h
    refine ⟨ψ' x₀ * ψ x₀ ^ (-κ), fun x hx => ?_⟩
    have hc : ψ' x * ψ x ^ (-κ) = ψ' x₀ * ψ x₀ ^ (-κ) :=
      const_of_hasDerivWithinAt_zero (g := fun y => ψ' y * ψ y ^ (-κ)) hI hd hx₀I hx
    rw [← hc, Real.rpow_neg (hpos x hx).le]
    have : ψ x ^ κ ≠ 0 := (Real.rpow_pos_of_pos (hpos x hx) κ).ne'
    field_simp
  · rintro ⟨α, hα⟩ x hx
    have h1 : HasDerivWithinAt (fun y => α * ψ y ^ κ) (α * (ψ' x * κ * ψ x ^ (κ - 1))) I x :=
      ((hψ x hx).rpow_const (Or.inl (hpos x hx).ne')).const_mul α
    have h2 : HasDerivWithinAt ψ' (α * (ψ' x * κ * ψ x ^ (κ - 1))) I x :=
      h1.congr_of_mem (fun y hy => hα y hy) hx
    have hu := (uniqueDiffOn_convex hI ⟨x₀, hx₀⟩ x hx).eq_deriv I (hψ' x hx) h2
    rw [hu, Real.rpow_sub_one (hpos x hx).ne', hα x hx]
    have : ψ x ≠ 0 := (hpos x hx).ne'
    field_simp

/-- **PT ⇔ K_ψ ≡ κ in ratio form (M8).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M8): "On an interval I with ψ > 0: K_ψ ≡ κ ⇔
ψ' = αψ^κ"; M6: "K_ψ = ψψ''/ψ'²".

Lean statement: let `N` be a configuration network (functions ψ, ψ', ψ''), and `I ⊆ ℝ` convex with
nonempty interior such that at every `x ∈ I`: `ψ(x) > 0`, `ψ'(x) ≠ 0`, ψ' is the derivative of ψ
within I and ψ'' the derivative of ψ' within I. Then for every real κ: the closure coefficient
`K_ψ(x) = ψ(x)ψ''(x)/ψ'(x)²` equals κ for all `x ∈ I` if and only if there is a real α with
`ψ'(x) = αψ(x)^κ` for all `x ∈ I`. -/
theorem pt_iff_closureK (N : CNet) (hI : Convex ℝ I) (hIi : (interior I).Nonempty)
    (hpos : ∀ x ∈ I, 0 < N.ψ x) (hne : ∀ x ∈ I, N.ψ' x ≠ 0)
    (hψ : ∀ x ∈ I, HasDerivWithinAt N.ψ (N.ψ' x) I x)
    (hψ' : ∀ x ∈ I, HasDerivWithinAt N.ψ' (N.ψ'' x) I x) (κ : ℝ) :
    (∀ x ∈ I, N.closureK x = κ) ↔ ∃ α : ℝ, ∀ x ∈ I, N.ψ' x = α * N.ψ x ^ κ := by
  rw [← pt_iff_const_closure hI hIi hpos hψ hψ' κ]
  refine forall₂_congr fun x hx => ?_
  have h2 : N.ψ' x ^ 2 ≠ 0 := pow_ne_zero 2 (hne x hx)
  rw [CNet.closureK, div_eq_iff h2]

/-- **The PT constants at θ = 1 (M8).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M8): "So NBM's constant closure ⟨k(k−1)⟩/⟨k⟩² is
exact **iff** the degree distribution is PT"; §C.1: "closure_constant(d) # K_ψ(1) =
ψ''(1)/ψ'(1)²  (NBM's heterogeneous constant closure)".

Lean statement: under the hypotheses of `pt_iff_const_closure` (I convex with nonempty interior,
ψ > 0 on I, derivative relations within I), assume moreover `1 ∈ I`, `ψ(1) = 1` and `ψ'(1) ≠ 0`.
If `ψ'(x) = αψ(x)^κ` for all `x ∈ I`, then `α = ψ'(1)` and `κ = ψ''(1)/ψ'(1)²`. So the only
constant closure that a PT degree distribution makes exact is `K_ψ(1) = ψ''(1)/ψ'(1)²`. -/
theorem pt_closure_at_one (hI : Convex ℝ I) (hIi : (interior I).Nonempty)
    (hpos : ∀ x ∈ I, 0 < ψ x) (hψ : ∀ x ∈ I, HasDerivWithinAt ψ (ψ' x) I x)
    (hψ' : ∀ x ∈ I, HasDerivWithinAt ψ' (ψ'' x) I x) (h1 : (1 : ℝ) ∈ I) (hψ1 : ψ 1 = 1)
    (hm : ψ' 1 ≠ 0) {α κ : ℝ} (hα : ∀ x ∈ I, ψ' x = α * ψ x ^ κ) :
    α = ψ' 1 ∧ κ = ψ'' 1 / ψ' 1 ^ 2 := by
  have hK := (pt_iff_const_closure hI hIi hpos hψ hψ' κ).2 ⟨α, hα⟩ 1 h1
  refine ⟨?_, ?_⟩
  · have := hα 1 h1
    rw [hψ1, Real.one_rpow, mul_one] at this
    exact this.symm
  · rw [hψ1, one_mul] at hK
    rw [hK]
    field_simp

/-- **The PT constants at θ = 1 (M8), with `α = ψ'(1)` unconditional.**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M8): "So NBM's constant closure ⟨k(k−1)⟩/⟨k⟩² is
exact **iff** the degree distribution is PT"; §C.1: "closure_constant(d) # K_ψ(1) =
ψ''(1)/ψ'(1)²  (NBM's heterogeneous constant closure)".

Lean statement: let `N` be a configuration network and `I ⊆ ℝ` convex with nonempty interior such
that, at every `x ∈ I`, `ψ(x) > 0`, `ψ'(x)` is the derivative of ψ within I and `ψ''(x)` the
derivative of ψ' within I; assume `1 ∈ I` and `ψ(1) = 1`. If `ψ'(x) = αψ(x)^κ` for all `x ∈ I`,
then `α = ψ'(1)`; and, if moreover `ψ'(1) ≠ 0`, then `κ = ψ''(1)/ψ'(1)²` and `κ` equals the
closure coefficient `K_ψ(1) = ψ(1)ψ''(1)/ψ'(1)²` (`N.closureK 1`). -/
theorem pt_constants_at_one (N : CNet) (hI : Convex ℝ I) (hIi : (interior I).Nonempty)
    (hpos : ∀ x ∈ I, 0 < N.ψ x) (hψ : ∀ x ∈ I, HasDerivWithinAt N.ψ (N.ψ' x) I x)
    (hψ' : ∀ x ∈ I, HasDerivWithinAt N.ψ' (N.ψ'' x) I x) (h1 : (1 : ℝ) ∈ I)
    (hψ1 : N.ψ 1 = 1) {α κ : ℝ} (hα : ∀ x ∈ I, N.ψ' x = α * N.ψ x ^ κ) :
    α = N.ψ' 1 ∧ (N.ψ' 1 ≠ 0 → κ = N.ψ'' 1 / N.ψ' 1 ^ 2) ∧
      (N.ψ' 1 ≠ 0 → κ = N.closureK 1) := by
  have ha : α = N.ψ' 1 := by
    have := hα 1 h1
    rw [hψ1, Real.one_rpow, mul_one] at this
    exact this.symm
  have hk : N.ψ' 1 ≠ 0 → κ = N.ψ'' 1 / N.ψ' 1 ^ 2 := fun hm =>
    (pt_closure_at_one hI hIi hpos hψ hψ' h1 hψ1 hm hα).2
  refine ⟨ha, hk, fun hm => ?_⟩
  rw [hk hm, CNet.closureK, hψ1, one_mul]

end PT

/-- **The Poisson PGF is of Poisson type with κ = 1 (M8, Poisson instance).**

Design statement (DESIGN_NetworkEpiCore.md §0): "**Poisson type (PT).** A degree PGF ψ is PT if
ψ' = αψ^κ. This covers Poisson (κ = 1)".

Lean statement: for every real `μ ≠ 0` and every `x ∈ ℝ`, the Poisson(μ) network
`ψ(x) = e^{μ(x−1)}` satisfies `ψ'(x) = μψ(x)^1` (real power) and its closure coefficient is
`K_ψ(x) = ψψ''/ψ'² = 1`. -/
theorem poisson_closureK (μ : ℝ) (hμ : μ ≠ 0) (x : ℝ) :
    (CNet.poisson μ).ψ' x = μ * (CNet.poisson μ).ψ x ^ (1 : ℝ) ∧
      (CNet.poisson μ).closureK x = 1 := by
  refine ⟨by simp [CNet.poisson], ?_⟩
  have he : Real.exp (μ * (x - 1)) ≠ 0 := (Real.exp_pos _).ne'
  simp only [CNet.closureK, CNet.poisson]
  field_simp

/-- **The Poisson PGF is of Poisson type with α = μ, κ = 1, for every μ (M8, Poisson instance).**

Design statement (DESIGN_NetworkEpiCore.md §0): "**Poisson type (PT).** A degree PGF ψ is PT if
ψ' = αψ^κ. This covers Poisson (κ = 1)".

Lean statement: for every real `μ` (including `μ = 0`) and every `x ∈ ℝ`, the Poisson(μ) network
`ψ(x) = e^{μ(x−1)}` satisfies `ψ'(x) = μψ(x)^1` (real power). -/
theorem poisson_isPT (μ x : ℝ) :
    (CNet.poisson μ).ψ' x = μ * (CNet.poisson μ).ψ x ^ (1 : ℝ) := by
  simp [CNet.poisson]

end NEP
