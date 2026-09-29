import NetworkEpi.Morphisms.Common

/-!
# L4g: the compact SIR EBCM is a restriction of the expanded one (M9)

DESIGN_NetworkEpiCore.md §D.5, row **M9**: "Compact ⊂ expanded | W = {τφ_R + γθ = γ} is invariant
for SIR-shaped P, and W → compact is a conjugacy | restriction"; §D.3: "Examples: the compact SIR
EBCM on {τφ_R + γθ = γ}".

## The two models

*Expanded*: the general per-reaction EB model of SIR (`s + I → I + I` at per-contact rate τ,
`I → R` at γ) on a configuration network `N`, state `(θ, ξ, φ_I, φ_R, pop_I, pop_R)`.

*Compact* (`compactSIR`; Miller 2011 with the explicit seed factor q, as in
`EdgeBasedModels.jl`'s `_build_compact`): state `(θ, R)` with
`θ̇ = −τθ + τqψ'(θ)/ψ'(1) + γ(1 − θ)` and `Ṙ = γ(1 − qψ(θ) − R)`; `S = qψ(θ)`, `I = 1 − S − R`.

## Results

* `compact_W_invariant` (and `compact_W_invariant_any`): along every EB SIR solution on a time
  interval, `τφ_R + γθ` is constant,
  so the design's set `W = {τφ_R + γθ = γ}` is invariant (no assumption on ψ).
* `compact_conj` (and `compact_conj_global`): the embedding `(θ, R) ↦ (θ, 1, φ_I, φ_R, 1 − qψ(θ) − R, R)` with
  `φ_R = γ(1−θ)/τ`, `φ_I = θ − qψ'(θ)/ψ'(1) − φ_R` and the projection `(θ, …, pop_R) ↦ (θ, pop_R)`
  form a conjugacy between the compact model and the expanded model restricted to
  `W' = W ∩ {ξ = 1, θ = φ_S + φ_I + φ_R, S + pop_I + pop_R = 1}` (`τ ≠ 0`).
* `compact_solution`, `compact_solution_ic`, `compact_solution_ic_at`: for `τ ≠ 0`, every expanded
  solution from the design's initial condition (seed factor `q = 1 − ρ`) stays in `W'` and its
  image `(θ, pop_R)` solves the compact model, for derivatives within the time interval and for
  two-sided derivatives.
* `compact_solution_poisson_spec`: for `μ ≠ 0` and `τ ≠ 0` these hypotheses are met on Poisson(μ)
  networks, by a local solution (DESIGN §M.4).
-/

open scoped BigOperators

namespace NEP

/-- The compact SIR EBCM (Miller 2011, with seed factor q) on `(θ, R)`:
`θ̇ = −τθ + τqψ'(θ)/ψ'(1) + γ(1 − θ)`, `Ṙ = γ(1 − qψ(θ) − R)`. -/
noncomputable def compactSIR (N : CNet) (q τ γ : ℝ) : DynSys where
  V := ℝ × ℝ
  F w := (-τ * w.1 + τ * N.phiS q w.1 1 + γ * (1 - w.1), γ * (1 - N.susc q w.1 1 - w.2))

/-- A function on the SIR node species `{I, R}` from its two values. -/
def sirVec (a b : ℝ) : SIRSp → ℝ
  | .I => a
  | .R => b

/-- `sirVec a b` takes the value `a` at `I`. -/
@[simp] lemma sirVec_I (a b : ℝ) : sirVec a b .I = a := rfl
/-- `sirVec a b` takes the value `b` at `R`. -/
@[simp] lemma sirVec_R (a b : ℝ) : sirVec a b .R = b := rfl

/-- The sum over the SIR node species. -/
lemma sum_SIRSp (f : SIRSp → ℝ) : ∑ X, f X = f .I + f .R := by
  rw [Fintype.sum_eq_add SIRSp.I SIRSp.R (by decide)]
  intro x hx
  cases x <;> simp_all

/-- The embedding of the compact model into the expanded one:
`(θ, R) ↦ (θ, ξ = 1, φ_I = θ − φ_S − φ_R, φ_R = γ(1 − θ)/τ, pop_I = 1 − S − R, pop_R = R)`,
with `φ_S = qψ'(θ)/ψ'(1)` and `S = qψ(θ)`. -/
noncomputable def compactEmb (N : CNet) (q τ γ : ℝ) (w : ℝ × ℝ) : EB SIRSp :=
  (w.1, 1, sirVec (w.1 - N.phiS q w.1 1 - γ * (1 - w.1) / τ) (γ * (1 - w.1) / τ),
    sirVec (1 - N.susc q w.1 1 - w.2) w.2)

/-- The projection `(θ, ξ, φ, pop) ↦ (θ, pop_R)`. -/
def compactProj (u : EB SIRSp) : ℝ × ℝ := (u.1, u.2.2.2 .R)

/-- The set `W' = {ξ = 1, τφ_R + γθ = γ, θ = φ_S + φ_I + φ_R, S + pop_I + pop_R = 1}`: the
design's `W = {τφ_R + γθ = γ}` together with the constraints that the design's initial condition
imposes on every solution (`xi_const`, `conservation`, `node_conservation`). -/
def compactW (N : CNet) (q τ γ : ℝ) : Set (EB SIRSp) :=
  {u | u.2.1 = 1 ∧ τ * u.2.2.1 .R + γ * u.1 = γ ∧
    u.1 = N.phiS q u.1 u.2.1 + u.2.2.1 .I + u.2.2.1 .R ∧
    N.susc q u.1 u.2.1 + u.2.2.2 .I + u.2.2.2 .R = 1}

/-- The EB field of SIR, componentwise. -/
lemma lift_sir_apply (N : CNet) (q τ γ : ℝ) (u : EB SIRSp) :
    lift N q (sirRxns τ γ) u = (-(τ * u.2.2.1 .I), 0,
      sirVec (τ * u.2.2.1 .I * (q * u.2.1 * N.ψ'' u.1 / N.ψ' 1) - τ * u.2.2.1 .I - γ * u.2.2.1 .I)
        (γ * u.2.2.1 .I),
      sirVec (τ * u.2.2.1 .I * (q * u.2.1 * N.ψ' u.1) - γ * u.2.2.2 .I) (γ * u.2.2.2 .I)) := by
  obtain ⟨θ, ξ, φ, p⟩ := u
  have hIR : (SIRSp.I : SIRSp) ≠ SIRSp.R := by decide
  simp only [lift, sirRxns, ebField, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]
  refine Prod.ext (by simp) (Prod.ext (by simp) (Prod.ext ?_ ?_))
  · funext X
    cases X <;> simp [hIR]; ring
  · funext X
    cases X <;> simp [hIR]; ring

/-- **The design's W is invariant (M9).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M9): "W = {τφ_R + γθ = γ} is invariant for
SIR-shaped P".

Lean statement: let `N` be any configuration network (no assumption on ψ, ψ', ψ''), `q, τ, γ`
real, `I` a time interval (a convex set of times with `0 ∈ I`) and `x : ℝ → EB SIRSp` a solution of
the EB model of SIR (`s + I → I + I` at per-contact rate τ, `I → R` at γ) within `I` at every
`t ∈ I`. Then `τφ_R(t) + γθ(t) = τφ_R(0) + γθ(0)` for every `t ∈ I`; in particular, if
`τφ_R(0) + γθ(0) = γ` (for example θ(0) = 1, φ_R(0) = 0) then `τφ_R(t) + γθ(t) = γ` on `I`. -/
theorem compact_W_invariant (N : CNet) (q τ γ : ℝ) {I : Set ℝ} (hI : Convex ℝ I)
    (h0 : (0 : ℝ) ∈ I) {x : ℝ → EB SIRSp}
    (hx : ∀ t ∈ I, HasDerivWithinAt x (lift N q (sirRxns τ γ) (x t)) I t) :
    ∀ t ∈ I, τ * (x t).2.2.1 .R + γ * (x t).1 = τ * (x 0).2.2.1 .R + γ * (x 0).1 := by
  have hd : ∀ t ∈ I, HasDerivWithinAt (fun t => τ * (x t).2.2.1 .R + γ * (x t).1) 0 I t := by
    intro t ht
    have h := ((hasDerivWithinAt_φ (hx t ht) SIRSp.R).const_mul τ).add
      ((hasDerivWithinAt_θ (hx t ht)).const_mul γ)
    rw [lift_sir_apply] at h
    simp only [sirVec_R] at h
    convert h using 1
    ring
  exact fun t ht => const_of_hasDerivWithinAt_zero
    (g := fun t => τ * (x t).2.2.1 .R + γ * (x t).1) hI hd h0 ht

/-- **The design's W is invariant, on any time interval (M9).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M9): "W = {τφ_R + γθ = γ} is invariant for
SIR-shaped P".

Lean statement: let `N` be any configuration network (no assumption on ψ, ψ', ψ''), `q, τ, γ`
real, `I` any convex set of times (0 need not lie in `I`) and `x : ℝ → EB SIRSp` a solution of the
EB model of SIR within `I` at every `t ∈ I`. Then `τφ_R(s) + γθ(s) = τφ_R(t) + γθ(t)` for all
`s, t ∈ I`; and if `x(s) ∈ W = {τφ_R + γθ = γ}` for one `s ∈ I`, then `x(t) ∈ W` for every
`t ∈ I`. -/
theorem compact_W_invariant_any (N : CNet) (q τ γ : ℝ) {I : Set ℝ} (hI : Convex ℝ I)
    {x : ℝ → EB SIRSp} (hx : ∀ t ∈ I, HasDerivWithinAt x (lift N q (sirRxns τ γ) (x t)) I t) :
    (∀ s ∈ I, ∀ t ∈ I,
      τ * (x s).2.2.1 .R + γ * (x s).1 = τ * (x t).2.2.1 .R + γ * (x t).1) ∧
    (∀ s ∈ I, τ * (x s).2.2.1 .R + γ * (x s).1 = γ →
      ∀ t ∈ I, τ * (x t).2.2.1 .R + γ * (x t).1 = γ) := by
  have hd : ∀ t ∈ I, HasDerivWithinAt (fun t => τ * (x t).2.2.1 .R + γ * (x t).1) 0 I t := by
    intro t ht
    have h := ((hasDerivWithinAt_φ (hx t ht) SIRSp.R).const_mul τ).add
      ((hasDerivWithinAt_θ (hx t ht)).const_mul γ)
    rw [lift_sir_apply] at h
    simp only [sirVec_R] at h
    convert h using 1
    ring
  have hc : ∀ s ∈ I, ∀ t ∈ I,
      τ * (x s).2.2.1 .R + γ * (x s).1 = τ * (x t).2.2.1 .R + γ * (x t).1 :=
    fun s hs t ht => const_of_hasDerivWithinAt_zero
      (g := fun t => τ * (x t).2.2.1 .R + γ * (x t).1) hI hd ht hs
  exact ⟨hc, fun s hs hW t ht => (hc t ht s hs).trans hW⟩

/-- The derivative of `compactEmb` at `w`. -/
noncomputable def compactD (N : CNet) (q τ γ : ℝ) (w : ℝ × ℝ) : ℝ × ℝ →L[ℝ] EB SIRSp :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).prod ((0 : ℝ × ℝ →L[ℝ] ℝ).prod
    ((ContinuousLinearMap.pi fun X => match X with
      | .I => (1 - q * 1 * N.ψ'' w.1 / N.ψ' 1 + γ / τ) • ContinuousLinearMap.fst ℝ ℝ ℝ
      | .R => (-(γ / τ)) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (ContinuousLinearMap.pi fun X => match X with
      | .I => (-(q * 1 * N.ψ' w.1)) • ContinuousLinearMap.fst ℝ ℝ ℝ -
          ContinuousLinearMap.snd ℝ ℝ ℝ
      | .R => ContinuousLinearMap.snd ℝ ℝ ℝ)))

/-- `compactEmb` has derivative `compactD` at `w` when ψ' and ψ'' are the derivatives of ψ and
ψ' at `θ = w.1`. -/
lemma hasFDerivAt_compactEmb (N : CNet) (q τ γ : ℝ) {w : ℝ × ℝ}
    (hψ : HasDerivAt N.ψ (N.ψ' w.1) w.1) (hψ' : HasDerivAt N.ψ' (N.ψ'' w.1) w.1) :
    HasFDerivAt (compactEmb N q τ γ) (compactD N q τ γ w) w := by
  have hθ : HasFDerivAt (fun w : ℝ × ℝ => w.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) w := hasFDerivAt_fst
  have hR : HasFDerivAt (fun w : ℝ × ℝ => w.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) w := hasFDerivAt_snd
  have h1 : HasFDerivAt (fun w : ℝ × ℝ => N.ψ' w.1) (N.ψ'' w.1 • ContinuousLinearMap.fst ℝ ℝ ℝ)
      w := hψ'.comp_hasFDerivAt w hθ
  have h0 : HasFDerivAt (fun w : ℝ × ℝ => N.ψ w.1) (N.ψ' w.1 • ContinuousLinearMap.fst ℝ ℝ ℝ)
      w := hψ.comp_hasFDerivAt w hθ
  have hφ : HasFDerivAt (fun w : ℝ × ℝ => sirVec (w.1 - N.phiS q w.1 1 - γ * (1 - w.1) / τ)
      (γ * (1 - w.1) / τ)) (ContinuousLinearMap.pi fun X => match X with
      | .I => (1 - q * 1 * N.ψ'' w.1 / N.ψ' 1 + γ / τ) • ContinuousLinearMap.fst ℝ ℝ ℝ
      | .R => (-(γ / τ)) • ContinuousLinearMap.fst ℝ ℝ ℝ) w := by
    refine hasFDerivAt_pi'.2 fun X => ?_
    rw [ContinuousLinearMap.proj_pi]
    cases X with
    | I =>
        have h := (hθ.sub (h1.const_mul (q * 1 / N.ψ' 1))).sub ((hθ.const_sub 1).const_mul (γ / τ))
        refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)).congr_fderiv ?_
        · simp only [sirVec_I, CNet.phiS, Pi.sub_apply]
          ring
        · refine ContinuousLinearMap.ext fun v => ?_
          simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
            ContinuousLinearMap.neg_apply, ContinuousLinearMap.coe_fst', smul_eq_mul]
          ring
    | R =>
        have h := (hθ.const_sub 1).const_mul (γ / τ)
        refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)).congr_fderiv ?_
        · simp only [sirVec_R]
          ring
        · refine ContinuousLinearMap.ext fun v => ?_
          simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply,
            ContinuousLinearMap.coe_fst', smul_eq_mul]
          ring
  have hp : HasFDerivAt (fun w : ℝ × ℝ => sirVec (1 - N.susc q w.1 1 - w.2) w.2)
      (ContinuousLinearMap.pi fun X => match X with
      | .I => (-(q * 1 * N.ψ' w.1)) • ContinuousLinearMap.fst ℝ ℝ ℝ -
          ContinuousLinearMap.snd ℝ ℝ ℝ
      | .R => ContinuousLinearMap.snd ℝ ℝ ℝ) w := by
    refine hasFDerivAt_pi'.2 fun X => ?_
    rw [ContinuousLinearMap.proj_pi]
    cases X with
    | I =>
        have h := ((h0.const_mul (q * 1)).const_sub 1).sub hR
        refine (h.congr_fderiv ?_)
        refine ContinuousLinearMap.ext fun v => ?_
        simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.neg_apply, ContinuousLinearMap.coe_fst',
          ContinuousLinearMap.coe_snd', smul_eq_mul]
        ring
    | R => exact hR
  exact hθ.prodMk ((hasFDerivAt_const (1 : ℝ) w).prodMk (hφ.prodMk hp))

/-- For `τ ≠ 0`, the embedding is a local semiconjugacy from the compact model to the expanded
model on the set of `(θ, R)` with θ ∈ Θ, where Θ is a set on which ψ' and ψ'' are the derivatives
of ψ and ψ'. -/
theorem compactEmb_semiconj (N : CNet) (q τ γ : ℝ) (hτ : τ ≠ 0) (Θ : Set ℝ)
    (hψ : ∀ θ ∈ Θ, HasDerivAt N.ψ (N.ψ' θ) θ) (hψ' : ∀ θ ∈ Θ, HasDerivAt N.ψ' (N.ψ'' θ) θ) :
    IsSemiconjOn (compactSIR N q τ γ) (ebSys N q (sirRxns τ γ)) {w | w.1 ∈ Θ}
      (compactEmb N q τ γ) := by
  refine isSemiconjOn_of_hasFDerivAt (A := compactSIR N q τ γ) (B := ebSys N q (sirRxns τ γ))
    (compactD N q τ γ) (fun w hw => hasFDerivAt_compactEmb N q τ γ (hψ w.1 hw) (hψ' w.1 hw))
    fun w _ => ?_
  obtain ⟨θ, R⟩ := w
  change compactD N q τ γ (θ, R) (compactSIR N q τ γ |>.F (θ, R)) =
    lift N q (sirRxns τ γ) (compactEmb N q τ γ (θ, R))
  rw [lift_sir_apply]
  simp only [compactD, compactSIR, compactEmb, CNet.phiS, CNet.susc,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.coe_pi', sirVec_I]
  refine Prod.ext ?_ (Prod.ext rfl (Prod.ext ?_ ?_))
  · simp only
    field_simp
    ring
  · funext X
    cases X <;>
      simp only [sirVec_I, sirVec_R, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_fst',
        smul_eq_mul] <;>
      field_simp <;> ring
  · funext X
    cases X
    · simp only [sirVec_I, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
      field_simp
      ring
    · rfl

/-- **The compact SIR EBCM is conjugate to the expanded one restricted to W' (M9).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M9): "Compact ⊂ expanded | W = {τφ_R + γθ = γ}
is invariant for SIR-shaped P, and W → compact is a conjugacy | restriction".

Lean statement: let `N` be a configuration network, `Θ ⊆ ℝ` a set of θ values at which ψ' and ψ''
are the derivatives of ψ and ψ', and `q, τ, γ` real with `τ ≠ 0`. Let the expanded model be the EB
model of SIR (`s + I → I + I` at per-contact rate τ, `I → R` at γ) on `N` with seed factor `q`, and
the compact model `θ̇ = −τθ + τqψ'(θ)/ψ'(1) + γ(1 − θ)`, `Ṙ = γ(1 − qψ(θ) − R)` on `(θ, R)`. Let
`W' = {ξ = 1, τφ_R + γθ = γ, θ = φ_S + φ_I + φ_R, S + pop_I + pop_R = 1}` (`φ_S = qξψ'(θ)/ψ'(1)`,
`S = qξψ(θ)`). Then the embedding `(θ, R) ↦ (θ, 1, θ − φ_S − γ(1 − θ)/τ, γ(1 − θ)/τ,
1 − qψ(θ) − R, R)` and the projection `(θ, ξ, φ, pop) ↦ (θ, pop_R)` form a conjugacy
(`IsConjOn`) between the compact model on `{θ ∈ Θ}` and the expanded model on `W' ∩ {θ ∈ Θ}`: both
are local semiconjugacies, each maps its set into the other's, and they are mutually inverse there.

Scope: the design's `W` alone is invariant (`compact_W_invariant`) but has the dimension of the
full state space minus one; the compact model is conjugate to the sub-manifold `W'` cut out by `W`
and the three conservation laws that every solution from the design's initial condition obeys
(`compact_solution`). -/
theorem compact_conj (N : CNet) (q τ γ : ℝ) (hτ : τ ≠ 0) (Θ : Set ℝ)
    (hψ : ∀ θ ∈ Θ, HasDerivAt N.ψ (N.ψ' θ) θ) (hψ' : ∀ θ ∈ Θ, HasDerivAt N.ψ' (N.ψ'' θ) θ) :
    IsConjOn (compactSIR N q τ γ) (ebSys N q (sirRxns τ γ)) {w | w.1 ∈ Θ}
      (compactW N q τ γ ∩ {u | u.1 ∈ Θ}) (compactEmb N q τ γ) compactProj := by
  have he := compactEmb_semiconj N q τ γ hτ Θ hψ hψ'
  have hce : ∀ w, compactProj (compactEmb N q τ γ w) = w := fun w => rfl
  have hec : ∀ u ∈ compactW N q τ γ ∩ {u | u.1 ∈ Θ},
      compactEmb N q τ γ (compactProj u) = u := by
    rintro ⟨θ, ξ, φ, p⟩ ⟨⟨hξ, hW, hc, hn⟩, -⟩
    simp only at hξ hW hc hn
    subst hξ
    have hR : φ .R = γ * (1 - θ) / τ := by
      field_simp
      linarith
    simp only [compactEmb, compactProj]
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ ?_))
    · funext X
      cases X
      · simp only [sirVec_I]
        rw [← hR]
        linarith
      · simp only [sirVec_R]
        exact hR.symm
    · funext X
      cases X
      · simp only [sirVec_I]
        linarith
      · rfl
  have hLp : ∀ u : EB SIRSp, HasFDerivAt compactProj
      ((ebTheta (σ := SIRSp)).prod ((ContinuousLinearMap.proj SIRSp.R).comp ebPop)) u :=
    fun u => ((ebTheta (σ := SIRSp)).prod ((ContinuousLinearMap.proj SIRSp.R).comp ebPop)).hasFDerivAt
  refine ⟨he, isSemiconjOn_inverse he (fun u _ => (hLp u).differentiableAt)
    (fun u hu => hu.2) hce hec, fun w hw => ⟨⟨rfl, ?_, ?_, ?_⟩, hw⟩, fun u hu => hu.2,
    fun w _ => hce w, hec⟩
  · change τ * (γ * (1 - w.1) / τ) + γ * w.1 = γ
    field_simp
    ring
  · change w.1 = N.phiS q w.1 1 + (w.1 - N.phiS q w.1 1 - γ * (1 - w.1) / τ) +
      γ * (1 - w.1) / τ
    ring
  · change N.susc q w.1 1 + (1 - N.susc q w.1 1 - w.2) + w.2 = 1
    ring

/-- **The compact SIR EBCM is conjugate to the expanded one restricted to W', for a globally C²
ψ (M9).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M9): "Compact ⊂ expanded | W = {τφ_R + γθ = γ}
is invariant for SIR-shaped P, and W → compact is a conjugacy | restriction".

Lean statement: `compact_conj` with Θ = ℝ: let `N` be a configuration network with ψ' and ψ'' the
derivatives of ψ and ψ' at every real θ, and `q, τ, γ` real with `τ ≠ 0`. Then the embedding
`(θ, R) ↦ (θ, 1, θ − φ_S − γ(1 − θ)/τ, γ(1 − θ)/τ, 1 − qψ(θ) − R, R)` and the projection
`(θ, ξ, φ, pop) ↦ (θ, pop_R)` form a conjugacy (`IsConjOn`) between the compact model on the whole
plane and the expanded SIR model on
`W' = {ξ = 1, τφ_R + γθ = γ, θ = φ_S + φ_I + φ_R, S + pop_I + pop_R = 1}`. -/
theorem compact_conj_global (N : CNet) (q τ γ : ℝ) (hτ : τ ≠ 0)
    (hψ : ∀ θ, HasDerivAt N.ψ (N.ψ' θ) θ) (hψ' : ∀ θ, HasDerivAt N.ψ' (N.ψ'' θ) θ) :
    IsConjOn (compactSIR N q τ γ) (ebSys N q (sirRxns τ γ)) Set.univ (compactW N q τ γ)
      (compactEmb N q τ γ) compactProj := by
  have h := compact_conj N q τ γ hτ Set.univ (fun θ _ => hψ θ) (fun θ _ => hψ' θ)
  convert h using 2
  ext u
  exact ⟨fun hu => ⟨hu, trivial⟩, fun hu => hu.1⟩

/-- **Expanded solutions from the design's initial condition are compact solutions (M9).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M9): "W = {τφ_R + γθ = γ} is invariant for
SIR-shaped P, and W → compact is a conjugacy"; §D.3: "Examples: the compact SIR EBCM on
{τφ_R + γθ = γ}".

Lean statement: let `N` be a configuration network with `ψ(1) = 1` and `ψ'(1) ≠ 0`, and `q, τ, γ`
real with `τ ≠ 0`. Let `I` be a time interval (a convex set of times with `0 ∈ I`) and
`x : ℝ → EB SIRSp` a solution of the EB model of SIR on `N` within `I` at every `t ∈ I`, with
ψ' and ψ'' the derivatives of ψ and ψ' at every visited `θ(t)`, and with the design's initial
condition `θ(0) = 1`, `ξ(0) = 1`, `φ_I(0) + φ_R(0) = pop_I(0) + pop_R(0) = 1 − q`, `φ_R(0) = 0`.
Then for every `t ∈ I`, `x(t) ∈ W'` (so `τφ_R + γθ = γ`, `ξ = 1`, `θ = φ_S + φ_I + φ_R` and
`S + pop_I + pop_R = 1`), and `t ↦ (θ(t), pop_R(t))` solves the compact model
`θ̇ = −τθ + τqψ'(θ)/ψ'(1) + γ(1 − θ)`, `Ṙ = γ(1 − qψ(θ) − R)` within `I` at every `t ∈ I`. -/
theorem compact_solution (N : CNet) (q τ γ : ℝ) (hτ : τ ≠ 0) (h1 : N.ψ 1 = 1)
    (hm : N.ψ' 1 ≠ 0) {I : Set ℝ} (hI : Convex ℝ I) (h0 : (0 : ℝ) ∈ I) {x : ℝ → EB SIRSp}
    (hx : ∀ t ∈ I, HasDerivWithinAt x (lift N q (sirRxns τ γ) (x t)) I t)
    (hψ : ∀ t ∈ I, HasDerivAt N.ψ (N.ψ' (x t).1) (x t).1)
    (hψ' : ∀ t ∈ I, HasDerivAt N.ψ' (N.ψ'' (x t).1) (x t).1)
    (hθ0 : (x 0).1 = 1) (hξ0 : (x 0).2.1 = 1) (hφ0 : (x 0).2.2.1 .I + (x 0).2.2.1 .R = 1 - q)
    (hp0 : (x 0).2.2.2 .I + (x 0).2.2.2 .R = 1 - q) (hR0 : (x 0).2.2.1 .R = 0) :
    (∀ t ∈ I, x t ∈ compactW N q τ γ) ∧
      ∀ t ∈ I, HasDerivWithinAt (fun t => compactProj (x t))
        ((compactSIR N q τ γ).F (compactProj (x t))) I t := by
  have hnoR : ∀ r ∈ sirRxns τ γ, r.isRemoval = false := by
    intro r hr
    simp only [sirRxns, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl <;> rfl
  have hnoE : ∀ r ∈ sirRxns τ γ, r.isExit = false := by
    intro r hr
    simp only [sirRxns, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl <;> rfl
  have hξ := xi_const N q (sirRxns τ γ) hnoE hI h0 hx
  have hc := conservation N q hm (sirRxns τ γ) hnoR hI h0 hx hψ' hθ0 hξ0
    (by rw [sum_SIRSp]; exact hφ0)
  have hn := node_conservation N q h1 (sirRxns τ γ) hnoR hI h0 hx hψ hθ0 hξ0
    (by rw [sum_SIRSp]; exact hp0)
  have hW := compact_W_invariant N q τ γ hI h0 hx
  have hmem : ∀ t ∈ I, x t ∈ compactW N q τ γ := by
    intro t ht
    refine ⟨by rw [hξ t ht, hξ0], ?_, ?_, ?_⟩
    · rw [hW t ht, hR0, hθ0]
      ring
    · have := hc t ht
      rw [sum_SIRSp] at this
      linarith
    · have := hn t ht
      rw [sum_SIRSp] at this
      linarith
  refine ⟨hmem, ?_⟩
  -- the projection is a local semiconjugacy on `W'` (from `compact_conj` with Θ = visited θ)
  intro t ht
  have hL : HasFDerivAt compactProj
      ((ebTheta (σ := SIRSp)).prod ((ContinuousLinearMap.proj SIRSp.R).comp ebPop)) (x t) :=
    ((ebTheta (σ := SIRSp)).prod ((ContinuousLinearMap.proj SIRSp.R).comp ebPop)).hasFDerivAt
  have h := hL.comp_hasDerivWithinAt t (hx t ht)
  convert h using 1
  obtain ⟨hξt, hWt, hct, hnt⟩ := hmem t ht
  rw [lift_sir_apply]
  simp only [compactSIR, compactProj, ContinuousLinearMap.prod_apply, ebTheta_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, ebPop_apply, sirVec_R]
  refine Prod.ext ?_ ?_
  · simp only
    rw [hξt] at hct
    have hφR : (x t).2.2.1 .R = γ * (1 - (x t).1) / τ := by
      field_simp
      linarith
    have hφI : (x t).2.2.1 .I = (x t).1 - N.phiS q (x t).1 1 - γ * (1 - (x t).1) / τ := by
      rw [← hφR]
      linarith
    rw [hφI]
    field_simp
    ring
  · simp only
    rw [hξt] at hnt
    have : (x t).2.2.2 .I = 1 - N.susc q (x t).1 1 - (x t).2.2.2 .R := by linarith
    rw [this]

/-- **Expanded solutions from the design's initial condition are compact solutions, with the
design's seed `q = 1 − ρ` (M9).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M9): "W = {τφ_R + γθ = γ} is invariant for
SIR-shaped P, and W → compact is a conjugacy"; §D.4: "initial condition: θ(0) = 1, ξ(0) = 1,
φ_X(0) = pop_X(0) = ρ_X".

Lean statement: let `N` be a configuration network with `ψ(1) = 1` and `ψ'(1) ≠ 0`, `ρ, τ, γ` real
with `τ ≠ 0`, and `q = 1 − ρ`. Let `I` be a convex set of times with `0 ∈ I` and
`x : ℝ → EB SIRSp` a solution of the EB model of SIR on `N` with seed factor `1 − ρ` within `I` at
every `t ∈ I`, with ψ' and ψ'' the derivatives of ψ and ψ' at every visited `θ(t)`, from the
design's initial condition `x(0) = (θ, ξ, φ_I, φ_R, pop_I, pop_R) = (1, 1, ρ, 0, ρ, 0)`. Then
`x(t) ∈ W'` for every `t ∈ I`, and `t ↦ (θ(t), pop_R(t))` solves the compact model within `I` at
every `t ∈ I`. -/
theorem compact_solution_ic (N : CNet) (ρ τ γ : ℝ) (hτ : τ ≠ 0) (h1 : N.ψ 1 = 1)
    (hm : N.ψ' 1 ≠ 0) {I : Set ℝ} (hI : Convex ℝ I) (h0 : (0 : ℝ) ∈ I) {x : ℝ → EB SIRSp}
    (hx0 : x 0 = ((1 : ℝ), (1 : ℝ), sirVec ρ 0, sirVec ρ 0))
    (hψ : ∀ t ∈ I, HasDerivAt N.ψ (N.ψ' (x t).1) (x t).1)
    (hψ' : ∀ t ∈ I, HasDerivAt N.ψ' (N.ψ'' (x t).1) (x t).1)
    (hx : ∀ t ∈ I, HasDerivWithinAt x (lift N (1 - ρ) (sirRxns τ γ) (x t)) I t) :
    (∀ t ∈ I, x t ∈ compactW N (1 - ρ) τ γ) ∧
      ∀ t ∈ I, HasDerivWithinAt (fun t => compactProj (x t))
        ((compactSIR N (1 - ρ) τ γ).F (compactProj (x t))) I t :=
  compact_solution N (1 - ρ) τ γ hτ h1 hm hI h0 hx hψ hψ' (by rw [hx0]) (by rw [hx0])
    (by rw [hx0]; simp) (by rw [hx0]; simp) (by rw [hx0]; simp)

/-- **Expanded solutions from the design's initial condition are compact solutions, for
two-sided derivatives (M9).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M9): "W = {τφ_R + γθ = γ} is invariant for
SIR-shaped P, and W → compact is a conjugacy"; §D.4: "initial condition: θ(0) = 1, ξ(0) = 1,
φ_X(0) = pop_X(0) = ρ_X".

Lean statement: as `compact_solution_ic` (ψ(1) = 1, ψ'(1) ≠ 0, τ ≠ 0, q = 1 − ρ, `I` convex with
`0 ∈ I`, derivative relations of ψ, ψ', ψ'' at the visited θ, `x(0) = (1, 1, ρ, 0, ρ, 0)`), for a
curve `x` with the two-sided derivative `x'(t) = lift … (x(t))` at every `t ∈ I`: then
`x(t) ∈ W'` for every `t ∈ I`, and `t ↦ (θ(t), pop_R(t))` has the two-sided derivative given by
the compact model at every `t ∈ I`. -/
theorem compact_solution_ic_at (N : CNet) (ρ τ γ : ℝ) (hτ : τ ≠ 0) (h1 : N.ψ 1 = 1)
    (hm : N.ψ' 1 ≠ 0) {I : Set ℝ} (hI : Convex ℝ I) (h0 : (0 : ℝ) ∈ I) {x : ℝ → EB SIRSp}
    (hx0 : x 0 = ((1 : ℝ), (1 : ℝ), sirVec ρ 0, sirVec ρ 0))
    (hψ : ∀ t ∈ I, HasDerivAt N.ψ (N.ψ' (x t).1) (x t).1)
    (hψ' : ∀ t ∈ I, HasDerivAt N.ψ' (N.ψ'' (x t).1) (x t).1)
    (hx : ∀ t ∈ I, HasDerivAt x (lift N (1 - ρ) (sirRxns τ γ) (x t)) t) :
    (∀ t ∈ I, x t ∈ compactW N (1 - ρ) τ γ) ∧
      ∀ t ∈ I, HasDerivAt (fun t => compactProj (x t))
        ((compactSIR N (1 - ρ) τ γ).F (compactProj (x t))) t := by
  have hmem := (compact_solution_ic N ρ τ γ hτ h1 hm hI h0 hx0 hψ hψ'
    (fun t ht => (hx t ht).hasDerivWithinAt)).1
  refine ⟨hmem, ?_⟩
  let Θ : Set ℝ := (fun t => (x t).1) '' I
  have hΘψ : ∀ θ ∈ Θ, HasDerivAt N.ψ (N.ψ' θ) θ := by
    rintro _ ⟨t, ht, rfl⟩
    exact hψ t ht
  have hΘψ' : ∀ θ ∈ Θ, HasDerivAt N.ψ' (N.ψ'' θ) θ := by
    rintro _ ⟨t, ht, rfl⟩
    exact hψ' t ht
  have hc := compact_conj N (1 - ρ) τ γ hτ Θ hΘψ hΘψ'
  have hU : ∀ t ∈ I, x t ∈ compactW N (1 - ρ) τ γ ∩ {u | u.1 ∈ Θ} :=
    fun t ht => ⟨hmem t ht, ⟨t, ht, rfl⟩⟩
  exact (SemiconjOn.ofIsSemiconjOn _ hc.2.1).map_solution_on
    (A := ebSys N (1 - ρ) (sirRxns τ γ)) hx hU

/-- **`compact_solution` is not vacuous: EB SIR on Poisson(μ) (M9).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M9): "W = {τφ_R + γθ = γ} is invariant for
SIR-shaped P, and W → compact is a conjugacy".

Lean statement: for all real `μ ≠ 0`, `q`, `τ ≠ 0` and `γ`, there are `ε > 0` and a curve
`x : ℝ → EB SIRSp` with the design's initial condition `x(0) = (θ, ξ, φ_I, φ_R, pop_I, pop_R) =
(1, 1, 1 − q, 0, 1 − q, 0)` that solves the EB model of SIR on the Poisson(μ) network
(`HasDerivAt`) at every `t ∈ (−ε, ε)`, and along which `t ↦ (θ(t), pop_R(t))` solves the compact
model `θ̇ = −τθ + τqψ'(θ)/ψ'(1) + γ(1 − θ)`, `Ṙ = γ(1 − qψ(θ) − R)` within `(−ε, ε)`. -/
theorem compact_solution_poisson (μ q τ γ : ℝ) (hμ : μ ≠ 0) (hτ : τ ≠ 0) :
    ∃ ε > (0 : ℝ), ∃ x : ℝ → EB SIRSp,
      x 0 = ((1 : ℝ), (1 : ℝ), sirVec (1 - q) 0, sirVec (1 - q) 0) ∧
      (∀ t ∈ Set.Ioo (-ε) ε,
        HasDerivAt x (lift (CNet.poisson μ) q (sirRxns τ γ) (x t)) t) ∧
      ∀ t ∈ Set.Ioo (-ε) ε, HasDerivWithinAt (fun t => compactProj (x t))
        ((compactSIR (CNet.poisson μ) q τ γ).F (compactProj (x t))) (Set.Ioo (-ε) ε) t := by
  have hψ : ContDiffAt ℝ 1 (CNet.poisson μ).ψ 1 := by
    show ContDiffAt ℝ 1 (fun x : ℝ => Real.exp (μ * (x - 1))) 1
    fun_prop
  have hψ' : ContDiffAt ℝ 1 (CNet.poisson μ).ψ' 1 := by
    show ContDiffAt ℝ 1 (fun x : ℝ => μ * Real.exp (μ * (x - 1))) 1
    fun_prop
  have hψ'' : ContDiffAt ℝ 1 (CNet.poisson μ).ψ'' 1 := by
    show ContDiffAt ℝ 1 (fun x : ℝ => μ ^ 2 * Real.exp (μ * (x - 1))) 1
    fun_prop
  obtain ⟨ε, hε, x, hx0, hx⟩ := exists_local_solution (CNet.poisson μ) q (sirRxns τ γ)
    ((1 : ℝ), (1 : ℝ), sirVec (1 - q) 0, sirVec (1 - q) 0) hψ hψ' hψ''
  refine ⟨ε, hε, x, hx0, hx, ?_⟩
  have h1 : (CNet.poisson μ).ψ 1 = 1 := by simp [CNet.poisson]
  have hm : (CNet.poisson μ).ψ' 1 ≠ 0 := by simp [CNet.poisson, hμ]
  refine (compact_solution (CNet.poisson μ) q τ γ hτ h1 hm (convex_Ioo (-ε) ε)
    ⟨by linarith, hε⟩ (fun t ht => (hx t ht).hasDerivWithinAt)
    (fun t _ => CNet.poisson_hasDerivAt_ψ μ _) (fun t _ => CNet.poisson_hasDerivAt_ψ' μ _)
    ?_ ?_ ?_ ?_ ?_).2 <;> rw [hx0] <;> simp

/-- **`compact_solution` is not vacuous on Poisson networks (M9).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M9): "W = {τφ_R + γθ = γ} is invariant for
SIR-shaped P, and W → compact is a conjugacy"; amended by §M.4: "For μ ≠ 0 and τ ≠ 0 the
Poisson(μ) network satisfies the PGF hypotheses of `compact_solution` (ψ(1) = 1, ψ'(1) = μ, and
ψ', ψ'' are the derivatives of ψ, ψ'), and a local EB SIR solution from the design's initial
condition (θ, ξ, φ_I, φ_R, pop_I, pop_R) = (1, 1, 1 − q, 0, 1 − q, 0) exists on some (−ε, ε); it
stays in W′ and its image (θ, pop_R) solves the compact model."

Lean statement: for all real `μ ≠ 0`, `q`, `τ ≠ 0` and `γ`: the Poisson(μ) network has
`ψ(1) = 1`, `ψ'(1) = μ`, and ψ', ψ'' are the derivatives of ψ, ψ' at every real θ; and there are
`ε > 0` and a curve `x : ℝ → EB SIRSp` with `x(0) = (1, 1, 1 − q, 0, 1 − q, 0)` that has the
two-sided derivative of the EB model of SIR on Poisson(μ) with seed factor `q` at every
`t ∈ (−ε, ε)`, lies in `W'` at every such `t`, and along which `t ↦ (θ(t), pop_R(t))` has the
two-sided derivative given by the compact model at every `t ∈ (−ε, ε)`. -/
theorem compact_solution_poisson_spec (μ q τ γ : ℝ) (hμ : μ ≠ 0) (hτ : τ ≠ 0) :
    ((CNet.poisson μ).ψ 1 = 1 ∧ (CNet.poisson μ).ψ' 1 = μ) ∧
    (∀ θ, HasDerivAt (CNet.poisson μ).ψ ((CNet.poisson μ).ψ' θ) θ) ∧
    (∀ θ, HasDerivAt (CNet.poisson μ).ψ' ((CNet.poisson μ).ψ'' θ) θ) ∧
    ∃ ε > (0 : ℝ), ∃ x : ℝ → EB SIRSp,
      x 0 = ((1 : ℝ), (1 : ℝ), sirVec (1 - q) 0, sirVec (1 - q) 0) ∧
      (∀ t ∈ Set.Ioo (-ε) ε,
        HasDerivAt x (lift (CNet.poisson μ) q (sirRxns τ γ) (x t)) t) ∧
      (∀ t ∈ Set.Ioo (-ε) ε, x t ∈ compactW (CNet.poisson μ) q τ γ) ∧
      ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt (fun t => compactProj (x t))
        ((compactSIR (CNet.poisson μ) q τ γ).F (compactProj (x t))) t := by
  have h1 : (CNet.poisson μ).ψ 1 = 1 := by simp [CNet.poisson]
  have hμ1 : (CNet.poisson μ).ψ' 1 = μ := by simp [CNet.poisson]
  have hm : (CNet.poisson μ).ψ' 1 ≠ 0 := by rw [hμ1]; exact hμ
  have hψ : ContDiffAt ℝ 1 (CNet.poisson μ).ψ 1 := by
    show ContDiffAt ℝ 1 (fun x : ℝ => Real.exp (μ * (x - 1))) 1
    fun_prop
  have hψ' : ContDiffAt ℝ 1 (CNet.poisson μ).ψ' 1 := by
    show ContDiffAt ℝ 1 (fun x : ℝ => μ * Real.exp (μ * (x - 1))) 1
    fun_prop
  have hψ'' : ContDiffAt ℝ 1 (CNet.poisson μ).ψ'' 1 := by
    show ContDiffAt ℝ 1 (fun x : ℝ => μ ^ 2 * Real.exp (μ * (x - 1))) 1
    fun_prop
  obtain ⟨ε, hε, x, hx0, hx⟩ := exists_local_solution (CNet.poisson μ) q (sirRxns τ γ)
    ((1 : ℝ), (1 : ℝ), sirVec (1 - q) 0, sirVec (1 - q) 0) hψ hψ' hψ''
  have hq : q = 1 - (1 - q) := by ring
  have hx' : ∀ t ∈ Set.Ioo (-ε) ε,
      HasDerivAt x (lift (CNet.poisson μ) (1 - (1 - q)) (sirRxns τ γ) (x t)) t := by
    rw [← hq]; exact hx
  have hs := compact_solution_ic_at (CNet.poisson μ) (1 - q) τ γ hτ h1 hm (convex_Ioo (-ε) ε)
    ⟨by linarith, hε⟩ hx0 (fun t _ => CNet.poisson_hasDerivAt_ψ μ _)
    (fun t _ => CNet.poisson_hasDerivAt_ψ' μ _) hx'
  rw [← hq] at hs
  exact ⟨⟨h1, hμ1⟩, CNet.poisson_hasDerivAt_ψ μ, CNet.poisson_hasDerivAt_ψ' μ, ε, hε, x, hx0, hx,
    hs.1, hs.2⟩

end NEP
