import NetworkEpi.Semantics.EB
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# SIR on a Poisson network and Rempała's quotient to mass action (M3 for SIR)

DESIGN_NetworkEpiCore.md §D.5, row **M3** ("Rempała quotient"): "EB_{Pois μ}(P) → MA(E_μ P),
E_μ P = c_μ P + {J_r → ∅ at τ_r} on the edge copies; π = (θ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ). For
SIR: MA(β = μτ, γ_MA = γ + τ). **The MA "I" is φ_I, not prevalence**", with Lean evidence
"**[L]** `NEP.rempala` (SIR)".

This module ports the SIR case of `DynSysSketch.lean` and ties it to the general EB lift of
`NetworkEpi.Semantics.EB`: `ebPoisSIR_lift` shows that the two-dimensional system `ebPoisSIR` is
the `(θ, φ_I)` part of `ebSys (CNet.poisson μ) q (sirRxns τ γ)` on `ξ = 1`, and
`rempala_lift` composes the two maps. The general-P quotient (L4c) belongs to
`NetworkEpi/Morphisms` (WP28).
-/

open CategoryTheory

namespace NEP

section Rempala
variable (μ τ γ q : ℝ)

/-- Edge-based SIR on a Poisson(μ) configuration network in coordinates `(θ, φ_I)`:
`θ̇ = −τφ_I`, `φ̇_I = τφ_I·qμe^{μ(θ−1)} − (τ + γ)φ_I` (per-contact rate τ, recovery rate γ, seed
factor q; ξ ≡ 1). -/
noncomputable def ebPoisSIR : DynSys where
  V := ℝ × ℝ
  F u := (-τ * u.2, τ * u.2 * q * μ * Real.exp (μ * (u.1 - 1)) - (τ + γ) * u.2)

/-- Mass-action SIR in coordinates `(S, I)` with contact rate `β` and removal rate `ρ`:
`Ṡ = −βSI`, `İ = βSI − ρI`. -/
noncomputable def maSIR (β ρ : ℝ) : DynSys where
  V := ℝ × ℝ
  F v := (-β * v.1 * v.2, β * v.1 * v.2 - ρ * v.2)

/-- Rempała's map `(θ, φ_I) ↦ (q e^{μ(θ−1)}, φ_I)`. -/
noncomputable def poisMap (u : ℝ × ℝ) : ℝ × ℝ := (q * Real.exp (μ * (u.1 - 1)), u.2)

/-- The derivative of Rempała's map: `Dπ(θ, φ)(dθ, dφ) = (qμe^{μ(θ−1)} dθ, dφ)`. -/
lemma hasFDerivAt_poisMap (u : ℝ × ℝ) :
    HasFDerivAt (poisMap μ q)
      ((q * (Real.exp (μ * (u.1 - 1)) * μ)) • (ContinuousLinearMap.fst ℝ ℝ ℝ) |>.prod
        (ContinuousLinearMap.snd ℝ ℝ ℝ)) u := by
  have h1 : HasFDerivAt (fun u : ℝ × ℝ => μ * (u.1 - 1)) (μ • ContinuousLinearMap.fst ℝ ℝ ℝ) u := by
    have := ((hasFDerivAt_fst (𝕜 := ℝ) (p := u)).sub_const 1).const_mul μ
    simpa using this
  have h2 := (h1.exp).const_mul q
  refine HasFDerivAt.prodMk (by simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using h2)
    hasFDerivAt_snd

/-- The derivative of Rempała's map with the scalar in the order written:
`Dπ(θ, φ)(dθ, dφ) = (qμe^{μ(θ−1)} dθ, dφ)`, i.e. the linear map
`((q μ e^{μ(θ−1)}) • fst, snd)`. -/
theorem hasFDerivAt_poisMap_qμ (u : ℝ × ℝ) :
    HasFDerivAt (poisMap μ q)
      (((q * μ * Real.exp (μ * (u.1 - 1))) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        (ContinuousLinearMap.snd ℝ ℝ ℝ)) u := by
  have e : q * μ * Real.exp (μ * (u.1 - 1)) = q * (Real.exp (μ * (u.1 - 1)) * μ) := by ring
  rw [e]
  exact hasFDerivAt_poisMap μ q u

/-- **Rempała's theorem for SIR as a semiconjugacy (M3, SIR case).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M3): "**Rempała quotient** ("back to mass
action on the same species") | EB_{Pois μ}(P) → MA(E_μ P), E_μ P = c_μ P + {J_r → ∅ at τ_r} on
the edge copies; π = (θ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ). For SIR: MA(β = μτ, γ_MA = γ + τ). **The
MA "I" is φ_I, not prevalence** | natural semiconjugacy (surjective submersion) | **[L]**
`NEP.rempala` (SIR)".

Lean statement: for all real `μ, τ, γ, q`, the map `π(θ, φ_I) = (q e^{μ(θ−1)}, φ_I)` is a
(global) semiconjugacy from edge-based SIR on a Poisson(μ) configuration network in coordinates
`(θ, φ_I)` (`θ̇ = −τφ_I`, `φ̇_I = τφ_I qμe^{μ(θ−1)} − (τ+γ)φ_I`, i.e. ξ ≡ 1, no exits) to
mass-action SIR `Ṡ = −βSI`, `İ = βSI − ρI` with `β = μτ` and `ρ = γ + τ`: `π` is differentiable
and `Dπ(u)·F(u) = G(π(u))` for every `u ∈ ℝ²`.

Scope: this is the SIR instance only. The design's "surjective submersion" holds for `μ ≠ 0` and
`q > 0`, onto the mass-action states with `S > 0` (`rempala_quotient_sir`); it fails for `μ = 0`
or `q = 0`. Naturality in `P` is `NEP.rempala_natural`. `rempala_lift` connects the
two-dimensional source to the general EB lift. -/
theorem rempala : IsSemiconj (ebPoisSIR μ τ γ q) (maSIR (μ * τ) (γ + τ)) (poisMap μ q) := by
  refine ⟨fun u => (hasFDerivAt_poisMap μ q u).differentiableAt, fun u => ?_⟩
  obtain ⟨θ, φ⟩ := u
  erw [(hasFDerivAt_poisMap μ q (θ, φ)).fderiv]
  refine Prod.ext ?_ ?_
  · show q * (Real.exp (μ * (θ - 1)) * μ) * (-τ * φ)
        = -(μ * τ) * (q * Real.exp (μ * (θ - 1))) * φ
    ring
  · show τ * φ * q * μ * Real.exp (μ * (θ - 1)) - (τ + γ) * φ
        = μ * τ * (q * Real.exp (μ * (θ - 1))) * φ - (γ + τ) * φ
    ring

/-- **Rempała's map for SIR is a surjective submersion onto `S > 0` (M3, SIR case).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M3): "π = (θ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ). For
SIR: MA(β = μτ, γ_MA = γ + τ). **The MA "I" is φ_I, not prevalence** | natural semiconjugacy
(surjective submersion)".

Lean statement: for real `μ ≠ 0` and `q`, (1) if `q ≠ 0`, the derivative of
`π(θ, φ_I) = (q e^{μ(θ−1)}, φ_I)` is surjective at every point; (2) if `q > 0`, every
mass-action state `(S, I)` with `S > 0` is `π(θ, φ_I)` for some `(θ, φ_I)`. -/
theorem rempala_quotient_sir (μ q : ℝ) (hμ : μ ≠ 0) :
    (q ≠ 0 → ∀ u : ℝ × ℝ, Function.Surjective (fderiv ℝ (poisMap μ q) u)) ∧
      (0 < q → ∀ S I : ℝ, 0 < S → ∃ u : ℝ × ℝ, poisMap μ q u = (S, I)) := by
  refine ⟨fun hq u v => ?_, fun hq S I hS => ?_⟩
  · rw [(hasFDerivAt_poisMap_qμ μ q u).fderiv]
    have he : q * μ * Real.exp (μ * (u.1 - 1)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hq hμ) (Real.exp_pos _).ne'
    refine ⟨(v.1 / (q * μ * Real.exp (μ * (u.1 - 1))), v.2), ?_⟩
    simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
    refine Prod.ext ?_ rfl
    field_simp
  · refine ⟨(1 + Real.log (S / q) / μ, I), ?_⟩
    simp only [poisMap]
    have : μ * (1 + Real.log (S / q) / μ - 1) = Real.log (S / q) := by
      field_simp
      ring
    rw [this, Real.exp_log (div_pos hS hq)]
    refine Prod.ext ?_ rfl
    field_simp

/-- **Rempała's map for SIR is a surjective submersion onto `S > 0` exactly when `μ ≠ 0` and
`q ≠ 0` (M3, SIR case).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M3): "π = (θ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ). For
SIR: MA(β = μτ, γ_MA = γ + τ). **The MA "I" is φ_I, not prevalence** | natural semiconjugacy
(surjective submersion)"; amended by §M.3: "The SIR quotient of M3 is a surjective submersion for
μ ≠ 0 and q > 0, onto the mass-action states with S > 0 (`NEP.rempala_quotient_sir`); it fails
for μ = 0 or q = 0."

Lean statement: for `π(θ, φ_I) = (q e^{μ(θ−1)}, φ_I)`: (1) for `μ ≠ 0` and `q > 0` the derivative
of `π` is surjective at every point; (2) for `μ ≠ 0` and `q > 0` every mass-action state `(S, I)`
with `S > 0` is `π(θ, φ_I)` for some `(θ, φ_I)`; (3) for `μ = 0` and every `q`, `π` is not a
surjective submersion onto `{S > 0}` (the derivative is not surjective anywhere, and `(1, 0)` is
not in its image at `(0, 0)`); (4) for `q = 0` and every `μ`, `π` is not a surjective submersion
onto `{S > 0}` (`π` misses every state with `S > 0`). -/
theorem rempala_quotient_sir_spec :
    (∀ μ q : ℝ, μ ≠ 0 → 0 < q → ∀ u : ℝ × ℝ, Function.Surjective (fderiv ℝ (poisMap μ q) u)) ∧
    (∀ μ q : ℝ, μ ≠ 0 → 0 < q → ∀ S I : ℝ, 0 < S → ∃ u : ℝ × ℝ, poisMap μ q u = (S, I)) ∧
    (∀ q : ℝ, ¬ ((∀ u : ℝ × ℝ, Function.Surjective (fderiv ℝ (poisMap 0 q) u)) ∧
      (∀ S I : ℝ, 0 < S → ∃ u : ℝ × ℝ, poisMap 0 q u = (S, I)))) ∧
    (∀ μ : ℝ, ¬ ((∀ u : ℝ × ℝ, Function.Surjective (fderiv ℝ (poisMap μ 0) u)) ∧
      (∀ S I : ℝ, 0 < S → ∃ u : ℝ × ℝ, poisMap μ 0 u = (S, I)))) := by
  refine ⟨fun μ q hμ hq => (rempala_quotient_sir μ q hμ).1 hq.ne',
    fun μ q hμ hq => (rempala_quotient_sir μ q hμ).2 hq, fun q ⟨hs, _⟩ => ?_,
    fun μ ⟨_, ho⟩ => ?_⟩
  · obtain ⟨v, hv⟩ := hs 0 (1, 0)
    rw [(hasFDerivAt_poisMap_qμ 0 q 0).fderiv] at hv
    have := congrArg Prod.fst hv
    simp at this
  · obtain ⟨u, hu⟩ := ho 1 0 one_pos
    have := congrArg Prod.fst hu
    simp [poisMap] at this

/-- Rempała's semiconjugacy as a morphism of `DynSys`. -/
noncomputable def rempalaHom : ebPoisSIR μ τ γ q ⟶ maSIR (μ * τ) (γ + τ) :=
  Semiconj.ofIsSemiconj _ (rempala μ τ γ q)

/-- Rempała's map is C^∞, so `rempalaHom` is also a morphism of the design's category **Dyn**
(whose morphisms are C¹). -/
theorem contDiff_poisMap : ContDiff ℝ ⊤ (poisMap μ q) := by
  unfold poisMap
  fun_prop

/-- **Rempała's map for SIR is a morphism of the design's category Dyn.**

Design statement (DESIGN_NetworkEpiCore.md §D.3): "Objects of **Dyn** are (V, F): V a
finite-dimensional real normed space, F: V → V a C¹ vector field. Morphisms (V, F) → (W, G) are C¹
maps π with Dπ(u)·F(u) = G(π(u)) (semiconjugacies)."

Lean statement: for all real `μ, τ, γ, q`: Rempała's map `(θ, φ_I) ↦ (q e^{μ(θ−1)}, φ_I)` is C^∞
(`ContDiff ℝ ∞`); the map of `rempalaHom μ τ γ q` is C¹; the source `ebPoisSIR μ τ γ q` and the
target `maSIR (μτ) (γ + τ)` have finite-dimensional state spaces and C¹ vector fields. -/
theorem contDiff_poisMap_dyn :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (poisMap μ q) ∧
      ContDiff ℝ 1 (Semiconj.π (rempalaHom μ τ γ q)) ∧
      (FiniteDimensional ℝ (ebPoisSIR μ τ γ q).V ∧ ContDiff ℝ 1 (ebPoisSIR μ τ γ q).F) ∧
      (FiniteDimensional ℝ (maSIR (μ * τ) (γ + τ)).V ∧ ContDiff ℝ 1 (maSIR (μ * τ) (γ + τ)).F) := by
  have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (poisMap μ q) := by
    unfold poisMap
    fun_prop
  refine ⟨h, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · show ContDiff ℝ 1 (poisMap μ q)
    unfold poisMap
    fun_prop
  · show FiniteDimensional ℝ (ℝ × ℝ)
    infer_instance
  · show ContDiff ℝ 1 (fun u : ℝ × ℝ =>
      (-τ * u.2, τ * u.2 * q * μ * Real.exp (μ * (u.1 - 1)) - (τ + γ) * u.2))
    fun_prop
  · show FiniteDimensional ℝ (ℝ × ℝ)
    infer_instance
  · show ContDiff ℝ 1 (fun v : ℝ × ℝ => (-(μ * τ) * v.1 * v.2, μ * τ * v.1 * v.2 - (γ + τ) * v.2))
    fun_prop

end Rempala

/-! ## The SIR EBCM of the general lift on a Poisson network -/

/-- The Poisson(μ) configuration network: `ψ(x) = e^{μ(x−1)}`, `ψ'(x) = μe^{μ(x−1)}`,
`ψ''(x) = μ²e^{μ(x−1)}`. -/
noncomputable def CNet.poisson (μ : ℝ) : CNet where
  ψ x := Real.exp (μ * (x - 1))
  ψ' x := μ * Real.exp (μ * (x - 1))
  ψ'' x := μ ^ 2 * Real.exp (μ * (x - 1))

/-- On the Poisson network, `ψ'` is the derivative of `ψ` everywhere. -/
theorem CNet.poisson_hasDerivAt_ψ (μ x : ℝ) :
    HasDerivAt (CNet.poisson μ).ψ ((CNet.poisson μ).ψ' x) x := by
  have h : HasDerivAt (fun x => μ * (x - 1)) μ x := by
    simpa using ((hasDerivAt_id x).sub_const 1).const_mul μ
  simpa [CNet.poisson, mul_comm] using h.exp

/-- On the Poisson network, `ψ''` is the derivative of `ψ'` everywhere. -/
theorem CNet.poisson_hasDerivAt_ψ' (μ x : ℝ) :
    HasDerivAt (CNet.poisson μ).ψ' ((CNet.poisson μ).ψ'' x) x := by
  have h : HasDerivAt (fun x => μ * (x - 1)) μ x := by
    simpa using ((hasDerivAt_id x).sub_const 1).const_mul μ
  have := h.exp.const_mul μ
  simpa [CNet.poisson, pow_two, mul_comm, mul_left_comm, mul_assoc] using this

/-- Node species of SIR (the susceptible species is implicit). -/
inductive SIRSp where
  | I | R
  deriving DecidableEq, Fintype

/-- SIR as a T_EB reaction list: `s + I → I + I` at per-contact rate `τ`, `I → R` at rate `γ`. -/
def sirRxns (τ γ : ℝ) : List (Rxn SIRSp) := [.contact .I .I τ, .trans .I (some .R) γ]

/-- The chart `(θ, ξ, φ, pop) ↦ (θ, φ_I)`. -/
def sirChart (u : EB SIRSp) : ℝ × ℝ := (u.1, u.2.2.1 .I)

/-- `sirChart` as a continuous linear map. -/
noncomputable def sirChartL : EB SIRSp →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ _).prod ((ContinuousLinearMap.proj SIRSp.I).comp
    ((ContinuousLinearMap.fst ℝ _ _).comp
      ((ContinuousLinearMap.snd ℝ ℝ _).comp (ContinuousLinearMap.snd ℝ ℝ _))))

/-- `sirChartL` is `sirChart`. -/
lemma sirChartL_apply (u : EB SIRSp) : sirChartL u = sirChart u := rfl

/-- **`ebPoisSIR` is the SIR EBCM of the general lift.** For `μ ≠ 0`, the chart
`(θ, ξ, φ, pop) ↦ (θ, φ_I)` is a local semiconjugacy on `{ξ = 1}` from the general EB model
`ebSys (CNet.poisson μ) q (sirRxns τ γ)` (the per-reaction lift of `s + I → I + I` at τ and
`I → R` at γ on a Poisson(μ) network) to `ebPoisSIR μ τ γ q`. -/
theorem ebPoisSIR_lift (μ τ γ q : ℝ) (hμ : μ ≠ 0) :
    IsSemiconjOn (ebSys (CNet.poisson μ) q (sirRxns τ γ)) (ebPoisSIR μ τ γ q) {u | u.2.1 = 1}
      sirChart := by
  have hd : ∀ u : EB SIRSp, HasFDerivAt sirChart sirChartL u := fun u => sirChartL.hasFDerivAt
  refine ⟨fun u _ => (hd u).differentiableAt, fun u hu => ?_⟩
  obtain ⟨θ, ξ, φ, p⟩ := u
  simp only [Set.mem_setOf_eq] at hu
  subst hu
  erw [(hd (θ, 1, φ, p)).fderiv]
  change sirChart (lift (CNet.poisson μ) q (sirRxns τ γ) (θ, 1, φ, p)) =
    (ebPoisSIR μ τ γ q).F (sirChart (θ, 1, φ, p))
  have hIR : (SIRSp.I : SIRSp) ≠ SIRSp.R := by decide
  simp only [sirChart, ebPoisSIR, lift, sirRxns, ebField, CNet.poisson, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Prod.fst_add, Prod.snd_add, Prod.fst_zero,
    Prod.snd_zero, Pi.add_apply, Pi.sub_apply, Pi.zero_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne hIR, sub_self, mul_zero, Real.exp_zero, mul_one]
  refine Prod.ext ?_ ?_
  · simp only [add_zero]
    ring
  · have hsq : q * (μ ^ 2 * Real.exp (μ * (θ - 1))) / μ = q * μ * Real.exp (μ * (θ - 1)) := by
      field_simp
    rw [hsq]
    ring

/-- **Rempała's quotient from the general SIR lift (M3, SIR case, on ξ = 1).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M3): "EB_{Pois μ}(P) → MA(E_μ P), E_μ P =
c_μ P + {J_r → ∅ at τ_r} on the edge copies; π = (θ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ). For SIR:
MA(β = μτ, γ_MA = γ + τ). **The MA "I" is φ_I, not prevalence**".

Lean statement: for all real `μ ≠ 0`, `τ`, `γ`, `q`, the map
`(θ, ξ, φ, pop) ↦ (q e^{μ(θ−1)}, φ_I)` is a local semiconjugacy on the set `{ξ = 1}` from the
general per-reaction EB model of SIR (`s + I → I + I` at per-contact rate τ, `I → R` at rate γ)
on the Poisson(μ) configuration network `ψ(x) = e^{μ(x−1)}` with seed factor `q`, to mass-action
SIR `Ṡ = −βSI`, `İ = βSI − ρI` with `β = μτ` and `ρ = γ + τ`: at every state with `ξ = 1` the map
is differentiable and carries the EB field to the MA field.

Scope: SIR only and on `ξ = 1` (SIR has no exits, so `ξ̇ = 0` and `ξ ≡ ξ(0) = 1`); on that set
the design's `qξe^{μ(θ−1)}` equals `q e^{μ(θ−1)}`. -/
theorem rempala_lift (μ τ γ q : ℝ) (hμ : μ ≠ 0) :
    IsSemiconjOn (ebSys (CNet.poisson μ) q (sirRxns τ γ)) (maSIR (μ * τ) (γ + τ))
      {u | u.2.1 = 1} (poisMap μ q ∘ sirChart) := by
  have h := ((SemiconjOn.ofIsSemiconjOn _ (ebPoisSIR_lift μ τ γ q hμ)).comp
    ((rempalaHom μ τ γ q : Semiconj _ _).toSemiconjOn Set.univ)).isSemiconjOn
  simpa using h

/-- **Rempała's theorem on trajectories (M3, SIR): EB solutions are mass-action solutions.**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M3): "EB_{Pois μ}(P) → MA(E_μ P) [...] π = (θ,
φ, pop) ↦ (qξe^{μ(θ−1)}, φ). For SIR: MA(β = μτ, γ_MA = γ + τ). **The MA "I" is φ_I, not
prevalence**"; §D.3: "semiconjugacies map solution curves to solution curves".

Lean statement: let `μ ≠ 0`, `τ`, `γ`, `q` be real, and let `I` be a time interval, i.e. any
convex set of times with `0 ∈ I` (for example `(a, b)` with `a < 0 < b`, `[0, T)`, `[0, ∞)` or
`ℝ`). Let `x : ℝ → EB SIRSp` solve, on `I`, the general per-reaction EB model of SIR
(`s + I → I + I` at per-contact rate τ, `I → R` at rate γ) on the Poisson(μ) configuration
network `ψ(x) = e^{μ(x−1)}` with seed factor `q`: `HasDerivWithinAt x (lift … (x t)) I t` for
every `t ∈ I` (one-sided at end points of `I` in `I`; implied by `HasDerivAt`). Assume
`ξ(0) = 1`. Then the curve `t ↦ (S(t), I(t)) = (q e^{μ(θ(t)−1)}, φ_I(t))` solves mass-action SIR
`Ṡ = −βSI`, `İ = βSI − (γ + τ)I` with `β = μτ` on `I`, in the same sense (derivative within `I`)
at every `t ∈ I`.

Scope: global solutions are not required; forward solutions on `[0, T)` and local solutions are
covered. -/
theorem rempala_solution (μ τ γ q : ℝ) (hμ : μ ≠ 0) {I : Set ℝ} (hI : Convex ℝ I)
    (h0 : (0 : ℝ) ∈ I) {x : ℝ → EB SIRSp}
    (hx : ∀ t ∈ I, HasDerivWithinAt x (lift (CNet.poisson μ) q (sirRxns τ γ) (x t)) I t)
    (hξ : (x 0).2.1 = 1) :
    ∀ t ∈ I, HasDerivWithinAt (fun t => (q * Real.exp (μ * ((x t).1 - 1)), (x t).2.2.1 .I))
      ((maSIR (μ * τ) (γ + τ)).F (q * Real.exp (μ * ((x t).1 - 1)), (x t).2.2.1 .I)) I t := by
  have hno : ∀ r ∈ sirRxns τ γ, r.isExit = false := by
    intro r hr
    simp only [sirRxns, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl <;> rfl
  have hU : ∀ t ∈ I, x t ∈ {u : EB SIRSp | u.2.1 = 1} := by
    intro t ht
    show (x t).2.1 = 1
    rw [xi_const (CNet.poisson μ) q (sirRxns τ γ) hno hI h0 hx t ht, hξ]
  exact (SemiconjOn.ofIsSemiconjOn _ (rempala_lift μ τ γ q hμ)).map_solution_within
    (A := ebSys (CNet.poisson μ) q (sirRxns τ γ)) hx hU

end NEP
