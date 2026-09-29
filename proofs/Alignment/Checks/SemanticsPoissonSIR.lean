import Alignment.Registry
import Alignment.Shadows.SemanticsPoissonSIR
import NetworkEpi

/-!
# Checkers: group `SemanticsPoissonSIR` (trusted module `NetworkEpi.Semantics.PoissonSIR`)

Checker author (SA-PASS role 3, non-blind). For each of the nine `implemented` claims of
`NetworkEpi/Semantics/PoissonSIR.lean` (`rempalaLift` and `rempalaSolution` are sourced in
`NetworkEpi/Morphisms/Rempala.lean`, hence `import NetworkEpi`) this file holds the `sa_claim`
registration (verbatim registry text, registry `impl` list), the forward checkers
`sa_impl% → Sᵢ`, the backward checker `S₁ → … → Sₙ → sa_impl%`, and `sa_fail_*` records where no
structural derivation exists.

No bridges are declared. The alignment helpers of the blind shadows (`remMap`, `remDeriv`,
`remXi`, `remXiOne`, `chartThetaPhiI`) are definitionally equal to the trusted `poisMap μ q`, the
derivative of `hasFDerivAt_poisMap_qμ`, the map of `rempala_lift_xi`, `poisMap μ q ∘ sirChart` and
`sirChart`, so definitional unfolding identifies them. The remaining mismatches involve no trusted
definition that a bridge could identify (the order on ℝ, excluded middle, missing or surplus
conjuncts), so they are recorded as failures.

The only local helper is `pairExt` (pair equality from its two coordinates), proved with
`congr`/`congrArg` and structure eta. It is inlined by the audit.

Recorded failures, in summary (after the text remediation and the new impl lists):

* `hasFDerivAtPoisMap`: none. The impl `hasFDerivAt_poisMap_qμ` has the scalar in the text's order
  `q * μ * exp (μ(θ−1))`, so S1 is the impl at `u = (θ, φ)` (definitional unfolding of `remDeriv`).
* `rempala`: none (the impl `rempala_quotient_sir_spec` states S3 ∧ S4 ∧ S5 ∧ S6 exactly).
* `contDiffPoisMap`: none (the impl `contDiff_poisMap_dyn` is the conjunction S1 ∧ S2 ∧ S3 ∧ S4).
* `rempalaLift`: none (`rempala_lift_xi` gives S1/S2 with `remXi`, `rempala_lift` gives S3/S4 with
  `remXiOne`, both by definitional unfolding).
* `rempalaSolution`: none (the impl `rempala_solution_any_xi0` is S1 ∧ S2).
-/

open NEP

namespace Alignment.Shadows.SemanticsPoissonSIR

/-- Pair equality from the two coordinates (structure eta, `congr`, `congrArg`). -/
theorem pairExt {α β : Type} (p r : α × β) (h1 : p.1 = r.1) (h2 : p.2 = r.2) : p = r :=
  congr (congrArg Prod.mk h1) h2

end Alignment.Shadows.SemanticsPoissonSIR

/-! ## `SemanticsPoissonSIR.hasFDerivAtPoisMap` -/

namespace Alignment.Shadows.SemanticsPoissonSIR.HasFDerivAtPoisMap

sa_claim "SemanticsPoissonSIR.hasFDerivAtPoisMap" group "SemanticsPoissonSIR" required
  text "The derivative of Rempała's map: `Dπ(θ, φ)(dθ, dφ) = (qμe^{μ(θ−1)} dθ, dφ)`."
  impl NEP.hasFDerivAt_poisMap_qμ

/-- S1: `remDeriv μ q (θ, φ)` is definitionally the impl's linear map at `u = (θ, φ)`. -/
@[sa_forward "SemanticsPoissonSIR.hasFDerivAtPoisMap" 1]
theorem fwd1 (h : sa_impl% "SemanticsPoissonSIR.hasFDerivAtPoisMap") : S1 := by
  intro μ q θ φ
  exact h μ q (θ, φ)

/-- Backward: `u` is definitionally `(u.1, u.2)` (structure eta). -/
@[sa_backward "SemanticsPoissonSIR.hasFDerivAtPoisMap"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsPoissonSIR.hasFDerivAtPoisMap" := by
  intro μ q u
  exact s1 μ q u.1 u.2

end Alignment.Shadows.SemanticsPoissonSIR.HasFDerivAtPoisMap

/-! ## `SemanticsPoissonSIR.rempala` -/

namespace Alignment.Shadows.SemanticsPoissonSIR.Rempala

sa_claim "SemanticsPoissonSIR.rempala" group "SemanticsPoissonSIR" required
  text "**Rempała's theorem for SIR as a semiconjugacy (M3, SIR case).** Design statement (DESIGN_NetworkEpiCore.md §D.5, M3): \"**Rempała quotient** (\"back to mass action on the same species\") | EB_{Pois μ}(P) → MA(E_μ P), E_μ P = c_μ P + {J_r → ∅ at τ_r} on the edge copies; π = (θ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ). For SIR: MA(β = μτ, γ_MA = γ + τ). **The MA \"I\" is φ_I, not prevalence** | natural semiconjugacy (surjective submersion) | **[L]** `NEP.rempala` (SIR)\". [...] The design's \"surjective submersion\" holds for `μ ≠ 0` and `q > 0`, onto the mass-action states with `S > 0` (`rempala_quotient_sir`); it fails for `μ = 0` or `q = 0`."
  impl NEP.rempala NEP.rempala_quotient_sir_spec

/-- S1 (S row): `remMap μ q` is definitionally `poisMap μ q`; project the identity of `rempala`
on `.1`. -/
@[sa_forward "SemanticsPoissonSIR.rempala" 1]
theorem fwd1 (h : sa_impl% "SemanticsPoissonSIR.rempala") : S1 := by
  intro μ τ γ q u
  exact ⟨(h.1 μ τ γ q).1 u, congrArg Prod.fst ((h.1 μ τ γ q).2 u)⟩

/-- S2 (I row): as S1, projected on `.2`. -/
@[sa_forward "SemanticsPoissonSIR.rempala" 2]
theorem fwd2 (h : sa_impl% "SemanticsPoissonSIR.rempala") : S2 := by
  intro μ τ γ q u
  exact ⟨(h.1 μ τ γ q).1 u, congrArg Prod.snd ((h.1 μ τ γ q).2 u)⟩

/-- S3–S6 are the four conjuncts of `rempala_quotient_sir_spec`. -/
@[sa_forward "SemanticsPoissonSIR.rempala" 3]
theorem fwd3 (h : sa_impl% "SemanticsPoissonSIR.rempala") : S3 := h.2.1

@[sa_forward "SemanticsPoissonSIR.rempala" 4]
theorem fwd4 (h : sa_impl% "SemanticsPoissonSIR.rempala") : S4 := h.2.2.1

@[sa_forward "SemanticsPoissonSIR.rempala" 5]
theorem fwd5 (h : sa_impl% "SemanticsPoissonSIR.rempala") : S5 := h.2.2.2.1

@[sa_forward "SemanticsPoissonSIR.rempala" 6]
theorem fwd6 (h : sa_impl% "SemanticsPoissonSIR.rempala") : S6 := h.2.2.2.2

/-- Backward: `rempala` from the two rows S1, S2 (`IsSemiconj` unfolds to differentiability and
the pointwise identity; `pairExt` joins the rows); the spec is S3 ∧ S4 ∧ S5 ∧ S6. -/
@[sa_backward "SemanticsPoissonSIR.rempala"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) :
    sa_impl% "SemanticsPoissonSIR.rempala" :=
  ⟨fun μ τ γ q => ⟨fun u => (s1 μ τ γ q u).1,
      fun u => pairExt _ _ (s1 μ τ γ q u).2 (s2 μ τ γ q u).2⟩, s3, s4, s5, s6⟩

end Alignment.Shadows.SemanticsPoissonSIR.Rempala

/-! ## `SemanticsPoissonSIR.contDiffPoisMap` -/

namespace Alignment.Shadows.SemanticsPoissonSIR.ContDiffPoisMap

sa_claim "SemanticsPoissonSIR.contDiffPoisMap" group "SemanticsPoissonSIR" required
  text "Rempała's map is C^∞, so `rempalaHom` is also a morphism of the design's category **Dyn** (whose morphisms are C¹)."
  impl NEP.contDiff_poisMap_dyn

/-- S1: the first conjunct of the impl, `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (poisMap μ q)`
(the impl quantifies over `τ, γ`, which this conjunct does not use; instantiate them at `0`). -/
@[sa_forward "SemanticsPoissonSIR.contDiffPoisMap" 1]
theorem fwd1 (h : sa_impl% "SemanticsPoissonSIR.contDiffPoisMap") : S1 := by
  intro μ q
  exact (h μ 0 0 q).1

/-- S2: the second conjunct, `ContDiff ℝ 1 (rempalaHom μ τ γ q).π`. -/
@[sa_forward "SemanticsPoissonSIR.contDiffPoisMap" 2]
theorem fwd2 (h : sa_impl% "SemanticsPoissonSIR.contDiffPoisMap") : S2 := by
  intro μ τ γ q
  exact (h μ τ γ q).2.1

/-- S3: the third conjunct is `IsDynObject (ebPoisSIR μ τ γ q)` unfolded. -/
@[sa_forward "SemanticsPoissonSIR.contDiffPoisMap" 3]
theorem fwd3 (h : sa_impl% "SemanticsPoissonSIR.contDiffPoisMap") : S3 := by
  intro μ τ γ q
  exact (h μ τ γ q).2.2.1

/-- S4: the fourth conjunct is `IsDynObject (maSIR (μ * τ) (γ + τ))` unfolded (`q` unused,
instantiated at `0`). -/
@[sa_forward "SemanticsPoissonSIR.contDiffPoisMap" 4]
theorem fwd4 (h : sa_impl% "SemanticsPoissonSIR.contDiffPoisMap") : S4 := by
  intro μ τ γ
  exact (h μ τ γ 0).2.2.2

@[sa_backward "SemanticsPoissonSIR.contDiffPoisMap"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) :
    sa_impl% "SemanticsPoissonSIR.contDiffPoisMap" := by
  intro μ τ γ q
  exact ⟨s1 μ q, s2 μ τ γ q, s3 μ τ γ q, s4 μ τ γ⟩

end Alignment.Shadows.SemanticsPoissonSIR.ContDiffPoisMap

/-! ## `SemanticsPoissonSIR.poissonHasDerivAtPsi` -/

namespace Alignment.Shadows.SemanticsPoissonSIR.PoissonHasDerivAtPsi

sa_claim "SemanticsPoissonSIR.poissonHasDerivAtPsi" group "SemanticsPoissonSIR" required
  text "On the Poisson network, `ψ'` is the derivative of `ψ` everywhere."
  impl NEP.CNet.poisson_hasDerivAt_ψ

@[sa_forward "SemanticsPoissonSIR.poissonHasDerivAtPsi" 1]
theorem fwd1 (h : sa_impl% "SemanticsPoissonSIR.poissonHasDerivAtPsi") : S1 := by
  intro μ x
  exact h μ x

@[sa_backward "SemanticsPoissonSIR.poissonHasDerivAtPsi"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsPoissonSIR.poissonHasDerivAtPsi" := by
  intro μ x
  exact s1 μ x

end Alignment.Shadows.SemanticsPoissonSIR.PoissonHasDerivAtPsi

/-! ## `SemanticsPoissonSIR.poissonHasDerivAtPsiPrime` -/

namespace Alignment.Shadows.SemanticsPoissonSIR.PoissonHasDerivAtPsiPrime

sa_claim "SemanticsPoissonSIR.poissonHasDerivAtPsiPrime" group "SemanticsPoissonSIR" required
  text "On the Poisson network, `ψ''` is the derivative of `ψ'` everywhere."
  impl NEP.CNet.poisson_hasDerivAt_ψ'

@[sa_forward "SemanticsPoissonSIR.poissonHasDerivAtPsiPrime" 1]
theorem fwd1 (h : sa_impl% "SemanticsPoissonSIR.poissonHasDerivAtPsiPrime") : S1 := by
  intro μ x
  exact h μ x

@[sa_backward "SemanticsPoissonSIR.poissonHasDerivAtPsiPrime"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsPoissonSIR.poissonHasDerivAtPsiPrime" := by
  intro μ x
  exact s1 μ x

end Alignment.Shadows.SemanticsPoissonSIR.PoissonHasDerivAtPsiPrime

/-! ## `SemanticsPoissonSIR.sirChartLApply` -/

namespace Alignment.Shadows.SemanticsPoissonSIR.SirChartLApply

sa_claim "SemanticsPoissonSIR.sirChartLApply" group "SemanticsPoissonSIR" required
  text "`sirChartL` is `sirChart`."
  impl NEP.sirChartL_apply

@[sa_forward "SemanticsPoissonSIR.sirChartLApply" 1]
theorem fwd1 (h : sa_impl% "SemanticsPoissonSIR.sirChartLApply") : S1 := by
  intro u
  exact congrArg Prod.fst (h u)

@[sa_forward "SemanticsPoissonSIR.sirChartLApply" 2]
theorem fwd2 (h : sa_impl% "SemanticsPoissonSIR.sirChartLApply") : S2 := by
  intro u
  exact congrArg Prod.snd (h u)

@[sa_backward "SemanticsPoissonSIR.sirChartLApply"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "SemanticsPoissonSIR.sirChartLApply" := by
  intro u
  exact pairExt _ _ (s1 u) (s2 u)

end Alignment.Shadows.SemanticsPoissonSIR.SirChartLApply

/-! ## `SemanticsPoissonSIR.ebPoisSIRLift` -/

namespace Alignment.Shadows.SemanticsPoissonSIR.EbPoisSIRLift

sa_claim "SemanticsPoissonSIR.ebPoisSIRLift" group "SemanticsPoissonSIR" required
  text "**`ebPoisSIR` is the SIR EBCM of the general lift.** For `μ ≠ 0`, the chart `(θ, ξ, φ, pop) ↦ (θ, φ_I)` is a local semiconjugacy on `{ξ = 1}` from the general EB model `ebSys (CNet.poisson μ) q (sirRxns τ γ)` (the per-reaction lift of `s + I → I + I` at τ and `I → R` at γ on a Poisson(μ) network) to `ebPoisSIR μ τ γ q`."
  impl NEP.ebPoisSIR_lift

/-- S1 (θ row): `chartThetaPhiI` is definitionally `sirChart`, and `u ∈ {u | u.2.1 = 1}` is
definitionally `u.2.1 = 1`. -/
@[sa_forward "SemanticsPoissonSIR.ebPoisSIRLift" 1]
theorem fwd1 (h : sa_impl% "SemanticsPoissonSIR.ebPoisSIRLift") : S1 := by
  intro μ τ γ q hμ u hu
  exact ⟨(h μ τ γ q hμ).1 u hu, congrArg Prod.fst ((h μ τ γ q hμ).2 u hu)⟩

/-- S2 (φ_I row): as S1, projected on `.2`. -/
@[sa_forward "SemanticsPoissonSIR.ebPoisSIRLift" 2]
theorem fwd2 (h : sa_impl% "SemanticsPoissonSIR.ebPoisSIRLift") : S2 := by
  intro μ τ γ q hμ u hu
  exact ⟨(h μ τ γ q hμ).1 u hu, congrArg Prod.snd ((h μ τ γ q hμ).2 u hu)⟩

@[sa_backward "SemanticsPoissonSIR.ebPoisSIRLift"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "SemanticsPoissonSIR.ebPoisSIRLift" := by
  intro μ τ γ q hμ
  exact ⟨fun u hu => (s1 μ τ γ q hμ u hu).1,
    fun u hu => pairExt _ _ (s1 μ τ γ q hμ u hu).2 (s2 μ τ γ q hμ u hu).2⟩

end Alignment.Shadows.SemanticsPoissonSIR.EbPoisSIRLift

/-! ## `SemanticsPoissonSIR.rempalaLift` -/

namespace Alignment.Shadows.SemanticsPoissonSIR.RempalaLift

sa_claim "SemanticsPoissonSIR.rempalaLift" group "SemanticsPoissonSIR" required
  text "**Rempała's quotient from the general SIR lift, with the design's map `(qξe^{μ(θ−1)}, φ_I)`, for `μ ≠ 0` (M3, SIR case).** Design statement (DESIGN_NetworkEpiCore.md §D.5, M3): \"EB_{Pois μ}(P) → MA(E_μ P), E_μ P = c_μ P + {J_r → ∅ at τ_r} on the edge copies; π = (θ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ). For SIR: MA(β = μτ, γ_MA = γ + τ). **The MA \"I\" is φ_I, not prevalence**\". [...] On the slice `ξ = 1` the map is `(q e^{μ(θ−1)}, φ_I)` (`NEP.rempala_lift`)."
  impl NEP.rempala_lift_xi NEP.rempala_lift

/-- S1 (design's map, S row): `remXi μ q` is definitionally the map of `rempala_lift_xi`, and
`Differentiable` is `∀ u, DifferentiableAt`. -/
@[sa_forward "SemanticsPoissonSIR.rempalaLift" 1]
theorem fwd1 (h : sa_impl% "SemanticsPoissonSIR.rempalaLift") : S1 := by
  intro μ τ γ q hμ u
  exact ⟨(h.1 μ τ γ q hμ).1 u, congrArg Prod.fst ((h.1 μ τ γ q hμ).2 u)⟩

/-- S2 (design's map, I row): as S1, projected on `.2`. -/
@[sa_forward "SemanticsPoissonSIR.rempalaLift" 2]
theorem fwd2 (h : sa_impl% "SemanticsPoissonSIR.rempalaLift") : S2 := by
  intro μ τ γ q hμ u
  exact ⟨(h.1 μ τ γ q hμ).1 u, congrArg Prod.snd ((h.1 μ τ γ q hμ).2 u)⟩

/-- S3 (slice map, S row): `poisMap μ q ∘ sirChart` is definitionally `remXiOne μ q`, and
`u ∈ {u | u.2.1 = 1}` is definitionally `u.2.1 = 1`. -/
@[sa_forward "SemanticsPoissonSIR.rempalaLift" 3]
theorem fwd3 (h : sa_impl% "SemanticsPoissonSIR.rempalaLift") : S3 := by
  intro μ τ γ q hμ u hu
  exact ⟨(h.2 μ τ γ q hμ).1 u hu, congrArg Prod.fst ((h.2 μ τ γ q hμ).2 u hu)⟩

/-- S4 (slice map, I row): as S3, projected on `.2`. -/
@[sa_forward "SemanticsPoissonSIR.rempalaLift" 4]
theorem fwd4 (h : sa_impl% "SemanticsPoissonSIR.rempalaLift") : S4 := by
  intro μ τ γ q hμ u hu
  exact ⟨(h.2 μ τ γ q hμ).1 u hu, congrArg Prod.snd ((h.2 μ τ γ q hμ).2 u hu)⟩

/-- Backward: S1 and S2 give `rempala_lift_xi` (differentiability at every state and both rows of
the identity); S3 and S4 give `rempala_lift` on `{ξ = 1}`. -/
@[sa_backward "SemanticsPoissonSIR.rempalaLift"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) :
    sa_impl% "SemanticsPoissonSIR.rempalaLift" := by
  refine ⟨?_, ?_⟩
  · intro μ τ γ q hμ
    exact ⟨fun u => (s1 μ τ γ q hμ u).1,
      fun u => pairExt _ _ (s1 μ τ γ q hμ u).2 (s2 μ τ γ q hμ u).2⟩
  · intro μ τ γ q hμ
    exact ⟨fun u hu => (s3 μ τ γ q hμ u hu).1,
      fun u hu => pairExt _ _ (s3 μ τ γ q hμ u hu).2 (s4 μ τ γ q hμ u hu).2⟩

end Alignment.Shadows.SemanticsPoissonSIR.RempalaLift

/-! ## `SemanticsPoissonSIR.rempalaSolution` -/

namespace Alignment.Shadows.SemanticsPoissonSIR.RempalaSolution

sa_claim "SemanticsPoissonSIR.rempalaSolution" group "SemanticsPoissonSIR" required
  text "**Rempała's theorem on trajectories with the design's map `(qξe^{μ(θ−1)}, φ_I)`, for `μ ≠ 0` (M3, SIR).** Design statement (DESIGN_NetworkEpiCore.md §D.5, M3): \"EB_{Pois μ}(P) → MA(E_μ P) [...] π = (θ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ). For SIR: MA(β = μτ, γ_MA = γ + τ). **The MA \"I\" is φ_I, not prevalence**\"; §D.3: \"semiconjugacies map solution curves to solution curves\". [...] No condition on `ξ(0)` is needed."
  impl NEP.rempala_solution_any_xi0

/-- S1 (`ξ(0) = 1`): the first conjunct of the impl (`remXi μ q (x s)` is definitionally the
impl's image curve). -/
@[sa_forward "SemanticsPoissonSIR.rempalaSolution" 1]
theorem fwd1 (h : sa_impl% "SemanticsPoissonSIR.rempalaSolution") : S1 := by
  intro μ τ γ q hμ I x h0 hx
  exact h.1 μ τ γ q hμ I x h0 hx

/-- S2 (`ξ(0) ≠ 1`): the second conjunct. -/
@[sa_forward "SemanticsPoissonSIR.rempalaSolution" 2]
theorem fwd2 (h : sa_impl% "SemanticsPoissonSIR.rempalaSolution") : S2 := by
  intro μ τ γ q hμ I x h0 hx
  exact h.2 μ τ γ q hμ I x h0 hx

@[sa_backward "SemanticsPoissonSIR.rempalaSolution"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "SemanticsPoissonSIR.rempalaSolution" :=
  ⟨fun μ τ γ q hμ I x h0 hx => s1 μ τ γ q hμ I x h0 hx,
    fun μ τ γ q hμ I x h0 hx => s2 μ τ γ q hμ I x h0 hx⟩

end Alignment.Shadows.SemanticsPoissonSIR.RempalaSolution


