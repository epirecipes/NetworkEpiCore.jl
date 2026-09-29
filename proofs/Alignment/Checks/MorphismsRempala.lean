import Alignment.Registry
import Alignment.Shadows.MorphismsRempala

/-!
# Checkers: group `MorphismsRempala` (trusted module `NetworkEpi.Morphisms.Rempala`)

Checker author (SA-PASS role 3, non-blind). For each of the fifteen shadowed `implemented` claims
this file holds the `sa_claim` registration (verbatim registry text, registry `impl` list), the
bridges, the forward checkers `sa_impl% → Sᵢ`, the backward checker, and an `sa_fail_*` record
wherever a check is not structurally derivable. `MorphismsRempala.rempalaSeirField` is registered
too; the informal entries (`header.construction`, `rempalaSeirConsequence`) are not.

## Bridges

One bridge statement, registered separately for each of the three claims whose text speaks of
"the derivative" of Rempała's map (`rempalaQuotient`, `rempalaEbField`, `rempalaDSurjective`):
`rempalaD μ q u = fderiv ℝ (rempalaMap μ q) u`, for every type `σ` (no finiteness). The trusted
`rempalaD` has the docstring "The derivative of `rempalaMap μ q` at `u`"; the RHS is Mathlib's
Fréchet derivative, the text's notion. The proof (`hasFDerivAt_rempalaMap_any`) is done from Mathlib
in the TVS setting (`IsLittleOTVS`), because `σ → ℝ` carries only the product topology for infinite
`σ`; it does not use `NEP.hasFDerivAt_rempalaMap`, `NEP.hasFDerivAt_susc`, `NEP.rempalaD_apply` or
any other implementation theorem (only the definitions `rempalaMap`, `rempalaD`, `suscD`, `ebXi`,
`ebTheta`, `ebPhi`, `CNet.susc`, `CNet.poisson` are unfolded).

No bridge is needed for the design's explicit objects (`rempalaGeneral` S2, `rempalaGeneralSir`
S2, `rempalaGeneralSolution` S3/S4). `designMap μ q` is definitionally `rempalaMap μ q`. The
design `E_μ` agrees with `Rxn.rempala μ` reaction by reaction, by a case split on `Rxn` and `rfl`
(helpers `rempala_eq_designERxn` and `designE_eq`, both structural).

## Recorded failures

Remediation (new trusted theorems `rempala_general_solution_at`, `rempala_natural_min`,
`rempala_seir_field_eqns`, `rempalaD_apply_left`, `hasFDerivAt_rempalaMap_all`,
`rempalaMap_surjective_preimage`, `rempala_sir_proj_field`) plus the blind re-shadowing of
`rempalaGeneralSolution`, `rempalaSeirField` and `rempalaSirProj` removed every earlier
`sa_fail_*` record in this group. All checks here are structural.
-/

open NEP

/-! ## `MorphismsRempala.rempalaGeneral` -/

namespace Alignment.Shadows.MorphismsRempala.RempalaGeneral
open Alignment.Shadows.MorphismsRempala

sa_claim "MorphismsRempala.rempalaGeneral" group "MorphismsRempala" required
  text "**Rempała's quotient for every T_EB model (M3, general P).** Design statement (DESIGN_NetworkEpiCore.md §D.5, M3): \"**Rempała quotient** (\"back to mass action on the same species\") | EB_{Pois μ}(P) → MA(E_μ P), E_μ P = c_μ P + {J_r → ∅ at τ_r} on the edge copies; π = (θ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ). For SIR: MA(β = μτ, γ_MA = γ + τ). **The MA \"I\" is φ_I, not prevalence** | natural semiconjugacy (surjective submersion)\"; §J.10: \"**Exits in D_μ** (§D.5 M2) are `s → Φ_Y + Y`; in E_μ they stay `S → V`.\" [...] the MA coordinate `x_X` is the EB edge probability `φ_X`, not the node fraction `pop_X`, which the map forgets. [...] for every T_EB reaction list `P` (contacts, exits, progressions, removals; any number of infectors and entry states) and every `μ ≠ 0`, `rempalaMap μ q` is a global semiconjugacy from the EB model of `P` on a Poisson(μ) configuration network to the mass-action model of `E_μ P`."
  impl NEP.rempala_general

/-- Helper (structural): the design's `E_μ` of one reaction is `Rxn.rempala μ` of it, by a case
split on the reaction and `rfl`. -/
theorem rempala_eq_designERxn {σ : Type} (μ : ℝ) (r : Rxn σ) :
    Rxn.rempala μ r = designERxn μ r := by
  cases r <;> rfl

@[sa_forward "MorphismsRempala.rempalaGeneral" 1]
theorem fwd1 (h : sa_impl% "MorphismsRempala.rempalaGeneral") : S1 := by
  intro σ _ _ P μ q hμ
  exact h μ q hμ P

/-- S2: `designMap μ q` is definitionally `rempalaMap μ q` (unfold `CNet.susc`, `CNet.poisson`);
`designE μ P = P.flatMap (designERxn μ)` and `rempalaRxns μ P = P.flatMap (Rxn.rempala μ)`, which
agree by `rempala_eq_designERxn`. -/
@[sa_forward "MorphismsRempala.rempalaGeneral" 2]
theorem fwd2 (h : sa_impl% "MorphismsRempala.rempalaGeneral") : S2 := by
  intro σ _ _ P μ q hμ
  have e : (Rxn.rempala μ : Rxn σ → List (NRxn σ)) = designERxn μ :=
    funext (rempala_eq_designERxn μ)
  have hh := h μ q hμ P
  unfold rempalaRxns at hh
  rw [e] at hh
  exact hh

@[sa_backward "MorphismsRempala.rempalaGeneral"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "MorphismsRempala.rempalaGeneral" := by
  intro σ _ _ μ q hμ rs
  exact s1 rs μ q hμ

end Alignment.Shadows.MorphismsRempala.RempalaGeneral

/-! ## `MorphismsRempala.rempalaGeneralSolution`

`sa_impl%` is `rempala_general_solution_at ∧ rempala_general_solution` (two-sided, then within `I`).
`(ebSys N q P).F` is definitionally `lift N q P` and `(maSys E).F` is `maLift E`. For S3/S4,
`designMap μ q` is definitionally `rempalaMap μ q`, and `designE μ P` equals `rempalaRxns μ P` via
`rempala_eq_designERxn` (case split on `Rxn` and `rfl`), so no bridge is needed. -/

namespace Alignment.Shadows.MorphismsRempala.RempalaGeneralSolution
open Alignment.Shadows.MorphismsRempala

sa_claim "MorphismsRempala.rempalaGeneralSolution" group "MorphismsRempala" required
  text "**Rempała's quotient on trajectories (M3, general P).** Design statement (DESIGN_NetworkEpiCore.md §D.5, M3): \"EB_{Pois μ}(P) → MA(E_μ P), E_μ P = c_μ P + {J_r → ∅ at τ_r} on the edge copies; π = (θ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ)\"; §D.3: \"semiconjugacies map solution curves to solution curves\". [...] No condition on `ξ(0)` is needed. [...] EB solutions on any set of times I (for example a time interval) map to MA solutions, both for derivatives within I and for two-sided derivatives at every time of I."
  impl NEP.rempala_general_solution_at NEP.rempala_general_solution

/-- Helper (structural): `designE μ P = rempalaRxns μ P`, from `rempala_eq_designERxn`. -/
theorem designE_eq {σ : Type} (μ : ℝ) (P : List (Rxn σ)) : rempalaRxns μ P = designE μ P := by
  have e : (Rxn.rempala μ : Rxn σ → List (NRxn σ)) = designERxn μ :=
    funext (RempalaGeneral.rempala_eq_designERxn μ)
  unfold rempalaRxns designE
  rw [e]

@[sa_forward "MorphismsRempala.rempalaGeneralSolution" 1]
theorem fwd1 (h : sa_impl% "MorphismsRempala.rempalaGeneralSolution") : S1 := by
  intro σ _ _ P μ q hμ I x hx
  exact h.1 μ q hμ P hx

@[sa_forward "MorphismsRempala.rempalaGeneralSolution" 2]
theorem fwd2 (h : sa_impl% "MorphismsRempala.rempalaGeneralSolution") : S2 := by
  intro σ _ _ P μ q hμ I x hx
  exact h.2 μ q hμ P hx

@[sa_forward "MorphismsRempala.rempalaGeneralSolution" 3]
theorem fwd3 (h : sa_impl% "MorphismsRempala.rempalaGeneralSolution") : S3 := by
  intro σ _ _ P μ q hμ I x hx
  have hh := h.1 μ q hμ P hx
  rw [designE_eq μ P] at hh
  exact hh

@[sa_forward "MorphismsRempala.rempalaGeneralSolution" 4]
theorem fwd4 (h : sa_impl% "MorphismsRempala.rempalaGeneralSolution") : S4 := by
  intro σ _ _ P μ q hμ I x hx
  have hh := h.2 μ q hμ P hx
  rw [designE_eq μ P] at hh
  exact hh

@[sa_backward "MorphismsRempala.rempalaGeneralSolution"]
theorem bwd (s1 : S1) (s2 : S2) (_s3 : S3) (_s4 : S4) :
    sa_impl% "MorphismsRempala.rempalaGeneralSolution" := by
  refine And.intro ?_ ?_
  · intro σ _ _ μ q hμ rs I x hx
    exact s1 rs μ q hμ I x hx
  · intro σ _ _ μ q hμ rs I x hx
    exact s2 rs μ q hμ I x hx

end Alignment.Shadows.MorphismsRempala.RempalaGeneralSolution

/-! ## `MorphismsRempala.rempalaNatural` -/

namespace Alignment.Shadows.MorphismsRempala.RempalaNatural

sa_claim "MorphismsRempala.rempalaNatural" group "MorphismsRempala" required
  text "**Rempała's quotient is natural in P (M3).** Design statement (DESIGN_NetworkEpiCore.md §D.5, M3): \"EB_{Pois μ}(P) → MA(E_μ P), E_μ P = c_μ P + {J_r → ∅ at τ_r} on the edge copies; π = (θ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ) [...] | natural semiconjugacy (surjective submersion)\". [...] this is naturality with respect to the species maps of the syntax (relabelling and gluing, DESIGN §D.1); it is not stated as a natural transformation of functors into `DynSys`. [...] `E_μ` commutes with relabelling species, and the map commutes with the pushforward and pullback of coordinates along species maps."
  impl NEP.rempala_natural_min

/-- The relabelling conjunct of the impl does not depend on `q`; any `q` (here `μ`) instantiates it. -/
@[sa_forward "MorphismsRempala.rempalaNatural" 1]
theorem fwd1 (h : sa_impl% "MorphismsRempala.rempalaNatural") : S1 := by
  intro σ σ' f μ P
  exact (h μ μ f).1 P

@[sa_forward "MorphismsRempala.rempalaNatural" 2]
theorem fwd2 (h : sa_impl% "MorphismsRempala.rempalaNatural") : S2 := by
  intro σ σ' _ _ f μ q u
  exact (h μ q f).2.1 u

@[sa_forward "MorphismsRempala.rempalaNatural" 3]
theorem fwd3 (h : sa_impl% "MorphismsRempala.rempalaNatural") : S3 := by
  intro σ σ' f μ q u
  exact (h μ q f).2.2 u

@[sa_backward "MorphismsRempala.rempalaNatural"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) : sa_impl% "MorphismsRempala.rempalaNatural" := by
  intro σ σ' μ q f
  refine And.intro (fun rs => s1 f μ rs) (And.intro ?_ (fun u => s3 f μ q u))
  intro _ _ u
  exact s2 f μ q u

end Alignment.Shadows.MorphismsRempala.RempalaNatural

/-! ## The derivative of Rempała's map (bridge helper, any `σ`) -/

namespace Alignment.Shadows.MorphismsRempala
open Asymptotics Filter Topology

/-- Helper for the bridges (not a checker): `rempalaMap μ q` has Fréchet derivative
`rempalaD μ q u` at `u` for every type `σ`, proved in the topological-vector-space setting from
Mathlib only (no implementation theorem is used). -/
theorem hasFDerivAt_rempalaMap_any {σ : Type} (μ q : ℝ) (u : EB σ) :
    HasFDerivAt (rempalaMap μ q) (rempalaD μ q u) u := by
  let P : EB σ →L[ℝ] ℝ × ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ _).prod
      ((ContinuousLinearMap.fst ℝ ℝ _).comp (ContinuousLinearMap.snd ℝ ℝ _))
  let g : ℝ × ℝ → ℝ := fun v => q * v.2 * Real.exp (μ * (v.1 - 1))
  let g' : ℝ × ℝ →L[ℝ] ℝ :=
    (q * Real.exp (μ * (u.1 - 1))) • ContinuousLinearMap.snd ℝ ℝ ℝ +
      (q * u.2.1 * (μ * Real.exp (μ * (u.1 - 1)))) • ContinuousLinearMap.fst ℝ ℝ ℝ
  have hg : HasFDerivAt g g' (P u) := by
    have h1 : HasFDerivAt (fun v : ℝ × ℝ => Real.exp (μ * (v.1 - 1)))
        (Real.exp (μ * (u.1 - 1)) • (μ • ContinuousLinearMap.fst ℝ ℝ ℝ)) (P u) := by
      have := ((hasFDerivAt_fst (𝕜 := ℝ) (p := P u)).sub_const 1).const_mul μ
      exact this.exp
    have h2 := ((hasFDerivAt_snd (𝕜 := ℝ) (p := P u)).const_mul q).mul h1
    refine h2.congr_fderiv ?_
    ext <;> simp [g', P] <;> ring_nf <;> simp
  have hT : Tendsto (Prod.map P P) (𝓝 u ×ˢ pure u) (𝓝 (P u) ×ˢ pure (P u)) :=
    (P.continuous.tendsto u).prodMap (tendsto_pure_pure _ _)
  have h1 := (HasFDerivAtFilter.isLittleOTVS hg).comp_tendsto hT
  have hO : (fun p : EB σ × EB σ => P p.1 - P p.2) =O[ℝ; 𝓝 u ×ˢ pure u]
      (fun p : EB σ × EB σ => p.1 - p.2) := by
    have := (P.isBigOTVS_id
      (l := map (fun p : EB σ × EB σ => p.1 - p.2) (𝓝 u ×ˢ pure u))).comp_tendsto tendsto_map
    refine this.congr_left ?_
    intro p; simp
  have hfst := h1.trans_isBigOTVS hO
  refine ⟨?_⟩
  have hsnd : (fun p : EB σ × EB σ =>
      (rempalaMap μ q p.1 - rempalaMap μ q p.2 - rempalaD μ q u (p.1 - p.2)).2)
      =o[ℝ; 𝓝 u ×ˢ pure u] (fun p : EB σ × EB σ => p.1 - p.2) := by
    refine (IsLittleOTVS.zero _ _).congr_left ?_
    intro p
    funext X
    simp only [rempalaMap, rempalaD, ebPhi, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', Prod.snd_sub, Prod.fst_sub, Pi.sub_apply, Pi.zero_apply,
      sub_self]
  have hfst' : (fun p : EB σ × EB σ =>
      (rempalaMap μ q p.1 - rempalaMap μ q p.2 - rempalaD μ q u (p.1 - p.2)).1)
      =o[ℝ; 𝓝 u ×ˢ pure u] (fun p : EB σ × EB σ => p.1 - p.2) := by
    refine hfst.congr_left ?_
    intro p
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, g, g', P, rempalaMap, rempalaD,
      suscD, ebXi, ebTheta, CNet.susc, CNet.poisson, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_comp', ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, Prod.fst_sub, Prod.snd_sub,
      smul_eq_mul]
  exact hfst'.prodMk hsnd

end Alignment.Shadows.MorphismsRempala

/-! ## `MorphismsRempala.rempalaQuotient` -/

namespace Alignment.Shadows.MorphismsRempala.RempalaQuotient

sa_claim "MorphismsRempala.rempalaQuotient" group "MorphismsRempala" required
  text "**Rempała's map is a surjective submersion (M3).** Design statement (DESIGN_NetworkEpiCore.md §D.5, M3): \"π = (θ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ) [...] | natural semiconjugacy (surjective submersion)\". [...] for `q ≠ 0` the map and its derivative at every point are surjective (a surjective submersion, i.e. a quotient)."
  impl NEP.rempala_quotient

/-- Bridge (needs independent review): the trusted `rempalaD μ q u` ("The derivative of
`rempalaMap μ q` at `u`") is the text's "derivative" of the map, Mathlib's Fréchet derivative. -/
@[sa_bridge "MorphismsRempala.rempalaQuotient"]
theorem bridge_rempalaD {σ : Type} (μ q : ℝ) (u : EB σ) :
    rempalaD μ q u = fderiv ℝ (rempalaMap μ q) u :=
  (hasFDerivAt_rempalaMap_any μ q u).fderiv.symm

@[sa_forward "MorphismsRempala.rempalaQuotient" 1]
theorem fwd1 (h : sa_impl% "MorphismsRempala.rempalaQuotient") : S1 := by
  intro σ μ q hq
  exact (h μ q hq).1

@[sa_forward "MorphismsRempala.rempalaQuotient" 2]
theorem fwd2 (h : sa_impl% "MorphismsRempala.rempalaQuotient") : S2 := by
  intro σ μ q hq u
  rw [← bridge_rempalaD μ q u]
  exact (h μ q hq).2 u

@[sa_backward "MorphismsRempala.rempalaQuotient"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "MorphismsRempala.rempalaQuotient" := by
  intro σ μ q hq
  refine And.intro (s1 μ q hq) (fun u => ?_)
  rw [bridge_rempalaD μ q u]
  exact s2 μ q hq u

end Alignment.Shadows.MorphismsRempala.RempalaQuotient

/-! ## `MorphismsRempala.rempalaGeneralSir`

`sirProj ∘ rempalaMap μ q` unfolds (`Function.comp`) to S1's map, and further (`sirProj`,
`rempalaMap`, `CNet.susc`, `CNet.poisson`) to S2's explicit map. -/

namespace Alignment.Shadows.MorphismsRempala.RempalaGeneralSir

sa_claim "MorphismsRempala.rempalaGeneralSir" group "MorphismsRempala" required
  text "**Rempała's theorem for SIR from the general quotient, without `ξ = 1` (M3, SIR).** Design statement (DESIGN_NetworkEpiCore.md §D.5, M3): \"EB_{Pois μ}(P) → MA(E_μ P) [...] π = (θ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ). For SIR: MA(β = μτ, γ_MA = γ + τ). **The MA \"I\" is φ_I, not prevalence**\". [...] it holds at every state, not only on `ξ = 1`. [...] for SIR, composing with the projection `(S, x) ↦ (S, x_I)` gives mass-action SIR with `β = μτ`, `ρ = γ + τ`, the SIR case `NEP.rempala`, now without the restriction `ξ = 1`."
  impl NEP.rempala_general_sir

@[sa_forward "MorphismsRempala.rempalaGeneralSir" 1]
theorem fwd1 (h : sa_impl% "MorphismsRempala.rempalaGeneralSir") : S1 := by
  intro μ τ γ q hμ
  exact h μ τ γ q hμ

@[sa_forward "MorphismsRempala.rempalaGeneralSir" 2]
theorem fwd2 (h : sa_impl% "MorphismsRempala.rempalaGeneralSir") : S2 := by
  intro μ τ γ q hμ
  exact h μ τ γ q hμ

@[sa_backward "MorphismsRempala.rempalaGeneralSir"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "MorphismsRempala.rempalaGeneralSir" := by
  intro μ τ γ q hμ
  exact s1 μ τ γ q hμ

end Alignment.Shadows.MorphismsRempala.RempalaGeneralSir

/-! ## `MorphismsRempala.rempalaSeirField`

The shadows read the field as `(maSys (rempalaRxns μ (seirRxns τ a γ))).F v`, definitionally
`maLift (rempalaRxns μ (seirRxns τ a γ)) v`, the impl's field. -/

namespace Alignment.Shadows.MorphismsRempala.RempalaSeirField

sa_claim "MorphismsRempala.rempalaSeirField" group "MorphismsRempala" required
  text "**Rempała's quotient for SEIR: the mass-action equations of `E_μ(SEIR)` (M3, SEIR).** Design statement (DESIGN_NetworkEpiCore.md §D.5, M3): \"EB_{Pois μ}(P) → MA(E_μ P), E_μ P = c_μ P + {J_r → ∅ at τ_r} on the edge copies; π = (θ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ)\"."
  impl NEP.rempala_seir_field_eqns

@[sa_forward "MorphismsRempala.rempalaSeirField" 1]
theorem fwd1 (h : sa_impl% "MorphismsRempala.rempalaSeirField") : S1 := by
  intro μ τ a γ v
  exact (h μ τ a γ v).1

@[sa_forward "MorphismsRempala.rempalaSeirField" 2]
theorem fwd2 (h : sa_impl% "MorphismsRempala.rempalaSeirField") : S2 := by
  intro μ τ a γ v
  exact (h μ τ a γ v).2.1

@[sa_forward "MorphismsRempala.rempalaSeirField" 3]
theorem fwd3 (h : sa_impl% "MorphismsRempala.rempalaSeirField") : S3 := by
  intro μ τ a γ v
  exact (h μ τ a γ v).2.2.1

@[sa_forward "MorphismsRempala.rempalaSeirField" 4]
theorem fwd4 (h : sa_impl% "MorphismsRempala.rempalaSeirField") : S4 := by
  intro μ τ a γ v
  exact (h μ τ a γ v).2.2.2

@[sa_backward "MorphismsRempala.rempalaSeirField"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) :
    sa_impl% "MorphismsRempala.rempalaSeirField" := by
  intro μ τ a γ v
  exact ⟨s1 μ τ a γ v, s2 μ τ a γ v, s3 μ τ a γ v, s4 μ τ a γ v⟩

end Alignment.Shadows.MorphismsRempala.RempalaSeirField

/-! ## `MorphismsRempala.rempalaDApply` -/

namespace Alignment.Shadows.MorphismsRempala.RempalaDApply

sa_claim "MorphismsRempala.rempalaDApply" group "MorphismsRempala" required
  text "`rempalaD μ q u v = (q (v_ξ e^{μ(θ−1)} + ξ μ e^{μ(θ−1)} v_θ), v_φ)`."
  impl NEP.rempalaD_apply_left

@[sa_forward "MorphismsRempala.rempalaDApply" 1]
theorem fwd1 (h : sa_impl% "MorphismsRempala.rempalaDApply") : S1 := by
  intro σ μ q u v
  exact (h μ q u v).1

@[sa_forward "MorphismsRempala.rempalaDApply" 2]
theorem fwd2 (h : sa_impl% "MorphismsRempala.rempalaDApply") : S2 := by
  intro σ μ q u v
  exact (h μ q u v).2

@[sa_backward "MorphismsRempala.rempalaDApply"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "MorphismsRempala.rempalaDApply" := by
  intro σ μ q u v
  exact ⟨s1 μ q u v, s2 μ q u v⟩

end Alignment.Shadows.MorphismsRempala.RempalaDApply

/-! ## `MorphismsRempala.hasFDerivAtRempalaMap` -/

namespace Alignment.Shadows.MorphismsRempala.HasFDerivAtRempalaMap

sa_claim "MorphismsRempala.hasFDerivAtRempalaMap" group "MorphismsRempala" required
  text "`rempalaMap μ q` has derivative `rempalaD μ q u` at every `u`."
  impl NEP.hasFDerivAt_rempalaMap_all

@[sa_forward "MorphismsRempala.hasFDerivAtRempalaMap" 1]
theorem fwd1 (h : sa_impl% "MorphismsRempala.hasFDerivAtRempalaMap") : S1 := by
  intro σ μ q u
  exact h μ q u

@[sa_backward "MorphismsRempala.hasFDerivAtRempalaMap"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsRempala.hasFDerivAtRempalaMap" := by
  intro σ μ q u
  exact s1 μ q u

end Alignment.Shadows.MorphismsRempala.HasFDerivAtRempalaMap

/-! ## `MorphismsRempala.rempalaEbField` -/

namespace Alignment.Shadows.MorphismsRempala.RempalaEbField

sa_claim "MorphismsRempala.rempalaEbField" group "MorphismsRempala" required
  text "**Per-reaction identity behind M3.** On the Poisson(μ) network with `μ ≠ 0`, the derivative of Rempała's map carries the EB field of each T_EB reaction `r` to the mass-action field of `E_μ r` at the image point."
  impl NEP.rempala_ebField

/-- Bridge (needs independent review): the trusted `rempalaD μ q u` is the text's "the derivative
of Rempała's map", Mathlib's Fréchet derivative. Same statement as
`RempalaQuotient.bridge_rempalaD`, registered for this claim. -/
@[sa_bridge "MorphismsRempala.rempalaEbField"]
theorem bridge_rempalaD {σ : Type} (μ q : ℝ) (u : EB σ) :
    rempalaD μ q u = fderiv ℝ (rempalaMap μ q) u :=
  (hasFDerivAt_rempalaMap_any μ q u).fderiv.symm

@[sa_forward "MorphismsRempala.rempalaEbField" 1]
theorem fwd1 (h : sa_impl% "MorphismsRempala.rempalaEbField") : S1 := by
  intro σ _ μ q hμ r u
  rw [← bridge_rempalaD μ q u]
  exact h μ q hμ r u

@[sa_backward "MorphismsRempala.rempalaEbField"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsRempala.rempalaEbField" := by
  intro σ _ μ q hμ r u
  rw [bridge_rempalaD μ q u]
  exact s1 μ q hμ r u

end Alignment.Shadows.MorphismsRempala.RempalaEbField

/-! ## `MorphismsRempala.rxnRempalaMap` -/

namespace Alignment.Shadows.MorphismsRempala.RxnRempalaMap

sa_claim "MorphismsRempala.rxnRempalaMap" group "MorphismsRempala" required
  text "`E_μ` commutes with relabelling the node species of one reaction."
  impl NEP.Rxn.rempala_map

@[sa_forward "MorphismsRempala.rxnRempalaMap" 1]
theorem fwd1 (h : sa_impl% "MorphismsRempala.rxnRempalaMap") : S1 := by
  intro σ σ' f μ r
  exact h μ f r

@[sa_backward "MorphismsRempala.rxnRempalaMap"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsRempala.rxnRempalaMap" := by
  intro σ σ' μ f r
  exact s1 f μ r

end Alignment.Shadows.MorphismsRempala.RxnRempalaMap

/-! ## `MorphismsRempala.rempalaMapPull` -/

namespace Alignment.Shadows.MorphismsRempala.RempalaMapPull

sa_claim "MorphismsRempala.rempalaMapPull" group "MorphismsRempala" required
  text "The pullback of Rempała's map: `π(θ, ξ, φ ∘ f, pop ∘ f) = pullMA f (π(θ, ξ, φ, pop))`."
  impl NEP.rempalaMap_pull

/-- `pullEB f (θ, ξ, φ, pop)` unfolds to `(θ, ξ, φ ∘ f, pop ∘ f)`. -/
@[sa_forward "MorphismsRempala.rempalaMapPull" 1]
theorem fwd1 (h : sa_impl% "MorphismsRempala.rempalaMapPull") : S1 := by
  intro σ σ' f μ q θ ξ φ pop
  exact h μ q f (θ, ξ, φ, pop)

/-- Every `u : EB σ'` is `(u.1, u.2.1, u.2.2.1, u.2.2.2)` (η for products). -/
@[sa_backward "MorphismsRempala.rempalaMapPull"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsRempala.rempalaMapPull" := by
  intro σ σ' μ q f u
  exact s1 f μ q u.1 u.2.1 u.2.2.1 u.2.2.2

end Alignment.Shadows.MorphismsRempala.RempalaMapPull

/-! ## `MorphismsRempala.rempalaMapPush` -/

namespace Alignment.Shadows.MorphismsRempala.RempalaMapPush

sa_claim "MorphismsRempala.rempalaMapPush" group "MorphismsRempala" required
  text "The pushforward of Rempała's map: `π(pushEB f u) = pushMA f (π u)`."
  impl NEP.rempalaMap_push

@[sa_forward "MorphismsRempala.rempalaMapPush" 1]
theorem fwd1 (h : sa_impl% "MorphismsRempala.rempalaMapPush") : S1 := by
  intro σ σ' _ _ f μ q u
  exact h μ q f u

@[sa_backward "MorphismsRempala.rempalaMapPush"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsRempala.rempalaMapPush" := by
  intro σ σ' _ _ μ q f u
  exact s1 f μ q u

end Alignment.Shadows.MorphismsRempala.RempalaMapPush

/-! ## `MorphismsRempala.rempalaMapSurjective` -/

namespace Alignment.Shadows.MorphismsRempala.RempalaMapSurjective

sa_claim "MorphismsRempala.rempalaMapSurjective" group "MorphismsRempala" required
  text "For `q ≠ 0` Rempała's map is surjective: `(S, x)` is the image of `(1, S/q, x, 0)` (θ = 1, ξ = S/q, φ = x)."
  impl NEP.rempalaMap_surjective_preimage

@[sa_forward "MorphismsRempala.rempalaMapSurjective" 1]
theorem fwd1 (h : sa_impl% "MorphismsRempala.rempalaMapSurjective") : S1 := by
  intro σ μ q hq
  exact (h μ q hq).1

@[sa_forward "MorphismsRempala.rempalaMapSurjective" 2]
theorem fwd2 (h : sa_impl% "MorphismsRempala.rempalaMapSurjective") : S2 := by
  intro σ μ q hq S x
  exact (h μ q hq).2 S x

@[sa_backward "MorphismsRempala.rempalaMapSurjective"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "MorphismsRempala.rempalaMapSurjective" := by
  intro σ μ q hq
  exact ⟨s1 μ q hq, s2 μ q hq⟩

end Alignment.Shadows.MorphismsRempala.RempalaMapSurjective

/-! ## `MorphismsRempala.rempalaDSurjective` -/

namespace Alignment.Shadows.MorphismsRempala.RempalaDSurjective

sa_claim "MorphismsRempala.rempalaDSurjective" group "MorphismsRempala" required
  text "For `q ≠ 0` the derivative of Rempała's map is surjective at every point (the map is a submersion)."
  impl NEP.rempalaD_surjective

/-- Bridge (needs independent review): the trusted `rempalaD μ q u` is the text's "the derivative
of Rempała's map", Mathlib's Fréchet derivative. Same statement as
`RempalaQuotient.bridge_rempalaD`, registered for this claim. -/
@[sa_bridge "MorphismsRempala.rempalaDSurjective"]
theorem bridge_rempalaD {σ : Type} (μ q : ℝ) (u : EB σ) :
    rempalaD μ q u = fderiv ℝ (rempalaMap μ q) u :=
  (hasFDerivAt_rempalaMap_any μ q u).fderiv.symm

@[sa_forward "MorphismsRempala.rempalaDSurjective" 1]
theorem fwd1 (h : sa_impl% "MorphismsRempala.rempalaDSurjective") : S1 := by
  intro σ μ q hq u
  rw [← bridge_rempalaD μ q u]
  exact h μ q hq u

@[sa_backward "MorphismsRempala.rempalaDSurjective"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsRempala.rempalaDSurjective" := by
  intro σ μ q hq u
  rw [bridge_rempalaD μ q u]
  exact s1 μ q hq u

end Alignment.Shadows.MorphismsRempala.RempalaDSurjective

/-! ## `MorphismsRempala.rempalaSirProj`

`sa_impl%` is `rempala_sir_proj_field ∧ rempala_sir_proj`. The shadows' field
`(maSys (rempalaRxns μ (sirRxns τ γ))).F v` is definitionally the impl's `maLift … v`. S3/S4 are
the two components of the pointwise identity: `(maSIR β ρ).F (S, I)` unfolds to
`(-β * S * I, β * S * I - ρ * I)` and `sirProj v = (v.1, v.2 I)`, so `congrArg Prod.fst/snd`
gives them with `β = μ * τ`, `ρ = γ + τ` as written. -/

namespace Alignment.Shadows.MorphismsRempala.RempalaSirProj

sa_claim "MorphismsRempala.rempalaSirProj" group "MorphismsRempala" required
  text "`E_μ` of SIR, projected to `(S, x_I)`, is mass-action SIR with `β = μτ` and `ρ = γ + τ`."
  impl NEP.rempala_sir_proj_field NEP.rempala_sir_proj

@[sa_forward "MorphismsRempala.rempalaSirProj" 1]
theorem fwd1 (h : sa_impl% "MorphismsRempala.rempalaSirProj") : S1 := by
  intro μ τ γ v
  exact h.1 μ τ γ v

@[sa_forward "MorphismsRempala.rempalaSirProj" 2]
theorem fwd2 (h : sa_impl% "MorphismsRempala.rempalaSirProj") : S2 := by
  intro μ τ γ
  exact h.2 μ τ γ

@[sa_forward "MorphismsRempala.rempalaSirProj" 3]
theorem fwd3 (h : sa_impl% "MorphismsRempala.rempalaSirProj") : S3 := by
  intro μ τ γ v
  exact congrArg Prod.fst (h.1 μ τ γ v)

@[sa_forward "MorphismsRempala.rempalaSirProj" 4]
theorem fwd4 (h : sa_impl% "MorphismsRempala.rempalaSirProj") : S4 := by
  intro μ τ γ v
  exact congrArg Prod.snd (h.1 μ τ γ v)

@[sa_backward "MorphismsRempala.rempalaSirProj"]
theorem bwd (s1 : S1) (s2 : S2) (_s3 : S3) (_s4 : S4) :
    sa_impl% "MorphismsRempala.rempalaSirProj" := by
  exact And.intro (fun μ τ γ v => s1 μ τ γ v) (fun μ τ γ => s2 μ τ γ)

end Alignment.Shadows.MorphismsRempala.RempalaSirProj
