import Alignment.Registry
import NetworkEpi.Semantics.PoissonSIR
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Blind shadow sets: group `SemanticsPoissonSIR`

Written blind (SA-PASS role 2). Sources read: `SA-PASS_SKILL.md`, `Alignment/README.md`,
`Alignment/Example/ExampleShadows.lean`, `Alignment/DataTypes/SemanticsPoissonSIR.md`, the entries of
the claims below in `Alignment/claims_blind.yaml`, and `DESIGN_NetworkEpiCore.md` (§0, §D.3–§D.7,
§J–§L). No trusted source file, theorem statement, definition body, checker or report was read.
Re-verified blind (second pass) against the regenerated `claims_blind.yaml` entries and DESIGN
§D.3, §D.5 M3, §D.7 L4c, §J.2 with the same reading set; the shadow statements are unchanged.
Re-shadowed blind (third pass, after text remediation) for `hasFDerivAtPoisMap`, `rempala`,
`contDiffPoisMap`, `rempalaLift` and `rempalaSolution`, from the regenerated `claims_blind.yaml`
entries and DESIGN §D.3, §D.5 M3, §J.2 and the binding amendments §M.3 and §M.5; same reading set.

Shared conventions (DESIGN §0, §D.3, §D.5 M3, §J.2):
* Rempała's map is `π = (θ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ)`; in the two SIR coordinates `(θ, φ_I)` of
  `ebPoisSIR` (ξ ≡ 1 there) it is `(θ, φ_I) ↦ (q e^{μ(θ−1)}, φ_I)`. "The MA "I" is φ_I, not
  prevalence": the second MA coordinate is `φ_I`. The shadows write this map out explicitly
  (`remMap`, `remXi`, `remXiOne`) rather than through the trusted `poisMap`, so that the checker has
  to show (by unfolding or a reviewed bridge) that the trusted map is the text's map.
* "For SIR: MA(β = μτ, γ_MA = γ + τ)" is the target `maSIR (μ * τ) (γ + τ)`.
* A (local) semiconjugacy `π : (V, F) → (W, G)` on `U` is written in primitive terms, as in the
  fields of `Semiconj` / `SemiconjOn`: `π` is differentiable at every `u ∈ U` and
  `fderiv ℝ π u (F u) = G (π u)` for every `u ∈ U`. The pair identity is split into its two
  coordinate rows (each shadow also carries the differentiability requirement, so that every
  shadow mentions the trusted vector fields; a bare "the explicit map is differentiable" shadow
  would be trusted-free).
* A solution on a time interval (DESIGN §J.2: "EB solutions are taken on a time interval I ∋ 0
  (`HasDerivWithinAt` on a convex I)") is a curve `x` with
  `∀ t ∈ I, HasDerivWithinAt x (F (x t)) I t`, for `I` convex with `0 ∈ I`.
* The design's category **Dyn** (§D.3): objects `(V, F)` with `V` finite-dimensional and `F` C¹;
  morphisms are C¹ semiconjugacies (`IsDynObject` below; see DataTypes (d)).
-/

open NEP

namespace Alignment.Shadows.SemanticsPoissonSIR

/-- Rempała's map in the SIR coordinates `(θ, φ_I)`, from the text:
`(θ, φ_I) ↦ (q e^{μ(θ−1)}, φ_I)` (DESIGN §D.5 M3 with ξ ≡ 1; the MA "I" is `φ_I`). -/
noncomputable def remMap (μ q : ℝ) (u : ℝ × ℝ) : ℝ × ℝ :=
  (q * Real.exp (μ * (u.1 - 1)), u.2)

/-- The text's derivative of Rempała's map at `u = (θ, φ)`:
`(dθ, dφ) ↦ (qμe^{μ(θ−1)} dθ, dφ)`. -/
noncomputable def remDeriv (μ q : ℝ) (u : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  ((q * μ * Real.exp (μ * (u.1 - 1))) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (ContinuousLinearMap.snd ℝ ℝ ℝ)

/-- The chart `(θ, ξ, φ, pop) ↦ (θ, φ_I)` on EB coordinates over `SIRSp`, from the text. -/
def chartThetaPhiI (u : EB SIRSp) : ℝ × ℝ :=
  (u.1, u.2.2.1 SIRSp.I)

/-- The design's M3 map on general EB coordinates, SIR case, literally:
`(θ, ξ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ_I)` (the MA "I" is `φ_I`). -/
noncomputable def remXi (μ q : ℝ) (u : EB SIRSp) : ℝ × ℝ :=
  (q * u.2.1 * Real.exp (μ * (u.1 - 1)), u.2.2.1 SIRSp.I)

/-- The design's M3 map with `ξ` set to its value `1` on the slice `{ξ = 1}`:
`(θ, ξ, φ, pop) ↦ (q e^{μ(θ−1)}, φ_I)`. -/
noncomputable def remXiOne (μ q : ℝ) (u : EB SIRSp) : ℝ × ℝ :=
  (q * Real.exp (μ * (u.1 - 1)), u.2.2.1 SIRSp.I)

/-- An object of the design's category **Dyn** (DESIGN §D.3): the state space is
finite-dimensional and the vector field is C¹. -/
def IsDynObject (A : DynSys) : Prop :=
  FiniteDimensional ℝ A.V ∧ ContDiff ℝ 1 A.F

end Alignment.Shadows.SemanticsPoissonSIR

/-! ## `SemanticsPoissonSIR.hasFDerivAtPoisMap`

Blind text (re-shadowed after text remediation; the text is unchanged): "The derivative of
Rempała's map: `Dπ(θ, φ)(dθ, dφ) = (qμe^{μ(θ−1)} dθ, dφ)`."

Data types used: `poisMap μ q` (Rempała's map `(θ, φ_I) ↦ (q e^{μ(θ−1)}, φ_I)`). The text gives no
restriction on `μ`, `q` or the point, so every parameter and every point `(θ, φ)` is quantified.
The derivative is the Fréchet derivative (`HasFDerivAt`) with the explicit linear map `remDeriv`
(`(dθ, dφ) ↦ (qμe^{μ(θ−1)} dθ, dφ)`). The statement is one derivative claim (an equality of linear
maps would be split only through library facts), so there is one shadow. -/

namespace Alignment.Shadows.SemanticsPoissonSIR.HasFDerivAtPoisMap

open Alignment.Shadows.SemanticsPoissonSIR

/-- Intended statement: for all `μ, q` and every point `u = (θ, φ)`, Rempała's map has Fréchet
derivative `(dθ, dφ) ↦ (qμe^{μ(θ−1)} dθ, dφ)` at `u`. -/
@[sa_reference "SemanticsPoissonSIR.hasFDerivAtPoisMap"]
def T : Prop :=
  ∀ μ q : ℝ, ∀ u : ℝ × ℝ, HasFDerivAt (poisMap μ q) (remDeriv μ q u) u

/-- S1: the derivative of `poisMap μ q` at `(θ, φ)` is `(dθ, dφ) ↦ (qμe^{μ(θ−1)} dθ, dφ)`. -/
@[sa_shadow "SemanticsPoissonSIR.hasFDerivAtPoisMap" 1]
def S1 : Prop :=
  ∀ μ q θ φ : ℝ, HasFDerivAt (poisMap μ q) (remDeriv μ q (θ, φ)) (θ, φ)

@[sa_ref_forward "SemanticsPoissonSIR.hasFDerivAtPoisMap" 1]
theorem ref_fwd1 : T → S1 := fun t μ q θ φ => t μ q (θ, φ)

@[sa_complete "SemanticsPoissonSIR.hasFDerivAtPoisMap"]
theorem complete (s1 : S1) : T := fun μ q u => s1 μ q u.1 u.2

end Alignment.Shadows.SemanticsPoissonSIR.HasFDerivAtPoisMap

/-! ## `SemanticsPoissonSIR.rempala`

Blind text (remediated): "**Rempała's theorem for SIR as a semiconjugacy (M3, SIR case).** Design
statement (DESIGN_NetworkEpiCore.md §D.5, M3): "**Rempała quotient** ("back to mass action on the
same species") | EB_{Pois μ}(P) → MA(E_μ P), E_μ P = c_μ P + {J_r → ∅ at τ_r} on the edge copies;
π = (θ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ). For SIR: MA(β = μτ, γ_MA = γ + τ). **The MA "I" is φ_I, not
prevalence** | natural semiconjugacy (surjective submersion) | **[L]** `NEP.rempala` (SIR)".
[...]
The design's "surjective submersion" holds for `μ ≠ 0` and `q > 0`, onto the mass-action states
with `S > 0` (`rempala_quotient_sir`); it fails for `μ = 0` or `q = 0`."

Data types used: `ebPoisSIR μ τ γ q` (EB SIR on Poisson(μ) in `(θ, φ_I)`, ξ ≡ 1), `maSIR β ρ`, and
`poisMap μ q` ("Rempała's map"). DESIGN §D.7 (L4c) names the SIR object; §M.3 (binding amendment)
is the source of the last sentence.

Readings.
* The semiconjugacy (S1, S2): for all `μ, τ, γ, q`, the text's map `π(θ, φ_I) = (q e^{μ(θ−1)}, φ_I)`
  (written out, `remMap`) is differentiable and carries the EB field to the MA field with `β = μτ`,
  `γ_MA = γ + τ`; split into the S row (S1) and the I row (S2, "the MA I is φ_I").
  AMBIGUITY: §M.3 says "The Poisson(μ) statements are for μ ≠ 0", but this claim's text restricts
  only the surjective-submersion part; the two-dimensional SIR identity involves no division by
  `ψ'(1) = μ`, so the semiconjugacy is read for every `μ` (a `μ ≠ 0` hypothesis on it would show up
  as a failing forward check).
* "The design's "surjective submersion" holds for μ ≠ 0 and q > 0, onto the mass-action states
  with S > 0": S3, Rempała's map is a submersion (`Dπ(u)` surjective at every `u`) for `μ ≠ 0`,
  `q > 0`; S4, it is onto `{(S, I) | S > 0}` for `μ ≠ 0`, `q > 0`.
* "it fails for μ = 0 or q = 0": the negation of the surjective submersion onto `{S > 0}`, split
  along the "or": S5 (`μ = 0`, every `q`), S6 (`q = 0`, every `μ`). "Fails" is read as the negation
  of the conjunction (submersion everywhere ∧ onto `{S > 0}`); it is not strengthened to the
  failure of each part separately.
* "natural" (in `P`) is empty for the single model SIR and is not formalised.
S3–S6 are stated for the trusted `poisMap` (the text's "Rempała's map"); a statement about the
explicit formula alone would be trusted-free. -/

namespace Alignment.Shadows.SemanticsPoissonSIR.Rempala

open Alignment.Shadows.SemanticsPoissonSIR

/-- The design's "surjective submersion onto the mass-action states with `S > 0`" for Rempała's
map `poisMap μ q`: its derivative is surjective at every point, and every `(S, I)` with `S > 0`
is an image point. -/
def SurjSubmersionPos (μ q : ℝ) : Prop :=
  (∀ u : ℝ × ℝ, Function.Surjective (fderiv ℝ (poisMap μ q) u)) ∧
    (∀ S I : ℝ, 0 < S → ∃ u : ℝ × ℝ, poisMap μ q u = (S, I))

/-- Intended statement: (i) for all `μ, τ, γ, q`, the map `(θ, φ_I) ↦ (q e^{μ(θ−1)}, φ_I)` is a
semiconjugacy from `ebPoisSIR μ τ γ q` to `maSIR (μτ) (γ + τ)`; (ii) for `μ ≠ 0`, `q > 0`,
Rempała's map is a submersion and (iii) onto `{S > 0}`; (iv) the surjective submersion onto
`{S > 0}` fails for `μ = 0` or `q = 0`. -/
@[sa_reference "SemanticsPoissonSIR.rempala"]
def T : Prop :=
  (∀ μ τ γ q : ℝ, Differentiable ℝ (remMap μ q) ∧
    ∀ u : ℝ × ℝ,
      fderiv ℝ (remMap μ q) u ((ebPoisSIR μ τ γ q).F u) =
        (maSIR (μ * τ) (γ + τ)).F (remMap μ q u)) ∧
  (∀ μ q : ℝ, μ ≠ 0 → 0 < q → ∀ u : ℝ × ℝ, Function.Surjective (fderiv ℝ (poisMap μ q) u)) ∧
  (∀ μ q : ℝ, μ ≠ 0 → 0 < q → ∀ S I : ℝ, 0 < S → ∃ u : ℝ × ℝ, poisMap μ q u = (S, I)) ∧
  (∀ μ q : ℝ, μ = 0 ∨ q = 0 → ¬ SurjSubmersionPos μ q)

/-- S1 (semiconjugacy, S row): `π` is differentiable at `u` and the S coordinate of `Dπ(u)·F(u)`
equals that of `G(π(u))`, i.e. `Ṡ = −(μτ) S φ_I` with `S = q e^{μ(θ−1)}`. -/
@[sa_shadow "SemanticsPoissonSIR.rempala" 1]
def S1 : Prop :=
  ∀ μ τ γ q : ℝ, ∀ u : ℝ × ℝ,
    DifferentiableAt ℝ (remMap μ q) u ∧
      (fderiv ℝ (remMap μ q) u ((ebPoisSIR μ τ γ q).F u)).1 =
        Prod.fst (α := ℝ) (β := ℝ) ((maSIR (μ * τ) (γ + τ)).F (remMap μ q u))

/-- S2 (semiconjugacy, I row; "the MA I is φ_I"): `π` is differentiable at `u` and the I
coordinate of `Dπ(u)·F(u)` equals that of `G(π(u))`, i.e. `φ̇_I = μτ S φ_I − (γ + τ) φ_I`. -/
@[sa_shadow "SemanticsPoissonSIR.rempala" 2]
def S2 : Prop :=
  ∀ μ τ γ q : ℝ, ∀ u : ℝ × ℝ,
    DifferentiableAt ℝ (remMap μ q) u ∧
      (fderiv ℝ (remMap μ q) u ((ebPoisSIR μ τ γ q).F u)).2 =
        Prod.snd (α := ℝ) (β := ℝ) ((maSIR (μ * τ) (γ + τ)).F (remMap μ q u))

/-- S3 (submersion): for `μ ≠ 0` and `q > 0`, the derivative of Rempała's map is surjective at
every point. -/
@[sa_shadow "SemanticsPoissonSIR.rempala" 3]
def S3 : Prop :=
  ∀ μ q : ℝ, μ ≠ 0 → 0 < q → ∀ u : ℝ × ℝ, Function.Surjective (fderiv ℝ (poisMap μ q) u)

/-- S4 (surjective onto `S > 0`): for `μ ≠ 0` and `q > 0`, every mass-action state `(S, I)` with
`S > 0` is the image of an EB state. -/
@[sa_shadow "SemanticsPoissonSIR.rempala" 4]
def S4 : Prop :=
  ∀ μ q : ℝ, μ ≠ 0 → 0 < q → ∀ S I : ℝ, 0 < S → ∃ u : ℝ × ℝ, poisMap μ q u = (S, I)

/-- S5 ("it fails for μ = 0"): for `μ = 0` and every `q`, Rempała's map is not a surjective
submersion onto `{S > 0}`. -/
@[sa_shadow "SemanticsPoissonSIR.rempala" 5]
def S5 : Prop :=
  ∀ q : ℝ,
    ¬ ((∀ u : ℝ × ℝ, Function.Surjective (fderiv ℝ (poisMap 0 q) u)) ∧
      (∀ S I : ℝ, 0 < S → ∃ u : ℝ × ℝ, poisMap 0 q u = (S, I)))

/-- S6 ("it fails for q = 0"): for `q = 0` and every `μ`, Rempała's map is not a surjective
submersion onto `{S > 0}`. -/
@[sa_shadow "SemanticsPoissonSIR.rempala" 6]
def S6 : Prop :=
  ∀ μ : ℝ,
    ¬ ((∀ u : ℝ × ℝ, Function.Surjective (fderiv ℝ (poisMap μ 0) u)) ∧
      (∀ S I : ℝ, 0 < S → ∃ u : ℝ × ℝ, poisMap μ 0 u = (S, I)))

@[sa_ref_forward "SemanticsPoissonSIR.rempala" 1]
theorem ref_fwd1 : T → S1 := fun t μ τ γ q u =>
  ⟨(t.1 μ τ γ q).1 u, congrArg Prod.fst ((t.1 μ τ γ q).2 u)⟩

@[sa_ref_forward "SemanticsPoissonSIR.rempala" 2]
theorem ref_fwd2 : T → S2 := fun t μ τ γ q u =>
  ⟨(t.1 μ τ γ q).1 u, congrArg Prod.snd ((t.1 μ τ γ q).2 u)⟩

@[sa_ref_forward "SemanticsPoissonSIR.rempala" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.1

@[sa_ref_forward "SemanticsPoissonSIR.rempala" 4]
theorem ref_fwd4 : T → S4 := fun t => t.2.2.1

@[sa_ref_forward "SemanticsPoissonSIR.rempala" 5]
theorem ref_fwd5 : T → S5 := fun t q => t.2.2.2 0 q (Or.inl rfl)

@[sa_ref_forward "SemanticsPoissonSIR.rempala" 6]
theorem ref_fwd6 : T → S6 := fun t μ => t.2.2.2 μ 0 (Or.inr rfl)

@[sa_complete "SemanticsPoissonSIR.rempala"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) : T := by
  refine ⟨fun μ τ γ q => ⟨fun u => (s1 μ τ γ q u).1,
      fun u => Prod.ext (s1 μ τ γ q u).2 (s2 μ τ γ q u).2⟩, s3, s4, ?_⟩
  rintro μ q (rfl | rfl)
  · exact s5 q
  · exact s6 μ

end Alignment.Shadows.SemanticsPoissonSIR.Rempala

/-! ## `SemanticsPoissonSIR.contDiffPoisMap`

Blind text (re-shadowed after text remediation; the text is unchanged): "Rempała's map is C^∞, so
`rempalaHom` is also a morphism of the design's category **Dyn** (whose morphisms are C¹)."

Data types used: `poisMap μ q` (Rempała's map), `rempalaHom μ τ γ q : ebPoisSIR μ τ γ q ⟶
maSIR (μ * τ) (γ + τ)` (a `Semiconj`, with underlying map `.π`), `ebPoisSIR`, `maSIR`. DESIGN §D.3:
"Objects of **Dyn** are (V, F): V a finite-dimensional real normed space, F: V → V a C¹ vector
field. Morphisms (V, F) → (W, G) are C¹ maps π with Dπ(u)·F(u) = G(π(u))". DataTypes (d): a claim
about Dyn is phrased with `DynSys` plus `FiniteDimensional ℝ A.V` / `ContDiff ℝ 1` conditions.

Split: S1 "Rempała's map is C^∞" (`ContDiff ℝ ∞`, `∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`, not `ω`, for all
`μ, q`: the text gives no restriction); "rempalaHom is a morphism of Dyn": the semiconjugacy
identity is already part of `rempalaHom : Semiconj`, and the extra Dyn requirements are S2 (its map
is C¹, the parenthetical "whose morphisms are C¹") and S3/S4 (its source and target are Dyn
objects, presupposed by "a morphism of Dyn").
AMBIGUITY: "so rempalaHom is also a morphism of Dyn" may be read as a remark rather than part of the
claim; it is kept because it is in the claim text, and it is split off (S2–S4) from S1. -/

namespace Alignment.Shadows.SemanticsPoissonSIR.ContDiffPoisMap

open Alignment.Shadows.SemanticsPoissonSIR

/-- Intended statement: Rempała's map is C^∞ for all `μ, q`, and every `rempalaHom μ τ γ q` is a
morphism of Dyn (C¹ map between Dyn objects). -/
@[sa_reference "SemanticsPoissonSIR.contDiffPoisMap"]
def T : Prop :=
  (∀ μ q : ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (poisMap μ q)) ∧
  (∀ μ τ γ q : ℝ, ContDiff ℝ 1 (Semiconj.π (rempalaHom μ τ γ q))) ∧
  (∀ μ τ γ q : ℝ, IsDynObject (ebPoisSIR μ τ γ q)) ∧
  (∀ μ τ γ : ℝ, IsDynObject (maSIR (μ * τ) (γ + τ)))

/-- S1: Rempała's map is C^∞ (smooth, `ContDiff ℝ ∞`) for all `μ, q`. -/
@[sa_shadow "SemanticsPoissonSIR.contDiffPoisMap" 1]
def S1 : Prop :=
  ∀ μ q : ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (poisMap μ q)

/-- S2: the underlying map of the morphism `rempalaHom μ τ γ q` is C¹ (a Dyn morphism map). -/
@[sa_shadow "SemanticsPoissonSIR.contDiffPoisMap" 2]
def S2 : Prop :=
  ∀ μ τ γ q : ℝ, ContDiff ℝ 1 (Semiconj.π (rempalaHom μ τ γ q))

/-- S3: the source `ebPoisSIR μ τ γ q` of `rempalaHom` is a Dyn object. -/
@[sa_shadow "SemanticsPoissonSIR.contDiffPoisMap" 3]
def S3 : Prop :=
  ∀ μ τ γ q : ℝ, IsDynObject (ebPoisSIR μ τ γ q)

/-- S4: the target `maSIR (μτ) (γ + τ)` of `rempalaHom` is a Dyn object. -/
@[sa_shadow "SemanticsPoissonSIR.contDiffPoisMap" 4]
def S4 : Prop :=
  ∀ μ τ γ : ℝ, IsDynObject (maSIR (μ * τ) (γ + τ))

@[sa_ref_forward "SemanticsPoissonSIR.contDiffPoisMap" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "SemanticsPoissonSIR.contDiffPoisMap" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1

@[sa_ref_forward "SemanticsPoissonSIR.contDiffPoisMap" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2.1

@[sa_ref_forward "SemanticsPoissonSIR.contDiffPoisMap" 4]
theorem ref_fwd4 : T → S4 := fun t => t.2.2.2

@[sa_complete "SemanticsPoissonSIR.contDiffPoisMap"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.SemanticsPoissonSIR.ContDiffPoisMap

/-! ## `SemanticsPoissonSIR.poissonHasDerivAtPsi`

Blind text: "On the Poisson network, `ψ'` is the derivative of `ψ` everywhere."

Data types used: `CNet.poisson μ` with fields `ψ`, `ψ'` (independent fields; the relation must be
stated). "The Poisson network": every `μ`; "everywhere": every `x : ℝ`. Atomic: one shadow. -/

namespace Alignment.Shadows.SemanticsPoissonSIR.PoissonHasDerivAtPsi

/-- Intended statement: for every `μ` and every `x`, `ψ` of `CNet.poisson μ` has derivative
`ψ' x` at `x`. -/
@[sa_reference "SemanticsPoissonSIR.poissonHasDerivAtPsi"]
def T : Prop := ∀ μ x : ℝ, HasDerivAt (CNet.poisson μ).ψ ((CNet.poisson μ).ψ' x) x

/-- S1: on every Poisson network, at every point, `ψ' x` is the derivative of `ψ`. -/
@[sa_shadow "SemanticsPoissonSIR.poissonHasDerivAtPsi" 1]
def S1 : Prop := ∀ μ x : ℝ, HasDerivAt (CNet.poisson μ).ψ ((CNet.poisson μ).ψ' x) x

@[sa_ref_forward "SemanticsPoissonSIR.poissonHasDerivAtPsi" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "SemanticsPoissonSIR.poissonHasDerivAtPsi"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SemanticsPoissonSIR.PoissonHasDerivAtPsi

/-! ## `SemanticsPoissonSIR.poissonHasDerivAtPsiPrime`

Blind text: "On the Poisson network, `ψ''` is the derivative of `ψ'` everywhere."

Data types used: `CNet.poisson μ` with fields `ψ'`, `ψ''`. Every `μ`, every `x`. One shadow. -/

namespace Alignment.Shadows.SemanticsPoissonSIR.PoissonHasDerivAtPsiPrime

/-- Intended statement: for every `μ` and every `x`, `ψ'` of `CNet.poisson μ` has derivative
`ψ'' x` at `x`. -/
@[sa_reference "SemanticsPoissonSIR.poissonHasDerivAtPsiPrime"]
def T : Prop := ∀ μ x : ℝ, HasDerivAt (CNet.poisson μ).ψ' ((CNet.poisson μ).ψ'' x) x

/-- S1: on every Poisson network, at every point, `ψ'' x` is the derivative of `ψ'`. -/
@[sa_shadow "SemanticsPoissonSIR.poissonHasDerivAtPsiPrime" 1]
def S1 : Prop := ∀ μ x : ℝ, HasDerivAt (CNet.poisson μ).ψ' ((CNet.poisson μ).ψ'' x) x

@[sa_ref_forward "SemanticsPoissonSIR.poissonHasDerivAtPsiPrime" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "SemanticsPoissonSIR.poissonHasDerivAtPsiPrime"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SemanticsPoissonSIR.PoissonHasDerivAtPsiPrime

/-! ## `SemanticsPoissonSIR.sirChartLApply`

Blind text: "`sirChartL` is `sirChart`."

Data types used: `sirChart : EB SIRSp → ℝ × ℝ`, `sirChartL : EB SIRSp →L[ℝ] ℝ × ℝ`. "Is": the
continuous linear map, applied to any EB state, gives the value of `sirChart`. The pair equality is
split into its two coordinates. -/

namespace Alignment.Shadows.SemanticsPoissonSIR.SirChartLApply

/-- Intended statement: `sirChartL u = sirChart u` for every EB state `u`. -/
@[sa_reference "SemanticsPoissonSIR.sirChartLApply"]
def T : Prop := ∀ u : EB SIRSp, sirChartL u = sirChart u

/-- S1: first coordinates agree. -/
@[sa_shadow "SemanticsPoissonSIR.sirChartLApply" 1]
def S1 : Prop := ∀ u : EB SIRSp, (sirChartL u).1 = (sirChart u).1

/-- S2: second coordinates agree. -/
@[sa_shadow "SemanticsPoissonSIR.sirChartLApply" 2]
def S2 : Prop := ∀ u : EB SIRSp, (sirChartL u).2 = (sirChart u).2

@[sa_ref_forward "SemanticsPoissonSIR.sirChartLApply" 1]
theorem ref_fwd1 : T → S1 := fun t u => congrArg Prod.fst (t u)

@[sa_ref_forward "SemanticsPoissonSIR.sirChartLApply" 2]
theorem ref_fwd2 : T → S2 := fun t u => congrArg Prod.snd (t u)

@[sa_complete "SemanticsPoissonSIR.sirChartLApply"]
theorem complete (s1 : S1) (s2 : S2) : T := fun u => Prod.ext (s1 u) (s2 u)

end Alignment.Shadows.SemanticsPoissonSIR.SirChartLApply

/-! ## `SemanticsPoissonSIR.ebPoisSIRLift`

Blind text: "**`ebPoisSIR` is the SIR EBCM of the general lift.** For `μ ≠ 0`, the chart
`(θ, ξ, φ, pop) ↦ (θ, φ_I)` is a local semiconjugacy on `{ξ = 1}` from the general EB model
`ebSys (CNet.poisson μ) q (sirRxns τ γ)` (the per-reaction lift of `s + I → I + I` at τ and
`I → R` at γ on a Poisson(μ) network) to `ebPoisSIR μ τ γ q`."

Data types used: `ebSys`, `CNet.poisson`, `sirRxns`, `ebPoisSIR`, EB coordinates
`u = (θ, ξ, φ, pop)` with `ξ = u.2.1`, `φ = u.2.2.1`. The chart is written out from the text
(`chartThetaPhiI`). "Local semiconjugacy on U" (DataTypes, `IsSemiconjOn`): differentiable at every
point of `U` and `Dπ(u)·F(u) = G(π(u))` for `u ∈ U`; `U = {u | u.2.1 = 1}`. All `τ, γ, q`, and
`μ ≠ 0` as the text says. Split into the θ row (S1) and the φ_I row (S2). -/

namespace Alignment.Shadows.SemanticsPoissonSIR.EbPoisSIRLift

open Alignment.Shadows.SemanticsPoissonSIR

/-- Intended statement: for `μ ≠ 0` and all `τ, γ, q`, the chart `(θ, ξ, φ, pop) ↦ (θ, φ_I)` is
differentiable at every `u` with `ξ = 1` and carries the general EB SIR field on Poisson(μ) to the
field of `ebPoisSIR μ τ γ q` there. -/
@[sa_reference "SemanticsPoissonSIR.ebPoisSIRLift"]
def T : Prop :=
  ∀ μ τ γ q : ℝ, μ ≠ 0 → ∀ u : EB SIRSp, u.2.1 = 1 →
    DifferentiableAt ℝ chartThetaPhiI u ∧
      fderiv ℝ chartThetaPhiI u ((ebSys (CNet.poisson μ) q (sirRxns τ γ)).F u) =
        (ebPoisSIR μ τ γ q).F (chartThetaPhiI u)

/-- S1 (θ row): on `{ξ = 1}`, for `μ ≠ 0`, the chart is differentiable and the θ coordinate of
`Dπ(u)·F(u)` equals the θ coordinate of the `ebPoisSIR` field at `π(u)`. -/
@[sa_shadow "SemanticsPoissonSIR.ebPoisSIRLift" 1]
def S1 : Prop :=
  ∀ μ τ γ q : ℝ, μ ≠ 0 → ∀ u : EB SIRSp, u.2.1 = 1 →
    DifferentiableAt ℝ chartThetaPhiI u ∧
      (fderiv ℝ chartThetaPhiI u ((ebSys (CNet.poisson μ) q (sirRxns τ γ)).F u)).1 =
        Prod.fst (α := ℝ) (β := ℝ) ((ebPoisSIR μ τ γ q).F (chartThetaPhiI u))

/-- S2 (φ_I row): on `{ξ = 1}`, for `μ ≠ 0`, the chart is differentiable and the φ_I coordinate of
`Dπ(u)·F(u)` equals the φ_I coordinate of the `ebPoisSIR` field at `π(u)`. -/
@[sa_shadow "SemanticsPoissonSIR.ebPoisSIRLift" 2]
def S2 : Prop :=
  ∀ μ τ γ q : ℝ, μ ≠ 0 → ∀ u : EB SIRSp, u.2.1 = 1 →
    DifferentiableAt ℝ chartThetaPhiI u ∧
      (fderiv ℝ chartThetaPhiI u ((ebSys (CNet.poisson μ) q (sirRxns τ γ)).F u)).2 =
        Prod.snd (α := ℝ) (β := ℝ) ((ebPoisSIR μ τ γ q).F (chartThetaPhiI u))

@[sa_ref_forward "SemanticsPoissonSIR.ebPoisSIRLift" 1]
theorem ref_fwd1 : T → S1 := fun t μ τ γ q hμ u hu =>
  ⟨(t μ τ γ q hμ u hu).1, congrArg Prod.fst (t μ τ γ q hμ u hu).2⟩

@[sa_ref_forward "SemanticsPoissonSIR.ebPoisSIRLift" 2]
theorem ref_fwd2 : T → S2 := fun t μ τ γ q hμ u hu =>
  ⟨(t μ τ γ q hμ u hu).1, congrArg Prod.snd (t μ τ γ q hμ u hu).2⟩

@[sa_complete "SemanticsPoissonSIR.ebPoisSIRLift"]
theorem complete (s1 : S1) (s2 : S2) : T := fun μ τ γ q hμ u hu =>
  ⟨(s1 μ τ γ q hμ u hu).1, Prod.ext (s1 μ τ γ q hμ u hu).2 (s2 μ τ γ q hμ u hu).2⟩

end Alignment.Shadows.SemanticsPoissonSIR.EbPoisSIRLift

/-! ## `SemanticsPoissonSIR.rempalaLift`

Blind text (remediated; source `NetworkEpi/Morphisms/Rempala.lean`): "**Rempała's quotient from the
general SIR lift, with the design's map `(qξe^{μ(θ−1)}, φ_I)`, for `μ ≠ 0` (M3, SIR case).** Design
statement (DESIGN_NetworkEpiCore.md §D.5, M3): "EB_{Pois μ}(P) → MA(E_μ P), E_μ P = c_μ P +
{J_r → ∅ at τ_r} on the edge copies; π = (θ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ). For SIR: MA(β = μτ,
γ_MA = γ + τ). **The MA "I" is φ_I, not prevalence**". [...] On the slice `ξ = 1` the map is
`(q e^{μ(θ−1)}, φ_I)` (`NEP.rempala_lift`)."

Data types used: source `ebSys (CNet.poisson μ) q (sirRxns τ γ)` ("the general SIR lift" on
Poisson(μ), state space `EB SIRSp`); target `maSIR (μ * τ) (γ + τ)` ("For SIR: MA(β = μτ,
γ_MA = γ + τ)", coordinates `(S, I)` with I = φ_I); the design's map written out, `remXi μ q u =
(qξe^{μ(θ−1)}, φ_I)`. Parameters: `μ ≠ 0` as the text says ("for μ ≠ 0"; §M.3), all `τ, γ, q`.

Readings.
* Main sentence (S1, S2): for `μ ≠ 0`, the design's map `(qξe^{μ(θ−1)}, φ_I)` is a (global)
  semiconjugacy from the general SIR lift to `maSIR (μτ) (γ + τ)`: differentiable at every EB state
  `u` and `Dπ(u)·F(u) = G(π(u))` for every `u` (no slice condition: the title restricts only `μ`).
  Split into the S row (S1) and the I row (S2, "the MA I is φ_I").
* AMBIGUITY (the slice sentence): "On the slice ξ = 1 the map is (q e^{μ(θ−1)}, φ_I)
  (NEP.rempala_lift)". Read literally it is the arithmetic identity `qξe^{μ(θ−1)} = q e^{μ(θ−1)}`
  at `ξ = 1`, which mentions no trusted notion. The cited `rempala_lift` is, per the module header
  (`header.portScope`: "`rempala_lift` composes the two maps"), the slice version of the quotient,
  so the sentence is read as: for `μ ≠ 0`, the map `(q e^{μ(θ−1)}, φ_I)` (`remXiOne`) is a local
  semiconjugacy on `{ξ = 1}` from the general SIR lift to `maSIR (μτ) (γ + τ)` (S3 S row, S4 I row).
* AMBIGUITY (the target): "MA(E_μ P)" could also be the general mass-action model
  `maSys (rempalaRxns μ (sirRxns τ γ))` with map `rempalaMap μ q`; the claim's "with the design's
  map (qξe^{μ(θ−1)}, φ_I)" (a map to the pair `(S, φ_I)`) and "For SIR: MA(β = μτ, γ_MA = γ + τ)"
  name the two-dimensional mass-action SIR `maSIR (μτ) (γ + τ)`, which is the reading formalised.
* "quotient" is the name of the M3 row ("Rempała quotient"); the quoted design statement stops
  before the Kind column, and the text gives no parameter range for a surjective submersion, so no
  surjectivity requirement is added here (the `rempala` claim carries it). -/

namespace Alignment.Shadows.SemanticsPoissonSIR.RempalaLift

open Alignment.Shadows.SemanticsPoissonSIR

/-- Intended statement: for `μ ≠ 0` and all `τ, γ, q`, (i) the design's map `(qξe^{μ(θ−1)}, φ_I)`
is a semiconjugacy from the general SIR lift on Poisson(μ) to `maSIR (μτ) (γ + τ)`; (ii) on the
slice `{ξ = 1}` the map `(q e^{μ(θ−1)}, φ_I)` is a local semiconjugacy between the same models. -/
@[sa_reference "SemanticsPoissonSIR.rempalaLift"]
def T : Prop :=
  (∀ μ τ γ q : ℝ, μ ≠ 0 → ∀ u : EB SIRSp,
    DifferentiableAt ℝ (remXi μ q) u ∧
      fderiv ℝ (remXi μ q) u ((ebSys (CNet.poisson μ) q (sirRxns τ γ)).F u) =
        (maSIR (μ * τ) (γ + τ)).F (remXi μ q u)) ∧
  (∀ μ τ γ q : ℝ, μ ≠ 0 → ∀ u : EB SIRSp, u.2.1 = 1 →
    DifferentiableAt ℝ (remXiOne μ q) u ∧
      fderiv ℝ (remXiOne μ q) u ((ebSys (CNet.poisson μ) q (sirRxns τ γ)).F u) =
        (maSIR (μ * τ) (γ + τ)).F (remXiOne μ q u))

/-- S1 (design's map, S row): for `μ ≠ 0`, at every EB state the map `(qξe^{μ(θ−1)}, φ_I)` is
differentiable and the S row of `Dπ(u)·F(u) = G(π(u))` holds. -/
@[sa_shadow "SemanticsPoissonSIR.rempalaLift" 1]
def S1 : Prop :=
  ∀ μ τ γ q : ℝ, μ ≠ 0 → ∀ u : EB SIRSp,
    DifferentiableAt ℝ (remXi μ q) u ∧
      (fderiv ℝ (remXi μ q) u ((ebSys (CNet.poisson μ) q (sirRxns τ γ)).F u)).1 =
        Prod.fst (α := ℝ) (β := ℝ) ((maSIR (μ * τ) (γ + τ)).F (remXi μ q u))

/-- S2 (design's map, I row; "the MA I is φ_I"): for `μ ≠ 0`, at every EB state the map
`(qξe^{μ(θ−1)}, φ_I)` is differentiable and the I row of `Dπ(u)·F(u) = G(π(u))` holds. -/
@[sa_shadow "SemanticsPoissonSIR.rempalaLift" 2]
def S2 : Prop :=
  ∀ μ τ γ q : ℝ, μ ≠ 0 → ∀ u : EB SIRSp,
    DifferentiableAt ℝ (remXi μ q) u ∧
      (fderiv ℝ (remXi μ q) u ((ebSys (CNet.poisson μ) q (sirRxns τ γ)).F u)).2 =
        Prod.snd (α := ℝ) (β := ℝ) ((maSIR (μ * τ) (γ + τ)).F (remXi μ q u))

/-- S3 (slice map, S row): for `μ ≠ 0`, on `{ξ = 1}` the map `(q e^{μ(θ−1)}, φ_I)` is
differentiable and the S row of `Dπ(u)·F(u) = G(π(u))` holds. -/
@[sa_shadow "SemanticsPoissonSIR.rempalaLift" 3]
def S3 : Prop :=
  ∀ μ τ γ q : ℝ, μ ≠ 0 → ∀ u : EB SIRSp, u.2.1 = 1 →
    DifferentiableAt ℝ (remXiOne μ q) u ∧
      (fderiv ℝ (remXiOne μ q) u ((ebSys (CNet.poisson μ) q (sirRxns τ γ)).F u)).1 =
        Prod.fst (α := ℝ) (β := ℝ) ((maSIR (μ * τ) (γ + τ)).F (remXiOne μ q u))

/-- S4 (slice map, I row): for `μ ≠ 0`, on `{ξ = 1}` the map `(q e^{μ(θ−1)}, φ_I)` is
differentiable and the I row of `Dπ(u)·F(u) = G(π(u))` holds. -/
@[sa_shadow "SemanticsPoissonSIR.rempalaLift" 4]
def S4 : Prop :=
  ∀ μ τ γ q : ℝ, μ ≠ 0 → ∀ u : EB SIRSp, u.2.1 = 1 →
    DifferentiableAt ℝ (remXiOne μ q) u ∧
      (fderiv ℝ (remXiOne μ q) u ((ebSys (CNet.poisson μ) q (sirRxns τ γ)).F u)).2 =
        Prod.snd (α := ℝ) (β := ℝ) ((maSIR (μ * τ) (γ + τ)).F (remXiOne μ q u))

@[sa_ref_forward "SemanticsPoissonSIR.rempalaLift" 1]
theorem ref_fwd1 : T → S1 := fun t μ τ γ q hμ u =>
  ⟨(t.1 μ τ γ q hμ u).1, congrArg Prod.fst (t.1 μ τ γ q hμ u).2⟩

@[sa_ref_forward "SemanticsPoissonSIR.rempalaLift" 2]
theorem ref_fwd2 : T → S2 := fun t μ τ γ q hμ u =>
  ⟨(t.1 μ τ γ q hμ u).1, congrArg Prod.snd (t.1 μ τ γ q hμ u).2⟩

@[sa_ref_forward "SemanticsPoissonSIR.rempalaLift" 3]
theorem ref_fwd3 : T → S3 := fun t μ τ γ q hμ u hu =>
  ⟨(t.2 μ τ γ q hμ u hu).1, congrArg Prod.fst (t.2 μ τ γ q hμ u hu).2⟩

@[sa_ref_forward "SemanticsPoissonSIR.rempalaLift" 4]
theorem ref_fwd4 : T → S4 := fun t μ τ γ q hμ u hu =>
  ⟨(t.2 μ τ γ q hμ u hu).1, congrArg Prod.snd (t.2 μ τ γ q hμ u hu).2⟩

@[sa_complete "SemanticsPoissonSIR.rempalaLift"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T :=
  ⟨fun μ τ γ q hμ u =>
      ⟨(s1 μ τ γ q hμ u).1, Prod.ext (s1 μ τ γ q hμ u).2 (s2 μ τ γ q hμ u).2⟩,
    fun μ τ γ q hμ u hu =>
      ⟨(s3 μ τ γ q hμ u hu).1, Prod.ext (s3 μ τ γ q hμ u hu).2 (s4 μ τ γ q hμ u hu).2⟩⟩

end Alignment.Shadows.SemanticsPoissonSIR.RempalaLift

/-! ## `SemanticsPoissonSIR.rempalaSolution`

Blind text (remediated; source `NetworkEpi/Morphisms/Rempala.lean`): "**Rempała's theorem on
trajectories with the design's map `(qξe^{μ(θ−1)}, φ_I)`, for `μ ≠ 0` (M3, SIR).** Design statement
(DESIGN_NetworkEpiCore.md §D.5, M3): "EB_{Pois μ}(P) → MA(E_μ P) [...] π = (θ, φ, pop) ↦
(qξe^{μ(θ−1)}, φ). For SIR: MA(β = μτ, γ_MA = γ + τ). **The MA "I" is φ_I, not prevalence**"; §D.3:
"semiconjugacies map solution curves to solution curves". [...] No condition on `ξ(0)` is needed."

Data types used: the general SIR lift `ebSys (CNet.poisson μ) q (sirRxns τ γ)` on `EB SIRSp` (the
map involves ξ, so the EB model is the one with the ξ coordinate, `EB_{Pois μ}(SIR)`),
`maSIR (μ * τ) (γ + τ)`, and the design's map written out (`remXi`). `μ ≠ 0` as the text says; all
`τ, γ, q`.

Solutions. There is no solution predicate; a solution on a set of times `I` is a curve `x` with
`∀ t ∈ I, HasDerivWithinAt x (F (x t)) I t` (DESIGN §J.2: "EB solutions are taken on a time interval
I ∋ 0 (`HasDerivWithinAt` on a convex I)"). The binding amendment §M.5 says ""Solutions are
mapped" is proved on any set of times I", so the shadows quantify over every set `I` (no convexity,
no `0 ∈ I`) and ask the image curve to solve the MA model on the same `I`.
AMBIGUITY (derivative form): §M.5 mentions both two-sided derivatives at every `t ∈ I` and
derivatives within `I`; this claim's text names neither, and the design's standing convention
(§J.2) is `HasDerivWithinAt`, which is the form formalised.

Split along "No condition on ξ(0) is needed": S1 for solutions with `ξ(0) = 1` (the design's initial
condition), S2 for solutions with `ξ(0) ≠ 1`. An implementation that assumes the design's `ξ(0) = 1`
passes S1 and fails S2. (The image curve is not split into coordinates: splitting a
`HasDerivWithinAt` of a pair is a library fact, not a structural step.) -/

namespace Alignment.Shadows.SemanticsPoissonSIR.RempalaSolution

open Alignment.Shadows.SemanticsPoissonSIR

/-- Intended statement: for `μ ≠ 0`, all `τ, γ, q`, every set of times `I` and every solution `x`
of the general SIR lift on Poisson(μ) on `I` (any `ξ(0)`), the curve
`t ↦ (qξ(t)e^{μ(θ(t)−1)}, φ_I(t))` is a solution of `maSIR (μτ) (γ + τ)` on `I`. -/
@[sa_reference "SemanticsPoissonSIR.rempalaSolution"]
def T : Prop :=
  ∀ μ τ γ q : ℝ, μ ≠ 0 → ∀ I : Set ℝ, ∀ x : ℝ → EB SIRSp,
    (∀ t ∈ I, HasDerivWithinAt x ((ebSys (CNet.poisson μ) q (sirRxns τ γ)).F (x t)) I t) →
      ∀ t ∈ I, HasDerivWithinAt (fun s => remXi μ q (x s))
        ((maSIR (μ * τ) (γ + τ)).F (remXi μ q (x t))) I t

/-- S1 (solutions from `ξ(0) = 1`): for `μ ≠ 0`, every solution of the general SIR lift on a set
of times `I` with `ξ(0) = 1` is mapped by `(qξe^{μ(θ−1)}, φ_I)` to a solution of mass-action SIR
with `β = μτ`, `γ_MA = γ + τ` on `I`. -/
@[sa_shadow "SemanticsPoissonSIR.rempalaSolution" 1]
def S1 : Prop :=
  ∀ μ τ γ q : ℝ, μ ≠ 0 → ∀ I : Set ℝ, ∀ x : ℝ → EB SIRSp, (x 0).2.1 = 1 →
    (∀ t ∈ I, HasDerivWithinAt x ((ebSys (CNet.poisson μ) q (sirRxns τ γ)).F (x t)) I t) →
      ∀ t ∈ I, HasDerivWithinAt (fun s => remXi μ q (x s))
        ((maSIR (μ * τ) (γ + τ)).F (remXi μ q (x t))) I t

/-- S2 (solutions from `ξ(0) ≠ 1`; "No condition on ξ(0) is needed"): the same for solutions with
`ξ(0) ≠ 1`. -/
@[sa_shadow "SemanticsPoissonSIR.rempalaSolution" 2]
def S2 : Prop :=
  ∀ μ τ γ q : ℝ, μ ≠ 0 → ∀ I : Set ℝ, ∀ x : ℝ → EB SIRSp, (x 0).2.1 ≠ 1 →
    (∀ t ∈ I, HasDerivWithinAt x ((ebSys (CNet.poisson μ) q (sirRxns τ γ)).F (x t)) I t) →
      ∀ t ∈ I, HasDerivWithinAt (fun s => remXi μ q (x s))
        ((maSIR (μ * τ) (γ + τ)).F (remXi μ q (x t))) I t

@[sa_ref_forward "SemanticsPoissonSIR.rempalaSolution" 1]
theorem ref_fwd1 : T → S1 := fun t μ τ γ q hμ I x _ => t μ τ γ q hμ I x

@[sa_ref_forward "SemanticsPoissonSIR.rempalaSolution" 2]
theorem ref_fwd2 : T → S2 := fun t μ τ γ q hμ I x _ => t μ τ γ q hμ I x

@[sa_complete "SemanticsPoissonSIR.rempalaSolution"]
theorem complete (s1 : S1) (s2 : S2) : T := by
  intro μ τ γ q hμ I x hx
  by_cases h0 : (x 0).2.1 = 1
  · exact s1 μ τ γ q hμ I x h0 hx
  · exact s2 μ τ γ q hμ I x h0 hx

end Alignment.Shadows.SemanticsPoissonSIR.RempalaSolution
