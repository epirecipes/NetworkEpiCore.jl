import Alignment.Registry
import NetworkEpi.Morphisms.Rempala

/-!
# Blind shadows: group `MorphismsRempala` (module `NetworkEpi.Morphisms.Rempala`)

Written blind from `Alignment/claims_blind.yaml`, `Alignment/DataTypes/MorphismsRempala.md`,
`Alignment/README.md`, `Alignment/Example/ExampleShadows.lean`, `SA-PASS_SKILL.md` and
`DESIGN_NetworkEpiCore.md` (§0, §D.3–§D.6, §J.10).

Vocabulary: Rempała's map `π = rempalaMap μ q : EB σ → MA σ`, the explicit linear map
`rempalaD μ q u`, `E_μ = rempalaRxns μ` (per reaction `Rxn.rempala μ`), the EB model
`ebSys N q P` on `CNet.poisson μ`, the mass-action model `maSys`, and the SIR/SEIR data.

Where the text spells out the design formulas for `π` and `E_μ`, a separate shadow states the
result for the design's explicit objects (`designMap`, `designE`), so that a wrong `rempalaMap`
or `rempalaRxns` falsifies it. "The derivative" of the map is read as `fderiv`.
-/

open NEP

namespace Alignment.Shadows.MorphismsRempala

/-- The design's `π = (θ, ξ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ)`: `S = qξe^{μ(θ−1)}` and `x = φ`
(the node fractions `pop` are forgotten). -/
noncomputable def designMap {σ : Type} (μ q : ℝ) (u : EB σ) : MA σ :=
  (q * u.2.1 * Real.exp (μ * (u.1 - 1)), u.2.2.1)

/-- The added removals of the design's `E_μ`: a contact `s + J → X + J` at `τ` contributes
`J → ∅` at `τ` (on the edge copy); exits and transitions contribute nothing. -/
def designRemoval {σ : Type} : Rxn σ → List (NRxn σ)
  | .contact J _ τ => [NRxn.trans J none τ]
  | .exit _ _ => []
  | .trans _ _ _ => []

/-- The design's `E_μ` of one reaction: `c_μ r` (as T_net syntax) together with its removal.
(DESIGN §D.5 M3 "E_μ P = c_μ P + {J_r → ∅ at τ_r}"; §J.10 exits stay `S → V`.) -/
def designERxn {σ : Type} (μ : ℝ) (r : Rxn σ) : List (NRxn σ) :=
  (Rxn.scaleContacts μ r).toNRxn :: designRemoval r

/-- The design's `E_μ P`, reaction by reaction. -/
def designE {σ : Type} (μ : ℝ) (P : List (Rxn σ)) : List (NRxn σ) :=
  P.flatMap (designERxn μ)

end Alignment.Shadows.MorphismsRempala

/-! ## `MorphismsRempala.rempalaGeneral` -/
namespace Alignment.Shadows.MorphismsRempala.RempalaGeneral
open Alignment.Shadows.MorphismsRempala

/-- For every T_EB list `P`, every `μ ≠ 0` and every `q`, Rempała's map is a global
semiconjugacy `EB_{Pois μ}(P) → MA(E_μ P)`; and the same holds for the design's explicit
`π` and `E_μ` (`x_X = φ_X`, not `pop_X`). -/
@[sa_reference "MorphismsRempala.rempalaGeneral"]
def T : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (P : List (Rxn σ)) (μ q : ℝ), μ ≠ 0 →
    IsSemiconj (ebSys (CNet.poisson μ) q P) (maSys (rempalaRxns μ P)) (rempalaMap μ q) ∧
    IsSemiconj (ebSys (CNet.poisson μ) q P) (maSys (designE μ P)) (designMap μ q)

/-- S1: `rempalaMap μ q` is a global semiconjugacy onto `maSys (rempalaRxns μ P)`. -/
@[sa_shadow "MorphismsRempala.rempalaGeneral" 1]
def S1 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (P : List (Rxn σ)) (μ q : ℝ), μ ≠ 0 →
    IsSemiconj (ebSys (CNet.poisson μ) q P) (maSys (rempalaRxns μ P)) (rempalaMap μ q)

/-- S2: the design's explicit `π = (θ, ξ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ)` is a global
semiconjugacy onto mass action of the design's `E_μ P = c_μ P + {J_r → ∅ at τ_r}`. -/
@[sa_shadow "MorphismsRempala.rempalaGeneral" 2]
def S2 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (P : List (Rxn σ)) (μ q : ℝ), μ ≠ 0 →
    IsSemiconj (ebSys (CNet.poisson μ) q P) (maSys (designE μ P)) (designMap μ q)

@[sa_ref_forward "MorphismsRempala.rempalaGeneral" 1]
theorem ref_fwd1 : T → S1 := by
  intro t σ _ _ P μ q hμ; exact (t P μ q hμ).1
@[sa_ref_forward "MorphismsRempala.rempalaGeneral" 2]
theorem ref_fwd2 : T → S2 := by
  intro t σ _ _ P μ q hμ; exact (t P μ q hμ).2
@[sa_complete "MorphismsRempala.rempalaGeneral"]
theorem complete (s1 : S1) (s2 : S2) : T := by
  intro σ _ _ P μ q hμ; exact ⟨s1 P μ q hμ, s2 P μ q hμ⟩

end Alignment.Shadows.MorphismsRempala.RempalaGeneral

/-! ## `MorphismsRempala.rempalaGeneralSolution`

Text: "EB solutions on any set of times I (for example a time interval) map to MA solutions,
both for derivatives within I and for two-sided derivatives at every time of I. [...] No
condition on `ξ(0)` is needed." Design: "EB_{Pois μ}(P) → MA(E_μ P), E_μ P = c_μ P +
{J_r → ∅ at τ_r} on the edge copies; π = (θ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ)"; §D.3
"semiconjugacies map solution curves to solution curves".

Reading: for every T_EB list `P`, every `μ ≠ 0` (§M.3: Poisson(μ) statements are for μ ≠ 0),
every seed factor `q`, every set `I ⊆ ℝ` (no convexity, no condition on `x 0`) and every EB
solution `x` of `ebSys (CNet.poisson μ) q P` on `I`, the curve `t ↦ π (x t)` is a solution of
`MA(E_μ P)` on `I`. Split: two-sided derivatives (S1, S3) vs derivatives within `I` (S2, S4);
library objects `rempalaMap`/`rempalaRxns` (S1, S2) vs the design's explicit `π`/`E_μ`
(`designMap`/`designE`, S3, S4), so that a `rempalaMap` or `rempalaRxns` that drifts from the
quoted formulas falsifies S3/S4 (through the checker's bridges). -/
namespace Alignment.Shadows.MorphismsRempala.RempalaGeneralSolution
open Alignment.Shadows.MorphismsRempala

/-- Two-sided reading, for a given map `π : EB σ → MA σ` and target list `E : List (NRxn σ)`. -/
def SolAtFor {σ : Type} [DecidableEq σ] [Fintype σ] (P : List (Rxn σ)) (μ q : ℝ)
    (π : EB σ → MA σ) (E : List (NRxn σ)) : Prop :=
  ∀ (I : Set ℝ) (x : ℝ → EB σ),
    (∀ t ∈ I, HasDerivAt x ((ebSys (CNet.poisson μ) q P).F (x t)) t) →
    ∀ t ∈ I, HasDerivAt (fun s => π (x s)) ((maSys E).F (π (x t))) t

/-- Within-`I` reading (one-sided at end points of `I`, any set `I`). -/
def SolWithinFor {σ : Type} [DecidableEq σ] [Fintype σ] (P : List (Rxn σ)) (μ q : ℝ)
    (π : EB σ → MA σ) (E : List (NRxn σ)) : Prop :=
  ∀ (I : Set ℝ) (x : ℝ → EB σ),
    (∀ t ∈ I, HasDerivWithinAt x ((ebSys (CNet.poisson μ) q P).F (x t)) I t) →
    ∀ t ∈ I, HasDerivWithinAt (fun s => π (x s)) ((maSys E).F (π (x t))) I t

@[sa_reference "MorphismsRempala.rempalaGeneralSolution"]
def T : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (P : List (Rxn σ)) (μ q : ℝ), μ ≠ 0 →
    SolAtFor P μ q (rempalaMap μ q) (rempalaRxns μ P) ∧
    SolWithinFor P μ q (rempalaMap μ q) (rempalaRxns μ P) ∧
    SolAtFor P μ q (designMap μ q) (designE μ P) ∧
    SolWithinFor P μ q (designMap μ q) (designE μ P)

/-- S1: every EB solution on any set of times `I` (two-sided derivatives at every `t ∈ I`)
maps under `rempalaMap μ q` to a solution of `maSys (rempalaRxns μ P)` on `I`; any `x 0`. -/
@[sa_shadow "MorphismsRempala.rempalaGeneralSolution" 1]
def S1 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (P : List (Rxn σ)) (μ q : ℝ), μ ≠ 0 →
    SolAtFor P μ q (rempalaMap μ q) (rempalaRxns μ P)

/-- S2: the same for derivatives within `I`. -/
@[sa_shadow "MorphismsRempala.rempalaGeneralSolution" 2]
def S2 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (P : List (Rxn σ)) (μ q : ℝ), μ ≠ 0 →
    SolWithinFor P μ q (rempalaMap μ q) (rempalaRxns μ P)

/-- S3: two-sided reading for the design's explicit `π = (qξe^{μ(θ−1)}, φ)` and
`E_μ P = c_μ P + {J_r → ∅ at τ_r}`. -/
@[sa_shadow "MorphismsRempala.rempalaGeneralSolution" 3]
def S3 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (P : List (Rxn σ)) (μ q : ℝ), μ ≠ 0 →
    SolAtFor P μ q (designMap μ q) (designE μ P)

/-- S4: within-`I` reading for the design's explicit `π` and `E_μ`. -/
@[sa_shadow "MorphismsRempala.rempalaGeneralSolution" 4]
def S4 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (P : List (Rxn σ)) (μ q : ℝ), μ ≠ 0 →
    SolWithinFor P μ q (designMap μ q) (designE μ P)

@[sa_ref_forward "MorphismsRempala.rempalaGeneralSolution" 1]
theorem ref_fwd1 : T → S1 := by
  intro t σ _ _ P μ q hμ; exact (t P μ q hμ).1
@[sa_ref_forward "MorphismsRempala.rempalaGeneralSolution" 2]
theorem ref_fwd2 : T → S2 := by
  intro t σ _ _ P μ q hμ; exact (t P μ q hμ).2.1
@[sa_ref_forward "MorphismsRempala.rempalaGeneralSolution" 3]
theorem ref_fwd3 : T → S3 := by
  intro t σ _ _ P μ q hμ; exact (t P μ q hμ).2.2.1
@[sa_ref_forward "MorphismsRempala.rempalaGeneralSolution" 4]
theorem ref_fwd4 : T → S4 := by
  intro t σ _ _ P μ q hμ; exact (t P μ q hμ).2.2.2
@[sa_complete "MorphismsRempala.rempalaGeneralSolution"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := by
  intro σ _ _ P μ q hμ
  exact ⟨s1 P μ q hμ, s2 P μ q hμ, s3 P μ q hμ, s4 P μ q hμ⟩

end Alignment.Shadows.MorphismsRempala.RempalaGeneralSolution

/-! ## `MorphismsRempala.rempalaNatural`

Text: "this is naturality with respect to the species maps of the syntax (relabelling and
gluing, DESIGN §D.1); it is not stated as a natural transformation of functors into `DynSys`.
[...] `E_μ` commutes with relabelling species, and the map commutes with the pushforward and
pullback of coordinates along species maps." Gluing along a cospan is relabelling along its
legs (DataTypes, `Rxn.map`), so every species map `f : σ → σ'` is covered. Three conjuncts, each
for all species maps `f` and all `μ` (and `q`, and every list / state). -/
namespace Alignment.Shadows.MorphismsRempala.RempalaNatural

/-- `E_μ (relabel f P) = relabel f (E_μ P)` for every T_EB list `P`. -/
def Relabel : Prop :=
  ∀ {σ σ' : Type} (f : σ → σ') (μ : ℝ) (P : List (Rxn σ)),
    rempalaRxns μ (P.map (Rxn.map f)) = (rempalaRxns μ P).map (NRxn.map f)

/-- `π (pushEB f u) = pushMA f (π u)`. -/
def Push : Prop :=
  ∀ {σ σ' : Type} [Fintype σ] [DecidableEq σ'] (f : σ → σ') (μ q : ℝ) (u : EB σ),
    rempalaMap μ q (pushEB f u) = pushMA f (rempalaMap μ q u)

/-- `π (pullEB f u) = pullMA f (π u)`. -/
def Pull : Prop :=
  ∀ {σ σ' : Type} (f : σ → σ') (μ q : ℝ) (u : EB σ'),
    rempalaMap μ q (pullEB f u) = pullMA f (rempalaMap μ q u)

@[sa_reference "MorphismsRempala.rempalaNatural"]
def T : Prop := Relabel ∧ Push ∧ Pull

/-- S1: `E_μ` of a relabelled list is the relabelling of `E_μ` of the list. -/
@[sa_shadow "MorphismsRempala.rempalaNatural" 1]
def S1 : Prop := Relabel
/-- S2: the map commutes with pushforward (fibre sums) of coordinates. -/
@[sa_shadow "MorphismsRempala.rempalaNatural" 2]
def S2 : Prop := Push
/-- S3: the map commutes with pullback (precomposition) of coordinates. -/
@[sa_shadow "MorphismsRempala.rempalaNatural" 3]
def S3 : Prop := Pull

@[sa_ref_forward "MorphismsRempala.rempalaNatural" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "MorphismsRempala.rempalaNatural" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "MorphismsRempala.rempalaNatural" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "MorphismsRempala.rempalaNatural"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.MorphismsRempala.RempalaNatural

/-! ## `MorphismsRempala.rempalaQuotient`

"for `q ≠ 0` the map and its derivative at every point are surjective". -/
namespace Alignment.Shadows.MorphismsRempala.RempalaQuotient

def MapSurj : Prop :=
  ∀ {σ : Type} (μ q : ℝ), q ≠ 0 → Function.Surjective (rempalaMap (σ := σ) μ q)

def DerivSurj : Prop :=
  ∀ {σ : Type} (μ q : ℝ), q ≠ 0 → ∀ u : EB σ,
    Function.Surjective (fderiv ℝ (rempalaMap (σ := σ) μ q) u)

@[sa_reference "MorphismsRempala.rempalaQuotient"]
def T : Prop := MapSurj ∧ DerivSurj

/-- S1: for `q ≠ 0` Rempała's map is surjective. -/
@[sa_shadow "MorphismsRempala.rempalaQuotient" 1]
def S1 : Prop := MapSurj
/-- S2: for `q ≠ 0` its (Fréchet) derivative at every point is surjective. -/
@[sa_shadow "MorphismsRempala.rempalaQuotient" 2]
def S2 : Prop := DerivSurj

@[sa_ref_forward "MorphismsRempala.rempalaQuotient" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "MorphismsRempala.rempalaQuotient" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "MorphismsRempala.rempalaQuotient"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.MorphismsRempala.RempalaQuotient

/-! ## `MorphismsRempala.rempalaGeneralSir`

"for SIR, composing with the projection `(S, x) ↦ (S, x_I)` gives mass-action SIR with
`β = μτ`, `ρ = γ + τ` [...] it holds at every state, not only on `ξ = 1`." The general
quotient assumes `μ ≠ 0`; the design adds "The MA "I" is φ_I, not prevalence". -/
namespace Alignment.Shadows.MorphismsRempala.RempalaGeneralSir
open Alignment.Shadows.MorphismsRempala

@[sa_reference "MorphismsRempala.rempalaGeneralSir"]
def T : Prop :=
  ∀ (μ τ γ q : ℝ), μ ≠ 0 →
    IsSemiconj (ebSys (CNet.poisson μ) q (sirRxns τ γ)) (maSIR (μ * τ) (γ + τ))
        (fun u => sirProj (rempalaMap μ q u)) ∧
    IsSemiconj (ebSys (CNet.poisson μ) q (sirRxns τ γ)) (maSIR (μ * τ) (γ + τ))
        (fun u => (q * u.2.1 * Real.exp (μ * (u.1 - 1)), u.2.2.1 SIRSp.I))

/-- S1: `sirProj ∘ rempalaMap μ q` is a global semiconjugacy from EB SIR on Poisson(μ) (any
`q`, every state) to mass-action SIR with `β = μτ`, `ρ = γ + τ`. -/
@[sa_shadow "MorphismsRempala.rempalaGeneralSir" 1]
def S1 : Prop :=
  ∀ (μ τ γ q : ℝ), μ ≠ 0 →
    IsSemiconj (ebSys (CNet.poisson μ) q (sirRxns τ γ)) (maSIR (μ * τ) (γ + τ))
        (fun u => sirProj (rempalaMap μ q u))

/-- S2: the explicit map `(θ, ξ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ_I)` (the MA `I` is `φ_I`, not
the prevalence `pop_I`) is such a semiconjugacy. -/
@[sa_shadow "MorphismsRempala.rempalaGeneralSir" 2]
def S2 : Prop :=
  ∀ (μ τ γ q : ℝ), μ ≠ 0 →
    IsSemiconj (ebSys (CNet.poisson μ) q (sirRxns τ γ)) (maSIR (μ * τ) (γ + τ))
        (fun u => (q * u.2.1 * Real.exp (μ * (u.1 - 1)), u.2.2.1 SIRSp.I))

@[sa_ref_forward "MorphismsRempala.rempalaGeneralSir" 1]
theorem ref_fwd1 : T → S1 := fun t μ τ γ q h => (t μ τ γ q h).1
@[sa_ref_forward "MorphismsRempala.rempalaGeneralSir" 2]
theorem ref_fwd2 : T → S2 := fun t μ τ γ q h => (t μ τ γ q h).2
@[sa_complete "MorphismsRempala.rempalaGeneralSir"]
theorem complete (s1 : S1) (s2 : S2) : T := fun μ τ γ q h => ⟨s1 μ τ γ q h, s2 μ τ γ q h⟩

end Alignment.Shadows.MorphismsRempala.RempalaGeneralSir

/-! ## `MorphismsRempala.rempalaSeirField`

Text: "Rempała's quotient for SEIR: the mass-action equations of `E_μ(SEIR)` (M3, SEIR)",
with the design's `E_μ P = c_μ P + {J_r → ∅ at τ_r}`. For SEIR (`s + I → E + I` at τ,
`E → I` at `a`, `I → R` at γ) the design's `E_μ(SEIR)` is `S + I → E + I` at `μτ`, `I → ∅` at
τ, `E → I` at `a`, `I → R` at γ, whose mass-action equations (flux `k·Π reactant fractions`)
are `Ṡ = −μτ S x_I`, `ẋ_E = μτ S x_I − a x_E`, `ẋ_I = a x_E − (γ + τ) x_I`, `ẋ_R = γ x_I`.
The field is that of the mass-action model `maSys (rempalaRxns μ (seirRxns τ a γ))`
(MA(E_μ P)). These are equations of syntax, with no network, so they are stated for every
`μ, τ, a, γ` and every state. One shadow per equation. -/
namespace Alignment.Shadows.MorphismsRempala.RempalaSeirField

/-- The vector field of MA(E_μ(SEIR)) at `v`. -/
noncomputable def F (μ τ a γ : ℝ) (v : MA SEIRSp) : MA SEIRSp :=
  (maSys (rempalaRxns μ (seirRxns τ a γ))).F v

def ES : Prop := ∀ (μ τ a γ : ℝ) (v : MA SEIRSp),
  (F μ τ a γ v).1 = -(μ * τ) * v.1 * v.2 SEIRSp.I
def EE : Prop := ∀ (μ τ a γ : ℝ) (v : MA SEIRSp),
  (F μ τ a γ v).2 SEIRSp.E = μ * τ * v.1 * v.2 SEIRSp.I - a * v.2 SEIRSp.E
def EI : Prop := ∀ (μ τ a γ : ℝ) (v : MA SEIRSp),
  (F μ τ a γ v).2 SEIRSp.I = a * v.2 SEIRSp.E - (γ + τ) * v.2 SEIRSp.I
def ER : Prop := ∀ (μ τ a γ : ℝ) (v : MA SEIRSp),
  (F μ τ a γ v).2 SEIRSp.R = γ * v.2 SEIRSp.I

@[sa_reference "MorphismsRempala.rempalaSeirField"]
def T : Prop := ES ∧ EE ∧ EI ∧ ER

/-- S1: `Ṡ = −μτ S x_I`. -/
@[sa_shadow "MorphismsRempala.rempalaSeirField" 1]
def S1 : Prop := ES
/-- S2: `ẋ_E = μτ S x_I − a x_E`. -/
@[sa_shadow "MorphismsRempala.rempalaSeirField" 2]
def S2 : Prop := EE
/-- S3: `ẋ_I = a x_E − (γ + τ) x_I` (removal rate `γ + τ` from I: `J_r → ∅` at τ). -/
@[sa_shadow "MorphismsRempala.rempalaSeirField" 3]
def S3 : Prop := EI
/-- S4: `ẋ_R = γ x_I`. -/
@[sa_shadow "MorphismsRempala.rempalaSeirField" 4]
def S4 : Prop := ER

@[sa_ref_forward "MorphismsRempala.rempalaSeirField" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "MorphismsRempala.rempalaSeirField" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "MorphismsRempala.rempalaSeirField" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "MorphismsRempala.rempalaSeirField" 4]
theorem ref_fwd4 : T → S4 := fun t => t.2.2.2
@[sa_complete "MorphismsRempala.rempalaSeirField"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.MorphismsRempala.RempalaSeirField

/-! ## `MorphismsRempala.rempalaDApply`

"`rempalaD μ q u v = (q (v_ξ e^{μ(θ−1)} + ξ μ e^{μ(θ−1)} v_θ), v_φ)`" with `u = (θ, ξ, φ, pop)`.
One shadow per component. -/
namespace Alignment.Shadows.MorphismsRempala.RempalaDApply

def C1 : Prop := ∀ {σ : Type} (μ q : ℝ) (u v : EB σ),
  (rempalaD μ q u v).1 =
    q * (v.2.1 * Real.exp (μ * (u.1 - 1)) + u.2.1 * μ * Real.exp (μ * (u.1 - 1)) * v.1)
def C2 : Prop := ∀ {σ : Type} (μ q : ℝ) (u v : EB σ), (rempalaD μ q u v).2 = v.2.2.1

@[sa_reference "MorphismsRempala.rempalaDApply"]
def T : Prop := C1 ∧ C2

/-- S1: the `S` component `q (v_ξ e^{μ(θ−1)} + ξ μ e^{μ(θ−1)} v_θ)`. -/
@[sa_shadow "MorphismsRempala.rempalaDApply" 1]
def S1 : Prop := C1
/-- S2: the `x` component is `v_φ`. -/
@[sa_shadow "MorphismsRempala.rempalaDApply" 2]
def S2 : Prop := C2

@[sa_ref_forward "MorphismsRempala.rempalaDApply" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "MorphismsRempala.rempalaDApply" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "MorphismsRempala.rempalaDApply"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.MorphismsRempala.RempalaDApply

/-! ## `MorphismsRempala.hasFDerivAtRempalaMap` -/
namespace Alignment.Shadows.MorphismsRempala.HasFDerivAtRempalaMap

@[sa_reference "MorphismsRempala.hasFDerivAtRempalaMap"]
def T : Prop := ∀ {σ : Type} (μ q : ℝ) (u : EB σ),
  HasFDerivAt (rempalaMap μ q) (rempalaD μ q u) u

/-- S1: `rempalaMap μ q` has Fréchet derivative `rempalaD μ q u` at every `u`. -/
@[sa_shadow "MorphismsRempala.hasFDerivAtRempalaMap" 1]
def S1 : Prop := ∀ {σ : Type} (μ q : ℝ) (u : EB σ),
  HasFDerivAt (rempalaMap μ q) (rempalaD μ q u) u

@[sa_ref_forward "MorphismsRempala.hasFDerivAtRempalaMap" 1]
theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "MorphismsRempala.hasFDerivAtRempalaMap"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MorphismsRempala.HasFDerivAtRempalaMap

/-! ## `MorphismsRempala.rempalaEbField`

"On the Poisson(μ) network with `μ ≠ 0`, the derivative of Rempała's map carries the EB field
of each T_EB reaction `r` to the mass-action field of `E_μ r` at the image point." -/
namespace Alignment.Shadows.MorphismsRempala.RempalaEbField

@[sa_reference "MorphismsRempala.rempalaEbField"]
def T : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (μ q : ℝ), μ ≠ 0 → ∀ (r : Rxn σ) (u : EB σ),
    fderiv ℝ (rempalaMap μ q) u (ebField (CNet.poisson μ) q r u) =
      maLift (Rxn.rempala μ r) (rempalaMap μ q u)

/-- S1: `Dπ(u)·(EB field of r)(u) = (MA field of E_μ r)(π u)` for every T_EB reaction and
state, on Poisson(μ), `μ ≠ 0`, any `q`. -/
@[sa_shadow "MorphismsRempala.rempalaEbField" 1]
def S1 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (μ q : ℝ), μ ≠ 0 → ∀ (r : Rxn σ) (u : EB σ),
    fderiv ℝ (rempalaMap μ q) u (ebField (CNet.poisson μ) q r u) =
      maLift (Rxn.rempala μ r) (rempalaMap μ q u)

@[sa_ref_forward "MorphismsRempala.rempalaEbField" 1]
theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "MorphismsRempala.rempalaEbField"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MorphismsRempala.RempalaEbField

/-! ## `MorphismsRempala.rxnRempalaMap` -/
namespace Alignment.Shadows.MorphismsRempala.RxnRempalaMap

@[sa_reference "MorphismsRempala.rxnRempalaMap"]
def T : Prop := ∀ {σ σ' : Type} (f : σ → σ') (μ : ℝ) (r : Rxn σ),
  Rxn.rempala μ (Rxn.map f r) = (Rxn.rempala μ r).map (NRxn.map f)

/-- S1: `E_μ (relabel f r) = relabel f (E_μ r)` for one reaction. -/
@[sa_shadow "MorphismsRempala.rxnRempalaMap" 1]
def S1 : Prop := ∀ {σ σ' : Type} (f : σ → σ') (μ : ℝ) (r : Rxn σ),
  Rxn.rempala μ (Rxn.map f r) = (Rxn.rempala μ r).map (NRxn.map f)

@[sa_ref_forward "MorphismsRempala.rxnRempalaMap" 1]
theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "MorphismsRempala.rxnRempalaMap"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MorphismsRempala.RxnRempalaMap

/-! ## `MorphismsRempala.rempalaMapPull` -/
namespace Alignment.Shadows.MorphismsRempala.RempalaMapPull

@[sa_reference "MorphismsRempala.rempalaMapPull"]
def T : Prop := ∀ {σ σ' : Type} (f : σ → σ') (μ q θ ξ : ℝ) (φ pop : σ' → ℝ),
  rempalaMap μ q ((θ, ξ, φ ∘ f, pop ∘ f) : EB σ) = pullMA f (rempalaMap μ q ((θ, ξ, φ, pop) : EB σ'))

/-- S1: `π(θ, ξ, φ ∘ f, pop ∘ f) = pullMA f (π(θ, ξ, φ, pop))`. -/
@[sa_shadow "MorphismsRempala.rempalaMapPull" 1]
def S1 : Prop := ∀ {σ σ' : Type} (f : σ → σ') (μ q θ ξ : ℝ) (φ pop : σ' → ℝ),
  rempalaMap μ q ((θ, ξ, φ ∘ f, pop ∘ f) : EB σ) = pullMA f (rempalaMap μ q ((θ, ξ, φ, pop) : EB σ'))

@[sa_ref_forward "MorphismsRempala.rempalaMapPull" 1]
theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "MorphismsRempala.rempalaMapPull"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MorphismsRempala.RempalaMapPull

/-! ## `MorphismsRempala.rempalaMapPush` -/
namespace Alignment.Shadows.MorphismsRempala.RempalaMapPush

@[sa_reference "MorphismsRempala.rempalaMapPush"]
def T : Prop := ∀ {σ σ' : Type} [Fintype σ] [DecidableEq σ'] (f : σ → σ') (μ q : ℝ) (u : EB σ),
  rempalaMap μ q (pushEB f u) = pushMA f (rempalaMap μ q u)

/-- S1: `π(pushEB f u) = pushMA f (π u)`. -/
@[sa_shadow "MorphismsRempala.rempalaMapPush" 1]
def S1 : Prop := ∀ {σ σ' : Type} [Fintype σ] [DecidableEq σ'] (f : σ → σ') (μ q : ℝ) (u : EB σ),
  rempalaMap μ q (pushEB f u) = pushMA f (rempalaMap μ q u)

@[sa_ref_forward "MorphismsRempala.rempalaMapPush" 1]
theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "MorphismsRempala.rempalaMapPush"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MorphismsRempala.RempalaMapPush

/-! ## `MorphismsRempala.rempalaMapSurjective`

"For `q ≠ 0` Rempała's map is surjective: `(S, x)` is the image of `(1, S/q, x, 0)`." -/
namespace Alignment.Shadows.MorphismsRempala.RempalaMapSurjective

def Surj : Prop :=
  ∀ {σ : Type} (μ q : ℝ), q ≠ 0 → Function.Surjective (rempalaMap (σ := σ) μ q)

def Preimage : Prop :=
  ∀ {σ : Type} (μ q : ℝ), q ≠ 0 → ∀ (S : ℝ) (x : σ → ℝ),
    rempalaMap μ q ((1, S / q, x, 0) : EB σ) = (S, x)

@[sa_reference "MorphismsRempala.rempalaMapSurjective"]
def T : Prop := Surj ∧ Preimage

/-- S1: for `q ≠ 0` Rempała's map is surjective. -/
@[sa_shadow "MorphismsRempala.rempalaMapSurjective" 1]
def S1 : Prop := Surj
/-- S2: for `q ≠ 0`, `π(1, S/q, x, 0) = (S, x)`. -/
@[sa_shadow "MorphismsRempala.rempalaMapSurjective" 2]
def S2 : Prop := Preimage

@[sa_ref_forward "MorphismsRempala.rempalaMapSurjective" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "MorphismsRempala.rempalaMapSurjective" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "MorphismsRempala.rempalaMapSurjective"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.MorphismsRempala.RempalaMapSurjective

/-! ## `MorphismsRempala.rempalaDSurjective`

"For `q ≠ 0` the derivative of Rempała's map is surjective at every point (the map is a
submersion)." The derivative is read as `fderiv`. -/
namespace Alignment.Shadows.MorphismsRempala.RempalaDSurjective

@[sa_reference "MorphismsRempala.rempalaDSurjective"]
def T : Prop :=
  ∀ {σ : Type} (μ q : ℝ), q ≠ 0 → ∀ u : EB σ,
    Function.Surjective (fderiv ℝ (rempalaMap (σ := σ) μ q) u)

/-- S1: for `q ≠ 0`, `fderiv ℝ (rempalaMap μ q) u` is surjective for every `u`. -/
@[sa_shadow "MorphismsRempala.rempalaDSurjective" 1]
def S1 : Prop :=
  ∀ {σ : Type} (μ q : ℝ), q ≠ 0 → ∀ u : EB σ,
    Function.Surjective (fderiv ℝ (rempalaMap (σ := σ) μ q) u)

@[sa_ref_forward "MorphismsRempala.rempalaDSurjective" 1]
theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "MorphismsRempala.rempalaDSurjective"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MorphismsRempala.RempalaDSurjective

/-! ## `MorphismsRempala.rempalaSirProj`

Text: "`E_μ` of SIR, projected to `(S, x_I)`, is mass-action SIR with `β = μτ` and
`ρ = γ + τ`." (`maSIR β ρ`: `Ṡ = −βSI`, `İ = βSI − ρI`.) Readings, all for every `μ, τ, γ`
(syntax only, no network):
* S1: the projected MA(E_μ SIR) field equals the `maSIR (μτ) (γ + τ)` field at the projected
  point;
* S2: the projection `(S, x) ↦ (S, x_I)` is a semiconjugacy `MA(E_μ SIR) → maSIR (μτ) (γ + τ)`;
* S3, S4: in primitive terms, the `S` and `x_I` components of the MA(E_μ SIR) field are
  `−μτ S x_I` and `μτ S x_I − (γ + τ) x_I` (so the projection really is onto `(S, x_I)` and the
  rates really are `β = μτ`, `ρ = γ + τ`). -/
namespace Alignment.Shadows.MorphismsRempala.RempalaSirProj

/-- The vector field of MA(E_μ(SIR)) at `v`. -/
noncomputable def F (μ τ γ : ℝ) (v : MA SIRSp) : MA SIRSp :=
  (maSys (rempalaRxns μ (sirRxns τ γ))).F v

def FieldEq : Prop := ∀ (μ τ γ : ℝ) (v : MA SIRSp),
  sirProj (F μ τ γ v) = (maSIR (μ * τ) (γ + τ)).F (sirProj v)

def Semi : Prop := ∀ (μ τ γ : ℝ),
  IsSemiconj (maSys (rempalaRxns μ (sirRxns τ γ))) (maSIR (μ * τ) (γ + τ)) sirProj

def CompS : Prop := ∀ (μ τ γ : ℝ) (v : MA SIRSp),
  (F μ τ γ v).1 = -(μ * τ) * v.1 * v.2 SIRSp.I

def CompI : Prop := ∀ (μ τ γ : ℝ) (v : MA SIRSp),
  (F μ τ γ v).2 SIRSp.I = μ * τ * v.1 * v.2 SIRSp.I - (γ + τ) * v.2 SIRSp.I

@[sa_reference "MorphismsRempala.rempalaSirProj"]
def T : Prop := FieldEq ∧ Semi ∧ CompS ∧ CompI

/-- S1: projecting the mass-action field of `E_μ(SIR)` to `(S, x_I)` gives the field of
mass-action SIR with `β = μτ`, `ρ = γ + τ` at the projected point. -/
@[sa_shadow "MorphismsRempala.rempalaSirProj" 1]
def S1 : Prop := FieldEq
/-- S2: the projection `(S, x) ↦ (S, x_I)` is a semiconjugacy from `MA(E_μ SIR)` to
mass-action SIR with `β = μτ`, `ρ = γ + τ`. -/
@[sa_shadow "MorphismsRempala.rempalaSirProj" 2]
def S2 : Prop := Semi
/-- S3: the `S` component of the MA(E_μ SIR) field is `−μτ S x_I`. -/
@[sa_shadow "MorphismsRempala.rempalaSirProj" 3]
def S3 : Prop := CompS
/-- S4: the `x_I` component of the MA(E_μ SIR) field is `μτ S x_I − (γ + τ) x_I`. -/
@[sa_shadow "MorphismsRempala.rempalaSirProj" 4]
def S4 : Prop := CompI

@[sa_ref_forward "MorphismsRempala.rempalaSirProj" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "MorphismsRempala.rempalaSirProj" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "MorphismsRempala.rempalaSirProj" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "MorphismsRempala.rempalaSirProj" 4]
theorem ref_fwd4 : T → S4 := fun t => t.2.2.2
@[sa_complete "MorphismsRempala.rempalaSirProj"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.MorphismsRempala.RempalaSirProj
