import Alignment.Registry
import NetworkEpi.Semantics.Solutions

/-!
# Blind shadow sets: group `SemanticsSolutions`

Blind shadow author. Files read (and nothing else from the project):
`SA-PASS_SKILL.md`, `Alignment/README.md`, `Alignment/Example/ExampleShadows.lean`,
`Alignment/DataTypes/SemanticsSolutions.md`, the `SemanticsSolutions.*` entries of
`Alignment/claims_blind.yaml` (regenerated with `scripts/sa_merge_claims.py`; the twelve assigned
ids plus the module-header entries `header.hypothesesMet`, `header.bullets`, used as spec prose),
`DESIGN_NetworkEpiCore.md` (§0, §D.1–§D.7, §J, §K, §L), and Mathlib sources
(`Mathlib/Analysis/Calculus/ContDiff/{Defs,FTaylorSeries}.lean`, for the `ContDiffAt` index type
`WithTop ℕ∞` and `ω = ⊤`).

Re-shadow after text remediation (blind; blocks `ebFieldContactEq`, `ebFieldRemoveEq`,
`ebFieldProgressEq`, `contDiffLift`, `conservationLocal`, `conservationLocalPoisson`,
`seirConservationLocal` replaced). Files read: `SA-PASS_SKILL.md`, `Alignment/README.md`,
`Alignment/Example/ExampleShadows.lean`, `Alignment/DataTypes/SemanticsSolutions.md`, the
`SemanticsSolutions.*` entries of `Alignment/claims_blind.yaml` (regenerated with
`scripts/sa_pass.sh --no-build`), `DESIGN_NetworkEpiCore.md` (§0, §D.3, §D.4, §J, §K, §L, §M), and
this file's previous version (itself blind).

Conventions used throughout (DESIGN §0, §D.4, DataTypes):
* a state `u : EB σ` is `(θ, ξ, φ, pop) = (u.1, u.2.1, u.2.2.1, u.2.2.2)`;
* `S = qξψ(θ)` and `φ_S = qξψ'(θ)/ψ'(1)` are written in primitive terms
  (`q * ξ * N.ψ θ` and `q * ξ * N.ψ' θ / N.ψ' 1`), never through `CNet.susc` / `CNet.phiS`;
* `Pi.single X c` is the species vector with `c` at `X` and `0` elsewhere; the "+=" contributions
  of DESIGN §D.4 to two species are added, so they accumulate when the species coincide;
* "`C^n`" is Mathlib's `ContDiffAt ℝ n` with `n : WithTop ℕ∞`. Each `C^n` claim is split into the
  finite-or-∞ levels `n : ℕ∞` (classical `C^n`) and the analytic level `ω = ⊤`.
  AMBIGUITY: "`C^n`" — classically `n ≤ ∞`; in Mathlib the index also includes `ω`. The split
  isolates the `ω` reading in its own shadow;
* "a solution on (−ε, ε)" of the EB field of `rs` is
  `∀ t ∈ Set.Ioo (-ε) ε, HasDerivWithinAt x (lift N q rs (x t)) (Set.Ioo (-ε) ε) t`
  (DESIGN §J.2: "EB solutions are taken on a time interval I ∋ 0 (`HasDerivWithinAt` on a convex
  I)"; DataTypes: "spells out `∀ t ∈ I, HasDerivWithinAt x (lift N q rs (x t)) I t`").
  `existsLocalSolution` says `HasDerivAt` explicitly and uses it;
* "removal-free" is "no reaction of the form `trans X none a`" (`X → ∅`);
* "θ = φ_S + Σ_X φ_X" at a state `u` is `u.1 = q * u.2.1 * N.ψ' u.1 / N.ψ' 1 + ∑ X, u.2.2.1 X`.
-/

open NEP

/-! ## `SemanticsSolutions.contDiffAtPiSingle`

Blind text: "`Pi.single Y` applied to a `C^n` function is `C^n` (a `fun_prop` rule)."

The text is about a Mathlib operation only (no NetworkEpi notion), so every shadow here is
necessarily trusted-free (`shadow_trusted_free`); the text is itself a calculus fact.
AMBIGUITY: "a `C^n` function is `C^n`" — globally, or at a point. Read pointwise (the
`fun_prop` form, a `C^n`-at-`x` function composed with `Pi.single Y` is `C^n` at `x`); the global
form follows from it. The codomain is the species vectors `σ → ℝ` (`σ` finite), the domain an
arbitrary real normed space `E`. -/
namespace Alignment.Shadows.SemanticsSolutions.ContDiffAtPiSingle

/-- Intended statement: for every finite species type `σ`, species `Y`, real normed space `E`,
`f : E → ℝ`, point `x` and smoothness level `n`: if `f` is `C^n` at `x` then so is
`y ↦ Pi.single Y (f y)`. -/
@[sa_reference "SemanticsSolutions.contDiffAtPiSingle"]
def T : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (Y : σ)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (x : E) (n : WithTop ℕ∞),
    ContDiffAt ℝ n f x → ContDiffAt ℝ n (fun y => (Pi.single Y (f y) : σ → ℝ)) x

/-- S1: the rule at every finite-or-∞ level `n : ℕ∞`. -/
@[sa_shadow "SemanticsSolutions.contDiffAtPiSingle" 1]
def S1 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (Y : σ)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (x : E) (n : ℕ∞),
    ContDiffAt ℝ (n : WithTop ℕ∞) f x →
      ContDiffAt ℝ (n : WithTop ℕ∞) (fun y => (Pi.single Y (f y) : σ → ℝ)) x

/-- S2: the rule at the analytic level `ω = ⊤`. -/
@[sa_shadow "SemanticsSolutions.contDiffAtPiSingle" 2]
def S2 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (Y : σ)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (x : E),
    ContDiffAt ℝ (⊤ : WithTop ℕ∞) f x →
      ContDiffAt ℝ (⊤ : WithTop ℕ∞) (fun y => (Pi.single Y (f y) : σ → ℝ)) x

@[sa_ref_forward "SemanticsSolutions.contDiffAtPiSingle" 1]
theorem ref_fwd1 : T → S1 := by
  intro t σ _ _ Y E _ _ f x n h
  exact t Y f x (n : WithTop ℕ∞) h

@[sa_ref_forward "SemanticsSolutions.contDiffAtPiSingle" 2]
theorem ref_fwd2 : T → S2 := by
  intro t σ _ _ Y E _ _ f x h
  exact t Y f x ⊤ h

@[sa_complete "SemanticsSolutions.contDiffAtPiSingle"]
theorem complete (s1 : S1) (s2 : S2) : T := by
  intro σ _ _ Y E _ _ f x n h
  induction n using WithTop.recTopCoe with
  | top => exact s2 Y f x h
  | coe m => exact s1 Y f x m h

end Alignment.Shadows.SemanticsSolutions.ContDiffAtPiSingle

/-! ## `SemanticsSolutions.ebFieldContactEq` (re-shadowed after text remediation)

Blind text: "The EB field of a contact `s + J → X + J`, written with the coordinate projections."

Source of the field: DESIGN §D.4, contact row, `r = (s + J → X + J, τ_r)`:
`θ̇ += −τ_r φ_J`, `φ̇_J += −τ_r φ_J`, `φ̇_X += +τ_r φ_J · qξψ''(θ)/ψ'(1)`,
`pop_X' += +τ_r φ_J · qξψ'(θ)` (the `cum` accumulator is not an `EB σ` coordinate). `ξ̇` collects
exits only (§D.4 notation `ξ̇ = −(Σ_e ν_e)ξ`), so a contact contributes `0` to `ξ`. "Written with the
coordinate projections": the identity holds at every state `u`, whose coordinates are the
projections `θ = u.1`, `ξ = u.2.1`, `φ = u.2.2.1`, `pop = u.2.2.2`. The two `φ` contributions
("+=" at `J` and at `X`) are added, so they accumulate when `J = X`. One shadow per coordinate. -/
namespace Alignment.Shadows.SemanticsSolutions.EbFieldContactEq

/-- Intended statement: for every species type, network data `N`, seed factor `q`, contact
`contact J X τ` and state `u`, the EB field is
`(−τφ_J, 0, −τφ_J·e_J + τφ_J·(qξψ''(θ)/ψ'(1))·e_X, τφ_J·(qξψ'(θ))·e_X)`. -/
@[sa_reference "SemanticsSolutions.ebFieldContactEq"]
def T : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (J X : σ) (τ : ℝ) (u : EB σ),
    ebField N q (Rxn.contact J X τ) u =
      (-(τ * u.2.2.1 J),
       0,
       Pi.single J (-(τ * u.2.2.1 J)) +
         Pi.single X (τ * u.2.2.1 J * (q * u.2.1 * N.ψ'' u.1 / N.ψ' 1)),
       Pi.single X (τ * u.2.2.1 J * (q * u.2.1 * N.ψ' u.1)))

/-- S1: `θ̇ = −τφ_J`. -/
@[sa_shadow "SemanticsSolutions.ebFieldContactEq" 1]
def S1 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (J X : σ) (τ : ℝ) (u : EB σ),
    (ebField N q (Rxn.contact J X τ) u).1 = -(τ * u.2.2.1 J)

/-- S2: a contact does not move the exit factor, `ξ̇ = 0`. -/
@[sa_shadow "SemanticsSolutions.ebFieldContactEq" 2]
def S2 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (J X : σ) (τ : ℝ) (u : EB σ),
    (ebField N q (Rxn.contact J X τ) u).2.1 = 0

/-- S3: `φ̇ = −τφ_J` at `J` plus `τφ_J·qξψ''(θ)/ψ'(1)` at `X`, `0` elsewhere. -/
@[sa_shadow "SemanticsSolutions.ebFieldContactEq" 3]
def S3 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (J X : σ) (τ : ℝ) (u : EB σ),
    (ebField N q (Rxn.contact J X τ) u).2.2.1 =
      Pi.single J (-(τ * u.2.2.1 J)) +
        Pi.single X (τ * u.2.2.1 J * (q * u.2.1 * N.ψ'' u.1 / N.ψ' 1))

/-- S4: `pop' = τφ_J·qξψ'(θ)` at `X`, `0` elsewhere. -/
@[sa_shadow "SemanticsSolutions.ebFieldContactEq" 4]
def S4 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (J X : σ) (τ : ℝ) (u : EB σ),
    (ebField N q (Rxn.contact J X τ) u).2.2.2 =
      Pi.single X (τ * u.2.2.1 J * (q * u.2.1 * N.ψ' u.1))

@[sa_ref_forward "SemanticsSolutions.ebFieldContactEq" 1]
theorem ref_fwd1 : T → S1 := by
  intro t σ _ N q J X τ u
  rw [t N q J X τ u]

@[sa_ref_forward "SemanticsSolutions.ebFieldContactEq" 2]
theorem ref_fwd2 : T → S2 := by
  intro t σ _ N q J X τ u
  rw [t N q J X τ u]

@[sa_ref_forward "SemanticsSolutions.ebFieldContactEq" 3]
theorem ref_fwd3 : T → S3 := by
  intro t σ _ N q J X τ u
  rw [t N q J X τ u]

@[sa_ref_forward "SemanticsSolutions.ebFieldContactEq" 4]
theorem ref_fwd4 : T → S4 := by
  intro t σ _ N q J X τ u
  rw [t N q J X τ u]

@[sa_complete "SemanticsSolutions.ebFieldContactEq"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := by
  intro σ _ N q J X τ u
  exact Prod.ext (s1 N q J X τ u) (Prod.ext (s2 N q J X τ u)
    (Prod.ext (s3 N q J X τ u) (s4 N q J X τ u)))

end Alignment.Shadows.SemanticsSolutions.EbFieldContactEq

/-! ## `SemanticsSolutions.ebFieldExitEq`

Blind text: "The EB field of an exit `s → Y`, written with the coordinate projections."

DESIGN §D.4, exit row: `ξ̇ += −νξ`, `φ̇_Y += νφ_S`, `pop_Y' += νS`, with `S = qξψ(θ)` and
`φ_S = qξψ'(θ)/ψ'(1)` (DESIGN §0); an exit does not touch `θ`. -/
namespace Alignment.Shadows.SemanticsSolutions.EbFieldExitEq

/-- Intended statement: the EB field of `exit Y ν` at `u = (θ, ξ, φ, pop)` is
`(0, −νξ, ν·(qξψ'(θ)/ψ'(1))·e_Y, ν·(qξψ(θ))·e_Y)`. -/
@[sa_reference "SemanticsSolutions.ebFieldExitEq"]
def T : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (Y : σ) (ν : ℝ) (u : EB σ),
    ebField N q (Rxn.exit Y ν) u =
      (0,
       -(ν * u.2.1),
       Pi.single Y (ν * (q * u.2.1 * N.ψ' u.1 / N.ψ' 1)),
       Pi.single Y (ν * (q * u.2.1 * N.ψ u.1)))

/-- S1: an exit leaves `θ` unchanged. -/
@[sa_shadow "SemanticsSolutions.ebFieldExitEq" 1]
def S1 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (Y : σ) (ν : ℝ) (u : EB σ),
    (ebField N q (Rxn.exit Y ν) u).1 = 0

/-- S2: `ξ̇ = −νξ`. -/
@[sa_shadow "SemanticsSolutions.ebFieldExitEq" 2]
def S2 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (Y : σ) (ν : ℝ) (u : EB σ),
    (ebField N q (Rxn.exit Y ν) u).2.1 = -(ν * u.2.1)

/-- S3: `φ̇ = νφ_S` at `Y`, `0` elsewhere. -/
@[sa_shadow "SemanticsSolutions.ebFieldExitEq" 3]
def S3 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (Y : σ) (ν : ℝ) (u : EB σ),
    (ebField N q (Rxn.exit Y ν) u).2.2.1 = Pi.single Y (ν * (q * u.2.1 * N.ψ' u.1 / N.ψ' 1))

/-- S4: `pop' = νS` at `Y`, `0` elsewhere. -/
@[sa_shadow "SemanticsSolutions.ebFieldExitEq" 4]
def S4 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (Y : σ) (ν : ℝ) (u : EB σ),
    (ebField N q (Rxn.exit Y ν) u).2.2.2 = Pi.single Y (ν * (q * u.2.1 * N.ψ u.1))

@[sa_ref_forward "SemanticsSolutions.ebFieldExitEq" 1]
theorem ref_fwd1 : T → S1 := by
  intro t σ _ N q Y ν u
  rw [t N q Y ν u]

@[sa_ref_forward "SemanticsSolutions.ebFieldExitEq" 2]
theorem ref_fwd2 : T → S2 := by
  intro t σ _ N q Y ν u
  rw [t N q Y ν u]

@[sa_ref_forward "SemanticsSolutions.ebFieldExitEq" 3]
theorem ref_fwd3 : T → S3 := by
  intro t σ _ N q Y ν u
  rw [t N q Y ν u]

@[sa_ref_forward "SemanticsSolutions.ebFieldExitEq" 4]
theorem ref_fwd4 : T → S4 := by
  intro t σ _ N q Y ν u
  rw [t N q Y ν u]

@[sa_complete "SemanticsSolutions.ebFieldExitEq"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := by
  intro σ _ N q Y ν u
  exact Prod.ext (s1 N q Y ν u) (Prod.ext (s2 N q Y ν u)
    (Prod.ext (s3 N q Y ν u) (s4 N q Y ν u)))

end Alignment.Shadows.SemanticsSolutions.EbFieldExitEq

/-! ## `SemanticsSolutions.ebFieldRemoveEq` (re-shadowed after text remediation)

Blind text: "The EB field of a removal `X → ∅`, written with the coordinate projections."

A removal `X → ∅` is `Rxn.trans X none a` (DataTypes, `Rxn`). DESIGN §D.4, transition row with
`Y = ∅`: `φ̇_X −= aφ_X`, `pop_X' −= a pop_X` and "Y = ∅: no gains". A transition has no `θ` or
`ξ` term (only contacts move `θ`, only exits move `ξ`). One shadow per coordinate, at every state
`u` (coordinates as projections of `u`). -/
namespace Alignment.Shadows.SemanticsSolutions.EbFieldRemoveEq

/-- Intended statement: the EB field of `trans X none a` at `u` is
`(0, 0, −aφ_X·e_X, −a pop_X·e_X)`. -/
@[sa_reference "SemanticsSolutions.ebFieldRemoveEq"]
def T : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (X : σ) (a : ℝ) (u : EB σ),
    ebField N q (Rxn.trans X none a) u =
      (0, 0, Pi.single X (-(a * u.2.2.1 X)), Pi.single X (-(a * u.2.2.2 X)))

/-- S1: a removal does not move `θ`. -/
@[sa_shadow "SemanticsSolutions.ebFieldRemoveEq" 1]
def S1 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (X : σ) (a : ℝ) (u : EB σ),
    (ebField N q (Rxn.trans X none a) u).1 = 0

/-- S2: a removal does not move `ξ`. -/
@[sa_shadow "SemanticsSolutions.ebFieldRemoveEq" 2]
def S2 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (X : σ) (a : ℝ) (u : EB σ),
    (ebField N q (Rxn.trans X none a) u).2.1 = 0

/-- S3: `φ̇ = −aφ_X` at `X` and `0` elsewhere (no gain). -/
@[sa_shadow "SemanticsSolutions.ebFieldRemoveEq" 3]
def S3 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (X : σ) (a : ℝ) (u : EB σ),
    (ebField N q (Rxn.trans X none a) u).2.2.1 = Pi.single X (-(a * u.2.2.1 X))

/-- S4: `pop' = −a pop_X` at `X` and `0` elsewhere (no gain). -/
@[sa_shadow "SemanticsSolutions.ebFieldRemoveEq" 4]
def S4 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (X : σ) (a : ℝ) (u : EB σ),
    (ebField N q (Rxn.trans X none a) u).2.2.2 = Pi.single X (-(a * u.2.2.2 X))

@[sa_ref_forward "SemanticsSolutions.ebFieldRemoveEq" 1]
theorem ref_fwd1 : T → S1 := by
  intro t σ _ N q X a u
  rw [t N q X a u]

@[sa_ref_forward "SemanticsSolutions.ebFieldRemoveEq" 2]
theorem ref_fwd2 : T → S2 := by
  intro t σ _ N q X a u
  rw [t N q X a u]

@[sa_ref_forward "SemanticsSolutions.ebFieldRemoveEq" 3]
theorem ref_fwd3 : T → S3 := by
  intro t σ _ N q X a u
  rw [t N q X a u]

@[sa_ref_forward "SemanticsSolutions.ebFieldRemoveEq" 4]
theorem ref_fwd4 : T → S4 := by
  intro t σ _ N q X a u
  rw [t N q X a u]

@[sa_complete "SemanticsSolutions.ebFieldRemoveEq"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := by
  intro σ _ N q X a u
  exact Prod.ext (s1 N q X a u) (Prod.ext (s2 N q X a u)
    (Prod.ext (s3 N q X a u) (s4 N q X a u)))

end Alignment.Shadows.SemanticsSolutions.EbFieldRemoveEq

/-! ## `SemanticsSolutions.ebFieldProgressEq` (re-shadowed after text remediation)

Blind text: "The EB field of a progression `X → Y`, written with the coordinate projections."

A progression `X → Y` is `Rxn.trans X (some Y) a` (DataTypes). DESIGN §D.4, transition row:
`φ̇_X −= aφ_X; φ̇_Y += aφ_X; pop_X' −= a pop_X; pop_Y' += a pop_X`; no `θ` or `ξ` term. The text
does not require `X ≠ Y`, so the loss at `X` and the gain at `Y` are added (they cancel when
`X = Y`). One shadow per coordinate, at every state `u`. -/
namespace Alignment.Shadows.SemanticsSolutions.EbFieldProgressEq

/-- Intended statement: the EB field of `trans X (some Y) a` at `u` is
`(0, 0, −aφ_X·e_X + aφ_X·e_Y, −a pop_X·e_X + a pop_X·e_Y)`. -/
@[sa_reference "SemanticsSolutions.ebFieldProgressEq"]
def T : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (X Y : σ) (a : ℝ) (u : EB σ),
    ebField N q (Rxn.trans X (some Y) a) u =
      (0, 0,
       Pi.single X (-(a * u.2.2.1 X)) + Pi.single Y (a * u.2.2.1 X),
       Pi.single X (-(a * u.2.2.2 X)) + Pi.single Y (a * u.2.2.2 X))

/-- S1: a progression does not move `θ`. -/
@[sa_shadow "SemanticsSolutions.ebFieldProgressEq" 1]
def S1 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (X Y : σ) (a : ℝ) (u : EB σ),
    (ebField N q (Rxn.trans X (some Y) a) u).1 = 0

/-- S2: a progression does not move `ξ`. -/
@[sa_shadow "SemanticsSolutions.ebFieldProgressEq" 2]
def S2 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (X Y : σ) (a : ℝ) (u : EB σ),
    (ebField N q (Rxn.trans X (some Y) a) u).2.1 = 0

/-- S3: `φ̇ = −aφ_X` at `X` plus `aφ_X` at `Y`, `0` elsewhere. -/
@[sa_shadow "SemanticsSolutions.ebFieldProgressEq" 3]
def S3 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (X Y : σ) (a : ℝ) (u : EB σ),
    (ebField N q (Rxn.trans X (some Y) a) u).2.2.1 =
      Pi.single X (-(a * u.2.2.1 X)) + Pi.single Y (a * u.2.2.1 X)

/-- S4: `pop' = −a pop_X` at `X` plus `a pop_X` at `Y`, `0` elsewhere. -/
@[sa_shadow "SemanticsSolutions.ebFieldProgressEq" 4]
def S4 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (X Y : σ) (a : ℝ) (u : EB σ),
    (ebField N q (Rxn.trans X (some Y) a) u).2.2.2 =
      Pi.single X (-(a * u.2.2.2 X)) + Pi.single Y (a * u.2.2.2 X)

@[sa_ref_forward "SemanticsSolutions.ebFieldProgressEq" 1]
theorem ref_fwd1 : T → S1 := by
  intro t σ _ N q X Y a u
  rw [t N q X Y a u]

@[sa_ref_forward "SemanticsSolutions.ebFieldProgressEq" 2]
theorem ref_fwd2 : T → S2 := by
  intro t σ _ N q X Y a u
  rw [t N q X Y a u]

@[sa_ref_forward "SemanticsSolutions.ebFieldProgressEq" 3]
theorem ref_fwd3 : T → S3 := by
  intro t σ _ N q X Y a u
  rw [t N q X Y a u]

@[sa_ref_forward "SemanticsSolutions.ebFieldProgressEq" 4]
theorem ref_fwd4 : T → S4 := by
  intro t σ _ N q X Y a u
  rw [t N q X Y a u]

@[sa_complete "SemanticsSolutions.ebFieldProgressEq"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := by
  intro σ _ N q X Y a u
  exact Prod.ext (s1 N q X Y a u) (Prod.ext (s2 N q X Y a u)
    (Prod.ext (s3 N q X Y a u) (s4 N q X Y a u)))

end Alignment.Shadows.SemanticsSolutions.EbFieldProgressEq

/-! ## `SemanticsSolutions.contDiffAtEbField`

Blind text: "The EB field of one reaction is `C^n` at every state `u` such that ψ, ψ' and ψ'' are
`C^n` at `θ = u.1`."

"One reaction" ranges over the three constructors of `Rxn σ` (contact, exit, transition); the
statement is split along them and along the smoothness level (`n : ℕ∞` versus `ω`). All three
hypotheses are kept for every reaction kind, as in the text. `σ` is finite so that `EB σ` is a
normed space. -/
namespace Alignment.Shadows.SemanticsSolutions.ContDiffAtEbField

/-- Intended statement: for every finite `σ`, network data `N`, seed factor `q`, reaction `r`,
level `n` and state `u`: if `ψ`, `ψ'`, `ψ''` are `C^n` at `u.1`, then `ebField N q r` is `C^n`
at `u`. -/
@[sa_reference "SemanticsSolutions.contDiffAtEbField"]
def T : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (r : Rxn σ) (n : WithTop ℕ∞)
    (u : EB σ),
    ContDiffAt ℝ n N.ψ u.1 → ContDiffAt ℝ n N.ψ' u.1 → ContDiffAt ℝ n N.ψ'' u.1 →
      ContDiffAt ℝ n (ebField N q r) u

/-- S1: contacts, finite-or-∞ level. -/
@[sa_shadow "SemanticsSolutions.contDiffAtEbField" 1]
def S1 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (J X : σ) (τ : ℝ) (n : ℕ∞)
    (u : EB σ),
    ContDiffAt ℝ (n : WithTop ℕ∞) N.ψ u.1 → ContDiffAt ℝ (n : WithTop ℕ∞) N.ψ' u.1 →
      ContDiffAt ℝ (n : WithTop ℕ∞) N.ψ'' u.1 →
        ContDiffAt ℝ (n : WithTop ℕ∞) (ebField N q (Rxn.contact J X τ)) u

/-- S2: exits, finite-or-∞ level. -/
@[sa_shadow "SemanticsSolutions.contDiffAtEbField" 2]
def S2 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (Y : σ) (ν : ℝ) (n : ℕ∞)
    (u : EB σ),
    ContDiffAt ℝ (n : WithTop ℕ∞) N.ψ u.1 → ContDiffAt ℝ (n : WithTop ℕ∞) N.ψ' u.1 →
      ContDiffAt ℝ (n : WithTop ℕ∞) N.ψ'' u.1 →
        ContDiffAt ℝ (n : WithTop ℕ∞) (ebField N q (Rxn.exit Y ν)) u

/-- S3: transitions (progressions and removals), finite-or-∞ level. -/
@[sa_shadow "SemanticsSolutions.contDiffAtEbField" 3]
def S3 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (X : σ) (Y : Option σ) (a : ℝ)
    (n : ℕ∞) (u : EB σ),
    ContDiffAt ℝ (n : WithTop ℕ∞) N.ψ u.1 → ContDiffAt ℝ (n : WithTop ℕ∞) N.ψ' u.1 →
      ContDiffAt ℝ (n : WithTop ℕ∞) N.ψ'' u.1 →
        ContDiffAt ℝ (n : WithTop ℕ∞) (ebField N q (Rxn.trans X Y a)) u

/-- S4: contacts, analytic level `ω`. -/
@[sa_shadow "SemanticsSolutions.contDiffAtEbField" 4]
def S4 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (J X : σ) (τ : ℝ) (u : EB σ),
    ContDiffAt ℝ (⊤ : WithTop ℕ∞) N.ψ u.1 → ContDiffAt ℝ (⊤ : WithTop ℕ∞) N.ψ' u.1 →
      ContDiffAt ℝ (⊤ : WithTop ℕ∞) N.ψ'' u.1 →
        ContDiffAt ℝ (⊤ : WithTop ℕ∞) (ebField N q (Rxn.contact J X τ)) u

/-- S5: exits, analytic level `ω`. -/
@[sa_shadow "SemanticsSolutions.contDiffAtEbField" 5]
def S5 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (Y : σ) (ν : ℝ) (u : EB σ),
    ContDiffAt ℝ (⊤ : WithTop ℕ∞) N.ψ u.1 → ContDiffAt ℝ (⊤ : WithTop ℕ∞) N.ψ' u.1 →
      ContDiffAt ℝ (⊤ : WithTop ℕ∞) N.ψ'' u.1 →
        ContDiffAt ℝ (⊤ : WithTop ℕ∞) (ebField N q (Rxn.exit Y ν)) u

/-- S6: transitions, analytic level `ω`. -/
@[sa_shadow "SemanticsSolutions.contDiffAtEbField" 6]
def S6 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (X : σ) (Y : Option σ) (a : ℝ)
    (u : EB σ),
    ContDiffAt ℝ (⊤ : WithTop ℕ∞) N.ψ u.1 → ContDiffAt ℝ (⊤ : WithTop ℕ∞) N.ψ' u.1 →
      ContDiffAt ℝ (⊤ : WithTop ℕ∞) N.ψ'' u.1 →
        ContDiffAt ℝ (⊤ : WithTop ℕ∞) (ebField N q (Rxn.trans X Y a)) u

@[sa_ref_forward "SemanticsSolutions.contDiffAtEbField" 1]
theorem ref_fwd1 : T → S1 := by
  intro t σ _ _ N q J X τ n u h1 h2 h3
  exact t N q (Rxn.contact J X τ) (n : WithTop ℕ∞) u h1 h2 h3

@[sa_ref_forward "SemanticsSolutions.contDiffAtEbField" 2]
theorem ref_fwd2 : T → S2 := by
  intro t σ _ _ N q Y ν n u h1 h2 h3
  exact t N q (Rxn.exit Y ν) (n : WithTop ℕ∞) u h1 h2 h3

@[sa_ref_forward "SemanticsSolutions.contDiffAtEbField" 3]
theorem ref_fwd3 : T → S3 := by
  intro t σ _ _ N q X Y a n u h1 h2 h3
  exact t N q (Rxn.trans X Y a) (n : WithTop ℕ∞) u h1 h2 h3

@[sa_ref_forward "SemanticsSolutions.contDiffAtEbField" 4]
theorem ref_fwd4 : T → S4 := by
  intro t σ _ _ N q J X τ u h1 h2 h3
  exact t N q (Rxn.contact J X τ) ⊤ u h1 h2 h3

@[sa_ref_forward "SemanticsSolutions.contDiffAtEbField" 5]
theorem ref_fwd5 : T → S5 := by
  intro t σ _ _ N q Y ν u h1 h2 h3
  exact t N q (Rxn.exit Y ν) ⊤ u h1 h2 h3

@[sa_ref_forward "SemanticsSolutions.contDiffAtEbField" 6]
theorem ref_fwd6 : T → S6 := by
  intro t σ _ _ N q X Y a u h1 h2 h3
  exact t N q (Rxn.trans X Y a) ⊤ u h1 h2 h3

@[sa_complete "SemanticsSolutions.contDiffAtEbField"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) : T := by
  intro σ _ _ N q r n u h1 h2 h3
  induction n using WithTop.recTopCoe with
  | top =>
    cases r with
    | contact J X τ => exact s4 N q J X τ u h1 h2 h3
    | exit Y ν => exact s5 N q Y ν u h1 h2 h3
    | trans X Y a => exact s6 N q X Y a u h1 h2 h3
  | coe m =>
    cases r with
    | contact J X τ => exact s1 N q J X τ m u h1 h2 h3
    | exit Y ν => exact s2 N q Y ν m u h1 h2 h3
    | trans X Y a => exact s3 N q X Y a m u h1 h2 h3

end Alignment.Shadows.SemanticsSolutions.ContDiffAtEbField

/-! ## `SemanticsSolutions.contDiffAtLift`

Blind text: "**The EB field of a reaction list is `C^n` where the degree data are.** For every
T_EB reaction list `rs`, the EB field `lift N q rs` is `C^n` at every state `u` such that ψ, ψ'
and ψ'' are `C^n` at `θ = u.1`."

Split along the smoothness level (`n : ℕ∞` versus `ω`). -/
namespace Alignment.Shadows.SemanticsSolutions.ContDiffAtLift

/-- Intended statement: for every finite `σ`, `N`, `q`, reaction list `rs`, level `n` and state
`u`: if `ψ`, `ψ'`, `ψ''` are `C^n` at `u.1`, then `lift N q rs` is `C^n` at `u`. -/
@[sa_reference "SemanticsSolutions.contDiffAtLift"]
def T : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ))
    (n : WithTop ℕ∞) (u : EB σ),
    ContDiffAt ℝ n N.ψ u.1 → ContDiffAt ℝ n N.ψ' u.1 → ContDiffAt ℝ n N.ψ'' u.1 →
      ContDiffAt ℝ n (lift N q rs) u

/-- S1: every finite-or-∞ level `n : ℕ∞`. -/
@[sa_shadow "SemanticsSolutions.contDiffAtLift" 1]
def S1 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)) (n : ℕ∞)
    (u : EB σ),
    ContDiffAt ℝ (n : WithTop ℕ∞) N.ψ u.1 → ContDiffAt ℝ (n : WithTop ℕ∞) N.ψ' u.1 →
      ContDiffAt ℝ (n : WithTop ℕ∞) N.ψ'' u.1 →
        ContDiffAt ℝ (n : WithTop ℕ∞) (lift N q rs) u

/-- S2: the analytic level `ω = ⊤`. -/
@[sa_shadow "SemanticsSolutions.contDiffAtLift" 2]
def S2 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)) (u : EB σ),
    ContDiffAt ℝ (⊤ : WithTop ℕ∞) N.ψ u.1 → ContDiffAt ℝ (⊤ : WithTop ℕ∞) N.ψ' u.1 →
      ContDiffAt ℝ (⊤ : WithTop ℕ∞) N.ψ'' u.1 →
        ContDiffAt ℝ (⊤ : WithTop ℕ∞) (lift N q rs) u

@[sa_ref_forward "SemanticsSolutions.contDiffAtLift" 1]
theorem ref_fwd1 : T → S1 := by
  intro t σ _ _ N q rs n u h1 h2 h3
  exact t N q rs (n : WithTop ℕ∞) u h1 h2 h3

@[sa_ref_forward "SemanticsSolutions.contDiffAtLift" 2]
theorem ref_fwd2 : T → S2 := by
  intro t σ _ _ N q rs u h1 h2 h3
  exact t N q rs ⊤ u h1 h2 h3

@[sa_complete "SemanticsSolutions.contDiffAtLift"]
theorem complete (s1 : S1) (s2 : S2) : T := by
  intro σ _ _ N q rs n u h1 h2 h3
  induction n using WithTop.recTopCoe with
  | top => exact s2 N q rs u h1 h2 h3
  | coe m => exact s1 N q rs m u h1 h2 h3

end Alignment.Shadows.SemanticsSolutions.ContDiffAtLift

/-! ## `SemanticsSolutions.contDiffLift` (re-shadowed after text remediation)

Blind text: "**EB models on a network with C¹ degree data are objects of Dyn.** Design statement
(DESIGN_NetworkEpiCore.md §D.3): "Objects of **Dyn** are (V, F): V a finite-dimensional real
normed space, F: V → V a C¹ vector field."; §D.4, the row of the representation functor **EB_N**
with domain "Open(Petri/T_EB), N fixed"."

Readings (DataTypes; module header claim `SemanticsSolutions.header.bullets`: "if ψ, ψ', ψ'' are
`C¹` everywhere (for example Poisson), the EB model `ebSys N q rs` is an object of the design's
category **Dyn**"):
* "EB model" of a T_EB reaction list `rs` on the network `N` (seed factor `q`) is the `DynSys`
  object `ebSys N q rs`; §D.4 "N fixed", domain T_EB: every `N`, every T_EB list `rs`, every `q`;
* "C¹ degree data": the three fields `ψ`, `ψ'`, `ψ''` of `N` are `C¹` on all of `ℝ`
  (`ContDiff ℝ 1`); no derivative relation between them is asserted by the text;
* "object of Dyn" (DataTypes (d): `DynSys` plus explicit `FiniteDimensional ℝ A.V` and
  `ContDiff ℝ 1 A.F`): a `DynSys` state space is a real normed space by construction, so the two
  remaining conditions of §D.3 are the finite dimension of `V` and the `C¹` field. One shadow each.
* Species types are finite (`Fintype σ`, as `ebSys` requires). -/
namespace Alignment.Shadows.SemanticsSolutions.ContDiffLift

/-- Intended statement. -/
@[sa_reference "SemanticsSolutions.contDiffLift"]
def T : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)),
    ContDiff ℝ 1 N.ψ → ContDiff ℝ 1 N.ψ' → ContDiff ℝ 1 N.ψ'' →
      FiniteDimensional ℝ (ebSys N q rs).V ∧ ContDiff ℝ 1 (ebSys N q rs).F

/-- S1: `V` is finite-dimensional (§D.3, first condition). -/
@[sa_shadow "SemanticsSolutions.contDiffLift" 1]
def S1 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)),
    ContDiff ℝ 1 N.ψ → ContDiff ℝ 1 N.ψ' → ContDiff ℝ 1 N.ψ'' →
      FiniteDimensional ℝ (ebSys N q rs).V

/-- S2: the vector field `F` is `C¹` (§D.3, second condition). -/
@[sa_shadow "SemanticsSolutions.contDiffLift" 2]
def S2 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)),
    ContDiff ℝ 1 N.ψ → ContDiff ℝ 1 N.ψ' → ContDiff ℝ 1 N.ψ'' →
      ContDiff ℝ 1 (ebSys N q rs).F

@[sa_ref_forward "SemanticsSolutions.contDiffLift" 1]
theorem ref_fwd1 : T → S1 := by
  intro t σ _ _ N q rs h1 h2 h3
  exact (t N q rs h1 h2 h3).1

@[sa_ref_forward "SemanticsSolutions.contDiffLift" 2]
theorem ref_fwd2 : T → S2 := by
  intro t σ _ _ N q rs h1 h2 h3
  exact (t N q rs h1 h2 h3).2

@[sa_complete "SemanticsSolutions.contDiffLift"]
theorem complete (s1 : S1) (s2 : S2) : T := by
  intro σ _ _ N q rs h1 h2 h3
  exact ⟨s1 N q rs h1 h2 h3, s2 N q rs h1 h2 h3⟩

end Alignment.Shadows.SemanticsSolutions.ContDiffLift

/-! ## `SemanticsSolutions.existsLocalSolution`

Blind text: "**Local existence of EB solutions (Picard–Lindelöf).** For every T_EB reaction list
`rs` and every state `u₀` such that ψ, ψ' and ψ'' are `C¹` at `θ = u₀.1`, there are `ε > 0` and
a curve `x` with `x 0 = u₀` that solves the EB field of rs (`HasDerivAt`) at every
`t ∈ (−ε, ε)`."

A single existential requirement (it cannot be split soundly: the same `ε` and `x` must serve
both the initial condition and the ODE). All `σ` (finite), `N`, `q` are quantified. -/
namespace Alignment.Shadows.SemanticsSolutions.ExistsLocalSolution

/-- Intended statement. -/
@[sa_reference "SemanticsSolutions.existsLocalSolution"]
def T : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)) (u₀ : EB σ),
    ContDiffAt ℝ 1 N.ψ u₀.1 → ContDiffAt ℝ 1 N.ψ' u₀.1 → ContDiffAt ℝ 1 N.ψ'' u₀.1 →
      ∃ ε > 0, ∃ x : ℝ → EB σ, x 0 = u₀ ∧
        ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt x (lift N q rs (x t)) t

/-- S1: the whole statement (one atomic existential requirement). -/
@[sa_shadow "SemanticsSolutions.existsLocalSolution" 1]
def S1 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)) (u₀ : EB σ),
    ContDiffAt ℝ 1 N.ψ u₀.1 → ContDiffAt ℝ 1 N.ψ' u₀.1 → ContDiffAt ℝ 1 N.ψ'' u₀.1 →
      ∃ ε > 0, ∃ x : ℝ → EB σ, x 0 = u₀ ∧
        ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt x (lift N q rs (x t)) t

@[sa_ref_forward "SemanticsSolutions.existsLocalSolution" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "SemanticsSolutions.existsLocalSolution"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SemanticsSolutions.ExistsLocalSolution

/-! ## `SemanticsSolutions.conservationLocal` (re-shadowed after text remediation)

Blind text: "**Edge conservation along a local EB solution from the design's initial condition.**
Design statement (DESIGN_NetworkEpiCore.md §D.4, Evidence): "The exit terms were checked by hand.
Conservation θ = φ_S + Σφ_X holds.""

The title is made precise by the module header (claim `SemanticsSolutions.header.bullets`):
"`conservation_local`: for every removal-free T_EB model on a network whose degree data are `C¹`
near θ = 1, with `ψ''` the derivative of `ψ'` near 1 and `ψ'(1) ≠ 0`, there is a solution on some
`(−ε, ε)` from the design's initial condition, and `θ = φ_S + Σ_X φ_X` holds along it."
* AMBIGUITY: "along a local EB solution" — existential or universal. The header says "there is a
  solution … and … holds along it": existential.
* Model class: removal-free (no `trans X none a`, i.e. no `X → ∅`; DESIGN §J.2 lowers removals to a
  sink species, §M.1 "For removal-free T_EB models (no `X → ∅`)"). Every finite `σ`, `N`, `q`.
* Network: `ψ, ψ', ψ''` are `C¹` near 1 — Mathlib's `ContDiffAt ℝ 1 · 1` (for a finite level this
  is `C¹` on a neighbourhood of 1); `ψ''` is the derivative of `ψ'` near 1
  (`∀ᶠ θ in 𝓝 1, HasDerivAt N.ψ' (N.ψ'' θ) θ`); `ψ'(1) ≠ 0`.
* AMBIGUITY: "the design's initial condition". Two readings, one shadow each:
  - (§D.4, literal) `θ(0) = 1, ξ(0) = 1, φ_X(0) = pop_X(0) = ρ_X` with `q = 1 − Σρ_X` (the relation
    written `Σ_X ρ_X = 1 − q`, the form of §M.1 and of the sibling Poisson text): shadow S1;
  - (§M.1, binding amendment: "the design's initial condition θ(0) = ξ(0) = 1, Σφ_X(0) = 1 − q",
    and the sibling text `conservationLocalPoisson`, "`conservation_local` for `CNet.poisson μ`":
    "initial data `φ₀, p₀` with `Σ_X φ₀(X) = 1 − q` … from `(1, 1, φ₀, p₀)`") `φ(0) = φ₀` with
    `Σφ₀ = 1 − q` and `pop(0) = p₀` unconstrained: shadow S2.
  The second reading implies the first, so `T` is the second reading.
* "A solution on `(−ε, ε)`": `HasDerivWithinAt` on `Set.Ioo (-ε) ε` at each of its points (DESIGN
  §J.2: "EB solutions are taken on a time interval I ∋ 0 (`HasDerivWithinAt` on a convex I)").
* "θ = φ_S + Σ_X φ_X" at time `t`, with `φ_S = qξψ'(θ)/ψ'(1)` (DESIGN §0), in primitive terms.
  One existential requirement per reading (the same `ε`, `x` must serve all conjuncts). -/
namespace Alignment.Shadows.SemanticsSolutions.ConservationLocal

/-- Intended statement (the general reading of the initial condition). -/
@[sa_reference "SemanticsSolutions.conservationLocal"]
def T : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ))
    (φ₀ p₀ : σ → ℝ),
    ContDiffAt ℝ 1 N.ψ 1 → ContDiffAt ℝ 1 N.ψ' 1 → ContDiffAt ℝ 1 N.ψ'' 1 →
    Filter.Eventually (fun θ : ℝ => HasDerivAt N.ψ' (N.ψ'' θ) θ) (nhds (1 : ℝ)) → N.ψ' 1 ≠ 0 →
    (∀ r ∈ rs, ∀ (X : σ) (a : ℝ), r ≠ Rxn.trans X none a) →
    ∑ X, φ₀ X = 1 - q →
      ∃ ε > 0, ∃ x : ℝ → EB σ, x 0 = ((1 : ℝ), (1 : ℝ), φ₀, p₀) ∧
        (∀ t ∈ Set.Ioo (-ε) ε, HasDerivWithinAt x (lift N q rs (x t)) (Set.Ioo (-ε) ε) t) ∧
        (∀ t ∈ Set.Ioo (-ε) ε,
          (x t).1 = q * (x t).2.1 * N.ψ' (x t).1 / N.ψ' 1 + ∑ X, (x t).2.2.1 X)

/-- S1: the §D.4 reading of the initial condition, `φ(0) = pop(0) = ρ` with `Σρ = 1 − q`. -/
@[sa_shadow "SemanticsSolutions.conservationLocal" 1]
def S1 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ))
    (ρ : σ → ℝ),
    ContDiffAt ℝ 1 N.ψ 1 → ContDiffAt ℝ 1 N.ψ' 1 → ContDiffAt ℝ 1 N.ψ'' 1 →
    Filter.Eventually (fun θ : ℝ => HasDerivAt N.ψ' (N.ψ'' θ) θ) (nhds (1 : ℝ)) → N.ψ' 1 ≠ 0 →
    (∀ r ∈ rs, ∀ (X : σ) (a : ℝ), r ≠ Rxn.trans X none a) →
    ∑ X, ρ X = 1 - q →
      ∃ ε > 0, ∃ x : ℝ → EB σ, x 0 = ((1 : ℝ), (1 : ℝ), ρ, ρ) ∧
        (∀ t ∈ Set.Ioo (-ε) ε, HasDerivWithinAt x (lift N q rs (x t)) (Set.Ioo (-ε) ε) t) ∧
        (∀ t ∈ Set.Ioo (-ε) ε,
          (x t).1 = q * (x t).2.1 * N.ψ' (x t).1 / N.ψ' 1 + ∑ X, (x t).2.2.1 X)

/-- S2: the §M.1 reading, `φ(0) = φ₀` with `Σφ₀ = 1 − q` and any `pop(0) = p₀`. -/
@[sa_shadow "SemanticsSolutions.conservationLocal" 2]
def S2 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ))
    (φ₀ p₀ : σ → ℝ),
    ContDiffAt ℝ 1 N.ψ 1 → ContDiffAt ℝ 1 N.ψ' 1 → ContDiffAt ℝ 1 N.ψ'' 1 →
    Filter.Eventually (fun θ : ℝ => HasDerivAt N.ψ' (N.ψ'' θ) θ) (nhds (1 : ℝ)) → N.ψ' 1 ≠ 0 →
    (∀ r ∈ rs, ∀ (X : σ) (a : ℝ), r ≠ Rxn.trans X none a) →
    ∑ X, φ₀ X = 1 - q →
      ∃ ε > 0, ∃ x : ℝ → EB σ, x 0 = ((1 : ℝ), (1 : ℝ), φ₀, p₀) ∧
        (∀ t ∈ Set.Ioo (-ε) ε, HasDerivWithinAt x (lift N q rs (x t)) (Set.Ioo (-ε) ε) t) ∧
        (∀ t ∈ Set.Ioo (-ε) ε,
          (x t).1 = q * (x t).2.1 * N.ψ' (x t).1 / N.ψ' 1 + ∑ X, (x t).2.2.1 X)

@[sa_ref_forward "SemanticsSolutions.conservationLocal" 1]
theorem ref_fwd1 : T → S1 := by
  intro t σ _ _ N q rs ρ h1 h2 h3 h4 h5 h6 h7
  exact t N q rs ρ ρ h1 h2 h3 h4 h5 h6 h7

@[sa_ref_forward "SemanticsSolutions.conservationLocal" 2]
theorem ref_fwd2 : T → S2 := fun t => t

@[sa_complete "SemanticsSolutions.conservationLocal"]
theorem complete (_s1 : S1) (s2 : S2) : T := s2

end Alignment.Shadows.SemanticsSolutions.ConservationLocal

/-! ## `SemanticsSolutions.conservationLocalPoisson` (re-shadowed after text remediation)

Blind text: "Edge conservation along a local solution on a Poisson(μ) network, `μ ≠ 0`
(`conservation_local` for `CNet.poisson μ`): for every removal-free T_EB reaction list `rs` and
initial data `φ₀, p₀` with `Σ_X φ₀(X) = 1 − q`, there are `ε > 0` and a solution on `(−ε, ε)` from
`(1, 1, φ₀, p₀)` along which `θ = φ_S + Σ_X φ_X`."

* Network `CNet.poisson μ`, every real `μ ≠ 0`; every finite `σ`, every seed factor `q`.
* Removal-free: no reaction `trans X none a` (`X → ∅`).
* A solution on `(−ε, ε)`: `HasDerivWithinAt` on `Set.Ioo (-ε) ε` (DESIGN §J.2).
* `φ_S = qξψ'(θ)/ψ'(1)` (DESIGN §0) with `ψ'` the field of `CNet.poisson μ`.
One existential requirement (the same `ε`, `x` serve all conjuncts). -/
namespace Alignment.Shadows.SemanticsSolutions.ConservationLocalPoisson

/-- Intended statement. -/
@[sa_reference "SemanticsSolutions.conservationLocalPoisson"]
def T : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (μ : ℝ) (q : ℝ) (rs : List (Rxn σ)) (φ₀ p₀ : σ → ℝ),
    μ ≠ 0 →
    (∀ r ∈ rs, ∀ (X : σ) (a : ℝ), r ≠ Rxn.trans X none a) →
    ∑ X, φ₀ X = 1 - q →
      ∃ ε > 0, ∃ x : ℝ → EB σ, x 0 = ((1 : ℝ), (1 : ℝ), φ₀, p₀) ∧
        (∀ t ∈ Set.Ioo (-ε) ε,
          HasDerivWithinAt x (lift (CNet.poisson μ) q rs (x t)) (Set.Ioo (-ε) ε) t) ∧
        (∀ t ∈ Set.Ioo (-ε) ε,
          (x t).1 = q * (x t).2.1 * (CNet.poisson μ).ψ' (x t).1 / (CNet.poisson μ).ψ' 1 +
            ∑ X, (x t).2.2.1 X)

/-- S1: the whole statement (one atomic existential requirement). -/
@[sa_shadow "SemanticsSolutions.conservationLocalPoisson" 1]
def S1 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (μ : ℝ) (q : ℝ) (rs : List (Rxn σ)) (φ₀ p₀ : σ → ℝ),
    μ ≠ 0 →
    (∀ r ∈ rs, ∀ (X : σ) (a : ℝ), r ≠ Rxn.trans X none a) →
    ∑ X, φ₀ X = 1 - q →
      ∃ ε > 0, ∃ x : ℝ → EB σ, x 0 = ((1 : ℝ), (1 : ℝ), φ₀, p₀) ∧
        (∀ t ∈ Set.Ioo (-ε) ε,
          HasDerivWithinAt x (lift (CNet.poisson μ) q rs (x t)) (Set.Ioo (-ε) ε) t) ∧
        (∀ t ∈ Set.Ioo (-ε) ε,
          (x t).1 = q * (x t).2.1 * (CNet.poisson μ).ψ' (x t).1 / (CNet.poisson μ).ψ' 1 +
            ∑ X, (x t).2.2.1 X)

@[sa_ref_forward "SemanticsSolutions.conservationLocalPoisson" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "SemanticsSolutions.conservationLocalPoisson"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SemanticsSolutions.ConservationLocalPoisson

/-! ## `SemanticsSolutions.seirConservationLocal` (re-shadowed after text remediation)

Blind text: "**Conservation is not vacuous for EB SEIR on Poisson(5).** With τ = 1/6, σ = 1/3,
γ = 1/4, seed φ_I(0) = pop_I(0) = 0.01 and q = 0.99 (so `Σ_X φ_X(0) = 1 − q`), there is a
solution on some interval `(−ε, ε)` from `(θ, ξ, φ, pop)(0) = (1, 1, φ₀, p₀)` along which
`θ = φ_S + Σ_X φ_X`."

* EB SEIR is the reaction list `seirRxns τ σ γ` (its second argument is the rate `σ` of `E → I`,
  DataTypes) on `CNet.poisson 5`, with seed factor `q = 0.99`.
* AMBIGUITY: "seed φ_I(0) = pop_I(0) = 0.01" names only the `I` entries. A seed placed in `I` (the
  design's `φ_X(0) = pop_X(0) = ρ_X` with `ρ_E = ρ_R = 0`, consistent with "so Σ_X φ_X(0) = 1 − q"
  = 0.01) gives `φ₀ = p₀ = Pi.single I 0.01`.
* Numerals as in the text (`1/6`, `1/3`, `1/4`, `0.01`, `0.99`).
* A solution on `(−ε, ε)`: `HasDerivWithinAt` on `Set.Ioo (-ε) ε` (DESIGN §J.2); `φ_S = qξψ'(θ)/ψ'(1)`.
One existential requirement. -/
namespace Alignment.Shadows.SemanticsSolutions.SeirConservationLocal

/-- Intended statement. -/
@[sa_reference "SemanticsSolutions.seirConservationLocal"]
def T : Prop :=
  ∃ ε > 0, ∃ x : ℝ → EB SEIRSp,
    x 0 = ((1 : ℝ), (1 : ℝ), (Pi.single SEIRSp.I (0.01 : ℝ) : SEIRSp → ℝ),
      (Pi.single SEIRSp.I (0.01 : ℝ) : SEIRSp → ℝ)) ∧
    (∀ t ∈ Set.Ioo (-ε) ε,
      HasDerivWithinAt x
        (lift (CNet.poisson 5) (0.99 : ℝ) (seirRxns (1/6 : ℝ) (1/3 : ℝ) (1/4 : ℝ)) (x t))
        (Set.Ioo (-ε) ε) t) ∧
    (∀ t ∈ Set.Ioo (-ε) ε,
      (x t).1 = (0.99 : ℝ) * (x t).2.1 * (CNet.poisson 5).ψ' (x t).1 / (CNet.poisson 5).ψ' 1 +
        ∑ X, (x t).2.2.1 X)

/-- S1: the whole statement (one atomic existential requirement). -/
@[sa_shadow "SemanticsSolutions.seirConservationLocal" 1]
def S1 : Prop :=
  ∃ ε > 0, ∃ x : ℝ → EB SEIRSp,
    x 0 = ((1 : ℝ), (1 : ℝ), (Pi.single SEIRSp.I (0.01 : ℝ) : SEIRSp → ℝ),
      (Pi.single SEIRSp.I (0.01 : ℝ) : SEIRSp → ℝ)) ∧
    (∀ t ∈ Set.Ioo (-ε) ε,
      HasDerivWithinAt x
        (lift (CNet.poisson 5) (0.99 : ℝ) (seirRxns (1/6 : ℝ) (1/3 : ℝ) (1/4 : ℝ)) (x t))
        (Set.Ioo (-ε) ε) t) ∧
    (∀ t ∈ Set.Ioo (-ε) ε,
      (x t).1 = (0.99 : ℝ) * (x t).2.1 * (CNet.poisson 5).ψ' (x t).1 / (CNet.poisson 5).ψ' 1 +
        ∑ X, (x t).2.2.1 X)

@[sa_ref_forward "SemanticsSolutions.seirConservationLocal" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "SemanticsSolutions.seirConservationLocal"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SemanticsSolutions.SeirConservationLocal
