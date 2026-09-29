import Alignment.Registry
import NetworkEpi.Morphisms.Poisson

/-!
# Blind shadow sets: group `MorphismsPoisson` (DESIGN §D.5 M2, §J.10, §L.1)

Written blind (re-shadowed after text remediation for poissonIsoSolution, poissonIsoNatural,
poissonIsoSir, poissonIsoSeir, poissonDLNone, hasFDerivAtPoissonMap, poissonEbField): from the entries of `Alignment/claims_blind.yaml`, `Alignment/DataTypes/MorphismsPoisson.md`,
`Alignment/README.md`, `Alignment/Example/ExampleShadows.lean` and `DESIGN_NetworkEpiCore.md` only.

Conventions used throughout (DataTypes §e):
* EB on Poisson(μ) with seed factor `q`: `ebSys (CNet.poisson μ) q P`; in the design's coordinates
  `(θ, φ, pop)` (slice ξ = 1, exit-free models): `ebSys1 (CNet.poisson μ) q P`.
* MA(D_μ P): `sSys (poissonRxns μ P)`, whose field is `sLift (poissonRxns μ P)`.
* π = `poissonMap μ q`; on the slice ξ = 1 it is `poissonMap μ q ∘ EB1.incl`.
* `S > 0` is `0 < v none` (`none` is the species `S` of `D_μ P`).
* "exit-free" is written primitively: no reaction of `P` is an exit `s → Y`.
* A "conjugacy onto S > 0" is written in primitive pieces following the docstring of `IsConjOn`
  (local semiconjugacies both ways, the image conditions, and the two inverse laws).
-/

open NEP

namespace Alignment.Shadows.MorphismsPoisson

/-- "P is exit-free": no reaction of `P` is an exit `s → Y`, in primitive terms. -/
def ExitFree {σ : Type} (P : List (Rxn σ)) : Prop := ∀ r ∈ P, ∀ (Y : σ) (ν : ℝ), r ≠ Rxn.exit Y ν

/-- π on the slice ξ = 1, in the design's coordinates `(θ, φ, pop)`. -/
noncomputable def piSlice {σ : Type} (μ q : ℝ) (w : EB1 σ) : DSp σ → ℝ := poissonMap μ q (EB1.incl w)

/-- The open set `S > 0` of MA(D_μ P). -/
def SPos (σ : Type) : Set (DSp σ → ℝ) := {v | 0 < v none}

end Alignment.Shadows.MorphismsPoisson

/-! ## `MorphismsPoisson.poissonIsoSemiconj`

Text: "for every T_EB model (exits allowed) and `μ ≠ 0`, `poissonMap` is a global semiconjugacy
from EB on Poisson(μ) to MA(D_μ P)." No restriction on `q` is stated, so `q` is arbitrary. -/
namespace Alignment.Shadows.MorphismsPoisson.PoissonIsoSemiconj

@[sa_reference "MorphismsPoisson.poissonIsoSemiconj"]
def T : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (μ q : ℝ) (P : List (Rxn σ)), μ ≠ 0 →
    IsSemiconj (ebSys (CNet.poisson μ) q P) (sSys (poissonRxns μ P)) (poissonMap μ q)

/-- S1: the whole statement (a single atomic requirement: global semiconjugacy, for all P with exits). -/
@[sa_shadow "MorphismsPoisson.poissonIsoSemiconj" 1]
def S1 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (μ q : ℝ) (P : List (Rxn σ)), μ ≠ 0 →
    IsSemiconj (ebSys (CNet.poisson μ) q P) (sSys (poissonRxns μ P)) (poissonMap μ q)

@[sa_ref_forward "MorphismsPoisson.poissonIsoSemiconj" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MorphismsPoisson.poissonIsoSemiconj"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MorphismsPoisson.PoissonIsoSemiconj

/-! ## `MorphismsPoisson.poissonIso`

Text: "for every **exit-free** T_EB model, `μ ≠ 0` and `q > 0`, the EB model in the design's
coordinates `(θ, φ, pop)` is conjugate to MA(D_μ P) restricted to the open set `S > 0`, with inverse
`(S, Φ, X) ↦ (1 + log(S/q)/μ, Φ, X)`."

The EB side is not restricted by the text, so its domain is all of `EB1 σ` (`Set.univ`); the MA side
is restricted to `S > 0`; the forward map is π (on ξ = 1) and the inverse is `poissonInv μ q`.
Conjugacy is split (per the `IsConjOn` docstring) into: π a local semiconjugacy on the whole EB
space (S1), π lands in `S > 0` (S2), the inverse a local semiconjugacy on `S > 0` (S3), and the two
inverse laws (S4, S5). The image condition of the inverse (`g(U) ⊆ univ`) is trivially true and is
omitted. -/
namespace Alignment.Shadows.MorphismsPoisson.PoissonIso

@[sa_reference "MorphismsPoisson.poissonIso"]
def T : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (μ q : ℝ) (P : List (Rxn σ)),
    ExitFree P → μ ≠ 0 → 0 < q →
      IsSemiconjOn (ebSys1 (CNet.poisson μ) q P) (sSys (poissonRxns μ P)) Set.univ (piSlice μ q) ∧
      (∀ w : EB1 σ, 0 < piSlice μ q w none) ∧
      IsSemiconjOn (sSys (poissonRxns μ P)) (ebSys1 (CNet.poisson μ) q P) (SPos σ)
        (poissonInv μ q) ∧
      (∀ w : EB1 σ, poissonInv μ q (piSlice μ q w) = w) ∧
      (∀ v ∈ SPos σ, piSlice μ q (poissonInv μ q v) = v)

/-- S1: π (on ξ = 1) is a semiconjugacy on the whole EB space, EB → MA(D_μ P). -/
@[sa_shadow "MorphismsPoisson.poissonIso" 1]
def S1 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (μ q : ℝ) (P : List (Rxn σ)),
    ExitFree P → μ ≠ 0 → 0 < q →
      IsSemiconjOn (ebSys1 (CNet.poisson μ) q P) (sSys (poissonRxns μ P)) Set.univ (piSlice μ q)

/-- S2: π maps the EB space into `S > 0`. -/
@[sa_shadow "MorphismsPoisson.poissonIso" 2]
def S2 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (μ q : ℝ) (P : List (Rxn σ)),
    ExitFree P → μ ≠ 0 → 0 < q →
      ∀ w : EB1 σ, 0 < piSlice μ q w none

/-- S3: the stated inverse is a semiconjugacy MA(D_μ P) → EB on `S > 0`. -/
@[sa_shadow "MorphismsPoisson.poissonIso" 3]
def S3 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (μ q : ℝ) (P : List (Rxn σ)),
    ExitFree P → μ ≠ 0 → 0 < q →
      IsSemiconjOn (sSys (poissonRxns μ P)) (ebSys1 (CNet.poisson μ) q P) (SPos σ)
        (poissonInv μ q)

/-- S4: inverse ∘ π = id on the EB space. -/
@[sa_shadow "MorphismsPoisson.poissonIso" 4]
def S4 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (μ q : ℝ) (P : List (Rxn σ)),
    ExitFree P → μ ≠ 0 → 0 < q →
      ∀ w : EB1 σ, poissonInv μ q (piSlice μ q w) = w

/-- S5: π ∘ inverse = id on `S > 0`. -/
@[sa_shadow "MorphismsPoisson.poissonIso" 5]
def S5 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (μ q : ℝ) (P : List (Rxn σ)),
    ExitFree P → μ ≠ 0 → 0 < q →
      ∀ v ∈ SPos σ, piSlice μ q (poissonInv μ q v) = v

@[sa_ref_forward "MorphismsPoisson.poissonIso" 1]
theorem ref_fwd1 : T → S1 := fun t _ _ _ μ q P he hμ hq => (t μ q P he hμ hq).1

@[sa_ref_forward "MorphismsPoisson.poissonIso" 2]
theorem ref_fwd2 : T → S2 := fun t _ _ _ μ q P he hμ hq => (t μ q P he hμ hq).2.1

@[sa_ref_forward "MorphismsPoisson.poissonIso" 3]
theorem ref_fwd3 : T → S3 := fun t _ _ _ μ q P he hμ hq => (t μ q P he hμ hq).2.2.1

@[sa_ref_forward "MorphismsPoisson.poissonIso" 4]
theorem ref_fwd4 : T → S4 := fun t _ _ _ μ q P he hμ hq => (t μ q P he hμ hq).2.2.2.1

@[sa_ref_forward "MorphismsPoisson.poissonIso" 5]
theorem ref_fwd5 : T → S5 := fun t _ _ _ μ q P he hμ hq => (t μ q P he hμ hq).2.2.2.2

@[sa_complete "MorphismsPoisson.poissonIso"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) : T :=
  fun μ q P he hμ hq =>
    ⟨s1 μ q P he hμ hq, s2 μ q P he hμ hq, s3 μ q P he hμ hq, s4 μ q P he hμ hq,
      s5 μ q P he hμ hq⟩

end Alignment.Shadows.MorphismsPoisson.PoissonIso

/-! ## `MorphismsPoisson.poissonIsoSolution`

Text: "**The Poisson isomorphism on trajectories (M2).** Design statement (DESIGN_NetworkEpiCore.md
§D.5, M2): "EB_{Pois μ}(P) ≅ MA(D_μ P) via π(θ, φ, pop) = (qξe^{μ(θ−1)}, Φ = φ, X = pop)"; §D.3:
"semiconjugacies map solution curves to solution curves". [...] Scope: the Poisson(μ) network is
taken with `μ ≠ 0`, as in the design, whose Poisson degree distributions have mean μ > 0 (for
`μ = 0` the PGF has `ψ' ≡ 0` and the network has no edges). Solutions are mapped on any set of
times `I`, both for derivatives within `I` (this theorem) and for two-sided derivatives at every
`t ∈ I` (`poisson_iso_solution_at`), as amended by §M.5 and §M.10."

Reading. The map π = `poissonMap μ q` is written with ξ, so it acts on the full EB coordinates
`(θ, ξ, φ, pop)`: the source is the EB model `ebSys (CNet.poisson μ) q P`, the target is
MA(D_μ P) = `sSys (poissonRxns μ P)`. The only stated hypothesis is `μ ≠ 0`: P is any T_EB list
(exits allowed; "exit-free" is not stated) and `q` is arbitrary. "Any set of times `I`" is an
arbitrary `I : Set ℝ` (no convexity, openness or `0 ∈ I`). A trajectory is a curve
`u : ℝ → EB σ` solving the EB equation at the times of `I`; its image is `poissonMap μ q ∘ u`,
which must solve MA(D_μ P) at the same times.

Two atomic requirements (the text's "both ... and"):
* S1 (within `I`): `HasDerivWithinAt u (F (u t)) I t` for all `t ∈ I` implies
  `HasDerivWithinAt (π ∘ u) (G (π (u t))) I t` for all `t ∈ I`;
* S2 (two-sided at every `t ∈ I`): `HasDerivAt u (F (u t)) t` for all `t ∈ I` implies
  `HasDerivAt (π ∘ u) (G (π (u t))) t` for all `t ∈ I`.
AMBIGUITY: the text attributes the two-sided statement to `poisson_iso_solution_at` and marks the
within-`I` statement as "this theorem"; both are asserted by the text, so both are shadows (S2
checks the claim only if the registry lists the `_at` theorem too).
AMBIGUITY: "≅" might suggest also mapping MA(D_μ P) trajectories in `S > 0` back to EB; the text
states no exit-free or `q > 0` hypothesis (needed for the inverse), and speaks only of solutions
being mapped by the semiconjugacy, so the inverse direction is not read into it. -/
namespace Alignment.Shadows.MorphismsPoisson.PoissonIsoSolution

/-- Intended statement: for every T_EB list `P`, `μ ≠ 0`, any `q` and any set of times `I`, π maps
EB-on-Poisson(μ) solutions to MA(D_μ P) solutions, both for derivatives within `I` and for
two-sided derivatives at every `t ∈ I`. -/
@[sa_reference "MorphismsPoisson.poissonIsoSolution"]
def T : Prop :=
  (∀ {σ : Type} [DecidableEq σ] [Fintype σ] (μ q : ℝ) (P : List (Rxn σ)), μ ≠ 0 →
    ∀ (I : Set ℝ) (u : ℝ → EB σ),
      (∀ t ∈ I, HasDerivWithinAt u ((ebSys (CNet.poisson μ) q P).F (u t)) I t) →
        ∀ t ∈ I, HasDerivWithinAt (poissonMap μ q ∘ u)
          ((sSys (poissonRxns μ P)).F (poissonMap μ q (u t))) I t) ∧
  (∀ {σ : Type} [DecidableEq σ] [Fintype σ] (μ q : ℝ) (P : List (Rxn σ)), μ ≠ 0 →
    ∀ (I : Set ℝ) (u : ℝ → EB σ),
      (∀ t ∈ I, HasDerivAt u ((ebSys (CNet.poisson μ) q P).F (u t)) t) →
        ∀ t ∈ I, HasDerivAt (poissonMap μ q ∘ u)
          ((sSys (poissonRxns μ P)).F (poissonMap μ q (u t))) t)

/-- S1 (derivatives within `I`): EB solutions within an arbitrary set of times `I` are mapped by π
to MA(D_μ P) solutions within `I`. -/
@[sa_shadow "MorphismsPoisson.poissonIsoSolution" 1]
def S1 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (μ q : ℝ) (P : List (Rxn σ)), μ ≠ 0 →
    ∀ (I : Set ℝ) (u : ℝ → EB σ),
      (∀ t ∈ I, HasDerivWithinAt u ((ebSys (CNet.poisson μ) q P).F (u t)) I t) →
        ∀ t ∈ I, HasDerivWithinAt (poissonMap μ q ∘ u)
          ((sSys (poissonRxns μ P)).F (poissonMap μ q (u t))) I t

/-- S2 (two-sided derivatives at every `t ∈ I`): EB curves solving (two-sided) at every time of an
arbitrary set `I` are mapped by π to curves solving MA(D_μ P) (two-sided) at every `t ∈ I`. -/
@[sa_shadow "MorphismsPoisson.poissonIsoSolution" 2]
def S2 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (μ q : ℝ) (P : List (Rxn σ)), μ ≠ 0 →
    ∀ (I : Set ℝ) (u : ℝ → EB σ),
      (∀ t ∈ I, HasDerivAt u ((ebSys (CNet.poisson μ) q P).F (u t)) t) →
        ∀ t ∈ I, HasDerivAt (poissonMap μ q ∘ u)
          ((sSys (poissonRxns μ P)).F (poissonMap μ q (u t))) t

@[sa_ref_forward "MorphismsPoisson.poissonIsoSolution" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "MorphismsPoisson.poissonIsoSolution" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "MorphismsPoisson.poissonIsoSolution"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.MorphismsPoisson.PoissonIsoSolution

/-! ## `MorphismsPoisson.poissonIsoNatural`

Text: "The Poisson isomorphism is natural in P (M2). [...] naturality with respect to the species
maps of the syntax (relabelling and gluing), [...] it is not stated as a natural transformation of
functors into `DynSys`. [...] `D_μ` commutes with relabelling species, and the map commutes with the
pullback and pushforward of coordinates along species maps."

Three requirements: (S1) `D_μ (P relabelled along f) = (D_μ P) relabelled along the induced species
map `dMap f``; (S2) `π (pullEB f u) = π u ∘ dMap f` (pullback of `DSp`-coordinates is precomposition);
(S3) `π (pushEB f u) = push (dMap f) (π u)` (pushforward sums over fibres). Gluing is relabelling
along cospan legs, so it is covered by arbitrary `f`. -/
namespace Alignment.Shadows.MorphismsPoisson.PoissonIsoNatural

@[sa_reference "MorphismsPoisson.poissonIsoNatural"]
def T : Prop :=
  (∀ {σ σ' : Type} (f : σ → σ') (μ : ℝ) (P : List (Rxn σ)),
      poissonRxns μ (P.map (Rxn.map f)) = (poissonRxns μ P).map (SRxn.map (dMap f))) ∧
  (∀ {σ σ' : Type} (f : σ → σ') (μ q : ℝ) (u : EB σ'),
      poissonMap μ q (pullEB f u) = fun i => poissonMap μ q u (dMap f i)) ∧
  (∀ {σ σ' : Type} [Fintype σ] [DecidableEq σ'] (f : σ → σ') (μ q : ℝ) (u : EB σ),
      poissonMap μ q (pushEB f u) = push (dMap f) (poissonMap μ q u))

/-- S1: `D_μ` commutes with relabelling the species of a reaction list. -/
@[sa_shadow "MorphismsPoisson.poissonIsoNatural" 1]
def S1 : Prop :=
  ∀ {σ σ' : Type} (f : σ → σ') (μ : ℝ) (P : List (Rxn σ)),
    poissonRxns μ (P.map (Rxn.map f)) = (poissonRxns μ P).map (SRxn.map (dMap f))

/-- S2: π commutes with pullback of coordinates along species maps. -/
@[sa_shadow "MorphismsPoisson.poissonIsoNatural" 2]
def S2 : Prop :=
  ∀ {σ σ' : Type} (f : σ → σ') (μ q : ℝ) (u : EB σ'),
    poissonMap μ q (pullEB f u) = fun i => poissonMap μ q u (dMap f i)

/-- S3: π commutes with pushforward of coordinates along species maps. -/
@[sa_shadow "MorphismsPoisson.poissonIsoNatural" 3]
def S3 : Prop :=
  ∀ {σ σ' : Type} [Fintype σ] [DecidableEq σ'] (f : σ → σ') (μ q : ℝ) (u : EB σ),
    poissonMap μ q (pushEB f u) = push (dMap f) (poissonMap μ q u)

@[sa_ref_forward "MorphismsPoisson.poissonIsoNatural" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "MorphismsPoisson.poissonIsoNatural" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1

@[sa_ref_forward "MorphismsPoisson.poissonIsoNatural" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2

@[sa_complete "MorphismsPoisson.poissonIsoNatural"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.MorphismsPoisson.PoissonIsoNatural

/-! ## `MorphismsPoisson.poissonDSirField`

Text: "**The mass-action equations of `D_μ(SIR)` (M2, SIR).** Design statement: "D_μ: contacts
S + Φ_J → Φ_X + X + Φ_J at rate μτ; Φ_J → ∅ at τ; transitions on both copies"."

SIR = `sirRxns τ γ` (`s + I → I + I` at τ, `I → R` at γ). By the quoted rule, D_μ(SIR) is
`S + Φ_I → Φ_I + I + Φ_I` at μτ, `Φ_I → ∅` at τ, `Φ_I → Φ_R` at γ and `I → R` at γ. Its multiset
mass-action equations (field `sLift`, flux `k·Π inputs`, change `flux·(out − in)`) are, with
`x = (S, Φ_I, Φ_R, I, R)`:
  Ṡ = −μτ S Φ_I,  Φ̇_I = μτ S Φ_I − τ Φ_I − γ Φ_I,  Φ̇_R = γ Φ_I,  İ = μτ S Φ_I − γ I,  Ṙ = γ I.
One shadow per component. No hypothesis on μ, τ, γ is stated. -/
namespace Alignment.Shadows.MorphismsPoisson.PoissonDSirField

/-- Shorthands for the species of `D_μ(SIR)`. -/
abbrev sS : DSp SIRSp := none
abbrev sPhiI : DSp SIRSp := some (Sum.inl SIRSp.I)
abbrev sPhiR : DSp SIRSp := some (Sum.inl SIRSp.R)
abbrev sI : DSp SIRSp := some (Sum.inr SIRSp.I)
abbrev sR : DSp SIRSp := some (Sum.inr SIRSp.R)

@[sa_reference "MorphismsPoisson.poissonDSirField"]
def T : Prop :=
  ∀ (μ τ γ : ℝ) (x : DSp SIRSp → ℝ),
    sLift (poissonRxns μ (sirRxns τ γ)) x sS = -(μ * τ * x sS * x sPhiI) ∧
    sLift (poissonRxns μ (sirRxns τ γ)) x sPhiI =
      μ * τ * x sS * x sPhiI - τ * x sPhiI - γ * x sPhiI ∧
    sLift (poissonRxns μ (sirRxns τ γ)) x sPhiR = γ * x sPhiI ∧
    sLift (poissonRxns μ (sirRxns τ γ)) x sI = μ * τ * x sS * x sPhiI - γ * x sI ∧
    sLift (poissonRxns μ (sirRxns τ γ)) x sR = γ * x sI

/-- S1: Ṡ = −μτ S Φ_I. -/
@[sa_shadow "MorphismsPoisson.poissonDSirField" 1]
def S1 : Prop :=
  ∀ (μ τ γ : ℝ) (x : DSp SIRSp → ℝ),
    sLift (poissonRxns μ (sirRxns τ γ)) x sS = -(μ * τ * x sS * x sPhiI)

/-- S2: Φ̇_I = μτ S Φ_I − τ Φ_I − γ Φ_I. -/
@[sa_shadow "MorphismsPoisson.poissonDSirField" 2]
def S2 : Prop :=
  ∀ (μ τ γ : ℝ) (x : DSp SIRSp → ℝ),
    sLift (poissonRxns μ (sirRxns τ γ)) x sPhiI =
      μ * τ * x sS * x sPhiI - τ * x sPhiI - γ * x sPhiI

/-- S3: Φ̇_R = γ Φ_I. -/
@[sa_shadow "MorphismsPoisson.poissonDSirField" 3]
def S3 : Prop :=
  ∀ (μ τ γ : ℝ) (x : DSp SIRSp → ℝ),
    sLift (poissonRxns μ (sirRxns τ γ)) x sPhiR = γ * x sPhiI

/-- S4: İ = μτ S Φ_I − γ I. -/
@[sa_shadow "MorphismsPoisson.poissonDSirField" 4]
def S4 : Prop :=
  ∀ (μ τ γ : ℝ) (x : DSp SIRSp → ℝ),
    sLift (poissonRxns μ (sirRxns τ γ)) x sI = μ * τ * x sS * x sPhiI - γ * x sI

/-- S5: Ṙ = γ I. -/
@[sa_shadow "MorphismsPoisson.poissonDSirField" 5]
def S5 : Prop :=
  ∀ (μ τ γ : ℝ) (x : DSp SIRSp → ℝ),
    sLift (poissonRxns μ (sirRxns τ γ)) x sR = γ * x sI

@[sa_ref_forward "MorphismsPoisson.poissonDSirField" 1]
theorem ref_fwd1 : T → S1 := fun t μ τ γ x => (t μ τ γ x).1

@[sa_ref_forward "MorphismsPoisson.poissonDSirField" 2]
theorem ref_fwd2 : T → S2 := fun t μ τ γ x => (t μ τ γ x).2.1

@[sa_ref_forward "MorphismsPoisson.poissonDSirField" 3]
theorem ref_fwd3 : T → S3 := fun t μ τ γ x => (t μ τ γ x).2.2.1

@[sa_ref_forward "MorphismsPoisson.poissonDSirField" 4]
theorem ref_fwd4 : T → S4 := fun t μ τ γ x => (t μ τ γ x).2.2.2.1

@[sa_ref_forward "MorphismsPoisson.poissonDSirField" 5]
theorem ref_fwd5 : T → S5 := fun t μ τ γ x => (t μ τ γ x).2.2.2.2

@[sa_complete "MorphismsPoisson.poissonDSirField"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) : T :=
  fun μ τ γ x => ⟨s1 μ τ γ x, s2 μ τ γ x, s3 μ τ γ x, s4 μ τ γ x, s5 μ τ γ x⟩

end Alignment.Shadows.MorphismsPoisson.PoissonDSirField

/-! ## `MorphismsPoisson.poissonIsoSir`

Text: "**The Poisson isomorphism for SIR (M2, SIR instance).** Design statement: "Poisson
isomorphism | EB_{Pois μ}(P) ≅ MA(D_μ P) via π(θ, φ, pop) = (qξe^{μ(θ−1)}, Φ = φ, X = pop) [...] |
natural iso onto S > 0"; §D.7, L4b: "SIR/SEIR concrete first"."

For P = `sirRxns τ γ` (exit-free), EB on Poisson(μ) in the design's coordinates `(θ, φ, pop)`
(`ebSys1`) is isomorphic via π to MA(D_μ SIR) restricted to `S > 0`: π is a semiconjugacy on the
whole EB space (S1), lands in `S > 0` (S2), and has an inverse on `S > 0` that is a semiconjugacy
(S3). The text names no inverse, so it is existential.
-- AMBIGUITY: no hypothesis on μ, q is quoted. DESIGN §M.3: "The Poisson(μ) statements are for
-- μ ≠ 0"; and "onto S > 0" is impossible for q ≤ 0 (then S = q e^{μ(θ−1)} ≤ 0) and for μ = 0
-- (S ≡ q, so the image misses most of S > 0), so μ ≠ 0 and 0 < q are assumed; τ, γ are arbitrary.
-- The inverse is not named in the text, so it is existential; "onto" is the pair (π lands in
-- S > 0) + (π ∘ g = id on S > 0).
-- "Natural" has no content for a single model and is not formalised here. -/
namespace Alignment.Shadows.MorphismsPoisson.PoissonIsoSir

@[sa_reference "MorphismsPoisson.poissonIsoSir"]
def T : Prop :=
  ∀ (μ q τ γ : ℝ), μ ≠ 0 → 0 < q →
    IsSemiconjOn (ebSys1 (CNet.poisson μ) q (sirRxns τ γ)) (sSys (poissonRxns μ (sirRxns τ γ)))
      Set.univ (piSlice μ q) ∧
    (∀ w : EB1 SIRSp, 0 < piSlice μ q w none) ∧
    ∃ g : (DSp SIRSp → ℝ) → EB1 SIRSp,
      IsSemiconjOn (sSys (poissonRxns μ (sirRxns τ γ))) (ebSys1 (CNet.poisson μ) q (sirRxns τ γ))
        (SPos SIRSp) g ∧
      (∀ w : EB1 SIRSp, g (piSlice μ q w) = w) ∧
      (∀ v ∈ SPos SIRSp, piSlice μ q (g v) = v)

/-- S1: π is a semiconjugacy EB(SIR) → MA(D_μ SIR) on the whole EB space. -/
@[sa_shadow "MorphismsPoisson.poissonIsoSir" 1]
def S1 : Prop :=
  ∀ (μ q τ γ : ℝ), μ ≠ 0 → 0 < q →
    IsSemiconjOn (ebSys1 (CNet.poisson μ) q (sirRxns τ γ)) (sSys (poissonRxns μ (sirRxns τ γ)))
      Set.univ (piSlice μ q)

/-- S2: π maps into `S > 0`. -/
@[sa_shadow "MorphismsPoisson.poissonIsoSir" 2]
def S2 : Prop :=
  ∀ (μ q : ℝ), μ ≠ 0 → 0 < q → ∀ w : EB1 SIRSp, 0 < piSlice μ q w none

/-- S3: π has a two-sided inverse on `S > 0` which is a semiconjugacy MA(D_μ SIR) → EB(SIR) there. -/
@[sa_shadow "MorphismsPoisson.poissonIsoSir" 3]
def S3 : Prop :=
  ∀ (μ q τ γ : ℝ), μ ≠ 0 → 0 < q →
    ∃ g : (DSp SIRSp → ℝ) → EB1 SIRSp,
      IsSemiconjOn (sSys (poissonRxns μ (sirRxns τ γ))) (ebSys1 (CNet.poisson μ) q (sirRxns τ γ))
        (SPos SIRSp) g ∧
      (∀ w : EB1 SIRSp, g (piSlice μ q w) = w) ∧
      (∀ v ∈ SPos SIRSp, piSlice μ q (g v) = v)

@[sa_ref_forward "MorphismsPoisson.poissonIsoSir" 1]
theorem ref_fwd1 : T → S1 := fun t μ q τ γ hμ hq => (t μ q τ γ hμ hq).1

@[sa_ref_forward "MorphismsPoisson.poissonIsoSir" 2]
theorem ref_fwd2 : T → S2 := fun t μ q hμ hq => (t μ q 0 0 hμ hq).2.1

@[sa_ref_forward "MorphismsPoisson.poissonIsoSir" 3]
theorem ref_fwd3 : T → S3 := fun t μ q τ γ hμ hq => (t μ q τ γ hμ hq).2.2

@[sa_complete "MorphismsPoisson.poissonIsoSir"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T :=
  fun μ q τ γ hμ hq => ⟨s1 μ q τ γ hμ hq, s2 μ q hμ hq, s3 μ q τ γ hμ hq⟩

end Alignment.Shadows.MorphismsPoisson.PoissonIsoSir

/-! ## `MorphismsPoisson.poissonIsoSeir`

Text: as for SIR, "**The Poisson isomorphism for SEIR (M2, SEIR instance).**" with the same design
quote. P = `seirRxns τ a γ` (exit-free). Same reading and same AMBIGUITY as for SIR: μ ≠ 0 (DESIGN
§M.3) and 0 < q (necessary for "onto S > 0"); τ, a, γ arbitrary; inverse existential. -/
namespace Alignment.Shadows.MorphismsPoisson.PoissonIsoSeir

@[sa_reference "MorphismsPoisson.poissonIsoSeir"]
def T : Prop :=
  ∀ (μ q τ a γ : ℝ), μ ≠ 0 → 0 < q →
    IsSemiconjOn (ebSys1 (CNet.poisson μ) q (seirRxns τ a γ))
      (sSys (poissonRxns μ (seirRxns τ a γ))) Set.univ (piSlice μ q) ∧
    (∀ w : EB1 SEIRSp, 0 < piSlice μ q w none) ∧
    ∃ g : (DSp SEIRSp → ℝ) → EB1 SEIRSp,
      IsSemiconjOn (sSys (poissonRxns μ (seirRxns τ a γ)))
        (ebSys1 (CNet.poisson μ) q (seirRxns τ a γ)) (SPos SEIRSp) g ∧
      (∀ w : EB1 SEIRSp, g (piSlice μ q w) = w) ∧
      (∀ v ∈ SPos SEIRSp, piSlice μ q (g v) = v)

/-- S1: π is a semiconjugacy EB(SEIR) → MA(D_μ SEIR) on the whole EB space. -/
@[sa_shadow "MorphismsPoisson.poissonIsoSeir" 1]
def S1 : Prop :=
  ∀ (μ q τ a γ : ℝ), μ ≠ 0 → 0 < q →
    IsSemiconjOn (ebSys1 (CNet.poisson μ) q (seirRxns τ a γ))
      (sSys (poissonRxns μ (seirRxns τ a γ))) Set.univ (piSlice μ q)

/-- S2: π maps into `S > 0`. -/
@[sa_shadow "MorphismsPoisson.poissonIsoSeir" 2]
def S2 : Prop :=
  ∀ (μ q : ℝ), μ ≠ 0 → 0 < q → ∀ w : EB1 SEIRSp, 0 < piSlice μ q w none

/-- S3: π has a two-sided inverse on `S > 0` which is a semiconjugacy there. -/
@[sa_shadow "MorphismsPoisson.poissonIsoSeir" 3]
def S3 : Prop :=
  ∀ (μ q τ a γ : ℝ), μ ≠ 0 → 0 < q →
    ∃ g : (DSp SEIRSp → ℝ) → EB1 SEIRSp,
      IsSemiconjOn (sSys (poissonRxns μ (seirRxns τ a γ)))
        (ebSys1 (CNet.poisson μ) q (seirRxns τ a γ)) (SPos SEIRSp) g ∧
      (∀ w : EB1 SEIRSp, g (piSlice μ q w) = w) ∧
      (∀ v ∈ SPos SEIRSp, piSlice μ q (g v) = v)

@[sa_ref_forward "MorphismsPoisson.poissonIsoSeir" 1]
theorem ref_fwd1 : T → S1 := fun t μ q τ a γ hμ hq => (t μ q τ a γ hμ hq).1

@[sa_ref_forward "MorphismsPoisson.poissonIsoSeir" 2]
theorem ref_fwd2 : T → S2 := fun t μ q hμ hq => (t μ q 0 0 0 hμ hq).2.1

@[sa_ref_forward "MorphismsPoisson.poissonIsoSeir" 3]
theorem ref_fwd3 : T → S3 := fun t μ q τ a γ hμ hq => (t μ q τ a γ hμ hq).2.2

@[sa_complete "MorphismsPoisson.poissonIsoSeir"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T :=
  fun μ q τ a γ hμ hq => ⟨s1 μ q τ a γ hμ hq, s2 μ q hμ hq, s3 μ q τ a γ hμ hq⟩

end Alignment.Shadows.MorphismsPoisson.PoissonIsoSeir

/-! ## `MorphismsPoisson.poissonDLNone`, `poissonDLInl`, `poissonDLInr`

Texts: "The `S`-component of `poissonDL`: `q (v_ξ e^{μ(θ−1)} + ξ μ e^{μ(θ−1)} v_θ)`."; "The
`Φ_X`-component of `poissonDL` is `v_{φ_X}`."; "The node-copy `X`-component of `poissonDL` is
`v_{pop_X}`." Here `u = (θ, ξ, φ, pop)` is the base point and `v` the tangent vector, in `EB σ`. -/
namespace Alignment.Shadows.MorphismsPoisson.PoissonDLNone

@[sa_reference "MorphismsPoisson.poissonDLNone"]
def T : Prop :=
  ∀ {σ : Type} (μ q : ℝ) (u v : EB σ),
    poissonDL μ q u v none =
      q * (v.2.1 * Real.exp (μ * (u.1 - 1)) + u.2.1 * μ * Real.exp (μ * (u.1 - 1)) * v.1)

@[sa_shadow "MorphismsPoisson.poissonDLNone" 1]
def S1 : Prop :=
  ∀ {σ : Type} (μ q : ℝ) (u v : EB σ),
    poissonDL μ q u v none =
      q * (v.2.1 * Real.exp (μ * (u.1 - 1)) + u.2.1 * μ * Real.exp (μ * (u.1 - 1)) * v.1)

@[sa_ref_forward "MorphismsPoisson.poissonDLNone" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MorphismsPoisson.poissonDLNone"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MorphismsPoisson.PoissonDLNone

namespace Alignment.Shadows.MorphismsPoisson.PoissonDLInl

@[sa_reference "MorphismsPoisson.poissonDLInl"]
def T : Prop :=
  ∀ {σ : Type} (μ q : ℝ) (u v : EB σ) (X : σ), poissonDL μ q u v (some (Sum.inl X)) = v.2.2.1 X

@[sa_shadow "MorphismsPoisson.poissonDLInl" 1]
def S1 : Prop :=
  ∀ {σ : Type} (μ q : ℝ) (u v : EB σ) (X : σ), poissonDL μ q u v (some (Sum.inl X)) = v.2.2.1 X

@[sa_ref_forward "MorphismsPoisson.poissonDLInl" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MorphismsPoisson.poissonDLInl"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MorphismsPoisson.PoissonDLInl

namespace Alignment.Shadows.MorphismsPoisson.PoissonDLInr

@[sa_reference "MorphismsPoisson.poissonDLInr"]
def T : Prop :=
  ∀ {σ : Type} (μ q : ℝ) (u v : EB σ) (X : σ), poissonDL μ q u v (some (Sum.inr X)) = v.2.2.2 X

@[sa_shadow "MorphismsPoisson.poissonDLInr" 1]
def S1 : Prop :=
  ∀ {σ : Type} (μ q : ℝ) (u v : EB σ) (X : σ), poissonDL μ q u v (some (Sum.inr X)) = v.2.2.2 X

@[sa_ref_forward "MorphismsPoisson.poissonDLInr" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MorphismsPoisson.poissonDLInr"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MorphismsPoisson.PoissonDLInr

/-! ## `MorphismsPoisson.hasFDerivAtPoissonMap`

Text: "`poissonMap μ q` has derivative `poissonDL μ q u` at every `u`." No restriction on σ, μ, q. -/
namespace Alignment.Shadows.MorphismsPoisson.HasFDerivAtPoissonMap

@[sa_reference "MorphismsPoisson.hasFDerivAtPoissonMap"]
def T : Prop :=
  ∀ {σ : Type} (μ q : ℝ) (u : EB σ), HasFDerivAt (poissonMap μ q) (poissonDL μ q u) u

@[sa_shadow "MorphismsPoisson.hasFDerivAtPoissonMap" 1]
def S1 : Prop :=
  ∀ {σ : Type} (μ q : ℝ) (u : EB σ), HasFDerivAt (poissonMap μ q) (poissonDL μ q u) u

@[sa_ref_forward "MorphismsPoisson.hasFDerivAtPoissonMap" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MorphismsPoisson.hasFDerivAtPoissonMap"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MorphismsPoisson.HasFDerivAtPoissonMap

/-! ## `MorphismsPoisson.poissonEbField`

Text: "**Per-reaction identity behind M2.** On the Poisson(μ) network with `μ ≠ 0`, the derivative
of `poissonMap` carries the EB field of each T_EB reaction `r` to the multiset mass-action field of
`D_μ r` at the image point."

"The derivative of `poissonMap`" is taken literally as the Fréchet derivative `fderiv ℝ (poissonMap μ q) u`;
the EB field of `r` is `ebField (CNet.poisson μ) q r`; the multiset mass-action field of `D_μ r` is
`sLift (Rxn.poissonD μ r)`. Every seed factor `q` and every state `u`. -/
namespace Alignment.Shadows.MorphismsPoisson.PoissonEbField

@[sa_reference "MorphismsPoisson.poissonEbField"]
def T : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (μ q : ℝ) (r : Rxn σ) (u : EB σ), μ ≠ 0 →
    fderiv ℝ (poissonMap μ q) u (ebField (CNet.poisson μ) q r u) =
      sLift (Rxn.poissonD μ r) (poissonMap μ q u)

@[sa_shadow "MorphismsPoisson.poissonEbField" 1]
def S1 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (μ q : ℝ) (r : Rxn σ) (u : EB σ), μ ≠ 0 →
    fderiv ℝ (poissonMap μ q) u (ebField (CNet.poisson μ) q r u) =
      sLift (Rxn.poissonD μ r) (poissonMap μ q u)

@[sa_ref_forward "MorphismsPoisson.poissonEbField" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MorphismsPoisson.poissonEbField"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MorphismsPoisson.PoissonEbField

/-! ## `MorphismsPoisson.rxnPoissonDMap`

Text: "`D_μ` commutes with relabelling the node species of one reaction." -/
namespace Alignment.Shadows.MorphismsPoisson.RxnPoissonDMap

@[sa_reference "MorphismsPoisson.rxnPoissonDMap"]
def T : Prop :=
  ∀ {σ σ' : Type} (f : σ → σ') (μ : ℝ) (r : Rxn σ),
    Rxn.poissonD μ (r.map f) = (Rxn.poissonD μ r).map (SRxn.map (dMap f))

@[sa_shadow "MorphismsPoisson.rxnPoissonDMap" 1]
def S1 : Prop :=
  ∀ {σ σ' : Type} (f : σ → σ') (μ : ℝ) (r : Rxn σ),
    Rxn.poissonD μ (r.map f) = (Rxn.poissonD μ r).map (SRxn.map (dMap f))

@[sa_ref_forward "MorphismsPoisson.rxnPoissonDMap" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MorphismsPoisson.rxnPoissonDMap"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MorphismsPoisson.RxnPoissonDMap

/-! ## `MorphismsPoisson.sirRxnsNoExit`, `seirRxnsNoExit`

Texts: "SIR has no exits." / "SEIR has no exits." Written primitively: no reaction of the list is an
exit `s → Y`, for all rates. -/
namespace Alignment.Shadows.MorphismsPoisson.SirRxnsNoExit

@[sa_reference "MorphismsPoisson.sirRxnsNoExit"]
def T : Prop := ∀ τ γ : ℝ, ExitFree (sirRxns τ γ)

@[sa_shadow "MorphismsPoisson.sirRxnsNoExit" 1]
def S1 : Prop := ∀ τ γ : ℝ, ∀ r ∈ sirRxns τ γ, ∀ (Y : SIRSp) (ν : ℝ), r ≠ Rxn.exit Y ν

@[sa_ref_forward "MorphismsPoisson.sirRxnsNoExit" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MorphismsPoisson.sirRxnsNoExit"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MorphismsPoisson.SirRxnsNoExit

namespace Alignment.Shadows.MorphismsPoisson.SeirRxnsNoExit

@[sa_reference "MorphismsPoisson.seirRxnsNoExit"]
def T : Prop := ∀ τ a γ : ℝ, ExitFree (seirRxns τ a γ)

@[sa_shadow "MorphismsPoisson.seirRxnsNoExit" 1]
def S1 : Prop := ∀ τ a γ : ℝ, ∀ r ∈ seirRxns τ a γ, ∀ (Y : SEIRSp) (ν : ℝ), r ≠ Rxn.exit Y ν

@[sa_ref_forward "MorphismsPoisson.seirRxnsNoExit" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MorphismsPoisson.seirRxnsNoExit"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MorphismsPoisson.SeirRxnsNoExit
