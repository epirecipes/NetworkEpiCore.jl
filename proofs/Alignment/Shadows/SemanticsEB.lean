import Alignment.Registry
import NetworkEpi.Semantics.EB

/-!
# Blind shadow sets for group `SemanticsEB` (trusted module `NetworkEpi.Semantics.EB`)

Written blind (SA-PASS role 2). Files read: `SA-PASS_SKILL.md`, `Alignment/README.md`,
`Alignment/Example/ExampleShadows.lean`, `Alignment/DataTypes/SemanticsEB.md`, the `SemanticsEB`
entries of `Alignment/claims_blind.yaml` (regenerated with `scripts/sa_merge_claims.py`), and
`DESIGN_NetworkEpiCore.md` (§0, §D.1–§D.7, §J–§M). Re-shadow after text remediation (ids
`header.fieldTable`, `hasDerivWithinAtCompClm`, `hasDerivWithinAt{Theta,Xi,Phi,Pop}`,
`{edgeDefect,nodeTotal}DerivEbField`, `xiConst`, `conservation`): same reading rules. Only DataTypes vocabulary was `#check`ed.
No trusted source, no checker, no report and no claims registry other than the blind extract was
opened.

Conventions (DataTypes, module header): for `u : EB σ`, `θ = u.1`, `ξ = u.2.1`, `φ = u.2.2.1`,
`pop = u.2.2.2`. DESIGN §0: `S = qξψ(θ)`, `φ_S = qξψ'(θ)/ψ'(1)`. The notions of the text (φ_S, S,
the edge defect `θ − φ_S − Σ_X φ_X`, the node total `qξψ(θ) + Σ_X pop_X`, their directional
derivatives, the removal flux `Σ_{(X → ∅, a) ∈ rs} a φ_X`, pushforward along fibres and pullback)
are written out in primitive terms below, so the checks also test the trusted definitions.
A trusted operation is used directly only when the claim is *about* that operation by name
(`push`, `pushEB`, `removalFlux`, `edgeDefectDeriv`, `nodeTotalDeriv`, `ebField`, `lift`).

Finiteness of the species type is assumed (`[Fintype σ]`) only where a notion needs it (a sum over
all species, a pushforward along fibres); `HasDerivWithinAt` on `EB σ` needs no finiteness.
-- AMBIGUITY (all curve/solution claims): the text never restricts the species type; the design's
-- models have finitely many species, but the text's statements do not need it, so the shadows
-- quantify over every species type unless a sum over species occurs.
-/

open NEP

namespace Alignment.Shadows.SemanticsEB

noncomputable section

/-! ## Primitive notions shared by several claims -/

/-- `φ_S = qξψ'(θ)/ψ'(1)` (DESIGN §0), at the state `u`. -/
def PhiS (N : CNet) (q : ℝ) {σ : Type} (u : EB σ) : ℝ :=
  q * u.2.1 * N.ψ' u.1 / N.ψ' 1

/-- `S = qξψ(θ)` (DESIGN §0), at the state `u`. -/
def Susc (N : CNet) (q : ℝ) {σ : Type} (u : EB σ) : ℝ :=
  q * u.2.1 * N.ψ u.1

/-- The edge defect `θ − φ_S − Σ_X φ_X`. -/
def EdgeDef {σ : Type} [Fintype σ] (N : CNet) (q : ℝ) (u : EB σ) : ℝ :=
  u.1 - PhiS N q u - ∑ X, u.2.2.1 X

/-- The derivative of the edge defect at `u` in the direction `v`, by the chain rule with `ψ''`
standing for the derivative of `ψ'` at `θ = u.1`:
`v_θ − q(v_ξ ψ'(θ) + ξ ψ''(θ) v_θ)/ψ'(1) − Σ_X v_{φ,X}`. -/
def EdgeDefD {σ : Type} [Fintype σ] (N : CNet) (q : ℝ) (u v : EB σ) : ℝ :=
  v.1 - q * (v.2.1 * N.ψ' u.1 + u.2.1 * (N.ψ'' u.1 * v.1)) / N.ψ' 1 - ∑ X, v.2.2.1 X

/-- The node total `S + Σ_X pop_X = qξψ(θ) + Σ_X pop_X`. -/
def NodeTot {σ : Type} [Fintype σ] (N : CNet) (q : ℝ) (u : EB σ) : ℝ :=
  Susc N q u + ∑ X, u.2.2.2 X

/-- The derivative of the node total at `u` in the direction `v`, by the chain rule with `ψ'`
standing for the derivative of `ψ` at `θ = u.1`: `q(v_ξ ψ(θ) + ξ ψ'(θ) v_θ) + Σ_X v_{pop,X}`. -/
def NodeTotD {σ : Type} [Fintype σ] (N : CNet) (q : ℝ) (u v : EB σ) : ℝ :=
  q * (v.2.1 * N.ψ u.1 + u.2.1 * (N.ψ' u.1 * v.1)) + ∑ X, v.2.2.2 X

/-- The contribution `a v_X` of a removal `X → ∅` at rate `a`; `0` for every other reaction. -/
def RemRate {σ : Type} (v : σ → ℝ) : Rxn σ → ℝ
  | .trans X none a => a * v X
  | _ => 0

/-- The removal flux `Σ_{(X → ∅, a) ∈ rs} a v_X` of a reaction list (with multiplicity). -/
def RemFlux {σ : Type} (rs : List (Rxn σ)) (v : σ → ℝ) : ℝ :=
  (rs.map (RemRate v)).sum

/-- The reaction `r` is not a removal `X → ∅`. -/
def NotRemoval {σ : Type} (r : Rxn σ) : Prop :=
  ∀ (X : σ) (a : ℝ), r ≠ Rxn.trans X none a

/-- The reaction list has no removal `X → ∅`. -/
def NoRemoval {σ : Type} (rs : List (Rxn σ)) : Prop :=
  ∀ r ∈ rs, ∀ (X : σ) (a : ℝ), r ≠ Rxn.trans X none a

/-- The reaction list has no exit `s → Y`. -/
def NoExit {σ : Type} (rs : List (Rxn σ)) : Prop :=
  ∀ r ∈ rs, ∀ (Y : σ) (ν : ℝ), r ≠ Rxn.exit Y ν

/-- Sum of species-indexed coordinates over the fibre `f⁻¹(y)`. -/
def FibreSum {σ σ' : Type} [Fintype σ] [DecidableEq σ'] (f : σ → σ') (v : σ → ℝ) (y : σ') : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x => f x = y), v x

/-- Pushforward of EB coordinates along a species map, in primitive terms: `θ`, `ξ` kept (the
susceptible species is glued to itself), `φ` and `pop` summed over fibres. -/
def PushF {σ σ' : Type} [Fintype σ] [DecidableEq σ'] (f : σ → σ') (u : EB σ) : EB σ' :=
  (u.1, u.2.1, FibreSum f u.2.2.1, FibreSum f u.2.2.2)

/-- Pullback of EB coordinates along a species map (identification of ported coordinates):
`θ`, `ξ` kept, `φ` and `pop` precomposed with the map. -/
def PullF {σ σ' : Type} (f : σ → σ') (u : EB σ') : EB σ :=
  (u.1, u.2.1, fun x => u.2.2.1 (f x), fun x => u.2.2.2 (f x))

end

end Alignment.Shadows.SemanticsEB

/-! ## `SemanticsEB.header.fieldTable` (re-shadowed; statement unchanged after re-reading the text)

Text: the per-reaction table (contact / transition / exit rows, initial condition row) and
"`ebField N q r u` is exactly this contribution of reaction `r` at state `u`, and `lift N q rs u`
is the sum of the contributions of the reactions in the list `rs`."

Reading: `+=` lists the contribution of the reaction to a coordinate; a coordinate that the row
does not list receives no contribution (0). "φ̇_X −= aφ_X" is the contribution `−(aφ_X)`.
Contributions to the same coordinate add (e.g. `J = X` for a contact, `X = Y` for a transition),
hence `Pi.single … + Pi.single …`. φ_S and S are the DESIGN §0 formulas.
-- AMBIGUITY: "initial condition: θ(0) = 1, ξ(0) = 1, φ_X(0) = pop_X(0) = ρ_X" is a row of the
-- quoted table but not a contribution of a reaction, and the closing sentence claims only that
-- `ebField`/`lift` are the contributions; the initial condition is not a Lean object (DataTypes
-- §(d)), so it is not formalised here.
-/

namespace Alignment.Shadows.SemanticsEB.FieldTable

open Alignment.Shadows.SemanticsEB

/-- Intended statement: `ebField` is the table's contribution for each reaction form, and `lift`
is the sum of the per-reaction contributions. -/
@[sa_reference "SemanticsEB.header.fieldTable"]
def T : Prop :=
  (∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (J X : σ) (τ : ℝ) (u : EB σ),
      ebField N q (Rxn.contact J X τ) u =
        (-(τ * u.2.2.1 J), 0,
          Pi.single J (-(τ * u.2.2.1 J)) +
            Pi.single X (τ * u.2.2.1 J * (q * u.2.1 * N.ψ'' u.1 / N.ψ' 1)),
          Pi.single X (τ * u.2.2.1 J * (q * u.2.1 * N.ψ' u.1)))) ∧
  (∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (X Y : σ) (a : ℝ) (u : EB σ),
      ebField N q (Rxn.trans X (some Y) a) u =
        (0, 0, Pi.single X (-(a * u.2.2.1 X)) + Pi.single Y (a * u.2.2.1 X),
          Pi.single X (-(a * u.2.2.2 X)) + Pi.single Y (a * u.2.2.2 X))) ∧
  (∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (X : σ) (a : ℝ) (u : EB σ),
      ebField N q (Rxn.trans X none a) u =
        (0, 0, Pi.single X (-(a * u.2.2.1 X)), Pi.single X (-(a * u.2.2.2 X)))) ∧
  (∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (Y : σ) (ν : ℝ) (u : EB σ),
      ebField N q (Rxn.exit Y ν) u =
        (0, -(ν * u.2.1), Pi.single Y (ν * PhiS N q u), Pi.single Y (ν * Susc N q u))) ∧
  (∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)) (u : EB σ),
      lift N q rs u = (rs.map (fun r => ebField N q r u)).sum)

/-- S1: contact, θ-component `−τφ_J`. -/
@[sa_shadow "SemanticsEB.header.fieldTable" 1]
def S1 : Prop := ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (J X : σ) (τ : ℝ) (u : EB σ),
  (ebField N q (Rxn.contact J X τ) u).1 = -(τ * u.2.2.1 J)

/-- S2: contact, no ξ-contribution. -/
@[sa_shadow "SemanticsEB.header.fieldTable" 2]
def S2 : Prop := ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (J X : σ) (τ : ℝ) (u : EB σ),
  (ebField N q (Rxn.contact J X τ) u).2.1 = 0

/-- S3: contact, φ-component: `−τφ_J` at `J` plus `τφ_J·qξψ''(θ)/ψ'(1)` at `X`. -/
@[sa_shadow "SemanticsEB.header.fieldTable" 3]
def S3 : Prop := ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (J X : σ) (τ : ℝ) (u : EB σ),
  (ebField N q (Rxn.contact J X τ) u).2.2.1 =
    Pi.single J (-(τ * u.2.2.1 J)) +
      Pi.single X (τ * u.2.2.1 J * (q * u.2.1 * N.ψ'' u.1 / N.ψ' 1))

/-- S4: contact, pop-component: `τφ_J·qξψ'(θ)` at `X`. -/
@[sa_shadow "SemanticsEB.header.fieldTable" 4]
def S4 : Prop := ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (J X : σ) (τ : ℝ) (u : EB σ),
  (ebField N q (Rxn.contact J X τ) u).2.2.2 =
    Pi.single X (τ * u.2.2.1 J * (q * u.2.1 * N.ψ' u.1))

/-- S5: transition `X → Y`, no θ-contribution. -/
@[sa_shadow "SemanticsEB.header.fieldTable" 5]
def S5 : Prop := ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (X Y : σ) (a : ℝ) (u : EB σ),
  (ebField N q (Rxn.trans X (some Y) a) u).1 = 0

/-- S6: transition `X → Y`, no ξ-contribution. -/
@[sa_shadow "SemanticsEB.header.fieldTable" 6]
def S6 : Prop := ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (X Y : σ) (a : ℝ) (u : EB σ),
  (ebField N q (Rxn.trans X (some Y) a) u).2.1 = 0

/-- S7: transition `X → Y`, φ-component: `−aφ_X` at `X`, `+aφ_X` at `Y`. -/
@[sa_shadow "SemanticsEB.header.fieldTable" 7]
def S7 : Prop := ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (X Y : σ) (a : ℝ) (u : EB σ),
  (ebField N q (Rxn.trans X (some Y) a) u).2.2.1 =
    Pi.single X (-(a * u.2.2.1 X)) + Pi.single Y (a * u.2.2.1 X)

/-- S8: transition `X → Y`, pop-component: `−a pop_X` at `X`, `+a pop_X` at `Y`. -/
@[sa_shadow "SemanticsEB.header.fieldTable" 8]
def S8 : Prop := ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (X Y : σ) (a : ℝ) (u : EB σ),
  (ebField N q (Rxn.trans X (some Y) a) u).2.2.2 =
    Pi.single X (-(a * u.2.2.2 X)) + Pi.single Y (a * u.2.2.2 X)

/-- S9: removal `X → ∅`, no θ-contribution. -/
@[sa_shadow "SemanticsEB.header.fieldTable" 9]
def S9 : Prop := ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (X : σ) (a : ℝ) (u : EB σ),
  (ebField N q (Rxn.trans X none a) u).1 = 0

/-- S10: removal `X → ∅`, no ξ-contribution. -/
@[sa_shadow "SemanticsEB.header.fieldTable" 10]
def S10 : Prop := ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (X : σ) (a : ℝ) (u : EB σ),
  (ebField N q (Rxn.trans X none a) u).2.1 = 0

/-- S11: removal `X → ∅`, φ-component: `−aφ_X` at `X`, no gain. -/
@[sa_shadow "SemanticsEB.header.fieldTable" 11]
def S11 : Prop := ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (X : σ) (a : ℝ) (u : EB σ),
  (ebField N q (Rxn.trans X none a) u).2.2.1 = Pi.single X (-(a * u.2.2.1 X))

/-- S12: removal `X → ∅`, pop-component: `−a pop_X` at `X`, no gain. -/
@[sa_shadow "SemanticsEB.header.fieldTable" 12]
def S12 : Prop := ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (X : σ) (a : ℝ) (u : EB σ),
  (ebField N q (Rxn.trans X none a) u).2.2.2 = Pi.single X (-(a * u.2.2.2 X))

/-- S13: exit `s → Y`, no θ-contribution. -/
@[sa_shadow "SemanticsEB.header.fieldTable" 13]
def S13 : Prop := ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (Y : σ) (ν : ℝ) (u : EB σ),
  (ebField N q (Rxn.exit Y ν) u).1 = 0

/-- S14: exit `s → Y`, ξ-component `−νξ`. -/
@[sa_shadow "SemanticsEB.header.fieldTable" 14]
def S14 : Prop := ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (Y : σ) (ν : ℝ) (u : EB σ),
  (ebField N q (Rxn.exit Y ν) u).2.1 = -(ν * u.2.1)

/-- S15: exit `s → Y`, φ-component `νφ_S` at `Y`, with `φ_S = qξψ'(θ)/ψ'(1)`. -/
@[sa_shadow "SemanticsEB.header.fieldTable" 15]
def S15 : Prop := ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (Y : σ) (ν : ℝ) (u : EB σ),
  (ebField N q (Rxn.exit Y ν) u).2.2.1 = Pi.single Y (ν * PhiS N q u)

/-- S16: exit `s → Y`, pop-component `νS` at `Y`, with `S = qξψ(θ)`. -/
@[sa_shadow "SemanticsEB.header.fieldTable" 16]
def S16 : Prop := ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (Y : σ) (ν : ℝ) (u : EB σ),
  (ebField N q (Rxn.exit Y ν) u).2.2.2 = Pi.single Y (ν * Susc N q u)

/-- S17: `lift N q rs u` is the sum of the per-reaction contributions. -/
@[sa_shadow "SemanticsEB.header.fieldTable" 17]
def S17 : Prop := ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)) (u : EB σ),
  lift N q rs u = (rs.map (fun r => ebField N q r u)).sum

@[sa_ref_forward "SemanticsEB.header.fieldTable" 1]
theorem ref_fwd1 : T → S1 := by
  intro t σ _ N q J X τ u; rw [t.1 N q J X τ u]
@[sa_ref_forward "SemanticsEB.header.fieldTable" 2]
theorem ref_fwd2 : T → S2 := by
  intro t σ _ N q J X τ u; rw [t.1 N q J X τ u]
@[sa_ref_forward "SemanticsEB.header.fieldTable" 3]
theorem ref_fwd3 : T → S3 := by
  intro t σ _ N q J X τ u; rw [t.1 N q J X τ u]
@[sa_ref_forward "SemanticsEB.header.fieldTable" 4]
theorem ref_fwd4 : T → S4 := by
  intro t σ _ N q J X τ u; rw [t.1 N q J X τ u]
@[sa_ref_forward "SemanticsEB.header.fieldTable" 5]
theorem ref_fwd5 : T → S5 := by
  intro t σ _ N q X Y a u; rw [t.2.1 N q X Y a u]
@[sa_ref_forward "SemanticsEB.header.fieldTable" 6]
theorem ref_fwd6 : T → S6 := by
  intro t σ _ N q X Y a u; rw [t.2.1 N q X Y a u]
@[sa_ref_forward "SemanticsEB.header.fieldTable" 7]
theorem ref_fwd7 : T → S7 := by
  intro t σ _ N q X Y a u; rw [t.2.1 N q X Y a u]
@[sa_ref_forward "SemanticsEB.header.fieldTable" 8]
theorem ref_fwd8 : T → S8 := by
  intro t σ _ N q X Y a u; rw [t.2.1 N q X Y a u]
@[sa_ref_forward "SemanticsEB.header.fieldTable" 9]
theorem ref_fwd9 : T → S9 := by
  intro t σ _ N q X a u; rw [t.2.2.1 N q X a u]
@[sa_ref_forward "SemanticsEB.header.fieldTable" 10]
theorem ref_fwd10 : T → S10 := by
  intro t σ _ N q X a u; rw [t.2.2.1 N q X a u]
@[sa_ref_forward "SemanticsEB.header.fieldTable" 11]
theorem ref_fwd11 : T → S11 := by
  intro t σ _ N q X a u; rw [t.2.2.1 N q X a u]
@[sa_ref_forward "SemanticsEB.header.fieldTable" 12]
theorem ref_fwd12 : T → S12 := by
  intro t σ _ N q X a u; rw [t.2.2.1 N q X a u]
@[sa_ref_forward "SemanticsEB.header.fieldTable" 13]
theorem ref_fwd13 : T → S13 := by
  intro t σ _ N q Y ν u; rw [t.2.2.2.1 N q Y ν u]
@[sa_ref_forward "SemanticsEB.header.fieldTable" 14]
theorem ref_fwd14 : T → S14 := by
  intro t σ _ N q Y ν u; rw [t.2.2.2.1 N q Y ν u]
@[sa_ref_forward "SemanticsEB.header.fieldTable" 15]
theorem ref_fwd15 : T → S15 := by
  intro t σ _ N q Y ν u; rw [t.2.2.2.1 N q Y ν u]
@[sa_ref_forward "SemanticsEB.header.fieldTable" 16]
theorem ref_fwd16 : T → S16 := by
  intro t σ _ N q Y ν u; rw [t.2.2.2.1 N q Y ν u]
@[sa_ref_forward "SemanticsEB.header.fieldTable" 17]
theorem ref_fwd17 : T → S17 := by
  intro t σ _ N q rs u; exact t.2.2.2.2 N q rs u

@[sa_complete "SemanticsEB.header.fieldTable"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) (s7 : S7)
    (s8 : S8) (s9 : S9) (s10 : S10) (s11 : S11) (s12 : S12) (s13 : S13) (s14 : S14)
    (s15 : S15) (s16 : S16) (s17 : S17) : T := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro σ _ N q J X τ u
    exact Prod.ext (s1 N q J X τ u) (Prod.ext (s2 N q J X τ u)
      (Prod.ext (s3 N q J X τ u) (s4 N q J X τ u)))
  · intro σ _ N q X Y a u
    exact Prod.ext (s5 N q X Y a u) (Prod.ext (s6 N q X Y a u)
      (Prod.ext (s7 N q X Y a u) (s8 N q X Y a u)))
  · intro σ _ N q X a u
    exact Prod.ext (s9 N q X a u) (Prod.ext (s10 N q X a u)
      (Prod.ext (s11 N q X a u) (s12 N q X a u)))
  · intro σ _ N q Y ν u
    exact Prod.ext (s13 N q Y ν u) (Prod.ext (s14 N q Y ν u)
      (Prod.ext (s15 N q Y ν u) (s16 N q Y ν u)))
  · intro σ _ N q rs u
    exact s17 N q rs u

end Alignment.Shadows.SemanticsEB.FieldTable

/-! ## `SemanticsEB.liftAppend`

Text (four docstrings): H1 part 1, "the EB lift is additive in the reaction list"; naturality of
the per-reaction EB field in species maps ("`ebField_map` ... relabelling/gluing naturality with
pushforward along fibres"); H1 part 2, "the EB lift is natural in species maps (relabelling and
gluing)" "with the exit case included"; H1, "the EB lift is strict under gluing":
"EB(glue(A,B)) = glue(EB A, EB B), for fixed N with s glued to s", and (§D.3, open systems)
"composition identifies ported coordinates and **adds** vector fields".

Reading. Gluing on the syntax: relabel along the cospan legs and concatenate (DataTypes §(d),
DESIGN §D.2 "concatenation of reaction lists"). The open-systems composite field at a glued state
`u` is: identify ported coordinates (pull `u` back along each leg), evaluate each component's
field, push each result forward along its leg (sum over fibres), and add. Naturality "with
pushforward along fibres" of a field `F_r` in the species map `f` is therefore
`F_{f(r)}(u) = f_*(F_r(f^* u))`, with `s` glued to `s` (θ, ξ kept by `f_*` and `f^*`).
-- AMBIGUITY: "natural in species maps" could be read as a semiconjugacy `f_*`
-- (`F_{f(r)}(f_* u) = f_*(F_r u)`); that reading fails for non-injective `f` (after gluing, a
-- contact's rate uses the summed φ of the fibre), so the design's "gluing naturality with
-- pushforward along fibres" is read with the pullback of the state, as in resource-sharer
-- composition (§D.3). All reactions, including exits, are covered ("with the exit case included").
-/

namespace Alignment.Shadows.SemanticsEB.LiftAppend

open Alignment.Shadows.SemanticsEB

/-- Intended statement: additivity in the reaction list, per-reaction and list naturality in
species maps (pushforward along fibres), and strictness under gluing along a cospan. -/
@[sa_reference "SemanticsEB.liftAppend"]
def T : Prop :=
  (∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (rs rs' : List (Rxn σ)) (u : EB σ),
      lift N q (rs ++ rs') u = lift N q rs u + lift N q rs' u) ∧
  (∀ {σ σ' : Type} [DecidableEq σ] [Fintype σ] [DecidableEq σ'] (N : CNet) (q : ℝ)
      (f : σ → σ') (r : Rxn σ) (u : EB σ'),
      ebField N q (Rxn.map f r) u = PushF f (ebField N q r (PullF f u))) ∧
  (∀ {σ σ' : Type} [DecidableEq σ] [Fintype σ] [DecidableEq σ'] (N : CNet) (q : ℝ)
      (f : σ → σ') (rs : List (Rxn σ)) (u : EB σ'),
      lift N q (rs.map (Rxn.map f)) u = PushF f (lift N q rs (PullF f u))) ∧
  (∀ {σA σB σ : Type} [DecidableEq σA] [Fintype σA] [DecidableEq σB] [Fintype σB]
      [DecidableEq σ] (N : CNet) (q : ℝ) (f : σA → σ) (g : σB → σ)
      (A : List (Rxn σA)) (B : List (Rxn σB)) (u : EB σ),
      lift N q (A.map (Rxn.map f) ++ B.map (Rxn.map g)) u =
        PushF f (lift N q A (PullF f u)) + PushF g (lift N q B (PullF g u)))

/-- S1 (H1 part 1): the lift of a concatenation is the sum of the lifts. -/
@[sa_shadow "SemanticsEB.liftAppend" 1]
def S1 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (rs rs' : List (Rxn σ)) (u : EB σ),
    lift N q (rs ++ rs') u = lift N q rs u + lift N q rs' u

/-- S2 (per-reaction naturality): the field of the relabelled reaction at `u` is the
pushforward along fibres of the original field at the pulled-back state. -/
@[sa_shadow "SemanticsEB.liftAppend" 2]
def S2 : Prop :=
  ∀ {σ σ' : Type} [DecidableEq σ] [Fintype σ] [DecidableEq σ'] (N : CNet) (q : ℝ)
    (f : σ → σ') (r : Rxn σ) (u : EB σ'),
    ebField N q (Rxn.map f r) u = PushF f (ebField N q r (PullF f u))

/-- S3 (H1 part 2): the same naturality for the lift of a reaction list. -/
@[sa_shadow "SemanticsEB.liftAppend" 3]
def S3 : Prop :=
  ∀ {σ σ' : Type} [DecidableEq σ] [Fintype σ] [DecidableEq σ'] (N : CNet) (q : ℝ)
    (f : σ → σ') (rs : List (Rxn σ)) (u : EB σ'),
    lift N q (rs.map (Rxn.map f)) u = PushF f (lift N q rs (PullF f u))

/-- S4 (H1, strict under gluing): the lift of `glue(A, B)` along a cospan `f, g` is the
open-systems composite of the two lifts (identify ported coordinates, add the fields). -/
@[sa_shadow "SemanticsEB.liftAppend" 4]
def S4 : Prop :=
  ∀ {σA σB σ : Type} [DecidableEq σA] [Fintype σA] [DecidableEq σB] [Fintype σB]
    [DecidableEq σ] (N : CNet) (q : ℝ) (f : σA → σ) (g : σB → σ)
    (A : List (Rxn σA)) (B : List (Rxn σB)) (u : EB σ),
    lift N q (A.map (Rxn.map f) ++ B.map (Rxn.map g)) u =
      PushF f (lift N q A (PullF f u)) + PushF g (lift N q B (PullF g u))

@[sa_ref_forward "SemanticsEB.liftAppend" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "SemanticsEB.liftAppend" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "SemanticsEB.liftAppend" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "SemanticsEB.liftAppend" 4]
theorem ref_fwd4 : T → S4 := fun t => t.2.2.2

@[sa_complete "SemanticsEB.liftAppend"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.SemanticsEB.LiftAppend

/-! ## Pushforward algebra: `SemanticsEB.pushSingle`, `pushAdd`, `pushNeg`, `pushSub`,
`pushZero`, `pushEBAdd`, `pushEBZero`

Each text is one equation about the trusted operation it names (`push`, `pushEB`), for every
species map `f`. -/

namespace Alignment.Shadows.SemanticsEB.PushSingle

/-- Text: "The pushforward of `Pi.single X c` is `Pi.single (f X) c`." -/
@[sa_reference "SemanticsEB.pushSingle"]
def T : Prop := ∀ {σ σ' : Type} [Fintype σ] [DecidableEq σ] [DecidableEq σ'] (f : σ → σ')
  (X : σ) (c : ℝ), push f (Pi.single X c) = Pi.single (f X) c
@[sa_shadow "SemanticsEB.pushSingle" 1]
def S1 : Prop := ∀ {σ σ' : Type} [Fintype σ] [DecidableEq σ] [DecidableEq σ'] (f : σ → σ')
  (X : σ) (c : ℝ), push f (Pi.single X c) = Pi.single (f X) c
@[sa_ref_forward "SemanticsEB.pushSingle" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SemanticsEB.pushSingle"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SemanticsEB.PushSingle

namespace Alignment.Shadows.SemanticsEB.PushAdd

/-- Text: "The pushforward is additive." -/
@[sa_reference "SemanticsEB.pushAdd"]
def T : Prop := ∀ {σ σ' : Type} [Fintype σ] [DecidableEq σ'] (f : σ → σ') (v w : σ → ℝ),
  push f (v + w) = push f v + push f w
@[sa_shadow "SemanticsEB.pushAdd" 1]
def S1 : Prop := ∀ {σ σ' : Type} [Fintype σ] [DecidableEq σ'] (f : σ → σ') (v w : σ → ℝ),
  push f (v + w) = push f v + push f w
@[sa_ref_forward "SemanticsEB.pushAdd" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SemanticsEB.pushAdd"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SemanticsEB.PushAdd

namespace Alignment.Shadows.SemanticsEB.PushNeg

/-- Text: "The pushforward commutes with negation." -/
@[sa_reference "SemanticsEB.pushNeg"]
def T : Prop := ∀ {σ σ' : Type} [Fintype σ] [DecidableEq σ'] (f : σ → σ') (v : σ → ℝ),
  push f (-v) = -push f v
@[sa_shadow "SemanticsEB.pushNeg" 1]
def S1 : Prop := ∀ {σ σ' : Type} [Fintype σ] [DecidableEq σ'] (f : σ → σ') (v : σ → ℝ),
  push f (-v) = -push f v
@[sa_ref_forward "SemanticsEB.pushNeg" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SemanticsEB.pushNeg"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SemanticsEB.PushNeg

namespace Alignment.Shadows.SemanticsEB.PushSub

/-- Text: "The pushforward commutes with subtraction." -/
@[sa_reference "SemanticsEB.pushSub"]
def T : Prop := ∀ {σ σ' : Type} [Fintype σ] [DecidableEq σ'] (f : σ → σ') (v w : σ → ℝ),
  push f (v - w) = push f v - push f w
@[sa_shadow "SemanticsEB.pushSub" 1]
def S1 : Prop := ∀ {σ σ' : Type} [Fintype σ] [DecidableEq σ'] (f : σ → σ') (v w : σ → ℝ),
  push f (v - w) = push f v - push f w
@[sa_ref_forward "SemanticsEB.pushSub" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SemanticsEB.pushSub"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SemanticsEB.PushSub

namespace Alignment.Shadows.SemanticsEB.PushZero

/-- Text: "The pushforward of zero is zero." -/
@[sa_reference "SemanticsEB.pushZero"]
def T : Prop := ∀ {σ σ' : Type} [Fintype σ] [DecidableEq σ'] (f : σ → σ'),
  push f (0 : σ → ℝ) = 0
@[sa_shadow "SemanticsEB.pushZero" 1]
def S1 : Prop := ∀ {σ σ' : Type} [Fintype σ] [DecidableEq σ'] (f : σ → σ'),
  push f (0 : σ → ℝ) = 0
@[sa_ref_forward "SemanticsEB.pushZero" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SemanticsEB.pushZero"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SemanticsEB.PushZero

namespace Alignment.Shadows.SemanticsEB.PushEBAdd

/-- Text: "The pushforward of EB coordinates is additive." -/
@[sa_reference "SemanticsEB.pushEBAdd"]
def T : Prop := ∀ {σ σ' : Type} [Fintype σ] [DecidableEq σ'] (f : σ → σ') (u w : EB σ),
  pushEB f (u + w) = pushEB f u + pushEB f w
@[sa_shadow "SemanticsEB.pushEBAdd" 1]
def S1 : Prop := ∀ {σ σ' : Type} [Fintype σ] [DecidableEq σ'] (f : σ → σ') (u w : EB σ),
  pushEB f (u + w) = pushEB f u + pushEB f w
@[sa_ref_forward "SemanticsEB.pushEBAdd" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SemanticsEB.pushEBAdd"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SemanticsEB.PushEBAdd

namespace Alignment.Shadows.SemanticsEB.PushEBZero

/-- Text: "The pushforward of the zero EB vector is zero." -/
@[sa_reference "SemanticsEB.pushEBZero"]
def T : Prop := ∀ {σ σ' : Type} [Fintype σ] [DecidableEq σ'] (f : σ → σ'),
  pushEB f (0 : EB σ) = 0
@[sa_shadow "SemanticsEB.pushEBZero" 1]
def S1 : Prop := ∀ {σ σ' : Type} [Fintype σ] [DecidableEq σ'] (f : σ → σ'),
  pushEB f (0 : EB σ) = 0
@[sa_ref_forward "SemanticsEB.pushEBZero" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SemanticsEB.pushEBZero"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SemanticsEB.PushEBZero

/-! ## `SemanticsEB.removalFluxEqZero`

Text: "Without removals `X → ∅` the removal flux vanishes." The claim is about the named
operation `removalFlux`; "without removals" is written in primitive terms (no reaction of the
list is `trans X none a`), for every coordinate vector `v`. -/

namespace Alignment.Shadows.SemanticsEB.RemovalFluxEqZero

open Alignment.Shadows.SemanticsEB

@[sa_reference "SemanticsEB.removalFluxEqZero"]
def T : Prop := ∀ {σ : Type} (rs : List (Rxn σ)) (v : σ → ℝ),
  NoRemoval rs → removalFlux rs v = 0
@[sa_shadow "SemanticsEB.removalFluxEqZero" 1]
def S1 : Prop := ∀ {σ : Type} (rs : List (Rxn σ)) (v : σ → ℝ),
  NoRemoval rs → removalFlux rs v = 0
@[sa_ref_forward "SemanticsEB.removalFluxEqZero" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SemanticsEB.removalFluxEqZero"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SemanticsEB.RemovalFluxEqZero

/-! ## `SemanticsEB.sumSingle`

Text: "The sum over all species of `Pi.single X c` is `c`." The text is itself arithmetic (a
finite sum over the species type), so the shadow mentions no trusted constant: it is expected to
be flagged `shadow_trusted_free` and needs an independent `sa_shadow_reviewed` record. -/

namespace Alignment.Shadows.SemanticsEB.SumSingle

@[sa_reference "SemanticsEB.sumSingle"]
def T : Prop := ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (X : σ) (c : ℝ),
  ∑ Y, (Pi.single X c : σ → ℝ) Y = c
@[sa_shadow "SemanticsEB.sumSingle" 1]
def S1 : Prop := ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (X : σ) (c : ℝ),
  ∑ Y, (Pi.single X c : σ → ℝ) Y = c
@[sa_ref_forward "SemanticsEB.sumSingle" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SemanticsEB.sumSingle"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SemanticsEB.SumSingle

/-! ## `SemanticsEB.hasDerivWithinAtCompClm` (re-shadowed)

Text: "Chain rule for a continuous linear map applied to a curve, within a set of times."
Reading: a continuous linear map `L`, a curve `x` with derivative `x'` within a set of times `I`
at a time `t`; then `L ∘ x` has derivative `L x'` within `I` at `t`. Every set `I`, every `t`.
-- AMBIGUITY: "a curve" is not given a state space. Reading (a), in the module's context (the EB
-- module's curves are `x : ℝ → EB σ`, DataTypes): `L : EB σ →L[ℝ] F` for every species type `σ`
-- and every real normed space `F` (shadow S1, mentions `EB`). Reading (b), literal and general:
-- a curve in any real normed space `E` (shadow S2). Both are required (T = S1 ∧ S2, equivalent to
-- S2). S2 is pure calculus and mentions no trusted constant: expected flag `shadow_trusted_free`,
-- to be lifted only by an independent review record (the text itself is calculus).
-/

namespace Alignment.Shadows.SemanticsEB.HasDerivWithinAtCompClm

/-- Reading (a): curves in the EB state space `EB σ`, any real normed target `F`. -/
def ChainEB : Prop :=
  ∀ {σ : Type} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : EB σ →L[ℝ] F) (x : ℝ → EB σ) (x' : EB σ) (I : Set ℝ) (t : ℝ),
    HasDerivWithinAt x x' I t → HasDerivWithinAt (fun s => L (x s)) (L x') I t

/-- Reading (b): curves in any real normed space `E`. -/
def ChainGen : Prop :=
  ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L : E →L[ℝ] F) (x : ℝ → E) (x' : E) (I : Set ℝ) (t : ℝ),
    HasDerivWithinAt x x' I t → HasDerivWithinAt (fun s => L (x s)) (L x') I t

@[sa_reference "SemanticsEB.hasDerivWithinAtCompClm"]
def T : Prop := ChainEB ∧ ChainGen

/-- S1: the chain rule for curves in `EB σ` (reading (a)). -/
@[sa_shadow "SemanticsEB.hasDerivWithinAtCompClm" 1]
def S1 : Prop := ChainEB

/-- S2: the chain rule for curves in any real normed space (reading (b)). -/
@[sa_shadow "SemanticsEB.hasDerivWithinAtCompClm" 2]
def S2 : Prop := ChainGen

@[sa_ref_forward "SemanticsEB.hasDerivWithinAtCompClm" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "SemanticsEB.hasDerivWithinAtCompClm" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "SemanticsEB.hasDerivWithinAtCompClm"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.SemanticsEB.HasDerivWithinAtCompClm

/-! ## Coordinates of a curve in `EB σ`: `SemanticsEB.hasDerivWithinAtTheta`, `…Xi`, `…Phi`,
`…Pop` (re-shadowed)

Texts: "The θ-coordinate (ξ-, each φ-, each pop-coordinate) of a curve has, within `I`, the
θ-coordinate (…) of its derivative." Reading: for every species type `σ`, every curve
`x : ℝ → EB σ` (module convention `θ = u.1`, `ξ = u.2.1`, `φ = u.2.2.1`, `pop = u.2.2.2`), every set
of times `I` and time `t`: if `x` has derivative `x'` within `I` at `t`, then the coordinate curve
has the corresponding coordinate of `x'` as derivative within `I` at `t` ("each" φ/pop coordinate:
for every species `X`). Each text is a single implication: one shadow each. -/

namespace Alignment.Shadows.SemanticsEB.HasDerivWithinAtTheta

@[sa_reference "SemanticsEB.hasDerivWithinAtTheta"]
def T : Prop := ∀ {σ : Type} (x : ℝ → EB σ) (x' : EB σ) (I : Set ℝ) (t : ℝ),
  HasDerivWithinAt x x' I t → HasDerivWithinAt (fun s => (x s).1) x'.1 I t
@[sa_shadow "SemanticsEB.hasDerivWithinAtTheta" 1]
def S1 : Prop := ∀ {σ : Type} (x : ℝ → EB σ) (x' : EB σ) (I : Set ℝ) (t : ℝ),
  HasDerivWithinAt x x' I t → HasDerivWithinAt (fun s => (x s).1) x'.1 I t
@[sa_ref_forward "SemanticsEB.hasDerivWithinAtTheta" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SemanticsEB.hasDerivWithinAtTheta"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SemanticsEB.HasDerivWithinAtTheta

namespace Alignment.Shadows.SemanticsEB.HasDerivWithinAtXi

@[sa_reference "SemanticsEB.hasDerivWithinAtXi"]
def T : Prop := ∀ {σ : Type} (x : ℝ → EB σ) (x' : EB σ) (I : Set ℝ) (t : ℝ),
  HasDerivWithinAt x x' I t → HasDerivWithinAt (fun s => (x s).2.1) x'.2.1 I t
@[sa_shadow "SemanticsEB.hasDerivWithinAtXi" 1]
def S1 : Prop := ∀ {σ : Type} (x : ℝ → EB σ) (x' : EB σ) (I : Set ℝ) (t : ℝ),
  HasDerivWithinAt x x' I t → HasDerivWithinAt (fun s => (x s).2.1) x'.2.1 I t
@[sa_ref_forward "SemanticsEB.hasDerivWithinAtXi" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SemanticsEB.hasDerivWithinAtXi"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SemanticsEB.HasDerivWithinAtXi

namespace Alignment.Shadows.SemanticsEB.HasDerivWithinAtPhi

@[sa_reference "SemanticsEB.hasDerivWithinAtPhi"]
def T : Prop := ∀ {σ : Type} (x : ℝ → EB σ) (x' : EB σ) (I : Set ℝ) (t : ℝ) (X : σ),
  HasDerivWithinAt x x' I t → HasDerivWithinAt (fun s => (x s).2.2.1 X) (x'.2.2.1 X) I t
@[sa_shadow "SemanticsEB.hasDerivWithinAtPhi" 1]
def S1 : Prop := ∀ {σ : Type} (x : ℝ → EB σ) (x' : EB σ) (I : Set ℝ) (t : ℝ) (X : σ),
  HasDerivWithinAt x x' I t → HasDerivWithinAt (fun s => (x s).2.2.1 X) (x'.2.2.1 X) I t
@[sa_ref_forward "SemanticsEB.hasDerivWithinAtPhi" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SemanticsEB.hasDerivWithinAtPhi"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SemanticsEB.HasDerivWithinAtPhi

namespace Alignment.Shadows.SemanticsEB.HasDerivWithinAtPop

@[sa_reference "SemanticsEB.hasDerivWithinAtPop"]
def T : Prop := ∀ {σ : Type} (x : ℝ → EB σ) (x' : EB σ) (I : Set ℝ) (t : ℝ) (X : σ),
  HasDerivWithinAt x x' I t → HasDerivWithinAt (fun s => (x s).2.2.2 X) (x'.2.2.2 X) I t
@[sa_shadow "SemanticsEB.hasDerivWithinAtPop" 1]
def S1 : Prop := ∀ {σ : Type} (x : ℝ → EB σ) (x' : EB σ) (I : Set ℝ) (t : ℝ) (X : σ),
  HasDerivWithinAt x x' I t → HasDerivWithinAt (fun s => (x s).2.2.2 X) (x'.2.2.2 X) I t
@[sa_ref_forward "SemanticsEB.hasDerivWithinAtPop" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SemanticsEB.hasDerivWithinAtPop"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SemanticsEB.HasDerivWithinAtPop

/-! ## Chain rules: `SemanticsEB.hasDerivWithinAtEdgeDefect`, `…NodeTotal`

Texts: "Chain rule for the edge defect along a curve, within a set of times `I`, when `ψ''` is
the derivative of `ψ'` at the current θ." / "Chain rule for the node total along a curve, within
a set of times `I`, when `ψ'` is the derivative of `ψ` at the current θ."
Reading: if `x` has derivative `x'` within `I` at `t` and `HasDerivAt ψ' (ψ''(θ(t))) θ(t)`
(resp. `HasDerivAt ψ (ψ'(θ(t))) θ(t)`), then `t ↦ edge defect (x t)` (resp. node total) has, within
`I` at `t`, the chain-rule derivative `EdgeDefD N q (x t) x'` (resp. `NodeTotD`). The edge defect
is `θ − φ_S − Σ_X φ_X`, the node total `qξψ(θ) + Σ_X pop_X` (sums over species: `[Fintype σ]`). -/

namespace Alignment.Shadows.SemanticsEB.HasDerivWithinAtEdgeDefect

open Alignment.Shadows.SemanticsEB

@[sa_reference "SemanticsEB.hasDerivWithinAtEdgeDefect"]
def T : Prop := ∀ {σ : Type} [Fintype σ] (N : CNet) (q : ℝ) (x : ℝ → EB σ) (x' : EB σ)
  (I : Set ℝ) (t : ℝ), HasDerivWithinAt x x' I t → HasDerivAt N.ψ' (N.ψ'' (x t).1) (x t).1 →
  HasDerivWithinAt (fun s => EdgeDef N q (x s)) (EdgeDefD N q (x t) x') I t
@[sa_shadow "SemanticsEB.hasDerivWithinAtEdgeDefect" 1]
def S1 : Prop := ∀ {σ : Type} [Fintype σ] (N : CNet) (q : ℝ) (x : ℝ → EB σ) (x' : EB σ)
  (I : Set ℝ) (t : ℝ), HasDerivWithinAt x x' I t → HasDerivAt N.ψ' (N.ψ'' (x t).1) (x t).1 →
  HasDerivWithinAt (fun s => EdgeDef N q (x s)) (EdgeDefD N q (x t) x') I t
@[sa_ref_forward "SemanticsEB.hasDerivWithinAtEdgeDefect" 1]
theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SemanticsEB.hasDerivWithinAtEdgeDefect"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SemanticsEB.HasDerivWithinAtEdgeDefect

namespace Alignment.Shadows.SemanticsEB.HasDerivWithinAtNodeTotal

open Alignment.Shadows.SemanticsEB

@[sa_reference "SemanticsEB.hasDerivWithinAtNodeTotal"]
def T : Prop := ∀ {σ : Type} [Fintype σ] (N : CNet) (q : ℝ) (x : ℝ → EB σ) (x' : EB σ)
  (I : Set ℝ) (t : ℝ), HasDerivWithinAt x x' I t → HasDerivAt N.ψ (N.ψ' (x t).1) (x t).1 →
  HasDerivWithinAt (fun s => NodeTot N q (x s)) (NodeTotD N q (x t) x') I t
@[sa_shadow "SemanticsEB.hasDerivWithinAtNodeTotal" 1]
def S1 : Prop := ∀ {σ : Type} [Fintype σ] (N : CNet) (q : ℝ) (x : ℝ → EB σ) (x' : EB σ)
  (I : Set ℝ) (t : ℝ), HasDerivWithinAt x x' I t → HasDerivAt N.ψ (N.ψ' (x t).1) (x t).1 →
  HasDerivWithinAt (fun s => NodeTot N q (x s)) (NodeTotD N q (x t) x') I t
@[sa_ref_forward "SemanticsEB.hasDerivWithinAtNodeTotal" 1]
theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SemanticsEB.hasDerivWithinAtNodeTotal"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SemanticsEB.HasDerivWithinAtNodeTotal

/-! ## Additivity of the named derivatives: `SemanticsEB.edgeDefectDerivAdd`,
`nodeTotalDerivAdd`

Texts: "`edgeDefectDeriv N q u` is additive in the direction." / "`nodeTotalDeriv N q u` is
additive in the direction." These are about the named trusted operations. -/

namespace Alignment.Shadows.SemanticsEB.EdgeDefectDerivAdd

@[sa_reference "SemanticsEB.edgeDefectDerivAdd"]
def T : Prop := ∀ {σ : Type} [Fintype σ] (N : CNet) (q : ℝ) (u v w : EB σ),
  edgeDefectDeriv N q u (v + w) = edgeDefectDeriv N q u v + edgeDefectDeriv N q u w
@[sa_shadow "SemanticsEB.edgeDefectDerivAdd" 1]
def S1 : Prop := ∀ {σ : Type} [Fintype σ] (N : CNet) (q : ℝ) (u v w : EB σ),
  edgeDefectDeriv N q u (v + w) = edgeDefectDeriv N q u v + edgeDefectDeriv N q u w
@[sa_ref_forward "SemanticsEB.edgeDefectDerivAdd" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SemanticsEB.edgeDefectDerivAdd"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SemanticsEB.EdgeDefectDerivAdd

namespace Alignment.Shadows.SemanticsEB.NodeTotalDerivAdd

@[sa_reference "SemanticsEB.nodeTotalDerivAdd"]
def T : Prop := ∀ {σ : Type} [Fintype σ] (N : CNet) (q : ℝ) (u v w : EB σ),
  nodeTotalDeriv N q u (v + w) = nodeTotalDeriv N q u v + nodeTotalDeriv N q u w
@[sa_shadow "SemanticsEB.nodeTotalDerivAdd" 1]
def S1 : Prop := ∀ {σ : Type} [Fintype σ] (N : CNet) (q : ℝ) (u v w : EB σ),
  nodeTotalDeriv N q u (v + w) = nodeTotalDeriv N q u v + nodeTotalDeriv N q u w
@[sa_ref_forward "SemanticsEB.nodeTotalDerivAdd" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SemanticsEB.nodeTotalDerivAdd"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SemanticsEB.NodeTotalDerivAdd

/-! ## Per reaction: `SemanticsEB.edgeDefectDerivEbField`, `nodeTotalDerivEbField` (re-shadowed)

Texts: "Per reaction, the edge defect changes only through removals." / "Per reaction, the node
total changes only through removals." Reading: for every degree data `N` (no hypothesis), every
`q`, every state `u` and every reaction `r` that is not a removal `X → ∅`, the rate of change of
the edge defect `θ − φ_S − Σ_X φ_X` (resp. the node total `qξψ(θ) + Σ_X pop_X`) along the field
`ebField N q r` at `u` is `0`. The rate of change is the chain-rule directional derivative
`EdgeDefD N q u (ebField N q r u)` (resp. `NodeTotD`), with `ψ''` (resp. `ψ'`) standing for the
derivative, as for the named derivatives in DataTypes. The non-removal T_EB reactions are
exactly contacts `s + J → X + J`, exits `s → Y` and progressions `X → Y`, so the claim splits
into one shadow per form (a conjunction over the reaction forms).
-- AMBIGUITY: "changes only through removals" says that non-removals cause no change; it does not
-- give the rate at which a removal changes the defect/total (that is the list-level balance law
-- stated by other claims), so no value is required for removals here.
-/

namespace Alignment.Shadows.SemanticsEB.EdgeDefectDerivEbField

open Alignment.Shadows.SemanticsEB

@[sa_reference "SemanticsEB.edgeDefectDerivEbField"]
def T : Prop := ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (r : Rxn σ)
  (u : EB σ), NotRemoval r → EdgeDefD N q u (ebField N q r u) = 0

/-- S1: a contact `s + J → X + J` leaves the edge defect unchanged. -/
@[sa_shadow "SemanticsEB.edgeDefectDerivEbField" 1]
def S1 : Prop := ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (J X : σ) (τ : ℝ)
  (u : EB σ), EdgeDefD N q u (ebField N q (Rxn.contact J X τ) u) = 0

/-- S2: an exit `s → Y` leaves the edge defect unchanged. -/
@[sa_shadow "SemanticsEB.edgeDefectDerivEbField" 2]
def S2 : Prop := ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (Y : σ) (ν : ℝ)
  (u : EB σ), EdgeDefD N q u (ebField N q (Rxn.exit Y ν) u) = 0

/-- S3: a progression `X → Y` leaves the edge defect unchanged. -/
@[sa_shadow "SemanticsEB.edgeDefectDerivEbField" 3]
def S3 : Prop := ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (X Y : σ) (a : ℝ)
  (u : EB σ), EdgeDefD N q u (ebField N q (Rxn.trans X (some Y) a) u) = 0

@[sa_ref_forward "SemanticsEB.edgeDefectDerivEbField" 1]
theorem ref_fwd1 : T → S1 := by
  intro t σ _ _ N q J X τ u
  exact t N q _ u (fun _ _ h => by cases h)
@[sa_ref_forward "SemanticsEB.edgeDefectDerivEbField" 2]
theorem ref_fwd2 : T → S2 := by
  intro t σ _ _ N q Y ν u
  exact t N q _ u (fun _ _ h => by cases h)
@[sa_ref_forward "SemanticsEB.edgeDefectDerivEbField" 3]
theorem ref_fwd3 : T → S3 := by
  intro t σ _ _ N q X Y a u
  exact t N q _ u (fun _ _ h => by cases h)
@[sa_complete "SemanticsEB.edgeDefectDerivEbField"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := by
  intro σ _ _ N q r u hr
  match r, hr with
  | .contact J X τ, _ => exact s1 N q J X τ u
  | .exit Y ν, _ => exact s2 N q Y ν u
  | .trans X (some Y) a, _ => exact s3 N q X Y a u
  | .trans X none a, hr => exact absurd rfl (hr X a)

end Alignment.Shadows.SemanticsEB.EdgeDefectDerivEbField

namespace Alignment.Shadows.SemanticsEB.NodeTotalDerivEbField

open Alignment.Shadows.SemanticsEB

@[sa_reference "SemanticsEB.nodeTotalDerivEbField"]
def T : Prop := ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (r : Rxn σ)
  (u : EB σ), NotRemoval r → NodeTotD N q u (ebField N q r u) = 0

/-- S1: a contact `s + J → X + J` leaves the node total unchanged. -/
@[sa_shadow "SemanticsEB.nodeTotalDerivEbField" 1]
def S1 : Prop := ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (J X : σ) (τ : ℝ)
  (u : EB σ), NodeTotD N q u (ebField N q (Rxn.contact J X τ) u) = 0

/-- S2: an exit `s → Y` leaves the node total unchanged. -/
@[sa_shadow "SemanticsEB.nodeTotalDerivEbField" 2]
def S2 : Prop := ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (Y : σ) (ν : ℝ)
  (u : EB σ), NodeTotD N q u (ebField N q (Rxn.exit Y ν) u) = 0

/-- S3: a progression `X → Y` leaves the node total unchanged. -/
@[sa_shadow "SemanticsEB.nodeTotalDerivEbField" 3]
def S3 : Prop := ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (X Y : σ) (a : ℝ)
  (u : EB σ), NodeTotD N q u (ebField N q (Rxn.trans X (some Y) a) u) = 0

@[sa_ref_forward "SemanticsEB.nodeTotalDerivEbField" 1]
theorem ref_fwd1 : T → S1 := by
  intro t σ _ _ N q J X τ u
  exact t N q _ u (fun _ _ h => by cases h)
@[sa_ref_forward "SemanticsEB.nodeTotalDerivEbField" 2]
theorem ref_fwd2 : T → S2 := by
  intro t σ _ _ N q Y ν u
  exact t N q _ u (fun _ _ h => by cases h)
@[sa_ref_forward "SemanticsEB.nodeTotalDerivEbField" 3]
theorem ref_fwd3 : T → S3 := by
  intro t σ _ _ N q X Y a u
  exact t N q _ u (fun _ _ h => by cases h)
@[sa_complete "SemanticsEB.nodeTotalDerivEbField"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := by
  intro σ _ _ N q r u hr
  match r, hr with
  | .contact J X τ, _ => exact s1 N q J X τ u
  | .exit Y ν, _ => exact s2 N q Y ν u
  | .trans X (some Y) a, _ => exact s3 N q X Y a u
  | .trans X none a, hr => exact absurd rfl (hr X a)

end Alignment.Shadows.SemanticsEB.NodeTotalDerivEbField

/-! ## Along the lift: `SemanticsEB.edgeDefectDerivLift`, `nodeTotalDerivLift`

Texts: "Along the EB field of a reaction list, the edge defect changes at the removal flux of φ."
/ "Along the EB field of a reaction list, the node total changes at minus the removal flux of
pop." Reading: for every reaction list and state `u`, the chain-rule derivative of the edge
defect (node total) in the direction `lift N q rs u` equals `Σ_{(X → ∅, a) ∈ rs} a φ_X`
(resp. `−Σ_{(X → ∅, a) ∈ rs} a pop_X`), with φ, pop the coordinates of `u`. -/

namespace Alignment.Shadows.SemanticsEB.EdgeDefectDerivLift

open Alignment.Shadows.SemanticsEB

@[sa_reference "SemanticsEB.edgeDefectDerivLift"]
def T : Prop := ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ)
  (rs : List (Rxn σ)) (u : EB σ), EdgeDefD N q u (lift N q rs u) = RemFlux rs u.2.2.1
@[sa_shadow "SemanticsEB.edgeDefectDerivLift" 1]
def S1 : Prop := ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ)
  (rs : List (Rxn σ)) (u : EB σ), EdgeDefD N q u (lift N q rs u) = RemFlux rs u.2.2.1
@[sa_ref_forward "SemanticsEB.edgeDefectDerivLift" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SemanticsEB.edgeDefectDerivLift"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SemanticsEB.EdgeDefectDerivLift

namespace Alignment.Shadows.SemanticsEB.NodeTotalDerivLift

open Alignment.Shadows.SemanticsEB

@[sa_reference "SemanticsEB.nodeTotalDerivLift"]
def T : Prop := ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ)
  (rs : List (Rxn σ)) (u : EB σ), NodeTotD N q u (lift N q rs u) = -RemFlux rs u.2.2.2
@[sa_shadow "SemanticsEB.nodeTotalDerivLift" 1]
def S1 : Prop := ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ)
  (rs : List (Rxn σ)) (u : EB σ), NodeTotD N q u (lift N q rs u) = -RemFlux rs u.2.2.2
@[sa_ref_forward "SemanticsEB.nodeTotalDerivLift" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SemanticsEB.nodeTotalDerivLift"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SemanticsEB.NodeTotalDerivLift

/-! ## Balance laws along solutions: `SemanticsEB.hasDerivWithinAtEdgeDefectLift`,
`hasDerivWithinAtNodeTotalLift`, `hasDerivAtEdgeDefectLift`, `hasDerivAtNodeTotalLift`

Edge text: "Let `x` solve the EB field of a T_EB reaction list `rs` within a set of times `I` at
the time `t` (`HasDerivWithinAt`), and let `ψ''` be the derivative of `ψ'` at `θ(t)`. Then,
within `I` at `t`, `d/dt (θ − φ_S − Σ_X φ_X) = Σ_{(X → ∅, a) ∈ rs} a φ_X`." Node text: same with
`ψ'` the derivative of `ψ` at `θ(t)` and `d/dt (S + Σ_X pop_X) = −Σ_{(X → ∅, a) ∈ rs} a pop_X`,
`S = qξψ(θ)`. The `HasDerivAt` versions are "the edge (node) balance law for two-sided
derivatives (… with `I = ℝ`)": solution and conclusion with two-sided derivatives at `t`.
Every set `I`, every time `t`, every T_EB reaction list, every degree data `N`.
-- AMBIGUITY: "Removals `X → ∅` make the partner inert ... so the defect grows" is explanation; a
-- sign statement would need `a ≥ 0`, `φ ≥ 0`, which the text does not assume. Not formalised.
-/

namespace Alignment.Shadows.SemanticsEB.HasDerivWithinAtEdgeDefectLift

open Alignment.Shadows.SemanticsEB

@[sa_reference "SemanticsEB.hasDerivWithinAtEdgeDefectLift"]
def T : Prop := ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ)
  (rs : List (Rxn σ)) (x : ℝ → EB σ) (I : Set ℝ) (t : ℝ),
  HasDerivWithinAt x (lift N q rs (x t)) I t → HasDerivAt N.ψ' (N.ψ'' (x t).1) (x t).1 →
  HasDerivWithinAt (fun s => EdgeDef N q (x s)) (RemFlux rs (x t).2.2.1) I t
@[sa_shadow "SemanticsEB.hasDerivWithinAtEdgeDefectLift" 1]
def S1 : Prop := ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ)
  (rs : List (Rxn σ)) (x : ℝ → EB σ) (I : Set ℝ) (t : ℝ),
  HasDerivWithinAt x (lift N q rs (x t)) I t → HasDerivAt N.ψ' (N.ψ'' (x t).1) (x t).1 →
  HasDerivWithinAt (fun s => EdgeDef N q (x s)) (RemFlux rs (x t).2.2.1) I t
@[sa_ref_forward "SemanticsEB.hasDerivWithinAtEdgeDefectLift" 1]
theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SemanticsEB.hasDerivWithinAtEdgeDefectLift"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SemanticsEB.HasDerivWithinAtEdgeDefectLift

namespace Alignment.Shadows.SemanticsEB.HasDerivWithinAtNodeTotalLift

open Alignment.Shadows.SemanticsEB

@[sa_reference "SemanticsEB.hasDerivWithinAtNodeTotalLift"]
def T : Prop := ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ)
  (rs : List (Rxn σ)) (x : ℝ → EB σ) (I : Set ℝ) (t : ℝ),
  HasDerivWithinAt x (lift N q rs (x t)) I t → HasDerivAt N.ψ (N.ψ' (x t).1) (x t).1 →
  HasDerivWithinAt (fun s => NodeTot N q (x s)) (-RemFlux rs (x t).2.2.2) I t
@[sa_shadow "SemanticsEB.hasDerivWithinAtNodeTotalLift" 1]
def S1 : Prop := ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ)
  (rs : List (Rxn σ)) (x : ℝ → EB σ) (I : Set ℝ) (t : ℝ),
  HasDerivWithinAt x (lift N q rs (x t)) I t → HasDerivAt N.ψ (N.ψ' (x t).1) (x t).1 →
  HasDerivWithinAt (fun s => NodeTot N q (x s)) (-RemFlux rs (x t).2.2.2) I t
@[sa_ref_forward "SemanticsEB.hasDerivWithinAtNodeTotalLift" 1]
theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SemanticsEB.hasDerivWithinAtNodeTotalLift"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SemanticsEB.HasDerivWithinAtNodeTotalLift

namespace Alignment.Shadows.SemanticsEB.HasDerivAtEdgeDefectLift

open Alignment.Shadows.SemanticsEB

@[sa_reference "SemanticsEB.hasDerivAtEdgeDefectLift"]
def T : Prop := ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ)
  (rs : List (Rxn σ)) (x : ℝ → EB σ) (t : ℝ),
  HasDerivAt x (lift N q rs (x t)) t → HasDerivAt N.ψ' (N.ψ'' (x t).1) (x t).1 →
  HasDerivAt (fun s => EdgeDef N q (x s)) (RemFlux rs (x t).2.2.1) t
@[sa_shadow "SemanticsEB.hasDerivAtEdgeDefectLift" 1]
def S1 : Prop := ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ)
  (rs : List (Rxn σ)) (x : ℝ → EB σ) (t : ℝ),
  HasDerivAt x (lift N q rs (x t)) t → HasDerivAt N.ψ' (N.ψ'' (x t).1) (x t).1 →
  HasDerivAt (fun s => EdgeDef N q (x s)) (RemFlux rs (x t).2.2.1) t
@[sa_ref_forward "SemanticsEB.hasDerivAtEdgeDefectLift" 1]
theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SemanticsEB.hasDerivAtEdgeDefectLift"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SemanticsEB.HasDerivAtEdgeDefectLift

namespace Alignment.Shadows.SemanticsEB.HasDerivAtNodeTotalLift

open Alignment.Shadows.SemanticsEB

@[sa_reference "SemanticsEB.hasDerivAtNodeTotalLift"]
def T : Prop := ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ)
  (rs : List (Rxn σ)) (x : ℝ → EB σ) (t : ℝ),
  HasDerivAt x (lift N q rs (x t)) t → HasDerivAt N.ψ (N.ψ' (x t).1) (x t).1 →
  HasDerivAt (fun s => NodeTot N q (x s)) (-RemFlux rs (x t).2.2.2) t
@[sa_shadow "SemanticsEB.hasDerivAtNodeTotalLift" 1]
def S1 : Prop := ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ)
  (rs : List (Rxn σ)) (x : ℝ → EB σ) (t : ℝ),
  HasDerivAt x (lift N q rs (x t)) t → HasDerivAt N.ψ (N.ψ' (x t).1) (x t).1 →
  HasDerivAt (fun s => NodeTot N q (x s)) (-RemFlux rs (x t).2.2.2) t
@[sa_ref_forward "SemanticsEB.hasDerivAtNodeTotalLift" 1]
theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SemanticsEB.hasDerivAtNodeTotalLift"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SemanticsEB.HasDerivAtNodeTotalLift

/-! ## Constancy lemmas: `SemanticsEB.constOfHasDerivWithinAtZero`, `constOfHasDerivAtZero`

Texts: "A real function whose derivative within a convex set `I` vanishes at every point of `I`
is constant on `I`: `g t = g t₀` for all `t, t₀ ∈ I`." / "A real function with derivative 0
everywhere is constant." Pure real analysis: the shadows mention no trusted constant (expected
flag `shadow_trusted_free`, to be lifted only by an independent review record).
"is constant" is written `∀ t t₀, g t = g t₀`, as in the first text. -/

namespace Alignment.Shadows.SemanticsEB.ConstOfHasDerivWithinAtZero

@[sa_reference "SemanticsEB.constOfHasDerivWithinAtZero"]
def T : Prop := ∀ (g : ℝ → ℝ) (I : Set ℝ), Convex ℝ I →
  (∀ t ∈ I, HasDerivWithinAt g 0 I t) → ∀ t ∈ I, ∀ t₀ ∈ I, g t = g t₀
@[sa_shadow "SemanticsEB.constOfHasDerivWithinAtZero" 1]
def S1 : Prop := ∀ (g : ℝ → ℝ) (I : Set ℝ), Convex ℝ I →
  (∀ t ∈ I, HasDerivWithinAt g 0 I t) → ∀ t ∈ I, ∀ t₀ ∈ I, g t = g t₀
@[sa_ref_forward "SemanticsEB.constOfHasDerivWithinAtZero" 1]
theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SemanticsEB.constOfHasDerivWithinAtZero"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SemanticsEB.ConstOfHasDerivWithinAtZero

namespace Alignment.Shadows.SemanticsEB.ConstOfHasDerivAtZero

@[sa_reference "SemanticsEB.constOfHasDerivAtZero"]
def T : Prop := ∀ g : ℝ → ℝ, (∀ t, HasDerivAt g 0 t) → ∀ t t₀, g t = g t₀
@[sa_shadow "SemanticsEB.constOfHasDerivAtZero" 1]
def S1 : Prop := ∀ g : ℝ → ℝ, (∀ t, HasDerivAt g 0 t) → ∀ t t₀, g t = g t₀
@[sa_ref_forward "SemanticsEB.constOfHasDerivAtZero" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SemanticsEB.constOfHasDerivAtZero"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SemanticsEB.ConstOfHasDerivAtZero

/-! ## `SemanticsEB.liftXiEqZero`

Text: "Without exits the ξ-component of the EB field vanishes." Reading: "the EB field" is the
EB vector field `lift N q rs` of a reaction list (DataTypes); for every list with no exit
`s → Y`, every state `u`: `(lift N q rs u).ξ = 0`.
-- AMBIGUITY: could also be read per reaction (`ebField N q r u` for a non-exit `r`); the list
-- reading is chosen because "the EB field" names `lift` and "without exits" is plural.
-/

namespace Alignment.Shadows.SemanticsEB.LiftXiEqZero

open Alignment.Shadows.SemanticsEB

@[sa_reference "SemanticsEB.liftXiEqZero"]
def T : Prop := ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)) (u : EB σ),
  NoExit rs → (lift N q rs u).2.1 = 0
@[sa_shadow "SemanticsEB.liftXiEqZero" 1]
def S1 : Prop := ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)) (u : EB σ),
  NoExit rs → (lift N q rs u).2.1 = 0
@[sa_ref_forward "SemanticsEB.liftXiEqZero" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SemanticsEB.liftXiEqZero"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SemanticsEB.LiftXiEqZero

/-! ## `SemanticsEB.xiConst` (re-shadowed)

Text: "**ξ is constant along EB solutions of exit-free models.** Let `I` be a time interval (a
convex set of times) with `0 ∈ I`, and let `x` solve the EB field of a T_EB reaction list `rs`
that has no exit `s → Y` on `I` (`HasDerivWithinAt x (lift N q rs (x t)) I t` for `t ∈ I`). Then
`ξ(t) = ξ(0)` for every `t ∈ I`. No assumption on the degree data is needed."
Reading: every species type (no finiteness: the statement has no sum over species), every degree
data `N` with no hypothesis on ψ, ψ', ψ'', every `q`, every exit-free list, every convex `I ∋ 0`,
every solution on `I`. A single implication: one shadow. -/

namespace Alignment.Shadows.SemanticsEB.XiConst

open Alignment.Shadows.SemanticsEB

@[sa_reference "SemanticsEB.xiConst"]
def T : Prop := ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ))
  (I : Set ℝ) (x : ℝ → EB σ), Convex ℝ I → (0 : ℝ) ∈ I → NoExit rs →
  (∀ t ∈ I, HasDerivWithinAt x (lift N q rs (x t)) I t) →
  ∀ t ∈ I, (x t).2.1 = (x 0).2.1
@[sa_shadow "SemanticsEB.xiConst" 1]
def S1 : Prop := ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ))
  (I : Set ℝ) (x : ℝ → EB σ), Convex ℝ I → (0 : ℝ) ∈ I → NoExit rs →
  (∀ t ∈ I, HasDerivWithinAt x (lift N q rs (x t)) I t) →
  ∀ t ∈ I, (x t).2.1 = (x 0).2.1
@[sa_ref_forward "SemanticsEB.xiConst" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SemanticsEB.xiConst"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SemanticsEB.XiConst

/-! ## `SemanticsEB.conservation` (re-shadowed after the §M.1 amendment)

Text: "**Edge conservation θ = φ_S + Σ_X φ_X is invariant along removal-free EB solutions.**
Design statement (DESIGN §D.4, Evidence): "The exit terms were checked by hand. Conservation
θ = φ_S + Σφ_X holds."; amended by §M.1: "For removal-free T_EB models (no `X → ∅`), θ = φ_S +
Σφ_X is invariant along every solution on a time interval: if it holds at t = 0 it holds at every
time of the interval. In particular, when ψ'(1) ≠ 0, it holds along solutions from the design's
initial condition θ(0) = ξ(0) = 1, Σφ_X(0) = 1 − q.""

Reading. "T_EB models" = reaction lists `rs : List (Rxn σ)` over any finite species type (the sum
Σ_X needs `[Fintype σ]`) on any degree data `N`, any `q`; "removal-free" = no `trans X none a`
in `rs` (exits and progressions allowed: "The exit terms were checked"); "a time interval" = a
convex `I ∋ 0` (the statement refers to t = 0 as a time of the interval); "solution on `I`" =
`HasDerivWithinAt x (lift N q rs (x t)) I t` for every `t ∈ I`; φ_S = qξψ'(θ)/ψ'(1) (DESIGN §0).
The text is a conjunction: (1) the invariance for every solution; (2) "in particular", under
ψ'(1) ≠ 0, the relation along every solution from θ(0) = ξ(0) = 1, Σφ_X(0) = 1 − q (no condition on
the individual φ_X(0), pop(0)). One shadow per conjunct.
-- AMBIGUITY (degree data): the text names no hypothesis on ψ, ψ', ψ''; but in `CNet` they are
-- independent fields, and "φ_S" and "ψ''" in the field are the design's derivatives of the degree
-- PGF. The weakest condition that makes the text's ψ'' the derivative of ψ' where the solution
-- goes is taken: `HasDerivAt N.ψ' (N.ψ'' θ(t)) θ(t)` for every `t ∈ I` (the module's convention of
-- conditions at the visited θ). No other condition (ψ(1) = 1, positivity, …) is imposed: the
-- text says "every solution", and invariance does not need one.
-/

namespace Alignment.Shadows.SemanticsEB.Conservation

open Alignment.Shadows.SemanticsEB

/-- Conjunct (1): invariance of θ = φ_S + Σ_X φ_X along every solution of a removal-free list on a
time interval, with ψ'' the derivative of ψ' at every visited θ. -/
def Invariant : Prop := ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ)
  (rs : List (Rxn σ)) (I : Set ℝ) (x : ℝ → EB σ), NoRemoval rs → Convex ℝ I → (0 : ℝ) ∈ I →
  (∀ t ∈ I, HasDerivWithinAt x (lift N q rs (x t)) I t) →
  (∀ t ∈ I, HasDerivAt N.ψ' (N.ψ'' (x t).1) (x t).1) →
  (x 0).1 = PhiS N q (x 0) + ∑ X, (x 0).2.2.1 X →
  ∀ t ∈ I, (x t).1 = PhiS N q (x t) + ∑ X, (x t).2.2.1 X

/-- Conjunct (2): with ψ'(1) ≠ 0, the relation holds along every such solution from the design's
initial condition θ(0) = ξ(0) = 1, Σ_X φ_X(0) = 1 − q. -/
def FromDesignIC : Prop := ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ)
  (rs : List (Rxn σ)) (I : Set ℝ) (x : ℝ → EB σ), NoRemoval rs → Convex ℝ I → (0 : ℝ) ∈ I →
  (∀ t ∈ I, HasDerivWithinAt x (lift N q rs (x t)) I t) →
  (∀ t ∈ I, HasDerivAt N.ψ' (N.ψ'' (x t).1) (x t).1) →
  N.ψ' 1 ≠ 0 → (x 0).1 = 1 → (x 0).2.1 = 1 → ∑ X, (x 0).2.2.1 X = 1 - q →
  ∀ t ∈ I, (x t).1 = PhiS N q (x t) + ∑ X, (x t).2.2.1 X

@[sa_reference "SemanticsEB.conservation"]
def T : Prop := Invariant ∧ FromDesignIC

/-- S1: invariance along every removal-free solution on a time interval. -/
@[sa_shadow "SemanticsEB.conservation" 1]
def S1 : Prop := Invariant

/-- S2: the relation along solutions from the design's initial condition, when ψ'(1) ≠ 0. -/
@[sa_shadow "SemanticsEB.conservation" 2]
def S2 : Prop := FromDesignIC

@[sa_ref_forward "SemanticsEB.conservation" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "SemanticsEB.conservation" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "SemanticsEB.conservation"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.SemanticsEB.Conservation

/-! ## `SemanticsEB.nodeConservation`

Text: "Let `N` be a configuration network with `ψ(1) = 1`, and let `rs` be a T_EB reaction list
with no removal `X → ∅`. Let `I` be a time interval (a convex set of times) with `0 ∈ I` and let
`x` solve the EB field of `rs` on `I` (…), with `ψ'` the derivative of `ψ` at every visited
`θ(t)`, `t ∈ I`, and with `θ(0) = 1`, `ξ(0) = 1` and `Σ_X pop_X(0) = 1 − q`. Then
`qξ(t)ψ(θ(t)) + Σ_X pop_X(t) = 1` for every `t ∈ I`." One implication, one shadow. -/

namespace Alignment.Shadows.SemanticsEB.NodeConservation

open Alignment.Shadows.SemanticsEB

@[sa_reference "SemanticsEB.nodeConservation"]
def T : Prop := ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ)
  (rs : List (Rxn σ)) (I : Set ℝ) (x : ℝ → EB σ), N.ψ 1 = 1 → NoRemoval rs →
  Convex ℝ I → (0 : ℝ) ∈ I →
  (∀ t ∈ I, HasDerivWithinAt x (lift N q rs (x t)) I t) →
  (∀ t ∈ I, HasDerivAt N.ψ (N.ψ' (x t).1) (x t).1) →
  (x 0).1 = 1 → (x 0).2.1 = 1 → ∑ X, (x 0).2.2.2 X = 1 - q →
  ∀ t ∈ I, q * (x t).2.1 * N.ψ (x t).1 + ∑ X, (x t).2.2.2 X = 1
@[sa_shadow "SemanticsEB.nodeConservation" 1]
def S1 : Prop := ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ)
  (rs : List (Rxn σ)) (I : Set ℝ) (x : ℝ → EB σ), N.ψ 1 = 1 → NoRemoval rs →
  Convex ℝ I → (0 : ℝ) ∈ I →
  (∀ t ∈ I, HasDerivWithinAt x (lift N q rs (x t)) I t) →
  (∀ t ∈ I, HasDerivAt N.ψ (N.ψ' (x t).1) (x t).1) →
  (x 0).1 = 1 → (x 0).2.1 = 1 → ∑ X, (x 0).2.2.2 X = 1 - q →
  ∀ t ∈ I, q * (x t).2.1 * N.ψ (x t).1 + ∑ X, (x t).2.2.2 X = 1
@[sa_ref_forward "SemanticsEB.nodeConservation" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SemanticsEB.nodeConservation"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SemanticsEB.NodeConservation
