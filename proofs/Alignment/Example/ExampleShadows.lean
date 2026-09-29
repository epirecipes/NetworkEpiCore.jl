import Alignment.Registry
import NetworkEpi.Syntax.Rxn

/-!
# Worked example: blind shadow sets (template for `Alignment/Shadows/<Group>.lean`)

A shadow author reads only the claim's entry in `claims_blind.yaml`, the group's
`Alignment/DataTypes/<Group>.md`, `Alignment/README.md`, this file and the cited source passage.
They never read theorem statements, definition bodies or checker files.

For each claim write the intended statement `T` (`@[sa_reference]`), atomic shadows
`S₁ … Sₙ` (`@[sa_shadow]`), and the completeness certificates `T → Sᵢ` (`@[sa_ref_forward]`)
and `S₁ → … → Sₙ → T` (`@[sa_complete]`). Certificates may use any tactic; they are only
required to be sorry-free. State notions in primitive terms (fields of the data types, the
opaque "operations under test" listed in `DataTypes/<Group>.md`), never through a theorem.

These example claims are registered under `EXAMPLE.*` ids (group `Example`) and excluded from
normal reports; `bash scripts/sa_pass.sh --self-test` requires all three to reach SA-PASS = 1.
Because the same person wrote these shadows and the checkers, they are *weak* passes and
illustrate the mechanics only.
-/

open NEP

namespace Alignment.Example.AdmissibleType

/-! ### `EXAMPLE.admissibleType` (a claim that needs a reviewed bridge)

Blind text: "EB-admissibility is membership of the reaction's type in T_EB: "the sub-theory with
no arrow into Sus" (DESIGN §B.2)."

Data types used: `NRxn σ` (T_net reactions over node species σ), its typing `NRxn.type` with
values in `TNet` (`contact`, `exit`, `progress`, `remove`, `resus`, `nodeContact`), and the
operation under test `NRxn.EBAdmissible`. DESIGN §B.2 defines T_EB = {contact, exit, progress,
remove}; membership is written below in primitive terms. -/

/-- Membership of a T_net type in T_EB = {contact, exit, progress, remove}, in primitive terms. -/
def InTEB (t : TNet) : Prop :=
  t = .contact ∨ t = .exit ∨ t = .progress ∨ t = .remove

/-- Intended statement: for every species type and every T_net reaction `r`, `r` is
EB-admissible exactly when its type lies in T_EB. -/
@[sa_reference "EXAMPLE.admissibleType"]
def T : Prop := ∀ {σ : Type} (r : NRxn σ), r.EBAdmissible ↔ InTEB r.type

/-- S1: admissible reactions have a T_EB type. -/
@[sa_shadow "EXAMPLE.admissibleType" 1]
def S1 : Prop := ∀ {σ : Type} (r : NRxn σ), r.EBAdmissible → InTEB r.type

/-- S2: reactions with a T_EB type are admissible. -/
@[sa_shadow "EXAMPLE.admissibleType" 2]
def S2 : Prop := ∀ {σ : Type} (r : NRxn σ), InTEB r.type → r.EBAdmissible

@[sa_ref_forward "EXAMPLE.admissibleType" 1]
theorem ref_fwd1 : T → S1 := fun t _ r => (t r).mp

@[sa_ref_forward "EXAMPLE.admissibleType" 2]
theorem ref_fwd2 : T → S2 := fun t _ r => (t r).mpr

@[sa_complete "EXAMPLE.admissibleType"]
theorem complete (s1 : S1) (s2 : S2) : T := fun r => ⟨s1 r, s2 r⟩

end Alignment.Example.AdmissibleType

namespace Alignment.Example.NotAdmissible

/-! ### `EXAMPLE.notAdmissible` (a claim with two implementation theorems)

Blind text: "Resusceptibility `X → s` (§B.2 type `:resus`, e.g. SIS `I → S`) is not
EB-admissible [...] A node contact `X + J → Y + J` with a node-species recipient (§B.2 type
`:node_contact`) is not EB-admissible."

Data types used: the constructors `NRxn.resus X a` (X → s at rate a) and
`NRxn.nodeContact X J Y τ` (X + J → Y + J at rate τ, `J = none` the susceptible species), and
the operation under test `NRxn.EBAdmissible`. -/

/-- Intended statement: no resusceptibility and no node contact is EB-admissible. -/
@[sa_reference "EXAMPLE.notAdmissible"]
def T : Prop :=
  (∀ {σ : Type} (X : σ) (a : ℝ), ¬ (NRxn.resus X a).EBAdmissible) ∧
    (∀ {σ : Type} (X : σ) (J : Option σ) (Y : σ) (τ : ℝ),
      ¬ (NRxn.nodeContact X J Y τ).EBAdmissible)

/-- S1: resusceptibility is refused. -/
@[sa_shadow "EXAMPLE.notAdmissible" 1]
def S1 : Prop := ∀ {σ : Type} (X : σ) (a : ℝ), ¬ (NRxn.resus X a).EBAdmissible

/-- S2: node contacts are refused. -/
@[sa_shadow "EXAMPLE.notAdmissible" 2]
def S2 : Prop :=
  ∀ {σ : Type} (X : σ) (J : Option σ) (Y : σ) (τ : ℝ), ¬ (NRxn.nodeContact X J Y τ).EBAdmissible

@[sa_ref_forward "EXAMPLE.notAdmissible" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "EXAMPLE.notAdmissible" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "EXAMPLE.notAdmissible"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Example.NotAdmissible

namespace Alignment.Example.RoundTrip

/-! ### `EXAMPLE.roundTrip` (a claim whose hypothesis needs a satisfiability witness)

Blind text: "An EB-admissible T_net reaction comes from T_EB syntax."

Data types used: `Rxn σ` (T_EB reactions), `NRxn σ` (T_net reactions), the inclusion
`Rxn.toNRxn` and the operation under test `NRxn.EBAdmissible`. -/

/-- Intended statement: every EB-admissible T_net reaction is the image of a T_EB reaction. -/
@[sa_reference "EXAMPLE.roundTrip"]
def T : Prop := ∀ {σ : Type} {r : NRxn σ}, r.EBAdmissible → ∃ r' : Rxn σ, r = r'.toNRxn

/-- S1: the whole statement (a single atomic requirement). -/
@[sa_shadow "EXAMPLE.roundTrip" 1]
def S1 : Prop := ∀ {σ : Type} {r : NRxn σ}, r.EBAdmissible → ∃ r' : Rxn σ, r = r'.toNRxn

@[sa_ref_forward "EXAMPLE.roundTrip" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "EXAMPLE.roundTrip"]
theorem complete (s1 : S1) : T := s1

end Alignment.Example.RoundTrip
