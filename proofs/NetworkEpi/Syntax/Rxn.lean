import Mathlib.Data.Real.Basic
import Mathlib.Data.Option.Basic

/-!
# L2: typed reaction syntax over T_EB ⊂ T_net

DESIGN_NetworkEpiCore.md §D.7, module L2 `NEP/Syntax/Rxn`: "`inductive Rxn σ` (contact J X τ \|
exit Y ν \| trans X (Option Y) a); `NRxn σ` adds resus and nodeContact; `Rxn.map`; decidable
`EBAdmissible`".

The models are reaction networks on one susceptible species `s` (left implicit: it is the unique
species of type `:sus`, DESIGN §B.2, "On an untyped network |Σ| = 1") and a type `σ` of node
species (type `:node`). The typing of §B.2 is therefore built into the syntax:

| constructor | §B.2 shape | §B.2 type | in T_EB? |
|---|---|---|---|
| `contact J X τ` | s + J → X + J (per-contact rate τ; J, X ∉ Σ; X = J allowed) | `:contact` | yes |
| `exit Y ν` | s → Y (Y ∉ Σ) | `:exit` | yes |
| `trans X (some Y) a` | X → Y (X, Y ∉ Σ) | `:progress` | yes |
| `trans X none a` | X → ∅ | `:remove` | yes |
| `NRxn.resus X a` | X → s | `:resus` | no |
| `NRxn.nodeContact X J Y τ` | X + J → Y + J with X ∉ Σ (`J = none` is s) | `:node_contact` | no |

"**T_EB** = {contact, exit, progress, remove}: the sub-theory with **no arrow into Sus**.
**T_net** = all eight types." (§B.2). With a single susceptible species, the §B.2 types
`:sus_move` (S₁ → S₂) cannot occur and `:sus_contact` (a contact whose product or infector is
susceptible) is not represented by `NRxn`; neither is admissible for EB.

**Exits to ∅.** §B.2 allows an exit `s → Y` with "Y ∉ Σ (or ∅)". The constructor `exit (Y : σ)`
always names a node species, so `s → ∅` is not directly expressible. Model it with an *inert sink
species* `D`: a node species that appears in no other reaction (no transition out of `D` and no
contact with `D` as infector). In the EB field (`NetworkEpi.Semantics.EB`) no coordinate other
than `φ_D` and `pop_D` depends on `φ_D` or `pop_D`, so θ, ξ, S and every other `φ_X`, `pop_X`
evolve exactly as for `s → ∅`. `φ_D` and `pop_D` then record the removed edge and node mass, and
the conservation laws count it.

**What the admissibility results say.** `EBAdmissible` is defined on the *syntax*: a T_net
reaction is admissible if it lies in the image of the T_EB syntax `Rxn σ`. The results
`ebAdmissible_iff_type`, `not_ebAdmissible_resus` and `exists_not_ebAdmissible` follow from the
definitions by case analysis, because `EBAdmissible` and `TNet.inTEB` are parallel case tables.
They say that the EB semantics of this library (`ebField`, defined on `Rxn σ`) has no input for
`resus` or `nodeContact`. They do **not** prove that no EB-type semantics for `X → s` could
exist. The design's reason for refusing SIS/SIRS is mathematical ("SIS has no exact edge-based
model"; a node that returns to Sus needs susceptible strata, which is pairwise, decision H6), and
it is not formalised here.
-/

namespace NEP

/-- T_EB reactions over node species `σ` (the susceptible species `s` is implicit):
* `contact J X τ` is `s + J → X + J` at per-contact rate `τ` (DESIGN §0: "τ is always a
  per-contact (per-edge) rate");
* `exit Y ν` is `s → Y` at rate `ν` (for example vaccination);
* `trans X (some Y) a` is `X → Y` and `trans X none a` is `X → ∅`, at rate `a`. -/
inductive Rxn (σ : Type) where
  /-- `s + J → X + J` at per-contact rate `τ`. -/
  | contact (J X : σ) (τ : ℝ)
  /-- `s → Y` at rate `ν`. -/
  | exit (Y : σ) (ν : ℝ)
  /-- `X → Y` (or `X → ∅` when `Y = none`) at rate `a`. -/
  | trans (X : σ) (Y : Option σ) (a : ℝ)

/-- T_net reactions over node species `σ` (single susceptible species `s`): `NRxn σ` has the
T_EB constructors of `Rxn σ` and adds
* `resus X a`: `X → s` at rate `a` (§B.2 type `:resus`, e.g. SIS `I → S`, SIRS `R → S`);
* `nodeContact X J Y τ`: `X + J → Y + J` at rate `τ`, with recipient `X` a node species and
  catalyst `J` (`J = none` means the catalyst is `s`) (§B.2 type `:node_contact`). -/
inductive NRxn (σ : Type) where
  /-- `s + J → X + J` at per-contact rate `τ`. -/
  | contact (J X : σ) (τ : ℝ)
  /-- `s → Y` at rate `ν`. -/
  | exit (Y : σ) (ν : ℝ)
  /-- `X → Y` (or `X → ∅`) at rate `a`. -/
  | trans (X : σ) (Y : Option σ) (a : ℝ)
  /-- `X → s` at rate `a`. -/
  | resus (X : σ) (a : ℝ)
  /-- `X + J → Y + J` at rate `τ`; `J = none` is the susceptible species. -/
  | nodeContact (X : σ) (J : Option σ) (Y : σ) (τ : ℝ)

/-- The transition types of the theory T_net that `NRxn` represents (DESIGN §B.2). -/
inductive TNet where
  | contact | exit | progress | remove | resus | nodeContact
  deriving DecidableEq, Repr

/-- Membership of a T_net type in the sub-theory T_EB = {contact, exit, progress, remove}. -/
def TNet.inTEB : TNet → Bool
  | .contact | .exit | .progress | .remove => true
  | .resus | .nodeContact => false

variable {σ σ' σ'' : Type}

/-- The typing of a T_net reaction (DESIGN §B.2). -/
def NRxn.type : NRxn σ → TNet
  | .contact .. => .contact
  | .exit .. => .exit
  | .trans _ (some _) _ => .progress
  | .trans _ none _ => .remove
  | .resus .. => .resus
  | .nodeContact .. => .nodeContact

/-- The inclusion of T_EB syntax into T_net syntax. -/
def Rxn.toNRxn : Rxn σ → NRxn σ
  | .contact J X τ => .contact J X τ
  | .exit Y ν => .exit Y ν
  | .trans X Y a => .trans X Y a

/-- The partial inverse of `Rxn.toNRxn`: `some r` on T_EB reactions, `none` otherwise. -/
def NRxn.toRxn? : NRxn σ → Option (Rxn σ)
  | .contact J X τ => some (.contact J X τ)
  | .exit Y ν => some (.exit Y ν)
  | .trans X Y a => some (.trans X Y a)
  | .resus .. => none
  | .nodeContact .. => none

/-- A T_net reaction is *EB-admissible* if it is one of the T_EB types contact, exit, progress
or remove (DESIGN §B.2: EB is defined on Petri/T_EB). -/
def NRxn.EBAdmissible (r : NRxn σ) : Prop := r.toRxn?.isSome = true

/-- EB-admissibility is decidable. -/
instance NRxn.decEBAdmissible : DecidablePred (NRxn.EBAdmissible (σ := σ)) :=
  fun r => inferInstanceAs (Decidable (r.toRxn?.isSome = true))

/-- A reaction list is EB-admissible if every reaction is. -/
def NRxn.EBAdmissibleList (rs : List (NRxn σ)) : Prop := ∀ r ∈ rs, r.EBAdmissible

/-- EB-admissibility of a reaction list is decidable. -/
instance NRxn.decEBAdmissibleList (rs : List (NRxn σ)) : Decidable (NRxn.EBAdmissibleList rs) :=
  List.decidableBAll _ rs

/-- `NRxn.toRxn?` is a left inverse of the inclusion `Rxn.toNRxn`. -/
@[simp] theorem Rxn.toRxn?_toNRxn (r : Rxn σ) : r.toNRxn.toRxn? = some r := by
  cases r <;> rfl

/-- The inclusion of T_EB syntax into T_net syntax is injective. -/
theorem Rxn.toNRxn_injective : Function.Injective (Rxn.toNRxn (σ := σ)) := by
  intro r r' h
  have := congrArg NRxn.toRxn? h
  simpa using this

/-- EB-admissibility is exactly membership in the image of T_EB syntax. -/
theorem NRxn.ebAdmissible_iff (r : NRxn σ) : r.EBAdmissible ↔ ∃ r' : Rxn σ, r = r'.toNRxn := by
  constructor
  · intro h
    cases r with
    | contact J X τ => exact ⟨.contact J X τ, rfl⟩
    | exit Y ν => exact ⟨.exit Y ν, rfl⟩
    | trans X Y a => exact ⟨.trans X Y a, rfl⟩
    | resus X a => exact absurd h (by simp [EBAdmissible, toRxn?])
    | nodeContact X J Y τ => exact absurd h (by simp [EBAdmissible, toRxn?])
  · rintro ⟨r', rfl⟩
    simp [EBAdmissible]

/-- EB-admissibility is membership of the reaction's type in T_EB: "the sub-theory with no arrow
into Sus" (DESIGN §B.2).

Design statement (DESIGN_NetworkEpiCore.md §B.2): "**T_EB** = {contact, exit, progress,
remove}: the sub-theory with **no arrow into Sus**. **T_net** = all eight types."

Lean statement: for every type of node species `σ` and every T_net reaction `r : NRxn σ` (one
implicit susceptible species), `r` is EB-admissible (it is in the image of the T_EB syntax
`Rxn σ`) if and only if its type `r.type` is one of contact, exit, progress or remove, i.e.
`TNet.inTEB r.type = true`.

Scope: a statement about the syntax. It holds by case analysis, because `EBAdmissible` and
`TNet.inTEB` are parallel case tables; it checks that the two agree. T_EB is the list {contact,
exit, progress, remove}; the gloss "no arrow into Sus" does not characterise it in this syntax,
since `nodeContact` (X + J → Y + J with X, Y ∉ Σ) has no arrow into Sus and is not in T_EB.
`TNet` has six of the design's eight T_net types: `:sus_move` and `:sus_contact` need a second
susceptible species or a susceptible product, which `NRxn` does not represent. -/
theorem NRxn.ebAdmissible_iff_type (r : NRxn σ) : r.EBAdmissible ↔ r.type.inTEB = true := by
  cases r with
  | trans X Y a => cases Y <;> simp [EBAdmissible, toRxn?, type, TNet.inTEB]
  | _ => simp [EBAdmissible, toRxn?, type, TNet.inTEB]

/-- An EB-admissible T_net reaction comes from T_EB syntax. -/
theorem NRxn.eq_toNRxn_of_ebAdmissible {r : NRxn σ} (h : r.EBAdmissible) :
    ∃ r' : Rxn σ, r = r'.toNRxn :=
  (NRxn.ebAdmissible_iff r).mp h

/-- Resusceptibility `X → s` (§B.2 type `:resus`, e.g. SIS `I → S`) is not EB-admissible
(DESIGN executive summary: "The EB lift is strictly partial: SIS/SIRS are refused").

Design statement (DESIGN_NetworkEpiCore.md, executive summary item 6): "**The EB lift is
strictly partial**: SIS/SIRS are refused with the alternatives named"; §B.2 table (the first ✗
is the EB column): "NodeTransition X ∉ Σ, Y ∈ Σ | `:resus` | I → S (SIS), R → S (SIRS), I₁ → R₁
when R₁ can be infected | ✗".

Lean statement: for every node species `X` and rate `a`, the T_net reaction `X → s`
(`NRxn.resus X a`) is not EB-admissible, i.e. it is not in the image of the T_EB syntax `Rxn σ`.

Scope: a statement about the syntax, true by definition. It says that the EB field of this
library has no input for `X → s`. It is **not** a proof that no EB-type semantics for
resusceptibility exists. -/
theorem NRxn.not_ebAdmissible_resus (X : σ) (a : ℝ) : ¬ (NRxn.resus X a).EBAdmissible := by
  simp [EBAdmissible, toRxn?]

/-- A node contact `X + J → Y + J` with a node-species recipient (§B.2 type `:node_contact`) is not
EB-admissible. -/
theorem NRxn.not_ebAdmissible_nodeContact (X : σ) (J : Option σ) (Y : σ) (τ : ℝ) :
    ¬ (NRxn.nodeContact X J Y τ).EBAdmissible := by
  simp [EBAdmissible, toRxn?]

/-- T_EB ⊊ T_net: some T_net reaction is not EB-admissible (the resusceptibility `X → s`).

Design statement (DESIGN_NetworkEpiCore.md §D.1): "**Petri/T_EB ⊂ Petri/T_net ⊂ Petri**, and
the back ends are defined on these: EB on Petri/T_EB"; executive summary item 6: "**The EB lift is
strictly partial**".

Lean statement: there is a T_net reaction (over the node species `Unit`) that is not
EB-admissible, namely the resusceptibility `() → s` at rate 1.

Scope: a statement about the syntax (T_EB ⊊ T_net), true by definition; see
`not_ebAdmissible_resus`. -/
theorem NRxn.exists_not_ebAdmissible : ∃ r : NRxn Unit, ¬ r.EBAdmissible :=
  ⟨.resus () 1, NRxn.not_ebAdmissible_resus () 1⟩

/-! Decidability in action (§B.2 examples): SIR is EB-admissible; SIS (`I → S`, a `:resus`) and an
S-catalysed recovery `I + S → R + S` (a `:node_contact`) are not. -/

section Examples
/-- Node species of the examples below. -/
private inductive Sp where
  | I | R
  deriving DecidableEq

example : NRxn.EBAdmissibleList [NRxn.contact Sp.I Sp.I 1, NRxn.trans Sp.I (some Sp.R) 1] := by
  decide
example : ¬ NRxn.EBAdmissibleList [NRxn.contact Sp.I Sp.I 1, NRxn.resus Sp.I 1] := by
  decide
example : ¬ (NRxn.nodeContact Sp.I none Sp.R 1).EBAdmissible := by
  decide
end Examples

/-! ## Relabelling species (morphisms of syntax, DESIGN §D.1) -/

/-- Relabel the node species of a T_EB reaction along `f` (DESIGN §D.1: "Morphisms of syntax are
type-preserving species maps that carry reactions to reactions"). Gluing species along a cospan
is relabelling along the cospan legs. -/
def Rxn.map (f : σ → σ') : Rxn σ → Rxn σ'
  | .contact J X τ => .contact (f J) (f X) τ
  | .exit Y ν => .exit (f Y) ν
  | .trans X Y a => .trans (f X) (Y.map f) a

/-- Relabel the node species of a T_net reaction along `f`. -/
def NRxn.map (f : σ → σ') : NRxn σ → NRxn σ'
  | .contact J X τ => .contact (f J) (f X) τ
  | .exit Y ν => .exit (f Y) ν
  | .trans X Y a => .trans (f X) (Y.map f) a
  | .resus X a => .resus (f X) a
  | .nodeContact X J Y τ => .nodeContact (f X) (J.map f) (f Y) τ

/-- Relabelling along the identity is the identity. -/
@[simp] theorem Rxn.map_id (r : Rxn σ) : r.map id = r := by
  cases r with
  | trans X Y a => cases Y <;> rfl
  | _ => rfl

/-- Relabelling is functorial: relabelling along `f` then `g` is relabelling along `g ∘ f`. -/
theorem Rxn.map_map (f : σ → σ') (g : σ' → σ'') (r : Rxn σ) : (r.map f).map g = r.map (g ∘ f) := by
  cases r with
  | trans X Y a => cases Y <;> rfl
  | _ => rfl

/-- Relabelling a T_net reaction along the identity is the identity. -/
@[simp] theorem NRxn.map_id (r : NRxn σ) : r.map id = r := by
  cases r with
  | trans X Y a => cases Y <;> rfl
  | nodeContact X J Y τ => cases J <;> rfl
  | _ => rfl

/-- Relabelling T_net reactions is functorial. -/
theorem NRxn.map_map (f : σ → σ') (g : σ' → σ'') (r : NRxn σ) :
    (r.map f).map g = r.map (g ∘ f) := by
  cases r with
  | trans X Y a => cases Y <;> rfl
  | nodeContact X J Y τ => cases J <;> rfl
  | _ => rfl

/-- Relabelling commutes with the inclusion T_EB ⊂ T_net. -/
theorem Rxn.toNRxn_map (f : σ → σ') (r : Rxn σ) : (r.map f).toNRxn = r.toNRxn.map f := by
  cases r <;> rfl

/-- Relabelling preserves the type of a reaction (morphisms of syntax are type-preserving). -/
@[simp] theorem NRxn.type_map (f : σ → σ') (r : NRxn σ) : (r.map f).type = r.type := by
  cases r with
  | trans X Y a => cases Y <;> rfl
  | _ => rfl

/-- Relabelling preserves and reflects EB-admissibility. -/
theorem NRxn.ebAdmissible_map (f : σ → σ') (r : NRxn σ) :
    (r.map f).EBAdmissible ↔ r.EBAdmissible := by
  rw [ebAdmissible_iff_type, ebAdmissible_iff_type, type_map]

/-! ## Rate conventions (DESIGN §D.2: "Rate conventions are endofunctors c_λ that act reaction by
reaction") -/

/-- The rate convention `c_κ`: multiply every contact rate by `κ`, leaving exits and transitions
unchanged (DESIGN §D.5 M1 uses `c_κ` for the well-mixed unit, M3 uses `c_μ`). -/
def Rxn.scaleContacts (κ : ℝ) : Rxn σ → Rxn σ
  | .contact J X τ => .contact J X (κ * τ)
  | r => r

/-- `c_κ` commutes with relabelling (it acts reaction by reaction). -/
theorem Rxn.scaleContacts_map (κ : ℝ) (f : σ → σ') (r : Rxn σ) :
    (r.map f).scaleContacts κ = (r.scaleContacts κ).map f := by
  cases r <;> rfl

end NEP
