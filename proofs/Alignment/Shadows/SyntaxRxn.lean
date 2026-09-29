import Alignment.Registry
import NetworkEpi.Syntax.Rxn

/-!
# SA-PASS blind shadows: group `SyntaxRxn` (trusted module `NetworkEpi.Syntax.Rxn`)

Written blind. The author read only `SA-PASS_SKILL.md`, `Alignment/README.md`,
`Alignment/Example/ExampleShadows.lean`, `Alignment/DataTypes/SyntaxRxn.md`, the `SyntaxRxn` entries
of `Alignment/claims_blind.yaml` and `DESIGN_NetworkEpiCore.md` (§B.2, §B.6, §B.9, §D.1, §D.2,
§D.5 M1, §D.7 L2, executive summary). No theorem statement, definition body or checker was read.

Vocabulary (from `DataTypes/SyntaxRxn.md`): `Rxn σ` (T_EB syntax: `contact J X τ`, `exit Y ν`,
`trans X Y a`), `NRxn σ` (T_net syntax: the same plus `resus X a` and `nodeContact X J Y τ`),
`TNet` (the six representable T_net types), `NRxn.type`, `Rxn.toNRxn` (the inclusion),
`NRxn.toRxn?` (its partial inverse), `NRxn.EBAdmissible`, `NRxn.EBAdmissibleList`, the
relabellings `Rxn.map`, `NRxn.map`, and the rate convention `Rxn.scaleContacts κ` (= `c_κ`).

Conventions used throughout:
* Every claim is stated for every species type `σ : Type` (and every relabelling `f`, `g`, every
  rate `κ`), since the texts carry no restriction.
* Laws of relabelling (`map id`, `map ∘ map`, commuting with the inclusion, with `c_κ`, type
  preservation) are split **by constructor**: relabelling acts constructor by constructor, and each
  constructor's rule is one atomic requirement that a wrong implementation can break on its own.
* Iffs are split into their two directions; ambiguous phrases are split into their readings
  (marked `AMBIGUITY`), and the reference `T` is the conjunction of all readings.
-/

open NEP

namespace Alignment.Shadows.SyntaxRxn

/-- Membership of a T_net type in T_EB = {contact, exit, progress, remove} (DESIGN §B.2: "**T_EB** =
{contact, exit, progress, remove}"), written in primitive terms (not through `TNet.inTEB`). -/
def InTEB (t : TNet) : Prop :=
  t = .contact ∨ t = .exit ∨ t = .progress ∨ t = .remove

end Alignment.Shadows.SyntaxRxn

/-! ## `SyntaxRxn.toRxnToNRxn`

Blind text: "`NRxn.toRxn?` is a left inverse of the inclusion `Rxn.toNRxn`."

`toRxn?` is partial (`Option`-valued), so "left inverse" means `toRxn? (toNRxn r) = some r` for
every T_EB reaction `r` (equivalently `toRxn? ∘ toNRxn = some`). Split by the constructor of `r`. -/
namespace Alignment.Shadows.SyntaxRxn.ToRxnToNRxn

/-- Intended statement: for every σ and every T_EB reaction `r`, `toRxn?` recovers `r` from its
inclusion into T_net. -/
@[sa_reference "SyntaxRxn.toRxnToNRxn"]
def T : Prop := ∀ {σ : Type} (r : Rxn σ), r.toNRxn.toRxn? = some r

/-- S1: contacts are recovered. -/
@[sa_shadow "SyntaxRxn.toRxnToNRxn" 1]
def S1 : Prop :=
  ∀ {σ : Type} (J X : σ) (τ : ℝ), (Rxn.contact J X τ).toNRxn.toRxn? = some (Rxn.contact J X τ)

/-- S2: exits are recovered. -/
@[sa_shadow "SyntaxRxn.toRxnToNRxn" 2]
def S2 : Prop :=
  ∀ {σ : Type} (Y : σ) (ν : ℝ), (Rxn.exit Y ν).toNRxn.toRxn? = some (Rxn.exit Y ν)

/-- S3: node transitions (progressions `X → Y` and removals `X → ∅`) are recovered. -/
@[sa_shadow "SyntaxRxn.toRxnToNRxn" 3]
def S3 : Prop :=
  ∀ {σ : Type} (X : σ) (Y : Option σ) (a : ℝ),
    (Rxn.trans X Y a).toNRxn.toRxn? = some (Rxn.trans X Y a)

@[sa_ref_forward "SyntaxRxn.toRxnToNRxn" 1]
theorem ref_fwd1 : T → S1 := by intro t σ J X τ; exact t _

@[sa_ref_forward "SyntaxRxn.toRxnToNRxn" 2]
theorem ref_fwd2 : T → S2 := by intro t σ Y ν; exact t _

@[sa_ref_forward "SyntaxRxn.toRxnToNRxn" 3]
theorem ref_fwd3 : T → S3 := by intro t σ X Y a; exact t _

@[sa_complete "SyntaxRxn.toRxnToNRxn"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := by
  intro σ r
  cases r with
  | contact J X τ => exact s1 J X τ
  | exit Y ν => exact s2 Y ν
  | trans X Y a => exact s3 X Y a

end Alignment.Shadows.SyntaxRxn.ToRxnToNRxn

/-! ## `SyntaxRxn.toNRxnInjective`

Blind text: "The inclusion of T_EB syntax into T_net syntax is injective."

The inclusion is `Rxn.toNRxn`. Injectivity is split by the constructor of the first argument:
each shadow says that the included reaction determines the original one. -/
namespace Alignment.Shadows.SyntaxRxn.ToNRxnInjective

/-- Intended statement: for every σ, `Rxn.toNRxn : Rxn σ → NRxn σ` is injective. -/
@[sa_reference "SyntaxRxn.toNRxnInjective"]
def T : Prop := ∀ {σ : Type}, Function.Injective (Rxn.toNRxn (σ := σ))

/-- S1: an included contact is included from nothing but that contact. -/
@[sa_shadow "SyntaxRxn.toNRxnInjective" 1]
def S1 : Prop :=
  ∀ {σ : Type} (J X : σ) (τ : ℝ) (r : Rxn σ),
    (Rxn.contact J X τ).toNRxn = r.toNRxn → Rxn.contact J X τ = r

/-- S2: an included exit is included from nothing but that exit. -/
@[sa_shadow "SyntaxRxn.toNRxnInjective" 2]
def S2 : Prop :=
  ∀ {σ : Type} (Y : σ) (ν : ℝ) (r : Rxn σ), (Rxn.exit Y ν).toNRxn = r.toNRxn → Rxn.exit Y ν = r

/-- S3: an included node transition is included from nothing but that transition. -/
@[sa_shadow "SyntaxRxn.toNRxnInjective" 3]
def S3 : Prop :=
  ∀ {σ : Type} (X : σ) (Y : Option σ) (a : ℝ) (r : Rxn σ),
    (Rxn.trans X Y a).toNRxn = r.toNRxn → Rxn.trans X Y a = r

@[sa_ref_forward "SyntaxRxn.toNRxnInjective" 1]
theorem ref_fwd1 : T → S1 := by intro t σ J X τ r e; exact t e

@[sa_ref_forward "SyntaxRxn.toNRxnInjective" 2]
theorem ref_fwd2 : T → S2 := by intro t σ Y ν r e; exact t e

@[sa_ref_forward "SyntaxRxn.toNRxnInjective" 3]
theorem ref_fwd3 : T → S3 := by intro t σ X Y a r e; exact t e

@[sa_complete "SyntaxRxn.toNRxnInjective"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := by
  intro σ r₁ r₂ e
  cases r₁ with
  | contact J X τ => exact s1 J X τ r₂ e
  | exit Y ν => exact s2 Y ν r₂ e
  | trans X Y a => exact s3 X Y a r₂ e

end Alignment.Shadows.SyntaxRxn.ToNRxnInjective

/-! ## `SyntaxRxn.ebAdmissibleIff`

Blind text: "EB-admissibility is exactly membership in the image of T_EB syntax."

"The image of T_EB syntax" is the range of the inclusion `Rxn.toNRxn`. The text is an iff: one
shadow per direction. -/
namespace Alignment.Shadows.SyntaxRxn.EbAdmissibleIff

/-- Intended statement: for every σ, a T_net reaction is EB-admissible iff it lies in the range of
`Rxn.toNRxn`. -/
@[sa_reference "SyntaxRxn.ebAdmissibleIff"]
def T : Prop :=
  ∀ {σ : Type} (r : NRxn σ), r.EBAdmissible ↔ r ∈ Set.range (Rxn.toNRxn (σ := σ))

/-- S1: every EB-admissible T_net reaction is the inclusion of some T_EB reaction. -/
@[sa_shadow "SyntaxRxn.ebAdmissibleIff" 1]
def S1 : Prop := ∀ {σ : Type} (r : NRxn σ), r.EBAdmissible → ∃ r' : Rxn σ, r'.toNRxn = r

/-- S2: every T_net reaction in the image of T_EB syntax is EB-admissible. -/
@[sa_shadow "SyntaxRxn.ebAdmissibleIff" 2]
def S2 : Prop := ∀ {σ : Type} (r : NRxn σ), (∃ r' : Rxn σ, r'.toNRxn = r) → r.EBAdmissible

@[sa_ref_forward "SyntaxRxn.ebAdmissibleIff" 1]
theorem ref_fwd1 : T → S1 := by
  intro t σ r hr
  obtain ⟨r', e⟩ := (t r).mp hr
  exact ⟨r', e⟩

@[sa_ref_forward "SyntaxRxn.ebAdmissibleIff" 2]
theorem ref_fwd2 : T → S2 := by
  intro t σ r hr
  obtain ⟨r', e⟩ := hr
  exact (t r).mpr ⟨r', e⟩

@[sa_complete "SyntaxRxn.ebAdmissibleIff"]
theorem complete (s1 : S1) (s2 : S2) : T := by
  intro σ r
  constructor
  · intro hr
    obtain ⟨r', e⟩ := s1 r hr
    exact ⟨r', e⟩
  · intro hr
    obtain ⟨r', e⟩ := hr
    exact s2 r ⟨r', e⟩

end Alignment.Shadows.SyntaxRxn.EbAdmissibleIff

/-! ## `SyntaxRxn.ebAdmissibleIffType` (re-shadowed blind after the text remediation)

Blind text: "EB-admissibility is membership of the reaction's type in T_EB: "the sub-theory with no
arrow into Sus" (DESIGN §B.2). Design statement (DESIGN_NetworkEpiCore.md §B.2): "**T_EB** =
{contact, exit, progress, remove}: the sub-theory with **no arrow into Sus**. **T_net** = all eight
types." [...] T_EB is the list {contact, exit, progress, remove}; the gloss "no arrow into Sus" does
not characterise it in this syntax, since `nodeContact` (X + J → Y + J with X, Y ∉ Σ) has no arrow
into Sus and is not in T_EB. `TNet` has six of the design's eight T_net types: `:sus_move` and
`:sus_contact` need a second susceptible species or a susceptible product, which `NRxn` does not
represent."

Reading. The text now fixes T_EB as the *list* {contact, exit, progress, remove} (`InTEB`, written
in primitive terms, not via `TNet.inTEB`), and says explicitly that the gloss "no arrow into Sus" is
not the criterion. So the claim is one iff, for every species type σ and every T_net reaction `r`:
`r.EBAdmissible ↔ r.type ∈ T_EB`. One shadow per direction; each is falsifiable (S1 by an
admissibility that admits a `resus`/`nodeContact` reaction, S2 by one that refuses, e.g., a
`remove`/`exit` reaction).

Not formalised as requirements of this claim (explanatory remarks of the text):
* "`nodeContact` ... has no arrow into Sus and is not in T_EB" justifies discarding the gloss. It is
  a fact about the typing `NRxn.type` of `nodeContact` (header table: `nodeContact ↦ :node_contact`,
  which is not in the list), not about the relation between admissibility and the type. The
  consequence for admissibility is the separate claim on node contacts.
* "`TNet` has six of the design's eight T_net types" describes the data type `TNet` (DataTypes (d));
  it constrains no operation, so a shadow for it would be provable without the implementation.
* "no arrow into Sus" cannot be stated: there are no Petri-net arcs in the vocabulary (DataTypes (d)),
  and the text says it is not the criterion here. -/
namespace Alignment.Shadows.SyntaxRxn.EbAdmissibleIffType

open Alignment.Shadows.SyntaxRxn (InTEB)

/-- Intended statement: for every σ and every T_net reaction `r`, `r` is EB-admissible exactly
when its type is one of contact, exit, progress, remove. -/
@[sa_reference "SyntaxRxn.ebAdmissibleIffType"]
def T : Prop := ∀ {σ : Type} (r : NRxn σ), r.EBAdmissible ↔ InTEB r.type

/-- S1 (only-if): an EB-admissible reaction has type contact, exit, progress or remove. -/
@[sa_shadow "SyntaxRxn.ebAdmissibleIffType" 1]
def S1 : Prop := ∀ {σ : Type} (r : NRxn σ), r.EBAdmissible → InTEB r.type

/-- S2 (if): a reaction whose type is contact, exit, progress or remove is EB-admissible. -/
@[sa_shadow "SyntaxRxn.ebAdmissibleIffType" 2]
def S2 : Prop := ∀ {σ : Type} (r : NRxn σ), InTEB r.type → r.EBAdmissible

@[sa_ref_forward "SyntaxRxn.ebAdmissibleIffType" 1]
theorem ref_fwd1 : T → S1 := by intro t σ r; exact (t r).mp

@[sa_ref_forward "SyntaxRxn.ebAdmissibleIffType" 2]
theorem ref_fwd2 : T → S2 := by intro t σ r; exact (t r).mpr

@[sa_complete "SyntaxRxn.ebAdmissibleIffType"]
theorem complete (s1 : S1) (s2 : S2) : T := by
  intro σ r
  exact ⟨s1 r, s2 r⟩

end Alignment.Shadows.SyntaxRxn.EbAdmissibleIffType

/-! ## `SyntaxRxn.eqToNRxnOfEbAdmissible`

Blind text: "An EB-admissible T_net reaction comes from T_EB syntax."

"Comes from T_EB syntax" = is the inclusion `Rxn.toNRxn r'` of some T_EB reaction `r'`.
AMBIGUITY: the text does not mention `toRxn?`; the reading "comes from" = "lies in the image of
the inclusion" is formalised (the weakest reading that matches the words). A single atomic
requirement. -/
namespace Alignment.Shadows.SyntaxRxn.EqToNRxnOfEbAdmissible

/-- Intended statement: every EB-admissible T_net reaction lies in the range of `Rxn.toNRxn`. -/
@[sa_reference "SyntaxRxn.eqToNRxnOfEbAdmissible"]
def T : Prop :=
  ∀ {σ : Type} (r : NRxn σ), r.EBAdmissible → r ∈ Set.range (Rxn.toNRxn (σ := σ))

/-- S1: an EB-admissible T_net reaction is the inclusion of some T_EB reaction. -/
@[sa_shadow "SyntaxRxn.eqToNRxnOfEbAdmissible" 1]
def S1 : Prop := ∀ {σ : Type} (r : NRxn σ), r.EBAdmissible → ∃ r' : Rxn σ, r'.toNRxn = r

@[sa_ref_forward "SyntaxRxn.eqToNRxnOfEbAdmissible" 1]
theorem ref_fwd1 : T → S1 := by
  intro t σ r hr
  obtain ⟨r', e⟩ := t r hr
  exact ⟨r', e⟩

@[sa_complete "SyntaxRxn.eqToNRxnOfEbAdmissible"]
theorem complete (s1 : S1) : T := by
  intro σ r hr
  obtain ⟨r', e⟩ := s1 r hr
  exact ⟨r', e⟩

end Alignment.Shadows.SyntaxRxn.EqToNRxnOfEbAdmissible

/-! ## `SyntaxRxn.notEbAdmissibleResus`

Blind text: "Resusceptibility `X → s` (§B.2 type `:resus`, e.g. SIS `I → S`) is not EB-admissible
(DESIGN executive summary: "The EB lift is strictly partial: SIS/SIRS are refused"). Design
statement (DESIGN_NetworkEpiCore.md, executive summary item 6): "**The EB lift is strictly
partial**: SIS/SIRS are refused with the alternatives named"; §B.2 table (the first ✗ is the EB
column): "NodeTransition X ∉ Σ, Y ∈ Σ | `:resus` | I → S (SIS), R → S (SIRS), I₁ → R₁ when R₁ can
be infected | ✗"."

AMBIGUITY (three readings, all formalised; `T` is their conjunction):
* S1, the syntactic reading: every reaction `X → s`, i.e. every `NRxn.resus X a`, is refused.
* S2, the typing reading: the §B.2 table marks the *type* `:resus` with ✗ in the EB column, so
  every T_net reaction whose type is `:resus` is refused.
* S3, the model reading: "SIS/SIRS are refused" is about models; a model (reaction list) is
  EB-admissible iff every reaction is (docstring of `NRxn.EBAdmissibleList`), and SIS (`I → S`)
  and SIRS (`R → S`) are refused because they contain a resusceptibility. Stated for every model
  that contains one, which covers SIS and SIRS.
"with the alternatives named" (error texts) is not representable (DataTypes (d)). -/
namespace Alignment.Shadows.SyntaxRxn.NotEbAdmissibleResus

/-- Intended statement: the conjunction of the three readings. -/
@[sa_reference "SyntaxRxn.notEbAdmissibleResus"]
def T : Prop :=
  (∀ {σ : Type} (X : σ) (a : ℝ), ¬ (NRxn.resus X a).EBAdmissible) ∧
    (∀ {σ : Type} (r : NRxn σ), r.type = TNet.resus → ¬ r.EBAdmissible) ∧
    (∀ {σ : Type} (rs : List (NRxn σ)) (X : σ) (a : ℝ),
      NRxn.resus X a ∈ rs → ¬ NRxn.EBAdmissibleList rs)

/-- S1: no resusceptibility `X → s` is EB-admissible. -/
@[sa_shadow "SyntaxRxn.notEbAdmissibleResus" 1]
def S1 : Prop := ∀ {σ : Type} (X : σ) (a : ℝ), ¬ (NRxn.resus X a).EBAdmissible

/-- S2: no T_net reaction of type `:resus` is EB-admissible. -/
@[sa_shadow "SyntaxRxn.notEbAdmissibleResus" 2]
def S2 : Prop := ∀ {σ : Type} (r : NRxn σ), r.type = TNet.resus → ¬ r.EBAdmissible

/-- S3: a model containing a resusceptibility (SIS `I → S`, SIRS `R → S`) is refused. -/
@[sa_shadow "SyntaxRxn.notEbAdmissibleResus" 3]
def S3 : Prop :=
  ∀ {σ : Type} (rs : List (NRxn σ)) (X : σ) (a : ℝ),
    NRxn.resus X a ∈ rs → ¬ NRxn.EBAdmissibleList rs

@[sa_ref_forward "SyntaxRxn.notEbAdmissibleResus" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "SyntaxRxn.notEbAdmissibleResus" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1

@[sa_ref_forward "SyntaxRxn.notEbAdmissibleResus" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2

@[sa_complete "SyntaxRxn.notEbAdmissibleResus"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.SyntaxRxn.NotEbAdmissibleResus

/-! ## `SyntaxRxn.notEbAdmissibleNodeContact`

Blind text: "A node contact `X + J → Y + J` with a node-species recipient (§B.2 type
`:node_contact`) is not EB-admissible."

Split: the catalyst is either the susceptible species (`J = none`, e.g. the S-catalysed recovery
`I + S → R + S` of §B.2) or a node species (`J = some J'`, e.g. tracing of infecteds).
AMBIGUITY: as for resusceptibility, the parenthetical type gives a typing reading (S3): every
T_net reaction of type `:node_contact` is refused. -/
namespace Alignment.Shadows.SyntaxRxn.NotEbAdmissibleNodeContact

/-- Intended statement: no node contact is EB-admissible, whatever its catalyst, and no reaction
of type `:node_contact` is. -/
@[sa_reference "SyntaxRxn.notEbAdmissibleNodeContact"]
def T : Prop :=
  (∀ {σ : Type} (X : σ) (J : Option σ) (Y : σ) (τ : ℝ),
      ¬ (NRxn.nodeContact X J Y τ).EBAdmissible) ∧
    (∀ {σ : Type} (r : NRxn σ), r.type = TNet.nodeContact → ¬ r.EBAdmissible)

/-- S1: a node contact catalysed by the susceptible species (`X + s → Y + s`) is refused. -/
@[sa_shadow "SyntaxRxn.notEbAdmissibleNodeContact" 1]
def S1 : Prop :=
  ∀ {σ : Type} (X Y : σ) (τ : ℝ), ¬ (NRxn.nodeContact X none Y τ).EBAdmissible

/-- S2: a node contact catalysed by a node species (`X + J → Y + J`, `J ∈ σ`) is refused. -/
@[sa_shadow "SyntaxRxn.notEbAdmissibleNodeContact" 2]
def S2 : Prop :=
  ∀ {σ : Type} (X J Y : σ) (τ : ℝ), ¬ (NRxn.nodeContact X (some J) Y τ).EBAdmissible

/-- S3: no T_net reaction of type `:node_contact` is EB-admissible. -/
@[sa_shadow "SyntaxRxn.notEbAdmissibleNodeContact" 3]
def S3 : Prop := ∀ {σ : Type} (r : NRxn σ), r.type = TNet.nodeContact → ¬ r.EBAdmissible

@[sa_ref_forward "SyntaxRxn.notEbAdmissibleNodeContact" 1]
theorem ref_fwd1 : T → S1 := by intro t σ X Y τ; exact t.1 X none Y τ

@[sa_ref_forward "SyntaxRxn.notEbAdmissibleNodeContact" 2]
theorem ref_fwd2 : T → S2 := by intro t σ X J Y τ; exact t.1 X (some J) Y τ

@[sa_ref_forward "SyntaxRxn.notEbAdmissibleNodeContact" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2

@[sa_complete "SyntaxRxn.notEbAdmissibleNodeContact"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := by
  refine ⟨?_, s3⟩
  intro σ X J Y τ
  cases J with
  | none => exact s1 X Y τ
  | some J => exact s2 X J Y τ

end Alignment.Shadows.SyntaxRxn.NotEbAdmissibleNodeContact

/-! ## `SyntaxRxn.existsNotEbAdmissible`

Blind text: "T_EB ⊊ T_net: some T_net reaction is not EB-admissible (the resusceptibility
`X → s`). Design statement (DESIGN_NetworkEpiCore.md §D.1): "**Petri/T_EB ⊂ Petri/T_net ⊂
Petri**, and the back ends are defined on these: EB on Petri/T_EB"; executive summary item 6:
"**The EB lift is strictly partial**"."

AMBIGUITY (quantifier over species types): `NRxn σ` is empty when `σ` is (every constructor names a
node species), so "some T_net reaction" can only hold for inhabited `σ`. The general reading is
formalised: for every species type with at least one node species `X` (the resusceptibility
`X → s` needs one). The parenthetical names the witness; it is read as a proof hint, not as part
of the statement.

AMBIGUITY (two readings of "T_EB ⊊ T_net"; `T` is their conjunction):
* S1, the text's own gloss: some T_net reaction is not EB-admissible;
* S2, strictness of the inclusion `Rxn.toNRxn` (DataTypes (d): "T_EB ⊂ T_net" is expressed with the
  inclusion and its image): some T_net reaction is not the inclusion of any T_EB reaction.
The non-strict part "⊂" is the existence of the inclusion `Rxn.toNRxn` (a definition; its
injectivity is claim `SyntaxRxn.toNRxnInjective`). "The back ends are defined on these: EB on
Petri/T_EB" concerns `ebField`, which is outside this module's vocabulary. -/
namespace Alignment.Shadows.SyntaxRxn.ExistsNotEbAdmissible

/-- Intended statement: over every inhabited species type, some T_net reaction is not
EB-admissible, and some T_net reaction is outside the image of T_EB syntax. -/
@[sa_reference "SyntaxRxn.existsNotEbAdmissible"]
def T : Prop :=
  (∀ {σ : Type} (_X : σ), ∃ r : NRxn σ, ¬ r.EBAdmissible) ∧
    (∀ {σ : Type} (_X : σ), ∃ r : NRxn σ, r ∉ Set.range (Rxn.toNRxn (σ := σ)))

/-- S1: some T_net reaction is not EB-admissible. -/
@[sa_shadow "SyntaxRxn.existsNotEbAdmissible" 1]
def S1 : Prop := ∀ {σ : Type} (_X : σ), ∃ r : NRxn σ, ¬ r.EBAdmissible

/-- S2: the inclusion of T_EB syntax into T_net syntax is not onto. -/
@[sa_shadow "SyntaxRxn.existsNotEbAdmissible" 2]
def S2 : Prop := ∀ {σ : Type} (_X : σ), ∃ r : NRxn σ, ∀ r' : Rxn σ, r'.toNRxn ≠ r

@[sa_ref_forward "SyntaxRxn.existsNotEbAdmissible" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "SyntaxRxn.existsNotEbAdmissible" 2]
theorem ref_fwd2 : T → S2 := by
  intro t σ X
  obtain ⟨r, hr⟩ := t.2 X
  exact ⟨r, fun r' e => hr ⟨r', e⟩⟩

@[sa_complete "SyntaxRxn.existsNotEbAdmissible"]
theorem complete (s1 : S1) (s2 : S2) : T := by
  refine ⟨s1, ?_⟩
  intro σ X
  obtain ⟨r, hr⟩ := s2 X
  refine ⟨r, ?_⟩
  rintro ⟨r', e⟩
  exact hr r' e

end Alignment.Shadows.SyntaxRxn.ExistsNotEbAdmissible

/-! ## `SyntaxRxn.rxnMapId`

Blind text: "Relabelling along the identity is the identity."

Relabelling a T_EB reaction is `Rxn.map`; the identity of species is `id`. For every σ and every
T_EB reaction `r`, `r.map id = r` (equivalently `Rxn.map id = id`). Split by constructor. -/
namespace Alignment.Shadows.SyntaxRxn.RxnMapId

/-- Intended statement: relabelling along `id` fixes every T_EB reaction. -/
@[sa_reference "SyntaxRxn.rxnMapId"]
def T : Prop := ∀ {σ : Type} (r : Rxn σ), r.map id = r

/-- S1: identity relabelling fixes contacts. -/
@[sa_shadow "SyntaxRxn.rxnMapId" 1]
def S1 : Prop := ∀ {σ : Type} (J X : σ) (τ : ℝ), (Rxn.contact J X τ).map id = Rxn.contact J X τ

/-- S2: identity relabelling fixes exits. -/
@[sa_shadow "SyntaxRxn.rxnMapId" 2]
def S2 : Prop := ∀ {σ : Type} (Y : σ) (ν : ℝ), (Rxn.exit Y ν).map id = Rxn.exit Y ν

/-- S3: identity relabelling fixes node transitions (including removals `X → ∅`). -/
@[sa_shadow "SyntaxRxn.rxnMapId" 3]
def S3 : Prop :=
  ∀ {σ : Type} (X : σ) (Y : Option σ) (a : ℝ), (Rxn.trans X Y a).map id = Rxn.trans X Y a

@[sa_ref_forward "SyntaxRxn.rxnMapId" 1]
theorem ref_fwd1 : T → S1 := by intro t σ J X τ; exact t _

@[sa_ref_forward "SyntaxRxn.rxnMapId" 2]
theorem ref_fwd2 : T → S2 := by intro t σ Y ν; exact t _

@[sa_ref_forward "SyntaxRxn.rxnMapId" 3]
theorem ref_fwd3 : T → S3 := by intro t σ X Y a; exact t _

@[sa_complete "SyntaxRxn.rxnMapId"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := by
  intro σ r
  cases r with
  | contact J X τ => exact s1 J X τ
  | exit Y ν => exact s2 Y ν
  | trans X Y a => exact s3 X Y a

end Alignment.Shadows.SyntaxRxn.RxnMapId

/-! ## `SyntaxRxn.rxnMapMap`

Blind text: "Relabelling is functorial: relabelling along `f` then `g` is relabelling along
`g ∘ f`."

The colon spells out what "functorial" asserts here: the composition law, for all species types
and all maps `f : σ → σ'`, `g : σ' → σ''`. AMBIGUITY: the identity law is the separate claim
`SyntaxRxn.rxnMapId`; since the text defines "functorial" by the composition law, only that law
is formalised. Split by constructor. -/
namespace Alignment.Shadows.SyntaxRxn.RxnMapMap

/-- Intended statement: `(r.map f).map g = r.map (g ∘ f)` for every T_EB reaction. -/
@[sa_reference "SyntaxRxn.rxnMapMap"]
def T : Prop :=
  ∀ {σ σ' σ'' : Type} (f : σ → σ') (g : σ' → σ'') (r : Rxn σ), (r.map f).map g = r.map (g ∘ f)

/-- S1: the composition law on contacts. -/
@[sa_shadow "SyntaxRxn.rxnMapMap" 1]
def S1 : Prop :=
  ∀ {σ σ' σ'' : Type} (f : σ → σ') (g : σ' → σ'') (J X : σ) (τ : ℝ),
    ((Rxn.contact J X τ).map f).map g = (Rxn.contact J X τ).map (g ∘ f)

/-- S2: the composition law on exits. -/
@[sa_shadow "SyntaxRxn.rxnMapMap" 2]
def S2 : Prop :=
  ∀ {σ σ' σ'' : Type} (f : σ → σ') (g : σ' → σ'') (Y : σ) (ν : ℝ),
    ((Rxn.exit Y ν).map f).map g = (Rxn.exit Y ν).map (g ∘ f)

/-- S3: the composition law on node transitions. -/
@[sa_shadow "SyntaxRxn.rxnMapMap" 3]
def S3 : Prop :=
  ∀ {σ σ' σ'' : Type} (f : σ → σ') (g : σ' → σ'') (X : σ) (Y : Option σ) (a : ℝ),
    ((Rxn.trans X Y a).map f).map g = (Rxn.trans X Y a).map (g ∘ f)

@[sa_ref_forward "SyntaxRxn.rxnMapMap" 1]
theorem ref_fwd1 : T → S1 := by intro t σ σ' σ'' f g J X τ; exact t f g _

@[sa_ref_forward "SyntaxRxn.rxnMapMap" 2]
theorem ref_fwd2 : T → S2 := by intro t σ σ' σ'' f g Y ν; exact t f g _

@[sa_ref_forward "SyntaxRxn.rxnMapMap" 3]
theorem ref_fwd3 : T → S3 := by intro t σ σ' σ'' f g X Y a; exact t f g _

@[sa_complete "SyntaxRxn.rxnMapMap"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := by
  intro σ σ' σ'' f g r
  cases r with
  | contact J X τ => exact s1 f g J X τ
  | exit Y ν => exact s2 f g Y ν
  | trans X Y a => exact s3 f g X Y a

end Alignment.Shadows.SyntaxRxn.RxnMapMap

/-! ## `SyntaxRxn.nRxnMapId`

Blind text: "Relabelling a T_net reaction along the identity is the identity."

For every σ and every T_net reaction `r`, `r.map id = r`. Split by the five constructors. -/
namespace Alignment.Shadows.SyntaxRxn.NRxnMapId

/-- Intended statement: relabelling along `id` fixes every T_net reaction. -/
@[sa_reference "SyntaxRxn.nRxnMapId"]
def T : Prop := ∀ {σ : Type} (r : NRxn σ), r.map id = r

/-- S1: identity relabelling fixes contacts. -/
@[sa_shadow "SyntaxRxn.nRxnMapId" 1]
def S1 : Prop :=
  ∀ {σ : Type} (J X : σ) (τ : ℝ), (NRxn.contact J X τ).map id = NRxn.contact J X τ

/-- S2: identity relabelling fixes exits. -/
@[sa_shadow "SyntaxRxn.nRxnMapId" 2]
def S2 : Prop := ∀ {σ : Type} (Y : σ) (ν : ℝ), (NRxn.exit Y ν).map id = NRxn.exit Y ν

/-- S3: identity relabelling fixes node transitions (including removals `X → ∅`). -/
@[sa_shadow "SyntaxRxn.nRxnMapId" 3]
def S3 : Prop :=
  ∀ {σ : Type} (X : σ) (Y : Option σ) (a : ℝ), (NRxn.trans X Y a).map id = NRxn.trans X Y a

/-- S4: identity relabelling fixes resusceptibilities `X → s`. -/
@[sa_shadow "SyntaxRxn.nRxnMapId" 4]
def S4 : Prop := ∀ {σ : Type} (X : σ) (a : ℝ), (NRxn.resus X a).map id = NRxn.resus X a

/-- S5: identity relabelling fixes node contacts `X + J → Y + J` (either kind of catalyst). -/
@[sa_shadow "SyntaxRxn.nRxnMapId" 5]
def S5 : Prop :=
  ∀ {σ : Type} (X : σ) (J : Option σ) (Y : σ) (τ : ℝ),
    (NRxn.nodeContact X J Y τ).map id = NRxn.nodeContact X J Y τ

@[sa_ref_forward "SyntaxRxn.nRxnMapId" 1]
theorem ref_fwd1 : T → S1 := by intro t σ J X τ; exact t _

@[sa_ref_forward "SyntaxRxn.nRxnMapId" 2]
theorem ref_fwd2 : T → S2 := by intro t σ Y ν; exact t _

@[sa_ref_forward "SyntaxRxn.nRxnMapId" 3]
theorem ref_fwd3 : T → S3 := by intro t σ X Y a; exact t _

@[sa_ref_forward "SyntaxRxn.nRxnMapId" 4]
theorem ref_fwd4 : T → S4 := by intro t σ X a; exact t _

@[sa_ref_forward "SyntaxRxn.nRxnMapId" 5]
theorem ref_fwd5 : T → S5 := by intro t σ X J Y τ; exact t _

@[sa_complete "SyntaxRxn.nRxnMapId"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) : T := by
  intro σ r
  cases r with
  | contact J X τ => exact s1 J X τ
  | exit Y ν => exact s2 Y ν
  | trans X Y a => exact s3 X Y a
  | resus X a => exact s4 X a
  | nodeContact X J Y τ => exact s5 X J Y τ

end Alignment.Shadows.SyntaxRxn.NRxnMapId

/-! ## `SyntaxRxn.nRxnMapMap`

Blind text: "Relabelling T_net reactions is functorial."

AMBIGUITY: unlike `SyntaxRxn.rxnMapMap`, this text does not spell out which law it means. A
functor preserves composition **and** identities, so both laws are formalised (S1–S5: composition,
split by constructor; S6: identities). The reading "composition only" (by analogy with the gloss
of `SyntaxRxn.rxnMapMap`) is contained in S1–S5. -/
namespace Alignment.Shadows.SyntaxRxn.NRxnMapMap

/-- Intended statement: relabelling T_net reactions preserves composition and identities. -/
@[sa_reference "SyntaxRxn.nRxnMapMap"]
def T : Prop :=
  (∀ {σ σ' σ'' : Type} (f : σ → σ') (g : σ' → σ'') (r : NRxn σ),
      (r.map f).map g = r.map (g ∘ f)) ∧
    (∀ {σ : Type} (r : NRxn σ), r.map id = r)

/-- S1: the composition law on contacts. -/
@[sa_shadow "SyntaxRxn.nRxnMapMap" 1]
def S1 : Prop :=
  ∀ {σ σ' σ'' : Type} (f : σ → σ') (g : σ' → σ'') (J X : σ) (τ : ℝ),
    ((NRxn.contact J X τ).map f).map g = (NRxn.contact J X τ).map (g ∘ f)

/-- S2: the composition law on exits. -/
@[sa_shadow "SyntaxRxn.nRxnMapMap" 2]
def S2 : Prop :=
  ∀ {σ σ' σ'' : Type} (f : σ → σ') (g : σ' → σ'') (Y : σ) (ν : ℝ),
    ((NRxn.exit Y ν).map f).map g = (NRxn.exit Y ν).map (g ∘ f)

/-- S3: the composition law on node transitions. -/
@[sa_shadow "SyntaxRxn.nRxnMapMap" 3]
def S3 : Prop :=
  ∀ {σ σ' σ'' : Type} (f : σ → σ') (g : σ' → σ'') (X : σ) (Y : Option σ) (a : ℝ),
    ((NRxn.trans X Y a).map f).map g = (NRxn.trans X Y a).map (g ∘ f)

/-- S4: the composition law on resusceptibilities. -/
@[sa_shadow "SyntaxRxn.nRxnMapMap" 4]
def S4 : Prop :=
  ∀ {σ σ' σ'' : Type} (f : σ → σ') (g : σ' → σ'') (X : σ) (a : ℝ),
    ((NRxn.resus X a).map f).map g = (NRxn.resus X a).map (g ∘ f)

/-- S5: the composition law on node contacts. -/
@[sa_shadow "SyntaxRxn.nRxnMapMap" 5]
def S5 : Prop :=
  ∀ {σ σ' σ'' : Type} (f : σ → σ') (g : σ' → σ'') (X : σ) (J : Option σ) (Y : σ) (τ : ℝ),
    ((NRxn.nodeContact X J Y τ).map f).map g = (NRxn.nodeContact X J Y τ).map (g ∘ f)

/-- S6: the identity law (relabelling along `id` fixes every T_net reaction). -/
@[sa_shadow "SyntaxRxn.nRxnMapMap" 6]
def S6 : Prop := ∀ {σ : Type} (r : NRxn σ), r.map id = r

@[sa_ref_forward "SyntaxRxn.nRxnMapMap" 1]
theorem ref_fwd1 : T → S1 := by intro t σ σ' σ'' f g J X τ; exact t.1 f g _

@[sa_ref_forward "SyntaxRxn.nRxnMapMap" 2]
theorem ref_fwd2 : T → S2 := by intro t σ σ' σ'' f g Y ν; exact t.1 f g _

@[sa_ref_forward "SyntaxRxn.nRxnMapMap" 3]
theorem ref_fwd3 : T → S3 := by intro t σ σ' σ'' f g X Y a; exact t.1 f g _

@[sa_ref_forward "SyntaxRxn.nRxnMapMap" 4]
theorem ref_fwd4 : T → S4 := by intro t σ σ' σ'' f g X a; exact t.1 f g _

@[sa_ref_forward "SyntaxRxn.nRxnMapMap" 5]
theorem ref_fwd5 : T → S5 := by intro t σ σ' σ'' f g X J Y τ; exact t.1 f g _

@[sa_ref_forward "SyntaxRxn.nRxnMapMap" 6]
theorem ref_fwd6 : T → S6 := fun t => t.2

@[sa_complete "SyntaxRxn.nRxnMapMap"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) : T := by
  refine ⟨?_, s6⟩
  intro σ σ' σ'' f g r
  cases r with
  | contact J X τ => exact s1 f g J X τ
  | exit Y ν => exact s2 f g Y ν
  | trans X Y a => exact s3 f g X Y a
  | resus X a => exact s4 f g X a
  | nodeContact X J Y τ => exact s5 f g X J Y τ

end Alignment.Shadows.SyntaxRxn.NRxnMapMap

/-! ## `SyntaxRxn.toNRxnMap`

Blind text: "Relabelling commutes with the inclusion T_EB ⊂ T_net."

For all σ, σ', every `f : σ → σ'` and every T_EB reaction `r`:
`(r.map f).toNRxn = r.toNRxn.map f` (equivalently `Rxn.toNRxn ∘ Rxn.map f = NRxn.map f ∘
Rxn.toNRxn`). Split by constructor. -/
namespace Alignment.Shadows.SyntaxRxn.ToNRxnMap

/-- Intended statement: including then relabelling equals relabelling then including. -/
@[sa_reference "SyntaxRxn.toNRxnMap"]
def T : Prop := ∀ {σ σ' : Type} (f : σ → σ') (r : Rxn σ), (r.map f).toNRxn = r.toNRxn.map f

/-- S1: the square commutes on contacts. -/
@[sa_shadow "SyntaxRxn.toNRxnMap" 1]
def S1 : Prop :=
  ∀ {σ σ' : Type} (f : σ → σ') (J X : σ) (τ : ℝ),
    ((Rxn.contact J X τ).map f).toNRxn = (Rxn.contact J X τ).toNRxn.map f

/-- S2: the square commutes on exits. -/
@[sa_shadow "SyntaxRxn.toNRxnMap" 2]
def S2 : Prop :=
  ∀ {σ σ' : Type} (f : σ → σ') (Y : σ) (ν : ℝ),
    ((Rxn.exit Y ν).map f).toNRxn = (Rxn.exit Y ν).toNRxn.map f

/-- S3: the square commutes on node transitions. -/
@[sa_shadow "SyntaxRxn.toNRxnMap" 3]
def S3 : Prop :=
  ∀ {σ σ' : Type} (f : σ → σ') (X : σ) (Y : Option σ) (a : ℝ),
    ((Rxn.trans X Y a).map f).toNRxn = (Rxn.trans X Y a).toNRxn.map f

@[sa_ref_forward "SyntaxRxn.toNRxnMap" 1]
theorem ref_fwd1 : T → S1 := by intro t σ σ' f J X τ; exact t f _

@[sa_ref_forward "SyntaxRxn.toNRxnMap" 2]
theorem ref_fwd2 : T → S2 := by intro t σ σ' f Y ν; exact t f _

@[sa_ref_forward "SyntaxRxn.toNRxnMap" 3]
theorem ref_fwd3 : T → S3 := by intro t σ σ' f X Y a; exact t f _

@[sa_complete "SyntaxRxn.toNRxnMap"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := by
  intro σ σ' f r
  cases r with
  | contact J X τ => exact s1 f J X τ
  | exit Y ν => exact s2 f Y ν
  | trans X Y a => exact s3 f X Y a

end Alignment.Shadows.SyntaxRxn.ToNRxnMap

/-! ## `SyntaxRxn.typeMap`

Blind text: "Relabelling preserves the type of a reaction (morphisms of syntax are
type-preserving)."

The type of a T_net reaction is `NRxn.type`; relabelling is `NRxn.map f` for any `f : σ → σ'`.
Split by constructor, with node transitions split into progressions (`Y = some _`, type
`:progress`) and removals (`Y = none`, type `:remove`), since these carry different types.
AMBIGUITY: T_EB reactions are reactions too (DESIGN §D.1: morphisms of syntax include relabelling
of T_EB-typed nets). Their type is the type of their inclusion, so S7 states that relabelling a
T_EB reaction along `Rxn.map` preserves that type. -/
namespace Alignment.Shadows.SyntaxRxn.TypeMap

/-- Intended statement: relabelling preserves the type of every T_net reaction, and of every
T_EB reaction (through the inclusion). -/
@[sa_reference "SyntaxRxn.typeMap"]
def T : Prop :=
  (∀ {σ σ' : Type} (f : σ → σ') (r : NRxn σ), (r.map f).type = r.type) ∧
    (∀ {σ σ' : Type} (f : σ → σ') (r : Rxn σ), (r.map f).toNRxn.type = r.toNRxn.type)

/-- S1: relabelling a contact keeps its type. -/
@[sa_shadow "SyntaxRxn.typeMap" 1]
def S1 : Prop :=
  ∀ {σ σ' : Type} (f : σ → σ') (J X : σ) (τ : ℝ),
    ((NRxn.contact J X τ).map f).type = (NRxn.contact J X τ).type

/-- S2: relabelling an exit keeps its type. -/
@[sa_shadow "SyntaxRxn.typeMap" 2]
def S2 : Prop :=
  ∀ {σ σ' : Type} (f : σ → σ') (Y : σ) (ν : ℝ), ((NRxn.exit Y ν).map f).type = (NRxn.exit Y ν).type

/-- S3: relabelling a progression `X → Y` keeps its type. -/
@[sa_shadow "SyntaxRxn.typeMap" 3]
def S3 : Prop :=
  ∀ {σ σ' : Type} (f : σ → σ') (X Y : σ) (a : ℝ),
    ((NRxn.trans X (some Y) a).map f).type = (NRxn.trans X (some Y) a).type

/-- S4: relabelling a removal `X → ∅` keeps its type. -/
@[sa_shadow "SyntaxRxn.typeMap" 4]
def S4 : Prop :=
  ∀ {σ σ' : Type} (f : σ → σ') (X : σ) (a : ℝ),
    ((NRxn.trans X none a).map f).type = (NRxn.trans X none a).type

/-- S5: relabelling a resusceptibility keeps its type. -/
@[sa_shadow "SyntaxRxn.typeMap" 5]
def S5 : Prop :=
  ∀ {σ σ' : Type} (f : σ → σ') (X : σ) (a : ℝ),
    ((NRxn.resus X a).map f).type = (NRxn.resus X a).type

/-- S6: relabelling a node contact keeps its type. -/
@[sa_shadow "SyntaxRxn.typeMap" 6]
def S6 : Prop :=
  ∀ {σ σ' : Type} (f : σ → σ') (X : σ) (J : Option σ) (Y : σ) (τ : ℝ),
    ((NRxn.nodeContact X J Y τ).map f).type = (NRxn.nodeContact X J Y τ).type

/-- S7: relabelling a T_EB reaction keeps the type of its inclusion. -/
@[sa_shadow "SyntaxRxn.typeMap" 7]
def S7 : Prop :=
  ∀ {σ σ' : Type} (f : σ → σ') (r : Rxn σ), (r.map f).toNRxn.type = r.toNRxn.type

@[sa_ref_forward "SyntaxRxn.typeMap" 1]
theorem ref_fwd1 : T → S1 := by intro t σ σ' f J X τ; exact t.1 f _

@[sa_ref_forward "SyntaxRxn.typeMap" 2]
theorem ref_fwd2 : T → S2 := by intro t σ σ' f Y ν; exact t.1 f _

@[sa_ref_forward "SyntaxRxn.typeMap" 3]
theorem ref_fwd3 : T → S3 := by intro t σ σ' f X Y a; exact t.1 f _

@[sa_ref_forward "SyntaxRxn.typeMap" 4]
theorem ref_fwd4 : T → S4 := by intro t σ σ' f X a; exact t.1 f _

@[sa_ref_forward "SyntaxRxn.typeMap" 5]
theorem ref_fwd5 : T → S5 := by intro t σ σ' f X a; exact t.1 f _

@[sa_ref_forward "SyntaxRxn.typeMap" 6]
theorem ref_fwd6 : T → S6 := by intro t σ σ' f X J Y τ; exact t.1 f _

@[sa_ref_forward "SyntaxRxn.typeMap" 7]
theorem ref_fwd7 : T → S7 := fun t => t.2

@[sa_complete "SyntaxRxn.typeMap"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) (s7 : S7) : T := by
  refine ⟨?_, s7⟩
  intro σ σ' f r
  cases r with
  | contact J X τ => exact s1 f J X τ
  | exit Y ν => exact s2 f Y ν
  | trans X Y a =>
    cases Y with
    | none => exact s4 f X a
    | some Y => exact s3 f X Y a
  | resus X a => exact s5 f X a
  | nodeContact X J Y τ => exact s6 f X J Y τ

end Alignment.Shadows.SyntaxRxn.TypeMap

/-! ## `SyntaxRxn.ebAdmissibleMap`

Blind text: "Relabelling preserves and reflects EB-admissibility."

For all σ, σ', every `f : σ → σ'` (no injectivity is assumed: the text has none, and DESIGN §B.9
allows merges) and every T_net reaction `r`. "Preserves" and "reflects" are the two directions. -/
namespace Alignment.Shadows.SyntaxRxn.EbAdmissibleMap

/-- Intended statement: `r.map f` is EB-admissible iff `r` is. -/
@[sa_reference "SyntaxRxn.ebAdmissibleMap"]
def T : Prop :=
  ∀ {σ σ' : Type} (f : σ → σ') (r : NRxn σ), (r.map f).EBAdmissible ↔ r.EBAdmissible

/-- S1 (preserves): relabelling an EB-admissible reaction gives an EB-admissible reaction. -/
@[sa_shadow "SyntaxRxn.ebAdmissibleMap" 1]
def S1 : Prop :=
  ∀ {σ σ' : Type} (f : σ → σ') (r : NRxn σ), r.EBAdmissible → (r.map f).EBAdmissible

/-- S2 (reflects): if a relabelled reaction is EB-admissible, so is the original. -/
@[sa_shadow "SyntaxRxn.ebAdmissibleMap" 2]
def S2 : Prop :=
  ∀ {σ σ' : Type} (f : σ → σ') (r : NRxn σ), (r.map f).EBAdmissible → r.EBAdmissible

@[sa_ref_forward "SyntaxRxn.ebAdmissibleMap" 1]
theorem ref_fwd1 : T → S1 := by intro t σ σ' f r; exact (t f r).mpr

@[sa_ref_forward "SyntaxRxn.ebAdmissibleMap" 2]
theorem ref_fwd2 : T → S2 := by intro t σ σ' f r; exact (t f r).mp

@[sa_complete "SyntaxRxn.ebAdmissibleMap"]
theorem complete (s1 : S1) (s2 : S2) : T := by
  intro σ σ' f r
  exact ⟨s2 f r, s1 f r⟩

end Alignment.Shadows.SyntaxRxn.EbAdmissibleMap

/-! ## `SyntaxRxn.scaleContactsMap`

Blind text: "`c_κ` commutes with relabelling (it acts reaction by reaction)."

`c_κ` is `Rxn.scaleContacts κ` (DataTypes: "multiply every contact rate by κ, leaving exits and
transitions unchanged"); relabelling is `Rxn.map f`. For every κ ∈ ℝ, all σ, σ', every
`f : σ → σ'` and every T_EB reaction: `(r.scaleContacts κ).map f = (r.map f).scaleContacts κ`.
"It acts reaction by reaction" is the reason; the per-reaction statement implies the model-level
one (`List.map`), so only the per-reaction statement is formalised. Split by constructor. -/
namespace Alignment.Shadows.SyntaxRxn.ScaleContactsMap

/-- Intended statement: scaling contact rates by κ commutes with relabelling, reaction by
reaction. -/
@[sa_reference "SyntaxRxn.scaleContactsMap"]
def T : Prop :=
  ∀ {σ σ' : Type} (κ : ℝ) (f : σ → σ') (r : Rxn σ),
    (r.scaleContacts κ).map f = (r.map f).scaleContacts κ

/-- S1: `c_κ` commutes with relabelling on contacts. -/
@[sa_shadow "SyntaxRxn.scaleContactsMap" 1]
def S1 : Prop :=
  ∀ {σ σ' : Type} (κ : ℝ) (f : σ → σ') (J X : σ) (τ : ℝ),
    ((Rxn.contact J X τ).scaleContacts κ).map f = ((Rxn.contact J X τ).map f).scaleContacts κ

/-- S2: `c_κ` commutes with relabelling on exits. -/
@[sa_shadow "SyntaxRxn.scaleContactsMap" 2]
def S2 : Prop :=
  ∀ {σ σ' : Type} (κ : ℝ) (f : σ → σ') (Y : σ) (ν : ℝ),
    ((Rxn.exit Y ν).scaleContacts κ).map f = ((Rxn.exit Y ν).map f).scaleContacts κ

/-- S3: `c_κ` commutes with relabelling on node transitions. -/
@[sa_shadow "SyntaxRxn.scaleContactsMap" 3]
def S3 : Prop :=
  ∀ {σ σ' : Type} (κ : ℝ) (f : σ → σ') (X : σ) (Y : Option σ) (a : ℝ),
    ((Rxn.trans X Y a).scaleContacts κ).map f = ((Rxn.trans X Y a).map f).scaleContacts κ

@[sa_ref_forward "SyntaxRxn.scaleContactsMap" 1]
theorem ref_fwd1 : T → S1 := by intro t σ σ' κ f J X τ; exact t κ f _

@[sa_ref_forward "SyntaxRxn.scaleContactsMap" 2]
theorem ref_fwd2 : T → S2 := by intro t σ σ' κ f Y ν; exact t κ f _

@[sa_ref_forward "SyntaxRxn.scaleContactsMap" 3]
theorem ref_fwd3 : T → S3 := by intro t σ σ' κ f X Y a; exact t κ f _

@[sa_complete "SyntaxRxn.scaleContactsMap"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := by
  intro σ σ' κ f r
  cases r with
  | contact J X τ => exact s1 κ f J X τ
  | exit Y ν => exact s2 κ f Y ν
  | trans X Y a => exact s3 κ f X Y a

end Alignment.Shadows.SyntaxRxn.ScaleContactsMap
