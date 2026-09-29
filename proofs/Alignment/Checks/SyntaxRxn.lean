import Alignment.Registry
import Alignment.Shadows.SyntaxRxn

/-!
# Checkers: group `SyntaxRxn` (trusted module `NetworkEpi.Syntax.Rxn`)

Checker author (SA-PASS role 3, non-blind). For each of the sixteen `implemented` claims of
`NetworkEpi/Syntax/Rxn.lean` this file holds the `sa_claim` registration (verbatim registry text,
registry `impl` list in registry order), the forward checkers `sa_impl% → Sᵢ` and the backward
checker `S₁ → … → Sₙ → sa_impl%`.

No bridges are declared. The blind shadows use the trusted notions themselves (`Rxn`, `NRxn`,
`Rxn.map`, `NRxn.map`, `Rxn.toNRxn`, `NRxn.toRxn?`, `NRxn.type`, `NRxn.EBAdmissible`,
`NRxn.EBAdmissibleList`, `Rxn.scaleContacts`, `TNet`) and one alignment helper, `InTEB`
(T_EB = {contact, exit, progress, remove} in primitive terms). The trusted `TNet.inTEB t = true`
is related to `InTEB t` by the structural helpers `inTEB_to` / `to_inTEB` below: case analysis
on `t`, `rfl`, `Or.inl/inr` and `Bool.noConfusion`, which the audit inlines. That is a
proof, so it needs no bridge. Other helpers: `adm_toNRxn` (every included T_EB reaction is
EB-admissible, by `rfl` per constructor) and `adm_of_map` (relabelling reflects admissibility,
by definitional unfolding per constructor). All are inlined and structural.

Where a shadow is strictly weaker than the implementation, the backward checker uses only some
shadows (hint `backward_unused_shadows`), for example the typing and model readings of
`notEbAdmissibleResus`. No check is recorded as failing.
-/

open NEP

namespace Alignment.Shadows.SyntaxRxn

/-- Structural helper: the trusted Boolean `TNet.inTEB` implies the primitive `InTEB`. -/
theorem inTEB_to : ∀ t : TNet, TNet.inTEB t = true → InTEB t
  | .contact, _ => Or.inl rfl
  | .exit, _ => Or.inr (Or.inl rfl)
  | .progress, _ => Or.inr (Or.inr (Or.inl rfl))
  | .remove, _ => Or.inr (Or.inr (Or.inr rfl))
  | .resus, e => Bool.noConfusion e
  | .nodeContact, e => Bool.noConfusion e

/-- Structural helper: the primitive `InTEB` implies the trusted Boolean `TNet.inTEB`. -/
theorem to_inTEB (t : TNet) (ht : InTEB t) : TNet.inTEB t = true := by
  rcases ht with e | e | e | e <;> (rw [e]; rfl)

/-- Structural helper: every included T_EB reaction is EB-admissible (definitional per case). -/
theorem adm_toNRxn {σ : Type} : ∀ r : Rxn σ, r.toNRxn.EBAdmissible
  | .contact _ _ _ => rfl
  | .exit _ _ => rfl
  | .trans _ _ _ => rfl

/-- Structural helper: relabelling reflects EB-admissibility (definitional per case). -/
theorem adm_of_map {σ σ' : Type} (f : σ → σ') :
    ∀ r : NRxn σ, (r.map f).EBAdmissible → r.EBAdmissible
  | .contact _ _ _, e => e
  | .exit _ _, e => e
  | .trans _ _ _, e => e
  | .resus _ _, e => e
  | .nodeContact _ _ _ _, e => e

end Alignment.Shadows.SyntaxRxn

/-! ## `SyntaxRxn.toRxnToNRxn` -/

namespace Alignment.Shadows.SyntaxRxn.ToRxnToNRxn

sa_claim "SyntaxRxn.toRxnToNRxn" group "SyntaxRxn" required
  text "`NRxn.toRxn?` is a left inverse of the inclusion `Rxn.toNRxn`."
  impl NEP.Rxn.toRxn?_toNRxn

@[sa_forward "SyntaxRxn.toRxnToNRxn" 1]
theorem fwd1 (h : sa_impl% "SyntaxRxn.toRxnToNRxn") : S1 := by
  intro σ J X τ
  exact h (Rxn.contact J X τ)

@[sa_forward "SyntaxRxn.toRxnToNRxn" 2]
theorem fwd2 (h : sa_impl% "SyntaxRxn.toRxnToNRxn") : S2 := by
  intro σ Y ν
  exact h (Rxn.exit Y ν)

@[sa_forward "SyntaxRxn.toRxnToNRxn" 3]
theorem fwd3 (h : sa_impl% "SyntaxRxn.toRxnToNRxn") : S3 := by
  intro σ X Y a
  exact h (Rxn.trans X Y a)

@[sa_backward "SyntaxRxn.toRxnToNRxn"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) : sa_impl% "SyntaxRxn.toRxnToNRxn" := by
  intro σ r
  cases r with
  | contact J X τ => exact s1 J X τ
  | exit Y ν => exact s2 Y ν
  | trans X Y a => exact s3 X Y a

end Alignment.Shadows.SyntaxRxn.ToRxnToNRxn

/-! ## `SyntaxRxn.toNRxnInjective` -/

namespace Alignment.Shadows.SyntaxRxn.ToNRxnInjective

sa_claim "SyntaxRxn.toNRxnInjective" group "SyntaxRxn" required
  text "The inclusion of T_EB syntax into T_net syntax is injective."
  impl NEP.Rxn.toNRxn_injective

@[sa_forward "SyntaxRxn.toNRxnInjective" 1]
theorem fwd1 (h : sa_impl% "SyntaxRxn.toNRxnInjective") : S1 := by
  intro σ J X τ r e
  exact h e

@[sa_forward "SyntaxRxn.toNRxnInjective" 2]
theorem fwd2 (h : sa_impl% "SyntaxRxn.toNRxnInjective") : S2 := by
  intro σ Y ν r e
  exact h e

@[sa_forward "SyntaxRxn.toNRxnInjective" 3]
theorem fwd3 (h : sa_impl% "SyntaxRxn.toNRxnInjective") : S3 := by
  intro σ X Y a r e
  exact h e

@[sa_backward "SyntaxRxn.toNRxnInjective"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) : sa_impl% "SyntaxRxn.toNRxnInjective" := by
  intro σ r₁ r₂ e
  cases r₁ with
  | contact J X τ => exact s1 J X τ r₂ e
  | exit Y ν => exact s2 Y ν r₂ e
  | trans X Y a => exact s3 X Y a r₂ e

end Alignment.Shadows.SyntaxRxn.ToNRxnInjective

/-! ## `SyntaxRxn.ebAdmissibleIff` -/

namespace Alignment.Shadows.SyntaxRxn.EbAdmissibleIff

sa_claim "SyntaxRxn.ebAdmissibleIff" group "SyntaxRxn" required
  text "EB-admissibility is exactly membership in the image of T_EB syntax."
  impl NEP.NRxn.ebAdmissible_iff

@[sa_forward "SyntaxRxn.ebAdmissibleIff" 1]
theorem fwd1 (h : sa_impl% "SyntaxRxn.ebAdmissibleIff") : S1 := by
  intro σ r hr
  obtain ⟨r', e⟩ := (h r).mp hr
  exact ⟨r', e.symm⟩

@[sa_forward "SyntaxRxn.ebAdmissibleIff" 2]
theorem fwd2 (h : sa_impl% "SyntaxRxn.ebAdmissibleIff") : S2 := by
  intro σ r hr
  obtain ⟨r', e⟩ := hr
  exact (h r).mpr ⟨r', e.symm⟩

@[sa_backward "SyntaxRxn.ebAdmissibleIff"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "SyntaxRxn.ebAdmissibleIff" := by
  intro σ r
  constructor
  · intro hr
    obtain ⟨r', e⟩ := s1 r hr
    exact ⟨r', e.symm⟩
  · intro hr
    obtain ⟨r', e⟩ := hr
    exact s2 r ⟨r', e.symm⟩

end Alignment.Shadows.SyntaxRxn.EbAdmissibleIff

/-! ## `SyntaxRxn.ebAdmissibleIffType`

The trusted right-hand side `TNet.inTEB r.type = true` is related to the shadow's `InTEB r.type`
by the structural helpers `inTEB_to` / `to_inTEB` (case analysis on the six types), so no
bridge is needed.

The registry text now says T_EB is the enumerated list {contact, exit, progress, remove} and
that the gloss "no arrow into Sus" is not the criterion; the blind shadows follow the list
(S1 only-if, S2 if), which is exactly the implementation's `TNet.inTEB`. The remaining
sentences (`nodeContact` is not in T_EB; `TNet` has six of eight types) are facts about the
data types `NRxn.type` / `TNet` and are not requirements on this implementation theorem; the
blind author left them unshadowed with that justification, and the node-contact refusal is the
separate claim `SyntaxRxn.notEbAdmissibleNodeContact`. -/

namespace Alignment.Shadows.SyntaxRxn.EbAdmissibleIffType

open Alignment.Shadows.SyntaxRxn (InTEB inTEB_to to_inTEB)

sa_claim "SyntaxRxn.ebAdmissibleIffType" group "SyntaxRxn" required
  text "EB-admissibility is membership of the reaction's type in T_EB: \"the sub-theory with no arrow into Sus\" (DESIGN §B.2). Design statement (DESIGN_NetworkEpiCore.md §B.2): \"**T_EB** = {contact, exit, progress, remove}: the sub-theory with **no arrow into Sus**. **T_net** = all eight types.\" [...] T_EB is the list {contact, exit, progress, remove}; the gloss \"no arrow into Sus\" does not characterise it in this syntax, since `nodeContact` (X + J → Y + J with X, Y ∉ Σ) has no arrow into Sus and is not in T_EB. `TNet` has six of the design's eight T_net types: `:sus_move` and `:sus_contact` need a second susceptible species or a susceptible product, which `NRxn` does not represent."
  impl NEP.NRxn.ebAdmissible_iff_type

@[sa_forward "SyntaxRxn.ebAdmissibleIffType" 1]
theorem fwd1 (h : sa_impl% "SyntaxRxn.ebAdmissibleIffType") : S1 := by
  intro σ r hr
  exact inTEB_to r.type ((h r).mp hr)

@[sa_forward "SyntaxRxn.ebAdmissibleIffType" 2]
theorem fwd2 (h : sa_impl% "SyntaxRxn.ebAdmissibleIffType") : S2 := by
  intro σ r ht
  exact (h r).mpr (to_inTEB r.type ht)

@[sa_backward "SyntaxRxn.ebAdmissibleIffType"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "SyntaxRxn.ebAdmissibleIffType" := by
  intro σ r
  exact ⟨fun hr => to_inTEB r.type (s1 r hr), fun ht => s2 r (inTEB_to r.type ht)⟩

end Alignment.Shadows.SyntaxRxn.EbAdmissibleIffType

/-! ## `SyntaxRxn.eqToNRxnOfEbAdmissible` -/

namespace Alignment.Shadows.SyntaxRxn.EqToNRxnOfEbAdmissible

sa_claim "SyntaxRxn.eqToNRxnOfEbAdmissible" group "SyntaxRxn" required
  text "An EB-admissible T_net reaction comes from T_EB syntax."
  impl NEP.NRxn.eq_toNRxn_of_ebAdmissible

@[sa_forward "SyntaxRxn.eqToNRxnOfEbAdmissible" 1]
theorem fwd1 (h : sa_impl% "SyntaxRxn.eqToNRxnOfEbAdmissible") : S1 := by
  intro σ r hr
  obtain ⟨r', e⟩ := h hr
  exact ⟨r', e.symm⟩

@[sa_backward "SyntaxRxn.eqToNRxnOfEbAdmissible"]
theorem bwd (s1 : S1) : sa_impl% "SyntaxRxn.eqToNRxnOfEbAdmissible" := by
  intro σ r hr
  obtain ⟨r', e⟩ := s1 r hr
  exact ⟨r', e.symm⟩

/-- Satisfiability witness: the hypothesis `r.EBAdmissible` of the implementation can hold
(the exit `s → ()` over `Unit` is admissible). -/
@[sa_witness "SyntaxRxn.eqToNRxnOfEbAdmissible" 1]
theorem witness : ∃ (σ : Type) (r : NRxn σ) (_ : r.EBAdmissible), True :=
  ⟨Unit, .exit () 1, rfl, trivial⟩

end Alignment.Shadows.SyntaxRxn.EqToNRxnOfEbAdmissible

/-! ## `SyntaxRxn.notEbAdmissibleResus`

The implementation is the constructor reading S1. The typing reading S2 follows because a
reaction of type `:resus` is a `resus X a` (every other case contradicts the type equation by
`TNet.noConfusion`). The model reading S3 follows because `EBAdmissibleList rs` unfolds to "every
reaction in `rs` is admissible". The backward checker uses S1 only. -/

namespace Alignment.Shadows.SyntaxRxn.NotEbAdmissibleResus

sa_claim "SyntaxRxn.notEbAdmissibleResus" group "SyntaxRxn" required
  text "Resusceptibility `X → s` (§B.2 type `:resus`, e.g. SIS `I → S`) is not EB-admissible (DESIGN executive summary: \"The EB lift is strictly partial: SIS/SIRS are refused\"). Design statement (DESIGN_NetworkEpiCore.md, executive summary item 6): \"**The EB lift is strictly partial**: SIS/SIRS are refused with the alternatives named\"; §B.2 table (the first ✗ is the EB column): \"NodeTransition X ∉ Σ, Y ∈ Σ | `:resus` | I → S (SIS), R → S (SIRS), I₁ → R₁ when R₁ can be infected | ✗\"."
  impl NEP.NRxn.not_ebAdmissible_resus

@[sa_forward "SyntaxRxn.notEbAdmissibleResus" 1]
theorem fwd1 (h : sa_impl% "SyntaxRxn.notEbAdmissibleResus") : S1 := by
  intro σ X a
  exact h X a

@[sa_forward "SyntaxRxn.notEbAdmissibleResus" 2]
theorem fwd2 (h : sa_impl% "SyntaxRxn.notEbAdmissibleResus") : S2 := by
  intro σ r ht
  cases r with
  | contact J X τ => exact TNet.noConfusion ht
  | exit Y ν => exact TNet.noConfusion ht
  | trans X Y a =>
    cases Y with
    | none => exact TNet.noConfusion ht
    | some Y => exact TNet.noConfusion ht
  | resus X a => exact h X a
  | nodeContact X J Y τ => exact TNet.noConfusion ht

@[sa_forward "SyntaxRxn.notEbAdmissibleResus" 3]
theorem fwd3 (h : sa_impl% "SyntaxRxn.notEbAdmissibleResus") : S3 := by
  intro σ rs X a hmem hl
  exact h X a (hl (NRxn.resus X a) hmem)

@[sa_backward "SyntaxRxn.notEbAdmissibleResus"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) : sa_impl% "SyntaxRxn.notEbAdmissibleResus" := by
  intro σ X a
  exact s1 X a

end Alignment.Shadows.SyntaxRxn.NotEbAdmissibleResus

/-! ## `SyntaxRxn.notEbAdmissibleNodeContact` -/

namespace Alignment.Shadows.SyntaxRxn.NotEbAdmissibleNodeContact

sa_claim "SyntaxRxn.notEbAdmissibleNodeContact" group "SyntaxRxn" required
  text "A node contact `X + J → Y + J` with a node-species recipient (§B.2 type `:node_contact`) is not EB-admissible."
  impl NEP.NRxn.not_ebAdmissible_nodeContact

@[sa_forward "SyntaxRxn.notEbAdmissibleNodeContact" 1]
theorem fwd1 (h : sa_impl% "SyntaxRxn.notEbAdmissibleNodeContact") : S1 := by
  intro σ X Y τ
  exact h X none Y τ

@[sa_forward "SyntaxRxn.notEbAdmissibleNodeContact" 2]
theorem fwd2 (h : sa_impl% "SyntaxRxn.notEbAdmissibleNodeContact") : S2 := by
  intro σ X J Y τ
  exact h X (some J) Y τ

@[sa_forward "SyntaxRxn.notEbAdmissibleNodeContact" 3]
theorem fwd3 (h : sa_impl% "SyntaxRxn.notEbAdmissibleNodeContact") : S3 := by
  intro σ r ht
  cases r with
  | contact J X τ => exact TNet.noConfusion ht
  | exit Y ν => exact TNet.noConfusion ht
  | trans X Y a =>
    cases Y with
    | none => exact TNet.noConfusion ht
    | some Y => exact TNet.noConfusion ht
  | resus X a => exact TNet.noConfusion ht
  | nodeContact X J Y τ => exact h X J Y τ

@[sa_backward "SyntaxRxn.notEbAdmissibleNodeContact"]
theorem bwd (s1 : S1) (s2 : S2) (_s3 : S3) : sa_impl% "SyntaxRxn.notEbAdmissibleNodeContact" := by
  intro σ X J Y τ
  cases J with
  | none => exact s1 X Y τ
  | some J => exact s2 X J Y τ

end Alignment.Shadows.SyntaxRxn.NotEbAdmissibleNodeContact

/-! ## `SyntaxRxn.existsNotEbAdmissible`

The implementation gives a non-admissible reaction over `Unit`. The shadows ask for one over every
inhabited `σ`. For `X : σ`, the relabelling of the implementation's witness along `fun _ => X`
is non-admissible, because relabelling reflects admissibility (`adm_of_map`). It is outside the
image of `Rxn.toNRxn` because included reactions are admissible (`adm_toNRxn`). The backward
checker instantiates S1 at `σ = Unit`, `X = ()`. -/

namespace Alignment.Shadows.SyntaxRxn.ExistsNotEbAdmissible

open Alignment.Shadows.SyntaxRxn (adm_toNRxn adm_of_map)

sa_claim "SyntaxRxn.existsNotEbAdmissible" group "SyntaxRxn" required
  text "T_EB ⊊ T_net: some T_net reaction is not EB-admissible (the resusceptibility `X → s`). Design statement (DESIGN_NetworkEpiCore.md §D.1): \"**Petri/T_EB ⊂ Petri/T_net ⊂ Petri**, and the back ends are defined on these: EB on Petri/T_EB\"; executive summary item 6: \"**The EB lift is strictly partial**\"."
  impl NEP.NRxn.exists_not_ebAdmissible

@[sa_forward "SyntaxRxn.existsNotEbAdmissible" 1]
theorem fwd1 (h : sa_impl% "SyntaxRxn.existsNotEbAdmissible") : S1 := by
  intro σ X
  obtain ⟨r, hr⟩ := h
  exact ⟨r.map (fun _ => X), fun ha => hr (adm_of_map (fun _ => X) r ha)⟩

@[sa_forward "SyntaxRxn.existsNotEbAdmissible" 2]
theorem fwd2 (h : sa_impl% "SyntaxRxn.existsNotEbAdmissible") : S2 := by
  intro σ X
  obtain ⟨r, hr⟩ := h
  refine ⟨r.map (fun _ => X), fun r' e => hr (adm_of_map (fun _ => X) r ?_)⟩
  rw [← e]
  exact adm_toNRxn r'

@[sa_backward "SyntaxRxn.existsNotEbAdmissible"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "SyntaxRxn.existsNotEbAdmissible" :=
  s1 ()

end Alignment.Shadows.SyntaxRxn.ExistsNotEbAdmissible

/-! ## `SyntaxRxn.rxnMapId` -/

namespace Alignment.Shadows.SyntaxRxn.RxnMapId

sa_claim "SyntaxRxn.rxnMapId" group "SyntaxRxn" required
  text "Relabelling along the identity is the identity."
  impl NEP.Rxn.map_id

@[sa_forward "SyntaxRxn.rxnMapId" 1]
theorem fwd1 (h : sa_impl% "SyntaxRxn.rxnMapId") : S1 := by
  intro σ J X τ
  exact h (Rxn.contact J X τ)

@[sa_forward "SyntaxRxn.rxnMapId" 2]
theorem fwd2 (h : sa_impl% "SyntaxRxn.rxnMapId") : S2 := by
  intro σ Y ν
  exact h (Rxn.exit Y ν)

@[sa_forward "SyntaxRxn.rxnMapId" 3]
theorem fwd3 (h : sa_impl% "SyntaxRxn.rxnMapId") : S3 := by
  intro σ X Y a
  exact h (Rxn.trans X Y a)

@[sa_backward "SyntaxRxn.rxnMapId"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) : sa_impl% "SyntaxRxn.rxnMapId" := by
  intro σ r
  cases r with
  | contact J X τ => exact s1 J X τ
  | exit Y ν => exact s2 Y ν
  | trans X Y a => exact s3 X Y a

end Alignment.Shadows.SyntaxRxn.RxnMapId

/-! ## `SyntaxRxn.rxnMapMap` -/

namespace Alignment.Shadows.SyntaxRxn.RxnMapMap

sa_claim "SyntaxRxn.rxnMapMap" group "SyntaxRxn" required
  text "Relabelling is functorial: relabelling along `f` then `g` is relabelling along `g ∘ f`."
  impl NEP.Rxn.map_map

@[sa_forward "SyntaxRxn.rxnMapMap" 1]
theorem fwd1 (h : sa_impl% "SyntaxRxn.rxnMapMap") : S1 := by
  intro σ σ' σ'' f g J X τ
  exact h f g (Rxn.contact J X τ)

@[sa_forward "SyntaxRxn.rxnMapMap" 2]
theorem fwd2 (h : sa_impl% "SyntaxRxn.rxnMapMap") : S2 := by
  intro σ σ' σ'' f g Y ν
  exact h f g (Rxn.exit Y ν)

@[sa_forward "SyntaxRxn.rxnMapMap" 3]
theorem fwd3 (h : sa_impl% "SyntaxRxn.rxnMapMap") : S3 := by
  intro σ σ' σ'' f g X Y a
  exact h f g (Rxn.trans X Y a)

@[sa_backward "SyntaxRxn.rxnMapMap"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) : sa_impl% "SyntaxRxn.rxnMapMap" := by
  intro σ σ' σ'' f g r
  cases r with
  | contact J X τ => exact s1 f g J X τ
  | exit Y ν => exact s2 f g Y ν
  | trans X Y a => exact s3 f g X Y a

end Alignment.Shadows.SyntaxRxn.RxnMapMap

/-! ## `SyntaxRxn.nRxnMapId` -/

namespace Alignment.Shadows.SyntaxRxn.NRxnMapId

sa_claim "SyntaxRxn.nRxnMapId" group "SyntaxRxn" required
  text "Relabelling a T_net reaction along the identity is the identity."
  impl NEP.NRxn.map_id

@[sa_forward "SyntaxRxn.nRxnMapId" 1]
theorem fwd1 (h : sa_impl% "SyntaxRxn.nRxnMapId") : S1 := by
  intro σ J X τ
  exact h (NRxn.contact J X τ)

@[sa_forward "SyntaxRxn.nRxnMapId" 2]
theorem fwd2 (h : sa_impl% "SyntaxRxn.nRxnMapId") : S2 := by
  intro σ Y ν
  exact h (NRxn.exit Y ν)

@[sa_forward "SyntaxRxn.nRxnMapId" 3]
theorem fwd3 (h : sa_impl% "SyntaxRxn.nRxnMapId") : S3 := by
  intro σ X Y a
  exact h (NRxn.trans X Y a)

@[sa_forward "SyntaxRxn.nRxnMapId" 4]
theorem fwd4 (h : sa_impl% "SyntaxRxn.nRxnMapId") : S4 := by
  intro σ X a
  exact h (NRxn.resus X a)

@[sa_forward "SyntaxRxn.nRxnMapId" 5]
theorem fwd5 (h : sa_impl% "SyntaxRxn.nRxnMapId") : S5 := by
  intro σ X J Y τ
  exact h (NRxn.nodeContact X J Y τ)

@[sa_backward "SyntaxRxn.nRxnMapId"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) : sa_impl% "SyntaxRxn.nRxnMapId" := by
  intro σ r
  cases r with
  | contact J X τ => exact s1 J X τ
  | exit Y ν => exact s2 Y ν
  | trans X Y a => exact s3 X Y a
  | resus X a => exact s4 X a
  | nodeContact X J Y τ => exact s5 X J Y τ

end Alignment.Shadows.SyntaxRxn.NRxnMapId

/-! ## `SyntaxRxn.nRxnMapMap`

The registry reads "functorial" as both laws, so `sa_impl%` is `NRxn.map_map ∧ NRxn.map_id`,
which matches the shadows S1–S5 (composition) and S6 (identity). -/

namespace Alignment.Shadows.SyntaxRxn.NRxnMapMap

sa_claim "SyntaxRxn.nRxnMapMap" group "SyntaxRxn" required
  text "Relabelling T_net reactions is functorial."
  impl NEP.NRxn.map_map NEP.NRxn.map_id

@[sa_forward "SyntaxRxn.nRxnMapMap" 1]
theorem fwd1 (h : sa_impl% "SyntaxRxn.nRxnMapMap") : S1 := by
  intro σ σ' σ'' f g J X τ
  exact h.1 f g (NRxn.contact J X τ)

@[sa_forward "SyntaxRxn.nRxnMapMap" 2]
theorem fwd2 (h : sa_impl% "SyntaxRxn.nRxnMapMap") : S2 := by
  intro σ σ' σ'' f g Y ν
  exact h.1 f g (NRxn.exit Y ν)

@[sa_forward "SyntaxRxn.nRxnMapMap" 3]
theorem fwd3 (h : sa_impl% "SyntaxRxn.nRxnMapMap") : S3 := by
  intro σ σ' σ'' f g X Y a
  exact h.1 f g (NRxn.trans X Y a)

@[sa_forward "SyntaxRxn.nRxnMapMap" 4]
theorem fwd4 (h : sa_impl% "SyntaxRxn.nRxnMapMap") : S4 := by
  intro σ σ' σ'' f g X a
  exact h.1 f g (NRxn.resus X a)

@[sa_forward "SyntaxRxn.nRxnMapMap" 5]
theorem fwd5 (h : sa_impl% "SyntaxRxn.nRxnMapMap") : S5 := by
  intro σ σ' σ'' f g X J Y τ
  exact h.1 f g (NRxn.nodeContact X J Y τ)

@[sa_forward "SyntaxRxn.nRxnMapMap" 6]
theorem fwd6 (h : sa_impl% "SyntaxRxn.nRxnMapMap") : S6 := by
  intro σ r
  exact h.2 r

@[sa_backward "SyntaxRxn.nRxnMapMap"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) :
    sa_impl% "SyntaxRxn.nRxnMapMap" := by
  refine ⟨?_, ?_⟩
  · intro σ σ' σ'' f g r
    cases r with
    | contact J X τ => exact s1 f g J X τ
    | exit Y ν => exact s2 f g Y ν
    | trans X Y a => exact s3 f g X Y a
    | resus X a => exact s4 f g X a
    | nodeContact X J Y τ => exact s5 f g X J Y τ
  · intro σ r
    exact s6 r

end Alignment.Shadows.SyntaxRxn.NRxnMapMap

/-! ## `SyntaxRxn.toNRxnMap` -/

namespace Alignment.Shadows.SyntaxRxn.ToNRxnMap

sa_claim "SyntaxRxn.toNRxnMap" group "SyntaxRxn" required
  text "Relabelling commutes with the inclusion T_EB ⊂ T_net."
  impl NEP.Rxn.toNRxn_map

@[sa_forward "SyntaxRxn.toNRxnMap" 1]
theorem fwd1 (h : sa_impl% "SyntaxRxn.toNRxnMap") : S1 := by
  intro σ σ' f J X τ
  exact h f (Rxn.contact J X τ)

@[sa_forward "SyntaxRxn.toNRxnMap" 2]
theorem fwd2 (h : sa_impl% "SyntaxRxn.toNRxnMap") : S2 := by
  intro σ σ' f Y ν
  exact h f (Rxn.exit Y ν)

@[sa_forward "SyntaxRxn.toNRxnMap" 3]
theorem fwd3 (h : sa_impl% "SyntaxRxn.toNRxnMap") : S3 := by
  intro σ σ' f X Y a
  exact h f (Rxn.trans X Y a)

@[sa_backward "SyntaxRxn.toNRxnMap"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) : sa_impl% "SyntaxRxn.toNRxnMap" := by
  intro σ σ' f r
  cases r with
  | contact J X τ => exact s1 f J X τ
  | exit Y ν => exact s2 f Y ν
  | trans X Y a => exact s3 f X Y a

end Alignment.Shadows.SyntaxRxn.ToNRxnMap

/-! ## `SyntaxRxn.typeMap`

S7 (T_EB reactions, through the inclusion) follows from the implementation, since
`(r.map f).toNRxn` and `r.toNRxn.map f` agree definitionally for each constructor of `r`. -/

namespace Alignment.Shadows.SyntaxRxn.TypeMap

sa_claim "SyntaxRxn.typeMap" group "SyntaxRxn" required
  text "Relabelling preserves the type of a reaction (morphisms of syntax are type-preserving)."
  impl NEP.NRxn.type_map

@[sa_forward "SyntaxRxn.typeMap" 1]
theorem fwd1 (h : sa_impl% "SyntaxRxn.typeMap") : S1 := by
  intro σ σ' f J X τ
  exact h f (NRxn.contact J X τ)

@[sa_forward "SyntaxRxn.typeMap" 2]
theorem fwd2 (h : sa_impl% "SyntaxRxn.typeMap") : S2 := by
  intro σ σ' f Y ν
  exact h f (NRxn.exit Y ν)

@[sa_forward "SyntaxRxn.typeMap" 3]
theorem fwd3 (h : sa_impl% "SyntaxRxn.typeMap") : S3 := by
  intro σ σ' f X Y a
  exact h f (NRxn.trans X (some Y) a)

@[sa_forward "SyntaxRxn.typeMap" 4]
theorem fwd4 (h : sa_impl% "SyntaxRxn.typeMap") : S4 := by
  intro σ σ' f X a
  exact h f (NRxn.trans X none a)

@[sa_forward "SyntaxRxn.typeMap" 5]
theorem fwd5 (h : sa_impl% "SyntaxRxn.typeMap") : S5 := by
  intro σ σ' f X a
  exact h f (NRxn.resus X a)

@[sa_forward "SyntaxRxn.typeMap" 6]
theorem fwd6 (h : sa_impl% "SyntaxRxn.typeMap") : S6 := by
  intro σ σ' f X J Y τ
  exact h f (NRxn.nodeContact X J Y τ)

@[sa_forward "SyntaxRxn.typeMap" 7]
theorem fwd7 (h : sa_impl% "SyntaxRxn.typeMap") : S7 := by
  intro σ σ' f r
  cases r with
  | contact J X τ => exact h f (NRxn.contact J X τ)
  | exit Y ν => exact h f (NRxn.exit Y ν)
  | trans X Y a => exact h f (NRxn.trans X Y a)

@[sa_backward "SyntaxRxn.typeMap"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) (_s7 : S7) :
    sa_impl% "SyntaxRxn.typeMap" := by
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

/-! ## `SyntaxRxn.ebAdmissibleMap` -/

namespace Alignment.Shadows.SyntaxRxn.EbAdmissibleMap

sa_claim "SyntaxRxn.ebAdmissibleMap" group "SyntaxRxn" required
  text "Relabelling preserves and reflects EB-admissibility."
  impl NEP.NRxn.ebAdmissible_map

@[sa_forward "SyntaxRxn.ebAdmissibleMap" 1]
theorem fwd1 (h : sa_impl% "SyntaxRxn.ebAdmissibleMap") : S1 := by
  intro σ σ' f r
  exact (h f r).mpr

@[sa_forward "SyntaxRxn.ebAdmissibleMap" 2]
theorem fwd2 (h : sa_impl% "SyntaxRxn.ebAdmissibleMap") : S2 := by
  intro σ σ' f r
  exact (h f r).mp

@[sa_backward "SyntaxRxn.ebAdmissibleMap"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "SyntaxRxn.ebAdmissibleMap" := by
  intro σ σ' f r
  exact ⟨s2 f r, s1 f r⟩

end Alignment.Shadows.SyntaxRxn.EbAdmissibleMap

/-! ## `SyntaxRxn.scaleContactsMap`

The implementation states the commutation as `(r.map f).scaleContacts κ = (r.scaleContacts κ).map f`
and the shadows state it the other way round, so the checkers use `Eq.symm`. -/

namespace Alignment.Shadows.SyntaxRxn.ScaleContactsMap

sa_claim "SyntaxRxn.scaleContactsMap" group "SyntaxRxn" required
  text "`c_κ` commutes with relabelling (it acts reaction by reaction)."
  impl NEP.Rxn.scaleContacts_map

@[sa_forward "SyntaxRxn.scaleContactsMap" 1]
theorem fwd1 (h : sa_impl% "SyntaxRxn.scaleContactsMap") : S1 := by
  intro σ σ' κ f J X τ
  exact (h κ f (Rxn.contact J X τ)).symm

@[sa_forward "SyntaxRxn.scaleContactsMap" 2]
theorem fwd2 (h : sa_impl% "SyntaxRxn.scaleContactsMap") : S2 := by
  intro σ σ' κ f Y ν
  exact (h κ f (Rxn.exit Y ν)).symm

@[sa_forward "SyntaxRxn.scaleContactsMap" 3]
theorem fwd3 (h : sa_impl% "SyntaxRxn.scaleContactsMap") : S3 := by
  intro σ σ' κ f X Y a
  exact (h κ f (Rxn.trans X Y a)).symm

@[sa_backward "SyntaxRxn.scaleContactsMap"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) : sa_impl% "SyntaxRxn.scaleContactsMap" := by
  intro σ σ' κ f r
  cases r with
  | contact J X τ => exact (s1 κ f J X τ).symm
  | exit Y ν => exact (s2 κ f Y ν).symm
  | trans X Y a => exact (s3 κ f X Y a).symm

end Alignment.Shadows.SyntaxRxn.ScaleContactsMap
