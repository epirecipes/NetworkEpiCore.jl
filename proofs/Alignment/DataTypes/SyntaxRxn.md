# DataTypes — group `SyntaxRxn`

Blind-safe vocabulary for shadow authors of group `SyntaxRxn` (SA-PASS). It lists the Lean imports, the
data types (structures and inductives with their fields) and the operations under test as **opaque
signatures with their docstrings only**. It contains no theorem statements, no proofs, no definition
bodies and no instance bodies. Where a docstring spells out a formula, that formula is the author's
*intent text*, not a guarantee about the body. Claim texts: `Alignment/claims_blind.yaml` (group
`SyntaxRxn`).

Trusted module under test: `NetworkEpi.Syntax.Rxn` (file `NetworkEpi/Syntax/Rxn.lean`). Everything is in namespace `NEP`
(write `open NEP`). Numbers are real (`ℝ`) unless stated.

## (a) Imports

```lean
import NetworkEpi.Syntax.Rxn   -- imports Mathlib.Data.Real.Basic, Mathlib.Data.Option.Basic
open NEP
```

## (b)–(c) Data types and operations under test

### From `NetworkEpi.Syntax.Rxn` (typed reaction syntax, one implicit susceptible species `s`)

```lean
/-- T_EB reactions over node species `σ` (the susceptible species `s` is implicit):
* `contact J X τ` is `s + J → X + J` at per-contact rate `τ` (DESIGN §0: "τ is always a
  per-contact (per-edge) rate");
* `exit Y ν` is `s → Y` at rate `ν` (for example vaccination);
* `trans X (some Y) a` is `X → Y` and `trans X none a` is `X → ∅`, at rate `a`. -/
inductive Rxn (σ : Type) where
  | contact (J X : σ) (τ : ℝ)       -- s + J → X + J at per-contact rate τ
  | exit (Y : σ) (ν : ℝ)            -- s → Y at rate ν
  | trans (X : σ) (Y : Option σ) (a : ℝ)   -- X → Y (or X → ∅ when Y = none) at rate a

/-- T_net reactions over node species `σ` (single susceptible species `s`): `NRxn σ` has the
T_EB constructors of `Rxn σ` and adds
* `resus X a`: `X → s` at rate `a` (§B.2 type `:resus`, e.g. SIS `I → S`, SIRS `R → S`);
* `nodeContact X J Y τ`: `X + J → Y + J` at rate `τ`, with recipient `X` a node species and
  catalyst `J` (`J = none` means the catalyst is `s`) (§B.2 type `:node_contact`). -/
inductive NRxn (σ : Type) where
  | contact (J X : σ) (τ : ℝ)
  | exit (Y : σ) (ν : ℝ)
  | trans (X : σ) (Y : Option σ) (a : ℝ)
  | resus (X : σ) (a : ℝ)                          -- X → s at rate a
  | nodeContact (X : σ) (J : Option σ) (Y : σ) (τ : ℝ)   -- X + J → Y + J; J = none is s

/-- The transition types of the theory T_net that `NRxn` represents (DESIGN §B.2). -/
inductive TNet where
  | contact | exit | progress | remove | resus | nodeContact
  deriving DecidableEq, Repr
```

| signature (opaque) | docstring |
|---|---|
| `TNet.inTEB : TNet → Bool` | Membership of a T_net type in the sub-theory T_EB = {contact, exit, progress, remove}. |
| `NRxn.type {σ : Type} : NRxn σ → TNet` | The typing of a T_net reaction (DESIGN §B.2). (Module header table: `contact` ↦ `:contact`, `exit` ↦ `:exit`, `trans X (some Y)` ↦ `:progress`, `trans X none` ↦ `:remove`, `resus` ↦ `:resus`, `nodeContact` ↦ `:node_contact`.) |
| `Rxn.toNRxn {σ : Type} : Rxn σ → NRxn σ` | The inclusion of T_EB syntax into T_net syntax. |
| `NRxn.toRxn? {σ : Type} : NRxn σ → Option (Rxn σ)` | The partial inverse of `Rxn.toNRxn`: `some r` on T_EB reactions, `none` otherwise. |
| `NRxn.EBAdmissible {σ : Type} (r : NRxn σ) : Prop` | A T_net reaction is *EB-admissible* if it is one of the T_EB types contact, exit, progress or remove (DESIGN §B.2: EB is defined on Petri/T_EB). |
| `instance NRxn.decEBAdmissible {σ : Type} : DecidablePred (NRxn.EBAdmissible (σ := σ))` | EB-admissibility is decidable. |
| `NRxn.EBAdmissibleList {σ : Type} (rs : List (NRxn σ)) : Prop` | A reaction list is EB-admissible if every reaction is. |
| `instance NRxn.decEBAdmissibleList {σ : Type} (rs : List (NRxn σ)) : Decidable (NRxn.EBAdmissibleList rs)` | EB-admissibility of a reaction list is decidable. |
| `Rxn.map {σ σ' : Type} (f : σ → σ') : Rxn σ → Rxn σ'` | Relabel the node species of a T_EB reaction along `f` (DESIGN §D.1: "Morphisms of syntax are type-preserving species maps that carry reactions to reactions"). Gluing species along a cospan is relabelling along the cospan legs. |
| `NRxn.map {σ σ' : Type} (f : σ → σ') : NRxn σ → NRxn σ'` | Relabel the node species of a T_net reaction along `f`. |
| `Rxn.scaleContacts {σ : Type} (κ : ℝ) : Rxn σ → Rxn σ` | The rate convention `c_κ`: multiply every contact rate by `κ`, leaving exits and transitions unchanged (DESIGN §D.5 M1 uses `c_κ` for the well-mixed unit, M3 uses `c_μ`). |

## (d) What is not defined (usage notes)

* One susceptible species `s` is implicit in `Rxn σ` and `NRxn σ`; node species form the type `σ`.
  The design's T_net has eight transition types, `TNet` has six: `:sus_move` and `:sus_contact` are
  not representable with a single susceptible species.
* There is no Lean notion of a Petri net, of the theories T_EB/T_net as categories, of an "arrow into
  Sus" (arcs of a Petri net), or of error messages / named alternatives. "T_EB ⊂ T_net" can be
  expressed with `Rxn.toNRxn` (the inclusion) and `NRxn.EBAdmissible` / the image of `Rxn.toNRxn`.
* The EB semantics (`NetworkEpi.Semantics.EB.ebField`) is defined on `Rxn σ` only.

## (e) Mathlib notions a faithful formalisation may need

* `Option`, `Option.map`, `Option.isSome`, `Option.elim`; `Function.Injective`, `Function.Surjective`,
  `Set.range`; `List`, `List.map`, `∀ r ∈ rs, …`; `Decidable`, `DecidablePred`, `decide`.
