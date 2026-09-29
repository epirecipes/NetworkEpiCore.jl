import Alignment.Registry
import NetworkEpi.Morphisms.Stoich

/-!
# Blind shadow sets: group `MorphismsStoich` (module `NetworkEpi.Morphisms.Stoich`)

Written blind. The author read only `SA-PASS_SKILL.md`, `Alignment/README.md`,
`Alignment/Example/ExampleShadows.lean`, `Alignment/DataTypes/MorphismsStoich.md`, the entries
of the five claim ids below in `Alignment/claims_blind.yaml`, and `DESIGN_NetworkEpiCore.md`
(§D.1–§D.7, §J, §K, §L). `#check` was used only on the DataTypes vocabulary. No theorem statement,
definition body, checker file or report was opened.

Vocabulary (DataTypes/MorphismsStoich.md): `SRxn ι` (multiset reaction `inp → out` at rate `k`),
its field `SRxn.field`, the list field `sLift`, the multiset mass-action model `sSys` (state
`ι → ℝ`, field `sLift rs`), the translation `NRxn.toSRxn : NRxn σ → SRxn (Option σ)` (`none` is the
susceptible species `s`), the coordinate maps `maToS` and `maToSL`, and from `Semantics.MA` the
per-reaction field `maField` and the model `maSys`.

Conventions of this file.
* Species types are `Type` (every operation of the module is stated over `ι σ : Type`; the texts
  say nothing about universes).
* A "field" `F` and a field `G` on another coordinate space "are the same" through a coordinate
  identification `c` when `c (F u) = G (c u)` for every state `u`. For the identification of
  `MA σ = (S, x)` with functions on `Option σ` the texts fix the convention "`none` is the
  susceptible species"; it is written out in primitive terms as `optCoords` below (so a checker
  that uses the module's `maToS` needs a reviewed bridge `maToS u = optCoords u`).
-/

open NEP

namespace Alignment.Shadows.MorphismsStoich

/-- The mass-action coordinates `(S, x)` as a function on `Option σ`, with `none` the susceptible
species: `none ↦ S` and `some X ↦ x_X`. This is the primitive form of the texts' "`none` is the
susceptible species". -/
def optCoords {σ : Type} (u : MA σ) : Option σ → ℝ
  | none => u.1
  | some X => u.2 X

end Alignment.Shadows.MorphismsStoich

/-! ## `MorphismsStoich.sLiftAppend`

Blind text: "The multiset mass-action field is additive in the reaction list."

The multiset mass-action field of a list `rs` is `sLift rs`. "Additive in the reaction list": the
field of a concatenation is the sum of the fields.

AMBIGUITY: "additive" could also be read as "a monoid morphism (lists, `++`, `[]`) → (fields,
`+`, `0`)", which would add `sLift [] = 0`. That law follows from the append law in an additive
group (`f [] = f ([] ++ []) = f [] + f []`), so both readings give the same `T`, and no separate
shadow is written for it. The equation is stated at every state `x` (as an equation in `ι → ℝ`);
by function extensionality this is the same as the equation of functions. -/

namespace Alignment.Shadows.MorphismsStoich.SLiftAppend

/-- Intended statement: for every species type `ι` (with decidable equality), all lists `rs₁`,
`rs₂` of multiset reactions and every state `x`, the multiset mass-action field of `rs₁ ++ rs₂`
at `x` is the field of `rs₁` at `x` plus the field of `rs₂` at `x`. -/
@[sa_reference "MorphismsStoich.sLiftAppend"]
def T : Prop :=
  ∀ {ι : Type} [DecidableEq ι] (rs₁ rs₂ : List (SRxn ι)) (x : ι → ℝ),
    sLift (rs₁ ++ rs₂) x = sLift rs₁ x + sLift rs₂ x

/-- S1: the field of a concatenation is the sum of the fields (a single atomic requirement). -/
@[sa_shadow "MorphismsStoich.sLiftAppend" 1]
def S1 : Prop :=
  ∀ {ι : Type} [DecidableEq ι] (rs₁ rs₂ : List (SRxn ι)) (x : ι → ℝ),
    sLift (rs₁ ++ rs₂) x = sLift rs₁ x + sLift rs₂ x

@[sa_ref_forward "MorphismsStoich.sLiftAppend" 1]
theorem ref_fwd1 : T → S1 := by
  intro t ι _ rs₁ rs₂ x
  exact t rs₁ rs₂ x

@[sa_complete "MorphismsStoich.sLiftAppend"]
theorem complete (s1 : S1) : T := by
  intro ι _ rs₁ rs₂ x
  exact s1 rs₁ rs₂ x

end Alignment.Shadows.MorphismsStoich.SLiftAppend

/-! ## `MorphismsStoich.sLiftFlatMap`

Blind text: "The multiset mass-action field of `rs.flatMap g` is the sum over `r ∈ rs` of the
fields of `g r`."

Here `rs : List α` for an arbitrary type `α` and `g : α → List (SRxn ι)`; "the fields of `g r`"
is the multiset mass-action field `sLift (g r)` of the list `g r`.

AMBIGUITY: "the sum over `r ∈ rs`" is read as the list sum over the entries of `rs`, with
multiplicity (`(rs.map …).sum`), since `rs.flatMap g` repeats `g r` once per occurrence of `r`. A
sum over the *set* of distinct elements of `rs` would make the text false for `rs = [r, r]`, so
it is not the intended reading. As for `sLiftAppend`, the equation is stated at every state `x`. -/

namespace Alignment.Shadows.MorphismsStoich.SLiftFlatMap

/-- Intended statement: for all types `α`, `ι` (with decidable equality on `ι`), every list
`rs : List α`, every `g : α → List (SRxn ι)` and every state `x`, the multiset mass-action field of
`rs.flatMap g` at `x` is the sum, over the entries `r` of `rs`, of the field of `g r` at `x`. -/
@[sa_reference "MorphismsStoich.sLiftFlatMap"]
def T : Prop :=
  ∀ {α ι : Type} [DecidableEq ι] (rs : List α) (g : α → List (SRxn ι)) (x : ι → ℝ),
    sLift (rs.flatMap g) x = (rs.map (fun r => sLift (g r) x)).sum

/-- S1: the field of `rs.flatMap g` is the list sum of the fields of the `g r` (a single atomic
requirement). -/
@[sa_shadow "MorphismsStoich.sLiftFlatMap" 1]
def S1 : Prop :=
  ∀ {α ι : Type} [DecidableEq ι] (rs : List α) (g : α → List (SRxn ι)) (x : ι → ℝ),
    sLift (rs.flatMap g) x = (rs.map (fun r => sLift (g r) x)).sum

@[sa_ref_forward "MorphismsStoich.sLiftFlatMap" 1]
theorem ref_fwd1 : T → S1 := by
  intro t α ι _ rs g x
  exact t rs g x

@[sa_complete "MorphismsStoich.sLiftFlatMap"]
theorem complete (s1 : S1) : T := by
  intro α ι _ rs g x
  exact s1 rs g x

end Alignment.Shadows.MorphismsStoich.SLiftFlatMap

/-! ## `MorphismsStoich.maToSLApply`

Blind text: "`maToSL` is `maToS`."

`maToSL : MA σ →L[ℝ] Option σ → ℝ` is a continuous linear map and `maToS : MA σ → Option σ → ℝ` a
function; "is" means that the underlying function of `maToSL` is `maToS`, i.e. they agree at every
state `u` (the same as the equation of functions by function extensionality). This is a text about
two named operations of the module, so both appear as they are; the convention of `maToS` itself
is not part of this text. -/

namespace Alignment.Shadows.MorphismsStoich.MaToSLApply

/-- Intended statement: for every species type `σ` and every state `u : MA σ`, `maToSL u = maToS u`. -/
@[sa_reference "MorphismsStoich.maToSLApply"]
def T : Prop := ∀ {σ : Type} (u : MA σ), maToSL u = maToS u

/-- S1: `maToSL` applied to `u` is `maToS u` (a single atomic requirement). -/
@[sa_shadow "MorphismsStoich.maToSLApply" 1]
def S1 : Prop := ∀ {σ : Type} (u : MA σ), maToSL u = maToS u

@[sa_ref_forward "MorphismsStoich.maToSLApply" 1]
theorem ref_fwd1 : T → S1 := by
  intro t σ u
  exact t u

@[sa_complete "MorphismsStoich.maToSLApply"]
theorem complete (s1 : S1) : T := by
  intro σ u
  exact s1 u

end Alignment.Shadows.MorphismsStoich.MaToSLApply

/-! ## `MorphismsStoich.maFieldToSRxn`

Blind text: "Per reaction, the `NRxn` mass-action field is the multiset mass-action field."

For a T_net reaction `r : NRxn σ` the `NRxn` mass-action field is `maField r : MA σ → MA σ`, and
the multiset mass-action field is the field `(NRxn.toSRxn r).field` of `r` read as a multiset
reaction over `Option σ` (`none` = the susceptible species, DataTypes docstring of `NRxn.toSRxn`).
The two live on different coordinate spaces, so "is" means: they agree through the identification
`optCoords` of `(S, x)` with a function on `Option σ` (`none ↦ S`), i.e.
`optCoords (maField r u) = (NRxn.toSRxn r).field (optCoords u)` for every state `u`.

"Per reaction" is a universal statement over `r`. It is split along the six reaction forms that the
docstrings of `maField` and `NRxn.toSRxn` list (contact, exit, progression `X → Y`, removal `X → ∅`,
resusceptibility, node contact), so that a wrong treatment of one form fails one shadow. -/

namespace Alignment.Shadows.MorphismsStoich.MaFieldToSRxn

/-- Intended statement: for every species type `σ` with decidable equality, every T_net reaction
`r` and every state `u = (S, x)`, the mass-action field of `r` at `u`, read on `Option σ`
(`none ↦ S`), is the multiset mass-action field of `NRxn.toSRxn r` at the same point. -/
@[sa_reference "MorphismsStoich.maFieldToSRxn"]
def T : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (r : NRxn σ) (u : MA σ),
    optCoords (maField r u) = (NRxn.toSRxn r).field (optCoords u)

/-- S1: contacts `s + J → X + J` (`{s, J} → {X, J}`). -/
@[sa_shadow "MorphismsStoich.maFieldToSRxn" 1]
def S1 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (J X : σ) (τ : ℝ) (u : MA σ),
    optCoords (maField (NRxn.contact J X τ) u) =
      (NRxn.toSRxn (NRxn.contact J X τ)).field (optCoords u)

/-- S2: exits `s → Y` (`{s} → {Y}`). -/
@[sa_shadow "MorphismsStoich.maFieldToSRxn" 2]
def S2 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (Y : σ) (ν : ℝ) (u : MA σ),
    optCoords (maField (NRxn.exit Y ν) u) =
      (NRxn.toSRxn (NRxn.exit Y ν)).field (optCoords u)

/-- S3: progressions `X → Y` (`{X} → {Y}`). -/
@[sa_shadow "MorphismsStoich.maFieldToSRxn" 3]
def S3 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (X Y : σ) (a : ℝ) (u : MA σ),
    optCoords (maField (NRxn.trans X (some Y) a) u) =
      (NRxn.toSRxn (NRxn.trans X (some Y) a)).field (optCoords u)

/-- S4: removals `X → ∅` (`{X} → 0`). -/
@[sa_shadow "MorphismsStoich.maFieldToSRxn" 4]
def S4 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (X : σ) (a : ℝ) (u : MA σ),
    optCoords (maField (NRxn.trans X none a) u) =
      (NRxn.toSRxn (NRxn.trans X none a)).field (optCoords u)

/-- S5: resusceptibility `X → s` (`{X} → {s}`). -/
@[sa_shadow "MorphismsStoich.maFieldToSRxn" 5]
def S5 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (X : σ) (a : ℝ) (u : MA σ),
    optCoords (maField (NRxn.resus X a) u) =
      (NRxn.toSRxn (NRxn.resus X a)).field (optCoords u)

/-- S6: node contacts `X + J → Y + J` (`{X, J} → {Y, J}`, `J = none` the susceptible catalyst). -/
@[sa_shadow "MorphismsStoich.maFieldToSRxn" 6]
def S6 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (X : σ) (J : Option σ) (Y : σ) (τ : ℝ) (u : MA σ),
    optCoords (maField (NRxn.nodeContact X J Y τ) u) =
      (NRxn.toSRxn (NRxn.nodeContact X J Y τ)).field (optCoords u)

@[sa_ref_forward "MorphismsStoich.maFieldToSRxn" 1]
theorem ref_fwd1 : T → S1 := by
  intro t σ _ J X τ u
  exact t (NRxn.contact J X τ) u

@[sa_ref_forward "MorphismsStoich.maFieldToSRxn" 2]
theorem ref_fwd2 : T → S2 := by
  intro t σ _ Y ν u
  exact t (NRxn.exit Y ν) u

@[sa_ref_forward "MorphismsStoich.maFieldToSRxn" 3]
theorem ref_fwd3 : T → S3 := by
  intro t σ _ X Y a u
  exact t (NRxn.trans X (some Y) a) u

@[sa_ref_forward "MorphismsStoich.maFieldToSRxn" 4]
theorem ref_fwd4 : T → S4 := by
  intro t σ _ X a u
  exact t (NRxn.trans X none a) u

@[sa_ref_forward "MorphismsStoich.maFieldToSRxn" 5]
theorem ref_fwd5 : T → S5 := by
  intro t σ _ X a u
  exact t (NRxn.resus X a) u

@[sa_ref_forward "MorphismsStoich.maFieldToSRxn" 6]
theorem ref_fwd6 : T → S6 := by
  intro t σ _ X J Y τ u
  exact t (NRxn.nodeContact X J Y τ) u

@[sa_complete "MorphismsStoich.maFieldToSRxn"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) : T := by
  intro σ _ r u
  cases r with
  | contact J X τ => exact s1 J X τ u
  | exit Y ν => exact s2 Y ν u
  | trans X Y a =>
    cases Y with
    | some Y => exact s3 X Y a u
    | none => exact s4 X a u
  | resus X a => exact s5 X a u
  | nodeContact X J Y τ => exact s6 X J Y τ u

end Alignment.Shadows.MorphismsStoich.MaFieldToSRxn

/-! ## `MorphismsStoich.maEqStoich`

Blind text: "**The multiset mass-action semantics agrees with `maField`.** Design statement
(DESIGN_NetworkEpiCore.md §D.4, row MA): "**MA** | Open(Petri) | x_X | total"; §D.7, "Honest
feasibility": "The hard parts are [...] the multiset stoichiometry for D_μ". [...] So `sSys` extends
the library's mass-action semantics to reactions with several products. [...] every T_net reaction
`NRxn σ` is a multiset reaction over `Option σ` (`none` is the susceptible species) with the same
mass-action field."

The text makes two claims.
1. *Per reaction* ("agrees with `maField`"; "every T_net reaction `NRxn σ` is a multiset reaction
   over `Option σ` (`none` is the susceptible species) with the same mass-action field"): for every
   `r : NRxn σ`, the multiset reaction `NRxn.toSRxn r` has the mass-action field of `r`, through the
   identification `optCoords` (`none ↦ S`). Split along the six reaction forms, as for
   `maFieldToSRxn` (shadows S1–S6).
2. *Semantics* ("So `sSys` extends the library's mass-action semantics to reactions with several
   products"): on T_net syntax, translated reaction by reaction by `NRxn.toSRxn`, the multiset model
   `sSys` is the library's mass-action model `maSys` (§D.7 notation "The mass-action model MA(P) of a
   T_net list P is `maSys P`"): for every finite `σ` and every list `rs`, the vector field of
   `sSys (rs.map NRxn.toSRxn)` at `optCoords u` is `optCoords` of the vector field of `maSys rs`
   at `u` (shadow S7).

AMBIGUITY: "extends the library's mass-action semantics". The semantics of a list is its `DynSys`
model, and "extends" is read as "restricted to (the translation of) T_net syntax it *is* the old
model in the identified coordinates", i.e. the two vector fields correspond under `optCoords`.
Since `optCoords` is a linear bijection, this is the same as saying that it is a conjugacy in
**Dyn** (for a linear `π`, `Dπ(u)·F(u) = π(F u)`); the calculus side (differentiability of a linear
map, `Dπ = π`) is a fact about linear maps and not part of the text, so the shadow is stated at the
level of vector fields. "To reactions with several products" says that `sSys` is also defined for
multiset reactions outside the image of `NRxn.toSRxn`; that is a typing fact
(`sSys : List (SRxn ι) → DynSys`), as are the quoted design cells "total" (every multiset list has a
model) and "x_X" (the state of `sSys` is `ι → ℝ`, which S7 needs in order to typecheck). No shadow is
written for those.

AMBIGUITY: "is a multiset reaction … with the same mass-action field" could be read existentially
(some multiset reaction over `Option σ` has the same field). The reading used here names the
canonical one, `NRxn.toSRxn r` (the DataTypes docstring: "`s + J → X + J` is `{s, J} → {X, J}`",
…). It implies the existential reading, so `T` is the stronger of the two. -/

namespace Alignment.Shadows.MorphismsStoich.MaEqStoich

/-- Intended statement: (1) for every species type `σ` with decidable equality, every T_net reaction
`r` and every state `u`, `optCoords (maField r u) = (NRxn.toSRxn r).field (optCoords u)`; and (2) for
every finite species type `σ` with decidable equality, every T_net list `rs` and every state `u`, the
vector field of `sSys (rs.map NRxn.toSRxn)` at `optCoords u` is `optCoords` of the vector field of
`maSys rs` at `u`. -/
@[sa_reference "MorphismsStoich.maEqStoich"]
def T : Prop :=
  (∀ {σ : Type} [DecidableEq σ] (r : NRxn σ) (u : MA σ),
      optCoords (maField r u) = (NRxn.toSRxn r).field (optCoords u)) ∧
    (∀ {σ : Type} [Fintype σ] [DecidableEq σ] (rs : List (NRxn σ)) (u : MA σ),
      (sSys (rs.map NRxn.toSRxn)).F (optCoords u) = optCoords ((maSys rs).F u))

/-- S1: per reaction, contacts `s + J → X + J` (`{s, J} → {X, J}`). -/
@[sa_shadow "MorphismsStoich.maEqStoich" 1]
def S1 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (J X : σ) (τ : ℝ) (u : MA σ),
    optCoords (maField (NRxn.contact J X τ) u) =
      (NRxn.toSRxn (NRxn.contact J X τ)).field (optCoords u)

/-- S2: per reaction, exits `s → Y` (`{s} → {Y}`). -/
@[sa_shadow "MorphismsStoich.maEqStoich" 2]
def S2 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (Y : σ) (ν : ℝ) (u : MA σ),
    optCoords (maField (NRxn.exit Y ν) u) =
      (NRxn.toSRxn (NRxn.exit Y ν)).field (optCoords u)

/-- S3: per reaction, progressions `X → Y` (`{X} → {Y}`). -/
@[sa_shadow "MorphismsStoich.maEqStoich" 3]
def S3 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (X Y : σ) (a : ℝ) (u : MA σ),
    optCoords (maField (NRxn.trans X (some Y) a) u) =
      (NRxn.toSRxn (NRxn.trans X (some Y) a)).field (optCoords u)

/-- S4: per reaction, removals `X → ∅` (`{X} → 0`). -/
@[sa_shadow "MorphismsStoich.maEqStoich" 4]
def S4 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (X : σ) (a : ℝ) (u : MA σ),
    optCoords (maField (NRxn.trans X none a) u) =
      (NRxn.toSRxn (NRxn.trans X none a)).field (optCoords u)

/-- S5: per reaction, resusceptibility `X → s` (`{X} → {s}`). -/
@[sa_shadow "MorphismsStoich.maEqStoich" 5]
def S5 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (X : σ) (a : ℝ) (u : MA σ),
    optCoords (maField (NRxn.resus X a) u) =
      (NRxn.toSRxn (NRxn.resus X a)).field (optCoords u)

/-- S6: per reaction, node contacts `X + J → Y + J` (`{X, J} → {Y, J}`, `J = none` the
susceptible catalyst). -/
@[sa_shadow "MorphismsStoich.maEqStoich" 6]
def S6 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (X : σ) (J : Option σ) (Y : σ) (τ : ℝ) (u : MA σ),
    optCoords (maField (NRxn.nodeContact X J Y τ) u) =
      (NRxn.toSRxn (NRxn.nodeContact X J Y τ)).field (optCoords u)

/-- S7: `sSys` extends the library's mass-action semantics: on every T_net list `rs` (finite `σ`),
the vector field of the multiset model of `rs.map NRxn.toSRxn` corresponds, under `optCoords`, to the
vector field of `maSys rs`. -/
@[sa_shadow "MorphismsStoich.maEqStoich" 7]
def S7 : Prop :=
  ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (rs : List (NRxn σ)) (u : MA σ),
    (sSys (rs.map NRxn.toSRxn)).F (optCoords u) = optCoords ((maSys rs).F u)

@[sa_ref_forward "MorphismsStoich.maEqStoich" 1]
theorem ref_fwd1 : T → S1 := by
  intro t σ _ J X τ u
  exact t.1 (NRxn.contact J X τ) u

@[sa_ref_forward "MorphismsStoich.maEqStoich" 2]
theorem ref_fwd2 : T → S2 := by
  intro t σ _ Y ν u
  exact t.1 (NRxn.exit Y ν) u

@[sa_ref_forward "MorphismsStoich.maEqStoich" 3]
theorem ref_fwd3 : T → S3 := by
  intro t σ _ X Y a u
  exact t.1 (NRxn.trans X (some Y) a) u

@[sa_ref_forward "MorphismsStoich.maEqStoich" 4]
theorem ref_fwd4 : T → S4 := by
  intro t σ _ X a u
  exact t.1 (NRxn.trans X none a) u

@[sa_ref_forward "MorphismsStoich.maEqStoich" 5]
theorem ref_fwd5 : T → S5 := by
  intro t σ _ X a u
  exact t.1 (NRxn.resus X a) u

@[sa_ref_forward "MorphismsStoich.maEqStoich" 6]
theorem ref_fwd6 : T → S6 := by
  intro t σ _ X J Y τ u
  exact t.1 (NRxn.nodeContact X J Y τ) u

@[sa_ref_forward "MorphismsStoich.maEqStoich" 7]
theorem ref_fwd7 : T → S7 := by
  intro t σ _ _ rs u
  exact t.2 rs u

@[sa_complete "MorphismsStoich.maEqStoich"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) (s7 : S7) : T := by
  refine ⟨?_, ?_⟩
  · intro σ _ r u
    cases r with
    | contact J X τ => exact s1 J X τ u
    | exit Y ν => exact s2 Y ν u
    | trans X Y a =>
      cases Y with
      | some Y => exact s3 X Y a u
      | none => exact s4 X a u
    | resus X a => exact s5 X a u
    | nodeContact X J Y τ => exact s6 X J Y τ u
  · intro σ _ _ rs u
    exact s7 rs u

end Alignment.Shadows.MorphismsStoich.MaEqStoich
