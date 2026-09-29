import Alignment.Registry
import NetworkEpi.Semantics.MA

/-!
# Blind shadow sets: group `SemanticsMA` (trusted module `NetworkEpi.Semantics.MA`)

Written blind. The author read only `SA-PASS_SKILL.md`, `Alignment/README.md`,
`Alignment/Example/ExampleShadows.lean`, `Alignment/DataTypes/SemanticsMA.md`, the entries of the
claims below in `Alignment/claims_blind.yaml`, and `DESIGN_NetworkEpiCore.md` (§D.3–§D.7, §J–§L).
No theorem statement, definition body or checker was read. `#check` was run only on the DataTypes
vocabulary (`maField`, `maLift`, `pushMA`, `pullMA`, `NRxn.map`, `MA`, `push`, `maSys`).

Vocabulary (DataTypes/SemanticsMA.md):
* `MA σ = ℝ × (σ → ℝ)`, mass-action coordinates `(S, x)`: `S = u.1` is the susceptible fraction,
  `x = u.2` the fraction in each node species;
* `maField r u`, the mass-action field of one T_net reaction; `maLift rs u`, the mass-action vector
  field of a reaction list (the sum of the per-reaction fields);
* `pushMA f u` (S kept, x summed over the fibres of `f`) and `pullMA f u` (S kept, x precomposed
  with `f`), for a species map `f : σ → σ'`;
* `NRxn.map f`, relabelling of the node species of a T_net reaction along `f`;
* gluing of models is expressed on the syntax (DataTypes §(d)): relabel two reaction lists along
  the legs `f : σA → σ`, `g : σB → σ` of a cospan and concatenate them (`++`).

Mass action is total on `NRxn σ` (module header: no admissibility condition), so every statement
below ranges over all T_net reactions, including `resus` and `nodeContact`, and over every species
type and every species map (with the `Fintype`/`DecidableEq` instances that `pushMA` and `maField`
need, quantified arbitrarily).
-/

open NEP

/-! ## `SemanticsMA.maLiftAppend`

Blind text (three fragments):
1. "**H1′ for mass action, part 1: the MA lift is additive in the reaction list.** Design
   statement (DESIGN_NetworkEpiCore.md §D.6): "H1′ same for MA, IB, Stoch | yes | same argument";
   §D.4, table row MA, column "Strict under gluing?": "**yes** (Baez–Pollard 2017)"."
2. "**H1′ for mass action, part 2: the MA lift is natural in species maps.** Design statement
   (DESIGN_NetworkEpiCore.md §D.6): "H1′ same for MA, IB, Stoch | yes | same argument" (the
   argument of H1: "local per-reaction fields")."
3. "**H1′ for mass action: the MA lift is strict under gluing.** Design statement
   (DESIGN_NetworkEpiCore.md §D.6): "H1′ same for MA, IB, Stoch | yes | same argument", where H1
   is "EB(glue(A,B)) = glue(EB A, EB B)"; §D.4, table row MA, column "Strict under gluing?":
   "**yes** (Baez–Pollard 2017)"; §D.3 (open systems): "composition identifies ported coordinates
   and **adds** vector fields"."

One shadow per fragment (the text is a conjunction of three claims).

* Part 1, "additive in the reaction list": the lift of a concatenation is the sum of the lifts,
  at every state `u`, for every species type and every pair of T_net reaction lists.
* Part 2, "natural in species maps": the design's naturality of the per-reaction field, stated for
  the lift. The group's own wording of per-reaction naturality (claim `SemanticsMA.maFieldMap`:
  "the field of `r.map f` at `u` is the pushforward of the field of `r` at `pullMA f u`") fixes
  the meaning: the lift of the relabelled list at `u : MA σ'` equals the pushforward along `f` of
  the lift of the original list at the pulled-back state `pullMA f u`.
  -- AMBIGUITY: "natural in species maps". A second conceivable reading ("`pushMA f` is a
  -- semiconjugacy `maSys rs ⟶ maSys (rs.map f)`") is false for non-injective `f` (merging two
  -- catalysts changes the flux `k S x_J`), and it does not match "local per-reaction fields"; the
  -- push/pull reading, used for the per-reaction field in `maFieldMap`, is taken.
* Part 3, "strict under gluing": `glue(A, B)` for reaction lists `rsA` over `σA`, `rsB` over
  `σB`, glued along a cospan `f : σA → σ ← σB : g`, is `rsA.map (NRxn.map f) ++ rsB.map (NRxn.map g)`
  (DataTypes §(d)); `glue(MA A, MA B)` "identifies ported coordinates and adds vector fields"
  (§D.3): at a state `u` of the glued coordinates each component field is evaluated at the
  restriction of `u` to its own species (`pullMA`), pushed into the glued coordinates (`pushMA`,
  which identifies the coordinates that the legs identify, S glued to S), and the two are added.
  Strictness is equality `MA(glue(A,B)) = glue(MA A, MA B)` (H1: "EB(glue(A,B)) = glue(EB A, EB B)").
-/

namespace Alignment.Shadows.SemanticsMA.MaLiftAppend

/-- Fragment 1, "the MA lift is additive in the reaction list": for every species type, every
two T_net reaction lists and every state, the lift of the concatenation is the sum of the
lifts. (Additivity on the list monoid `(List, ++, [])`; since `MA σ` is an additive group this
also forces the lift of the empty list to be `0`.) -/
def Additive : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (rs₁ rs₂ : List (NRxn σ)) (u : MA σ),
    maLift (rs₁ ++ rs₂) u = maLift rs₁ u + maLift rs₂ u

/-- Fragment 2, "the MA lift is natural in species maps" (the argument of H1: "local
per-reaction fields"): relabelling the reaction list along any species map `f : σ → σ'` and
lifting gives, at every state `u` of the target coordinates, the pushforward along `f` of the
lift of the original list evaluated at the pulled-back state `pullMA f u` (S kept, x
precomposed with `f`).
-- AMBIGUITY: "natural in species maps". Read as the push/pull naturality square of the field
-- (the only reading consistent with "local per-reaction fields" for arbitrary, possibly
-- non-injective, `f`); the alternative "`pushMA f` is a semiconjugacy" is false when `f` merges
-- two catalysts, since the flux `k S x_J` is not linear in the merged coordinate. -/
def Natural : Prop :=
  ∀ {σ σ' : Type} [DecidableEq σ] [Fintype σ] [DecidableEq σ'] (f : σ → σ')
    (rs : List (NRxn σ)) (u : MA σ'),
    maLift (rs.map (NRxn.map f)) u = pushMA f (maLift rs (pullMA f u))

/-- Fragment 3, "the MA lift is strict under gluing", `MA(glue(A,B)) = glue(MA A, MA B)`:
for every cospan of species maps `f : σA → σ ← σB : g` (s glued to s, which `pushMA`/`pullMA`
do by keeping `S`) and all T_net reaction lists `rsA`, `rsB`,
* `glue(A,B)` is the syntax-side gluing (DataTypes §(d), DESIGN §D.2 "pushout of species sets
  with concatenation of reaction lists"): `rsA.map (NRxn.map f) ++ rsB.map (NRxn.map g)`;
* `glue(MA A, MA B)` "identifies ported coordinates and adds vector fields" (§D.3): at a state
  `u` of the glued coordinates, each component field is evaluated at the component's own
  coordinates `pullMA f u` (resp. `pullMA g u`), carried into the glued coordinates by `pushMA`,
  and the two contributions are added;
* strictness is equality of the two vector fields at every state `u`. -/
def StrictGlue : Prop :=
  ∀ {σA σB σ : Type} [DecidableEq σA] [Fintype σA] [DecidableEq σB] [Fintype σB]
    [DecidableEq σ] (f : σA → σ) (g : σB → σ)
    (rsA : List (NRxn σA)) (rsB : List (NRxn σB)) (u : MA σ),
    maLift (rsA.map (NRxn.map f) ++ rsB.map (NRxn.map g)) u =
      pushMA f (maLift rsA (pullMA f u)) + pushMA g (maLift rsB (pullMA g u))

/-- Intended statement: the conjunction of the three fragments. -/
@[sa_reference "SemanticsMA.maLiftAppend"]
def T : Prop := Additive ∧ Natural ∧ StrictGlue

/-- S1: the MA lift is additive in the reaction list. -/
@[sa_shadow "SemanticsMA.maLiftAppend" 1]
def S1 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (rs₁ rs₂ : List (NRxn σ)) (u : MA σ),
    maLift (rs₁ ++ rs₂) u = maLift rs₁ u + maLift rs₂ u

/-- S2: the MA lift is natural in species maps (push/pull square). -/
@[sa_shadow "SemanticsMA.maLiftAppend" 2]
def S2 : Prop :=
  ∀ {σ σ' : Type} [DecidableEq σ] [Fintype σ] [DecidableEq σ'] (f : σ → σ')
    (rs : List (NRxn σ)) (u : MA σ'),
    maLift (rs.map (NRxn.map f)) u = pushMA f (maLift rs (pullMA f u))

/-- S3: the MA lift is strict under gluing along any cospan of species maps. -/
@[sa_shadow "SemanticsMA.maLiftAppend" 3]
def S3 : Prop :=
  ∀ {σA σB σ : Type} [DecidableEq σA] [Fintype σA] [DecidableEq σB] [Fintype σB]
    [DecidableEq σ] (f : σA → σ) (g : σB → σ)
    (rsA : List (NRxn σA)) (rsB : List (NRxn σB)) (u : MA σ),
    maLift (rsA.map (NRxn.map f) ++ rsB.map (NRxn.map g)) u =
      pushMA f (maLift rsA (pullMA f u)) + pushMA g (maLift rsB (pullMA g u))

@[sa_ref_forward "SemanticsMA.maLiftAppend" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "SemanticsMA.maLiftAppend" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1

@[sa_ref_forward "SemanticsMA.maLiftAppend" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2

@[sa_complete "SemanticsMA.maLiftAppend"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.SemanticsMA.MaLiftAppend

/-! ## `SemanticsMA.pushMAAdd`

Blind text: "The pushforward of MA coordinates is additive."

`pushMA f : MA σ → MA σ'` (S kept, x summed over fibres). Additivity: `pushMA f (u + v) =
pushMA f u + pushMA f v` for every species map `f` and all MA vectors `u v` (addition on
`MA σ = ℝ × (σ → ℝ)` is componentwise). A single atomic requirement. -/

namespace Alignment.Shadows.SemanticsMA.PushMAAdd

/-- Intended statement: for every species map, the pushforward of MA coordinates preserves sums. -/
@[sa_reference "SemanticsMA.pushMAAdd"]
def T : Prop :=
  ∀ {σ σ' : Type} [Fintype σ] [DecidableEq σ'] (f : σ → σ') (u v : MA σ),
    pushMA f (u + v) = pushMA f u + pushMA f v

/-- S1: the whole statement (a single atomic requirement). -/
@[sa_shadow "SemanticsMA.pushMAAdd" 1]
def S1 : Prop :=
  ∀ {σ σ' : Type} [Fintype σ] [DecidableEq σ'] (f : σ → σ') (u v : MA σ),
    pushMA f (u + v) = pushMA f u + pushMA f v

@[sa_ref_forward "SemanticsMA.pushMAAdd" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "SemanticsMA.pushMAAdd"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SemanticsMA.PushMAAdd

/-! ## `SemanticsMA.pushMAZero`

Blind text: "The pushforward of the zero MA vector is zero."

For every species map `f : σ → σ'`, `pushMA f 0 = 0`, where `0 : MA σ` is the zero vector
`(0, 0)` of `ℝ × (σ → ℝ)` and the right-hand side is the zero of `MA σ'`. -/

namespace Alignment.Shadows.SemanticsMA.PushMAZero

/-- Intended statement: for every species map, the pushforward sends the zero MA vector to zero. -/
@[sa_reference "SemanticsMA.pushMAZero"]
def T : Prop :=
  ∀ {σ σ' : Type} [Fintype σ] [DecidableEq σ'] (f : σ → σ'), pushMA f (0 : MA σ) = 0

/-- S1: the whole statement (a single atomic requirement). -/
@[sa_shadow "SemanticsMA.pushMAZero" 1]
def S1 : Prop :=
  ∀ {σ σ' : Type} [Fintype σ] [DecidableEq σ'] (f : σ → σ'), pushMA f (0 : MA σ) = 0

@[sa_ref_forward "SemanticsMA.pushMAZero" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "SemanticsMA.pushMAZero"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SemanticsMA.PushMAZero

/-! ## `SemanticsMA.elimMap`

Blind text: "Reading a catalyst density after relabelling: `J = none` (the susceptible species)
gives `S`, `J = some X` gives `x (f X)`."

A catalyst `J : Option σ` (`none` is the susceptible species `s`, DataTypes `NRxn.nodeContact`)
is read in MA coordinates `u = (S, x) : MA σ'` as `J.elim S x` (DataTypes §(e): "`J.elim S x` is
`S` for `J = none` and `x X` for `J = some X`"; `maField` docstring: "`x_J = S` when `J = none`").
Relabelling along `f : σ → σ'` sends the catalyst `J` to `J.map f` (`Option.map`). The text states
the value of the relabelled catalyst's density at `u` in the two cases, so one shadow per case.

-- AMBIGUITY: "after relabelling". Read as: the catalyst is relabelled (`J.map f`) and its density
-- is read in the target coordinates `u : MA σ'` (the catalyst of `r.map f`). The alternative
-- "read the unrelabelled `J` in `pullMA f u`" gives the same two values but is not "after
-- relabelling" of the catalyst; it is not taken.
-- NOTE (for the reviewer): `S` and `x` are the MA coordinates `u.1`, `u.2` (DataTypes: "for
-- u : MA σ, S = u.1 (susceptible fraction), x = u.2"), so the shadows are stated over `u : MA σ'`.
-- Beyond that coordinate type the text is a statement about `Option.map`/`Option.elim`. -/

namespace Alignment.Shadows.SemanticsMA.ElimMap

/-- Intended statement: after relabelling along `f`, the catalyst `none` (the susceptible species)
reads as `S`, and the catalyst `some X` reads as `x (f X)`, in every MA state `u = (S, x)`. -/
@[sa_reference "SemanticsMA.elimMap"]
def T : Prop :=
  (∀ {σ σ' : Type} (f : σ → σ') (u : MA σ'),
      ((none : Option σ).map f).elim u.1 u.2 = u.1) ∧
  (∀ {σ σ' : Type} (f : σ → σ') (u : MA σ') (X : σ),
      ((some X : Option σ).map f).elim u.1 u.2 = u.2 (f X))

/-- S1: the relabelled susceptible catalyst (`J = none`) reads as the susceptible fraction `S`. -/
@[sa_shadow "SemanticsMA.elimMap" 1]
def S1 : Prop :=
  ∀ {σ σ' : Type} (f : σ → σ') (u : MA σ'),
    ((none : Option σ).map f).elim u.1 u.2 = u.1

/-- S2: the relabelled node-species catalyst `J = some X` reads as `x (f X)`. -/
@[sa_shadow "SemanticsMA.elimMap" 2]
def S2 : Prop :=
  ∀ {σ σ' : Type} (f : σ → σ') (u : MA σ') (X : σ),
    ((some X : Option σ).map f).elim u.1 u.2 = u.2 (f X)

@[sa_ref_forward "SemanticsMA.elimMap" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "SemanticsMA.elimMap" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "SemanticsMA.elimMap"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.SemanticsMA.ElimMap

/-! ## `SemanticsMA.maFieldMap`

Blind text: "Naturality of the per-reaction mass-action field in species maps: the field of
`r.map f` at `u` is the pushforward of the field of `r` at `pullMA f u`."

For every species map `f : σ → σ'`, every T_net reaction `r : NRxn σ` and every MA state
`u : MA σ'`: `maField (r.map f) u = pushMA f (maField r (pullMA f u))`.

The text quantifies over all reactions `r`, and mass action is total on T_net (module header), so
the statement is split along the six T_net reaction types of DESIGN §B.2 (`NRxn.type`): contact,
exit, progress (`trans X (some Y)`), remove (`trans X none`), resus and node contact. The six
shadows are jointly equivalent to the statement (every `r : NRxn σ` has exactly one of these
shapes), and each is falsified by an implementation that omits or mishandles that reaction type
(for example one proved only for the T_EB constructors). -/

namespace Alignment.Shadows.SemanticsMA.MaFieldMap

/-- Intended statement: the per-reaction mass-action field is natural in species maps. -/
@[sa_reference "SemanticsMA.maFieldMap"]
def T : Prop :=
  ∀ {σ σ' : Type} [DecidableEq σ] [Fintype σ] [DecidableEq σ'] (f : σ → σ') (r : NRxn σ)
    (u : MA σ'),
    maField (r.map f) u = pushMA f (maField r (pullMA f u))

/-- S1 (contact `s + J → X + J`, type `:contact`). -/
@[sa_shadow "SemanticsMA.maFieldMap" 1]
def S1 : Prop :=
  ∀ {σ σ' : Type} [DecidableEq σ] [Fintype σ] [DecidableEq σ'] (f : σ → σ') (J X : σ) (τ : ℝ)
    (u : MA σ'),
    maField ((NRxn.contact J X τ).map f) u = pushMA f (maField (NRxn.contact J X τ) (pullMA f u))

/-- S2 (exit `s → Y`, type `:exit`). -/
@[sa_shadow "SemanticsMA.maFieldMap" 2]
def S2 : Prop :=
  ∀ {σ σ' : Type} [DecidableEq σ] [Fintype σ] [DecidableEq σ'] (f : σ → σ') (Y : σ) (ν : ℝ)
    (u : MA σ'),
    maField ((NRxn.exit Y ν).map f) u = pushMA f (maField (NRxn.exit Y ν) (pullMA f u))

/-- S3 (progression `X → Y`, type `:progress`). -/
@[sa_shadow "SemanticsMA.maFieldMap" 3]
def S3 : Prop :=
  ∀ {σ σ' : Type} [DecidableEq σ] [Fintype σ] [DecidableEq σ'] (f : σ → σ') (X Y : σ) (a : ℝ)
    (u : MA σ'),
    maField ((NRxn.trans X (some Y) a).map f) u =
      pushMA f (maField (NRxn.trans X (some Y) a) (pullMA f u))

/-- S4 (removal `X → ∅`, type `:remove`). -/
@[sa_shadow "SemanticsMA.maFieldMap" 4]
def S4 : Prop :=
  ∀ {σ σ' : Type} [DecidableEq σ] [Fintype σ] [DecidableEq σ'] (f : σ → σ') (X : σ) (a : ℝ)
    (u : MA σ'),
    maField ((NRxn.trans X none a).map f) u =
      pushMA f (maField (NRxn.trans X none a) (pullMA f u))

/-- S5 (resusceptibility `X → s`, type `:resus`; outside T_EB, but mass action is total). -/
@[sa_shadow "SemanticsMA.maFieldMap" 5]
def S5 : Prop :=
  ∀ {σ σ' : Type} [DecidableEq σ] [Fintype σ] [DecidableEq σ'] (f : σ → σ') (X : σ) (a : ℝ)
    (u : MA σ'),
    maField ((NRxn.resus X a).map f) u = pushMA f (maField (NRxn.resus X a) (pullMA f u))

/-- S6 (node contact `X + J → Y + J`, `J = none` the susceptible species, type `:node_contact`;
outside T_EB, but mass action is total). -/
@[sa_shadow "SemanticsMA.maFieldMap" 6]
def S6 : Prop :=
  ∀ {σ σ' : Type} [DecidableEq σ] [Fintype σ] [DecidableEq σ'] (f : σ → σ') (X : σ)
    (J : Option σ) (Y : σ) (τ : ℝ) (u : MA σ'),
    maField ((NRxn.nodeContact X J Y τ).map f) u =
      pushMA f (maField (NRxn.nodeContact X J Y τ) (pullMA f u))

@[sa_ref_forward "SemanticsMA.maFieldMap" 1]
theorem ref_fwd1 : T → S1 := by
  intro t σ σ' _ _ _ f J X τ u
  exact t f (NRxn.contact J X τ) u

@[sa_ref_forward "SemanticsMA.maFieldMap" 2]
theorem ref_fwd2 : T → S2 := by
  intro t σ σ' _ _ _ f Y ν u
  exact t f (NRxn.exit Y ν) u

@[sa_ref_forward "SemanticsMA.maFieldMap" 3]
theorem ref_fwd3 : T → S3 := by
  intro t σ σ' _ _ _ f X Y a u
  exact t f (NRxn.trans X (some Y) a) u

@[sa_ref_forward "SemanticsMA.maFieldMap" 4]
theorem ref_fwd4 : T → S4 := by
  intro t σ σ' _ _ _ f X a u
  exact t f (NRxn.trans X none a) u

@[sa_ref_forward "SemanticsMA.maFieldMap" 5]
theorem ref_fwd5 : T → S5 := by
  intro t σ σ' _ _ _ f X a u
  exact t f (NRxn.resus X a) u

@[sa_ref_forward "SemanticsMA.maFieldMap" 6]
theorem ref_fwd6 : T → S6 := by
  intro t σ σ' _ _ _ f X J Y τ u
  exact t f (NRxn.nodeContact X J Y τ) u

@[sa_complete "SemanticsMA.maFieldMap"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) : T := by
  intro σ σ' _ _ _ f r u
  cases r with
  | contact J X τ => exact s1 f J X τ u
  | exit Y ν => exact s2 f Y ν u
  | trans X Y a =>
    cases Y with
    | none => exact s4 f X a u
    | some Y => exact s3 f X Y a u
  | resus X a => exact s5 f X a u
  | nodeContact X J Y τ => exact s6 f X J Y τ u

end Alignment.Shadows.SemanticsMA.MaFieldMap
