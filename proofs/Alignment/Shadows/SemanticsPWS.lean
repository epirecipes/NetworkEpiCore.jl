import Alignment.Registry
import NetworkEpi.Semantics.PWS

/-!
# Blind shadow sets: group `SemanticsPWS`

Written blind. The author read only `SA-PASS_SKILL.md`, `Alignment/README.md`,
`Alignment/Example/ExampleShadows.lean`, `Alignment/DataTypes/SemanticsPWS.md`, the entries of the
four claims below in `Alignment/claims_blind.yaml`, and `DESIGN_NetworkEpiCore.md` (§D.1–§D.7,
§J, §L). No trusted source file, checker, report or registry fragment was opened.
The blocks of `SemanticsPWS.f2SumSV` and `SemanticsPWS.pwSGlueNotStrict` were re-shadowed blind
after a text remediation (same reading list, plus DESIGN §M).

Vocabulary (DataTypes/SemanticsPWS.md): `PWS σ = ℝ × ℝ × (σ → ℝ) × (σ → ℝ)` with
`[s] = w.1`, `[ss] = w.2.1`, `[sZ] = w.2.2.1 Z`, `[Z] = w.2.2.2 Z`; the per-reaction field
`pwSField K` and the reaction-list field `pwSLift K` with constant triple closure
`[A s B] = K [As][sB]/[s]`; the pushforward `pushPW f` (`[s]`, `[ss]` kept, `[sZ]`, `[Z]` summed
over fibres) and the pullback `pullPW f`; the F2 witness `f2A` (infection `s + I → I + I` at
τ = 1), `f2B` (vaccination `s → V` at ν = 1) and `f2State` over `Unit ⊕ Unit` with
`I = Sum.inl ()`, `V = Sum.inr ()`.

Gluing (DataTypes §(d)): models are glued on the syntax by relabelling two reaction lists along the
legs `f : σA → σ`, `g : σB → σ` of a cospan and concatenating them,
`A.map (Rxn.map f) ++ B.map (Rxn.map g)`. The glue of the two *vector fields* (DESIGN §D.3, open
systems: "composition identifies ported coordinates and **adds** vector fields") is, at a state `w`
of the glued coordinates, the sum of the pushed-forward fields of `A` and `B` evaluated at the
pulled-back states: `pushPW f (pwSLift K A (pullPW f w)) + pushPW g (pwSLift K B (pullPW g w))`.
-/

open NEP

namespace Alignment.Shadows.SemanticsPWS.PwSLiftAppend

/-! ### `SemanticsPWS.pwSLiftAppend`

Blind text: "The PW^S field is additive in the reaction list (like the EB lift)."

Reading: for every node-species type `σ`, every closure constant `K`, all reaction lists `rs₁`,
`rs₂` and every state `w`, the field of the concatenation is the sum of the fields,
`pwSLift K (rs₁ ++ rs₂) w = pwSLift K rs₁ w + pwSLift K rs₂ w` (addition in
`ℝ × ℝ × (σ → ℝ) × (σ → ℝ)` is componentwise). The text restricts neither `K` nor `σ` nor the
lists nor the state, so all are universally quantified.

AMBIGUITY: "(like the EB lift)" — read as a comparison with the EB lift's additivity (a claim of
group `SemanticsEB`), not as a second assertion of this claim.

Split: the equality of four-component states is split into its four coordinates `[s]`, `[ss]`,
`[sZ]` (every `Z`) and `[Z]` (every `Z`), one atomic requirement each. -/

/-- Intended statement: the PW^S vector field is additive over concatenation of reaction lists. -/
@[sa_reference "SemanticsPWS.pwSLiftAppend"]
def T : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (K : ℝ) (rs₁ rs₂ : List (Rxn σ)) (w : PWS σ),
    pwSLift K (rs₁ ++ rs₂) w = pwSLift K rs₁ w + pwSLift K rs₂ w

/-- S1: the `[s]` coordinate is additive. -/
@[sa_shadow "SemanticsPWS.pwSLiftAppend" 1]
def S1 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (K : ℝ) (rs₁ rs₂ : List (Rxn σ)) (w : PWS σ),
    (pwSLift K (rs₁ ++ rs₂) w).1 = (pwSLift K rs₁ w).1 + (pwSLift K rs₂ w).1

/-- S2: the `[ss]` coordinate is additive. -/
@[sa_shadow "SemanticsPWS.pwSLiftAppend" 2]
def S2 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (K : ℝ) (rs₁ rs₂ : List (Rxn σ)) (w : PWS σ),
    (pwSLift K (rs₁ ++ rs₂) w).2.1 = (pwSLift K rs₁ w).2.1 + (pwSLift K rs₂ w).2.1

/-- S3: every `[sZ]` coordinate is additive. -/
@[sa_shadow "SemanticsPWS.pwSLiftAppend" 3]
def S3 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (K : ℝ) (rs₁ rs₂ : List (Rxn σ)) (w : PWS σ) (Z : σ),
    (pwSLift K (rs₁ ++ rs₂) w).2.2.1 Z = (pwSLift K rs₁ w).2.2.1 Z + (pwSLift K rs₂ w).2.2.1 Z

/-- S4: every `[Z]` coordinate is additive. -/
@[sa_shadow "SemanticsPWS.pwSLiftAppend" 4]
def S4 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (K : ℝ) (rs₁ rs₂ : List (Rxn σ)) (w : PWS σ) (Z : σ),
    (pwSLift K (rs₁ ++ rs₂) w).2.2.2 Z = (pwSLift K rs₁ w).2.2.2 Z + (pwSLift K rs₂ w).2.2.2 Z

@[sa_ref_forward "SemanticsPWS.pwSLiftAppend" 1]
theorem ref_fwd1 : T → S1 := by
  intro t σ _ K rs₁ rs₂ w
  exact congrArg (fun p : PWS σ => p.1) (t K rs₁ rs₂ w)

@[sa_ref_forward "SemanticsPWS.pwSLiftAppend" 2]
theorem ref_fwd2 : T → S2 := by
  intro t σ _ K rs₁ rs₂ w
  exact congrArg (fun p : PWS σ => p.2.1) (t K rs₁ rs₂ w)

@[sa_ref_forward "SemanticsPWS.pwSLiftAppend" 3]
theorem ref_fwd3 : T → S3 := by
  intro t σ _ K rs₁ rs₂ w Z
  exact congrArg (fun p : PWS σ => p.2.2.1 Z) (t K rs₁ rs₂ w)

@[sa_ref_forward "SemanticsPWS.pwSLiftAppend" 4]
theorem ref_fwd4 : T → S4 := by
  intro t σ _ K rs₁ rs₂ w Z
  exact congrArg (fun p : PWS σ => p.2.2.2 Z) (t K rs₁ rs₂ w)

@[sa_complete "SemanticsPWS.pwSLiftAppend"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := by
  intro σ _ K rs₁ rs₂ w
  exact Prod.ext (s1 K rs₁ rs₂ w)
    (Prod.ext (s2 K rs₁ rs₂ w)
      (Prod.ext (funext fun Z => s3 K rs₁ rs₂ w Z) (funext fun Z => s4 K rs₁ rs₂ w Z)))

end Alignment.Shadows.SemanticsPWS.PwSLiftAppend

namespace Alignment.Shadows.SemanticsPWS.F2GluedSV

/-! ### `SemanticsPWS.f2GluedSV`

Blind text: "The `[sV]` component of the PW^S field of the glued witness model at `f2State` is
`−1`."

Reading: the glued witness model is `f2A` relabelled along `Sum.inl` (species `I`) concatenated
with `f2B` relabelled along `Sum.inr` (species `V`) (DataTypes §(d): gluing is relabelling along
the cospan legs and `++`; `f2State` lives over `Unit ⊕ Unit` with `I = Sum.inl ()`,
`V = Sum.inr ()`). Its PW^S field is `pwSLift K` of that list; the `[sV]` component at `f2State`
is `(pwSLift K (f2A.map (Rxn.map Sum.inl) ++ f2B.map (Rxn.map Sum.inr)) f2State).2.2.1 (Sum.inr ())`, and the text says it equals `−1`.

AMBIGUITY: the text does not name the closure constant `K`. By the module header (quoted in
DataTypes), the glued infection contact drains `[sV]` by `τ[V s I] = τ K [Vs][sI]/[s]`, which at
`f2State` (`[s] = [sV] = [sI] = 1`, τ = 1) is `K`, while the vaccination exit contributes
`−ν[sV] + ν[ss] = 0`; so the component is `−K` and the stated value `−1` is the witness at the
unit closure `K = 1`. A "for every K" reading would contradict the stated value, so the only
coherent reading is `K = 1`. -/

/-- Intended statement: at the unit closure, the `[sV]` component of the PW^S field of the glued
F2 witness model at `f2State` is `−1`. -/
@[sa_reference "SemanticsPWS.f2GluedSV"]
def T : Prop :=
  (pwSLift 1 (f2A.map (Rxn.map Sum.inl) ++ f2B.map (Rxn.map Sum.inr)) f2State).2.2.1
      (Sum.inr ()) = -1

/-- S1: the whole statement (a single atomic requirement). -/
@[sa_shadow "SemanticsPWS.f2GluedSV" 1]
def S1 : Prop :=
  (pwSLift 1 (f2A.map (Rxn.map Sum.inl) ++ f2B.map (Rxn.map Sum.inr)) f2State).2.2.1
      (Sum.inr ()) = -1

@[sa_ref_forward "SemanticsPWS.f2GluedSV" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "SemanticsPWS.f2GluedSV"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SemanticsPWS.F2GluedSV

namespace Alignment.Shadows.SemanticsPWS.F2SumSV

/-! ### `SemanticsPWS.f2SumSV` (re-shadowed blind after text remediation)

Blind text: "The `[sV]` component of the sum of the pushed-forward PW^S fields of `A` and `B` is
`0`."

Reading: `A = f2A` (infection `s + I → I + I`, τ = 1, one node species `I`) and `B = f2B`
(vaccination `s → V`, ν = 1, one node species `V`), the F2 witness of DataTypes. They are glued
along the cospan `Sum.inl : Unit → Unit ⊕ Unit` (`I = Sum.inl ()`) and
`Sum.inr : Unit → Unit ⊕ Unit` (`V = Sum.inr ()`). The pushed-forward PW^S field of `A` at a glued
state `w` is `pushPW Sum.inl (pwSLift K f2A (pullPW Sum.inl w))`, likewise for `B` along
`Sum.inr`; "the sum" is their sum in `PWS (Unit ⊕ Unit)` (DESIGN §D.3: composition "adds vector
fields"), i.e. `glue(PW^S A, PW^S B)` of §D.4. The `[sV]` component is the `Sum.inr ()` entry of
the `[sZ]` coordinate (`.2.2.1`).

AMBIGUITY (state): the text names no state. The `[sV]` component of this sum is not zero at every
state (by the module header, the exit contributes `ν([ss] − [sV])` to `[sV]'`), so a
"for every state" reading would be false; the statement is read at the witness state `f2State`
(`[s] = [ss] = [sI] = [sV] = 1`, `[I] = [V] = 0`), the state of the companion sentence about the
glued model.

AMBIGUITY (closure constant `K`): the text names none. Readings, one shadow each:
(a) for every closure constant `K` (the text restricts none; the sum involves no triple of `A`
landing on `V`, so the value is `K`-free by the header formulas);
(b) at the unit closure `K = 1`, the constant at which the companion glued value `−1` is stated.
Reading (a) implies reading (b). -/

/-- The `[sV]` component, at `f2State`, of the sum of the pushed-forward PW^S fields of `f2A`
(along `Sum.inl`) and `f2B` (along `Sum.inr`), with closure constant `K`. -/
noncomputable def sumSV (K : ℝ) : ℝ :=
  (pushPW Sum.inl (pwSLift K f2A (pullPW Sum.inl f2State)) +
      pushPW Sum.inr (pwSLift K f2B (pullPW Sum.inr f2State))).2.2.1 (Sum.inr ())

/-- Intended statement: for every closure constant `K` the `[sV]` component of the sum of the
pushed-forward PW^S fields of `A` and `B` at `f2State` is `0`; in particular at `K = 1`. -/
@[sa_reference "SemanticsPWS.f2SumSV"]
def T : Prop := (∀ K : ℝ, sumSV K = 0) ∧ sumSV 1 = 0

/-- S1 (reading (a)): for every closure constant, the component is `0`. -/
@[sa_shadow "SemanticsPWS.f2SumSV" 1]
def S1 : Prop := ∀ K : ℝ, sumSV K = 0

/-- S2 (reading (b)): at the unit closure, the component is `0`. -/
@[sa_shadow "SemanticsPWS.f2SumSV" 2]
def S2 : Prop := sumSV 1 = 0

@[sa_ref_forward "SemanticsPWS.f2SumSV" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "SemanticsPWS.f2SumSV" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "SemanticsPWS.f2SumSV"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.SemanticsPWS.F2SumSV

namespace Alignment.Shadows.SemanticsPWS.PwSGlueNotStrict

/-! ### `SemanticsPWS.pwSGlueNotStrict` (re-shadowed blind after text remediation)

Blind text: "**F2: the S-anchored pairwise field is not strict under gluing.** Design statement
(DESIGN_NetworkEpiCore.md §D.6): "**F2/F2′** same for PW, PW^S, PB, clustered EB | **no** (lax) |
a contact drains [Z s] (or triangle pairs) for every Z | Lean witness (stretch, L3)"; §D.4: "A
PW^S contact drains every [Z s] through the closed triple [Z s J]. When B's species are glued in,
A's contacts must also drain [Z_B s], which A's system does not contain. So PW^S(glue(A,B)) ≠
glue(PW^S A, PW^S B).""

Reading. "Strict under gluing" is the §D.6 law H1 ("EB(glue(A,B)) = glue(EB A, EB B)") with
PW^S in place of EB. On the Lean side (DataTypes §(d)):
* `glue(A,B)` for `A : List (Rxn σA)`, `B : List (Rxn σB)` and a cospan `f : σA → σ ← σB : g`
  is `A.map (Rxn.map f) ++ B.map (Rxn.map g)`; since `glue` is a pushout on identified species
  (DESIGN §D.6, table of §B: "pushout on the identified species"), the legs are injective and
  jointly surjective (`IsGlueCospan`); the susceptible `s` is implicit and glued to itself;
* `PW^S(glue(A,B))` is the field `w ↦ pwSLift K (glue) w` on `PWS σ`;
* `glue(PW^S A, PW^S B)` identifies ported coordinates and adds the fields (§D.3):
  `w ↦ pushPW f (pwSLift K A (pullPW f w)) + pushPW g (pwSLift K B (pullPW g w))`.
The conclusion "PW^S(glue(A,B)) ≠ glue(PW^S A, PW^S B)" is the inequality of these two fields
(functions `PWS σ → PWS σ`) for some gluing, i.e. a witness exists ("**no**", "Lean witness").
The reason clause ("a contact drains [Z s] for every Z") explains why; its concrete instance at
the F2 witness is the subject of the claims `SemanticsPWS.f2GluedSV` / `SemanticsPWS.f2SumSV`.

AMBIGUITY ("≠" as a witness vs "the law fails"): the text says "≠" and cites a "Lean witness",
so a witness gluing with unequal fields is required (`GlueFails`), not merely the negation of the
universally quantified law. A generic reading "for every A with a contact and every B with a new
species the fields differ" is not taken: it needs conditions (τ ≠ 0, K ≠ 0, no cancellation) the
text does not state, and the text presents the contact draining as the reason.

AMBIGUITY (closure constant `K`): the text names none. Readings, one shadow each:
(a) for every closure constant `K` (the text restricts none);
(b) at the unit closure `K = 1` of the witness. Reading (a) implies reading (b).

AMBIGUITY ("(lax)"): a lax comparison map is not formalised (DataTypes: "no notion of a lax
comparison map"); only the failure of strictness is. -/

/-- The legs of a gluing cospan (a pushout of species along identified species): both legs are
injective and together they cover the glued species. -/
def IsGlueCospan {σA σB σ : Type} (f : σA → σ) (g : σB → σ) : Prop :=
  Function.Injective f ∧ Function.Injective g ∧ ∀ y : σ, (∃ a, f a = y) ∨ (∃ b, g b = y)

/-- Failure of strictness of PW^S (closure constant `K`) under gluing: there is a gluing cospan
and reaction lists `A`, `B` such that the PW^S field of the glued model differs from the glue
(pushforward along the legs of the fields at the pulled-back states, added) of the PW^S fields. -/
def GlueFails (K : ℝ) : Prop :=
  ∃ (σA σB σ : Type) (_ : Fintype σA) (_ : DecidableEq σA) (_ : Fintype σB) (_ : DecidableEq σB)
    (_ : DecidableEq σ) (f : σA → σ) (g : σB → σ) (A : List (Rxn σA)) (B : List (Rxn σB)),
    IsGlueCospan f g ∧
      (fun w : PWS σ => pwSLift K (A.map (Rxn.map f) ++ B.map (Rxn.map g)) w) ≠
        (fun w : PWS σ => pushPW f (pwSLift K A (pullPW f w)) + pushPW g (pwSLift K B (pullPW g w)))

/-- Intended statement: for every closure constant `K`, PW^S is not strict under gluing (a witness
gluing exists); in particular at the unit closure. -/
@[sa_reference "SemanticsPWS.pwSGlueNotStrict"]
def T : Prop := (∀ K : ℝ, GlueFails K) ∧ GlueFails 1

/-- S1 (reading (a)): for every `K`, a gluing on which the two PW^S fields differ exists. -/
@[sa_shadow "SemanticsPWS.pwSGlueNotStrict" 1]
def S1 : Prop := ∀ K : ℝ, GlueFails K

/-- S2 (reading (b)): at `K = 1`, a gluing on which the two PW^S fields differ exists. -/
@[sa_shadow "SemanticsPWS.pwSGlueNotStrict" 2]
def S2 : Prop := GlueFails 1

@[sa_ref_forward "SemanticsPWS.pwSGlueNotStrict" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "SemanticsPWS.pwSGlueNotStrict" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "SemanticsPWS.pwSGlueNotStrict"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.SemanticsPWS.PwSGlueNotStrict
