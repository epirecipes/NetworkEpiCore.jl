import Alignment.Registry
import NetworkEpi.Dyn.Basic

/-!
# Blind shadow sets: group `DynBasic` (trusted module `NetworkEpi.Dyn.Basic`)

Written blind. The author read only `SA-PASS_SKILL.md`, `Alignment/README.md`,
`Alignment/Example/ExampleShadows.lean`, `Alignment/DataTypes/DynBasic.md`, the entries of the
eleven claim ids below in `Alignment/claims_blind.yaml`, and `DESIGN_NetworkEpiCore.md` (§D.3,
§D.7 and amendment §J.2). Vocabulary was checked with `#check` on the `DataTypes/DynBasic.md`
names only.

Vocabulary: `DynSys` (fields `V`, `F`; `A.V` is a real normed space), `Semiconj A B` (fields `π`,
`diff`, `comm`), `SemiconjOn A B U`, the predicates `IsSemiconj`, `IsSemiconjOn`, the category
instance `dynCategory` (`A ⟶ B`, `𝟙 A`, `f ≫ g`), `DynSys.restrict`, `DynSys.restrictIncl`,
`invariantIncl`. There is no trusted "is a solution" predicate (`DataTypes`, §d); solutions are
spelled out with `HasDerivAt` / `HasDerivWithinAt` at the times concerned.

Conventions used throughout.
* "Semiconjugacy" (bundled) is `Semiconj A B`, a local semiconjugacy on `U` is `SemiconjOn A B U`;
  its underlying map is `m.π`.
* A curve is `x : ℝ → A.V`. "`x'(t) = F(x(t))`" is `HasDerivAt x (A.F (x t)) t` (two-sided), or
  `HasDerivWithinAt x (A.F (x t)) I t` when the text says "within `I`" / "on a time interval"
  (DESIGN §J.2: "EB solutions are taken on a time interval I ∋ 0 (`HasDerivWithinAt` on a convex
  I)"). The image curve is `m.π ∘ x` and its required derivative is `B.F (m.π (x t))`.
* An *open time interval* (possibly unbounded or empty) is a set `J : Set ℝ` with `IsOpen J` and
  `Convex ℝ J`; a *time interval* is a set `I` with `Convex ℝ I`.
-/

open NEP CategoryTheory

/-! ## `DynBasic.semiconjIsSemiconj` -/
namespace Alignment.Shadows.DynBasic.SemiconjIsSemiconj

/-! Blind text: "A bundled semiconjugacy satisfies `IsSemiconj`."

The text names the predicate `IsSemiconj` itself, so the shadow is stated with it: for all
systems `A`, `B` and every bundled semiconjugacy `m : Semiconj A B`, the underlying map `m.π`
satisfies `IsSemiconj A B`. One atomic requirement. -/

/-- Intended statement: every bundled semiconjugacy's map satisfies `IsSemiconj`. -/
@[sa_reference "DynBasic.semiconjIsSemiconj"]
def T : Prop := ∀ {A B : DynSys} (m : Semiconj A B), IsSemiconj A B m.π

/-- S1: for every `m : Semiconj A B`, `IsSemiconj A B m.π`. -/
@[sa_shadow "DynBasic.semiconjIsSemiconj" 1]
def S1 : Prop := ∀ {A B : DynSys} (m : Semiconj A B), IsSemiconj A B m.π

@[sa_ref_forward "DynBasic.semiconjIsSemiconj" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "DynBasic.semiconjIsSemiconj"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.DynBasic.SemiconjIsSemiconj

/-! ## `DynBasic.semiconjOnIsSemiconjOn` -/
namespace Alignment.Shadows.DynBasic.SemiconjOnIsSemiconjOn

/-! Blind text: "A bundled local semiconjugacy satisfies `IsSemiconjOn`."

For all systems `A`, `B`, every set `U ⊆ A.V` and every bundled local semiconjugacy
`m : SemiconjOn A B U`, the map `m.π` satisfies `IsSemiconjOn A B U` (on the same set `U`). -/

/-- Intended statement: every bundled local semiconjugacy on `U` satisfies `IsSemiconjOn` on `U`. -/
@[sa_reference "DynBasic.semiconjOnIsSemiconjOn"]
def T : Prop := ∀ {A B : DynSys} {U : Set A.V} (m : SemiconjOn A B U), IsSemiconjOn A B U m.π

/-- S1: for every `U` and `m : SemiconjOn A B U`, `IsSemiconjOn A B U m.π`. -/
@[sa_shadow "DynBasic.semiconjOnIsSemiconjOn" 1]
def S1 : Prop := ∀ {A B : DynSys} {U : Set A.V} (m : SemiconjOn A B U), IsSemiconjOn A B U m.π

@[sa_ref_forward "DynBasic.semiconjOnIsSemiconjOn" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "DynBasic.semiconjOnIsSemiconjOn"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.DynBasic.SemiconjOnIsSemiconjOn

/-! ## `DynBasic.homEqSemiconj` -/
namespace Alignment.Shadows.DynBasic.HomEqSemiconj

/-! Blind text: "The morphisms of `DynSys` are exactly the semiconjugacies."

"Exactly" is read as the strongest natural statement: in the category `DynSys` (instance
`dynCategory`), the hom type `A ⟶ B` *is* the type `Semiconj A B`, for all objects `A`, `B`.
AMBIGUITY: "are exactly" could also be read as a bijection `(A ⟶ B) ≃ Semiconj A B`; the type
equality implies that reading, and a bijection as a data-level shadow could not be checked
non-vacuously. -/

/-- Intended statement: for all `A B : DynSys`, `(A ⟶ B) = Semiconj A B`. -/
@[sa_reference "DynBasic.homEqSemiconj"]
def T : Prop := ∀ A B : DynSys, (A ⟶ B) = Semiconj A B

/-- S1: the hom type of `DynSys` is the type of semiconjugacies. -/
@[sa_shadow "DynBasic.homEqSemiconj" 1]
def S1 : Prop := ∀ A B : DynSys, (A ⟶ B) = Semiconj A B

@[sa_ref_forward "DynBasic.homEqSemiconj" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "DynBasic.homEqSemiconj"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.DynBasic.HomEqSemiconj

/-! ## `DynBasic.idPi` -/
namespace Alignment.Shadows.DynBasic.IdPi

/-! Blind text: "In `DynSys` the identity morphism is the identity map."

For every object `A`, the underlying map of the category's identity `𝟙 A` is the identity
function of `A.V`. -/

/-- Intended statement: `(𝟙 A).π = id` for every `A : DynSys`. -/
@[sa_reference "DynBasic.idPi"]
def T : Prop := ∀ A : DynSys, Semiconj.π (𝟙 A) = (id : A.V → A.V)

/-- S1: the identity morphism's underlying map is `id`. -/
@[sa_shadow "DynBasic.idPi" 1]
def S1 : Prop := ∀ A : DynSys, Semiconj.π (𝟙 A) = (id : A.V → A.V)

@[sa_ref_forward "DynBasic.idPi" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "DynBasic.idPi"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.DynBasic.IdPi

/-! ## `DynBasic.compPi` -/
namespace Alignment.Shadows.DynBasic.CompPi

/-! Blind text: "In `DynSys` composition of morphisms is composition of the underlying maps."

For all `f : A ⟶ B` and `g : B ⟶ C`, the underlying map of the categorical composite `f ≫ g`
(first `f`, then `g`) is the composite of maps `g.π ∘ f.π`. -/

/-- Intended statement: `(f ≫ g).π = g.π ∘ f.π`. -/
@[sa_reference "DynBasic.compPi"]
def T : Prop :=
  ∀ {A B C : DynSys} (f : A ⟶ B) (g : B ⟶ C),
    Semiconj.π (f ≫ g) = Semiconj.π g ∘ Semiconj.π f

/-- S1: composition of morphisms is composition of underlying maps. -/
@[sa_shadow "DynBasic.compPi" 1]
def S1 : Prop :=
  ∀ {A B C : DynSys} (f : A ⟶ B) (g : B ⟶ C),
    Semiconj.π (f ≫ g) = Semiconj.π g ∘ Semiconj.π f

@[sa_ref_forward "DynBasic.compPi" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "DynBasic.compPi"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.DynBasic.CompPi

/-! ## `DynBasic.mapSolution` -/
namespace Alignment.Shadows.DynBasic.MapSolution

/-! Blind text: "**Semiconjugacies map solutions to solutions.** Design statement
(DESIGN_NetworkEpiCore.md §D.3): "[L] `instance : Category DynSys` and `Semiconj.map_solution`
(semiconjugacies map solution curves to solution curves)". [...] **The category `DynSys`**
(DESIGN §D.3: "[L] `instance : Category DynSys`"). Objects are `DynSys`, morphisms `A ⟶ B` are
`Semiconj A B`, the identity is `id` and composition is composition of maps (`comp_π`, `id_π`)."

The claim has two parts, split into atomic shadows.

1. Solutions to solutions. A solution curve of `A` is `x : ℝ → A.V` with `x'(t) = F(x(t))` at
   the times of its domain; its image `m.π ∘ x` must satisfy `(π ∘ x)'(t) = G(π(x(t)))` at the
   same times.
   AMBIGUITY: "solution curves" does not fix the time domain. Two readings are both part of the
   text, one shadow each:
   * S1 (global): curves solving at every `t : ℝ`;
   * S2 (open interval): curves solving (two-sided, `HasDerivAt`) at every time of an open
     interval `J` (`IsOpen J`, `Convex ℝ J`, possibly unbounded), mapped to curves solving at
     every time of the same `J`. Justification: the binding amendment DESIGN §J.2 says "Global
     solutions need not exist; EB SEIR on Poisson(5) blows up backward at t ≈ −7.33", so
     "solution curves" cannot mean only curves defined on all of `ℝ`.
   One-sided solutions (`HasDerivWithinAt` on a closed or half-open interval) are not read into
   this text: the separate claim `DynBasic.semiconjMapSolutionWithin` says "within" explicitly.
2. The category. "morphisms `A ⟶ B` are `Semiconj A B`" (S3), "the identity is `id`" (S4) and
   "composition is composition of maps" (S5). "Objects are `DynSys`" is the type of the instance
   and has no propositional content.
   AMBIGUITY: "the identity is `id`" could mean `𝟙 A = Semiconj.id A` or "the identity morphism's
   map is the identity map". The text's own gloss "(`comp_π`, `id_π`)" is about underlying maps,
   so S4 states `(𝟙 A).π = id`. -/

/-- Intended statement: semiconjugacies map global solutions and solutions on open intervals to
solutions, and `DynSys` is the category with hom `Semiconj`, identity map `id` and composition of
maps. -/
@[sa_reference "DynBasic.mapSolution"]
def T : Prop :=
  (∀ {A B : DynSys} (m : Semiconj A B) (x : ℝ → A.V),
      (∀ t : ℝ, HasDerivAt x (A.F (x t)) t) →
        ∀ t : ℝ, HasDerivAt (m.π ∘ x) (B.F (m.π (x t))) t) ∧
  (∀ {A B : DynSys} (m : Semiconj A B) (J : Set ℝ), IsOpen J → Convex ℝ J →
      ∀ x : ℝ → A.V, (∀ t ∈ J, HasDerivAt x (A.F (x t)) t) →
        ∀ t ∈ J, HasDerivAt (m.π ∘ x) (B.F (m.π (x t))) t) ∧
  (∀ A B : DynSys, (A ⟶ B) = Semiconj A B) ∧
  (∀ A : DynSys, Semiconj.π (𝟙 A) = (id : A.V → A.V)) ∧
  (∀ {A B C : DynSys} (f : A ⟶ B) (g : B ⟶ C),
      Semiconj.π (f ≫ g) = Semiconj.π g ∘ Semiconj.π f)

/-- S1 (global solutions): if `x'(t) = F(x(t))` at every `t : ℝ`, then
`(m.π ∘ x)'(t) = G(m.π(x(t)))` at every `t : ℝ`. -/
@[sa_shadow "DynBasic.mapSolution" 1]
def S1 : Prop :=
  ∀ {A B : DynSys} (m : Semiconj A B) (x : ℝ → A.V),
    (∀ t : ℝ, HasDerivAt x (A.F (x t)) t) →
      ∀ t : ℝ, HasDerivAt (m.π ∘ x) (B.F (m.π (x t))) t

/-- S2 (solutions on an open time interval): if `x'(t) = F(x(t))` at every `t` of an open
interval `J`, then `(m.π ∘ x)'(t) = G(m.π(x(t)))` at every `t ∈ J`. -/
@[sa_shadow "DynBasic.mapSolution" 2]
def S2 : Prop :=
  ∀ {A B : DynSys} (m : Semiconj A B) (J : Set ℝ), IsOpen J → Convex ℝ J →
    ∀ x : ℝ → A.V, (∀ t ∈ J, HasDerivAt x (A.F (x t)) t) →
      ∀ t ∈ J, HasDerivAt (m.π ∘ x) (B.F (m.π (x t))) t

/-- S3: the morphisms `A ⟶ B` of `DynSys` are `Semiconj A B`. -/
@[sa_shadow "DynBasic.mapSolution" 3]
def S3 : Prop := ∀ A B : DynSys, (A ⟶ B) = Semiconj A B

/-- S4: the identity morphism's underlying map is `id`. -/
@[sa_shadow "DynBasic.mapSolution" 4]
def S4 : Prop := ∀ A : DynSys, Semiconj.π (𝟙 A) = (id : A.V → A.V)

/-- S5: composition of morphisms is composition of underlying maps. -/
@[sa_shadow "DynBasic.mapSolution" 5]
def S5 : Prop :=
  ∀ {A B C : DynSys} (f : A ⟶ B) (g : B ⟶ C),
    Semiconj.π (f ≫ g) = Semiconj.π g ∘ Semiconj.π f

@[sa_ref_forward "DynBasic.mapSolution" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "DynBasic.mapSolution" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1

@[sa_ref_forward "DynBasic.mapSolution" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2.1

@[sa_ref_forward "DynBasic.mapSolution" 4]
theorem ref_fwd4 : T → S4 := fun t => t.2.2.2.1

@[sa_ref_forward "DynBasic.mapSolution" 5]
theorem ref_fwd5 : T → S5 := fun t => t.2.2.2.2

@[sa_complete "DynBasic.mapSolution"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) : T :=
  ⟨s1, s2, s3, s4, s5⟩

end Alignment.Shadows.DynBasic.MapSolution

/-! ## `DynBasic.semiconjMapSolutionWithin` -/
namespace Alignment.Shadows.DynBasic.SemiconjMapSolutionWithin

/-! Blind text: "Semiconjugacies map solutions within a set of times to solutions within it: if
`x'(t) = F(x(t))` within `I` (`HasDerivWithinAt`) at every `t ∈ I`, then `(π ∘ x)'(t) = G(π(x(t)))`
within `I` at every `t ∈ I`."

"A set of times" is an arbitrary `I : Set ℝ` (no convexity, openness or `0 ∈ I` condition). One
atomic implication. -/

/-- Intended statement: for every semiconjugacy `m`, every set of times `I` and every curve `x`
solving within `I` at each `t ∈ I`, the curve `m.π ∘ x` solves `B`'s equation within `I` at each
`t ∈ I`. -/
@[sa_reference "DynBasic.semiconjMapSolutionWithin"]
def T : Prop :=
  ∀ {A B : DynSys} (m : Semiconj A B) (I : Set ℝ) (x : ℝ → A.V),
    (∀ t ∈ I, HasDerivWithinAt x (A.F (x t)) I t) →
      ∀ t ∈ I, HasDerivWithinAt (m.π ∘ x) (B.F (m.π (x t))) I t

/-- S1: the whole implication (a single atomic requirement). -/
@[sa_shadow "DynBasic.semiconjMapSolutionWithin" 1]
def S1 : Prop :=
  ∀ {A B : DynSys} (m : Semiconj A B) (I : Set ℝ) (x : ℝ → A.V),
    (∀ t ∈ I, HasDerivWithinAt x (A.F (x t)) I t) →
      ∀ t ∈ I, HasDerivWithinAt (m.π ∘ x) (B.F (m.π (x t))) I t

@[sa_ref_forward "DynBasic.semiconjMapSolutionWithin" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "DynBasic.semiconjMapSolutionWithin"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.DynBasic.SemiconjMapSolutionWithin

/-! ## `DynBasic.mapSolutionOn` -/
namespace Alignment.Shadows.DynBasic.MapSolutionOn

/-! Blind text: "**Local semiconjugacies map solutions that stay in `U` to solutions.** Design
statement (DESIGN_NetworkEpiCore.md §D.3): "**Local version `SemiconjOn U`.** The identity holds on
an open set U, and solutions that stay in U are mapped. This is needed for maps that divide by
ψ(θ) or ψ'(θ).""

A local semiconjugacy is `m : SemiconjOn A B U`. A solution that stays in `U` is a curve `x` with
`x(t) ∈ U` and `x'(t) = F(x(t))` at the times of its domain; the image `m.π ∘ x` must satisfy
`(π ∘ x)'(t) = G(π(x(t)))` at the same times.

AMBIGUITY (the set `U`): the design statement says "an open set U". The headline speaks of local
semiconjugacies in general, and `SemiconjOn` (DataTypes) deliberately does not require `U` to be
open ("openness is not required here because differentiability is asked for at each point of
`U`"). The shadows therefore quantify over every `U : Set A.V`; this reading implies the
open-`U` one.

AMBIGUITY (the time domain), as for `DynBasic.mapSolution`: S1 reads "solutions" as curves on all
of `ℝ` (staying in `U` and solving at every `t`), S2 as curves on an open time interval `J`
(staying in `U` and solving, two-sided, at every `t ∈ J`). DESIGN §J.2: "Global solutions need not
exist". Solutions on a general time interval (`HasDerivWithinAt`) are the separate claim
`DynBasic.semiconjOnMapSolutionWithin`. -/

/-- Intended statement: local semiconjugacies on any `U` map global solutions staying in `U`, and
solutions on an open interval staying in `U` there, to solutions. -/
@[sa_reference "DynBasic.mapSolutionOn"]
def T : Prop :=
  (∀ {A B : DynSys} {U : Set A.V} (m : SemiconjOn A B U) (x : ℝ → A.V),
      (∀ t : ℝ, x t ∈ U) → (∀ t : ℝ, HasDerivAt x (A.F (x t)) t) →
        ∀ t : ℝ, HasDerivAt (m.π ∘ x) (B.F (m.π (x t))) t) ∧
  (∀ {A B : DynSys} {U : Set A.V} (m : SemiconjOn A B U) (J : Set ℝ), IsOpen J → Convex ℝ J →
      ∀ x : ℝ → A.V, (∀ t ∈ J, x t ∈ U) → (∀ t ∈ J, HasDerivAt x (A.F (x t)) t) →
        ∀ t ∈ J, HasDerivAt (m.π ∘ x) (B.F (m.π (x t))) t)

/-- S1 (global solutions staying in `U`): if `x(t) ∈ U` and `x'(t) = F(x(t))` for every `t : ℝ`,
then `(m.π ∘ x)'(t) = G(m.π(x(t)))` for every `t : ℝ`. -/
@[sa_shadow "DynBasic.mapSolutionOn" 1]
def S1 : Prop :=
  ∀ {A B : DynSys} {U : Set A.V} (m : SemiconjOn A B U) (x : ℝ → A.V),
    (∀ t : ℝ, x t ∈ U) → (∀ t : ℝ, HasDerivAt x (A.F (x t)) t) →
      ∀ t : ℝ, HasDerivAt (m.π ∘ x) (B.F (m.π (x t))) t

/-- S2 (solutions on an open time interval staying in `U`): if `x(t) ∈ U` and
`x'(t) = F(x(t))` for every `t` of an open interval `J`, then `(m.π ∘ x)'(t) = G(m.π(x(t)))` for
every `t ∈ J`. -/
@[sa_shadow "DynBasic.mapSolutionOn" 2]
def S2 : Prop :=
  ∀ {A B : DynSys} {U : Set A.V} (m : SemiconjOn A B U) (J : Set ℝ), IsOpen J → Convex ℝ J →
    ∀ x : ℝ → A.V, (∀ t ∈ J, x t ∈ U) → (∀ t ∈ J, HasDerivAt x (A.F (x t)) t) →
      ∀ t ∈ J, HasDerivAt (m.π ∘ x) (B.F (m.π (x t))) t

@[sa_ref_forward "DynBasic.mapSolutionOn" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "DynBasic.mapSolutionOn" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "DynBasic.mapSolutionOn"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.DynBasic.MapSolutionOn

/-! ## `DynBasic.semiconjOnMapSolutionWithin` -/
namespace Alignment.Shadows.DynBasic.SemiconjOnMapSolutionWithin

/-! Blind text: "**Local semiconjugacies map solutions within a set of times `I` that stay in `U`
to solutions within `I`.** Design statement (DESIGN_NetworkEpiCore.md §D.3): "**Local version
`SemiconjOn U`.** The identity holds on an open set U, and solutions that stay in U are mapped.
This is needed for maps that divide by ψ(θ) or ψ'(θ).""

A local semiconjugacy on `U` is `m : SemiconjOn A B U` (map `m.π`). "A set of times `I`" is an
arbitrary `I : Set ℝ`: no convexity, openness, non-emptiness or `0 ∈ I` condition, since the text
states none. A solution *within* `I` that *stays in `U`* is a curve `x : ℝ → A.V` with `x t ∈ U`
and `HasDerivWithinAt x (A.F (x t)) I t` for every `t ∈ I`; being mapped "to a solution within
`I`" means `HasDerivWithinAt (m.π ∘ x) (B.F (m.π (x t))) I t` for every `t ∈ I`.

AMBIGUITY (the set `U`): the design quote says "an open set U"; the headline says local
semiconjugacies in general and `SemiconjOn` does not require openness (DataTypes). The shadow
quantifies over every `U : Set A.V`, which implies the open-`U` reading.
AMBIGUITY (bundled vs predicate): "local semiconjugacy" is read as the bundled `SemiconjOn A B U`
(the claim id names `SemiconjOn`); the predicate form `IsSemiconjOn A B U π` carries the same
content. One atomic implication. -/

/-- Intended statement: for every local semiconjugacy `m` on any `U`, every set of times `I` and
every curve `x` that stays in `U` and solves `A`'s equation within `I` at each `t ∈ I`, the curve
`m.π ∘ x` solves `B`'s equation within `I` at each `t ∈ I`. -/
@[sa_reference "DynBasic.semiconjOnMapSolutionWithin"]
def T : Prop :=
  ∀ {A B : DynSys} {U : Set A.V} (m : SemiconjOn A B U) (I : Set ℝ) (x : ℝ → A.V),
    (∀ t ∈ I, x t ∈ U) → (∀ t ∈ I, HasDerivWithinAt x (A.F (x t)) I t) →
      ∀ t ∈ I, HasDerivWithinAt (m.π ∘ x) (B.F (m.π (x t))) I t

/-- S1: the whole implication (a single atomic requirement): solutions within an arbitrary set of
times `I` that stay in `U` are mapped by `m.π` to solutions of `B` within `I`. -/
@[sa_shadow "DynBasic.semiconjOnMapSolutionWithin" 1]
def S1 : Prop :=
  ∀ {A B : DynSys} {U : Set A.V} (m : SemiconjOn A B U) (I : Set ℝ) (x : ℝ → A.V),
    (∀ t ∈ I, x t ∈ U) → (∀ t ∈ I, HasDerivWithinAt x (A.F (x t)) I t) →
      ∀ t ∈ I, HasDerivWithinAt (m.π ∘ x) (B.F (m.π (x t))) I t

@[sa_ref_forward "DynBasic.semiconjOnMapSolutionWithin" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "DynBasic.semiconjOnMapSolutionWithin"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.DynBasic.SemiconjOnMapSolutionWithin

/-! ## `DynBasic.hasFDerivAtRestrictIncl` -/
namespace Alignment.Shadows.DynBasic.HasFDerivAtRestrictIncl

/-! Blind text: "The chart `w ↦ p₀ + w` has derivative the inclusion `W →L[ℝ] V` at every point."

For every system `A`, base point `p₀ : A.V` and submodule `W`, the chart has Fréchet derivative
`W.subtypeL` (the inclusion `W →L[ℝ] A.V`) at every `w : ↥W`. "Has derivative" is `HasFDerivAt`.

The text identifies the chart both as the library's chart and by its formula, so two shadows:
* S1: about the trusted chart `A.restrictIncl p₀ W` (DataTypes: "The chart of the restriction,
  `w ↦ p₀ + w`");
* S2: about the map written out as in the text, `fun w : ↥W => p₀ + (w : A.V)`. -/

/-- The chart `w ↦ p₀ + w` of the affine subspace `p₀ + W`, written in primitive terms. -/
def chart (A : DynSys) (p₀ : A.V) (W : Submodule ℝ A.V) : ↥W → A.V :=
  fun w => p₀ + (w : A.V)

/-- Intended statement: the chart (the library's `restrictIncl`, which is `w ↦ p₀ + w`) has
derivative `W.subtypeL` at every point. -/
@[sa_reference "DynBasic.hasFDerivAtRestrictIncl"]
def T : Prop :=
  (∀ (A : DynSys) (p₀ : A.V) (W : Submodule ℝ A.V) (w : ↥W),
      HasFDerivAt (A.restrictIncl p₀ W) W.subtypeL w) ∧
  (∀ (A : DynSys) (p₀ : A.V) (W : Submodule ℝ A.V) (w : ↥W),
      HasFDerivAt (chart A p₀ W) W.subtypeL w)

/-- S1: the library chart `A.restrictIncl p₀ W` has derivative `W.subtypeL` at every `w`. -/
@[sa_shadow "DynBasic.hasFDerivAtRestrictIncl" 1]
def S1 : Prop :=
  ∀ (A : DynSys) (p₀ : A.V) (W : Submodule ℝ A.V) (w : ↥W),
    HasFDerivAt (A.restrictIncl p₀ W) W.subtypeL w

/-- S2: the map `w ↦ p₀ + w` of the text has derivative `W.subtypeL` at every `w`. -/
@[sa_shadow "DynBasic.hasFDerivAtRestrictIncl" 2]
def S2 : Prop :=
  ∀ (A : DynSys) (p₀ : A.V) (W : Submodule ℝ A.V) (w : ↥W),
    HasFDerivAt (chart A p₀ W) W.subtypeL w

@[sa_ref_forward "DynBasic.hasFDerivAtRestrictIncl" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "DynBasic.hasFDerivAtRestrictIncl" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "DynBasic.hasFDerivAtRestrictIncl"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.DynBasic.HasFDerivAtRestrictIncl

/-! ## `DynBasic.invariantIncl` -/
namespace Alignment.Shadows.DynBasic.InvariantIncl

/-! Blind text: "**The inclusion of an invariant subsystem is a semiconjugacy (a restriction).**
Design statement (DESIGN_NetworkEpiCore.md §D.3): "The inclusion of an invariant subsystem is a
restriction. "Model A is exact for initial conditions in W" is a morphism *out of* (W, F|_W).""

An invariant subsystem of `A` is an affine subspace `p₀ + W` (any `p₀ : A.V`, any submodule `W`)
to which `F` is tangent, `∀ w ∈ W, F(p₀ + w) ∈ W`; the subsystem is `(W, F|_W)` in the chart
`w ↦ p₀ + w`, with vector field `w ↦ F(p₀ + w)` (DataTypes, `DynSys.restrict`). Its inclusion is
the chart `w ↦ p₀ + w`. "Is a semiconjugacy" is the Prop-level notion `IsSemiconj` (a morphism
out of `(W, F|_W)` whose map is the inclusion); a data-level "there is a morphism" shadow could
not be checked non-vacuously.

AMBIGUITY: §D.3's category Dyn asks for C¹ morphisms; the headline says "is a semiconjugacy",
the library's notion (`IsSemiconj`: differentiable, `Dπ(u)·F(u) = G(π(u))`). The library notion
is used.

Two shadows, as for the chart:
* S1: with the library's restriction and chart, `IsSemiconj (A.restrict p₀ W hW) A
  (A.restrictIncl p₀ W)`;
* S2: with the subsystem `(W, F|_W)` and the inclusion `w ↦ p₀ + w` written out as the text
  describes them (`subsys`, `chart` below). -/

/-- The invariant subsystem `(W, F|_W)` of `A` at `p₀`, in the chart `w ↦ p₀ + w`: state space
`↥W`, vector field `w ↦ F(p₀ + w)` (which lies in `W` by tangency `hW`). Primitive terms. -/
noncomputable def subsys (A : DynSys) (p₀ : A.V) (W : Submodule ℝ A.V)
    (hW : ∀ w ∈ W, A.F (p₀ + w) ∈ W) : DynSys where
  V := ↥W
  F := fun w => ⟨A.F (p₀ + (w : A.V)), hW (w : A.V) w.2⟩

/-- The inclusion of the subsystem, `w ↦ p₀ + w`, as a map `(subsys A p₀ W hW).V → A.V`. -/
def chart (A : DynSys) (p₀ : A.V) (W : Submodule ℝ A.V)
    (hW : ∀ w ∈ W, A.F (p₀ + w) ∈ W) : (subsys A p₀ W hW).V → A.V :=
  fun (w : ↥W) => p₀ + (w : A.V)

/-- Intended statement: for every `A`, `p₀`, `W` with `F` tangent to `p₀ + W`, the inclusion of
the invariant subsystem into `A` is a semiconjugacy (library form and primitive form). -/
@[sa_reference "DynBasic.invariantIncl"]
def T : Prop :=
  (∀ (A : DynSys) (p₀ : A.V) (W : Submodule ℝ A.V) (hW : ∀ w ∈ W, A.F (p₀ + w) ∈ W),
      IsSemiconj (A.restrict p₀ W hW) A (A.restrictIncl p₀ W)) ∧
  (∀ (A : DynSys) (p₀ : A.V) (W : Submodule ℝ A.V) (hW : ∀ w ∈ W, A.F (p₀ + w) ∈ W),
      IsSemiconj (subsys A p₀ W hW) A (chart A p₀ W hW))

/-- S1: the library chart is a semiconjugacy from the library restriction to `A`. -/
@[sa_shadow "DynBasic.invariantIncl" 1]
def S1 : Prop :=
  ∀ (A : DynSys) (p₀ : A.V) (W : Submodule ℝ A.V) (hW : ∀ w ∈ W, A.F (p₀ + w) ∈ W),
    IsSemiconj (A.restrict p₀ W hW) A (A.restrictIncl p₀ W)

/-- S2: the inclusion `w ↦ p₀ + w` is a semiconjugacy from `(W, F|_W)` to `A`. -/
@[sa_shadow "DynBasic.invariantIncl" 2]
def S2 : Prop :=
  ∀ (A : DynSys) (p₀ : A.V) (W : Submodule ℝ A.V) (hW : ∀ w ∈ W, A.F (p₀ + w) ∈ W),
    IsSemiconj (subsys A p₀ W hW) A (chart A p₀ W hW)

@[sa_ref_forward "DynBasic.invariantIncl" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "DynBasic.invariantIncl" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "DynBasic.invariantIncl"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.DynBasic.InvariantIncl
