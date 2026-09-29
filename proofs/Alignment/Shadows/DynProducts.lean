import Alignment.Registry
import NetworkEpi.Dyn.Products
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Blind shadow sets for group `DynProducts` (module `NetworkEpi.Dyn.Products`)

Written blind. The author read only `SA-PASS_SKILL.md`, `Alignment/README.md`,
`Alignment/Example/ExampleShadows.lean`, `Alignment/DataTypes/DynProducts.md`, the entries
`DynProducts.prodIsLimit`, `DynProducts.instHasLimitPair`, `DynProducts.pointEq`,
`DynProducts.header.dynClosure` and `DynProducts.pointIsTerminal` of
`Alignment/claims_blind.yaml` (the first, the fourth and the fifth re-shadowed after the text
remediation), and DESIGN_NetworkEpiCore.md (§D.3, §D.7, §J–§L). No trusted
statement, definition body, checker or report was opened.

Vocabulary (from `DataTypes/DynProducts.md`): `DynSys` (a real normed space `V` with a field
`F : V → V`), its constructor `DynSys.mk`, morphisms `A ⟶ B` (= `Semiconj A B`, with underlying
map `Semiconj.π`) of the category instance `dynCategory`, composition `≫`, the object
`DynSys.point`, and the Mathlib limit notions `IsLimit`, `BinaryFan.mk`, `HasLimit`, `pair`,
`HasBinaryProducts`, `IsTerminal`, `HasTerminal`. `IsLimit` and `IsTerminal` are data, so they
are wrapped in `Nonempty`.

The objects the texts name by their data (`(V × W, F × G)`, `(Fin 0 → ℝ, 0)`) are written with
the constructor `DynSys.mk` in primitive terms, not through the operations under test
`DynSys.prod`, `prodFan`, `DynSys.point`, so that the shadows also test that those operations
build the named objects.
-/

open NEP CategoryTheory Limits

namespace Alignment.Shadows.DynProducts

/-- The system the texts write `(V × W, F × G)`: state space `A.V × B.V` (Mathlib's product
normed space) and vector field `(v, w) ↦ (F v, G w)`, in primitive terms. -/
noncomputable def ProdObj (A B : DynSys) : DynSys :=
  DynSys.mk (A.V × B.V) (fun p => (A.F p.1, B.F p.2))

/-- The zero-dimensional system the text writes `(Fin 0 → ℝ, 0)`, in primitive terms. -/
noncomputable def ZeroDimObj : DynSys :=
  DynSys.mk (Fin 0 → ℝ) 0

/-- An object of the design's category **Dyn** (DESIGN §D.3: "Objects of **Dyn** are (V, F):
V a finite-dimensional real normed space, F: V → V a C¹ vector field"). -/
def IsDynObj (A : DynSys) : Prop :=
  FiniteDimensional ℝ A.V ∧ ContDiff ℝ 1 A.F

/-- A morphism of the design's category **Dyn** (DESIGN §D.3: "Morphisms (V, F) → (W, G) are
C¹ maps π with Dπ(u)·F(u) = G(π(u)) (semiconjugacies)"): a semiconjugacy whose map is C¹. -/
def IsDynHom {A B : DynSys} (f : A ⟶ B) : Prop :=
  ContDiff ℝ 1 (Semiconj.π f)

end Alignment.Shadows.DynProducts

namespace Alignment.Shadows.DynProducts.ProdIsLimit

open Alignment.Shadows.DynProducts

/-! ### `DynProducts.prodIsLimit` (re-shadowed after the text remediation)

Blind text: "**`(V × W, F × G)` is the categorical product of `(V, F)` and `(W, G)` in
`DynSys`.** Design statement (DESIGN_NetworkEpiCore.md §D.3): "**Products.** Dyn has binary
products and a terminal object (Lean stretch L1b)"; §D.7: "L1b `NEP/Dyn/Products` | cartesian
structure | `HasBinaryProducts DynSys`, terminal object". [...] **`DynSys` has binary
products.** [...] **`DynSys` has a terminal object**, the zero-dimensional system
`(Fin 0 → ℝ, 0)`."

The text makes these requirements (one shadow each):

* S1, S2: for all systems `(V, F)`, `(W, G)`, the system `(V × W, F × G)` is their categorical
  product in `DynSys`.
  -- AMBIGUITY: "`(V × W, F × G)` is the categorical product". Read with the coordinate
  -- projections of `V × W` as the legs (S1, the usual meaning of writing a product as `V × W`),
  -- or as a statement about the object alone, with some legs (S2). S1 implies S2; both are kept
  -- so that a limit cone with other legs is told apart from a wrong apex.
* S3: `DynSys` has binary products (`HasBinaryProducts DynSys`, named in §D.7).
* S4, S5: `DynSys` has a terminal object (S4), and the zero-dimensional system
  `(Fin 0 → ℝ, 0)` is one (S5).

-- AMBIGUITY: the quoted design statement says "Dyn has binary products and a terminal object".
-- Every sentence of the claim outside the quotation says "in `DynSys`", and the quoted §D.7 row
-- gives the Lean form as `HasBinaryProducts DynSys`, so "Dyn" is read here as `DynSys`
-- (S3–S5). The reading with the design's finite-dimensional C¹ category **Dyn** is the subject
-- of the separate claim `DynProducts.header.dynClosure` ("Because Dyn is not a full
-- subcategory of `DynSys`, they do not by themselves imply that Dyn has these limits"), and is
-- shadowed there.
-/

/-- Intended statement: the conjunction of the requirements listed above. -/
@[sa_reference "DynProducts.prodIsLimit"]
def T : Prop :=
  (∀ A B : DynSys, ∃ (p₁ : ProdObj A B ⟶ A) (p₂ : ProdObj A B ⟶ B),
      Semiconj.π p₁ = Prod.fst ∧ Semiconj.π p₂ = Prod.snd ∧
        Nonempty (IsLimit (BinaryFan.mk p₁ p₂))) ∧
  (∀ A B : DynSys, ∃ (p₁ : ProdObj A B ⟶ A) (p₂ : ProdObj A B ⟶ B),
      Nonempty (IsLimit (BinaryFan.mk p₁ p₂))) ∧
  HasBinaryProducts DynSys ∧
  HasTerminal DynSys ∧
  Nonempty (IsTerminal ZeroDimObj)

/-- S1: for all `A = (V, F)` and `B = (W, G)`, the coordinate projections of `V × W` are
semiconjugacies `(V × W, F × G) ⟶ A` and `(V × W, F × G) ⟶ B`, and the binary fan they form
is a limit cone in `DynSys`. -/
@[sa_shadow "DynProducts.prodIsLimit" 1]
def S1 : Prop :=
  ∀ A B : DynSys, ∃ (p₁ : ProdObj A B ⟶ A) (p₂ : ProdObj A B ⟶ B),
    Semiconj.π p₁ = Prod.fst ∧ Semiconj.π p₂ = Prod.snd ∧
      Nonempty (IsLimit (BinaryFan.mk p₁ p₂))

/-- S2: for all `A = (V, F)` and `B = (W, G)`, the object `(V × W, F × G)` carries a binary fan
over `A`, `B` that is a limit cone in `DynSys` (the object-level reading). -/
@[sa_shadow "DynProducts.prodIsLimit" 2]
def S2 : Prop :=
  ∀ A B : DynSys, ∃ (p₁ : ProdObj A B ⟶ A) (p₂ : ProdObj A B ⟶ B),
    Nonempty (IsLimit (BinaryFan.mk p₁ p₂))

/-- S3: `DynSys` has binary products. -/
@[sa_shadow "DynProducts.prodIsLimit" 3]
def S3 : Prop := HasBinaryProducts DynSys

/-- S4: `DynSys` has a terminal object. -/
@[sa_shadow "DynProducts.prodIsLimit" 4]
def S4 : Prop := HasTerminal DynSys

/-- S5: the zero-dimensional system `(Fin 0 → ℝ, 0)` is a terminal object of `DynSys`. -/
@[sa_shadow "DynProducts.prodIsLimit" 5]
def S5 : Prop := Nonempty (IsTerminal ZeroDimObj)

@[sa_ref_forward "DynProducts.prodIsLimit" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "DynProducts.prodIsLimit" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1

@[sa_ref_forward "DynProducts.prodIsLimit" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2.1

@[sa_ref_forward "DynProducts.prodIsLimit" 4]
theorem ref_fwd4 : T → S4 := fun t => t.2.2.2.1

@[sa_ref_forward "DynProducts.prodIsLimit" 5]
theorem ref_fwd5 : T → S5 := fun t => t.2.2.2.2

@[sa_complete "DynProducts.prodIsLimit"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) : T :=
  ⟨s1, s2, s3, s4, s5⟩

end Alignment.Shadows.DynProducts.ProdIsLimit

namespace Alignment.Shadows.DynProducts.HeaderDynClosure

open Alignment.Shadows.DynProducts

/-! ### `DynProducts.header.dynClosure`

Blind text: "**Scope: `DynSys`, and the closure of the design's Dyn.** `prod_isLimit`,
`hasBinaryProducts`, `point_isTerminal` and `hasTerminal` are limits in `DynSys` (see
`NetworkEpi.Dyn.Basic`). Because Dyn is not a full subcategory of `DynSys`, they do not by
themselves imply that Dyn has these limits. The same constructions stay in the design's **Dyn**
(finite-dimensional, C¹): a product of finite-dimensional spaces with C¹ fields is
finite-dimensional with a C¹ field, the projections are C¹, the pairing of two C¹ maps is C¹,
`Fin 0 → ℝ` is finite-dimensional with the C¹ field 0, and the maps to it are C¹
(`dyn_prod_closed`, `dyn_point_closed`). Uniqueness of the factorisation is inherited from
`DynSys`, so Dyn has binary products and a terminal object, computed as in `DynSys`."

Dyn objects and morphisms are `IsDynObj` / `IsDynHom` (DESIGN §D.3: finite-dimensional state
space and C¹ field; C¹ semiconjugacy). "The same constructions" are the `DynSys` constructions
of this module: `DynSys.prod`, `prodFst`, `prodSnd`, `prodLift`, `DynSys.point`, `toPoint`, so
the shadows are stated with these operations.

The first two sentences describe other statements (the `DynSys` limits, claim
`DynProducts.prodIsLimit`, and the non-implication, claim `DynProducts.header.notFull`); they
make no requirement of their own here. The requirements are:

* S1, S2: for Dyn objects `A`, `B`, the product `A.prod B` is finite-dimensional (S1) and has a
  C¹ field (S2).
* S3, S4: the projections `prodFst A B`, `prodSnd A B` are C¹ (for Dyn objects `A`, `B`).
* S5: the pairing `prodLift f g` of two C¹ semiconjugacies between Dyn objects is C¹.
* S6, S7: the state space `Fin 0 → ℝ` of `DynSys.point` is finite-dimensional (S6) and its
  field is C¹ (S7).
* S8: the maps `toPoint A` to it (from Dyn objects `A`) are C¹.
* S9: Dyn has binary products computed as in `DynSys`: every pair of Dyn morphisms
  `f : C ⟶ A`, `g : C ⟶ B` between Dyn objects factors through `(prodFst A B, prodSnd A B)`
  by a unique Dyn morphism. (With S1–S4 this is the universal property of the product in Dyn.)
* S10: Dyn has a terminal object computed as in `DynSys`: every Dyn object has exactly one Dyn
  morphism to `DynSys.point`. (With S6, S7 this makes `DynSys.point` terminal in Dyn.)

-- AMBIGUITY: "the projections are C¹", "the pairing of two C¹ maps is C¹", "the maps to it are
-- C¹". Read inside the frame "The same constructions stay in the design's Dyn", i.e. for Dyn
-- objects (and, for the pairing, Dyn morphisms). An unconditional reading is stronger; the
-- Dyn reading is the one the sentence states.
-- AMBIGUITY: "`Fin 0 → ℝ` is finite-dimensional with the C¹ field 0": the construction that
-- stays in Dyn is `DynSys.point`; that its data are `(Fin 0 → ℝ, 0)` is the separate claim
-- `DynProducts.header.construction`. S6, S7 are stated on `DynSys.point`.
-- AMBIGUITY: "the maps to it": read as the construction `toPoint A`; that every morphism into
-- the point is C¹ follows from S10's uniqueness only among C¹ maps, so it is not added.
-- AMBIGUITY: "Dyn has binary products": uniqueness is among Dyn morphisms (Dyn is a
-- subcategory, not full), as a Dyn-internal universal property requires.
-/

/-- Intended statement: the conjunction of the requirements listed above. -/
@[sa_reference "DynProducts.header.dynClosure"]
def T : Prop :=
  (∀ A B : DynSys, IsDynObj A → IsDynObj B → FiniteDimensional ℝ (A.prod B).V) ∧
  (∀ A B : DynSys, IsDynObj A → IsDynObj B → ContDiff ℝ 1 (A.prod B).F) ∧
  (∀ A B : DynSys, IsDynObj A → IsDynObj B → IsDynHom (prodFst A B)) ∧
  (∀ A B : DynSys, IsDynObj A → IsDynObj B → IsDynHom (prodSnd A B)) ∧
  (∀ A B C : DynSys, IsDynObj A → IsDynObj B → IsDynObj C →
      ∀ (f : C ⟶ A) (g : C ⟶ B), IsDynHom f → IsDynHom g → IsDynHom (prodLift f g)) ∧
  FiniteDimensional ℝ DynSys.point.V ∧
  ContDiff ℝ 1 DynSys.point.F ∧
  (∀ A : DynSys, IsDynObj A → IsDynHom (toPoint A)) ∧
  (∀ A B : DynSys, IsDynObj A → IsDynObj B →
      ∀ C : DynSys, IsDynObj C → ∀ (f : C ⟶ A) (g : C ⟶ B), IsDynHom f → IsDynHom g →
        ∃ h : C ⟶ A.prod B, IsDynHom h ∧ h ≫ prodFst A B = f ∧ h ≫ prodSnd A B = g ∧
          ∀ h' : C ⟶ A.prod B, IsDynHom h' → h' ≫ prodFst A B = f → h' ≫ prodSnd A B = g →
            h' = h) ∧
  (∀ C : DynSys, IsDynObj C →
      ∃ h : C ⟶ DynSys.point, IsDynHom h ∧ ∀ h' : C ⟶ DynSys.point, IsDynHom h' → h' = h)

/-- S1: the product of two Dyn objects has a finite-dimensional state space. -/
@[sa_shadow "DynProducts.header.dynClosure" 1]
def S1 : Prop :=
  ∀ A B : DynSys, IsDynObj A → IsDynObj B → FiniteDimensional ℝ (A.prod B).V

/-- S2: the product of two Dyn objects has a C¹ vector field. -/
@[sa_shadow "DynProducts.header.dynClosure" 2]
def S2 : Prop :=
  ∀ A B : DynSys, IsDynObj A → IsDynObj B → ContDiff ℝ 1 (A.prod B).F

/-- S3: the first projection out of the product of two Dyn objects is C¹. -/
@[sa_shadow "DynProducts.header.dynClosure" 3]
def S3 : Prop :=
  ∀ A B : DynSys, IsDynObj A → IsDynObj B → IsDynHom (prodFst A B)

/-- S4: the second projection out of the product of two Dyn objects is C¹. -/
@[sa_shadow "DynProducts.header.dynClosure" 4]
def S4 : Prop :=
  ∀ A B : DynSys, IsDynObj A → IsDynObj B → IsDynHom (prodSnd A B)

/-- S5: the pairing of two C¹ semiconjugacies between Dyn objects is C¹. -/
@[sa_shadow "DynProducts.header.dynClosure" 5]
def S5 : Prop :=
  ∀ A B C : DynSys, IsDynObj A → IsDynObj B → IsDynObj C →
    ∀ (f : C ⟶ A) (g : C ⟶ B), IsDynHom f → IsDynHom g → IsDynHom (prodLift f g)

/-- S6: the state space of the zero-dimensional system is finite-dimensional. -/
@[sa_shadow "DynProducts.header.dynClosure" 6]
def S6 : Prop := FiniteDimensional ℝ DynSys.point.V

/-- S7: the vector field of the zero-dimensional system is C¹. -/
@[sa_shadow "DynProducts.header.dynClosure" 7]
def S7 : Prop := ContDiff ℝ 1 DynSys.point.F

/-- S8: the map from a Dyn object to the zero-dimensional system is C¹. -/
@[sa_shadow "DynProducts.header.dynClosure" 8]
def S8 : Prop := ∀ A : DynSys, IsDynObj A → IsDynHom (toPoint A)

/-- S9: every pair of Dyn morphisms out of a Dyn object into two Dyn objects factors through the
`DynSys` projections by a unique Dyn morphism (binary products in Dyn, computed as in
`DynSys`). -/
@[sa_shadow "DynProducts.header.dynClosure" 9]
def S9 : Prop :=
  ∀ A B : DynSys, IsDynObj A → IsDynObj B →
    ∀ C : DynSys, IsDynObj C → ∀ (f : C ⟶ A) (g : C ⟶ B), IsDynHom f → IsDynHom g →
      ∃ h : C ⟶ A.prod B, IsDynHom h ∧ h ≫ prodFst A B = f ∧ h ≫ prodSnd A B = g ∧
        ∀ h' : C ⟶ A.prod B, IsDynHom h' → h' ≫ prodFst A B = f → h' ≫ prodSnd A B = g →
          h' = h

/-- S10: every Dyn object has exactly one Dyn morphism to the zero-dimensional system (terminal
object in Dyn, computed as in `DynSys`). -/
@[sa_shadow "DynProducts.header.dynClosure" 10]
def S10 : Prop :=
  ∀ C : DynSys, IsDynObj C →
    ∃ h : C ⟶ DynSys.point, IsDynHom h ∧ ∀ h' : C ⟶ DynSys.point, IsDynHom h' → h' = h

@[sa_ref_forward "DynProducts.header.dynClosure" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "DynProducts.header.dynClosure" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1

@[sa_ref_forward "DynProducts.header.dynClosure" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2.1

@[sa_ref_forward "DynProducts.header.dynClosure" 4]
theorem ref_fwd4 : T → S4 := fun t => t.2.2.2.1

@[sa_ref_forward "DynProducts.header.dynClosure" 5]
theorem ref_fwd5 : T → S5 := fun t => t.2.2.2.2.1

@[sa_ref_forward "DynProducts.header.dynClosure" 6]
theorem ref_fwd6 : T → S6 := fun t => t.2.2.2.2.2.1

@[sa_ref_forward "DynProducts.header.dynClosure" 7]
theorem ref_fwd7 : T → S7 := fun t => t.2.2.2.2.2.2.1

@[sa_ref_forward "DynProducts.header.dynClosure" 8]
theorem ref_fwd8 : T → S8 := fun t => t.2.2.2.2.2.2.2.1

@[sa_ref_forward "DynProducts.header.dynClosure" 9]
theorem ref_fwd9 : T → S9 := fun t => t.2.2.2.2.2.2.2.2.1

@[sa_ref_forward "DynProducts.header.dynClosure" 10]
theorem ref_fwd10 : T → S10 := fun t => t.2.2.2.2.2.2.2.2.2

@[sa_complete "DynProducts.header.dynClosure"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) (s7 : S7)
    (s8 : S8) (s9 : S9) (s10 : S10) : T :=
  ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10⟩

end Alignment.Shadows.DynProducts.HeaderDynClosure

namespace Alignment.Shadows.DynProducts.PointIsTerminal

/-! ### `DynProducts.pointIsTerminal`

Blind text: "The zero-dimensional system is terminal."

"The zero-dimensional system" is `DynSys.point` (DataTypes: "The zero-dimensional system
`(Fin 0 → ℝ, 0)`"). "Terminal" is terminal in the category `DynSys` of this module, Mathlib's
`IsTerminal`, which is data, so it is wrapped in `Nonempty`.
-- AMBIGUITY: "The zero-dimensional system". The definite article names one object, read as
-- `DynSys.point`; the reading "every zero-dimensional system is terminal" is not taken. That
-- `DynSys.point` is zero-dimensional (its data are `(Fin 0 → ℝ, 0)`, one state) is the subject
-- of the claims `DynProducts.header.construction` and `DynProducts.pointEq`, not a requirement
-- of this sentence. A single atomic requirement. -/

/-- Intended statement: `DynSys.point` is a terminal object of `DynSys`. -/
@[sa_reference "DynProducts.pointIsTerminal"]
def T : Prop := Nonempty (IsTerminal DynSys.point)

/-- S1: the whole statement (a single atomic requirement). -/
@[sa_shadow "DynProducts.pointIsTerminal" 1]
def S1 : Prop := Nonempty (IsTerminal DynSys.point)

@[sa_ref_forward "DynProducts.pointIsTerminal" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "DynProducts.pointIsTerminal"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.DynProducts.PointIsTerminal


namespace Alignment.Shadows.DynProducts.InstHasLimitPair

/-! ### `DynProducts.instHasLimitPair`

Blind text: "Every pair of objects of `DynSys` has a product."

"Has a product" is Mathlib's `HasLimit (pair A B)` (the diagram `pair A B` over the discrete
two-object category; `HasBinaryProduct A B` abbreviates it). "Every pair" is read over all
`A B : DynSys`, including `A = B`. The statement is a single atomic requirement. -/

/-- Intended statement: every two objects of `DynSys` have a binary product. -/
@[sa_reference "DynProducts.instHasLimitPair"]
def T : Prop := ∀ A B : DynSys, HasLimit (pair A B)

/-- S1: the whole statement (a single atomic requirement). -/
@[sa_shadow "DynProducts.instHasLimitPair" 1]
def S1 : Prop := ∀ A B : DynSys, HasLimit (pair A B)

@[sa_ref_forward "DynProducts.instHasLimitPair" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "DynProducts.instHasLimitPair"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.DynProducts.InstHasLimitPair

namespace Alignment.Shadows.DynProducts.PointEq

/-! ### `DynProducts.pointEq`

Blind text: "The state space of `DynSys.point` has exactly one element."

"Exactly one element" is `∃ x, ∀ y, y = x` on `DynSys.point.V`. It splits into "at least one"
and "at most one". The "at least one" half holds for every `DynSys` whatever the
implementation (a normed space contains `0`), so it cannot be falsified by a wrong
implementation and is not a shadow of its own. The completeness certificate uses `0` to recover
it. The shadow is the "at most one" half: any two states of `DynSys.point` are equal. -/

/-- Intended statement: the state space of `DynSys.point` has exactly one element. -/
@[sa_reference "DynProducts.pointEq"]
def T : Prop := ∃ x : DynSys.point.V, ∀ y : DynSys.point.V, y = x

/-- S1: any two states of `DynSys.point` are equal (at most one element). -/
@[sa_shadow "DynProducts.pointEq" 1]
def S1 : Prop := ∀ x y : DynSys.point.V, x = y

@[sa_ref_forward "DynProducts.pointEq" 1]
theorem ref_fwd1 : T → S1 := by
  rintro ⟨z, hz⟩ x y
  exact (hz x).trans (hz y).symm

@[sa_complete "DynProducts.pointEq"]
theorem complete (s1 : S1) : T := ⟨0, fun y => s1 y 0⟩

end Alignment.Shadows.DynProducts.PointEq
