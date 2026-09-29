import NetworkEpi.Dyn.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# L1b: binary products and the terminal object of `DynSys`

DESIGN_NetworkEpiCore.md §D.3: "**Products.** Dyn has binary products and a terminal object
(Lean stretch L1b)"; §D.7 table: "L1b `NEP/Dyn/Products` | cartesian structure |
`HasBinaryProducts DynSys`, terminal object".

The product of `(V, F)` and `(W, G)` is `(V × W, F × G)` with the two coordinate projections;
the terminal object is the zero-dimensional system `(Fin 0 → ℝ, 0)`.

**Scope: `DynSys`, and the closure of the design's Dyn.** `prod_isLimit`, `hasBinaryProducts`,
`point_isTerminal` and `hasTerminal` are limits in `DynSys` (see `NetworkEpi.Dyn.Basic`). Because
Dyn is not a full subcategory of `DynSys`, they do not by themselves imply that Dyn has these
limits. The same constructions stay in the design's **Dyn** (finite-dimensional, C¹): a product of
finite-dimensional spaces with C¹ fields is finite-dimensional with a C¹ field, the projections
are C¹, the pairing of two C¹ maps is C¹, `Fin 0 → ℝ` is finite-dimensional with the C¹ field 0,
and the maps to it are C¹ (`dyn_prod_closed`, `dyn_point_closed`). Uniqueness of the factorisation
is inherited from `DynSys`, so Dyn has binary products and a terminal object, computed as in
`DynSys`.
-/

open CategoryTheory Limits

namespace NEP

/-- The product system `(V × W, (v, w) ↦ (F v, G w))`. -/
noncomputable def DynSys.prod (A B : DynSys) : DynSys where
  V := A.V × B.V
  F u := (A.F u.1, B.F u.2)

/-- The first projection `(V × W, F × G) → (V, F)`. -/
noncomputable def prodFst (A B : DynSys) : A.prod B ⟶ A :=
  (⟨Prod.fst, differentiable_fst, fun u => by
    show fderiv ℝ (Prod.fst : A.V × B.V → A.V) u (A.F u.1, B.F u.2) = A.F u.1
    rw [fderiv_fst]
    rfl⟩ : Semiconj (A.prod B) A)

/-- The second projection `(V × W, F × G) → (W, G)`. -/
noncomputable def prodSnd (A B : DynSys) : A.prod B ⟶ B :=
  (⟨Prod.snd, differentiable_snd, fun u => by
    show fderiv ℝ (Prod.snd : A.V × B.V → B.V) u (A.F u.1, B.F u.2) = B.F u.2
    rw [fderiv_snd]
    rfl⟩ : Semiconj (A.prod B) B)

/-- The pairing `u ↦ (f u, g u)` of two semiconjugacies out of the same system. -/
noncomputable def prodLift {A B C : DynSys} (f : C ⟶ A) (g : C ⟶ B) : C ⟶ A.prod B :=
  let f' : Semiconj C A := f
  let g' : Semiconj C B := g
  (⟨fun u => (f'.π u, g'.π u), f'.diff.prodMk g'.diff, fun u => by
    show fderiv ℝ (fun u => (f'.π u, g'.π u)) u (C.F u) = (A.F (f'.π u), B.F (g'.π u))
    rw [DifferentiableAt.fderiv_prodMk (f'.diff u) (g'.diff u)]
    simp [f'.comm, g'.comm]⟩ : Semiconj C (A.prod B))

/-- The binary fan `(V, F) ← (V × W, F × G) → (W, G)`. -/
noncomputable def prodFan (A B : DynSys) : BinaryFan A B := BinaryFan.mk (prodFst A B) (prodSnd A B)

/-- The product fan is a limit cone. -/
noncomputable def prodFanIsLimit (A B : DynSys) : IsLimit (prodFan A B) :=
  BinaryFan.IsLimit.mk _ (fun f g => prodLift f g) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun f g m h₁ h₂ => by
      apply Semiconj.ext
      funext u
      have e₁ := congrFun (congrArg Semiconj.π h₁) u
      have e₂ := congrFun (congrArg Semiconj.π h₂) u
      exact Prod.ext e₁ e₂)

/-- **`(V × W, F × G)` is the categorical product of `(V, F)` and `(W, G)` in `DynSys`.**

Design statement (DESIGN_NetworkEpiCore.md §D.3): "**Products.** Dyn has binary products and a
terminal object (Lean stretch L1b)"; §D.7: "L1b `NEP/Dyn/Products` | cartesian structure |
`HasBinaryProducts DynSys`, terminal object".

Lean statement: for all objects `A = (V, F)` and `B = (W, G)` of `DynSys`, the binary fan with
apex `(V × W, (v, w) ↦ (F v, G w))` and legs the coordinate projections is a limit cone: every
pair of semiconjugacies `f : C → A`, `g : C → B` factors as `u ↦ (f u, g u)` through the
projections, uniquely. -/
theorem prod_isLimit (A B : DynSys) : Nonempty (IsLimit (prodFan A B)) :=
  ⟨prodFanIsLimit A B⟩

/-- Every pair of objects of `DynSys` has a product. -/
instance (A B : DynSys) : HasLimit (pair A B) :=
  HasLimit.mk ⟨prodFan A B, prodFanIsLimit A B⟩

/-- **`DynSys` has binary products.**

Design statement (DESIGN_NetworkEpiCore.md §D.3): "**Products.** Dyn has binary products and a
terminal object (Lean stretch L1b)".

Lean statement: the category `DynSys` (objects: real normed spaces with vector fields; morphisms:
differentiable semiconjugacies) has all binary products (`HasBinaryProducts DynSys`).

Scope: proved for `DynSys`. That the design's Dyn (finite-dimensional, C¹) is closed under these
products is `dyn_prod_closed`. -/
theorem hasBinaryProducts : HasBinaryProducts DynSys :=
  hasBinaryProducts_of_hasLimit_pair DynSys

/-- The zero-dimensional system `(Fin 0 → ℝ, 0)`. -/
noncomputable def DynSys.point : DynSys where
  V := Fin 0 → ℝ
  F _ := 0

/-- The state space of `DynSys.point` has exactly one element. -/
theorem point_eq (a b : DynSys.point.V) : a = b :=
  funext fun i : Fin 0 => i.elim0

/-- The unique semiconjugacy into the zero-dimensional system. -/
noncomputable def toPoint (A : DynSys) : A ⟶ DynSys.point :=
  (⟨fun _ => 0, differentiable_const _, fun _ => point_eq _ _⟩ :
    Semiconj A DynSys.point)

/-- The zero-dimensional system is terminal. -/
noncomputable def pointIsTerminal : IsTerminal DynSys.point :=
  IsTerminal.ofUniqueHom toPoint (fun A m => by
    apply Semiconj.ext
    funext u
    exact point_eq _ _)

/-- **`DynSys` has a terminal object**, the zero-dimensional system `(Fin 0 → ℝ, 0)`.

Design statement (DESIGN_NetworkEpiCore.md §D.3): "**Products.** Dyn has binary products and a
terminal object (Lean stretch L1b)".

Lean statement: the zero-dimensional system `(Fin 0 → ℝ, 0)` is a terminal object of `DynSys`
(from every object there is exactly one semiconjugacy to it), so `HasTerminal DynSys`.

Scope: proved for `DynSys`; that the terminal object and the maps to it are also in the design's
Dyn is `dyn_point_closed`, and the identification of the terminal object is `point_isTerminal`. -/
theorem hasTerminal : HasTerminal DynSys :=
  pointIsTerminal.hasTerminal

/-- **The zero-dimensional system `(Fin 0 → ℝ, 0)` is a terminal object of `DynSys`.**

Design statement (DESIGN_NetworkEpiCore.md §D.3): "**Products.** Dyn has binary products and a
terminal object (Lean stretch L1b)".

Lean statement: `DynSys.point = (Fin 0 → ℝ, 0)` is a terminal object of `DynSys`
(`Nonempty (IsTerminal DynSys.point)`): from every object there is exactly one semiconjugacy
to it. -/
theorem point_isTerminal : Nonempty (IsTerminal DynSys.point) :=
  ⟨pointIsTerminal⟩

/-- **The design's Dyn is closed under the binary products of `DynSys`.**

Design statement (DESIGN_NetworkEpiCore.md §D.3): "Objects of **Dyn** are (V, F): V a
finite-dimensional real normed space, F: V → V a C¹ vector field. Morphisms (V, F) → (W, G) are C¹
maps π with Dπ(u)·F(u) = G(π(u)) (semiconjugacies)." [...] "**Products.** Dyn has binary products
and a terminal object (Lean stretch L1b)".

Lean statement: let `A = (V, F)` and `B = (W, G)` be objects of `DynSys` with `V`, `W`
finite-dimensional and `F`, `G` of class C¹. Then the product system `(V × W, F × G)` has a
finite-dimensional state space and a C¹ vector field, the two projections are C¹, and for every
object `C` and all semiconjugacies `f : C → A`, `g : C → B` whose maps are C¹, the pairing
`u ↦ (f u, g u)` (the unique factorisation of `prod_isLimit`) is C¹. So a pair of objects of Dyn
has a product in Dyn, computed as in `DynSys`. -/
theorem dyn_prod_closed (A B : DynSys) [FiniteDimensional ℝ A.V] [FiniteDimensional ℝ B.V]
    (hA : ContDiff ℝ 1 A.F) (hB : ContDiff ℝ 1 B.F) :
    FiniteDimensional ℝ (A.prod B).V ∧ ContDiff ℝ 1 (A.prod B).F ∧
      ContDiff ℝ 1 (prodFst A B : Semiconj (A.prod B) A).π ∧
      ContDiff ℝ 1 (prodSnd A B : Semiconj (A.prod B) B).π ∧
      ∀ {C : DynSys} (f : C ⟶ A) (g : C ⟶ B), ContDiff ℝ 1 (f : Semiconj C A).π →
        ContDiff ℝ 1 (g : Semiconj C B).π →
        ContDiff ℝ 1 (prodLift f g : Semiconj C (A.prod B)).π := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show FiniteDimensional ℝ (A.V × B.V)
    infer_instance
  · show ContDiff ℝ 1 (fun u : A.V × B.V => (A.F u.1, B.F u.2))
    exact (hA.comp contDiff_fst).prodMk (hB.comp contDiff_snd)
  · exact contDiff_fst
  · exact contDiff_snd
  · intro C f g hf hg
    exact hf.prodMk hg

/-- **The terminal object of `DynSys` and the maps to it lie in the design's Dyn.**

Design statement (DESIGN_NetworkEpiCore.md §D.3): "**Products.** Dyn has binary products and a
terminal object (Lean stretch L1b)".

Lean statement: the state space `Fin 0 → ℝ` of `DynSys.point` is finite-dimensional, its vector
field `0` is C¹, and for every object `A` the unique semiconjugacy `A → DynSys.point` is C¹. -/
theorem dyn_point_closed :
    FiniteDimensional ℝ DynSys.point.V ∧ ContDiff ℝ 1 DynSys.point.F ∧
      ∀ A : DynSys, ContDiff ℝ 1 (toPoint A : Semiconj A DynSys.point).π := by
  refine ⟨?_, ?_, fun A => ?_⟩
  · show FiniteDimensional ℝ (Fin 0 → ℝ)
    infer_instance
  · exact contDiff_const
  · exact contDiff_const

/-- **The design's Dyn is closed under the binary products of `DynSys` (pairing of Dyn maps).**

Design statement (DESIGN_NetworkEpiCore.md §D.3): "Objects of **Dyn** are (V, F): V a
finite-dimensional real normed space, F: V → V a C¹ vector field. Morphisms (V, F) → (W, G) are C¹
maps π with Dπ(u)·F(u) = G(π(u)) (semiconjugacies)." [...] "**Products.** Dyn has binary products
and a terminal object (Lean stretch L1b)".

Lean statement: as `dyn_prod_closed`, with the pairing clause stated for Dyn objects only: let
`A`, `B` be objects of `DynSys` with finite-dimensional state spaces and C¹ vector fields. Then
`A × B` has a finite-dimensional state space and a C¹ field, the projections are C¹, and for every
object `C` with a finite-dimensional state space and a C¹ field and all semiconjugacies
`f : C → A`, `g : C → B` with C¹ maps, the pairing `u ↦ (f u, g u)` is C¹. (`dyn_prod_closed`
states the pairing clause for every `C`.) -/
theorem dyn_prod_closed_of_dyn (A B : DynSys) [FiniteDimensional ℝ A.V]
    [FiniteDimensional ℝ B.V] (hA : ContDiff ℝ 1 A.F) (hB : ContDiff ℝ 1 B.F) :
    FiniteDimensional ℝ (A.prod B).V ∧ ContDiff ℝ 1 (A.prod B).F ∧
      ContDiff ℝ 1 (prodFst A B : Semiconj (A.prod B) A).π ∧
      ContDiff ℝ 1 (prodSnd A B : Semiconj (A.prod B) B).π ∧
      ∀ {C : DynSys}, (FiniteDimensional ℝ C.V ∧ ContDiff ℝ 1 C.F) →
        ∀ (f : C ⟶ A) (g : C ⟶ B), ContDiff ℝ 1 (f : Semiconj C A).π →
        ContDiff ℝ 1 (g : Semiconj C B).π →
        ContDiff ℝ 1 (prodLift f g : Semiconj C (A.prod B)).π := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := dyn_prod_closed A B hA hB
  exact ⟨h1, h2, h3, h4, fun _ f g hf hg => h5 f g hf hg⟩

/-- **The terminal object of `DynSys` and the maps to it from Dyn objects lie in the design's
Dyn.**

Design statement (DESIGN_NetworkEpiCore.md §D.3): "**Products.** Dyn has binary products and a
terminal object (Lean stretch L1b)".

Lean statement: as `dyn_point_closed`, with the last clause stated for Dyn objects only: the state
space `Fin 0 → ℝ` of `DynSys.point` is finite-dimensional, its vector field `0` is C¹, and for
every object `A` with a finite-dimensional state space and a C¹ field the unique semiconjugacy
`A → DynSys.point` is C¹. (`dyn_point_closed` states the last clause for every `A`.) -/
theorem dyn_point_closed_of_dyn :
    FiniteDimensional ℝ DynSys.point.V ∧ ContDiff ℝ 1 DynSys.point.F ∧
      ∀ A : DynSys, (FiniteDimensional ℝ A.V ∧ ContDiff ℝ 1 A.F) →
        ContDiff ℝ 1 (toPoint A : Semiconj A DynSys.point).π := by
  obtain ⟨h1, h2, h3⟩ := dyn_point_closed
  exact ⟨h1, h2, fun A _ => h3 A⟩

/-- **The design's Dyn has binary products** (universal property among Dyn objects and Dyn maps).

Design statement (DESIGN_NetworkEpiCore.md §D.3): "Objects of **Dyn** are (V, F): V a
finite-dimensional real normed space, F: V → V a C¹ vector field. Morphisms (V, F) → (W, G) are C¹
maps π with Dπ(u)·F(u) = G(π(u)) (semiconjugacies)." [...] "**Products.** Dyn has binary products
and a terminal object (Lean stretch L1b)".

Lean statement: for all objects `A`, `B` of `DynSys` whose state spaces are finite-dimensional
and whose vector fields are C¹, there are an object `P` (finite-dimensional, C¹ field) and
semiconjugacies `p₁ : P → A`, `p₂ : P → B` with C¹ maps such that, for every object `C`
(finite-dimensional, C¹ field) and all semiconjugacies `f : C → A`, `g : C → B` with C¹ maps,
there is a semiconjugacy `h : C → P` with C¹ map, `h ≫ p₁ = f` and `h ≫ p₂ = g`, and every
semiconjugacy `h'` with C¹ map and the same two properties equals `h`. (`P` is the product
system `(V × W, F × G)` and `p₁`, `p₂` are the coordinate projections.) -/
theorem dyn_isProduct (A B : DynSys) (hA : FiniteDimensional ℝ A.V ∧ ContDiff ℝ 1 A.F)
    (hB : FiniteDimensional ℝ B.V ∧ ContDiff ℝ 1 B.F) :
    ∃ (P : DynSys) (p₁ : P ⟶ A) (p₂ : P ⟶ B),
      (FiniteDimensional ℝ P.V ∧ ContDiff ℝ 1 P.F) ∧ ContDiff ℝ 1 (Semiconj.π p₁) ∧
        ContDiff ℝ 1 (Semiconj.π p₂) ∧
        ∀ C : DynSys, (FiniteDimensional ℝ C.V ∧ ContDiff ℝ 1 C.F) →
          ∀ (f : C ⟶ A) (g : C ⟶ B), ContDiff ℝ 1 (Semiconj.π f) → ContDiff ℝ 1 (Semiconj.π g) →
            ∃ h : C ⟶ P, ContDiff ℝ 1 (Semiconj.π h) ∧ h ≫ p₁ = f ∧ h ≫ p₂ = g ∧
              ∀ h' : C ⟶ P, ContDiff ℝ 1 (Semiconj.π h') → h' ≫ p₁ = f → h' ≫ p₂ = g →
                h' = h := by
  obtain ⟨hAf, hAc⟩ := hA
  obtain ⟨hBf, hBc⟩ := hB
  obtain ⟨h1, h2, h3, h4, h5⟩ := dyn_prod_closed A B hAc hBc
  refine ⟨A.prod B, prodFst A B, prodSnd A B, ⟨h1, h2⟩, h3, h4, ?_⟩
  intro C _ f g hf hg
  refine ⟨prodLift f g, h5 f g hf hg, rfl, rfl, ?_⟩
  intro h' _ e₁ e₂
  apply Semiconj.ext
  funext u
  exact Prod.ext (congrFun (congrArg Semiconj.π e₁) u) (congrFun (congrArg Semiconj.π e₂) u)

/-- **The design's Dyn has a terminal object** (universal property among Dyn objects and Dyn
maps).

Design statement (DESIGN_NetworkEpiCore.md §D.3): "Objects of **Dyn** are (V, F): V a
finite-dimensional real normed space, F: V → V a C¹ vector field. Morphisms (V, F) → (W, G) are C¹
maps π with Dπ(u)·F(u) = G(π(u)) (semiconjugacies)." [...] "**Products.** Dyn has binary products
and a terminal object (Lean stretch L1b)".

Lean statement: there is an object `P` of `DynSys` (finite-dimensional, C¹ field; namely
`(Fin 0 → ℝ, 0)`) such that for every object `C` (finite-dimensional, C¹ field) there is a
semiconjugacy `h : C → P` with C¹ map, and every semiconjugacy `C → P` with C¹ map equals `h`. -/
theorem dyn_isTerminal :
    ∃ P : DynSys, (FiniteDimensional ℝ P.V ∧ ContDiff ℝ 1 P.F) ∧
      ∀ C : DynSys, (FiniteDimensional ℝ C.V ∧ ContDiff ℝ 1 C.F) →
        ∃ h : C ⟶ P, ContDiff ℝ 1 (Semiconj.π h) ∧
          ∀ h' : C ⟶ P, ContDiff ℝ 1 (Semiconj.π h') → h' = h := by
  obtain ⟨h1, h2, h3⟩ := dyn_point_closed
  refine ⟨DynSys.point, ⟨h1, h2⟩, fun C _ => ⟨toPoint C, h3 C, fun h' _ => ?_⟩⟩
  apply Semiconj.ext
  funext u
  exact point_eq _ _

end NEP
