import Alignment.Registry
import Alignment.Shadows.DynProducts

/-!
# Checks for group `DynProducts` (module `NetworkEpi.Dyn.Products`)

Checker author (non-blind). Registrations and structural forward/backward checkers for `DynProducts.prodIsLimit`, `DynProducts.header.dynClosure`,
`DynProducts.pointIsTerminal`, `DynProducts.instHasLimitPair` and `DynProducts.pointEq`.

No bridges. The shadows' objects `ProdObj A B` and `ZeroDimObj` are definitionally equal to the
implementation's `DynSys.prod A B` and `DynSys.point`. `IsDynObj` and `IsDynHom` are
definitionally the implementation's hypotheses `FiniteDimensional ℝ A.V ∧ ContDiff ℝ 1 A.F` and
`ContDiff ℝ 1 (Semiconj.π f)`.
-/

open NEP CategoryTheory Limits

namespace Alignment.Checks.DynProducts

/-- Two semiconjugacies with the same underlying map are equal. This is structural: it
transports the structure-eta identity `p = ⟨p.π, p.diff, p.comm⟩` along `e`. The proof fields
are arguments of the data constructor, and proof irrelevance closes the rest definitionally. -/
theorem hom_eq_of_pi_eq {X Y : DynSys} (p q : X ⟶ Y) (e : Semiconj.π p = Semiconj.π q) :
    p = q :=
  @Eq.rec _ (Semiconj.π p)
    (fun f e' => p = (Semiconj.mk f (e' ▸ p.diff) (e' ▸ p.comm) : Semiconj X Y))
    (rfl : p = (Semiconj.mk p.π p.diff p.comm : Semiconj X Y)) (Semiconj.π q) e

/-- A morphism into `A.prod B` is determined by its two composites with the projections. This
is structural: `congrArg`/`congr` on the underlying maps, then function and pair eta
(definitional), then `hom_eq_of_pi_eq`. -/
theorem eq_prodLift {A B C : DynSys} (f : C ⟶ A) (g : C ⟶ B) (h' : C ⟶ A.prod B)
    (e₁ : h' ≫ prodFst A B = f) (e₂ : h' ≫ prodSnd A B = g) : h' = prodLift f g :=
  hom_eq_of_pi_eq h' (prodLift f g)
    (congr (congrArg (fun (a : C.V → A.V) (b : C.V → B.V) (u : C.V) => (a u, b u))
        (congrArg Semiconj.π e₁)) (congrArg Semiconj.π e₂) :
      (fun u => ((h' ≫ prodFst A B).π u, (h' ≫ prodSnd A B).π u)) =
        fun u => ((f : Semiconj C A).π u, (g : Semiconj C B).π u))

/-- Every morphism into `DynSys.point` is `toPoint`. This is structural: its state space
`Fin 0 → ℝ` has no coordinates (`Fin.elim0`, elimination of the empty type `Fin 0`). -/
theorem eq_toPoint {C : DynSys} (h' : C ⟶ DynSys.point) : h' = toPoint C :=
  hom_eq_of_pi_eq h' (toPoint C) (funext fun _ => funext fun i : Fin 0 => Fin.elim0 i)

end Alignment.Checks.DynProducts

namespace Alignment.Shadows.DynProducts.ProdIsLimit

open Alignment.Shadows.DynProducts Alignment.Checks.DynProducts

sa_claim "DynProducts.prodIsLimit" group "DynProducts" required
  text "**`(V × W, F × G)` is the categorical product of `(V, F)` and `(W, G)` in `DynSys`.** Design statement (DESIGN_NetworkEpiCore.md §D.3): \"**Products.** Dyn has binary products and a terminal object (Lean stretch L1b)\"; §D.7: \"L1b `NEP/Dyn/Products` | cartesian structure | `HasBinaryProducts DynSys`, terminal object\". [...] **`DynSys` has binary products.** [...] **`DynSys` has a terminal object**, the zero-dimensional system `(Fin 0 → ℝ, 0)`."
  impl NEP.prod_isLimit NEP.hasBinaryProducts NEP.hasTerminal NEP.point_isTerminal

@[sa_forward "DynProducts.prodIsLimit" 1]
theorem fwd1 (h : sa_impl% "DynProducts.prodIsLimit") : S1 :=
  fun A B => ⟨prodFst A B, prodSnd A B, rfl, rfl, h.1 A B⟩

@[sa_forward "DynProducts.prodIsLimit" 2]
theorem fwd2 (h : sa_impl% "DynProducts.prodIsLimit") : S2 :=
  fun A B => ⟨prodFst A B, prodSnd A B, h.1 A B⟩

@[sa_forward "DynProducts.prodIsLimit" 3]
theorem fwd3 (h : sa_impl% "DynProducts.prodIsLimit") : S3 := h.2.1

@[sa_forward "DynProducts.prodIsLimit" 4]
theorem fwd4 (h : sa_impl% "DynProducts.prodIsLimit") : S4 := h.2.2.1

@[sa_forward "DynProducts.prodIsLimit" 5]
theorem fwd5 (h : sa_impl% "DynProducts.prodIsLimit") : S5 := h.2.2.2

/-- Backward. `prod_isLimit` from S1: the legs `p₁`, `p₂` S1 provides have the maps `Prod.fst`,
`Prod.snd`, so they are `prodFst`, `prodSnd` (`hom_eq_of_pi_eq`, structural), and S1's limit
cone is `prodFan A B` after rewriting. The other three conjuncts are S3, S4, S5 (`ZeroDimObj`
is definitionally `DynSys.point`). -/
@[sa_backward "DynProducts.prodIsLimit"]
theorem bwd (s1 : S1) (_s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) :
    sa_impl% "DynProducts.prodIsLimit" := by
  refine ⟨fun A B => ?_, s3, s4, s5⟩
  obtain ⟨p₁, p₂, e₁, e₂, hl⟩ := s1 A B
  have q₁ : p₁ = prodFst A B := hom_eq_of_pi_eq p₁ (prodFst A B) e₁
  have q₂ : p₂ = prodSnd A B := hom_eq_of_pi_eq p₂ (prodSnd A B) e₂
  rw [q₁, q₂] at hl
  exact hl

end Alignment.Shadows.DynProducts.ProdIsLimit

namespace Alignment.Shadows.DynProducts.HeaderDynClosure

open Alignment.Shadows.DynProducts Alignment.Checks.DynProducts

sa_claim "DynProducts.header.dynClosure" group "DynProducts" required
  text "**Scope: `DynSys`, and the closure of the design's Dyn.** `prod_isLimit`, `hasBinaryProducts`, `point_isTerminal` and `hasTerminal` are limits in `DynSys` (see `NetworkEpi.Dyn.Basic`). Because Dyn is not a full subcategory of `DynSys`, they do not by themselves imply that Dyn has these limits. The same constructions stay in the design's **Dyn** (finite-dimensional, C¹): a product of finite-dimensional spaces with C¹ fields is finite-dimensional with a C¹ field, the projections are C¹, the pairing of two C¹ maps is C¹, `Fin 0 → ℝ` is finite-dimensional with the C¹ field 0, and the maps to it are C¹ (`dyn_prod_closed`, `dyn_point_closed`). Uniqueness of the factorisation is inherited from `DynSys`, so Dyn has binary products and a terminal object, computed as in `DynSys`."
  impl NEP.dyn_prod_closed_of_dyn NEP.dyn_point_closed_of_dyn NEP.dyn_isProduct NEP.dyn_isTerminal

@[sa_forward "DynProducts.header.dynClosure" 1]
theorem fwd1 (h : sa_impl% "DynProducts.header.dynClosure") : S1 := by
  intro A B hA hB
  have p := h.1
  exact (@p A B hA.1 hB.1 hA.2 hB.2).1

@[sa_forward "DynProducts.header.dynClosure" 2]
theorem fwd2 (h : sa_impl% "DynProducts.header.dynClosure") : S2 := by
  intro A B hA hB
  have p := h.1
  exact (@p A B hA.1 hB.1 hA.2 hB.2).2.1

@[sa_forward "DynProducts.header.dynClosure" 3]
theorem fwd3 (h : sa_impl% "DynProducts.header.dynClosure") : S3 := by
  intro A B hA hB
  have p := h.1
  exact (@p A B hA.1 hB.1 hA.2 hB.2).2.2.1

@[sa_forward "DynProducts.header.dynClosure" 4]
theorem fwd4 (h : sa_impl% "DynProducts.header.dynClosure") : S4 := by
  intro A B hA hB
  have p := h.1
  exact (@p A B hA.1 hB.1 hA.2 hB.2).2.2.2.1

@[sa_forward "DynProducts.header.dynClosure" 5]
theorem fwd5 (h : sa_impl% "DynProducts.header.dynClosure") : S5 := by
  intro A B C hA hB hC f g hf hg
  have p := h.1
  exact (@p A B hA.1 hB.1 hA.2 hB.2).2.2.2.2 hC f g hf hg

@[sa_forward "DynProducts.header.dynClosure" 6]
theorem fwd6 (h : sa_impl% "DynProducts.header.dynClosure") : S6 := h.2.1.1

@[sa_forward "DynProducts.header.dynClosure" 7]
theorem fwd7 (h : sa_impl% "DynProducts.header.dynClosure") : S7 := h.2.1.2.1

@[sa_forward "DynProducts.header.dynClosure" 8]
theorem fwd8 (h : sa_impl% "DynProducts.header.dynClosure") : S8 :=
  fun A hA => h.2.1.2.2 A hA

/-- S9: the factorisation is `prodLift f g`. Its C¹-ness is the pairing clause of
`dyn_prod_closed_of_dyn` (from `h`). The two triangles hold definitionally. Uniqueness among all
semiconjugacies, and so among Dyn morphisms, is `eq_prodLift` (structural). -/
@[sa_forward "DynProducts.header.dynClosure" 9]
theorem fwd9 (h : sa_impl% "DynProducts.header.dynClosure") : S9 := by
  intro A B hA hB C hC f g hf hg
  have p := h.1
  exact ⟨prodLift f g, (@p A B hA.1 hB.1 hA.2 hB.2).2.2.2.2 hC f g hf hg, rfl, rfl,
    fun h' _ e₁ e₂ => eq_prodLift f g h' e₁ e₂⟩

/-- S10: the Dyn morphism is `toPoint C`. Its C¹-ness is the last clause of
`dyn_point_closed_of_dyn` (from `h`). Uniqueness is `eq_toPoint` (structural). -/
@[sa_forward "DynProducts.header.dynClosure" 10]
theorem fwd10 (h : sa_impl% "DynProducts.header.dynClosure") : S10 :=
  fun C hC => ⟨toPoint C, h.2.1.2.2 C hC, fun h' _ => eq_toPoint h'⟩

/-- Backward. `dyn_prod_closed_of_dyn` is S1–S5, `dyn_point_closed_of_dyn` is S6–S8,
`dyn_isProduct` is witnessed by `A.prod B`, `prodFst`, `prodSnd` with S1–S4 and S9, and
`dyn_isTerminal` by `DynSys.point` with S6, S7 and S10. -/
@[sa_backward "DynProducts.header.dynClosure"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) (s7 : S7) (s8 : S8)
    (s9 : S9) (s10 : S10) : sa_impl% "DynProducts.header.dynClosure" := by
  refine ⟨?_, ⟨s6, s7, fun A hA => s8 A hA⟩, ?_, ⟨DynSys.point, ⟨s6, s7⟩, s10⟩⟩
  · intro A B iA iB hA hB
    exact ⟨s1 A B ⟨iA, hA⟩ ⟨iB, hB⟩, s2 A B ⟨iA, hA⟩ ⟨iB, hB⟩, s3 A B ⟨iA, hA⟩ ⟨iB, hB⟩,
      s4 A B ⟨iA, hA⟩ ⟨iB, hB⟩,
      fun {C} hC f g hf hg => s5 A B C ⟨iA, hA⟩ ⟨iB, hB⟩ hC f g hf hg⟩
  · intro A B hA hB
    exact ⟨A.prod B, prodFst A B, prodSnd A B, ⟨s1 A B hA hB, s2 A B hA hB⟩, s3 A B hA hB,
      s4 A B hA hB, fun C hC f g hf hg => s9 A B hA hB C hC f g hf hg⟩

end Alignment.Shadows.DynProducts.HeaderDynClosure

namespace Alignment.Shadows.DynProducts.PointIsTerminal

sa_claim "DynProducts.pointIsTerminal" group "DynProducts" required
  text "The zero-dimensional system is terminal."
  impl NEP.point_isTerminal

@[sa_forward "DynProducts.pointIsTerminal" 1]
theorem fwd1 (h : sa_impl% "DynProducts.pointIsTerminal") : S1 := h

@[sa_backward "DynProducts.pointIsTerminal"]
theorem bwd (s1 : S1) : sa_impl% "DynProducts.pointIsTerminal" := s1

end Alignment.Shadows.DynProducts.PointIsTerminal

namespace Alignment.Shadows.DynProducts.InstHasLimitPair

sa_claim "DynProducts.instHasLimitPair" group "DynProducts" required
  text "Every pair of objects of `DynSys` has a product."
  impl NEP.instHasLimitDiscreteWalkingPairDynSysPair

@[sa_forward "DynProducts.instHasLimitPair" 1]
theorem fwd1 (h : sa_impl% "DynProducts.instHasLimitPair") : S1 :=
  fun A B => h A B

@[sa_backward "DynProducts.instHasLimitPair"]
theorem bwd (s1 : S1) : sa_impl% "DynProducts.instHasLimitPair" :=
  fun A B => s1 A B

end Alignment.Shadows.DynProducts.InstHasLimitPair

namespace Alignment.Shadows.DynProducts.PointEq

sa_claim "DynProducts.pointEq" group "DynProducts" required
  text "The state space of `DynSys.point` has exactly one element."
  impl NEP.point_eq

@[sa_forward "DynProducts.pointEq" 1]
theorem fwd1 (h : sa_impl% "DynProducts.pointEq") : S1 :=
  fun x y => h x y

@[sa_backward "DynProducts.pointEq"]
theorem bwd (s1 : S1) : sa_impl% "DynProducts.pointEq" :=
  fun a b => s1 a b

end Alignment.Shadows.DynProducts.PointEq
