import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Analysis.Normed.Module.Basic

/-!
# L1: the category `DynSys` of vector fields and semiconjugacies

DESIGN_NetworkEpiCore.md §D.3 and §D.7, module L1 `NEP/Dyn/Basic`:
"`structure DynSys`, `structure Semiconj`, `instance : Category DynSys`, `Semiconj.map_solution`;
`SemiconjOn U`, `map_solution_on`, `invariant_incl`".

## Relation to the design's category **Dyn**

The design (§D.3) says: "Objects of **Dyn** are (V, F): V a finite-dimensional real normed space,
F: V → V a C¹ vector field. Morphisms (V, F) → (W, G) are C¹ maps π with Dπ(u)·F(u) = G(π(u))
(semiconjugacies). Identity and composition come from the chain rule."

The Lean category `DynSys` is deliberately *more general*: `V` is any real normed space (not
necessarily finite-dimensional), `F` is any function `V → V` (no regularity), and a morphism is
a map that is differentiable everywhere (not necessarily C¹) and satisfies
`fderiv ℝ π u (F u) = G (π u)` for every `u`. The design's **Dyn** is therefore a subcategory of
`DynSys` (same composition and identities), and every theorem below about all objects or all
morphisms of `DynSys` holds in particular for **Dyn**.

A *solution* of `(V, F)` on a set of times `I` is a curve `x : ℝ → V` with
`HasDerivAt x (F (x t)) t` for every `t ∈ I` (`map_solution`, `map_solution_on`), or, on a time
interval that may contain its end points (for example a forward solution on `[0, T)`), with
`HasDerivWithinAt x (F (x t)) I t` for every `t ∈ I` (`map_solution_within`). The second notion
is weaker: `HasDerivAt` at `t` implies `HasDerivWithinAt` within any `I` at `t`. Statements below
are written with the hypothesis spelled out. Global solutions (`I = ℝ`) need not exist.
-/

open CategoryTheory

namespace NEP

/-- An object of the design's category **Dyn** (DESIGN §D.3), generalised: a real normed space
`V` with a vector field `F : V → V`. The ODE is `u̇ = F u`. -/
structure DynSys where
  /-- The state space. -/
  V : Type
  [ng : NormedAddCommGroup V]
  [ns : NormedSpace ℝ V]
  /-- The vector field. -/
  F : V → V

attribute [instance] DynSys.ng DynSys.ns

/-- `IsSemiconj A B π`: the map `π : A.V → B.V` is differentiable and carries the vector field
of `A` to that of `B`, i.e. `Dπ(u)·F(u) = G(π(u))` for every `u` (DESIGN §D.3). -/
def IsSemiconj (A B : DynSys) (π : A.V → B.V) : Prop :=
  Differentiable ℝ π ∧ ∀ u, fderiv ℝ π u (A.F u) = B.F (π u)

/-- A morphism of `DynSys` (a *semiconjugacy*, DESIGN §D.3): a differentiable map `π` with
`Dπ(u)·F(u) = G(π(u))` for every `u`. -/
@[ext] structure Semiconj (A B : DynSys) where
  /-- The underlying map of state spaces. -/
  π : A.V → B.V
  /-- `π` is differentiable everywhere. -/
  diff : Differentiable ℝ π
  /-- The semiconjugacy identity `Dπ(u)·F(u) = G(π(u))`. -/
  comm : ∀ u, fderiv ℝ π u (A.F u) = B.F (π u)

/-- A bundled semiconjugacy satisfies `IsSemiconj`. -/
theorem Semiconj.isSemiconj {A B : DynSys} (m : Semiconj A B) : IsSemiconj A B m.π :=
  ⟨m.diff, m.comm⟩

/-- Bundle a map satisfying `IsSemiconj` as a morphism. -/
def Semiconj.ofIsSemiconj {A B : DynSys} (π : A.V → B.V) (h : IsSemiconj A B π) :
    Semiconj A B :=
  ⟨π, h.1, h.2⟩

/-- The identity semiconjugacy. -/
def Semiconj.id (A : DynSys) : Semiconj A A :=
  ⟨_root_.id, differentiable_id, fun u => by simp [fderiv_id]⟩

/-- Composition of semiconjugacies, `(f ≫ g).π = g.π ∘ f.π`; the identity holds by the chain
rule. -/
def Semiconj.comp {A B C : DynSys} (f : Semiconj A B) (g : Semiconj B C) : Semiconj A C :=
  ⟨g.π ∘ f.π, g.diff.comp f.diff, fun u => by
    rw [fderiv_comp u (g.diff _) (f.diff u)]
    simp [ContinuousLinearMap.comp_apply, f.comm, g.comm]⟩

/-- **The category `DynSys`** (DESIGN §D.3: "[L] `instance : Category DynSys`").
Objects are `DynSys`, morphisms `A ⟶ B` are `Semiconj A B`, the identity is `id` and
composition is composition of maps (`comp_π`, `id_π`). -/
instance dynCategory : Category DynSys where
  Hom A B := Semiconj A B
  id A := Semiconj.id A
  comp f g := Semiconj.comp f g
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The morphisms of `DynSys` are exactly the semiconjugacies. -/
theorem hom_eq_semiconj (A B : DynSys) : (A ⟶ B) = Semiconj A B := rfl

/-- In `DynSys` the identity morphism is the identity map. -/
@[simp] theorem id_π (A : DynSys) : Semiconj.π (𝟙 A : Semiconj A A) = _root_.id := rfl

/-- In `DynSys` composition of morphisms is composition of the underlying maps. -/
@[simp] theorem comp_π {A B C : DynSys} (f : A ⟶ B) (g : B ⟶ C) :
    Semiconj.π (f ≫ g : Semiconj A C) = Semiconj.π (g : Semiconj B C) ∘ Semiconj.π (f : Semiconj A B) :=
  rfl

/-- **Semiconjugacies map solutions to solutions.**

Design statement (DESIGN_NetworkEpiCore.md §D.3): "[L] `instance : Category DynSys` and
`Semiconj.map_solution` (semiconjugacies map solution curves to solution curves)".

Lean statement: let `m` be a semiconjugacy from `(V, F)` to `(W, G)` and let `I` be any set of
times. If a curve `x : ℝ → V` satisfies `x'(t) = F(x(t))` (as `HasDerivAt`) at every `t ∈ I`,
then the curve `π ∘ x` satisfies `(π ∘ x)'(t) = G(π(x(t)))` at every `t ∈ I`. With `I = univ`
this is the statement for global solutions. -/
theorem Semiconj.map_solution {A B : DynSys} (m : Semiconj A B) {x : ℝ → A.V} {I : Set ℝ}
    (hx : ∀ t ∈ I, HasDerivAt x (A.F (x t)) t) :
    ∀ t ∈ I, HasDerivAt (m.π ∘ x) (B.F (m.π (x t))) t := by
  intro t ht
  have h := (m.diff (x t)).hasFDerivAt.comp_hasDerivAt t (hx t ht)
  rwa [m.comm] at h

/-- Semiconjugacies map solutions within a set of times to solutions within it: if
`x'(t) = F(x(t))` within `I` (`HasDerivWithinAt`) at every `t ∈ I`, then
`(π ∘ x)'(t) = G(π(x(t)))` within `I` at every `t ∈ I`. -/
theorem Semiconj.map_solution_within {A B : DynSys} (m : Semiconj A B) {x : ℝ → A.V}
    {I : Set ℝ} (hx : ∀ t ∈ I, HasDerivWithinAt x (A.F (x t)) I t) :
    ∀ t ∈ I, HasDerivWithinAt (m.π ∘ x) (B.F (m.π (x t))) I t := by
  intro t ht
  have h := (m.diff (x t)).hasFDerivAt.comp_hasDerivWithinAt t (hx t ht)
  rwa [m.comm] at h

/-- **Semiconjugacies map global solutions to global solutions.**

Design statement (DESIGN_NetworkEpiCore.md §D.3): "[L] `instance : Category DynSys` and
`Semiconj.map_solution` (semiconjugacies map solution curves to solution curves)".

Lean statement: let `m` be a semiconjugacy from `(V, F)` to `(W, G)`. If a curve `x : ℝ → V`
satisfies `x'(t) = F(x(t))` (as `HasDerivAt`) at every `t : ℝ`, then `π ∘ x` satisfies
`(π ∘ x)'(t) = G(π(x(t)))` at every `t : ℝ`. (The case `I = univ` of `Semiconj.map_solution`.) -/
theorem Semiconj.map_solution_global {A B : DynSys} (m : Semiconj A B) (x : ℝ → A.V)
    (hx : ∀ t : ℝ, HasDerivAt x (A.F (x t)) t) :
    ∀ t : ℝ, HasDerivAt (m.π ∘ x) (B.F (m.π (x t))) t :=
  fun t => m.map_solution (I := Set.univ) (fun t _ => hx t) t (Set.mem_univ t)

/-- **Semiconjugacies map solutions on an open time interval to solutions on it.**

Design statement (DESIGN_NetworkEpiCore.md §D.3): "[L] `instance : Category DynSys` and
`Semiconj.map_solution` (semiconjugacies map solution curves to solution curves)".

Lean statement: let `m` be a semiconjugacy from `(V, F)` to `(W, G)` and `J` an open time
interval (`IsOpen J`, `Convex ℝ J`, possibly unbounded). If a curve `x : ℝ → V` satisfies
`x'(t) = F(x(t))` (as `HasDerivAt`) at every `t ∈ J`, then `π ∘ x` satisfies
`(π ∘ x)'(t) = G(π(x(t)))` at every `t ∈ J`. (A special case of `Semiconj.map_solution`, which
needs neither openness nor convexity.) -/
theorem Semiconj.map_solution_open {A B : DynSys} (m : Semiconj A B) (J : Set ℝ)
    (_hJo : IsOpen J) (_hJc : Convex ℝ J) (x : ℝ → A.V)
    (hx : ∀ t ∈ J, HasDerivAt x (A.F (x t)) t) :
    ∀ t ∈ J, HasDerivAt (m.π ∘ x) (B.F (m.π (x t))) t :=
  m.map_solution hx

/-! ## Local semiconjugacies -/

/-- A *local semiconjugacy on `U`* (DESIGN §D.3, "Local version `SemiconjOn U`"): a map
`π : A.V → B.V` that is differentiable at every point of `U` and satisfies
`Dπ(u)·F(u) = G(π(u))` for every `u ∈ U`. The design's use is an open `U` such as
`{ψ(θ) ≠ 0, ψ'(θ) ≠ 0}`; openness is not required here because differentiability is asked for
at each point of `U`. -/
structure SemiconjOn (A B : DynSys) (U : Set A.V) where
  /-- The underlying map. -/
  π : A.V → B.V
  /-- `π` is differentiable at every point of `U`. -/
  diff : ∀ u ∈ U, DifferentiableAt ℝ π u
  /-- The semiconjugacy identity on `U`. -/
  comm : ∀ u ∈ U, fderiv ℝ π u (A.F u) = B.F (π u)

/-- `IsSemiconjOn A B U π`: `π` is differentiable at every point of `U` and
`Dπ(u)·F(u) = G(π(u))` for every `u ∈ U`. -/
def IsSemiconjOn (A B : DynSys) (U : Set A.V) (π : A.V → B.V) : Prop :=
  (∀ u ∈ U, DifferentiableAt ℝ π u) ∧ ∀ u ∈ U, fderiv ℝ π u (A.F u) = B.F (π u)

/-- A bundled local semiconjugacy satisfies `IsSemiconjOn`. -/
theorem SemiconjOn.isSemiconjOn {A B : DynSys} {U : Set A.V} (m : SemiconjOn A B U) :
    IsSemiconjOn A B U m.π :=
  ⟨m.diff, m.comm⟩

/-- Bundle a map satisfying `IsSemiconjOn` as a local semiconjugacy. -/
def SemiconjOn.ofIsSemiconjOn {A B : DynSys} {U : Set A.V} (π : A.V → B.V)
    (h : IsSemiconjOn A B U π) : SemiconjOn A B U :=
  ⟨π, h.1, h.2⟩

/-- A global semiconjugacy is a local one on every set. -/
def Semiconj.toSemiconjOn {A B : DynSys} (m : Semiconj A B) (U : Set A.V) : SemiconjOn A B U :=
  ⟨m.π, fun u _ => m.diff u, fun u _ => m.comm u⟩

/-- Restricting a local semiconjugacy to a smaller set. -/
def SemiconjOn.mono {A B : DynSys} {U U' : Set A.V} (m : SemiconjOn A B U) (h : U' ⊆ U) :
    SemiconjOn A B U' :=
  ⟨m.π, fun u hu => m.diff u (h hu), fun u hu => m.comm u (h hu)⟩

/-- Composition of local semiconjugacies: `g ∘ f` is a local semiconjugacy on the set of points
of `U` that `f` sends into `W`. -/
def SemiconjOn.comp {A B C : DynSys} {U : Set A.V} {W : Set B.V} (f : SemiconjOn A B U)
    (g : SemiconjOn B C W) : SemiconjOn A C (U ∩ f.π ⁻¹' W) :=
  ⟨g.π ∘ f.π, fun u hu => (g.diff _ hu.2).comp u (f.diff u hu.1), fun u hu => by
    rw [fderiv_comp u (g.diff _ hu.2) (f.diff u hu.1), ContinuousLinearMap.comp_apply,
      f.comm u hu.1, g.comm _ hu.2]
    rfl⟩

/-- **Local semiconjugacies map solutions that stay in `U` to solutions.**

Design statement (DESIGN_NetworkEpiCore.md §D.3): "**Local version `SemiconjOn U`.** The
identity holds on an open set U, and solutions that stay in U are mapped. This is needed for
maps that divide by ψ(θ) or ψ'(θ)."

Lean statement: let `m` be a local semiconjugacy on `U` from `(V, F)` to `(W, G)` and let `I` be
any set of times. If a curve `x` satisfies `x'(t) = F(x(t))` at every `t ∈ I` and `x(t) ∈ U` for
every `t ∈ I`, then `(π ∘ x)'(t) = G(π(x(t)))` at every `t ∈ I`. -/
theorem SemiconjOn.map_solution_on {A B : DynSys} {U : Set A.V} (m : SemiconjOn A B U)
    {x : ℝ → A.V} {I : Set ℝ} (hx : ∀ t ∈ I, HasDerivAt x (A.F (x t)) t)
    (hU : ∀ t ∈ I, x t ∈ U) :
    ∀ t ∈ I, HasDerivAt (m.π ∘ x) (B.F (m.π (x t))) t := by
  intro t ht
  have h := (m.diff (x t) (hU t ht)).hasFDerivAt.comp_hasDerivAt t (hx t ht)
  rwa [m.comm _ (hU t ht)] at h

/-- **Local semiconjugacies map solutions within a set of times `I` that stay in `U` to solutions
within `I`.**

Design statement (DESIGN_NetworkEpiCore.md §D.3): "**Local version `SemiconjOn U`.** The
identity holds on an open set U, and solutions that stay in U are mapped. This is needed for
maps that divide by ψ(θ) or ψ'(θ)."

Lean statement: let `m` be a local semiconjugacy on `U` from `(V, F)` to `(W, G)` and let `I` be
any set of times. If a curve `x` satisfies `x'(t) = F(x(t))` within `I` (`HasDerivWithinAt`, so
one-sided at end points of `I` that lie in `I`, as for a forward solution on `[0, T)`) at every
`t ∈ I`, and `x(t) ∈ U` for every `t ∈ I`, then `(π ∘ x)'(t) = G(π(x(t)))` within `I` at every
`t ∈ I`. -/
theorem SemiconjOn.map_solution_within {A B : DynSys} {U : Set A.V} (m : SemiconjOn A B U)
    {x : ℝ → A.V} {I : Set ℝ} (hx : ∀ t ∈ I, HasDerivWithinAt x (A.F (x t)) I t)
    (hU : ∀ t ∈ I, x t ∈ U) :
    ∀ t ∈ I, HasDerivWithinAt (m.π ∘ x) (B.F (m.π (x t))) I t := by
  intro t ht
  have h := (m.diff (x t) (hU t ht)).hasFDerivAt.comp_hasDerivWithinAt t (hx t ht)
  rwa [m.comm _ (hU t ht)] at h

/-- **Local semiconjugacies map global solutions that stay in `U` to global solutions.**

Design statement (DESIGN_NetworkEpiCore.md §D.3): "**Local version `SemiconjOn U`.** The
identity holds on an open set U, and solutions that stay in U are mapped. This is needed for
maps that divide by ψ(θ) or ψ'(θ)."

Lean statement: let `m` be a local semiconjugacy on `U` from `(V, F)` to `(W, G)` (`U` need not be
open). If a curve `x` satisfies `x(t) ∈ U` and `x'(t) = F(x(t))` for every `t : ℝ`, then
`(π ∘ x)'(t) = G(π(x(t)))` for every `t : ℝ`. (The case `I = univ` of
`SemiconjOn.map_solution_on`.) -/
theorem SemiconjOn.map_solution_on_global {A B : DynSys} {U : Set A.V} (m : SemiconjOn A B U)
    (x : ℝ → A.V) (hU : ∀ t : ℝ, x t ∈ U) (hx : ∀ t : ℝ, HasDerivAt x (A.F (x t)) t) :
    ∀ t : ℝ, HasDerivAt (m.π ∘ x) (B.F (m.π (x t))) t :=
  fun t => m.map_solution_on (I := Set.univ) (fun t _ => hx t) (fun t _ => hU t) t
    (Set.mem_univ t)

/-- **Local semiconjugacies map solutions on an open time interval that stay in `U` to solutions
on it.**

Design statement (DESIGN_NetworkEpiCore.md §D.3): "**Local version `SemiconjOn U`.** The
identity holds on an open set U, and solutions that stay in U are mapped. This is needed for
maps that divide by ψ(θ) or ψ'(θ)."

Lean statement: let `m` be a local semiconjugacy on `U` from `(V, F)` to `(W, G)` (`U` need not be
open) and `J` an open time interval (`IsOpen J`, `Convex ℝ J`). If a curve `x` satisfies
`x(t) ∈ U` and `x'(t) = F(x(t))` for every `t ∈ J`, then `(π ∘ x)'(t) = G(π(x(t)))` for every
`t ∈ J`. (A special case of `SemiconjOn.map_solution_on`.) -/
theorem SemiconjOn.map_solution_on_open {A B : DynSys} {U : Set A.V} (m : SemiconjOn A B U)
    (J : Set ℝ) (_hJo : IsOpen J) (_hJc : Convex ℝ J) (x : ℝ → A.V) (hU : ∀ t ∈ J, x t ∈ U)
    (hx : ∀ t ∈ J, HasDerivAt x (A.F (x t)) t) :
    ∀ t ∈ J, HasDerivAt (m.π ∘ x) (B.F (m.π (x t))) t :=
  m.map_solution_on hx hU

/-! ## Invariant affine subspaces and restrictions -/

/-- The *restriction* of `A` to the affine subspace `p₀ + W`, in the chart `w ↦ p₀ + w`
(DESIGN §D.3: "The inclusion of an invariant subsystem is a restriction"). The hypothesis
`hW` says that `F` is tangent to `p₀ + W`: `F(p₀ + w) ∈ W` for every `w ∈ W`. The restricted
system lives on `W` with vector field `w ↦ F(p₀ + w)`. With `p₀ = 0` this is the restriction
to an invariant linear subspace. -/
noncomputable def DynSys.restrict (A : DynSys) (p₀ : A.V) (W : Submodule ℝ A.V)
    (hW : ∀ w ∈ W, A.F (p₀ + w) ∈ W) : DynSys where
  V := W
  F w := ⟨A.F (p₀ + w), hW w w.2⟩

/-- The chart of the restriction, `w ↦ p₀ + w`. -/
def DynSys.restrictIncl (A : DynSys) (p₀ : A.V) (W : Submodule ℝ A.V) : W → A.V :=
  fun w => p₀ + (w : A.V)

/-- The chart `w ↦ p₀ + w` has derivative the inclusion `W →L[ℝ] V` at every point. -/
theorem DynSys.hasFDerivAt_restrictIncl (A : DynSys) (p₀ : A.V) (W : Submodule ℝ A.V) (w : W) :
    HasFDerivAt (A.restrictIncl p₀ W) W.subtypeL w :=
  (W.subtypeL.hasFDerivAt).const_add p₀

/-- **The inclusion of an invariant subsystem is a semiconjugacy (a restriction).**

Design statement (DESIGN_NetworkEpiCore.md §D.3): "The inclusion of an invariant subsystem is a
restriction. "Model A is exact for initial conditions in W" is a morphism *out of* (W, F|_W)."

Lean statement: let `W` be a linear subspace of `A.V` and `p₀ ∈ A.V` such that the vector field
`F` of `A` is tangent to the affine subspace `p₀ + W`, i.e. `F(p₀ + w) ∈ W` for every `w ∈ W`.
Then the map `w ↦ p₀ + w` from the restricted system `(W, w ↦ F(p₀ + w))` to `A` is a
semiconjugacy: it is differentiable and `D(p₀ + ·)(w)·F(p₀ + w) = F(p₀ + w)` for every `w ∈ W`. -/
theorem invariant_incl (A : DynSys) (p₀ : A.V) (W : Submodule ℝ A.V)
    (hW : ∀ w ∈ W, A.F (p₀ + w) ∈ W) :
    IsSemiconj (A.restrict p₀ W hW) A (A.restrictIncl p₀ W) := by
  refine ⟨fun w => (A.hasFDerivAt_restrictIncl p₀ W w).differentiableAt, fun w => ?_⟩
  erw [(A.hasFDerivAt_restrictIncl p₀ W w).fderiv]
  rfl

/-- The restriction morphism `(W, F|_W) ⟶ A` of `invariant_incl`. -/
noncomputable def invariantIncl (A : DynSys) (p₀ : A.V) (W : Submodule ℝ A.V)
    (hW : ∀ w ∈ W, A.F (p₀ + w) ∈ W) : A.restrict p₀ W hW ⟶ A :=
  Semiconj.ofIsSemiconj _ (invariant_incl A p₀ W hW)

end NEP
