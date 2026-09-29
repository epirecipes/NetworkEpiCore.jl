import Alignment.Registry
import NetworkEpi.Morphisms.WellMixed

/-!
# Blind shadows: group `MorphismsWellMixed` (DESIGN §D.5 row M1, §C.3 `WellMixed(κ)`)

Written blind from `Alignment/claims_blind.yaml` (the entries of the ids below),
`Alignment/DataTypes/MorphismsWellMixed.md`, `Alignment/README.md`,
`Alignment/Example/ExampleShadows.lean`, `SA-PASS_SKILL.md` and `DESIGN_NetworkEpiCore.md`
(§C.3, §D.3, §D.5 M1). No trusted source, checker or report was read.

Conventions used throughout (DataTypes §(e), DESIGN §D.3):

* species form a type `σ`; instances (`Fintype σ`, `DecidableEq σ`) are assumed "where required",
  i.e. where an operation or a normed structure on `σ → ℝ` needs them;
* "semiconjugacy π : A → B" (global): `π` differentiable and `Dπ(u)·F(u) = G(π(u))` for every `u`;
  its local version on `U` asks both at points of `U` only;
* "exit-free": `∀ r ∈ rs, r.isExit = false`;
* a *solution of `A` on a set of times `I`*: `∀ t ∈ I, HasDerivAt x (A.F (x t)) t`.
  -- AMBIGUITY: "solutions are mapped" does not fix the solution notion; DataTypes §(f) allows
  -- either `HasDerivAt` at every `t ∈ I` or `HasDerivWithinAt … I t`, and DESIGN §M.5 asserts
  -- both for M1. The (re-shadowed) `wellmixedUnitSolution` shadows state both readings, one
  -- shadow each, for every set of times `I` (so in particular every interval).
-/

open NEP

namespace Alignment.Shadows.MorphismsWellMixed

/-- Exit-free reaction list (DataTypes §(e)). -/
def ExitFree {σ : Type} (rs : List (Rxn σ)) : Prop := ∀ r ∈ rs, r.isExit = false

/-- The inclusion `(θ, x) ↦ (θ, 1, x)` of the slice `ξ = 1`. -/
def inclXi1 {σ : Type} (w : ℝ × (σ → ℝ)) : WM σ := (w.1, 1, w.2)

end Alignment.Shadows.MorphismsWellMixed

/-! ## `MorphismsWellMixed.wellmixedUnitSemiconj`

Text: "for every T_EB model (exits allowed) and all κ, q, `(θ, ξ, x) ↦ (qξe^{κ(θ−1)}, x)` is a
global semiconjugacy onto MA(c_κ P)". Model: `wmSys κ q P`; target: `maSys (wmTarget κ P)`;
map: `wmMap κ q`. A global semiconjugacy (DESIGN §D.3) is a differentiable map with
`Dπ(u)·F(u) = G(π(u))` for every `u`: one shadow per conjunct.
-- AMBIGUITY: "onto" is read as "to (the target system)"; surjectivity is the separate
-- claim `wellmixedUnitQuotient` (and fails for q = 0). -/
namespace Alignment.Shadows.MorphismsWellMixed.WellmixedUnitSemiconj

@[sa_reference "MorphismsWellMixed.wellmixedUnitSemiconj"]
def T : Prop :=
  ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (κ q : ℝ) (P : List (Rxn σ)),
    Differentiable ℝ (wmMap (σ := σ) κ q) ∧
    ∀ u : WM σ, fderiv ℝ (wmMap κ q) u ((wmSys κ q P).F u) =
      (maSys (wmTarget κ P)).F (wmMap κ q u)

/-- S1: the map is differentiable (for every model, all κ, q). -/
@[sa_shadow "MorphismsWellMixed.wellmixedUnitSemiconj" 1]
def S1 : Prop :=
  ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (κ q : ℝ) (_P : List (Rxn σ)),
    Differentiable ℝ (wmMap (σ := σ) κ q)

/-- S2: its derivative carries the well-mixed EB field of `P` (exits allowed) to the
mass-action field of `c_κ P`, at every state. -/
@[sa_shadow "MorphismsWellMixed.wellmixedUnitSemiconj" 2]
def S2 : Prop :=
  ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (κ q : ℝ) (P : List (Rxn σ)) (u : WM σ),
    fderiv ℝ (wmMap κ q) u ((wmSys κ q P).F u) = (maSys (wmTarget κ P)).F (wmMap κ q u)

@[sa_ref_forward "MorphismsWellMixed.wellmixedUnitSemiconj" 1]
theorem ref_fwd1 : T → S1 := by
  intro t σ _ _ κ q P
  exact (t κ q P).1

@[sa_ref_forward "MorphismsWellMixed.wellmixedUnitSemiconj" 2]
theorem ref_fwd2 : T → S2 := by
  intro t σ _ _ κ q P u
  exact (t κ q P).2 u

@[sa_complete "MorphismsWellMixed.wellmixedUnitSemiconj"]
theorem complete (s1 : S1) (s2 : S2) : T := by
  intro σ _ _ κ q P
  exact ⟨s1 κ q P, fun u => s2 κ q P u⟩

end Alignment.Shadows.MorphismsWellMixed.WellmixedUnitSemiconj

/-! ## `MorphismsWellMixed.wellmixedUnitQuotient`

Text (title): "The well-mixed map with exits is a quotient (M1)"; design: "With exits,
(θ, ξ, x) ↦ (qξe^{κ(θ−1)}, x) is a quotient semiconjugacy"; precise fragment: "for `q ≠ 0` it is a
surjective submersion". DESIGN §D.3: "A surjective submersion is a quotient." The map is
`wmMap κ q` (all κ; the text puts no condition on κ). Read as: for all κ and all `q ≠ 0`,
`wmMap κ q : WM σ → MA σ` is (1) surjective, (2) differentiable, and (3) a submersion: its
derivative `fderiv ℝ (wmMap κ q) u` is surjective at every state `u`.
-- AMBIGUITY: "quotient semiconjugacy" also asserts the semiconjugacy (field identity); the
-- title and the precise fragment ("it is a surjective submersion") make the quotient
-- property the content of this claim, and the semiconjugacy is the separate claim
-- `wellmixedUnitSemiconj`, so it has no shadow here.
-- AMBIGUITY: "submersion" is read with the design's DynSys regularity (differentiable, as in
-- `Semiconj.diff`) rather than C¹, plus a surjective derivative at every point. -/
namespace Alignment.Shadows.MorphismsWellMixed.WellmixedUnitQuotient

@[sa_reference "MorphismsWellMixed.wellmixedUnitQuotient"]
def T : Prop :=
  (∀ {σ : Type} (κ q : ℝ), q ≠ 0 → Function.Surjective (wmMap (σ := σ) κ q)) ∧
  (∀ {σ : Type} [Fintype σ] (κ q : ℝ), q ≠ 0 → Differentiable ℝ (wmMap (σ := σ) κ q)) ∧
  (∀ {σ : Type} [Fintype σ] (κ q : ℝ), q ≠ 0 →
    ∀ u : WM σ, Function.Surjective (fderiv ℝ (wmMap (σ := σ) κ q) u))

/-- S1: for `q ≠ 0` the map `(θ, ξ, x) ↦ (qξe^{κ(θ−1)}, x)` is surjective onto `MA σ`. -/
@[sa_shadow "MorphismsWellMixed.wellmixedUnitQuotient" 1]
def S1 : Prop := ∀ {σ : Type} (κ q : ℝ), q ≠ 0 → Function.Surjective (wmMap (σ := σ) κ q)

/-- S2: for `q ≠ 0` the map is differentiable (a submersion is a differentiable map). -/
@[sa_shadow "MorphismsWellMixed.wellmixedUnitQuotient" 2]
def S2 : Prop :=
  ∀ {σ : Type} [Fintype σ] (κ q : ℝ), q ≠ 0 → Differentiable ℝ (wmMap (σ := σ) κ q)

/-- S3: submersion: for `q ≠ 0` the derivative is surjective at every state. -/
@[sa_shadow "MorphismsWellMixed.wellmixedUnitQuotient" 3]
def S3 : Prop :=
  ∀ {σ : Type} [Fintype σ] (κ q : ℝ), q ≠ 0 →
    ∀ u : WM σ, Function.Surjective (fderiv ℝ (wmMap (σ := σ) κ q) u)

@[sa_ref_forward "MorphismsWellMixed.wellmixedUnitQuotient" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "MorphismsWellMixed.wellmixedUnitQuotient" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1

@[sa_ref_forward "MorphismsWellMixed.wellmixedUnitQuotient" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2

@[sa_complete "MorphismsWellMixed.wellmixedUnitQuotient"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.MorphismsWellMixed.WellmixedUnitQuotient

/-! ## `MorphismsWellMixed.wellmixedUnit`

Text: "for exit-free P, `κ ≠ 0` and `q > 0`, the model on `(θ; x)` is conjugate to MA(c_κ P)
restricted to `S > 0` (inverse `(S, x) ↦ (1 + log(S/q)/κ, x)`)". Model on `(θ; x)`:
`wmSys1 κ q P` (whole state space); target: `maSys (wmTarget κ P)` on `U = {v | 0 < v.1}`;
`h = wmMap1 κ q`, `g = wmInv κ q`. A conjugacy between `A` on `V = univ` and `B` on `U`
(DESIGN §D.3 "conjugacies (diffeomorphic semiconjugacies)", local version on `U`): `h` a
semiconjugacy on `V` with `h(V) ⊆ U`, `g` a semiconjugacy on `U` (differentiable at points of
`U`, field identity at points of `U`), and `g ∘ h = id` on `V`, `h ∘ g = id` on `U`. The
condition `g(U) ⊆ V = univ` is vacuous and has no shadow. -/
namespace Alignment.Shadows.MorphismsWellMixed.WellmixedUnit

/-- The common hypotheses of the claim. -/
def Hyp {σ : Type} (κ q : ℝ) (P : List (Rxn σ)) : Prop := ExitFree P ∧ κ ≠ 0 ∧ 0 < q

@[sa_reference "MorphismsWellMixed.wellmixedUnit"]
def T : Prop :=
  ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (κ q : ℝ) (P : List (Rxn σ)), Hyp κ q P →
    (∀ w : ℝ × (σ → ℝ), DifferentiableAt ℝ (wmMap1 κ q) w) ∧
    (∀ w : ℝ × (σ → ℝ), fderiv ℝ (wmMap1 κ q) w ((wmSys1 κ q P).F w) =
        (maSys (wmTarget κ P)).F (wmMap1 κ q w)) ∧
    (∀ w : ℝ × (σ → ℝ), 0 < (wmMap1 κ q w).1) ∧
    (∀ v : MA σ, 0 < v.1 → DifferentiableAt ℝ (wmInv κ q) v) ∧
    (∀ v : MA σ, 0 < v.1 → fderiv ℝ (wmInv κ q) v ((maSys (wmTarget κ P)).F v) =
        (wmSys1 κ q P).F (wmInv κ q v)) ∧
    (∀ w : ℝ × (σ → ℝ), wmInv κ q (wmMap1 (σ := σ) κ q w) = w) ∧
    (∀ v : MA σ, 0 < v.1 → wmMap1 κ q (wmInv κ q v) = v)

/-- S1: the forward map `(θ, x) ↦ (qe^{κ(θ−1)}, x)` is differentiable at every state. -/
@[sa_shadow "MorphismsWellMixed.wellmixedUnit" 1]
def S1 : Prop :=
  ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (κ q : ℝ) (P : List (Rxn σ)), Hyp κ q P →
    ∀ w : ℝ × (σ → ℝ), DifferentiableAt ℝ (wmMap1 κ q) w

/-- S2: the forward map carries the `(θ; x)` field to the mass-action field of `c_κ P`. -/
@[sa_shadow "MorphismsWellMixed.wellmixedUnit" 2]
def S2 : Prop :=
  ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (κ q : ℝ) (P : List (Rxn σ)), Hyp κ q P →
    ∀ w : ℝ × (σ → ℝ), fderiv ℝ (wmMap1 κ q) w ((wmSys1 κ q P).F w) =
      (maSys (wmTarget κ P)).F (wmMap1 κ q w)

/-- S3: the forward map lands in the restriction `S > 0`. -/
@[sa_shadow "MorphismsWellMixed.wellmixedUnit" 3]
def S3 : Prop :=
  ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (κ q : ℝ) (P : List (Rxn σ)), Hyp κ q P →
    ∀ w : ℝ × (σ → ℝ), 0 < (wmMap1 κ q w).1

/-- S4: the inverse `(S, x) ↦ (1 + log(S/q)/κ, x)` is differentiable at every point with `S > 0`. -/
@[sa_shadow "MorphismsWellMixed.wellmixedUnit" 4]
def S4 : Prop :=
  ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (κ q : ℝ) (P : List (Rxn σ)), Hyp κ q P →
    ∀ v : MA σ, 0 < v.1 → DifferentiableAt ℝ (wmInv κ q) v

/-- S5: on `S > 0` the inverse carries the mass-action field of `c_κ P` back to the `(θ; x)` field. -/
@[sa_shadow "MorphismsWellMixed.wellmixedUnit" 5]
def S5 : Prop :=
  ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (κ q : ℝ) (P : List (Rxn σ)), Hyp κ q P →
    ∀ v : MA σ, 0 < v.1 → fderiv ℝ (wmInv κ q) v ((maSys (wmTarget κ P)).F v) =
      (wmSys1 κ q P).F (wmInv κ q v)

/-- S6: `wmInv ∘ wmMap1 = id` on the whole `(θ; x)` space. -/
@[sa_shadow "MorphismsWellMixed.wellmixedUnit" 6]
def S6 : Prop :=
  ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (κ q : ℝ) (P : List (Rxn σ)), Hyp κ q P →
    ∀ w : ℝ × (σ → ℝ), wmInv κ q (wmMap1 (σ := σ) κ q w) = w

/-- S7: `wmMap1 ∘ wmInv = id` on `S > 0`. -/
@[sa_shadow "MorphismsWellMixed.wellmixedUnit" 7]
def S7 : Prop :=
  ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (κ q : ℝ) (P : List (Rxn σ)), Hyp κ q P →
    ∀ v : MA σ, 0 < v.1 → wmMap1 κ q (wmInv κ q v) = v

@[sa_ref_forward "MorphismsWellMixed.wellmixedUnit" 1]
theorem ref_fwd1 : T → S1 := by
  intro t σ _ _ κ q P h; exact (t κ q P h).1
@[sa_ref_forward "MorphismsWellMixed.wellmixedUnit" 2]
theorem ref_fwd2 : T → S2 := by
  intro t σ _ _ κ q P h; exact (t κ q P h).2.1
@[sa_ref_forward "MorphismsWellMixed.wellmixedUnit" 3]
theorem ref_fwd3 : T → S3 := by
  intro t σ _ _ κ q P h; exact (t κ q P h).2.2.1
@[sa_ref_forward "MorphismsWellMixed.wellmixedUnit" 4]
theorem ref_fwd4 : T → S4 := by
  intro t σ _ _ κ q P h; exact (t κ q P h).2.2.2.1
@[sa_ref_forward "MorphismsWellMixed.wellmixedUnit" 5]
theorem ref_fwd5 : T → S5 := by
  intro t σ _ _ κ q P h; exact (t κ q P h).2.2.2.2.1
@[sa_ref_forward "MorphismsWellMixed.wellmixedUnit" 6]
theorem ref_fwd6 : T → S6 := by
  intro t σ _ _ κ q P h; exact (t κ q P h).2.2.2.2.2.1
@[sa_ref_forward "MorphismsWellMixed.wellmixedUnit" 7]
theorem ref_fwd7 : T → S7 := by
  intro t σ _ _ κ q P h; exact (t κ q P h).2.2.2.2.2.2

@[sa_complete "MorphismsWellMixed.wellmixedUnit"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) (s7 : S7) : T := by
  intro σ _ _ κ q P h
  exact ⟨s1 κ q P h, s2 κ q P h, s3 κ q P h, s4 κ q P h, s5 κ q P h, s6 κ q P h, s7 κ q P h⟩

end Alignment.Shadows.MorphismsWellMixed.WellmixedUnit

/-! ## `MorphismsWellMixed.wellmixedUnitIic`

Text (title): "The half-space θ ≤ 1 corresponds to S ∈ (0, q] (M1)"; design: "EB_{WM(κ)}(P) on
(θ; x) with S = q e^{κ(θ−1)} is conjugate to MA(c_κ P) on S ∈ (0, q]"; precise fragment: "for
`κ > 0` the half-space `θ ≤ 1` corresponds to `S ∈ (0, q]`". The correspondence is through the
coordinate change `(θ, x) ↦ (q e^{κ(θ−1)}, x)` = `wmMap1 κ q`. "Corresponds" under a change of
coordinates is read as: the map carries the half-space `A = {θ ≤ 1}` onto `B = {S ∈ (0, q]}`
and only `A` goes to `B`, i.e. `wmMap1 '' A = B` and `wmMap1 ⁻¹' B = A`. Three atomic
requirements: (1) `A` is mapped into `B`; (2) every point of `B` is the image of a point of `A`;
(3) a state mapped into `B` lies in `A`.
-- AMBIGUITY: `q > 0` is not restated in the fragment. For `q ≤ 0` the set `S ∈ (0, q]` is
-- empty while `{θ ≤ 1}` is not, so the text is false there; `q > 0` is taken from the design
-- context (`S = q e^{κ(θ−1)}` ranges over `(0, q]` only for `q > 0`; the conjugacy claim of M1
-- assumes `q > 0`).
-- AMBIGUITY: the design quote's conjugacy on `S ∈ (0, q]` is not re-shadowed here; the title
-- and the precise fragment make the half-space correspondence the content of this claim. -/
namespace Alignment.Shadows.MorphismsWellMixed.WellmixedUnitIic

@[sa_reference "MorphismsWellMixed.wellmixedUnitIic"]
def T : Prop :=
  ∀ {σ : Type} (κ q : ℝ), 0 < κ → 0 < q →
    wmMap1 (σ := σ) κ q '' {w | w.1 ≤ 1} = {v | v.1 ∈ Set.Ioc 0 q} ∧
    wmMap1 (σ := σ) κ q ⁻¹' {v | v.1 ∈ Set.Ioc 0 q} = {w | w.1 ≤ 1}

/-- S1: a state with `θ ≤ 1` is mapped to `S ∈ (0, q]`. -/
@[sa_shadow "MorphismsWellMixed.wellmixedUnitIic" 1]
def S1 : Prop :=
  ∀ {σ : Type} (κ q : ℝ), 0 < κ → 0 < q →
    ∀ w : ℝ × (σ → ℝ), w.1 ≤ 1 → (wmMap1 κ q w).1 ∈ Set.Ioc 0 q

/-- S2: every `(S, x)` with `S ∈ (0, q]` is the image of a state with `θ ≤ 1`. -/
@[sa_shadow "MorphismsWellMixed.wellmixedUnitIic" 2]
def S2 : Prop :=
  ∀ {σ : Type} (κ q : ℝ), 0 < κ → 0 < q →
    ∀ v : MA σ, v.1 ∈ Set.Ioc 0 q → ∃ w : ℝ × (σ → ℝ), w.1 ≤ 1 ∧ wmMap1 κ q w = v

/-- S3: only the half-space goes to `S ∈ (0, q]`: a state mapped to `S ∈ (0, q]` has `θ ≤ 1`. -/
@[sa_shadow "MorphismsWellMixed.wellmixedUnitIic" 3]
def S3 : Prop :=
  ∀ {σ : Type} (κ q : ℝ), 0 < κ → 0 < q →
    ∀ w : ℝ × (σ → ℝ), (wmMap1 κ q w).1 ∈ Set.Ioc 0 q → w.1 ≤ 1

@[sa_ref_forward "MorphismsWellMixed.wellmixedUnitIic" 1]
theorem ref_fwd1 : T → S1 := by
  intro t σ κ q hκ hq w hw
  have : wmMap1 κ q w ∈ wmMap1 (σ := σ) κ q '' {w | w.1 ≤ 1} := ⟨w, hw, rfl⟩
  rw [(t κ q hκ hq).1] at this
  exact this

@[sa_ref_forward "MorphismsWellMixed.wellmixedUnitIic" 2]
theorem ref_fwd2 : T → S2 := by
  intro t σ κ q hκ hq v hv
  have : v ∈ wmMap1 (σ := σ) κ q '' {w | w.1 ≤ 1} := by rw [(t κ q hκ hq).1]; exact hv
  obtain ⟨w, hw, e⟩ := this
  exact ⟨w, hw, e⟩

@[sa_ref_forward "MorphismsWellMixed.wellmixedUnitIic" 3]
theorem ref_fwd3 : T → S3 := by
  intro t σ κ q hκ hq w hw
  have : w ∈ wmMap1 (σ := σ) κ q ⁻¹' {v | v.1 ∈ Set.Ioc 0 q} := hw
  rw [(t κ q hκ hq).2] at this
  exact this

@[sa_complete "MorphismsWellMixed.wellmixedUnitIic"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := by
  intro σ κ q hκ hq
  refine ⟨?_, ?_⟩
  · ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact s1 κ q hκ hq w hw
    · intro hv
      obtain ⟨w, hw, e⟩ := s2 κ q hκ hq v hv
      exact ⟨w, hw, e⟩
  · ext w
    constructor
    · intro hw
      exact s3 κ q hκ hq w hw
    · intro hw
      exact s1 κ q hκ hq w hw

end Alignment.Shadows.MorphismsWellMixed.WellmixedUnitIic

/-! ## `MorphismsWellMixed.wellmixedUnitSolution`

Text (precise fragment): "solutions are mapped: `(θ, ξ, x) ↦ (qξe^{κ(θ−1)}, x)` (exits allowed)
and, for exit-free P, `(θ, x) ↦ (q e^{κ(θ−1)}, x)` map EB solutions to solutions of MA(c_κ P);
for exit-free P, `κ ≠ 0` and `q > 0` the inverse maps MA solutions that stay in `S > 0` (which
contains `S ∈ (0, q]`) back to solutions on `(θ; x)`." Design: §D.3 "semiconjugacies map
solution curves to solution curves". Three maps (conjunction), each for every T_EB model `P`
(exit-free where the text says so) and every set of times `I`:

1. `wmMap κ q` (all κ, q, exits allowed) maps solutions of `wmSys κ q P` on `I` to solutions of
   `maSys (wmTarget κ P)` on `I`;
2. `wmMap1 κ q` (exit-free `P`, all κ, q) maps solutions of `wmSys1 κ q P` on `I` to solutions
   of `maSys (wmTarget κ P)` on `I`;
3. `wmInv κ q` (exit-free `P`, `κ ≠ 0`, `q > 0`) maps solutions of `maSys (wmTarget κ P)` on `I`
   with `S > 0` at every `t ∈ I` to solutions of `wmSys1 κ q P` on `I`.

-- AMBIGUITY: "solution" is not fixed by the text. DataTypes §(f) gives two notions of a
-- solution on a set of times `I` (two-sided `HasDerivAt` at every `t ∈ I`, or
-- `HasDerivWithinAt … I t`), and DESIGN §M.5 says "Solutions are mapped" is meant for both
-- ("for M1 it covers (θ, ξ, x) ↦ (qξe^{κ(θ−1)}, x), the exit-free (θ, x) ↦ (q e^{κ(θ−1)}, x),
-- and the inverse on S > 0"). Both readings are asserted, one shadow per map and reading:
-- S1–S3 two-sided (`HasDerivAt`), S4–S6 within `I` (`HasDerivWithinAt`). Neither reading
-- implies the other.
-- The parenthesis "(which contains `S ∈ (0, q]`)" is the arithmetic fact `(0, q] ⊆ (0, ∞)`;
-- it mentions no model notion and has no shadow (it would be content-free). -/
namespace Alignment.Shadows.MorphismsWellMixed.WellmixedUnitSolution

/-- Reading "two-sided": map 1. -/
def At1 : Prop :=
  ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (κ q : ℝ) (P : List (Rxn σ)) (I : Set ℝ)
    (x : ℝ → WM σ),
    (∀ t ∈ I, HasDerivAt x ((wmSys κ q P).F (x t)) t) →
    ∀ t ∈ I, HasDerivAt (fun s => wmMap κ q (x s))
      ((maSys (wmTarget κ P)).F (wmMap κ q (x t))) t

/-- Reading "two-sided": map 2. -/
def At2 : Prop :=
  ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (κ q : ℝ) (P : List (Rxn σ)), ExitFree P →
    ∀ (I : Set ℝ) (w : ℝ → ℝ × (σ → ℝ)),
    (∀ t ∈ I, HasDerivAt w ((wmSys1 κ q P).F (w t)) t) →
    ∀ t ∈ I, HasDerivAt (fun s => wmMap1 κ q (w s))
      ((maSys (wmTarget κ P)).F (wmMap1 κ q (w t))) t

/-- Reading "two-sided": map 3 (the inverse, on MA solutions staying in `S > 0`). -/
def At3 : Prop :=
  ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (κ q : ℝ) (P : List (Rxn σ)), ExitFree P →
    κ ≠ 0 → 0 < q → ∀ (I : Set ℝ) (v : ℝ → MA σ),
    (∀ t ∈ I, 0 < (v t).1) →
    (∀ t ∈ I, HasDerivAt v ((maSys (wmTarget κ P)).F (v t)) t) →
    ∀ t ∈ I, HasDerivAt (fun s => wmInv κ q (v s)) ((wmSys1 κ q P).F (wmInv κ q (v t))) t

/-- Reading "within `I`": map 1. -/
def Within1 : Prop :=
  ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (κ q : ℝ) (P : List (Rxn σ)) (I : Set ℝ)
    (x : ℝ → WM σ),
    (∀ t ∈ I, HasDerivWithinAt x ((wmSys κ q P).F (x t)) I t) →
    ∀ t ∈ I, HasDerivWithinAt (fun s => wmMap κ q (x s))
      ((maSys (wmTarget κ P)).F (wmMap κ q (x t))) I t

/-- Reading "within `I`": map 2. -/
def Within2 : Prop :=
  ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (κ q : ℝ) (P : List (Rxn σ)), ExitFree P →
    ∀ (I : Set ℝ) (w : ℝ → ℝ × (σ → ℝ)),
    (∀ t ∈ I, HasDerivWithinAt w ((wmSys1 κ q P).F (w t)) I t) →
    ∀ t ∈ I, HasDerivWithinAt (fun s => wmMap1 κ q (w s))
      ((maSys (wmTarget κ P)).F (wmMap1 κ q (w t))) I t

/-- Reading "within `I`": map 3. -/
def Within3 : Prop :=
  ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (κ q : ℝ) (P : List (Rxn σ)), ExitFree P →
    κ ≠ 0 → 0 < q → ∀ (I : Set ℝ) (v : ℝ → MA σ),
    (∀ t ∈ I, 0 < (v t).1) →
    (∀ t ∈ I, HasDerivWithinAt v ((maSys (wmTarget κ P)).F (v t)) I t) →
    ∀ t ∈ I, HasDerivWithinAt (fun s => wmInv κ q (v s))
      ((wmSys1 κ q P).F (wmInv κ q (v t))) I t

@[sa_reference "MorphismsWellMixed.wellmixedUnitSolution"]
def T : Prop := (At1 ∧ At2 ∧ At3) ∧ (Within1 ∧ Within2 ∧ Within3)

/-- S1: with exits, `wmMap` maps (two-sided) solutions of the well-mixed EB model on any `I` to
solutions of MA(c_κ P) on `I`. -/
@[sa_shadow "MorphismsWellMixed.wellmixedUnitSolution" 1]
def S1 : Prop := At1

/-- S2: exit-free, `wmMap1` maps (two-sided) solutions on `(θ; x)` to solutions of MA(c_κ P). -/
@[sa_shadow "MorphismsWellMixed.wellmixedUnitSolution" 2]
def S2 : Prop := At2

/-- S3: exit-free, `κ ≠ 0`, `q > 0`: `wmInv` maps (two-sided) MA solutions staying in `S > 0`
back to solutions on `(θ; x)`. -/
@[sa_shadow "MorphismsWellMixed.wellmixedUnitSolution" 3]
def S3 : Prop := At3

/-- S4: as S1, for solutions within `I` (one-sided at end points of `I`). -/
@[sa_shadow "MorphismsWellMixed.wellmixedUnitSolution" 4]
def S4 : Prop := Within1

/-- S5: as S2, for solutions within `I`. -/
@[sa_shadow "MorphismsWellMixed.wellmixedUnitSolution" 5]
def S5 : Prop := Within2

/-- S6: as S3, for solutions within `I`. -/
@[sa_shadow "MorphismsWellMixed.wellmixedUnitSolution" 6]
def S6 : Prop := Within3

@[sa_ref_forward "MorphismsWellMixed.wellmixedUnitSolution" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1.1
@[sa_ref_forward "MorphismsWellMixed.wellmixedUnitSolution" 2]
theorem ref_fwd2 : T → S2 := fun t => t.1.2.1
@[sa_ref_forward "MorphismsWellMixed.wellmixedUnitSolution" 3]
theorem ref_fwd3 : T → S3 := fun t => t.1.2.2
@[sa_ref_forward "MorphismsWellMixed.wellmixedUnitSolution" 4]
theorem ref_fwd4 : T → S4 := fun t => t.2.1
@[sa_ref_forward "MorphismsWellMixed.wellmixedUnitSolution" 5]
theorem ref_fwd5 : T → S5 := fun t => t.2.2.1
@[sa_ref_forward "MorphismsWellMixed.wellmixedUnitSolution" 6]
theorem ref_fwd6 : T → S6 := fun t => t.2.2.2

@[sa_complete "MorphismsWellMixed.wellmixedUnitSolution"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) : T :=
  ⟨⟨s1, s2, s3⟩, ⟨s4, s5, s6⟩⟩

end Alignment.Shadows.MorphismsWellMixed.WellmixedUnitSolution

/-! ## `MorphismsWellMixed.wmDApply`

Text: "`wmD κ q u v = (q e^{κ(θ−1)} v_ξ + qξκ e^{κ(θ−1)} v_θ, v_x)`", with `u = (θ, ξ, x)` and
`v = (v_θ, v_ξ, v_x)`. One shadow per component of the pair. -/
namespace Alignment.Shadows.MorphismsWellMixed.WmDApply

@[sa_reference "MorphismsWellMixed.wmDApply"]
def T : Prop :=
  ∀ {σ : Type} (κ q : ℝ) (u v : WM σ),
    wmD κ q u v = (q * Real.exp (κ * (u.1 - 1)) * v.2.1 +
      q * u.2.1 * κ * Real.exp (κ * (u.1 - 1)) * v.1, v.2.2)

/-- S1: the `S`-component. -/
@[sa_shadow "MorphismsWellMixed.wmDApply" 1]
def S1 : Prop :=
  ∀ {σ : Type} (κ q : ℝ) (u v : WM σ),
    (wmD κ q u v).1 = q * Real.exp (κ * (u.1 - 1)) * v.2.1 +
      q * u.2.1 * κ * Real.exp (κ * (u.1 - 1)) * v.1

/-- S2: the `x`-component is `v_x`. -/
@[sa_shadow "MorphismsWellMixed.wmDApply" 2]
def S2 : Prop := ∀ {σ : Type} (κ q : ℝ) (u v : WM σ), (wmD κ q u v).2 = v.2.2

@[sa_ref_forward "MorphismsWellMixed.wmDApply" 1]
theorem ref_fwd1 : T → S1 := by
  intro t σ κ q u v; rw [t κ q u v]
@[sa_ref_forward "MorphismsWellMixed.wmDApply" 2]
theorem ref_fwd2 : T → S2 := by
  intro t σ κ q u v; rw [t κ q u v]

@[sa_complete "MorphismsWellMixed.wmDApply"]
theorem complete (s1 : S1) (s2 : S2) : T := by
  intro σ κ q u v
  exact Prod.ext (s1 κ q u v) (s2 κ q u v)

end Alignment.Shadows.MorphismsWellMixed.WmDApply

/-! ## `MorphismsWellMixed.hasFDerivAtWmMap`

Text: "`wmMap κ q` has derivative `wmD κ q u` at every `u`." (all κ, q; `Fintype σ` is needed
for the normed structure on `σ → ℝ`). A single atomic requirement. -/
namespace Alignment.Shadows.MorphismsWellMixed.HasFDerivAtWmMap

@[sa_reference "MorphismsWellMixed.hasFDerivAtWmMap"]
def T : Prop :=
  ∀ {σ : Type} [Fintype σ] (κ q : ℝ) (u : WM σ), HasFDerivAt (wmMap κ q) (wmD κ q u) u

@[sa_shadow "MorphismsWellMixed.hasFDerivAtWmMap" 1]
def S1 : Prop :=
  ∀ {σ : Type} [Fintype σ] (κ q : ℝ) (u : WM σ), HasFDerivAt (wmMap κ q) (wmD κ q u) u

@[sa_ref_forward "MorphismsWellMixed.hasFDerivAtWmMap" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MorphismsWellMixed.hasFDerivAtWmMap"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MorphismsWellMixed.HasFDerivAtWmMap

/-! ## `MorphismsWellMixed.wmFieldEq`

Text: "The derivative of `wmMap` carries the well-mixed EB field of each T_EB reaction `r` to the
mass-action field of `c_κ r`." The derivative is the Fréchet derivative
`fderiv ℝ (wmMap κ q) u`; the well-mixed field of `r` is `wmField κ q r`; `c_κ r` as T_net
syntax is `(r.scaleContacts κ).toNRxn`; its mass-action field is `maField`, evaluated at the
image state `wmMap κ q u` (a field identity `Dπ(u)·F(u) = G(π(u))`, DESIGN §D.3). All κ, q and
all states `u`. "Each T_EB reaction" is split along the four T_EB types (contact, exit,
progression `X → Y`, removal `X → ∅`).
-- AMBIGUITY: "the derivative of wmMap" is read as the true derivative `fderiv`, not the
-- explicit linear map `wmD` (which is only *intended* as the derivative). -/
namespace Alignment.Shadows.MorphismsWellMixed.WmFieldEq

@[sa_reference "MorphismsWellMixed.wmFieldEq"]
def T : Prop :=
  ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (κ q : ℝ) (r : Rxn σ) (u : WM σ),
    fderiv ℝ (wmMap κ q) u (wmField κ q r u) =
      maField (r.scaleContacts κ).toNRxn (wmMap κ q u)

/-- S1: contacts `s + J → X + J`. -/
@[sa_shadow "MorphismsWellMixed.wmFieldEq" 1]
def S1 : Prop :=
  ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (κ q : ℝ) (J X : σ) (τ : ℝ) (u : WM σ),
    fderiv ℝ (wmMap κ q) u (wmField κ q (Rxn.contact J X τ) u) =
      maField ((Rxn.contact J X τ).scaleContacts κ).toNRxn (wmMap κ q u)

/-- S2: exits `s → Y`. -/
@[sa_shadow "MorphismsWellMixed.wmFieldEq" 2]
def S2 : Prop :=
  ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (κ q : ℝ) (Y : σ) (ν : ℝ) (u : WM σ),
    fderiv ℝ (wmMap κ q) u (wmField κ q (Rxn.exit Y ν) u) =
      maField ((Rxn.exit Y ν).scaleContacts κ).toNRxn (wmMap κ q u)

/-- S3: progressions `X → Y`. -/
@[sa_shadow "MorphismsWellMixed.wmFieldEq" 3]
def S3 : Prop :=
  ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (κ q : ℝ) (X Y : σ) (a : ℝ) (u : WM σ),
    fderiv ℝ (wmMap κ q) u (wmField κ q (Rxn.trans X (some Y) a) u) =
      maField ((Rxn.trans X (some Y) a).scaleContacts κ).toNRxn (wmMap κ q u)

/-- S4: removals `X → ∅`. -/
@[sa_shadow "MorphismsWellMixed.wmFieldEq" 4]
def S4 : Prop :=
  ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (κ q : ℝ) (X : σ) (a : ℝ) (u : WM σ),
    fderiv ℝ (wmMap κ q) u (wmField κ q (Rxn.trans X none a) u) =
      maField ((Rxn.trans X none a).scaleContacts κ).toNRxn (wmMap κ q u)

@[sa_ref_forward "MorphismsWellMixed.wmFieldEq" 1]
theorem ref_fwd1 : T → S1 := by
  intro t σ _ _ κ q J X τ u; exact t κ q (Rxn.contact J X τ) u
@[sa_ref_forward "MorphismsWellMixed.wmFieldEq" 2]
theorem ref_fwd2 : T → S2 := by
  intro t σ _ _ κ q Y ν u; exact t κ q (Rxn.exit Y ν) u
@[sa_ref_forward "MorphismsWellMixed.wmFieldEq" 3]
theorem ref_fwd3 : T → S3 := by
  intro t σ _ _ κ q X Y a u; exact t κ q (Rxn.trans X (some Y) a) u
@[sa_ref_forward "MorphismsWellMixed.wmFieldEq" 4]
theorem ref_fwd4 : T → S4 := by
  intro t σ _ _ κ q X a u; exact t κ q (Rxn.trans X none a) u

@[sa_complete "MorphismsWellMixed.wmFieldEq"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := by
  intro σ _ _ κ q r u
  cases r with
  | contact J X τ => exact s1 κ q J X τ u
  | exit Y ν => exact s2 κ q Y ν u
  | trans X Y a =>
    cases Y with
    | some Y => exact s3 κ q X Y a u
    | none => exact s4 κ q X a u

end Alignment.Shadows.MorphismsWellMixed.WmFieldEq

/-! ## `MorphismsWellMixed.wmLiftXiEqZero`

Text: "Without exits the ξ-component of the well-mixed field vanishes." For every exit-free
list, all κ, q and every state, `(wmLift κ q rs u).2.1 = 0`. -/
namespace Alignment.Shadows.MorphismsWellMixed.WmLiftXiEqZero

@[sa_reference "MorphismsWellMixed.wmLiftXiEqZero"]
def T : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (κ q : ℝ) (rs : List (Rxn σ)), ExitFree rs →
    ∀ u : WM σ, (wmLift κ q rs u).2.1 = 0

@[sa_shadow "MorphismsWellMixed.wmLiftXiEqZero" 1]
def S1 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (κ q : ℝ) (rs : List (Rxn σ)), ExitFree rs →
    ∀ u : WM σ, (wmLift κ q rs u).2.1 = 0

@[sa_ref_forward "MorphismsWellMixed.wmLiftXiEqZero" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MorphismsWellMixed.wmLiftXiEqZero"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MorphismsWellMixed.WmLiftXiEqZero

/-! ## `MorphismsWellMixed.wmSys1Incl`

Text: "For an exit-free model, `(θ, x) ↦ (θ, 1, x)` is a semiconjugacy from `wmSys1` to
`wmSys`". All κ, q. A semiconjugacy (DESIGN §D.3) = differentiable ∧ field identity. The
differentiability of the inclusion alone mentions no trusted notion (it would be a
content-free shadow), so the two conjuncts are kept together in one shadow, stated
primitively over the two systems. -/
namespace Alignment.Shadows.MorphismsWellMixed.WmSys1Incl

@[sa_reference "MorphismsWellMixed.wmSys1Incl"]
def T : Prop :=
  ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (κ q : ℝ) (rs : List (Rxn σ)), ExitFree rs →
    Differentiable ℝ (inclXi1 (σ := σ)) ∧
    ∀ w : ℝ × (σ → ℝ), fderiv ℝ inclXi1 w ((wmSys1 κ q rs).F w) = (wmSys κ q rs).F (inclXi1 w)

@[sa_shadow "MorphismsWellMixed.wmSys1Incl" 1]
def S1 : Prop :=
  ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (κ q : ℝ) (rs : List (Rxn σ)), ExitFree rs →
    Differentiable ℝ (inclXi1 (σ := σ)) ∧
    ∀ w : ℝ × (σ → ℝ), fderiv ℝ inclXi1 w ((wmSys1 κ q rs).F w) = (wmSys κ q rs).F (inclXi1 w)

@[sa_ref_forward "MorphismsWellMixed.wmSys1Incl" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MorphismsWellMixed.wmSys1Incl"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MorphismsWellMixed.WmSys1Incl
