import Alignment.Registry
import NetworkEpi

/-!
# Blind shadows — group `Docs`

Written blind from `Alignment/claims_blind.yaml`, `Alignment/DataTypes/Docs.md`,
`Alignment/README.md`, `Alignment/Example/ExampleShadows.lean` and the cited passage of
`proofs/README.md` (lines 48–52). Re-shadowed after the text remediation of the README passage.
-/

open NEP

namespace Alignment.Shadows.Docs.EdgeDefectWithRemovals

/-! ### `Docs.readme.edgeDefectWithRemovals`

Blind text: "For any reaction list, `d/dt (θ − φ_S − Σφ_X) = Σ_{(X→∅,a)∈rs} a φ_X`. A removal
leaves θ unchanged and lowers Σφ by aφ_X (the partner becomes inert: its edges stay in θ but
leave every φ class), so the rate is non-negative when the removal rates and the φ_X are
non-negative. Without removals the rate is 0."

Reading (one shadow per assertion).
* S1 "For any reaction list, `d/dt (θ − φ_S − Σφ_X) = Σ_{(X→∅,a)∈rs} a φ_X`": for every
  species type, every configuration network `N`, seed factor `q` and reaction list `rs` (no
  restriction on `rs`), along any curve that solves the EB model `lift N q rs` at time `t`, the
  edge defect `θ − φ_S − Σ_X φ_X` (with `φ_S = qξψ'(θ)/ψ'(1)`, `CNet.phiS`) has derivative
  `Σ_{(X → ∅, a) ∈ rs} a φ_X` at `t`. Differentiating `φ_S` needs `ψ''` to be the derivative of
  `ψ'`; this is assumed only at the point `θ(t)` where it is used (the text states no hypothesis;
  the README's surrounding prose says differentiating results assume `HasDerivAt` relations
  between ψ, ψ', ψ''). Stated pointwise in `t`, which covers solutions on any open interval.
* S2 "A removal leaves θ unchanged": the EB field of a removal `X → ∅` has zero θ-component.
* S3 "and lowers Σφ by aφ_X (… its edges stay in θ but leave every φ class)": the φ-components
  of the EB field of a removal `X → ∅` at rate `a` sum to `−a φ_X` (the edge mass leaves the φ
  classes altogether rather than moving between them).
* S4 "so the rate is non-negative when the removal rates and the φ_X are non-negative": for every
  reaction list, if every removal in it has rate `a ≥ 0` and every `φ_X ≥ 0`, then
  `Σ_{(X→∅,a)∈rs} a φ_X ≥ 0`. ("The rate" is the right-hand side of S1.)
* S5 "Without removals the rate is 0": if `rs` contains no removal `X → ∅`, then
  `Σ_{(X→∅,a)∈rs} a φ_X = 0` for every `φ`.

AMBIGUITY: "Σ_{(X→∅,a)∈rs}" — read as a sum over the list with multiplicity (a removal listed
twice contributes twice), consistent with the EB field of a list being the sum of per-reaction
fields.

The defect and the removal sum are written in primitive terms (not via `edgeDefect` /
`removalFlux`), so the shadows do not depend on those definitions' bodies.
-/

/-- The edge defect `θ − φ_S − Σ_X φ_X`, in primitive terms. -/
noncomputable def defect {σ : Type} [Fintype σ] (N : CNet) (q : ℝ) (u : EB σ) : ℝ :=
  u.1 - N.phiS q u.1 u.2.1 - ∑ X, u.2.2.1 X

/-- The contribution `a φ_X` of a removal `X → ∅` at rate `a`; zero for every other reaction. -/
noncomputable def remTerm {σ : Type} (φ : σ → ℝ) : Rxn σ → ℝ
  | .trans X none a => a * φ X
  | _ => 0

/-- `Σ_{(X → ∅, a) ∈ rs} a φ_X`, counted with multiplicity in the list. -/
noncomputable def remSum {σ : Type} (rs : List (Rxn σ)) (φ : σ → ℝ) : ℝ :=
  (rs.map (remTerm φ)).sum

/-- S1: for any reaction list, the edge-defect balance along EB solutions. -/
@[sa_shadow "Docs.readme.edgeDefectWithRemovals" 1]
def S1 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ))
    (x : ℝ → EB σ) (t : ℝ),
      HasDerivAt x (lift N q rs (x t)) t →
      HasDerivAt N.ψ' (N.ψ'' (x t).1) (x t).1 →
      HasDerivAt (fun s => defect N q (x s)) (remSum rs (x t).2.2.1) t

/-- S2: "A removal leaves θ unchanged": a removal's EB field has zero θ-component. -/
@[sa_shadow "Docs.readme.edgeDefectWithRemovals" 2]
def S2 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (X : σ) (a : ℝ) (u : EB σ),
    (ebField N q (Rxn.trans X none a) u).1 = 0

/-- S3: "lowers Σφ by aφ_X": a removal's φ-components sum to `−a φ_X`. -/
@[sa_shadow "Docs.readme.edgeDefectWithRemovals" 3]
def S3 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (X : σ) (a : ℝ) (u : EB σ),
    ∑ Y, (ebField N q (Rxn.trans X none a) u).2.2.1 Y = -(a * u.2.2.1 X)

/-- S4: the rate is `≥ 0` when the removal rates and the φ_X are non-negative. -/
@[sa_shadow "Docs.readme.edgeDefectWithRemovals" 4]
def S4 : Prop :=
  ∀ {σ : Type} (rs : List (Rxn σ)) (φ : σ → ℝ),
    (∀ (X : σ) (a : ℝ), Rxn.trans X none a ∈ rs → 0 ≤ a) →
    (∀ X, 0 ≤ φ X) →
    0 ≤ remSum rs φ

/-- S5: without removals the rate is 0. -/
@[sa_shadow "Docs.readme.edgeDefectWithRemovals" 5]
def S5 : Prop :=
  ∀ {σ : Type} (rs : List (Rxn σ)) (φ : σ → ℝ),
    (∀ (X : σ) (a : ℝ), Rxn.trans X none a ∉ rs) →
    remSum rs φ = 0

/-- Intended statement: the conjunction of the five assertions. -/
@[sa_reference "Docs.readme.edgeDefectWithRemovals"]
def T : Prop := S1 ∧ S2 ∧ S3 ∧ S4 ∧ S5

@[sa_ref_forward "Docs.readme.edgeDefectWithRemovals" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "Docs.readme.edgeDefectWithRemovals" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1

@[sa_ref_forward "Docs.readme.edgeDefectWithRemovals" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2.1

@[sa_ref_forward "Docs.readme.edgeDefectWithRemovals" 4]
theorem ref_fwd4 : T → S4 := fun t => t.2.2.2.1

@[sa_ref_forward "Docs.readme.edgeDefectWithRemovals" 5]
theorem ref_fwd5 : T → S5 := fun t => t.2.2.2.2

@[sa_complete "Docs.readme.edgeDefectWithRemovals"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) : T :=
  ⟨s1, s2, s3, s4, s5⟩

end Alignment.Shadows.Docs.EdgeDefectWithRemovals
