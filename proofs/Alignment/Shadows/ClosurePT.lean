import Alignment.Registry
import NetworkEpi.Closure.PT

/-!
# Blind shadows for group `ClosurePT` (module `NetworkEpi.Closure.PT`, DESIGN §D.5 M8, §D.7 L4d)

Written blind: the author read only `SA-PASS_SKILL.md`, `Alignment/README.md`,
`Alignment/Example/ExampleShadows.lean`, `Alignment/DataTypes/ClosurePT.md`, the `ClosurePT.*`
entries of `Alignment/claims_blind.yaml` and `DESIGN_NetworkEpiCore.md` (§0, §C.1, §D.5 M6/M8,
§D.7 L4d, §L.3).

Conventions taken from the texts.

* "ψ" with its derivatives ψ', ψ'' is represented by a configuration-network record `N : CNet`
  (fields `N.ψ`, `N.ψ'`, `N.ψ''`, which are free functions, DataTypes (b)). A `CNet` is exactly a
  triple of real functions, so quantifying over `N : CNet` is quantifying over all ψ, ψ', ψ''.
  The relations "ψ' is the derivative of ψ within I" and "ψ'' is the derivative of ψ' within I"
  are stated with `HasDerivWithinAt` at every point of `I` (module header: "derivatives are taken
  within I, so one-sided derivatives at end points suffice"; DataTypes (e)).
* "Interval" (module header): "Intervals are convex sets with nonempty interior (for example
  `(0, 1]`, `[a, b]` with `a < b`, or an open interval)": `Convex ℝ I ∧ (interior I).Nonempty`.
* "PT on I" (DESIGN §0 "A degree PGF ψ is PT if ψ' = αψ^κ"; DataTypes (e)):
  `∃ α, ∀ x ∈ I, ψ' x = α * ψ x ^ κ` with the real power `Real.rpow`.
* "K_ψ" (M6: "K_ψ = ψψ''/ψ'²") is the operation under test `N.closureK`.
-/

open NEP

namespace Alignment.Shadows.ClosurePT

/-- An interval in the module's sense: a convex set with nonempty interior. -/
def IsInterval (I : Set ℝ) : Prop := Convex ℝ I ∧ (interior I).Nonempty

end Alignment.Shadows.ClosurePT

/-! ## `ClosurePT.ptIffConstClosure`

Text: "PT ⇔ constant closure | On an interval I with ψ > 0: K_ψ ≡ κ ⇔ ψ' = αψ^κ. [...]" and the
§D.7 L4d statement "`(∀ x ∈ I, ψ x * ψ'' x = κ * ψ' x ^ 2) ↔ ∃ α, ∀ x ∈ I, ψ' x = α * ψ x ^ κ`
(with ψ > 0 on I; ...)"; "an analytic statement about ψ on I"; "(both directions, product form of
the design's §D.7 table)".

Formalised for every ψ (every `CNet`), every interval I and every real κ, with ψ > 0 on I and ψ',
ψ'' the derivatives within I (the text's "ψ'" and "ψ''" are derivatives of ψ). The iff is split
into its two directions.
-- AMBIGUITY: the design statement writes the closure as "K_ψ ≡ κ" (ratio form), the Lean
-- statement says "product form of the design's §D.7 table"; the claim is read in product form
-- `ψ ψ'' = κ ψ'²` (the ratio form is claim `ClosurePT.ptIffClosureK`).
-/

namespace Alignment.Shadows.ClosurePT.PtIffConstClosure

open Alignment.Shadows.ClosurePT

/-- Intended statement: on an interval with ψ > 0 (and ψ', ψ'' its derivatives within I), the
product-form constant closure `ψψ'' = κψ'²` on I holds iff ψ is PT with exponent κ on I. -/
@[sa_reference "ClosurePT.ptIffConstClosure"]
def T : Prop :=
  ∀ (N : CNet) (I : Set ℝ) (κ : ℝ), IsInterval I →
    (∀ x ∈ I, 0 < N.ψ x) →
    (∀ x ∈ I, HasDerivWithinAt N.ψ (N.ψ' x) I x) →
    (∀ x ∈ I, HasDerivWithinAt N.ψ' (N.ψ'' x) I x) →
    ((∀ x ∈ I, N.ψ x * N.ψ'' x = κ * N.ψ' x ^ 2) ↔ ∃ α : ℝ, ∀ x ∈ I, N.ψ' x = α * N.ψ x ^ κ)

/-- S1 (⇒): constant closure (product form) on I implies PT with exponent κ on I. -/
@[sa_shadow "ClosurePT.ptIffConstClosure" 1]
def S1 : Prop :=
  ∀ (N : CNet) (I : Set ℝ) (κ : ℝ), IsInterval I →
    (∀ x ∈ I, 0 < N.ψ x) →
    (∀ x ∈ I, HasDerivWithinAt N.ψ (N.ψ' x) I x) →
    (∀ x ∈ I, HasDerivWithinAt N.ψ' (N.ψ'' x) I x) →
    (∀ x ∈ I, N.ψ x * N.ψ'' x = κ * N.ψ' x ^ 2) → ∃ α : ℝ, ∀ x ∈ I, N.ψ' x = α * N.ψ x ^ κ

/-- S2 (⇐): PT with exponent κ on I implies constant closure (product form) on I. -/
@[sa_shadow "ClosurePT.ptIffConstClosure" 2]
def S2 : Prop :=
  ∀ (N : CNet) (I : Set ℝ) (κ : ℝ), IsInterval I →
    (∀ x ∈ I, 0 < N.ψ x) →
    (∀ x ∈ I, HasDerivWithinAt N.ψ (N.ψ' x) I x) →
    (∀ x ∈ I, HasDerivWithinAt N.ψ' (N.ψ'' x) I x) →
    (∃ α : ℝ, ∀ x ∈ I, N.ψ' x = α * N.ψ x ^ κ) → ∀ x ∈ I, N.ψ x * N.ψ'' x = κ * N.ψ' x ^ 2

@[sa_ref_forward "ClosurePT.ptIffConstClosure" 1]
theorem ref_fwd1 : T → S1 := fun t N I κ hI hpos h1 h2 => (t N I κ hI hpos h1 h2).mp

@[sa_ref_forward "ClosurePT.ptIffConstClosure" 2]
theorem ref_fwd2 : T → S2 := fun t N I κ hI hpos h1 h2 => (t N I κ hI hpos h1 h2).mpr

@[sa_complete "ClosurePT.ptIffConstClosure"]
theorem complete (s1 : S1) (s2 : S2) : T := fun N I κ hI hpos h1 h2 =>
  ⟨s1 N I κ hI hpos h1 h2, s2 N I κ hI hpos h1 h2⟩

end Alignment.Shadows.ClosurePT.PtIffConstClosure

/-! ## `ClosurePT.ptIffClosureK`

Text: "PT ⇔ K_ψ ≡ κ in ratio form (M8). Design statement ...: "On an interval I with ψ > 0:
K_ψ ≡ κ ⇔ ψ' = αψ^κ"; M6: "K_ψ = ψψ''/ψ'²". [...] (the ratio form `K_ψ = ψψ''/ψ'² ≡ κ`, where
ψ' ≠ 0)".

Formalised for every ψ (`CNet`), interval I and κ, with ψ > 0 on I, ψ', ψ'' the derivatives
within I, and ψ' ≠ 0 on I; `K_ψ` is `N.closureK`. Split into the two directions.
-- AMBIGUITY: "where ψ' ≠ 0" is read as a hypothesis on the whole interval (the ratio K_ψ is
-- defined on I), not as "K_ψ ≡ κ at the points of I where ψ' ≠ 0" with no hypothesis.
-/

namespace Alignment.Shadows.ClosurePT.PtIffClosureK

open Alignment.Shadows.ClosurePT

/-- Intended statement: on an interval with ψ > 0 and ψ' ≠ 0 (ψ', ψ'' the derivatives within
I), `K_ψ ≡ κ` on I iff ψ is PT with exponent κ on I. -/
@[sa_reference "ClosurePT.ptIffClosureK"]
def T : Prop :=
  ∀ (N : CNet) (I : Set ℝ) (κ : ℝ), IsInterval I →
    (∀ x ∈ I, 0 < N.ψ x) →
    (∀ x ∈ I, HasDerivWithinAt N.ψ (N.ψ' x) I x) →
    (∀ x ∈ I, HasDerivWithinAt N.ψ' (N.ψ'' x) I x) →
    (∀ x ∈ I, N.ψ' x ≠ 0) →
    ((∀ x ∈ I, N.closureK x = κ) ↔ ∃ α : ℝ, ∀ x ∈ I, N.ψ' x = α * N.ψ x ^ κ)

/-- S1 (⇒): `K_ψ ≡ κ` on I implies PT with exponent κ on I. -/
@[sa_shadow "ClosurePT.ptIffClosureK" 1]
def S1 : Prop :=
  ∀ (N : CNet) (I : Set ℝ) (κ : ℝ), IsInterval I →
    (∀ x ∈ I, 0 < N.ψ x) →
    (∀ x ∈ I, HasDerivWithinAt N.ψ (N.ψ' x) I x) →
    (∀ x ∈ I, HasDerivWithinAt N.ψ' (N.ψ'' x) I x) →
    (∀ x ∈ I, N.ψ' x ≠ 0) →
    (∀ x ∈ I, N.closureK x = κ) → ∃ α : ℝ, ∀ x ∈ I, N.ψ' x = α * N.ψ x ^ κ

/-- S2 (⇐): PT with exponent κ on I implies `K_ψ ≡ κ` on I. -/
@[sa_shadow "ClosurePT.ptIffClosureK" 2]
def S2 : Prop :=
  ∀ (N : CNet) (I : Set ℝ) (κ : ℝ), IsInterval I →
    (∀ x ∈ I, 0 < N.ψ x) →
    (∀ x ∈ I, HasDerivWithinAt N.ψ (N.ψ' x) I x) →
    (∀ x ∈ I, HasDerivWithinAt N.ψ' (N.ψ'' x) I x) →
    (∀ x ∈ I, N.ψ' x ≠ 0) →
    (∃ α : ℝ, ∀ x ∈ I, N.ψ' x = α * N.ψ x ^ κ) → ∀ x ∈ I, N.closureK x = κ

@[sa_ref_forward "ClosurePT.ptIffClosureK" 1]
theorem ref_fwd1 : T → S1 := fun t N I κ hI hpos h1 h2 hne => (t N I κ hI hpos h1 h2 hne).mp

@[sa_ref_forward "ClosurePT.ptIffClosureK" 2]
theorem ref_fwd2 : T → S2 := fun t N I κ hI hpos h1 h2 hne => (t N I κ hI hpos h1 h2 hne).mpr

@[sa_complete "ClosurePT.ptIffClosureK"]
theorem complete (s1 : S1) (s2 : S2) : T := fun N I κ hI hpos h1 h2 hne =>
  ⟨s1 N I κ hI hpos h1 h2 hne, s2 N I κ hI hpos h1 h2 hne⟩

end Alignment.Shadows.ClosurePT.PtIffClosureK

/-! ## `ClosurePT.ptClosureAtOne`

Text (after remediation): "The PT constants at θ = 1 (M8), with `α = ψ'(1)` unconditional.
Design statement (DESIGN_NetworkEpiCore.md §D.5, M8): "So NBM's constant closure ⟨k(k−1)⟩/⟨k⟩² is
exact **iff** the degree distribution is PT"; §C.1: "closure_constant(d) # K_ψ(1) = ψ''(1)/ψ'(1)²
(NBM's heterogeneous constant closure)". [...] if moreover `1 ∈ I` and `ψ(1) = 1`, the constants
are `α = ψ'(1)` and `κ = ψ''(1)/ψ'(1)²` (the value of NBM's constant closure,
`closure_constant(d)`); the value of κ, and `K_ψ(1)` itself, need `ψ'(1) ≠ 0`".

Premise (the "PT constants" of the M8 setting, DESIGN §D.5 M8: "On an interval I with ψ > 0:
K_ψ ≡ κ ⇔ ψ' = αψ^κ"): ψ is PT on the interval I with constants α, κ
(`∀ x ∈ I, ψ' x = α * ψ x ^ κ`), ψ > 0 on I, ψ', ψ'' the derivatives within I; "moreover" 1 ∈ I
and ψ(1) = 1. Conclusions, one shadow each:
* S1 `α = ψ'(1)`, "unconditional": no proviso ψ'(1) ≠ 0;
* S2 `κ = ψ''(1)/ψ'(1)²`, under ψ'(1) ≠ 0 ("the value of κ ... need[s] ψ'(1) ≠ 0");
* S3 κ is the value of NBM's constant closure `K_ψ(1)` (`N.closureK 1`, §C.1), under ψ'(1) ≠ 0
  ("`K_ψ(1)` itself need[s] ψ'(1) ≠ 0").
-- AMBIGUITY: "unconditional" is read relative to the only condition the sentence names,
-- `ψ'(1) ≠ 0`: the α conclusion keeps the M8 premise (interval, ψ > 0, ψ', ψ'' derivatives
-- within I, PT with constants α κ, 1 ∈ I, ψ(1) = 1) but has no `ψ'(1) ≠ 0` proviso.
-- AMBIGUITY: "if moreover" continues a premise not quoted; it is read as the M8 setting: the PT
-- relation with given constants α, κ (the "PT constants" of the title) on an interval with ψ > 0
-- and ψ', ψ'' the derivatives of ψ, ψ' within I (module header convention).
-/

namespace Alignment.Shadows.ClosurePT.PtClosureAtOne

open Alignment.Shadows.ClosurePT

/-- The common premise: ψ PT on the interval I with constants α, κ, ψ > 0 on I, ψ', ψ'' the
derivatives within I, `1 ∈ I` and `ψ(1) = 1`. -/
def Premise (N : CNet) (I : Set ℝ) (α κ : ℝ) : Prop :=
  IsInterval I ∧ (∀ x ∈ I, 0 < N.ψ x) ∧
    (∀ x ∈ I, HasDerivWithinAt N.ψ (N.ψ' x) I x) ∧
    (∀ x ∈ I, HasDerivWithinAt N.ψ' (N.ψ'' x) I x) ∧
    (∀ x ∈ I, N.ψ' x = α * N.ψ x ^ κ) ∧ (1 : ℝ) ∈ I ∧ N.ψ 1 = 1

/-- Intended statement: under the premise, `α = ψ'(1)` (no further condition); and, when
`ψ'(1) ≠ 0`, `κ = ψ''(1)/ψ'(1)²` and `κ = K_ψ(1)` (NBM's constant closure). -/
@[sa_reference "ClosurePT.ptClosureAtOne"]
def T : Prop :=
  ∀ (N : CNet) (I : Set ℝ) (α κ : ℝ), Premise N I α κ →
    α = N.ψ' 1 ∧
      (N.ψ' 1 ≠ 0 → κ = N.ψ'' 1 / N.ψ' 1 ^ 2) ∧
      (N.ψ' 1 ≠ 0 → κ = N.closureK 1)

/-- S1: the PT coefficient is `α = ψ'(1)`, with no proviso `ψ'(1) ≠ 0` ("unconditional"). -/
@[sa_shadow "ClosurePT.ptClosureAtOne" 1]
def S1 : Prop :=
  ∀ (N : CNet) (I : Set ℝ) (α κ : ℝ), Premise N I α κ → α = N.ψ' 1

/-- S2: the PT exponent is `κ = ψ''(1)/ψ'(1)²` (when ψ'(1) ≠ 0). -/
@[sa_shadow "ClosurePT.ptClosureAtOne" 2]
def S2 : Prop :=
  ∀ (N : CNet) (I : Set ℝ) (α κ : ℝ), Premise N I α κ →
    N.ψ' 1 ≠ 0 → κ = N.ψ'' 1 / N.ψ' 1 ^ 2

/-- S3: the PT exponent is the value of NBM's constant closure `K_ψ(1)` (when ψ'(1) ≠ 0). -/
@[sa_shadow "ClosurePT.ptClosureAtOne" 3]
def S3 : Prop :=
  ∀ (N : CNet) (I : Set ℝ) (α κ : ℝ), Premise N I α κ →
    N.ψ' 1 ≠ 0 → κ = N.closureK 1

@[sa_ref_forward "ClosurePT.ptClosureAtOne" 1]
theorem ref_fwd1 : T → S1 := fun t N I α κ hp => (t N I α κ hp).1

@[sa_ref_forward "ClosurePT.ptClosureAtOne" 2]
theorem ref_fwd2 : T → S2 := fun t N I α κ hp => (t N I α κ hp).2.1

@[sa_ref_forward "ClosurePT.ptClosureAtOne" 3]
theorem ref_fwd3 : T → S3 := fun t N I α κ hp => (t N I α κ hp).2.2

@[sa_complete "ClosurePT.ptClosureAtOne"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := fun N I α κ hp =>
  ⟨s1 N I α κ hp, s2 N I α κ hp, s3 N I α κ hp⟩

end Alignment.Shadows.ClosurePT.PtClosureAtOne

/-! ## `ClosurePT.poissonClosureK`

Text: "The Poisson PGF is of Poisson type with κ = 1 (M8, Poisson instance). Design statement
(DESIGN_NetworkEpiCore.md §0): "Poisson type (PT). A degree PGF ψ is PT if ψ' = αψ^κ. This covers
Poisson (κ = 1)". [...] the Poisson PGF is PT with `α = μ`, `κ = 1`."

"Poisson PGF" is `CNet.poisson μ`; "PT with α = μ, κ = 1" is `ψ' x = μ * ψ x ^ (1 : ℝ)` (real
power, DataTypes (e)). No interval or sign condition on μ is stated, so the relation is asked for
every real μ and at every real x (hence on every interval).
-/

namespace Alignment.Shadows.ClosurePT.PoissonClosureK

/-- Intended statement: for every μ, the Poisson(μ) PGF satisfies `ψ' = μ ψ^1` everywhere. -/
@[sa_reference "ClosurePT.poissonClosureK"]
def T : Prop :=
  ∀ (μ x : ℝ), (CNet.poisson μ).ψ' x = μ * (CNet.poisson μ).ψ x ^ (1 : ℝ)

/-- S1: the whole statement (one atomic requirement: PT with the constants α = μ, κ = 1). -/
@[sa_shadow "ClosurePT.poissonClosureK" 1]
def S1 : Prop :=
  ∀ (μ x : ℝ), (CNet.poisson μ).ψ' x = μ * (CNet.poisson μ).ψ x ^ (1 : ℝ)

@[sa_ref_forward "ClosurePT.poissonClosureK" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "ClosurePT.poissonClosureK"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.ClosurePT.PoissonClosureK

/-! ## `ClosurePT.hasDerivWithinAtPtQuotient`

Text: "The derivative of `ψ'ψ^{−κ}` within `I`, when ψ > 0 at `x`:
`ψ''ψ^{−κ} − κψ'²ψ^{−κ−1} = ψ^{−κ−1}(ψψ'' − κψ'²)`."

Formalised for every ψ (`CNet`), every set I, every point x and every real κ: if ψ(x) > 0, ψ has
derivative ψ'(x) within I at x and ψ' has derivative ψ''(x) within I at x, then `y ↦ ψ'(y)ψ(y)^{−κ}`
has derivative within I at x equal to each of the two displayed expressions (the text's `=` chain
is split: S1 the expanded form, S2 the factored form).
-- AMBIGUITY: the text puts no condition on I and does not require x ∈ I; I is taken to be an
-- arbitrary set of reals (the module's interval convention is not needed for a pointwise
-- derivative computation and is not mentioned in this sentence).
-/

namespace Alignment.Shadows.ClosurePT.HasDerivWithinAtPtQuotient

/-- The common hypotheses: ψ(x) > 0 and ψ', ψ'' are the derivatives of ψ, ψ' within I at x. -/
def Hyp (N : CNet) (I : Set ℝ) (x : ℝ) : Prop :=
  0 < N.ψ x ∧ HasDerivWithinAt N.ψ (N.ψ' x) I x ∧ HasDerivWithinAt N.ψ' (N.ψ'' x) I x

/-- Intended statement: the derivative of `ψ'ψ^{−κ}` within I at x is
`ψ''ψ^{−κ} − κψ'²ψ^{−κ−1}` and also `ψ^{−κ−1}(ψψ'' − κψ'²)`. -/
@[sa_reference "ClosurePT.hasDerivWithinAtPtQuotient"]
def T : Prop :=
  ∀ (N : CNet) (I : Set ℝ) (x κ : ℝ), Hyp N I x →
    HasDerivWithinAt (fun y => N.ψ' y * N.ψ y ^ (-κ))
        (N.ψ'' x * N.ψ x ^ (-κ) - κ * N.ψ' x ^ 2 * N.ψ x ^ (-κ - 1)) I x ∧
      HasDerivWithinAt (fun y => N.ψ' y * N.ψ y ^ (-κ))
        (N.ψ x ^ (-κ - 1) * (N.ψ x * N.ψ'' x - κ * N.ψ' x ^ 2)) I x

/-- S1: the derivative is the expanded form `ψ''ψ^{−κ} − κψ'²ψ^{−κ−1}`. -/
@[sa_shadow "ClosurePT.hasDerivWithinAtPtQuotient" 1]
def S1 : Prop :=
  ∀ (N : CNet) (I : Set ℝ) (x κ : ℝ), Hyp N I x →
    HasDerivWithinAt (fun y => N.ψ' y * N.ψ y ^ (-κ))
        (N.ψ'' x * N.ψ x ^ (-κ) - κ * N.ψ' x ^ 2 * N.ψ x ^ (-κ - 1)) I x

/-- S2: the derivative is the factored form `ψ^{−κ−1}(ψψ'' − κψ'²)`. -/
@[sa_shadow "ClosurePT.hasDerivWithinAtPtQuotient" 2]
def S2 : Prop :=
  ∀ (N : CNet) (I : Set ℝ) (x κ : ℝ), Hyp N I x →
    HasDerivWithinAt (fun y => N.ψ' y * N.ψ y ^ (-κ))
        (N.ψ x ^ (-κ - 1) * (N.ψ x * N.ψ'' x - κ * N.ψ' x ^ 2)) I x

@[sa_ref_forward "ClosurePT.hasDerivWithinAtPtQuotient" 1]
theorem ref_fwd1 : T → S1 := fun t N I x κ h => (t N I x κ h).1

@[sa_ref_forward "ClosurePT.hasDerivWithinAtPtQuotient" 2]
theorem ref_fwd2 : T → S2 := fun t N I x κ h => (t N I x κ h).2

@[sa_complete "ClosurePT.hasDerivWithinAtPtQuotient"]
theorem complete (s1 : S1) (s2 : S2) : T := fun N I x κ h => ⟨s1 N I x κ h, s2 N I x κ h⟩

end Alignment.Shadows.ClosurePT.HasDerivWithinAtPtQuotient
