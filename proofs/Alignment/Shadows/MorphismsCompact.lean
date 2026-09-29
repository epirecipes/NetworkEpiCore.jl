import Alignment.Registry
import NetworkEpi.Morphisms.Compact

/-!
# Blind shadows: group `MorphismsCompact` (DESIGN §D.5 row M9, §D.3, amendment §L.2)

Written blind from `claims_blind.yaml` (ids `MorphismsCompact.*`), `DataTypes/MorphismsCompact.md`,
`Alignment/README.md`, `Example/ExampleShadows.lean` and `DESIGN_NetworkEpiCore.md` (§0, §D.3–§D.5,
§E.2, §L.2, §M.4). The ids `compactWInvariant`, `compactConj`, `compactSolution` and
`compactSolutionPoisson` were re-shadowed blind after the text remediation (§M.4).

Conventions used throughout (from DataTypes (e) and DESIGN §0/§D.4):
* expanded model: `ebSys N q (sirRxns τ γ)` on `EB SIRSp = (θ, ξ, φ, pop)`, with
  `u.1 = θ`, `u.2.1 = ξ`, `u.2.2.1 .I = φ_I`, `u.2.2.1 .R = φ_R`, `u.2.2.2 .I = pop_I`,
  `u.2.2.2 .R = pop_R`; `S = qξψ(θ)`, `φ_S = qξψ'(θ)/ψ'(1)`;
* compact model: `compactSIR N q τ γ` on `(θ, R) ∈ ℝ × ℝ`;
* the maps and sets that the claim text spells out by formula (the embedding, the projection,
  `W`, `W'`) are written below in primitive terms from the text, not through the library's
  `compactEmb`/`compactProj`/`compactW` (except where a claim names the library operation);
* "solution on a time interval `I`": `I` convex; derivatives within `I`
  (`HasDerivWithinAt … I t`, one-sided at end points), and where a conclusion is itself a
  derivative statement also the two-sided reading (`HasDerivAt`) as a separate shadow.
-/

open NEP

namespace Alignment.Shadows.MorphismsCompact

/-- A primitive SIRSp-indexed vector: `a` at `I`, `b` at `R`. -/
def sv (a b : ℝ) : SIRSp → ℝ := fun X =>
  match X with
  | .I => a
  | .R => b

/-- The design's set `W = {τφ_R + γθ = γ}` in `EB SIRSp` (DataTypes (e)). -/
def Wset (τ γ : ℝ) : Set (EB SIRSp) := {u | τ * u.2.2.1 .R + γ * u.1 = γ}

/-- The text's `W' = W ∩ {ξ = 1, θ = φ_S + φ_I + φ_R, S + pop_I + pop_R = 1}`, with
`φ_S = qξψ'(θ)/ψ'(1)` and `S = qξψ(θ)` (DESIGN §0), in primitive terms. -/
def Wp (N : CNet) (q τ γ : ℝ) : Set (EB SIRSp) :=
  {u | τ * u.2.2.1 .R + γ * u.1 = γ ∧ u.2.1 = 1 ∧
       u.1 = q * u.2.1 * N.ψ' u.1 / N.ψ' 1 + u.2.2.1 .I + u.2.2.1 .R ∧
       q * u.2.1 * N.ψ u.1 + u.2.2.2 .I + u.2.2.2 .R = 1}

/-- The text's embedding `(θ, R) ↦ (θ, 1, φ_I, φ_R, 1 − qψ(θ) − R, R)` with
`φ_R = γ(1−θ)/τ`, `φ_I = θ − qψ'(θ)/ψ'(1) − φ_R`, in primitive terms. -/
noncomputable def emb (N : CNet) (q τ γ : ℝ) (w : ℝ × ℝ) : EB SIRSp :=
  (w.1, 1,
    sv (w.1 - q * N.ψ' w.1 / N.ψ' 1 - γ * (1 - w.1) / τ) (γ * (1 - w.1) / τ),
    sv (1 - q * N.ψ w.1 - w.2) w.2)

/-- The text's projection `(θ, …, pop_R) ↦ (θ, pop_R)`. -/
def proj (u : EB SIRSp) : ℝ × ℝ := (u.1, u.2.2.2 .R)

/-- The design's initial condition (§D.4) for SIR seeded in its entry state `I` with fraction
`ρ`: `θ(0) = 1`, `ξ(0) = 1`, `φ_I(0) = pop_I(0) = ρ`, `φ_R(0) = pop_R(0) = 0`; the seed factor is
`q = 1 − ρ` (substituted into the models below). -/
def ic (ρ : ℝ) : EB SIRSp := (1, 1, sv ρ 0, sv ρ 0)

end Alignment.Shadows.MorphismsCompact

/-! ### `MorphismsCompact.sirVecApply` -/
namespace Alignment.Shadows.MorphismsCompact.SirVecApply

/-- Intended: `sirVec a b` is `a` at `I` and `b` at `R`. -/
@[sa_reference "MorphismsCompact.sirVecApply"]
def T : Prop := (∀ a b : ℝ, sirVec a b SIRSp.I = a) ∧ (∀ a b : ℝ, sirVec a b SIRSp.R = b)

@[sa_shadow "MorphismsCompact.sirVecApply" 1]
def S1 : Prop := ∀ a b : ℝ, sirVec a b SIRSp.I = a

@[sa_shadow "MorphismsCompact.sirVecApply" 2]
def S2 : Prop := ∀ a b : ℝ, sirVec a b SIRSp.R = b

@[sa_ref_forward "MorphismsCompact.sirVecApply" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "MorphismsCompact.sirVecApply" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "MorphismsCompact.sirVecApply"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.MorphismsCompact.SirVecApply

/-! ### `MorphismsCompact.compactWInvariant` (re-shadowed after text remediation)

Text: "along every EB SIR solution on a time interval, `τφ_R + γθ` is constant, so the design's
set `W = {τφ_R + γθ = γ}` is invariant (no assumption on ψ)." Design statement (§D.5, M9): "W =
{τφ_R + γθ = γ} is invariant for SIR-shaped P".
Two conjuncts: (S1) constancy of `τφ_R + γθ`, (S2) invariance of `W`. "Every EB SIR solution":
all `N : CNet` ("no assumption on ψ": no derivative or normalisation hypothesis), all seed
factors `q`, all rates `τ, γ`, every time interval `I` and every solution on it.
-- AMBIGUITY: "solution on a time interval" — `I` convex (an interval of ℝ, possibly closed or
-- degenerate) and the solution property read with derivatives within `I` (one-sided at end
-- points of `I`). This is the weakest hypothesis; the two-sided reading is a special case. -/
namespace Alignment.Shadows.MorphismsCompact.CompactWInvariant

open Alignment.Shadows.MorphismsCompact

/-- S1: `τφ_R + γθ` takes the same value at any two times of the interval. -/
@[sa_shadow "MorphismsCompact.compactWInvariant" 1]
def S1 : Prop :=
  ∀ (N : CNet) (q τ γ : ℝ) (I : Set ℝ) (x : ℝ → EB SIRSp), Convex ℝ I →
    (∀ t ∈ I, HasDerivWithinAt x ((ebSys N q (sirRxns τ γ)).F (x t)) I t) →
    ∀ s ∈ I, ∀ t ∈ I,
      τ * (x s).2.2.1 SIRSp.R + γ * (x s).1 = τ * (x t).2.2.1 SIRSp.R + γ * (x t).1

/-- S2: `W` is invariant: a solution that lies in `W` at one time of the interval lies in `W`
at every time of the interval. -/
@[sa_shadow "MorphismsCompact.compactWInvariant" 2]
def S2 : Prop :=
  ∀ (N : CNet) (q τ γ : ℝ) (I : Set ℝ) (x : ℝ → EB SIRSp), Convex ℝ I →
    (∀ t ∈ I, HasDerivWithinAt x ((ebSys N q (sirRxns τ γ)).F (x t)) I t) →
    ∀ s ∈ I, x s ∈ Wset τ γ → ∀ t ∈ I, x t ∈ Wset τ γ

@[sa_reference "MorphismsCompact.compactWInvariant"]
def T : Prop := S1 ∧ S2

@[sa_ref_forward "MorphismsCompact.compactWInvariant" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "MorphismsCompact.compactWInvariant" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "MorphismsCompact.compactWInvariant"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.MorphismsCompact.CompactWInvariant

/-! ### `MorphismsCompact.compactConj` (re-shadowed after text remediation)

Text: "the embedding `(θ, R) ↦ (θ, 1, φ_I, φ_R, 1 − qψ(θ) − R, R)` with `φ_R = γ(1−θ)/τ`,
`φ_I = θ − qψ'(θ)/ψ'(1) − φ_R` and the projection `(θ, …, pop_R) ↦ (θ, pop_R)` form a conjugacy
between the compact model and the expanded model restricted to
`W' = W ∩ {ξ = 1, θ = φ_S + φ_I + φ_R, S + pop_I + pop_R = 1}` (`τ ≠ 0`)."
The embedding, projection and `W'` are written from the text's formulas (`emb`, `proj`, `Wp`).
"Conjugacy" of `A` on `V` with `B` on `U` via `h, g` is `IsConjOn A B V U h g` (DataTypes (e)),
whose docstring is: `h` a local semiconjugacy on `V` from `A` to `B` with `h(V) ⊆ U`, `g` a local
semiconjugacy on `U` from `B` to `A` with `g(U) ⊆ V`, `g (h u) = u` on `V`, `h (g v) = v` on
`U`. Here `A` = compact on its whole state space (`V = univ`), `B` = expanded, `U = W'`,
`h` = embedding, `g` = projection. The component `g(U) ⊆ univ` holds trivially and is omitted.
One shadow per remaining component; all `N, q, γ`.
-- AMBIGUITY: the text states only `τ ≠ 0`, but writes ψ', ψ'' for the derivatives of ψ (DESIGN
-- §0), and the embedding is differentiable only through them. Read as: ψ' and ψ'' are the
-- derivatives of ψ and ψ' at every point (the compact state space is the whole plane, so no
-- smaller set of θ is named). No normalisation of ψ is assumed.
-- AMBIGUITY: "the expanded model restricted to W'" is read through `IsConjOn` (the design's
-- invariance of W is claim `MorphismsCompact.compactWInvariant`); invariance of `W'` itself is
-- not added as a separate requirement. -/
namespace Alignment.Shadows.MorphismsCompact.CompactConj

open Alignment.Shadows.MorphismsCompact

/-- Hypotheses of the claim: `τ ≠ 0`, and ψ', ψ'' are the derivatives of ψ, ψ' everywhere. -/
def Hyp (N : CNet) (τ : ℝ) : Prop :=
  τ ≠ 0 ∧ (∀ θ : ℝ, HasDerivAt N.ψ (N.ψ' θ) θ) ∧ (∀ θ : ℝ, HasDerivAt N.ψ' (N.ψ'' θ) θ)

/-- S1: the embedding is a local semiconjugacy on the whole compact plane from the compact to
the expanded model. -/
@[sa_shadow "MorphismsCompact.compactConj" 1]
def S1 : Prop :=
  ∀ (N : CNet) (q τ γ : ℝ), Hyp N τ →
    IsSemiconjOn (compactSIR N q τ γ) (ebSys N q (sirRxns τ γ)) Set.univ (emb N q τ γ)

/-- S2: the embedding maps the compact plane into `W'`. -/
@[sa_shadow "MorphismsCompact.compactConj" 2]
def S2 : Prop :=
  ∀ (N : CNet) (q τ γ : ℝ), Hyp N τ → ∀ w : ℝ × ℝ, emb N q τ γ w ∈ Wp N q τ γ

/-- S3: the projection is a local semiconjugacy on `W'` from the expanded to the compact
model. -/
@[sa_shadow "MorphismsCompact.compactConj" 3]
def S3 : Prop :=
  ∀ (N : CNet) (q τ γ : ℝ), Hyp N τ →
    IsSemiconjOn (ebSys N q (sirRxns τ γ)) (compactSIR N q τ γ) (Wp N q τ γ) proj

/-- S4: projection after embedding is the identity on the compact plane. -/
@[sa_shadow "MorphismsCompact.compactConj" 4]
def S4 : Prop :=
  ∀ (N : CNet) (q τ γ : ℝ), Hyp N τ → ∀ w : ℝ × ℝ, proj (emb N q τ γ w) = w

/-- S5: embedding after projection is the identity on `W'`. -/
@[sa_shadow "MorphismsCompact.compactConj" 5]
def S5 : Prop :=
  ∀ (N : CNet) (q τ γ : ℝ), Hyp N τ → ∀ u ∈ Wp N q τ γ, emb N q τ γ (proj u) = u

@[sa_reference "MorphismsCompact.compactConj"]
def T : Prop := S1 ∧ S2 ∧ S3 ∧ S4 ∧ S5

@[sa_ref_forward "MorphismsCompact.compactConj" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "MorphismsCompact.compactConj" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "MorphismsCompact.compactConj" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "MorphismsCompact.compactConj" 4] theorem ref_fwd4 : T → S4 :=
  fun t => t.2.2.2.1
@[sa_ref_forward "MorphismsCompact.compactConj" 5] theorem ref_fwd5 : T → S5 :=
  fun t => t.2.2.2.2
@[sa_complete "MorphismsCompact.compactConj"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) : T :=
  ⟨s1, s2, s3, s4, s5⟩

end Alignment.Shadows.MorphismsCompact.CompactConj

/-! ### `MorphismsCompact.compactSolution` (re-shadowed after text remediation)

Text: "for `τ ≠ 0`, every expanded solution from the design's initial condition (seed factor
`q = 1 − ρ`) stays in `W'` and its image `(θ, pop_R)` solves the compact model, for derivatives
within the time interval and for two-sided derivatives."
Two readings of "solution" (within `I`; two-sided at every `t ∈ I`), each with two conclusions
(stays in `W'`; the image solves the compact model in the same sense): four shadows.
-- AMBIGUITY: "the design's initial condition" (§D.4: θ(0) = 1, ξ(0) = 1, φ_X(0) = pop_X(0) = ρ_X,
-- q = 1 − Σρ). "Seed factor q = 1 − ρ" names a single ρ: the SIR seed is in the entry state I,
-- ρ_I = ρ, ρ_R = 0 (confirmed by §M.4: "(θ, ξ, φ_I, φ_R, pop_I, pop_R) = (1, 1, 1 − q, 0, 1 − q,
-- 0)"). ρ is any real (the text states no range).
-- AMBIGUITY: the text states no hypothesis on ψ; §M.4 names "the PGF hypotheses of
-- compact_solution (ψ(1) = 1, ψ'(1) = μ, and ψ', ψ'' are the derivatives of ψ, ψ')". Read for a
-- general network as: ψ(1) = 1, ψ'(1) ≠ 0 (φ_S = qξψ'(θ)/ψ'(1) divides by it; for Poisson it is
-- μ ≠ 0), and ψ', ψ'' the derivatives of ψ, ψ' at the points θ(t), t ∈ I, visited by the
-- solution (the most general reading: it covers PGFs defined only near [0, 1]).
-- AMBIGUITY: "the time interval": `I` convex with `0 ∈ I` (the initial condition is at t = 0).
-- AMBIGUITY: the sentence-final "for derivatives within the time interval and for two-sided
-- derivatives" is read as qualifying both the hypothesis "solution" and the conclusion "solves",
-- and as applying to both conclusions ("stays in W'" and "solves"). -/
namespace Alignment.Shadows.MorphismsCompact.CompactSolution

open Alignment.Shadows.MorphismsCompact

/-- Common hypotheses (except the solution property): `τ ≠ 0`, the PGF hypotheses along the
solution, `I` an interval containing 0, and the design's initial condition at 0. -/
def Hyp (N : CNet) (ρ τ : ℝ) (I : Set ℝ) (x : ℝ → EB SIRSp) : Prop :=
  τ ≠ 0 ∧ N.ψ 1 = 1 ∧ N.ψ' 1 ≠ 0 ∧ Convex ℝ I ∧ 0 ∈ I ∧ x 0 = ic ρ ∧
    (∀ t ∈ I, HasDerivAt N.ψ (N.ψ' (x t).1) (x t).1) ∧
    (∀ t ∈ I, HasDerivAt N.ψ' (N.ψ'' (x t).1) (x t).1)

/-- S1 (within reading): the solution stays in `W'`. -/
@[sa_shadow "MorphismsCompact.compactSolution" 1]
def S1 : Prop :=
  ∀ (N : CNet) (ρ τ γ : ℝ) (I : Set ℝ) (x : ℝ → EB SIRSp), Hyp N ρ τ I x →
    (∀ t ∈ I, HasDerivWithinAt x ((ebSys N (1 - ρ) (sirRxns τ γ)).F (x t)) I t) →
    ∀ t ∈ I, x t ∈ Wp N (1 - ρ) τ γ

/-- S2 (within reading): the image `(θ, pop_R)` solves the compact model within `I`. -/
@[sa_shadow "MorphismsCompact.compactSolution" 2]
def S2 : Prop :=
  ∀ (N : CNet) (ρ τ γ : ℝ) (I : Set ℝ) (x : ℝ → EB SIRSp), Hyp N ρ τ I x →
    (∀ t ∈ I, HasDerivWithinAt x ((ebSys N (1 - ρ) (sirRxns τ γ)).F (x t)) I t) →
    ∀ t ∈ I, HasDerivWithinAt (fun s => proj (x s))
      ((compactSIR N (1 - ρ) τ γ).F (proj (x t))) I t

/-- S3 (two-sided reading): the solution stays in `W'`. -/
@[sa_shadow "MorphismsCompact.compactSolution" 3]
def S3 : Prop :=
  ∀ (N : CNet) (ρ τ γ : ℝ) (I : Set ℝ) (x : ℝ → EB SIRSp), Hyp N ρ τ I x →
    (∀ t ∈ I, HasDerivAt x ((ebSys N (1 - ρ) (sirRxns τ γ)).F (x t)) t) →
    ∀ t ∈ I, x t ∈ Wp N (1 - ρ) τ γ

/-- S4 (two-sided reading): the image `(θ, pop_R)` solves the compact model, with two-sided
derivatives at every `t ∈ I`. -/
@[sa_shadow "MorphismsCompact.compactSolution" 4]
def S4 : Prop :=
  ∀ (N : CNet) (ρ τ γ : ℝ) (I : Set ℝ) (x : ℝ → EB SIRSp), Hyp N ρ τ I x →
    (∀ t ∈ I, HasDerivAt x ((ebSys N (1 - ρ) (sirRxns τ γ)).F (x t)) t) →
    ∀ t ∈ I, HasDerivAt (fun s => proj (x s)) ((compactSIR N (1 - ρ) τ γ).F (proj (x t))) t

@[sa_reference "MorphismsCompact.compactSolution"]
def T : Prop := S1 ∧ S2 ∧ S3 ∧ S4

@[sa_ref_forward "MorphismsCompact.compactSolution" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "MorphismsCompact.compactSolution" 2] theorem ref_fwd2 : T → S2 :=
  fun t => t.2.1
@[sa_ref_forward "MorphismsCompact.compactSolution" 3] theorem ref_fwd3 : T → S3 :=
  fun t => t.2.2.1
@[sa_ref_forward "MorphismsCompact.compactSolution" 4] theorem ref_fwd4 : T → S4 :=
  fun t => t.2.2.2
@[sa_complete "MorphismsCompact.compactSolution"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.MorphismsCompact.CompactSolution

/-! ### `MorphismsCompact.compactSolutionPoisson` (re-shadowed after text remediation)

Text (§M.4): "For μ ≠ 0 and τ ≠ 0 the Poisson(μ) network satisfies the PGF hypotheses of
`compact_solution` (ψ(1) = 1, ψ'(1) = μ, and ψ', ψ'' are the derivatives of ψ, ψ'), and a local
EB SIR solution from the design's initial condition (θ, ξ, φ_I, φ_R, pop_I, pop_R) =
(1, 1, 1 − q, 0, 1 − q, 0) exists on some (−ε, ε); it stays in W′ and its image (θ, pop_R)
solves the compact model."
The hypotheses "μ ≠ 0 and τ ≠ 0" scope the whole sentence, so every shadow carries both. Split:
the four PGF facts (S1–S4), and the existence of a local solution that stays in `W'` and whose
image solves the compact model (S5: a single existential, because "it stays … and its image
solves" is about the solution that exists). The seed factor `q` and the rate `γ` are arbitrary
(the text restricts neither).
-- AMBIGUITY: "ψ', ψ'' are the derivatives of ψ, ψ'" — read at every point of ℝ (the Poisson PGF
-- is entire; the text names no set).
-- AMBIGUITY: "local EB SIR solution … on some (−ε, ε)" — `ε > 0`, the solution property with
-- two-sided derivatives at every t ∈ (−ε, ε) (an open interval), initial value at t = 0; "its
-- image solves the compact model" in the same sense on the same interval. -/
namespace Alignment.Shadows.MorphismsCompact.CompactSolutionPoisson

open Alignment.Shadows.MorphismsCompact

/-- S1: Poisson(μ) has ψ(1) = 1. -/
@[sa_shadow "MorphismsCompact.compactSolutionPoisson" 1]
def S1 : Prop :=
  ∀ μ τ : ℝ, μ ≠ 0 → τ ≠ 0 → (CNet.poisson μ).ψ 1 = 1

/-- S2: Poisson(μ) has ψ'(1) = μ. -/
@[sa_shadow "MorphismsCompact.compactSolutionPoisson" 2]
def S2 : Prop :=
  ∀ μ τ : ℝ, μ ≠ 0 → τ ≠ 0 → (CNet.poisson μ).ψ' 1 = μ

/-- S3: for Poisson(μ), ψ' is the derivative of ψ at every point. -/
@[sa_shadow "MorphismsCompact.compactSolutionPoisson" 3]
def S3 : Prop :=
  ∀ μ τ : ℝ, μ ≠ 0 → τ ≠ 0 →
    ∀ θ : ℝ, HasDerivAt (CNet.poisson μ).ψ ((CNet.poisson μ).ψ' θ) θ

/-- S4: for Poisson(μ), ψ'' is the derivative of ψ' at every point. -/
@[sa_shadow "MorphismsCompact.compactSolutionPoisson" 4]
def S4 : Prop :=
  ∀ μ τ : ℝ, μ ≠ 0 → τ ≠ 0 →
    ∀ θ : ℝ, HasDerivAt (CNet.poisson μ).ψ' ((CNet.poisson μ).ψ'' θ) θ

/-- S5: a local EB SIR solution from `(1, 1, 1 − q, 0, 1 − q, 0)` exists on some `(−ε, ε)`,
stays in `W'` there, and its image `(θ, pop_R)` solves the compact model there. -/
@[sa_shadow "MorphismsCompact.compactSolutionPoisson" 5]
def S5 : Prop :=
  ∀ μ τ γ q : ℝ, μ ≠ 0 → τ ≠ 0 → ∃ ε > 0, ∃ x : ℝ → EB SIRSp,
    x 0 = (1, 1, sv (1 - q) 0, sv (1 - q) 0) ∧
    (∀ t ∈ Set.Ioo (-ε) ε,
      HasDerivAt x ((ebSys (CNet.poisson μ) q (sirRxns τ γ)).F (x t)) t) ∧
    (∀ t ∈ Set.Ioo (-ε) ε, x t ∈ Wp (CNet.poisson μ) q τ γ) ∧
    (∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt (fun s => proj (x s))
      ((compactSIR (CNet.poisson μ) q τ γ).F (proj (x t))) t)

@[sa_reference "MorphismsCompact.compactSolutionPoisson"]
def T : Prop := S1 ∧ S2 ∧ S3 ∧ S4 ∧ S5

@[sa_ref_forward "MorphismsCompact.compactSolutionPoisson" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t.1
@[sa_ref_forward "MorphismsCompact.compactSolutionPoisson" 2] theorem ref_fwd2 : T → S2 :=
  fun t => t.2.1
@[sa_ref_forward "MorphismsCompact.compactSolutionPoisson" 3] theorem ref_fwd3 : T → S3 :=
  fun t => t.2.2.1
@[sa_ref_forward "MorphismsCompact.compactSolutionPoisson" 4] theorem ref_fwd4 : T → S4 :=
  fun t => t.2.2.2.1
@[sa_ref_forward "MorphismsCompact.compactSolutionPoisson" 5] theorem ref_fwd5 : T → S5 :=
  fun t => t.2.2.2.2
@[sa_complete "MorphismsCompact.compactSolutionPoisson"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) : T :=
  ⟨s1, s2, s3, s4, s5⟩

end Alignment.Shadows.MorphismsCompact.CompactSolutionPoisson

/-! ### `MorphismsCompact.hasFDerivAtCompactEmb`

Text: "`compactEmb` has derivative `compactD` at `w` when ψ' and ψ'' are the derivatives of ψ
and ψ' at `θ = w.1`." The text names the library operations, so they are used directly; no
restriction on `q, τ, γ`. -/
namespace Alignment.Shadows.MorphismsCompact.HasFDerivAtCompactEmb

@[sa_reference "MorphismsCompact.hasFDerivAtCompactEmb"]
def T : Prop :=
  ∀ (N : CNet) (q τ γ : ℝ) (w : ℝ × ℝ),
    HasDerivAt N.ψ (N.ψ' w.1) w.1 → HasDerivAt N.ψ' (N.ψ'' w.1) w.1 →
    HasFDerivAt (compactEmb N q τ γ) (compactD N q τ γ w) w

/-- S1: the whole statement (a single atomic requirement). -/
@[sa_shadow "MorphismsCompact.hasFDerivAtCompactEmb" 1]
def S1 : Prop :=
  ∀ (N : CNet) (q τ γ : ℝ) (w : ℝ × ℝ),
    HasDerivAt N.ψ (N.ψ' w.1) w.1 → HasDerivAt N.ψ' (N.ψ'' w.1) w.1 →
    HasFDerivAt (compactEmb N q τ γ) (compactD N q τ γ w) w

@[sa_ref_forward "MorphismsCompact.hasFDerivAtCompactEmb" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t
@[sa_complete "MorphismsCompact.hasFDerivAtCompactEmb"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MorphismsCompact.HasFDerivAtCompactEmb

/-! ### `MorphismsCompact.compactEmbSemiconj`

Text: "For `τ ≠ 0`, the embedding is a local semiconjugacy from the compact model to the
expanded model on the set of `(θ, R)` with θ ∈ Θ, where Θ is a set on which ψ' and ψ'' are the
derivatives of ψ and ψ'." "The embedding" is the text's formula (`emb` above); "local
semiconjugacy on U" is `IsSemiconjOn` (DataTypes (e)). All `N, q, γ`, all sets Θ.
-- AMBIGUITY: "ψ' and ψ'' are the derivatives of ψ and ψ'" on Θ — read as two-sided
-- `HasDerivAt` at every θ ∈ Θ (ψ is a function on ℝ; differentiability of the embedding at
-- `(θ, R)` needs the two-sided derivative). -/
namespace Alignment.Shadows.MorphismsCompact.CompactEmbSemiconj

open Alignment.Shadows.MorphismsCompact

@[sa_reference "MorphismsCompact.compactEmbSemiconj"]
def T : Prop :=
  ∀ (N : CNet) (q τ γ : ℝ) (Θ : Set ℝ), τ ≠ 0 →
    (∀ θ ∈ Θ, HasDerivAt N.ψ (N.ψ' θ) θ) → (∀ θ ∈ Θ, HasDerivAt N.ψ' (N.ψ'' θ) θ) →
    IsSemiconjOn (compactSIR N q τ γ) (ebSys N q (sirRxns τ γ)) {w : ℝ × ℝ | w.1 ∈ Θ}
      (emb N q τ γ)

/-- S1: the whole statement (a single atomic requirement). -/
@[sa_shadow "MorphismsCompact.compactEmbSemiconj" 1]
def S1 : Prop :=
  ∀ (N : CNet) (q τ γ : ℝ) (Θ : Set ℝ), τ ≠ 0 →
    (∀ θ ∈ Θ, HasDerivAt N.ψ (N.ψ' θ) θ) → (∀ θ ∈ Θ, HasDerivAt N.ψ' (N.ψ'' θ) θ) →
    IsSemiconjOn (compactSIR N q τ γ) (ebSys N q (sirRxns τ γ)) {w : ℝ × ℝ | w.1 ∈ Θ}
      (emb N q τ γ)

@[sa_ref_forward "MorphismsCompact.compactEmbSemiconj" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t
@[sa_complete "MorphismsCompact.compactEmbSemiconj"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MorphismsCompact.CompactEmbSemiconj
