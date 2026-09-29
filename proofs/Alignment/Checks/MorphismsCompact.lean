import Alignment.Registry
import Alignment.Shadows.MorphismsCompact

/-!
# Checkers: group `MorphismsCompact` (trusted module `NetworkEpi.Morphisms.Compact`)

Checker author (SA-PASS role 3, non-blind). This file covers the seven `implemented` claims of
`NetworkEpi/Morphisms/Compact.lean`. For each one it holds the `sa_claim` registration
(verbatim registry text, registry `impl` list), the structural forward checkers
`sa_impl% → Sᵢ`, the backward checker `S₁ → … → Sₙ → sa_impl%`, and an `sa_fail_*` record
wherever a check cannot be derived. The informal claim `header.models` is not registered.

**Bridges** (each needs independent review). The blind shadows write the text's embedding,
`W'` and projection in primitive terms (`emb`, `Wp`, `proj`). The projection `proj` is
definitionally equal to the trusted `compactProj`, and the shadows' `sv a b` / `ic ρ` are
definitionally equal to `sirVec a b` / `(1, 1, sirVec ρ 0, sirVec ρ 0)`; none needs a bridge.
The other two do:

* `compactEmb N q τ γ w = emb N q τ γ w`. The trusted definition writes `φ_S` as
  `N.phiS q θ 1 = q * 1 * ψ'(θ) / ψ'(1)` and `S` as `N.susc q θ 1 = q * 1 * ψ(θ)`; the text writes
  `qψ'(θ)/ψ'(1)` and `qψ(θ)`. They differ by the factor `* 1`. Copies: `CompactConj.bridge_emb`,
  `CompactEmbSemiconj.bridge_emb`.
* `compactW N q τ γ = Wp N q τ γ`. The same `φ_S = qξψ'(θ)/ψ'(1)`, `S = qξψ(θ)` spelled through
  `phiS`/`susc`, with the conjuncts `ξ = 1` and `τφ_R + γθ = γ` in the other order. Copies:
  `CompactConj.bridge_W`, `CompactSolution.bridge_W`, `CompactSolutionPoisson.bridge_W` (the last
  two are new with the re-shadowing and carry the same statement hash as `CompactConj.bridge_W`).

After the text remediation and blind re-shadowing of `compactWInvariant`, `compactConj`,
`compactSolution` and `compactSolutionPoisson`, the new impls (`compact_W_invariant_any`,
`compact_conj_global`, `compact_solution_ic` + `compact_solution_ic_at`,
`compact_solution_poisson_spec`) match the shadows, and every forward and backward check is
structural; no `sa_fail_*` record remains in this group.
-/

open NEP

/-! ### `MorphismsCompact.sirVecApply` -/
namespace Alignment.Shadows.MorphismsCompact.SirVecApply

sa_claim "MorphismsCompact.sirVecApply" group "MorphismsCompact" required
  text "`sirVec a b` takes the value `a` at `I`. [...] `sirVec a b` takes the value `b` at `R`."
  impl NEP.sirVec_I NEP.sirVec_R

@[sa_forward "MorphismsCompact.sirVecApply" 1]
theorem fwd1 (h : sa_impl% "MorphismsCompact.sirVecApply") : S1 := h.1

@[sa_forward "MorphismsCompact.sirVecApply" 2]
theorem fwd2 (h : sa_impl% "MorphismsCompact.sirVecApply") : S2 := h.2

@[sa_backward "MorphismsCompact.sirVecApply"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "MorphismsCompact.sirVecApply" := ⟨s1, s2⟩

end Alignment.Shadows.MorphismsCompact.SirVecApply

/-! ### `MorphismsCompact.compactWInvariant` -/
namespace Alignment.Shadows.MorphismsCompact.CompactWInvariant

open Alignment.Shadows.MorphismsCompact

sa_claim "MorphismsCompact.compactWInvariant" group "MorphismsCompact" required
  text "**The design's W is invariant (M9).** Design statement (DESIGN_NetworkEpiCore.md §D.5, M9): \"W = {τφ_R + γθ = γ} is invariant for SIR-shaped P\". [...] along every EB SIR solution on a time interval, `τφ_R + γθ` is constant, so the design's set `W = {τφ_R + γθ = γ}` is invariant (no assumption on ψ)."
  impl NEP.compact_W_invariant_any

@[sa_forward "MorphismsCompact.compactWInvariant" 1]
theorem fwd1 (h : sa_impl% "MorphismsCompact.compactWInvariant") : S1 := by
  intro N q τ γ I x hI hx
  exact (h N q τ γ hI hx).1

@[sa_forward "MorphismsCompact.compactWInvariant" 2]
theorem fwd2 (h : sa_impl% "MorphismsCompact.compactWInvariant") : S2 := by
  intro N q τ γ I x hI hx s hs hW t ht
  exact (h N q τ γ hI hx).2 s hs hW t ht

@[sa_backward "MorphismsCompact.compactWInvariant"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "MorphismsCompact.compactWInvariant" := by
  intro N q τ γ I hI x hx
  exact ⟨s1 N q τ γ I x hI hx, s2 N q τ γ I x hI hx⟩

end Alignment.Shadows.MorphismsCompact.CompactWInvariant

/-! ### `MorphismsCompact.compactConj` -/
namespace Alignment.Shadows.MorphismsCompact.CompactConj

open Alignment.Shadows.MorphismsCompact

sa_claim "MorphismsCompact.compactConj" group "MorphismsCompact" required
  text "**The compact SIR EBCM is conjugate to the expanded one restricted to W' (M9).** Design statement (DESIGN_NetworkEpiCore.md §D.5, M9): \"Compact ⊂ expanded | W = {τφ_R + γθ = γ} is invariant for SIR-shaped P, and W → compact is a conjugacy | restriction\". [...] the embedding `(θ, R) ↦ (θ, 1, φ_I, φ_R, 1 − qψ(θ) − R, R)` with `φ_R = γ(1−θ)/τ`, `φ_I = θ − qψ'(θ)/ψ'(1) − φ_R` and the projection `(θ, …, pop_R) ↦ (θ, pop_R)` form a conjugacy between the compact model and the expanded model restricted to `W' = W ∩ {ξ = 1, θ = φ_S + φ_I + φ_R, S + pop_I + pop_R = 1}` (`τ ≠ 0`)."
  impl NEP.compact_conj_global

/-- Bridge (needs independent review): the trusted embedding `compactEmb` is the text's
embedding `(θ, R) ↦ (θ, 1, θ − qψ'(θ)/ψ'(1) − γ(1−θ)/τ, γ(1−θ)/τ, 1 − qψ(θ) − R, R)`
(`emb`, written blind from the text). They differ only by the factor `ξ = 1` inside
`phiS q θ 1` and `susc q θ 1`. -/
@[sa_bridge "MorphismsCompact.compactConj"]
theorem bridge_emb (N : CNet) (q τ γ : ℝ) (w : ℝ × ℝ) : compactEmb N q τ γ w = emb N q τ γ w := by
  simp only [compactEmb, emb, CNet.phiS, CNet.susc, mul_one]
  rfl

/-- Bridge (needs independent review): the trusted set `compactW` is the text's
`W' = W ∩ {ξ = 1, θ = φ_S + φ_I + φ_R, S + pop_I + pop_R = 1}` with `W = {τφ_R + γθ = γ}`,
`φ_S = qξψ'(θ)/ψ'(1)` and `S = qξψ(θ)` (`Wp`, written blind from the text and DESIGN §0). -/
@[sa_bridge "MorphismsCompact.compactConj"]
theorem bridge_W (N : CNet) (q τ γ : ℝ) : compactW N q τ γ = Wp N q τ γ := by
  ext u
  simp only [compactW, Wp, CNet.phiS, CNet.susc, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h2, h1, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h2, h1, h3, h4⟩

@[sa_forward "MorphismsCompact.compactConj" 1]
theorem fwd1 (h : sa_impl% "MorphismsCompact.compactConj") : S1 := by
  intro N q τ γ hyp
  have e : compactEmb N q τ γ = emb N q τ γ := funext (bridge_emb N q τ γ)
  rw [← e]
  exact (h N q τ γ hyp.1 hyp.2.1 hyp.2.2).1

@[sa_forward "MorphismsCompact.compactConj" 2]
theorem fwd2 (h : sa_impl% "MorphismsCompact.compactConj") : S2 := by
  intro N q τ γ hyp w
  rw [← bridge_emb N q τ γ w, ← bridge_W N q τ γ]
  exact (h N q τ γ hyp.1 hyp.2.1 hyp.2.2).2.2.1 w trivial

@[sa_forward "MorphismsCompact.compactConj" 3]
theorem fwd3 (h : sa_impl% "MorphismsCompact.compactConj") : S3 := by
  intro N q τ γ hyp
  rw [← bridge_W N q τ γ]
  exact (h N q τ γ hyp.1 hyp.2.1 hyp.2.2).2.1

@[sa_forward "MorphismsCompact.compactConj" 4]
theorem fwd4 (h : sa_impl% "MorphismsCompact.compactConj") : S4 := by
  intro N q τ γ hyp w
  rw [← bridge_emb N q τ γ w]
  exact (h N q τ γ hyp.1 hyp.2.1 hyp.2.2).2.2.2.2.1 w trivial

@[sa_forward "MorphismsCompact.compactConj" 5]
theorem fwd5 (h : sa_impl% "MorphismsCompact.compactConj") : S5 := by
  intro N q τ γ hyp u hu
  rw [← bridge_emb N q τ γ (proj u)]
  rw [← bridge_W N q τ γ] at hu
  exact (h N q τ γ hyp.1 hyp.2.1 hyp.2.2).2.2.2.2.2 u hu

/-- The component `g(W') ⊆ univ` of `IsConjOn`, which the blind author omitted as trivial, is
supplied by `trivial` (membership in `Set.univ` is `True`). -/
@[sa_backward "MorphismsCompact.compactConj"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) :
    sa_impl% "MorphismsCompact.compactConj" := by
  intro N q τ γ hτ hψ hψ'
  have hyp : Hyp N τ := ⟨hτ, hψ, hψ'⟩
  have e : compactEmb N q τ γ = emb N q τ γ := funext (bridge_emb N q τ γ)
  rw [e, bridge_W N q τ γ]
  exact ⟨s1 N q τ γ hyp, s3 N q τ γ hyp, fun w _ => s2 N q τ γ hyp w, fun _ _ => trivial,
    fun w _ => s4 N q τ γ hyp w, fun u hu => s5 N q τ γ hyp u hu⟩

end Alignment.Shadows.MorphismsCompact.CompactConj

/-! ### `MorphismsCompact.compactSolution` -/
namespace Alignment.Shadows.MorphismsCompact.CompactSolution

open Alignment.Shadows.MorphismsCompact

sa_claim "MorphismsCompact.compactSolution" group "MorphismsCompact" required
  text "**Expanded solutions from the design's initial condition are compact solutions (M9).** Design statement (DESIGN_NetworkEpiCore.md §D.5, M9): \"W = {τφ_R + γθ = γ} is invariant for SIR-shaped P, and W → compact is a conjugacy\"; §D.3: \"Examples: the compact SIR EBCM on {τφ_R + γθ = γ}\". [...] for `τ ≠ 0`, every expanded solution from the design's initial condition (seed factor `q = 1 − ρ`) stays in `W'` and its image `(θ, pop_R)` solves the compact model, for derivatives within the time interval and for two-sided derivatives."
  impl NEP.compact_solution_ic NEP.compact_solution_ic_at

/-- Bridge (needs independent review; copy of `CompactConj.bridge_W` for this claim): the
trusted set `compactW` is the text's `W' = W ∩ {ξ = 1, θ = φ_S + φ_I + φ_R, S + pop_I + pop_R = 1}`
(`Wp`, written blind from the text and DESIGN §0). -/
@[sa_bridge "MorphismsCompact.compactSolution"]
theorem bridge_W (N : CNet) (q τ γ : ℝ) : compactW N q τ γ = Wp N q τ γ := by
  ext u
  simp only [compactW, Wp, CNet.phiS, CNet.susc, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h2, h1, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h2, h1, h3, h4⟩

@[sa_forward "MorphismsCompact.compactSolution" 1]
theorem fwd1 (h : sa_impl% "MorphismsCompact.compactSolution") : S1 := by
  intro N ρ τ γ I x hy hx t ht
  rw [← bridge_W N (1 - ρ) τ γ]
  exact (h.1 N ρ τ γ hy.1 hy.2.1 hy.2.2.1 hy.2.2.2.1 hy.2.2.2.2.1 hy.2.2.2.2.2.1
    hy.2.2.2.2.2.2.1 hy.2.2.2.2.2.2.2 hx).1 t ht

@[sa_forward "MorphismsCompact.compactSolution" 2]
theorem fwd2 (h : sa_impl% "MorphismsCompact.compactSolution") : S2 := by
  intro N ρ τ γ I x hy hx t ht
  exact (h.1 N ρ τ γ hy.1 hy.2.1 hy.2.2.1 hy.2.2.2.1 hy.2.2.2.2.1 hy.2.2.2.2.2.1
    hy.2.2.2.2.2.2.1 hy.2.2.2.2.2.2.2 hx).2 t ht

@[sa_forward "MorphismsCompact.compactSolution" 3]
theorem fwd3 (h : sa_impl% "MorphismsCompact.compactSolution") : S3 := by
  intro N ρ τ γ I x hy hx t ht
  rw [← bridge_W N (1 - ρ) τ γ]
  exact (h.2 N ρ τ γ hy.1 hy.2.1 hy.2.2.1 hy.2.2.2.1 hy.2.2.2.2.1 hy.2.2.2.2.2.1
    hy.2.2.2.2.2.2.1 hy.2.2.2.2.2.2.2 hx).1 t ht

@[sa_forward "MorphismsCompact.compactSolution" 4]
theorem fwd4 (h : sa_impl% "MorphismsCompact.compactSolution") : S4 := by
  intro N ρ τ γ I x hy hx t ht
  exact (h.2 N ρ τ γ hy.1 hy.2.1 hy.2.2.1 hy.2.2.2.1 hy.2.2.2.2.1 hy.2.2.2.2.2.1
    hy.2.2.2.2.2.2.1 hy.2.2.2.2.2.2.2 hx).2 t ht

@[sa_backward "MorphismsCompact.compactSolution"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) :
    sa_impl% "MorphismsCompact.compactSolution" := by
  refine ⟨?_, ?_⟩
  · intro N ρ τ γ hτ h1 hm I hI h0 x hx0 hψ hψ' hx
    have hy : Hyp N ρ τ I x := ⟨hτ, h1, hm, hI, h0, hx0, hψ, hψ'⟩
    rw [bridge_W N (1 - ρ) τ γ]
    exact ⟨s1 N ρ τ γ I x hy hx, s2 N ρ τ γ I x hy hx⟩
  · intro N ρ τ γ hτ h1 hm I hI h0 x hx0 hψ hψ' hx
    have hy : Hyp N ρ τ I x := ⟨hτ, h1, hm, hI, h0, hx0, hψ, hψ'⟩
    rw [bridge_W N (1 - ρ) τ γ]
    exact ⟨s3 N ρ τ γ I x hy hx, s4 N ρ τ γ I x hy hx⟩

end Alignment.Shadows.MorphismsCompact.CompactSolution

/-! ### `MorphismsCompact.compactSolutionPoisson` -/
namespace Alignment.Shadows.MorphismsCompact.CompactSolutionPoisson

open Alignment.Shadows.MorphismsCompact

sa_claim "MorphismsCompact.compactSolutionPoisson" group "MorphismsCompact" required
  text "**`compact_solution` is not vacuous on Poisson networks (M9).** Design statement (DESIGN_NetworkEpiCore.md §D.5, M9): \"W = {τφ_R + γθ = γ} is invariant for SIR-shaped P, and W → compact is a conjugacy\"; amended by §M.4: \"For μ ≠ 0 and τ ≠ 0 the Poisson(μ) network satisfies the PGF hypotheses of `compact_solution` (ψ(1) = 1, ψ'(1) = μ, and ψ', ψ'' are the derivatives of ψ, ψ'), and a local EB SIR solution from the design's initial condition (θ, ξ, φ_I, φ_R, pop_I, pop_R) = (1, 1, 1 − q, 0, 1 − q, 0) exists on some (−ε, ε); it stays in W′ and its image (θ, pop_R) solves the compact model.\""
  impl NEP.compact_solution_poisson_spec

/-- Bridge (needs independent review; copy of `CompactConj.bridge_W` for this claim): the
trusted set `compactW` is the text's `W' = W ∩ {ξ = 1, θ = φ_S + φ_I + φ_R, S + pop_I + pop_R = 1}`
(`Wp`, written blind from the text and DESIGN §0). -/
@[sa_bridge "MorphismsCompact.compactSolutionPoisson"]
theorem bridge_W (N : CNet) (q τ γ : ℝ) : compactW N q τ γ = Wp N q τ γ := by
  ext u
  simp only [compactW, Wp, CNet.phiS, CNet.susc, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h2, h1, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h2, h1, h3, h4⟩

-- S1–S4 do not depend on `q` and `γ`; the impl is instantiated at `q = γ = 0`.
@[sa_forward "MorphismsCompact.compactSolutionPoisson" 1]
theorem fwd1 (h : sa_impl% "MorphismsCompact.compactSolutionPoisson") : S1 := by
  intro μ τ hμ hτ
  exact (h μ 0 τ 0 hμ hτ).1.1

@[sa_forward "MorphismsCompact.compactSolutionPoisson" 2]
theorem fwd2 (h : sa_impl% "MorphismsCompact.compactSolutionPoisson") : S2 := by
  intro μ τ hμ hτ
  exact (h μ 0 τ 0 hμ hτ).1.2

@[sa_forward "MorphismsCompact.compactSolutionPoisson" 3]
theorem fwd3 (h : sa_impl% "MorphismsCompact.compactSolutionPoisson") : S3 := by
  intro μ τ hμ hτ
  exact (h μ 0 τ 0 hμ hτ).2.1

@[sa_forward "MorphismsCompact.compactSolutionPoisson" 4]
theorem fwd4 (h : sa_impl% "MorphismsCompact.compactSolutionPoisson") : S4 := by
  intro μ τ hμ hτ
  exact (h μ 0 τ 0 hμ hτ).2.2.1

@[sa_forward "MorphismsCompact.compactSolutionPoisson" 5]
theorem fwd5 (h : sa_impl% "MorphismsCompact.compactSolutionPoisson") : S5 := by
  intro μ τ γ q hμ hτ
  obtain ⟨ε, hε, x, hx0, hx, hW, hp⟩ := (h μ q τ γ hμ hτ).2.2.2
  refine ⟨ε, hε, x, hx0, hx, ?_, hp⟩
  intro t ht
  rw [← bridge_W (CNet.poisson μ) q τ γ]
  exact hW t ht

@[sa_backward "MorphismsCompact.compactSolutionPoisson"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) :
    sa_impl% "MorphismsCompact.compactSolutionPoisson" := by
  intro μ q τ γ hμ hτ
  obtain ⟨ε, hε, x, hx0, hx, hW, hp⟩ := s5 μ τ γ q hμ hτ
  refine ⟨⟨s1 μ τ hμ hτ, s2 μ τ hμ hτ⟩, s3 μ τ hμ hτ, s4 μ τ hμ hτ, ε, hε, x, hx0, hx, ?_, hp⟩
  intro t ht
  rw [bridge_W (CNet.poisson μ) q τ γ]
  exact hW t ht

end Alignment.Shadows.MorphismsCompact.CompactSolutionPoisson

/-! ### `MorphismsCompact.hasFDerivAtCompactEmb` -/
namespace Alignment.Shadows.MorphismsCompact.HasFDerivAtCompactEmb

sa_claim "MorphismsCompact.hasFDerivAtCompactEmb" group "MorphismsCompact" required
  text "`compactEmb` has derivative `compactD` at `w` when ψ' and ψ'' are the derivatives of ψ and ψ' at `θ = w.1`."
  impl NEP.hasFDerivAt_compactEmb

@[sa_forward "MorphismsCompact.hasFDerivAtCompactEmb" 1]
theorem fwd1 (h : sa_impl% "MorphismsCompact.hasFDerivAtCompactEmb") : S1 := by
  intro N q τ γ w hψ hψ'
  exact h N q τ γ hψ hψ'

@[sa_backward "MorphismsCompact.hasFDerivAtCompactEmb"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsCompact.hasFDerivAtCompactEmb" := by
  intro N q τ γ w hψ hψ'
  exact s1 N q τ γ w hψ hψ'

end Alignment.Shadows.MorphismsCompact.HasFDerivAtCompactEmb

/-! ### `MorphismsCompact.compactEmbSemiconj` -/
namespace Alignment.Shadows.MorphismsCompact.CompactEmbSemiconj

open Alignment.Shadows.MorphismsCompact

sa_claim "MorphismsCompact.compactEmbSemiconj" group "MorphismsCompact" required
  text "For `τ ≠ 0`, the embedding is a local semiconjugacy from the compact model to the expanded model on the set of `(θ, R)` with θ ∈ Θ, where Θ is a set on which ψ' and ψ'' are the derivatives of ψ and ψ'."
  impl NEP.compactEmb_semiconj

/-- Bridge (needs independent review; copy of `CompactConj.bridge_emb` for this claim): the
trusted `compactEmb` is the text's embedding (`emb`); they differ only by the factor `ξ = 1`
inside `phiS q θ 1` and `susc q θ 1`. -/
@[sa_bridge "MorphismsCompact.compactEmbSemiconj"]
theorem bridge_emb (N : CNet) (q τ γ : ℝ) (w : ℝ × ℝ) : compactEmb N q τ γ w = emb N q τ γ w := by
  simp only [compactEmb, emb, CNet.phiS, CNet.susc, mul_one]
  rfl

@[sa_forward "MorphismsCompact.compactEmbSemiconj" 1]
theorem fwd1 (h : sa_impl% "MorphismsCompact.compactEmbSemiconj") : S1 := by
  intro N q τ γ Θ hτ hψ hψ'
  have e : compactEmb N q τ γ = emb N q τ γ := funext (bridge_emb N q τ γ)
  rw [← e]
  exact h N q τ γ hτ Θ hψ hψ'

@[sa_backward "MorphismsCompact.compactEmbSemiconj"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsCompact.compactEmbSemiconj" := by
  intro N q τ γ hτ Θ hψ hψ'
  have e : compactEmb N q τ γ = emb N q τ γ := funext (bridge_emb N q τ γ)
  rw [e]
  exact s1 N q τ γ Θ hτ hψ hψ'

end Alignment.Shadows.MorphismsCompact.CompactEmbSemiconj
