import Alignment.Registry
import Alignment.Shadows.ClosurePT
import NetworkEpi

/-!
# Checkers: group `ClosurePT` (trusted module `NetworkEpi.Closure.PT`)

Checker author (SA-PASS role 3, non-blind). For the five `implemented` claims of
`NetworkEpi/Closure/PT.lean`, this file holds the `sa_claim` registration (verbatim registry text,
registry `impl` list), the forward checkers `sa_impl% → Sᵢ`, the backward checkers
`S₁ → … → Sₙ → sa_impl%`, and `sa_fail_*` records.

No bridges are declared. The blind shadows use the trusted notions themselves (`CNet` and its
projections, `CNet.closureK`, `CNet.poisson`). The implementations `pt_iff_const_closure`,
`hasDerivWithinAt_pt_quotient_expanded` and `hasDerivWithinAt_pt_quotient` quantify over free functions
`ψ ψ' ψ'' : ℝ → ℝ`. The backward checkers pack them into the record `⟨ψ, ψ', ψ''⟩ : CNet`, whose
projections reduce definitionally. No witnesses are needed: no implementation hypothesis is
headed by a trusted-library predicate (they are `Convex`, `interior`, `HasDerivWithinAt`, `<`,
`∈`, `=` and `≠`).

`import NetworkEpi` loads the trusted root, so the audit can walk the imports of `NetworkEpi.lean`
(`NetworkEpi.Morphisms.All` imports `NetworkEpi.Closure.PT`). Without it, a standalone audit of
this module flags every implementation as `impl_untrusted`.

Remediated implementations (this pass): `ClosurePT.ptClosureAtOne` is implemented by
`pt_constants_at_one` (α = ψ'(1) with no proviso; κ = ψ''(1)/ψ'(1)² and κ = K_ψ(1) under
ψ'(1) ≠ 0), `ClosurePT.poissonClosureK` by `poisson_isPT` (every μ, PT identity only), and
`ClosurePT.hasDerivWithinAtPtQuotient` by `hasDerivWithinAt_pt_quotient_expanded` together with
`hasDerivWithinAt_pt_quotient` (expanded and factored forms). All their checks are structural and
no failure is recorded for them.
-/

open NEP

/-! ## `ClosurePT.ptIffConstClosure` -/

namespace Alignment.Shadows.ClosurePT.PtIffConstClosure

sa_claim "ClosurePT.ptIffConstClosure" group "ClosurePT" required
  text "**Poisson type ⇔ constant closure (M8), both directions.** Design statement (DESIGN_NetworkEpiCore.md §D.5, M8): \"PT ⇔ constant closure | On an interval I with ψ > 0: K_ψ ≡ κ ⇔ ψ' = αψ^κ. Proof of ⇒: d/dx(ψ'ψ^{−κ}) = ψ^{−κ−1}(ψψ'' − κψ'²) = 0. So NBM's constant closure ⟨k(k−1)⟩/⟨k⟩² is exact **iff** the degree distribution is PT\"; §D.7, L4d `Closure/PT`: \"`(∀ x ∈ I, ψ x * ψ'' x = κ * ψ' x ^ 2) ↔ ∃ α, ∀ x ∈ I, ψ' x = α * ψ x ^ κ` (with ψ > 0 on I; `is_const_of_deriv_eq_zero`)\". [...] an analytic statement about ψ on I [...] (both directions, product form of the design's §D.7 table)"
  impl NEP.pt_iff_const_closure

@[sa_forward "ClosurePT.ptIffConstClosure" 1]
theorem fwd1 (h : sa_impl% "ClosurePT.ptIffConstClosure") : S1 := by
  intro N I κ hI hpos h1 h2 hK
  exact (h hI.1 hI.2 hpos h1 h2 κ).mp hK

@[sa_forward "ClosurePT.ptIffConstClosure" 2]
theorem fwd2 (h : sa_impl% "ClosurePT.ptIffConstClosure") : S2 := by
  intro N I κ hI hpos h1 h2 hα
  exact (h hI.1 hI.2 hpos h1 h2 κ).mpr hα

/-- The free functions are packed into `⟨ψ, ψ', ψ''⟩ : CNet`. -/
@[sa_backward "ClosurePT.ptIffConstClosure"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "ClosurePT.ptIffConstClosure" := by
  intro ψ ψ' ψ'' I hI hIi hpos h1 h2 κ
  exact ⟨s1 ⟨ψ, ψ', ψ''⟩ I κ ⟨hI, hIi⟩ hpos h1 h2, s2 ⟨ψ, ψ', ψ''⟩ I κ ⟨hI, hIi⟩ hpos h1 h2⟩

end Alignment.Shadows.ClosurePT.PtIffConstClosure

/-! ## `ClosurePT.ptIffClosureK` -/

namespace Alignment.Shadows.ClosurePT.PtIffClosureK

sa_claim "ClosurePT.ptIffClosureK" group "ClosurePT" required
  text "**PT ⇔ K_ψ ≡ κ in ratio form (M8).** Design statement (DESIGN_NetworkEpiCore.md §D.5, M8): \"On an interval I with ψ > 0: K_ψ ≡ κ ⇔ ψ' = αψ^κ\"; M6: \"K_ψ = ψψ''/ψ'²\". [...] (the ratio form `K_ψ = ψψ''/ψ'² ≡ κ`, where ψ' ≠ 0)"
  impl NEP.pt_iff_closureK

@[sa_forward "ClosurePT.ptIffClosureK" 1]
theorem fwd1 (h : sa_impl% "ClosurePT.ptIffClosureK") : S1 := by
  intro N I κ hI hpos h1 h2 hne hK
  exact (h N hI.1 hI.2 hpos hne h1 h2 κ).mp hK

@[sa_forward "ClosurePT.ptIffClosureK" 2]
theorem fwd2 (h : sa_impl% "ClosurePT.ptIffClosureK") : S2 := by
  intro N I κ hI hpos h1 h2 hne hα
  exact (h N hI.1 hI.2 hpos hne h1 h2 κ).mpr hα

@[sa_backward "ClosurePT.ptIffClosureK"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "ClosurePT.ptIffClosureK" := by
  intro I N hI hIi hpos hne h1 h2 κ
  exact ⟨s1 N I κ ⟨hI, hIi⟩ hpos h1 h2 hne, s2 N I κ ⟨hI, hIi⟩ hpos h1 h2 hne⟩

end Alignment.Shadows.ClosurePT.PtIffClosureK

/-! ## `ClosurePT.ptClosureAtOne` -/

namespace Alignment.Shadows.ClosurePT.PtClosureAtOne

sa_claim "ClosurePT.ptClosureAtOne" group "ClosurePT" required
  text "**The PT constants at θ = 1 (M8), with `α = ψ'(1)` unconditional.** Design statement (DESIGN_NetworkEpiCore.md §D.5, M8): \"So NBM's constant closure ⟨k(k−1)⟩/⟨k⟩² is exact **iff** the degree distribution is PT\"; §C.1: \"closure_constant(d) # K_ψ(1) = ψ''(1)/ψ'(1)² (NBM's heterogeneous constant closure)\". [...] if moreover `1 ∈ I` and `ψ(1) = 1`, the constants are `α = ψ'(1)` and `κ = ψ''(1)/ψ'(1)²` (the value of NBM's constant closure, `closure_constant(d)`); the value of κ, and `K_ψ(1)` itself, need `ψ'(1) ≠ 0`"
  impl NEP.pt_constants_at_one

@[sa_forward "ClosurePT.ptClosureAtOne" 1]
theorem fwd1 (h : sa_impl% "ClosurePT.ptClosureAtOne") : S1 := by
  intro N I α κ hp
  exact (h N hp.1.1 hp.1.2 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2.1 hp.2.2.2.2.2.2 hp.2.2.2.2.1).1

@[sa_forward "ClosurePT.ptClosureAtOne" 2]
theorem fwd2 (h : sa_impl% "ClosurePT.ptClosureAtOne") : S2 := by
  intro N I α κ hp hm
  exact (h N hp.1.1 hp.1.2 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2.1 hp.2.2.2.2.2.2 hp.2.2.2.2.1).2.1 hm

@[sa_forward "ClosurePT.ptClosureAtOne" 3]
theorem fwd3 (h : sa_impl% "ClosurePT.ptClosureAtOne") : S3 := by
  intro N I α κ hp hm
  exact (h N hp.1.1 hp.1.2 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2.1 hp.2.2.2.2.2.2 hp.2.2.2.2.1).2.2 hm

@[sa_backward "ClosurePT.ptClosureAtOne"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) : sa_impl% "ClosurePT.ptClosureAtOne" := by
  intro I N hI hIi hpos h1 h2 hone hψ1 α κ hα
  exact ⟨s1 N I α κ ⟨⟨hI, hIi⟩, hpos, h1, h2, hα, hone, hψ1⟩,
    s2 N I α κ ⟨⟨hI, hIi⟩, hpos, h1, h2, hα, hone, hψ1⟩,
    s3 N I α κ ⟨⟨hI, hIi⟩, hpos, h1, h2, hα, hone, hψ1⟩⟩

end Alignment.Shadows.ClosurePT.PtClosureAtOne

/-! ## `ClosurePT.poissonClosureK` -/

namespace Alignment.Shadows.ClosurePT.PoissonClosureK

sa_claim "ClosurePT.poissonClosureK" group "ClosurePT" required
  text "**The Poisson PGF is of Poisson type with κ = 1 (M8, Poisson instance).** Design statement (DESIGN_NetworkEpiCore.md §0): \"**Poisson type (PT).** A degree PGF ψ is PT if ψ' = αψ^κ. This covers Poisson (κ = 1)\". [...] the Poisson PGF is PT with `α = μ`, `κ = 1`."
  impl NEP.poisson_isPT

@[sa_forward "ClosurePT.poissonClosureK" 1]
theorem fwd1 (h : sa_impl% "ClosurePT.poissonClosureK") : S1 := by
  intro μ x
  exact h μ x

@[sa_backward "ClosurePT.poissonClosureK"]
theorem bwd (s1 : S1) : sa_impl% "ClosurePT.poissonClosureK" := by
  intro μ x
  exact s1 μ x

end Alignment.Shadows.ClosurePT.PoissonClosureK

/-! ## `ClosurePT.hasDerivWithinAtPtQuotient` -/

namespace Alignment.Shadows.ClosurePT.HasDerivWithinAtPtQuotient

sa_claim "ClosurePT.hasDerivWithinAtPtQuotient" group "ClosurePT" required
  text "The derivative of `ψ'ψ^{−κ}` within `I`, when ψ > 0 at `x`: `ψ''ψ^{−κ} − κψ'²ψ^{−κ−1} = ψ^{−κ−1}(ψψ'' − κψ'²)`."
  impl NEP.hasDerivWithinAt_pt_quotient_expanded NEP.hasDerivWithinAt_pt_quotient

@[sa_forward "ClosurePT.hasDerivWithinAtPtQuotient" 1]
theorem fwd1 (h : sa_impl% "ClosurePT.hasDerivWithinAtPtQuotient") : S1 := by
  intro N I x κ hx
  obtain ⟨hpos, h1, h2⟩ := hx
  exact h.1 κ hpos h1 h2

@[sa_forward "ClosurePT.hasDerivWithinAtPtQuotient" 2]
theorem fwd2 (h : sa_impl% "ClosurePT.hasDerivWithinAtPtQuotient") : S2 := by
  intro N I x κ hx
  obtain ⟨hpos, h1, h2⟩ := hx
  exact h.2 κ hpos h1 h2

/-- The free functions are packed into `⟨ψ, ψ', ψ''⟩ : CNet`; `s1` gives the expanded form and
`s2` the factored form. -/
@[sa_backward "ClosurePT.hasDerivWithinAtPtQuotient"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "ClosurePT.hasDerivWithinAtPtQuotient" := by
  refine ⟨?_, ?_⟩
  · intro ψ ψ' ψ'' I κ x hpos h1 h2
    exact s1 ⟨ψ, ψ', ψ''⟩ I x κ ⟨hpos, h1, h2⟩
  · intro ψ ψ' ψ'' I κ x hpos h1 h2
    exact s2 ⟨ψ, ψ', ψ''⟩ I x κ ⟨hpos, h1, h2⟩

end Alignment.Shadows.ClosurePT.HasDerivWithinAtPtQuotient
