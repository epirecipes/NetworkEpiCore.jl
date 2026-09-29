import Alignment.Registry
import Alignment.Shadows.MorphismsPoisson

/-!
# Checkers: group `MorphismsPoisson` (trusted module `NetworkEpi.Morphisms.Poisson`)

Checker author (SA-PASS role 3, non-blind). For each of the `implemented` claims of
`NetworkEpi/Morphisms/Poisson.lean` this file holds the `sa_claim` registration (verbatim registry
text, registry `impl` list), the bridges, the forward checkers `sa_impl% → Sᵢ`, the backward
checker, and an `sa_fail_*` record wherever a check is not structurally derivable. The informal
`header.construction` and the missing `header.exitsNotConjugacy` are not registered, as in the
other groups.

## Bridges

No checker uses a bridge. `bridge_poissonDL` (`poissonDL μ q u = fderiv ℝ (poissonMap μ q) u`,
finite `σ`, registered for `poissonEbField`) is kept only because `Alignment.ReviewedBridges`
holds a review record for it. The impl `poisson_ebField_fderiv` is now stated with `fderiv`, so
the checkers no longer need it. Its proof (`hasFDerivAt_poissonMap_aux`) uses Mathlib calculus
lemmas only, and no implementation theorem.

No bridge is needed for "exit-free". The shadows write it primitively
(`∀ r ∈ P, ∀ Y ν, r ≠ Rxn.exit Y ν`), and the impls write `∀ r ∈ P, r.isExit = false`. The helpers
`exitFree_of_isExit` and `isExit_of_exitFree` convert between the two forms structurally, by a case
split on the reaction (plain data) and a `Bool` match to refute `true = false`.

## Recorded failures

None. `poissonIsoSolution` was re-shadowed blind after its text named both solution notions
(S1 within `I`, S2 two-sided at every `t ∈ I`); S2 is `poisson_iso_solution_at` and S1 is
`poisson_iso_solution`.

After remediation, every claim of the re-shadowed seven (`poissonIsoNatural`, `poissonIsoSir`,
`poissonIsoSeir`, `poissonDLNone`, `hasFDerivAtPoissonMap`, `poissonEbField`) has structural
forward and backward checkers against its new text-form impl.
-/

open NEP

/-! ## Exit-freeness: primitive form ↔ `Rxn.isExit` (structural helpers, not bridges) -/

namespace Alignment.Shadows.MorphismsPoisson

/-- `true = false` is absurd, by a match on `Bool` (structural, no `Bool.noConfusion` lemma). -/
theorem bool_true_ne_false (e : true = false) : False :=
  Eq.mp (congrArg (fun b : Bool => match b with | true => True | false => False) e) trivial

/-- From the impls' `isExit = false` to the primitive exit-freeness of one reaction. -/
theorem exitFree_of_isExit {σ : Type} (r : Rxn σ) (hr : r.isExit = false) :
    ∀ (Y : σ) (ν : ℝ), r ≠ Rxn.exit Y ν := by
  intro Y ν e
  rw [e] at hr
  exact bool_true_ne_false hr

/-- From the primitive exit-freeness of one reaction to the impls' `isExit = false`. -/
theorem isExit_of_exitFree {σ : Type} (r : Rxn σ) (hr : ∀ (Y : σ) (ν : ℝ), r ≠ Rxn.exit Y ν) :
    r.isExit = false := by
  cases r with
  | contact J X τ => rfl
  | exit Y ν => exact False.elim (hr Y ν rfl)
  | trans X Y a => rfl

end Alignment.Shadows.MorphismsPoisson

/-! ## `MorphismsPoisson.poissonIsoSemiconj` -/

namespace Alignment.Shadows.MorphismsPoisson.PoissonIsoSemiconj

sa_claim "MorphismsPoisson.poissonIsoSemiconj" group "MorphismsPoisson" required
  text "**The Poisson map is a semiconjugacy for every T_EB model (M2, with exits).** Design statement (DESIGN_NetworkEpiCore.md §D.5, M2): \"Poisson isomorphism | EB_{Pois μ}(P) ≅ MA(D_μ P) via π(θ, φ, pop) = (qξe^{μ(θ−1)}, Φ = φ, X = pop), natural in P. D_μ: contacts S + Φ_J → Φ_X + X + Φ_J at rate μτ; Φ_J → ∅ at τ; transitions on both copies\"; §J.10: \"**Exits in D_μ** (§D.5 M2) are `s → Φ_Y + Y`\". [...] for every T_EB model (exits allowed) and `μ ≠ 0`, `poissonMap` is a global semiconjugacy from EB on Poisson(μ) to MA(D_μ P)."
  impl NEP.poisson_iso_semiconj

@[sa_forward "MorphismsPoisson.poissonIsoSemiconj" 1]
theorem fwd1 (h : sa_impl% "MorphismsPoisson.poissonIsoSemiconj") : S1 := by
  intro σ _ _ μ q P hμ
  exact h μ q hμ P

@[sa_backward "MorphismsPoisson.poissonIsoSemiconj"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsPoisson.poissonIsoSemiconj" := by
  intro σ _ _ μ q hμ rs
  exact s1 μ q rs hμ

end Alignment.Shadows.MorphismsPoisson.PoissonIsoSemiconj

/-! ## `MorphismsPoisson.poissonIso`

`IsConjOn A B V U h g` is by definition `IsSemiconjOn A B V h ∧ IsSemiconjOn B A U g ∧
(∀ u ∈ V, h u ∈ U) ∧ (∀ v ∈ U, g v ∈ V) ∧ (∀ u ∈ V, g (h u) = u) ∧ ∀ v ∈ U, h (g v) = v`. Here
`V = Set.univ` (membership is `True`), `U = {v | 0 < v none}`, which is definitionally `SPos σ`,
and `piSlice μ q` is definitionally `poissonMap μ q ∘ EB1.incl`. -/

namespace Alignment.Shadows.MorphismsPoisson.PoissonIso
open Alignment.Shadows.MorphismsPoisson

sa_claim "MorphismsPoisson.poissonIso" group "MorphismsPoisson" required
  text "**The Poisson isomorphism for exit-free models (M2).** Design statement (DESIGN_NetworkEpiCore.md §D.5, M2): \"Poisson isomorphism | EB_{Pois μ}(P) ≅ MA(D_μ P) via π(θ, φ, pop) = (qξe^{μ(θ−1)}, Φ = φ, X = pop), natural in P. D_μ: contacts S + Φ_J → Φ_X + X + Φ_J at rate μτ; Φ_J → ∅ at τ; transitions on both copies | natural iso onto S > 0\". [...] for every **exit-free** T_EB model, `μ ≠ 0` and `q > 0`, the EB model in the design's coordinates `(θ, φ, pop)` is conjugate to MA(D_μ P) restricted to the open set `S > 0`, with inverse `(S, Φ, X) ↦ (1 + log(S/q)/μ, Φ, X)`."
  impl NEP.poisson_iso

@[sa_forward "MorphismsPoisson.poissonIso" 1]
theorem fwd1 (h : sa_impl% "MorphismsPoisson.poissonIso") : S1 := by
  intro σ _ _ μ q P he hμ hq
  exact (h μ q hμ hq P (fun r hr => isExit_of_exitFree r (he r hr))).1

@[sa_forward "MorphismsPoisson.poissonIso" 2]
theorem fwd2 (h : sa_impl% "MorphismsPoisson.poissonIso") : S2 := by
  intro σ _ _ μ q P he hμ hq w
  exact (h μ q hμ hq P (fun r hr => isExit_of_exitFree r (he r hr))).2.2.1 w trivial

@[sa_forward "MorphismsPoisson.poissonIso" 3]
theorem fwd3 (h : sa_impl% "MorphismsPoisson.poissonIso") : S3 := by
  intro σ _ _ μ q P he hμ hq
  exact (h μ q hμ hq P (fun r hr => isExit_of_exitFree r (he r hr))).2.1

@[sa_forward "MorphismsPoisson.poissonIso" 4]
theorem fwd4 (h : sa_impl% "MorphismsPoisson.poissonIso") : S4 := by
  intro σ _ _ μ q P he hμ hq w
  exact (h μ q hμ hq P (fun r hr => isExit_of_exitFree r (he r hr))).2.2.2.2.1 w trivial

@[sa_forward "MorphismsPoisson.poissonIso" 5]
theorem fwd5 (h : sa_impl% "MorphismsPoisson.poissonIso") : S5 := by
  intro σ _ _ μ q P he hμ hq v hv
  exact (h μ q hμ hq P (fun r hr => isExit_of_exitFree r (he r hr))).2.2.2.2.2 v hv

@[sa_backward "MorphismsPoisson.poissonIso"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) :
    sa_impl% "MorphismsPoisson.poissonIso" := by
  intro σ _ _ μ q hμ hq rs hrs
  have he : ExitFree rs := fun r hr => exitFree_of_isExit r (hrs r hr)
  exact And.intro (s1 μ q rs he hμ hq)
    (And.intro (s3 μ q rs he hμ hq)
      (And.intro (fun w _ => s2 μ q rs he hμ hq w)
        (And.intro (fun _ _ => trivial)
          (And.intro (fun w _ => s4 μ q rs he hμ hq w) (fun v hv => s5 μ q rs he hμ hq v hv)))))

end Alignment.Shadows.MorphismsPoisson.PoissonIso

/-! ## `MorphismsPoisson.poissonIsoSolution`

`(ebSys N q rs).F` is by definition `lift N q rs`, and `(sSys rs).F` is `sLift rs`. The registry
`impl` list is `[poisson_iso_solution_at, poisson_iso_solution]`, so `sa_impl%` is their
conjunction in that order. -/

namespace Alignment.Shadows.MorphismsPoisson.PoissonIsoSolution

sa_claim "MorphismsPoisson.poissonIsoSolution" group "MorphismsPoisson" required
  text "**The Poisson isomorphism on trajectories (M2).** Design statement (DESIGN_NetworkEpiCore.md §D.5, M2): \"EB_{Pois μ}(P) ≅ MA(D_μ P) via π(θ, φ, pop) = (qξe^{μ(θ−1)}, Φ = φ, X = pop)\"; §D.3: \"semiconjugacies map solution curves to solution curves\". [...] Scope: the Poisson(μ) network is taken with `μ ≠ 0`, as in the design, whose Poisson degree distributions have mean μ > 0 (for `μ = 0` the PGF has `ψ' ≡ 0` and the network has no edges). Solutions are mapped on any set of times `I`, both for derivatives within `I` (this theorem) and for two-sided derivatives at every `t ∈ I` (`poisson_iso_solution_at`), as amended by §M.5 and §M.10."
  impl NEP.poisson_iso_solution_at NEP.poisson_iso_solution

@[sa_forward "MorphismsPoisson.poissonIsoSolution" 1]
theorem fwd1 (h : sa_impl% "MorphismsPoisson.poissonIsoSolution") : S1 := by
  intro σ _ _ μ q P hμ I x hx
  exact h.2 μ q hμ P hx

/-- S2 (two-sided derivatives at every `t ∈ I`) is `poisson_iso_solution_at`. -/
@[sa_forward "MorphismsPoisson.poissonIsoSolution" 2]
theorem fwd2 (h : sa_impl% "MorphismsPoisson.poissonIsoSolution") : S2 := by
  intro σ _ _ μ q P hμ I x hx
  exact h.1 μ q hμ P hx

@[sa_backward "MorphismsPoisson.poissonIsoSolution"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "MorphismsPoisson.poissonIsoSolution" := by
  refine ⟨?_, ?_⟩
  · intro σ _ _ μ q hμ P I x hx
    exact s2 μ q P hμ I x hx
  · intro σ _ _ μ q hμ P I x hx
    exact s1 μ q P hμ I x hx

end Alignment.Shadows.MorphismsPoisson.PoissonIsoSolution

/-! ## `MorphismsPoisson.poissonIsoNatural`

`poissonMap μ q u ∘ dMap f` is definitionally `fun i => poissonMap μ q u (dMap f i)`. The impl
`poisson_iso_natural_min` puts the instances `[Fintype σ] [DecidableEq σ']` only on the pushforward
conjunct, exactly as the shadows do. The first two conjuncts are stated for all `μ, q`; S1 has no
`q`, so the checker instantiates the impl's `q` with `μ` (any real would do). -/

namespace Alignment.Shadows.MorphismsPoisson.PoissonIsoNatural

sa_claim "MorphismsPoisson.poissonIsoNatural" group "MorphismsPoisson" required
  text "**The Poisson isomorphism is natural in P (M2).** Design statement (DESIGN_NetworkEpiCore.md §D.5, M2): \"EB_{Pois μ}(P) ≅ MA(D_μ P) via π(θ, φ, pop) = (qξe^{μ(θ−1)}, Φ = φ, X = pop), natural in P\". [...] naturality with respect to the species maps of the syntax (relabelling and gluing), [...] it is not stated as a natural transformation of functors into `DynSys`. [...] `D_μ` commutes with relabelling species, and the map commutes with the pullback and pushforward of coordinates along species maps."
  impl NEP.poisson_iso_natural_min

@[sa_forward "MorphismsPoisson.poissonIsoNatural" 1]
theorem fwd1 (h : sa_impl% "MorphismsPoisson.poissonIsoNatural") : S1 := by
  intro σ σ' f μ P
  exact (h μ μ f).1 P

@[sa_forward "MorphismsPoisson.poissonIsoNatural" 2]
theorem fwd2 (h : sa_impl% "MorphismsPoisson.poissonIsoNatural") : S2 := by
  intro σ σ' f μ q u
  exact (h μ q f).2.1 u

@[sa_forward "MorphismsPoisson.poissonIsoNatural" 3]
theorem fwd3 (h : sa_impl% "MorphismsPoisson.poissonIsoNatural") : S3 := by
  intro σ σ' _ _ f μ q u
  exact (h μ q f).2.2 u

@[sa_backward "MorphismsPoisson.poissonIsoNatural"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) : sa_impl% "MorphismsPoisson.poissonIsoNatural" := by
  intro σ σ' μ q f
  refine And.intro (fun rs => s1 f μ rs) (And.intro (fun u => s2 f μ q u) ?_)
  intro _ _ u
  exact s3 f μ q u

end Alignment.Shadows.MorphismsPoisson.PoissonIsoNatural

/-! ## `MorphismsPoisson.poissonDSirField`

After ζ-reduction of the impl's `let`s, its five conjuncts are literally S1–S5 (the shadow's
species abbreviations `sS`, `sPhiI`, … unfold to `none`, `some (.inl .I)`, …). -/

namespace Alignment.Shadows.MorphismsPoisson.PoissonDSirField

sa_claim "MorphismsPoisson.poissonDSirField" group "MorphismsPoisson" required
  text "**The mass-action equations of `D_μ(SIR)` (M2, SIR).** Design statement (DESIGN_NetworkEpiCore.md §D.5, M2): \"D_μ: contacts S + Φ_J → Φ_X + X + Φ_J at rate μτ; Φ_J → ∅ at τ; transitions on both copies\"."
  impl NEP.poissonD_sir_field

@[sa_forward "MorphismsPoisson.poissonDSirField" 1]
theorem fwd1 (h : sa_impl% "MorphismsPoisson.poissonDSirField") : S1 := by
  intro μ τ γ x
  exact (h μ τ γ x).1

@[sa_forward "MorphismsPoisson.poissonDSirField" 2]
theorem fwd2 (h : sa_impl% "MorphismsPoisson.poissonDSirField") : S2 := by
  intro μ τ γ x
  exact (h μ τ γ x).2.1

@[sa_forward "MorphismsPoisson.poissonDSirField" 3]
theorem fwd3 (h : sa_impl% "MorphismsPoisson.poissonDSirField") : S3 := by
  intro μ τ γ x
  exact (h μ τ γ x).2.2.1

@[sa_forward "MorphismsPoisson.poissonDSirField" 4]
theorem fwd4 (h : sa_impl% "MorphismsPoisson.poissonDSirField") : S4 := by
  intro μ τ γ x
  exact (h μ τ γ x).2.2.2.1

@[sa_forward "MorphismsPoisson.poissonDSirField" 5]
theorem fwd5 (h : sa_impl% "MorphismsPoisson.poissonDSirField") : S5 := by
  intro μ τ γ x
  exact (h μ τ γ x).2.2.2.2

@[sa_backward "MorphismsPoisson.poissonDSirField"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) :
    sa_impl% "MorphismsPoisson.poissonDSirField" := by
  intro μ τ γ v
  exact And.intro (s1 μ τ γ v)
    (And.intro (s2 μ τ γ v) (And.intro (s3 μ τ γ v) (And.intro (s4 μ τ γ v) (s5 μ τ γ v))))

end Alignment.Shadows.MorphismsPoisson.PoissonDSirField

/-! ## `MorphismsPoisson.poissonIsoSir`

`poissonMap μ q ∘ EB1.incl` is definitionally `piSlice μ q`, and `{v | 0 < v none}` is
definitionally `SPos SIRSp`. The impl `poisson_iso_sir_iso` is stated in the shadows' form
(semiconjugacy on the whole space, values in `S > 0`, an existential inverse). -/

namespace Alignment.Shadows.MorphismsPoisson.PoissonIsoSir

sa_claim "MorphismsPoisson.poissonIsoSir" group "MorphismsPoisson" required
  text "**The Poisson isomorphism for SIR (M2, SIR instance).** Design statement (DESIGN_NetworkEpiCore.md §D.5, M2): \"Poisson isomorphism | EB_{Pois μ}(P) ≅ MA(D_μ P) via π(θ, φ, pop) = (qξe^{μ(θ−1)}, Φ = φ, X = pop) [...] | natural iso onto S > 0\"; §D.7, L4b: \"SIR/SEIR concrete first\"."
  impl NEP.poisson_iso_sir_iso

@[sa_forward "MorphismsPoisson.poissonIsoSir" 1]
theorem fwd1 (h : sa_impl% "MorphismsPoisson.poissonIsoSir") : S1 := by
  intro μ q τ γ hμ hq
  exact (h μ τ γ q hμ hq).1

@[sa_forward "MorphismsPoisson.poissonIsoSir" 2]
theorem fwd2 (h : sa_impl% "MorphismsPoisson.poissonIsoSir") : S2 := by
  intro μ q hμ hq w
  exact (h μ μ μ q hμ hq).2.1 w

@[sa_forward "MorphismsPoisson.poissonIsoSir" 3]
theorem fwd3 (h : sa_impl% "MorphismsPoisson.poissonIsoSir") : S3 := by
  intro μ q τ γ hμ hq
  exact (h μ τ γ q hμ hq).2.2

@[sa_backward "MorphismsPoisson.poissonIsoSir"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) : sa_impl% "MorphismsPoisson.poissonIsoSir" := by
  intro μ τ γ q hμ hq
  exact And.intro (s1 μ q τ γ hμ hq) (And.intro (s2 μ q hμ hq) (s3 μ q τ γ hμ hq))

end Alignment.Shadows.MorphismsPoisson.PoissonIsoSir

/-! ## `MorphismsPoisson.poissonIsoSeir`

`poissonMap μ q ∘ EB1.incl` is definitionally `piSlice μ q`, and `{v | 0 < v none}` is
definitionally `SPos SEIRSp`. The impl `poisson_iso_seir_iso` is stated in the shadows' form
(semiconjugacy on the whole space, values in `S > 0`, an existential inverse). -/

namespace Alignment.Shadows.MorphismsPoisson.PoissonIsoSeir

sa_claim "MorphismsPoisson.poissonIsoSeir" group "MorphismsPoisson" required
  text "**The Poisson isomorphism for SEIR (M2, SEIR instance).** Design statement (DESIGN_NetworkEpiCore.md §D.5, M2): \"Poisson isomorphism | EB_{Pois μ}(P) ≅ MA(D_μ P) via π(θ, φ, pop) = (qξe^{μ(θ−1)}, Φ = φ, X = pop) [...] | natural iso onto S > 0\"; §D.7, L4b: \"SIR/SEIR concrete first\"."
  impl NEP.poisson_iso_seir_iso

@[sa_forward "MorphismsPoisson.poissonIsoSeir" 1]
theorem fwd1 (h : sa_impl% "MorphismsPoisson.poissonIsoSeir") : S1 := by
  intro μ q τ a γ hμ hq
  exact (h μ τ a γ q hμ hq).1

@[sa_forward "MorphismsPoisson.poissonIsoSeir" 2]
theorem fwd2 (h : sa_impl% "MorphismsPoisson.poissonIsoSeir") : S2 := by
  intro μ q hμ hq w
  exact (h μ μ μ μ q hμ hq).2.1 w

@[sa_forward "MorphismsPoisson.poissonIsoSeir" 3]
theorem fwd3 (h : sa_impl% "MorphismsPoisson.poissonIsoSeir") : S3 := by
  intro μ q τ a γ hμ hq
  exact (h μ τ a γ q hμ hq).2.2

@[sa_backward "MorphismsPoisson.poissonIsoSeir"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) : sa_impl% "MorphismsPoisson.poissonIsoSeir" := by
  intro μ τ a γ q hμ hq
  exact And.intro (s1 μ q τ a γ hμ hq) (And.intro (s2 μ q hμ hq) (s3 μ q τ a γ hμ hq))

end Alignment.Shadows.MorphismsPoisson.PoissonIsoSeir

/-! ## `MorphismsPoisson.poissonDLNone` -/

namespace Alignment.Shadows.MorphismsPoisson.PoissonDLNone

sa_claim "MorphismsPoisson.poissonDLNone" group "MorphismsPoisson" required
  text "The `S`-component of `poissonDL`: `q (v_ξ e^{μ(θ−1)} + ξ μ e^{μ(θ−1)} v_θ)`."
  impl NEP.poissonDL_none_left

@[sa_forward "MorphismsPoisson.poissonDLNone" 1]
theorem fwd1 (h : sa_impl% "MorphismsPoisson.poissonDLNone") : S1 := by
  intro σ μ q u v
  exact h μ q u v

@[sa_backward "MorphismsPoisson.poissonDLNone"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsPoisson.poissonDLNone" := by
  intro σ μ q u v
  exact s1 μ q u v

end Alignment.Shadows.MorphismsPoisson.PoissonDLNone

/-! ## `MorphismsPoisson.poissonDLInl` -/

namespace Alignment.Shadows.MorphismsPoisson.PoissonDLInl

sa_claim "MorphismsPoisson.poissonDLInl" group "MorphismsPoisson" required
  text "The `Φ_X`-component of `poissonDL` is `v_{φ_X}`."
  impl NEP.poissonDL_inl

@[sa_forward "MorphismsPoisson.poissonDLInl" 1]
theorem fwd1 (h : sa_impl% "MorphismsPoisson.poissonDLInl") : S1 := by
  intro σ μ q u v X
  exact h μ q u v X

@[sa_backward "MorphismsPoisson.poissonDLInl"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsPoisson.poissonDLInl" := by
  intro σ μ q u v X
  exact s1 μ q u v X

end Alignment.Shadows.MorphismsPoisson.PoissonDLInl

/-! ## `MorphismsPoisson.poissonDLInr` -/

namespace Alignment.Shadows.MorphismsPoisson.PoissonDLInr

sa_claim "MorphismsPoisson.poissonDLInr" group "MorphismsPoisson" required
  text "The node-copy `X`-component of `poissonDL` is `v_{pop_X}`."
  impl NEP.poissonDL_inr

@[sa_forward "MorphismsPoisson.poissonDLInr" 1]
theorem fwd1 (h : sa_impl% "MorphismsPoisson.poissonDLInr") : S1 := by
  intro σ μ q u v X
  exact h μ q u v X

@[sa_backward "MorphismsPoisson.poissonDLInr"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsPoisson.poissonDLInr" := by
  intro σ μ q u v X
  exact s1 μ q u v X

end Alignment.Shadows.MorphismsPoisson.PoissonDLInr

/-! ## `MorphismsPoisson.hasFDerivAtPoissonMap` -/

namespace Alignment.Shadows.MorphismsPoisson.HasFDerivAtPoissonMap

sa_claim "MorphismsPoisson.hasFDerivAtPoissonMap" group "MorphismsPoisson" required
  text "`poissonMap μ q` has derivative `poissonDL μ q u` at every `u`."
  impl NEP.hasFDerivAt_poissonMap_all

@[sa_forward "MorphismsPoisson.hasFDerivAtPoissonMap" 1]
theorem fwd1 (h : sa_impl% "MorphismsPoisson.hasFDerivAtPoissonMap") : S1 := by
  intro σ μ q u
  exact h μ q u

@[sa_backward "MorphismsPoisson.hasFDerivAtPoissonMap"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsPoisson.hasFDerivAtPoissonMap" := by
  intro σ μ q u
  exact s1 μ q u

end Alignment.Shadows.MorphismsPoisson.HasFDerivAtPoissonMap

/-! ## The derivative of `poissonMap` (bridge helper, finite `σ`) -/

namespace Alignment.Shadows.MorphismsPoisson

/-- Helper for the bridge (not a checker): `poissonMap μ q` has Fréchet derivative
`poissonDL μ q u` at `u`, for finite `σ`. Proved from Mathlib calculus lemmas only. It does not use
`NEP.hasFDerivAt_poissonMap`, `NEP.hasFDerivAt_susc`, `NEP.suscD_apply`,
`NEP.CNet.poisson_hasDerivAt_ψ` or any other implementation theorem. -/
theorem hasFDerivAt_poissonMap_aux {σ : Type} [Fintype σ] (μ q : ℝ) (u : EB σ) :
    HasFDerivAt (poissonMap μ q) (poissonDL μ q u) u := by
  refine hasFDerivAt_pi'.2 fun i => ?_
  rw [poissonDL, ContinuousLinearMap.proj_pi]
  rcases i with _ | X | X
  · have hθ : HasFDerivAt (fun u : EB σ => u.1) (ContinuousLinearMap.fst ℝ ℝ _) u :=
      hasFDerivAt_fst
    have hξ := (hasFDerivAt_snd (𝕜 := ℝ) (p := u)).fst
    have hE := ((hθ.sub_const 1).const_mul μ).exp
    have hS := (hξ.const_mul q).mul hE
    change HasFDerivAt (fun u : EB σ => q * u.2.1 * Real.exp (μ * (u.1 - 1)))
      (suscD (CNet.poisson μ) q u) u
    refine hS.congr_fderiv ?_
    ext v <;> simp [suscD, ebXi, ebTheta, CNet.poisson] <;> first | ring1 | exact Or.inl (mul_comm _ _)
  · exact ((ContinuousLinearMap.proj X).comp ebPhi).hasFDerivAt
  · exact ((ContinuousLinearMap.proj X).comp ebPop).hasFDerivAt

end Alignment.Shadows.MorphismsPoisson

/-! ## `MorphismsPoisson.poissonEbField`

The impl `poisson_ebField_fderiv` is stated with Mathlib's `fderiv ℝ (poissonMap μ q) u` for finite
`σ`, exactly as S1, so the checkers need no bridge. `bridge_poissonDL` is kept only because
`Alignment.ReviewedBridges` holds a review record for it; no checker uses it. -/

namespace Alignment.Shadows.MorphismsPoisson.PoissonEbField

sa_claim "MorphismsPoisson.poissonEbField" group "MorphismsPoisson" required
  text "**Per-reaction identity behind M2.** On the Poisson(μ) network with `μ ≠ 0`, the derivative of `poissonMap` carries the EB field of each T_EB reaction `r` to the multiset mass-action field of `D_μ r` at the image point."
  impl NEP.poisson_ebField_fderiv

/-- Bridge (needs independent review). The trusted definition `poissonDL μ q u` (docstring: "The
derivative of `poissonMap μ q` at `u`") is the text's "the derivative of `poissonMap`" at `u`,
i.e. Mathlib's Fréchet derivative `fderiv ℝ (poissonMap μ q) u` (finite `σ`, so `EB σ` is a
finite-dimensional normed space). The proof recomputes the derivative with Mathlib calculus lemmas
(`hasFDerivAt_poissonMap_aux`). It uses no implementation theorem, in particular not
`NEP.hasFDerivAt_poissonMap`. -/
@[sa_bridge "MorphismsPoisson.poissonEbField"]
theorem bridge_poissonDL {σ : Type} [Fintype σ] (μ q : ℝ) (u : EB σ) :
    poissonDL μ q u = fderiv ℝ (poissonMap μ q) u :=
  (Alignment.Shadows.MorphismsPoisson.hasFDerivAt_poissonMap_aux μ q u).fderiv.symm

@[sa_forward "MorphismsPoisson.poissonEbField" 1]
theorem fwd1 (h : sa_impl% "MorphismsPoisson.poissonEbField") : S1 := by
  intro σ _ _ μ q r u hμ
  exact h μ q hμ r u

@[sa_backward "MorphismsPoisson.poissonEbField"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsPoisson.poissonEbField" := by
  intro σ _ _ μ q hμ r u
  exact s1 μ q r u hμ

end Alignment.Shadows.MorphismsPoisson.PoissonEbField

/-! ## `MorphismsPoisson.rxnPoissonDMap` -/

namespace Alignment.Shadows.MorphismsPoisson.RxnPoissonDMap

sa_claim "MorphismsPoisson.rxnPoissonDMap" group "MorphismsPoisson" required
  text "`D_μ` commutes with relabelling the node species of one reaction."
  impl NEP.Rxn.poissonD_map

@[sa_forward "MorphismsPoisson.rxnPoissonDMap" 1]
theorem fwd1 (h : sa_impl% "MorphismsPoisson.rxnPoissonDMap") : S1 := by
  intro σ σ' f μ r
  exact h μ f r

@[sa_backward "MorphismsPoisson.rxnPoissonDMap"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsPoisson.rxnPoissonDMap" := by
  intro σ σ' μ f r
  exact s1 f μ r

end Alignment.Shadows.MorphismsPoisson.RxnPoissonDMap

/-! ## `MorphismsPoisson.sirRxnsNoExit` -/

namespace Alignment.Shadows.MorphismsPoisson.SirRxnsNoExit
open Alignment.Shadows.MorphismsPoisson

sa_claim "MorphismsPoisson.sirRxnsNoExit" group "MorphismsPoisson" required
  text "SIR has no exits."
  impl NEP.sirRxns_noExit

@[sa_forward "MorphismsPoisson.sirRxnsNoExit" 1]
theorem fwd1 (h : sa_impl% "MorphismsPoisson.sirRxnsNoExit") : S1 := by
  intro τ γ r hr
  exact exitFree_of_isExit r (h τ γ r hr)

@[sa_backward "MorphismsPoisson.sirRxnsNoExit"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsPoisson.sirRxnsNoExit" := by
  intro τ γ r hr
  exact isExit_of_exitFree r (s1 τ γ r hr)

end Alignment.Shadows.MorphismsPoisson.SirRxnsNoExit

/-! ## `MorphismsPoisson.seirRxnsNoExit` -/

namespace Alignment.Shadows.MorphismsPoisson.SeirRxnsNoExit
open Alignment.Shadows.MorphismsPoisson

sa_claim "MorphismsPoisson.seirRxnsNoExit" group "MorphismsPoisson" required
  text "SEIR has no exits."
  impl NEP.seirRxns_noExit

@[sa_forward "MorphismsPoisson.seirRxnsNoExit" 1]
theorem fwd1 (h : sa_impl% "MorphismsPoisson.seirRxnsNoExit") : S1 := by
  intro τ a γ r hr
  exact exitFree_of_isExit r (h τ a γ r hr)

@[sa_backward "MorphismsPoisson.seirRxnsNoExit"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsPoisson.seirRxnsNoExit" := by
  intro τ a γ r hr
  exact isExit_of_exitFree r (s1 τ a γ r hr)

end Alignment.Shadows.MorphismsPoisson.SeirRxnsNoExit
