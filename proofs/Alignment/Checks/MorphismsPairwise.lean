import Alignment.Registry
import Alignment.Shadows.MorphismsPairwise

/-!
# Checkers: group `MorphismsPairwise` (trusted module `NetworkEpi.Morphisms.Pairwise`)

Checker author (SA-PASS role 3, non-blind). For each of the ten `implemented` claims of
`NetworkEpi/Morphisms/Pairwise.lean` this file holds the `sa_claim` registration (verbatim registry
text, registry `impl` list), the forward checkers `sa_impl% → Sᵢ`, the backward checker
`S₁ → … → Sₙ → sa_impl%`, and an `sa_fail_*` record wherever a check is not structurally
derivable. The informal `header.target` and `header.notFreeScalar` and the missing
`constClosureOnlyIf` are not registered, as in the other groups.

The seven claims `ebToPwsSolution`, `ebToPwsSir`, `ebToPwsSeir`, `ebToPwsPt`, `ebToPwsPoisson`,
`pwsEbField`, `pwsDomainPoisson` were re-checked after the text remediation and the blind
re-shadow (impls: the `…_global`, `…_any`, `…_closure_one`, `…_solution_at`, `…_of_mul`,
`…_spec` restatements).

## Bridges

None. Every identification is definitional: the blind `DomU N Θ` is the trusted `pwsDomain N Θ`
(same set-builder body), `DomU0 N` is the set `{u | ψ ≠ 0 ∧ ψ' ≠ 0 ∧ ξ ≠ 0}` of the `…_global` and
`…_any` impls, a point of `DomU0 N` is in `pwsDomain N Set.univ` because `u.1 ∈ Set.univ` is
`True`, `(ebSys N q rs).F` is `lift N q rs`, `(pgfSys N rs).F` is `pgfLift N rs`, and
`IsSemiconjOn A B U π` is `DiffOnU A B U π ∧ CommOnU A B U π` by definition.

## Recorded failures

None. `ebToPwsSolution` uses the global-C² corollaries (`eb_to_pws_solution{_at}_global`) and
`pwsDomainPoisson` the `μ ≠ 0` restatement `pwsDomain_poisson_of_ne`.
-/

open NEP

/-! ## `MorphismsPairwise.ebToPws` -/
namespace Alignment.Shadows.MorphismsPairwise.EbToPws
open Alignment.Shadows.MorphismsPairwise

sa_claim "MorphismsPairwise.ebToPws" group "MorphismsPairwise" required
  text "**EB → S-anchored pairwise with the PGF closure, for every ψ and every T_EB model (M6).** Design statement (DESIGN_NetworkEpiCore.md §D.5, M6): \"**EB → S-anchored pairwise** | π^PW(θ, ξ, φ, pop) = (θ, [s] = qξψ(θ), [sX] = qξψ'(θ)φ_X, [ss] = q²ξ²ψ'(θ)²/ψ'(1), [X] = pop_X) onto PW^S with closure [Z s J] = K_ψ(θ)[Zs][sJ]/[s], K_ψ = ψψ''/ψ'². It holds **for every C² ψ and every T_EB model**, on U = {ψ ≠ 0, ψ' ≠ 0} (the DSA closure, Kiss, Kenah & Rempała 2023) | natural semiconjugacy\"; §A.4: \"`PGFClosure()`: the S-anchored subsystem with closure K_ψ(θ) = ψ(θ)ψ''(θ)/ψ'(θ)² and an auxiliary θ, where θ̇ = −Σ_r τ_r [s J_r]/(qξψ'(θ)). It is exact against EB for every ψ (M6)\".
[...]
No condition on ψ'(1) is needed.
[...]
for every T_EB reaction list (contacts, exits, progressions, removals), every configuration network and every set Θ of θ values at which ψ' and ψ'' are the derivatives of ψ and ψ', π^PW is a local semiconjugacy from EB to `pgfSys` on `U = {θ ∈ Θ, ψ(θ) ≠ 0, ψ'(θ) ≠ 0, ξ ≠ 0}` (for `q ≠ 0`)."
  impl NEP.eb_to_pws

@[sa_forward "MorphismsPairwise.ebToPws" 1]
theorem fwd1 (h : sa_impl% "MorphismsPairwise.ebToPws") : S1 := by
  intro σ _ _ N q rs Θ hq hd
  exact h N q hq Θ (fun θ hθ => (hd θ hθ).1) (fun θ hθ => (hd θ hθ).2) rs

@[sa_backward "MorphismsPairwise.ebToPws"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsPairwise.ebToPws" := by
  intro σ _ _ N q hq Θ hψ hψ' rs
  exact s1 N q rs Θ hq (fun θ hθ => ⟨hψ θ hθ, hψ' θ hθ⟩)

end Alignment.Shadows.MorphismsPairwise.EbToPws

/-! ## `MorphismsPairwise.ebToPwsSolution` -/
namespace Alignment.Shadows.MorphismsPairwise.EbToPwsSolution
open Alignment.Shadows.MorphismsPairwise

sa_claim "MorphismsPairwise.ebToPwsSolution" group "MorphismsPairwise" required
  text "**EB → PW^S on trajectories (M6).** Design statement (DESIGN_NetworkEpiCore.md §D.5, M6): \"π^PW(θ, ξ, φ, pop) = (θ, [s] = qξψ(θ), [sX] = qξψ'(θ)φ_X, [ss] = q²ξ²ψ'(θ)²/ψ'(1), [X] = pop_X) onto PW^S with closure [Z s J] = K_ψ(θ)[Zs][sJ]/[s], K_ψ = ψψ''/ψ'². It holds **for every C² ψ and every T_EB model**, on U = {ψ ≠ 0, ψ' ≠ 0}\"; §D.3: \"solutions that stay in U are mapped\".
[...]
EB solutions that stay in `U` map to PGF-closure solutions."
  impl NEP.eb_to_pws_solution_at_global NEP.eb_to_pws_solution_global

/-- S1 (two-sided derivatives on `I`) is the first impl `eb_to_pws_solution_at_global`; `C2 N`
and `DomU0 N` are its hypotheses by definition. -/
@[sa_forward "MorphismsPairwise.ebToPwsSolution" 1]
theorem fwd1 (h : sa_impl% "MorphismsPairwise.ebToPwsSolution") : S1 := by
  intro σ _ _ N q rs I x hq hc hx hU
  exact h.1 N q rs I x hq hc hx hU

/-- S2 (within-`I` solutions) is the second impl `eb_to_pws_solution_global`. -/
@[sa_forward "MorphismsPairwise.ebToPwsSolution" 2]
theorem fwd2 (h : sa_impl% "MorphismsPairwise.ebToPwsSolution") : S2 := by
  intro σ _ _ N q rs I x hq hc hx hU
  exact h.2 N q rs I x hq hc hx hU

@[sa_backward "MorphismsPairwise.ebToPwsSolution"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "MorphismsPairwise.ebToPwsSolution" := by
  refine ⟨?_, ?_⟩
  · intro σ _ _ N q rs I x hq hc hx hU
    exact s1 N q rs I x hq hc hx hU
  · intro σ _ _ N q rs I x hq hc hx hU
    exact s2 N q rs I x hq hc hx hU

end Alignment.Shadows.MorphismsPairwise.EbToPwsSolution

/-! ## `MorphismsPairwise.ebToPwsSir` -/
namespace Alignment.Shadows.MorphismsPairwise.EbToPwsSir
open Alignment.Shadows.MorphismsPairwise

sa_claim "MorphismsPairwise.ebToPwsSir" group "MorphismsPairwise" required
  text "**EB → PW^S for SIR (M6, SIR instance).** Design statement (DESIGN_NetworkEpiCore.md §D.5, M6): \"It holds **for every C² ψ and every T_EB model**, on U = {ψ ≠ 0, ψ' ≠ 0}\"; §D.7, L4e: \"SIR and SEIR with generic C² ψ via `HasDerivAt` hypotheses\"."
  impl NEP.eb_to_pws_sir_global

/-- `DomU0 N` is by definition the impl's set `{u | ψ ≠ 0 ∧ ψ' ≠ 0 ∧ ξ ≠ 0}`, and `DiffOnU`,
`CommOnU` are by definition the two conjuncts of `IsSemiconjOn`. -/
@[sa_forward "MorphismsPairwise.ebToPwsSir" 1]
theorem fwd1 (h : sa_impl% "MorphismsPairwise.ebToPwsSir") : S1 := by
  intro N q τ γ hq hc
  exact (h N q τ γ hq (fun θ => (hc θ).1) (fun θ => (hc θ).2)).1

@[sa_forward "MorphismsPairwise.ebToPwsSir" 2]
theorem fwd2 (h : sa_impl% "MorphismsPairwise.ebToPwsSir") : S2 := by
  intro N q τ γ hq hc
  exact (h N q τ γ hq (fun θ => (hc θ).1) (fun θ => (hc θ).2)).2

@[sa_backward "MorphismsPairwise.ebToPwsSir"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "MorphismsPairwise.ebToPwsSir" := by
  intro N q τ γ hq hψ hψ'
  exact ⟨s1 N q τ γ hq (fun θ => ⟨hψ θ, hψ' θ⟩), s2 N q τ γ hq (fun θ => ⟨hψ θ, hψ' θ⟩)⟩

end Alignment.Shadows.MorphismsPairwise.EbToPwsSir

/-! ## `MorphismsPairwise.ebToPwsSeir` -/
namespace Alignment.Shadows.MorphismsPairwise.EbToPwsSeir
open Alignment.Shadows.MorphismsPairwise

sa_claim "MorphismsPairwise.ebToPwsSeir" group "MorphismsPairwise" required
  text "**EB → PW^S for SEIR (M6, SEIR instance).** Design statement (DESIGN_NetworkEpiCore.md §D.5, M6): \"It holds **for every C² ψ and every T_EB model**, on U = {ψ ≠ 0, ψ' ≠ 0}\"; §D.7, L4e: \"SIR and SEIR with generic C² ψ via `HasDerivAt` hypotheses\"."
  impl NEP.eb_to_pws_seir_global

@[sa_forward "MorphismsPairwise.ebToPwsSeir" 1]
theorem fwd1 (h : sa_impl% "MorphismsPairwise.ebToPwsSeir") : S1 := by
  intro N q τ a γ hq hc
  exact (h N q τ a γ hq (fun θ => (hc θ).1) (fun θ => (hc θ).2)).1

@[sa_forward "MorphismsPairwise.ebToPwsSeir" 2]
theorem fwd2 (h : sa_impl% "MorphismsPairwise.ebToPwsSeir") : S2 := by
  intro N q τ a γ hq hc
  exact (h N q τ a γ hq (fun θ => (hc θ).1) (fun θ => (hc θ).2)).2

@[sa_backward "MorphismsPairwise.ebToPwsSeir"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "MorphismsPairwise.ebToPwsSeir" := by
  intro N q τ a γ hq hψ hψ'
  exact ⟨s1 N q τ a γ hq (fun θ => ⟨hψ θ, hψ' θ⟩), s2 N q τ a γ hq (fun θ => ⟨hψ θ, hψ' θ⟩)⟩

end Alignment.Shadows.MorphismsPairwise.EbToPwsSeir

/-! ## `MorphismsPairwise.ebToPwsConst` -/
namespace Alignment.Shadows.MorphismsPairwise.EbToPwsConst
open Alignment.Shadows.MorphismsPairwise

sa_claim "MorphismsPairwise.ebToPwsConst" group "MorphismsPairwise" required
  text "**The constant-closure pairwise model is exact when K_ψ is constant (M6 with M8).** Design statement (DESIGN_NetworkEpiCore.md §D.5, M8): \"So NBM's constant closure ⟨k(k−1)⟩/⟨k⟩² is exact **iff** the degree distribution is PT\"; M6: \"onto PW^S with closure [Z s J] = K_ψ(θ)[Zs][sJ]/[s], K_ψ = ψψ''/ψ'²\".
[...]
this is the \"if\" direction of the design's \"exact iff PT\"
[...]
if `K_ψ ≡ κ` on Θ, the PW^S part alone, with the **constant** closure κ, is the image of EB: the constant-closure pairwise model is exact."
  impl NEP.eb_to_pws_const

@[sa_forward "MorphismsPairwise.ebToPwsConst" 1]
theorem fwd1 (h : sa_impl% "MorphismsPairwise.ebToPwsConst") : S1 := by
  intro σ _ _ N q rs Θ κ hq hd hK
  exact h N q κ hq Θ (fun θ hθ => (hd θ hθ).1) (fun θ hθ => (hd θ hθ).2) hK rs

@[sa_backward "MorphismsPairwise.ebToPwsConst"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsPairwise.ebToPwsConst" := by
  intro σ _ _ N q κ hq Θ hψ hψ' hK rs
  exact s1 N q rs Θ κ hq (fun θ hθ => ⟨hψ θ hθ, hψ' θ hθ⟩) hK

end Alignment.Shadows.MorphismsPairwise.EbToPwsConst

/-! ## `MorphismsPairwise.ebToPwsPt` -/
namespace Alignment.Shadows.MorphismsPairwise.EbToPwsPt
open Alignment.Shadows.MorphismsPairwise

sa_claim "MorphismsPairwise.ebToPwsPt" group "MorphismsPairwise" required
  text "**For a Poisson-type degree distribution the constant closure is exact (M8 ⇒ M6).** Design statement (DESIGN_NetworkEpiCore.md §D.5, M8): \"PT ⇔ constant closure | On an interval I with ψ > 0: K_ψ ≡ κ ⇔ ψ' = αψ^κ [...] So NBM's constant closure ⟨k(k−1)⟩/⟨k⟩² is exact **iff** the degree distribution is PT\"; §C.3: \"heterogeneous pairwise with constant K = closure_constant(d) (exact iff PT, M8)\".
[...]
the \"if\" direction of \"exact iff PT\""
  impl NEP.eb_to_pws_pt_any NEP.eb_to_pws_pt_closure_one

/-- S1 from the first impl `eb_to_pws_pt_any` (PT exponent κ): the `Hyp` bundle gives exactly the
impl's hypotheses, with the PT witness α taken from `PT N Θ κ`. -/
@[sa_forward "MorphismsPairwise.ebToPwsPt" 1]
theorem fwd1 (h : sa_impl% "MorphismsPairwise.ebToPwsPt") : S1 := by
  intro σ _ _ N q rs Θ κ hyp
  exact Exists.elim hyp.2.2.2.2.2 fun α hPT =>
    (h.1 N q α κ hyp.1 Θ hyp.2.2.1 hyp.2.2.2.1 (fun θ hθ => (hyp.2.1 θ hθ).1)
      (fun θ hθ => (hyp.2.1 θ hθ).2) hyp.2.2.2.2.1 hPT rs).1

@[sa_forward "MorphismsPairwise.ebToPwsPt" 2]
theorem fwd2 (h : sa_impl% "MorphismsPairwise.ebToPwsPt") : S2 := by
  intro σ _ _ N q rs Θ κ hyp
  exact Exists.elim hyp.2.2.2.2.2 fun α hPT =>
    (h.1 N q α κ hyp.1 Θ hyp.2.2.1 hyp.2.2.2.1 (fun θ hθ => (hyp.2.1 θ hθ).1)
      (fun θ hθ => (hyp.2.1 θ hθ).2) hyp.2.2.2.2.1 hPT rs).2

/-- S3 (NBM's closure ψ''(1)/ψ'(1)²) from the second impl `eb_to_pws_pt_closure_one`. -/
@[sa_forward "MorphismsPairwise.ebToPwsPt" 3]
theorem fwd3 (h : sa_impl% "MorphismsPairwise.ebToPwsPt") : S3 := by
  intro σ _ _ N q rs Θ κ hyp h1 hψ1
  exact Exists.elim hyp.2.2.2.2.2 fun α hPT =>
    (h.2 N q α κ hyp.1 Θ hyp.2.2.1 hyp.2.2.2.1 (fun θ hθ => (hyp.2.1 θ hθ).1)
      (fun θ hθ => (hyp.2.1 θ hθ).2) hyp.2.2.2.2.1 hPT h1 hψ1 rs).2

/-- Both impls from the shadows. The differentiability part of the second impl is S1:
`DiffOnU A B U π` mentions `B` only through `B.V`, and `(pwSSys K rs).V = PWS σ` for every `K`,
so S1 at κ is by definition the differentiability for the target `pwSSys (ψ''(1)/ψ'(1)²) rs`. -/
@[sa_backward "MorphismsPairwise.ebToPwsPt"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) : sa_impl% "MorphismsPairwise.ebToPwsPt" := by
  refine ⟨?_, ?_⟩
  · intro σ _ _ N q α κ hq Θ hΘ hΘi hψ hψ' hpos hPT rs
    have hyp : EbToPwsPt.Hyp N q Θ κ :=
      ⟨hq, fun θ hθ => ⟨hψ θ hθ, hψ' θ hθ⟩, hΘ, hΘi, hpos, α, hPT⟩
    exact ⟨s1 N q rs Θ κ hyp, s2 N q rs Θ κ hyp⟩
  · intro σ _ _ N q α κ hq Θ hΘ hΘi hψ hψ' hpos hPT h1 hψ1 rs
    have hyp : EbToPwsPt.Hyp N q Θ κ :=
      ⟨hq, fun θ hθ => ⟨hψ θ hθ, hψ' θ hθ⟩, hΘ, hΘi, hpos, α, hPT⟩
    exact ⟨s1 N q rs Θ κ hyp, s3 N q rs Θ κ hyp h1 hψ1⟩

end Alignment.Shadows.MorphismsPairwise.EbToPwsPt

/-! ## `MorphismsPairwise.ebToPwsPoisson` -/
namespace Alignment.Shadows.MorphismsPairwise.EbToPwsPoisson
open Alignment.Shadows.MorphismsPairwise

sa_claim "MorphismsPairwise.ebToPwsPoisson" group "MorphismsPairwise" required
  text "**On a Poisson network the constant closure K = 1 is exact (M6, M8, Poisson instance).** Design statement (DESIGN_NetworkEpiCore.md §D.5, M8): \"So NBM's constant closure ⟨k(k−1)⟩/⟨k⟩² is exact **iff** the degree distribution is PT\"; §0: \"This covers Poisson (κ = 1)\"."
  impl NEP.eb_to_pws_poisson_any

/-- `DomU0 (poisson μ)` is by definition the impl's set. -/
@[sa_forward "MorphismsPairwise.ebToPwsPoisson" 1]
theorem fwd1 (h : sa_impl% "MorphismsPairwise.ebToPwsPoisson") : S1 := by
  intro σ _ _ μ q rs hq
  exact (h μ q hq rs).1

@[sa_forward "MorphismsPairwise.ebToPwsPoisson" 2]
theorem fwd2 (h : sa_impl% "MorphismsPairwise.ebToPwsPoisson") : S2 := by
  intro σ _ _ μ q rs hq
  exact (h μ q hq rs).2

@[sa_backward "MorphismsPairwise.ebToPwsPoisson"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "MorphismsPairwise.ebToPwsPoisson" := by
  intro σ _ _ μ q hq rs
  exact ⟨s1 μ q rs hq, s2 μ q rs hq⟩

end Alignment.Shadows.MorphismsPairwise.EbToPwsPoisson

/-! ## `MorphismsPairwise.hasFDerivAtPwImage` -/
namespace Alignment.Shadows.MorphismsPairwise.HasFDerivAtPwImage
open Alignment.Shadows.MorphismsPairwise

sa_claim "MorphismsPairwise.hasFDerivAtPwImage" group "MorphismsPairwise" required
  text "π^PW has derivative `pwD N q u` at every state whose θ is a point where ψ' and ψ'' are the derivatives of ψ and ψ'."
  impl NEP.hasFDerivAt_pwImage

@[sa_forward "MorphismsPairwise.hasFDerivAtPwImage" 1]
theorem fwd1 (h : sa_impl% "MorphismsPairwise.hasFDerivAtPwImage") : S1 := by
  intro σ _ N q u hψ hψ'
  exact h N q hψ hψ'

@[sa_backward "MorphismsPairwise.hasFDerivAtPwImage"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsPairwise.hasFDerivAtPwImage" := by
  intro σ _ N q u hψ hψ'
  exact s1 N q u hψ hψ'

end Alignment.Shadows.MorphismsPairwise.HasFDerivAtPwImage

/-! ## `MorphismsPairwise.pwsEbField` -/
namespace Alignment.Shadows.MorphismsPairwise.PwsEbField
open Alignment.Shadows.MorphismsPairwise

sa_claim "MorphismsPairwise.pwsEbField" group "MorphismsPairwise" required
  text "**Per-reaction identity behind M6.** At a state with `ψ(θ) ≠ 0`, `ψ'(θ) ≠ 0` and `qξ ≠ 0`, the derivative of π^PW carries the EB field of each T_EB reaction `r` to the PGF-closure field of `r` at the image point."
  impl NEP.pws_ebField_of_mul

@[sa_forward "MorphismsPairwise.pwsEbField" 1]
theorem fwd1 (h : sa_impl% "MorphismsPairwise.pwsEbField") : S1 := by
  intro σ _ N q J X τ u h0 h1 hqξ
  exact h N q (Rxn.contact J X τ) u h0 h1 hqξ

@[sa_forward "MorphismsPairwise.pwsEbField" 2]
theorem fwd2 (h : sa_impl% "MorphismsPairwise.pwsEbField") : S2 := by
  intro σ _ N q Y ν u h0 h1 hqξ
  exact h N q (Rxn.exit Y ν) u h0 h1 hqξ

@[sa_forward "MorphismsPairwise.pwsEbField" 3]
theorem fwd3 (h : sa_impl% "MorphismsPairwise.pwsEbField") : S3 := by
  intro σ _ N q X Y a u h0 h1 hqξ
  exact h N q (Rxn.trans X Y a) u h0 h1 hqξ

/-- Case split on the reaction constructor (`Rxn` is plain data with no proof fields). -/
@[sa_backward "MorphismsPairwise.pwsEbField"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) : sa_impl% "MorphismsPairwise.pwsEbField" := by
  intro σ _ N q r u h0 h1 hqξ
  cases r with
  | contact J X τ => exact s1 N q J X τ u h0 h1 hqξ
  | exit Y ν => exact s2 N q Y ν u h0 h1 hqξ
  | trans X Y a => exact s3 N q X Y a u h0 h1 hqξ

end Alignment.Shadows.MorphismsPairwise.PwsEbField

/-! ## `MorphismsPairwise.pwsDomainPoisson` -/
namespace Alignment.Shadows.MorphismsPairwise.PwsDomainPoisson
open Alignment.Shadows.MorphismsPairwise

sa_claim "MorphismsPairwise.pwsDomainPoisson" group "MorphismsPairwise" required
  text "The domain of M6 on a Poisson(μ) network with `μ ≠ 0` is `{ξ ≠ 0}`: ψ > 0 and ψ' ≠ 0 everywhere."
  impl NEP.pwsDomain_poisson_of_ne

@[sa_forward "MorphismsPairwise.pwsDomainPoisson" 1]
theorem fwd1 (h : sa_impl% "MorphismsPairwise.pwsDomainPoisson") : S1 := by
  intro μ hμ σ
  exact (h μ hμ).1

@[sa_forward "MorphismsPairwise.pwsDomainPoisson" 2]
theorem fwd2 (h : sa_impl% "MorphismsPairwise.pwsDomainPoisson") : S2 := by
  intro μ hμ x
  exact (h μ hμ).2.1 x

@[sa_forward "MorphismsPairwise.pwsDomainPoisson" 3]
theorem fwd3 (h : sa_impl% "MorphismsPairwise.pwsDomainPoisson") : S3 := by
  intro μ hμ x
  exact (h μ hμ).2.2 x

@[sa_backward "MorphismsPairwise.pwsDomainPoisson"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) : sa_impl% "MorphismsPairwise.pwsDomainPoisson" :=
  fun μ hμ => ⟨fun {σ} => s1 μ hμ (σ := σ), s2 μ hμ, s3 μ hμ⟩

end Alignment.Shadows.MorphismsPairwise.PwsDomainPoisson
