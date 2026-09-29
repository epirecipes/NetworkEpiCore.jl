import Alignment.Registry
import Alignment.Shadows.SemanticsSolutions
import Alignment.Audit

/-!
# Checkers: group `SemanticsSolutions` (trusted module `NetworkEpi.Semantics.Solutions`)

Checker author (SA-PASS role 3, non-blind). For the twelve `implemented` claims of
`NetworkEpi/Semantics/Solutions.lean`, this file holds the `sa_claim` registration (verbatim
registry text, registry `impl` list), the forward checkers `sa_impl% → Sᵢ`, and the backward
checker `S₁ → … → Sₙ → sa_impl%`, or an `sa_fail_*` record.

## Bridges (need independent review in `Alignment.ReviewedBridges`)

* `ConservationLocal.bridge_isRemoval`, `ConservationLocalPoisson.bridge_isRemoval`: the trusted
  Boolean test `Rxn.isRemoval r = true` vs the text's "`r` is a removal `X → ∅`", i.e.
  `∃ X a, r = Rxn.trans X none a` ("removal-free" in the shadows is
  `∀ r ∈ rs, ∀ X a, r ≠ Rxn.trans X none a`). The statement is identical to the reviewed
  `SemanticsEB.RemovalFluxEqZero.bridge_isRemoval` (same hash). One bridge per claim, because a
  bridge may only be used by the claims it is registered for.

No other bridge is needed: `CNet.phiS N q θ ξ` unfolds definitionally to the shadows' primitive
`q * ξ * N.ψ' θ / N.ψ' 1`, and `ebSys N q rs` has `V = EB σ`, `F = lift N q rs` by definition.

## Checker pass after the registry retargeting (SA-PASS triage)

The registry now names, as `impl`, the trusted theorems stated in the text's form:
`ebField_contact_table`, `ebField_remove_table`, `ebField_progress_table` (each summand as a
`Pi.single` of the signed value), `ebSys_mem_dyn` (finite-dimensionality ∧ `C¹`: the object of
**Dyn**), `conservation_local_within`, `conservation_local_poisson_within` and
`seir_conservation_local_within` (`HasDerivWithinAt` on `Ioo (-ε) ε`; decimals `0.01`, `0.99`).
Against these, all seven claims have structural forward and backward checkers; the earlier
`sa_fail_*` records (which were about the previous `impl`s `ebField_*_eq`, `contDiff_lift`,
`conservation_local`, `conservation_local_poisson`, `seir_conservation_local`) are removed.
The registry flags the three `_table` theorems and the SEIR decimal form as WEAK (normal form
written after the shadows); the checkers here are exact matches with no algebra.

The field-table backward checkers rebuild the quadruple with `prod4_ext` (structure eta plus
`congrArg`), so every shadow is used. `conservationLocal`'s backward checker uses only `s2`
(the blind author's reading S2 implies S1; hint `backward_unused_shadows`, unscored).

`contDiffAtPiSingle` passes structurally, but its shadows mention no trusted constant (the text
is a pure Mathlib calculus fact), so the claim carries `shadow_trusted_free` until an independent
`sa_shadow_reviewed` record is written in `Alignment.ReviewedBridges`.
-/

open NEP

/-! ## Structural helpers (inlined by the audit; bridges are passed in as arguments) -/

namespace Alignment.Checks.SemanticsSolutions

/-- A quadruple is determined by its four projections: `e` is definitionally
`(e.1, e.2.1, e.2.2.1, e.2.2.2)` (structure eta), and each projection is rewritten in turn with
`congrArg`. -/
theorem prod4_ext {A B C D : Type} (e : A × B × C × D) {a : A} {b : B} {c : C} {d : D}
    (h1 : e.1 = a) (h2 : e.2.1 = b) (h3 : e.2.2.1 = c) (h4 : e.2.2.2 = d) :
    e = (a, b, c, d) :=
  Eq.trans (congrArg (fun x : A => ((x, e.2.1, e.2.2.1, e.2.2.2) : A × B × C × D)) h1)
    (Eq.trans (congrArg (fun y : B => ((a, y, e.2.2.1, e.2.2.2) : A × B × C × D)) h2)
      (Eq.trans (congrArg (fun z : C => ((a, b, z, e.2.2.2) : A × B × C × D)) h3)
        (congrArg (fun w : D => ((a, b, c, w) : A × B × C × D)) h4)))

/-- `false = true` is absurd, by kernel reduction of a `Bool` eliminator into `Prop`. -/
theorem boolFalseNeTrue (h : false = true) : False :=
  Eq.mp (congrArg (fun b : Bool => Bool.rec (motive := fun _ => Prop) True False b) h) trivial

/-- A reaction that is not of the form `trans X none a` has `isRemoval = false`, given the
Boolean characterisation `hb` (a bridge). -/
theorem isRemoval_false_of {σ : Type}
    (hb : ∀ r : Rxn σ, r.isRemoval = true ↔ ∃ (X : σ) (a : ℝ), r = Rxn.trans X none a)
    (r : Rxn σ) (hn : ∀ (X : σ) (a : ℝ), r ≠ Rxn.trans X none a) : r.isRemoval = false :=
  match hr : r.isRemoval with
  | false => rfl
  | true => False.elim (Exists.elim ((hb r).mp hr) fun X h' => Exists.elim h' fun a he => hn X a he)

/-- Conversely, `isRemoval = false` excludes the form `trans X none a`. -/
theorem notRemoval_of_isRemoval_false {σ : Type}
    (hb : ∀ r : Rxn σ, r.isRemoval = true ↔ ∃ (X : σ) (a : ℝ), r = Rxn.trans X none a)
    (r : Rxn σ) (hf : r.isRemoval = false) : ∀ (X : σ) (a : ℝ), r ≠ Rxn.trans X none a :=
  fun X a he => boolFalseNeTrue (hf.symm.trans ((hb r).mpr ⟨X, a, he⟩))

/-- Proof of the `isRemoval` bridge statements (bridges may use any tactic; this does not depend
on any implementation theorem). -/
theorem isRemoval_iff_aux {σ : Type} (r : Rxn σ) :
    r.isRemoval = true ↔ ∃ (X : σ) (a : ℝ), r = Rxn.trans X none a := by
  cases r with
  | contact J X τ => simp [Rxn.isRemoval]
  | exit Y ν => simp [Rxn.isRemoval]
  | trans X Y a => cases Y <;> simp [Rxn.isRemoval]

end Alignment.Checks.SemanticsSolutions

/-! ## `SemanticsSolutions.contDiffAtPiSingle` -/

namespace Alignment.Shadows.SemanticsSolutions.ContDiffAtPiSingle

sa_claim "SemanticsSolutions.contDiffAtPiSingle" group "SemanticsSolutions" required
  text "`Pi.single Y` applied to a `C^n` function is `C^n` (a `fun_prop` rule)."
  impl NEP.contDiffAt_pi_single

@[sa_forward "SemanticsSolutions.contDiffAtPiSingle" 1]
theorem fwd1 (h : sa_impl% "SemanticsSolutions.contDiffAtPiSingle") : S1 := by
  intro σ _ _ Y E _ _ f x n hf
  exact h Y hf

@[sa_forward "SemanticsSolutions.contDiffAtPiSingle" 2]
theorem fwd2 (h : sa_impl% "SemanticsSolutions.contDiffAtPiSingle") : S2 := by
  intro σ _ _ Y E _ _ f x hf
  exact h Y hf

/-- Case split on the level `n : WithTop ℕ∞` (`WithTop.recTopCoe`, a data recursor). -/
@[sa_backward "SemanticsSolutions.contDiffAtPiSingle"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "SemanticsSolutions.contDiffAtPiSingle" := by
  intro σ _ _ E _ _ n Y g u hg
  induction n using WithTop.recTopCoe with
  | top => exact s2 Y g u hg
  | coe m => exact s1 Y g u m hg

end Alignment.Shadows.SemanticsSolutions.ContDiffAtPiSingle

/-! ## `SemanticsSolutions.ebFieldContactEq` -/

namespace Alignment.Shadows.SemanticsSolutions.EbFieldContactEq

open Alignment.Checks.SemanticsSolutions

sa_claim "SemanticsSolutions.ebFieldContactEq" group "SemanticsSolutions" required
  text "The EB field of a contact `s + J → X + J`, written with the coordinate projections."
  impl NEP.ebField_contact_table

@[sa_forward "SemanticsSolutions.ebFieldContactEq" 1]
theorem fwd1 (h : sa_impl% "SemanticsSolutions.ebFieldContactEq") : S1 := by
  intro σ _ N q J X τ u
  exact congrArg (fun F : EB σ → EB σ => (F u).1) (h N q J X τ)

@[sa_forward "SemanticsSolutions.ebFieldContactEq" 2]
theorem fwd2 (h : sa_impl% "SemanticsSolutions.ebFieldContactEq") : S2 := by
  intro σ _ N q J X τ u
  exact congrArg (fun F : EB σ → EB σ => (F u).2.1) (h N q J X τ)

@[sa_forward "SemanticsSolutions.ebFieldContactEq" 3]
theorem fwd3 (h : sa_impl% "SemanticsSolutions.ebFieldContactEq") : S3 := by
  intro σ _ N q J X τ u
  exact congrArg (fun F : EB σ → EB σ => (F u).2.2.1) (h N q J X τ)

@[sa_forward "SemanticsSolutions.ebFieldContactEq" 4]
theorem fwd4 (h : sa_impl% "SemanticsSolutions.ebFieldContactEq") : S4 := by
  intro σ _ N q J X τ u
  exact congrArg (fun F : EB σ → EB σ => (F u).2.2.2) (h N q J X τ)

@[sa_backward "SemanticsSolutions.ebFieldContactEq"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) :
    sa_impl% "SemanticsSolutions.ebFieldContactEq" := by
  intro σ _ N q J X τ
  funext u
  exact prod4_ext _ (s1 N q J X τ u) (s2 N q J X τ u) (s3 N q J X τ u) (s4 N q J X τ u)

end Alignment.Shadows.SemanticsSolutions.EbFieldContactEq

/-! ## `SemanticsSolutions.ebFieldExitEq` -/

namespace Alignment.Shadows.SemanticsSolutions.EbFieldExitEq

sa_claim "SemanticsSolutions.ebFieldExitEq" group "SemanticsSolutions" required
  text "The EB field of an exit `s → Y`, written with the coordinate projections."
  impl NEP.ebField_exit_eq

@[sa_forward "SemanticsSolutions.ebFieldExitEq" 1]
theorem fwd1 (h : sa_impl% "SemanticsSolutions.ebFieldExitEq") : S1 := by
  intro σ _ N q Y ν u
  exact congrArg (fun F : EB σ → EB σ => (F u).1) (h N q Y ν)

@[sa_forward "SemanticsSolutions.ebFieldExitEq" 2]
theorem fwd2 (h : sa_impl% "SemanticsSolutions.ebFieldExitEq") : S2 := by
  intro σ _ N q Y ν u
  exact congrArg (fun F : EB σ → EB σ => (F u).2.1) (h N q Y ν)

@[sa_forward "SemanticsSolutions.ebFieldExitEq" 3]
theorem fwd3 (h : sa_impl% "SemanticsSolutions.ebFieldExitEq") : S3 := by
  intro σ _ N q Y ν u
  exact congrArg (fun F : EB σ → EB σ => (F u).2.2.1) (h N q Y ν)

@[sa_forward "SemanticsSolutions.ebFieldExitEq" 4]
theorem fwd4 (h : sa_impl% "SemanticsSolutions.ebFieldExitEq") : S4 := by
  intro σ _ N q Y ν u
  exact congrArg (fun F : EB σ → EB σ => (F u).2.2.2) (h N q Y ν)

/-- `funext`, then both sides are eta-expanded 4-tuples (structure eta is definitional). -/
@[sa_backward "SemanticsSolutions.ebFieldExitEq"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) :
    sa_impl% "SemanticsSolutions.ebFieldExitEq" := by
  intro σ _ N q Y ν
  funext u
  show ((ebField N q (Rxn.exit Y ν) u).1, (ebField N q (Rxn.exit Y ν) u).2.1,
      (ebField N q (Rxn.exit Y ν) u).2.2.1, (ebField N q (Rxn.exit Y ν) u).2.2.2) =
    ((0 : ℝ), -(ν * u.2.1), Pi.single Y (ν * (q * u.2.1 * N.ψ' u.1 / N.ψ' 1)),
      Pi.single Y (ν * (q * u.2.1 * N.ψ u.1)))
  exact congr (congrArg Prod.mk (s1 N q Y ν u))
    (congr (congrArg Prod.mk (s2 N q Y ν u))
      (congr (congrArg Prod.mk (s3 N q Y ν u)) (s4 N q Y ν u)))

end Alignment.Shadows.SemanticsSolutions.EbFieldExitEq

/-! ## `SemanticsSolutions.ebFieldRemoveEq` -/

namespace Alignment.Shadows.SemanticsSolutions.EbFieldRemoveEq

open Alignment.Checks.SemanticsSolutions

sa_claim "SemanticsSolutions.ebFieldRemoveEq" group "SemanticsSolutions" required
  text "The EB field of a removal `X → ∅`, written with the coordinate projections."
  impl NEP.ebField_remove_table

@[sa_forward "SemanticsSolutions.ebFieldRemoveEq" 1]
theorem fwd1 (h : sa_impl% "SemanticsSolutions.ebFieldRemoveEq") : S1 := by
  intro σ _ N q X a u
  exact congrArg (fun F : EB σ → EB σ => (F u).1) (h N q X a)

@[sa_forward "SemanticsSolutions.ebFieldRemoveEq" 2]
theorem fwd2 (h : sa_impl% "SemanticsSolutions.ebFieldRemoveEq") : S2 := by
  intro σ _ N q X a u
  exact congrArg (fun F : EB σ → EB σ => (F u).2.1) (h N q X a)

@[sa_forward "SemanticsSolutions.ebFieldRemoveEq" 3]
theorem fwd3 (h : sa_impl% "SemanticsSolutions.ebFieldRemoveEq") : S3 := by
  intro σ _ N q X a u
  exact congrArg (fun F : EB σ → EB σ => (F u).2.2.1) (h N q X a)

@[sa_forward "SemanticsSolutions.ebFieldRemoveEq" 4]
theorem fwd4 (h : sa_impl% "SemanticsSolutions.ebFieldRemoveEq") : S4 := by
  intro σ _ N q X a u
  exact congrArg (fun F : EB σ → EB σ => (F u).2.2.2) (h N q X a)

@[sa_backward "SemanticsSolutions.ebFieldRemoveEq"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) :
    sa_impl% "SemanticsSolutions.ebFieldRemoveEq" := by
  intro σ _ N q X a
  funext u
  exact prod4_ext _ (s1 N q X a u) (s2 N q X a u) (s3 N q X a u) (s4 N q X a u)

end Alignment.Shadows.SemanticsSolutions.EbFieldRemoveEq

/-! ## `SemanticsSolutions.ebFieldProgressEq` -/

namespace Alignment.Shadows.SemanticsSolutions.EbFieldProgressEq

open Alignment.Checks.SemanticsSolutions

sa_claim "SemanticsSolutions.ebFieldProgressEq" group "SemanticsSolutions" required
  text "The EB field of a progression `X → Y`, written with the coordinate projections."
  impl NEP.ebField_progress_table

@[sa_forward "SemanticsSolutions.ebFieldProgressEq" 1]
theorem fwd1 (h : sa_impl% "SemanticsSolutions.ebFieldProgressEq") : S1 := by
  intro σ _ N q X Y a u
  exact congrArg (fun F : EB σ → EB σ => (F u).1) (h N q X Y a)

@[sa_forward "SemanticsSolutions.ebFieldProgressEq" 2]
theorem fwd2 (h : sa_impl% "SemanticsSolutions.ebFieldProgressEq") : S2 := by
  intro σ _ N q X Y a u
  exact congrArg (fun F : EB σ → EB σ => (F u).2.1) (h N q X Y a)

@[sa_forward "SemanticsSolutions.ebFieldProgressEq" 3]
theorem fwd3 (h : sa_impl% "SemanticsSolutions.ebFieldProgressEq") : S3 := by
  intro σ _ N q X Y a u
  exact congrArg (fun F : EB σ → EB σ => (F u).2.2.1) (h N q X Y a)

@[sa_forward "SemanticsSolutions.ebFieldProgressEq" 4]
theorem fwd4 (h : sa_impl% "SemanticsSolutions.ebFieldProgressEq") : S4 := by
  intro σ _ N q X Y a u
  exact congrArg (fun F : EB σ → EB σ => (F u).2.2.2) (h N q X Y a)

@[sa_backward "SemanticsSolutions.ebFieldProgressEq"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) :
    sa_impl% "SemanticsSolutions.ebFieldProgressEq" := by
  intro σ _ N q X Y a
  funext u
  exact prod4_ext _ (s1 N q X Y a u) (s2 N q X Y a u) (s3 N q X Y a u) (s4 N q X Y a u)

end Alignment.Shadows.SemanticsSolutions.EbFieldProgressEq

/-! ## `SemanticsSolutions.contDiffAtEbField` -/

namespace Alignment.Shadows.SemanticsSolutions.ContDiffAtEbField

sa_claim "SemanticsSolutions.contDiffAtEbField" group "SemanticsSolutions" required
  text "The EB field of one reaction is `C^n` at every state `u` such that ψ, ψ' and ψ'' are `C^n` at `θ = u.1`."
  impl NEP.contDiffAt_ebField

@[sa_forward "SemanticsSolutions.contDiffAtEbField" 1]
theorem fwd1 (h : sa_impl% "SemanticsSolutions.contDiffAtEbField") : S1 := by
  intro σ _ _ N q J X τ n u h1 h2 h3
  exact h N q (Rxn.contact J X τ) h1 h2 h3

@[sa_forward "SemanticsSolutions.contDiffAtEbField" 2]
theorem fwd2 (h : sa_impl% "SemanticsSolutions.contDiffAtEbField") : S2 := by
  intro σ _ _ N q Y ν n u h1 h2 h3
  exact h N q (Rxn.exit Y ν) h1 h2 h3

@[sa_forward "SemanticsSolutions.contDiffAtEbField" 3]
theorem fwd3 (h : sa_impl% "SemanticsSolutions.contDiffAtEbField") : S3 := by
  intro σ _ _ N q X Y a n u h1 h2 h3
  exact h N q (Rxn.trans X Y a) h1 h2 h3

@[sa_forward "SemanticsSolutions.contDiffAtEbField" 4]
theorem fwd4 (h : sa_impl% "SemanticsSolutions.contDiffAtEbField") : S4 := by
  intro σ _ _ N q J X τ u h1 h2 h3
  exact h N q (Rxn.contact J X τ) h1 h2 h3

@[sa_forward "SemanticsSolutions.contDiffAtEbField" 5]
theorem fwd5 (h : sa_impl% "SemanticsSolutions.contDiffAtEbField") : S5 := by
  intro σ _ _ N q Y ν u h1 h2 h3
  exact h N q (Rxn.exit Y ν) h1 h2 h3

@[sa_forward "SemanticsSolutions.contDiffAtEbField" 6]
theorem fwd6 (h : sa_impl% "SemanticsSolutions.contDiffAtEbField") : S6 := by
  intro σ _ _ N q X Y a u h1 h2 h3
  exact h N q (Rxn.trans X Y a) h1 h2 h3

/-- Case split on the level (`WithTop.recTopCoe`) and on the reaction (`Rxn` recursor). -/
@[sa_backward "SemanticsSolutions.contDiffAtEbField"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) :
    sa_impl% "SemanticsSolutions.contDiffAtEbField" := by
  intro σ _ _ N q r u n h1 h2 h3
  induction n using WithTop.recTopCoe with
  | top =>
    cases r with
    | contact J X τ => exact s4 N q J X τ u h1 h2 h3
    | exit Y ν => exact s5 N q Y ν u h1 h2 h3
    | trans X Y a => exact s6 N q X Y a u h1 h2 h3
  | coe m =>
    cases r with
    | contact J X τ => exact s1 N q J X τ m u h1 h2 h3
    | exit Y ν => exact s2 N q Y ν m u h1 h2 h3
    | trans X Y a => exact s3 N q X Y a m u h1 h2 h3

end Alignment.Shadows.SemanticsSolutions.ContDiffAtEbField

/-! ## `SemanticsSolutions.contDiffAtLift` -/

namespace Alignment.Shadows.SemanticsSolutions.ContDiffAtLift

sa_claim "SemanticsSolutions.contDiffAtLift" group "SemanticsSolutions" required
  text "**The EB field of a reaction list is `C^n` where the degree data are.** For every T_EB reaction list `rs`, the EB field `lift N q rs` is `C^n` at every state `u` such that ψ, ψ' and ψ'' are `C^n` at `θ = u.1`."
  impl NEP.contDiffAt_lift

@[sa_forward "SemanticsSolutions.contDiffAtLift" 1]
theorem fwd1 (h : sa_impl% "SemanticsSolutions.contDiffAtLift") : S1 := by
  intro σ _ _ N q rs n u h1 h2 h3
  exact h N q rs h1 h2 h3

@[sa_forward "SemanticsSolutions.contDiffAtLift" 2]
theorem fwd2 (h : sa_impl% "SemanticsSolutions.contDiffAtLift") : S2 := by
  intro σ _ _ N q rs u h1 h2 h3
  exact h N q rs h1 h2 h3

@[sa_backward "SemanticsSolutions.contDiffAtLift"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "SemanticsSolutions.contDiffAtLift" := by
  intro σ _ _ N q rs u n h1 h2 h3
  induction n using WithTop.recTopCoe with
  | top => exact s2 N q rs u h1 h2 h3
  | coe m => exact s1 N q rs m u h1 h2 h3

end Alignment.Shadows.SemanticsSolutions.ContDiffAtLift

/-! ## `SemanticsSolutions.contDiffLift` -/

namespace Alignment.Shadows.SemanticsSolutions.ContDiffLift

sa_claim "SemanticsSolutions.contDiffLift" group "SemanticsSolutions" required
  text "**EB models on a network with C¹ degree data are objects of Dyn.** Design statement (DESIGN_NetworkEpiCore.md §D.3): \"Objects of **Dyn** are (V, F): V a finite-dimensional real normed space, F: V → V a C¹ vector field.\"; §D.4, the row of the representation functor **EB_N** with domain \"Open(Petri/T_EB), N fixed\"."
  impl NEP.ebSys_mem_dyn

@[sa_forward "SemanticsSolutions.contDiffLift" 1]
theorem fwd1 (h : sa_impl% "SemanticsSolutions.contDiffLift") : S1 := by
  intro σ _ _ N q rs h1 h2 h3
  exact (h N q rs h1 h2 h3).1

@[sa_forward "SemanticsSolutions.contDiffLift" 2]
theorem fwd2 (h : sa_impl% "SemanticsSolutions.contDiffLift") : S2 := by
  intro σ _ _ N q rs h1 h2 h3
  exact (h N q rs h1 h2 h3).2

@[sa_backward "SemanticsSolutions.contDiffLift"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "SemanticsSolutions.contDiffLift" := by
  intro σ _ _ N q rs h1 h2 h3
  exact ⟨s1 N q rs h1 h2 h3, s2 N q rs h1 h2 h3⟩

end Alignment.Shadows.SemanticsSolutions.ContDiffLift

/-! ## `SemanticsSolutions.existsLocalSolution` -/

namespace Alignment.Shadows.SemanticsSolutions.ExistsLocalSolution

sa_claim "SemanticsSolutions.existsLocalSolution" group "SemanticsSolutions" required
  text "**Local existence of EB solutions (Picard–Lindelöf).** For every T_EB reaction list `rs` and every state `u₀` such that ψ, ψ' and ψ'' are `C¹` at `θ = u₀.1`, there are `ε > 0` and a curve `x` with `x 0 = u₀` that solves the EB field of `rs` (`HasDerivAt`) at every `t ∈ (−ε, ε)`."
  impl NEP.exists_local_solution

/-- S1 is the implementation's statement (up to the order of the instance binders). -/
@[sa_forward "SemanticsSolutions.existsLocalSolution" 1]
theorem fwd1 (h : sa_impl% "SemanticsSolutions.existsLocalSolution") : S1 := by
  intro σ _ _ N q rs u₀ h1 h2 h3
  exact h N q rs u₀ h1 h2 h3

@[sa_backward "SemanticsSolutions.existsLocalSolution"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsSolutions.existsLocalSolution" := by
  intro σ _ _ N q rs u₀ h1 h2 h3
  exact s1 N q rs u₀ h1 h2 h3

end Alignment.Shadows.SemanticsSolutions.ExistsLocalSolution

/-! ## `SemanticsSolutions.conservationLocal` -/

namespace Alignment.Shadows.SemanticsSolutions.ConservationLocal

open Alignment.Checks.SemanticsSolutions

sa_claim "SemanticsSolutions.conservationLocal" group "SemanticsSolutions" required
  text "**Edge conservation along a local EB solution from the design's initial condition.** Design statement (DESIGN_NetworkEpiCore.md §D.4, Evidence): \"The exit terms were checked by hand. Conservation θ = φ_S + Σφ_X holds.\""
  impl NEP.conservation_local_within

/-- Bridge (needs independent review): the trusted Boolean test `Rxn.isRemoval r = true` vs the
text's "`r` is a removal `X → ∅`", i.e. `r = trans X none a` for some `X`, `a`. Same statement
(and hash) as the reviewed `SemanticsEB.RemovalFluxEqZero.bridge_isRemoval`. -/
@[sa_bridge "SemanticsSolutions.conservationLocal"]
theorem bridge_isRemoval {σ : Type} (r : Rxn σ) :
    r.isRemoval = true ↔ ∃ (X : σ) (a : ℝ), r = Rxn.trans X none a :=
  isRemoval_iff_aux r

/-- `CNet.phiS N q θ ξ` unfolds definitionally to the shadow's `q * ξ * N.ψ' θ / N.ψ' 1`. -/
@[sa_forward "SemanticsSolutions.conservationLocal" 1]
theorem fwd1 (h : sa_impl% "SemanticsSolutions.conservationLocal") : S1 := by
  intro σ _ _ N q rs ρ h1 h2 h3 h4 h5 h6 h7
  exact h N q h5 h1 h2 h3 h4 rs (fun r hr => isRemoval_false_of bridge_isRemoval r (h6 r hr))
    ρ ρ h7

@[sa_forward "SemanticsSolutions.conservationLocal" 2]
theorem fwd2 (h : sa_impl% "SemanticsSolutions.conservationLocal") : S2 := by
  intro σ _ _ N q rs φ₀ p₀ h1 h2 h3 h4 h5 h6 h7
  exact h N q h5 h1 h2 h3 h4 rs (fun r hr => isRemoval_false_of bridge_isRemoval r (h6 r hr))
    φ₀ p₀ h7

/-- Uses only `s2` (S2 implies S1; the blind author's certificate is `complete _ s2`). -/
@[sa_backward "SemanticsSolutions.conservationLocal"]
theorem bwd (_s1 : S1) (s2 : S2) : sa_impl% "SemanticsSolutions.conservationLocal" := by
  intro σ _ _ N q hm hψ hψ' hψ'' hd rs hrs φ₀ p₀ hφ₀
  exact s2 N q rs φ₀ p₀ hψ hψ' hψ'' hd hm
    (fun r hr => notRemoval_of_isRemoval_false bridge_isRemoval r (hrs r hr)) hφ₀

end Alignment.Shadows.SemanticsSolutions.ConservationLocal

/-! ## `SemanticsSolutions.conservationLocalPoisson` -/

namespace Alignment.Shadows.SemanticsSolutions.ConservationLocalPoisson

open Alignment.Checks.SemanticsSolutions

sa_claim "SemanticsSolutions.conservationLocalPoisson" group "SemanticsSolutions" required
  text "Edge conservation along a local solution on a Poisson(μ) network, `μ ≠ 0` (`conservation_local` for `CNet.poisson μ`): for every removal-free T_EB reaction list `rs` and initial data `φ₀, p₀` with `Σ_X φ₀(X) = 1 − q`, there are `ε > 0` and a solution on `(−ε, ε)` from `(1, 1, φ₀, p₀)` along which `θ = φ_S + Σ_X φ_X`."
  impl NEP.conservation_local_poisson_within

/-- Bridge (needs independent review): as `ConservationLocal.bridge_isRemoval` ("removal-free"
is "no reaction of the form `X → ∅`"). -/
@[sa_bridge "SemanticsSolutions.conservationLocalPoisson"]
theorem bridge_isRemoval {σ : Type} (r : Rxn σ) :
    r.isRemoval = true ↔ ∃ (X : σ) (a : ℝ), r = Rxn.trans X none a :=
  isRemoval_iff_aux r

@[sa_forward "SemanticsSolutions.conservationLocalPoisson" 1]
theorem fwd1 (h : sa_impl% "SemanticsSolutions.conservationLocalPoisson") : S1 := by
  intro σ _ _ μ q rs φ₀ p₀ hμ hn hφ₀
  exact h μ hμ q rs (fun r hr => isRemoval_false_of bridge_isRemoval r (hn r hr)) φ₀ p₀ hφ₀

@[sa_backward "SemanticsSolutions.conservationLocalPoisson"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsSolutions.conservationLocalPoisson" := by
  intro σ _ _ μ hμ q rs hrs φ₀ p₀ hφ₀
  exact s1 μ q rs φ₀ p₀ hμ
    (fun r hr => notRemoval_of_isRemoval_false bridge_isRemoval r (hrs r hr)) hφ₀

end Alignment.Shadows.SemanticsSolutions.ConservationLocalPoisson

/-! ## `SemanticsSolutions.seirConservationLocal` -/

namespace Alignment.Shadows.SemanticsSolutions.SeirConservationLocal

sa_claim "SemanticsSolutions.seirConservationLocal" group "SemanticsSolutions" required
  text "**Conservation is not vacuous for EB SEIR on Poisson(5).** With τ = 1/6, σ = 1/3, γ = 1/4, seed φ_I(0) = pop_I(0) = 0.01 and q = 0.99 (so `Σ_X φ_X(0) = 1 − q`), there is a solution on some interval `(−ε, ε)` from `(θ, ξ, φ, pop)(0) = (1, 1, φ₀, p₀)` along which `θ = φ_S + Σ_X φ_X`."
  impl NEP.seir_conservation_local_within

/-- The statements agree up to unfolding `CNet.phiS` (definitional). -/
@[sa_forward "SemanticsSolutions.seirConservationLocal" 1]
theorem fwd1 (h : sa_impl% "SemanticsSolutions.seirConservationLocal") : S1 := h

@[sa_backward "SemanticsSolutions.seirConservationLocal"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsSolutions.seirConservationLocal" := s1

end Alignment.Shadows.SemanticsSolutions.SeirConservationLocal
