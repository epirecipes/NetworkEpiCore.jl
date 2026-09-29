import Alignment.Registry
import Alignment.Example.ExampleChecks
import NetworkEpi.Syntax.Rxn
import NetworkEpi.Semantics.EB
import NetworkEpi.Semantics.MA
import NetworkEpi.Semantics.PoissonSIR
import Mathlib.Tactic.Ring

/-!
# SA-PASS self-test mocks

Every claim here (ids `SELFTEST.*`, group `SelfTest`) is deliberately misaligned or
mis-registered in exactly one way. `bash scripts/sa_pass.sh --self-test` checks that the audit
reports exactly the statuses listed in `Alignment/Example/selftest_expected.yaml`, and that the
worked example (`EXAMPLE.*`) passes. Normal reports exclude these ids.

When the audit changes, add every newly found bypass here as a mock (red-team, then port).
The implementation theorems used are real trusted theorems of `NetworkEpi`; only the
registrations are mocks. Shadows that are not about a content-free statement mention a trusted
constant (for example `∀ N : CNet, N.ψ = N.ψ`), so that the only defect of each mock is the one
it tests.

**Port from `EdgeBasedModels.jl/proofs/Alignment/Example/SelfTest.lean`.** Every mock of the EBM
self-test is ported with NetworkEpi constants except `SELFTEST.refutedHypothesis`. That mock
needs a trusted theorem with an unsatisfiable hypothesis, and a sound refuter fires only on an
unsatisfiable hypothesis. NetworkEpi has no such theorem, by design. The refuter-validity mocks
(`AlignmentRefuter.*`) are kept. `SELFTEST.witnessMissing` has valid refuters with the same head
(`NRxn.EBAdmissible`) in scope, so its expected empty flag set is the no-false-positive control.
The EBM self-test covers the positive detection with the same `Audit.lean` code. The EBM mock
`trajectoryGapZero` was universe-polymorphic; NetworkEpi has no universe-polymorphic theorem, so
the witness mocks here are monomorphic.
-/

set_option linter.unusedVariables false

open NEP

namespace Alignment.Example.SelfTest

set_option hygiene false in
/-- `selftest_shadows1 "id" Ns : P` declares in namespace `Ns` a reference `T := P`, a single
shadow `S1 := P` and the two completeness certificates. -/
macro "selftest_shadows1 " id:str ns:ident " : " p:term : command => `(
  namespace $ns
  @[sa_reference $id] def T : Prop := $p
  @[sa_shadow $id 1] def S1 : Prop := $p
  @[sa_ref_forward $id 1] theorem ref_fwd1 : T → S1 := fun t => t
  @[sa_complete $id] theorem complete (s1 : S1) : T := s1
  end $ns)

/-! ## Vacuity mocks (expected: forward `vacuous`) -/

selftest_shadows1 "SELFTEST.vacuousIgnore" VacuousIgnore :
  ∀ (N : CNet) (q θ ξ : ℝ), N.susc q θ ξ = q * ξ * N.ψ θ

namespace VacuousIgnore
sa_claim "SELFTEST.vacuousIgnore" group "SelfTest" required
  text "mock: the forward checker ignores the hypothesis" impl NEP.lift_append
@[sa_forward "SELFTEST.vacuousIgnore" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.vacuousIgnore") : S1 := fun _ _ _ _ => rfl
end VacuousIgnore

selftest_shadows1 "SELFTEST.vacuousBeta" VacuousBeta :
  ∀ (N : CNet) (q θ ξ : ℝ), N.susc q θ ξ = q * ξ * N.ψ θ

namespace VacuousBeta
sa_claim "SELFTEST.vacuousBeta" group "SelfTest" required
  text "mock: eta/beta dodge (fun _ => p) h" impl NEP.lift_append
@[sa_forward "SELFTEST.vacuousBeta" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.vacuousBeta") : S1 :=
  (fun (_ : sa_impl% "SELFTEST.vacuousBeta") => (fun _ _ _ _ => rfl : S1)) h
end VacuousBeta

selftest_shadows1 "SELFTEST.vacuousAndLeft" VacuousAndLeft :
  ∀ (N : CNet) (q θ ξ : ℝ), N.susc q θ ξ = q * ξ * N.ψ θ

namespace VacuousAndLeft
sa_claim "SELFTEST.vacuousAndLeft" group "SelfTest" required
  text "mock: And.left ⟨p, h⟩ dodge" impl NEP.lift_append
@[sa_forward "SELFTEST.vacuousAndLeft" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.vacuousAndLeft") : S1 :=
  And.left (⟨fun _ _ _ _ => rfl, h⟩ : S1 ∧ sa_impl% "SELFTEST.vacuousAndLeft")
end VacuousAndLeft

selftest_shadows1 "SELFTEST.vacuousAuxLemma" VacuousAuxLemma :
  ∀ (N : CNet) (q θ ξ : ℝ), N.susc q θ ξ = q * ξ * N.ψ θ

namespace VacuousAuxLemma
sa_claim "SELFTEST.vacuousAuxLemma" group "SelfTest" required
  text "mock: auxiliary lemma dodge" impl NEP.lift_append
theorem aux (h : sa_impl% "SELFTEST.vacuousAuxLemma") : S1 := fun _ _ _ _ => rfl
@[sa_forward "SELFTEST.vacuousAuxLemma" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.vacuousAuxLemma") : S1 := aux h
end VacuousAuxLemma

selftest_shadows1 "SELFTEST.vacuousEval" VacuousEval :
  ∀ (N : CNet) (q θ ξ : ℝ), N.susc q θ ξ = q * ξ * N.ψ θ

namespace VacuousEval
sa_claim "SELFTEST.vacuousEval" group "SelfTest" required
  text "mock: hypothesis passed to a library function that discards it"
  impl NEP.lift_append
/-- `h` survives normalisation (Function.eval is not unfolded) and only the replacement of the
hypothesis type by an arbitrary proposition exposes the dodge. -/
@[sa_forward "SELFTEST.vacuousEval" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.vacuousEval") : S1 :=
  Function.eval (@h) (fun _ => (fun _ _ _ _ => rfl : S1))
end VacuousEval

selftest_shadows1 "SELFTEST.vacuousConst" VacuousConst :
  ∀ (N : CNet) (q θ ξ : ℝ), N.susc q θ ξ = q * ξ * N.ψ θ

namespace VacuousConst
sa_claim "SELFTEST.vacuousConst" group "SelfTest" required
  text "mock: Function.const / id wrappers around a hypothesis-free proof"
  impl NEP.lift_append
@[sa_forward "SELFTEST.vacuousConst" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.vacuousConst") : S1 :=
  (id (Function.const (sa_impl% "SELFTEST.vacuousConst") (fun _ _ _ _ => rfl : S1))) h
end VacuousConst

selftest_shadows1 "SELFTEST.vacuousMatch" VacuousMatch : ∀ N : CNet, N.ψ = N.ψ

namespace VacuousMatch
sa_claim "SELFTEST.vacuousMatch" group "SelfTest" required
  text "mock: the hypothesis is destructured but its components are ignored"
  impl NEP.NRxn.not_ebAdmissible_resus NEP.NRxn.not_ebAdmissible_nodeContact
@[sa_forward "SELFTEST.vacuousMatch" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.vacuousMatch") : S1 := by
  obtain ⟨_h1, _h2⟩ := h
  exact fun _ => rfl
end VacuousMatch

selftest_shadows1 "SELFTEST.vacuousExistsElim" VacuousExistsElim : ∀ N : CNet, N.ψ = N.ψ

namespace VacuousExistsElim
sa_claim "SELFTEST.vacuousExistsElim" group "SelfTest" required
  text "mock: Exists.elim on the hypothesis with a continuation ignoring the witness"
  impl NEP.NRxn.exists_not_ebAdmissible
@[sa_forward "SELFTEST.vacuousExistsElim" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.vacuousExistsElim") : S1 :=
  Exists.elim h (fun _ _ => fun _ => rfl)
end VacuousExistsElim

selftest_shadows1 "SELFTEST.vacuousDataArg" VacuousDataArg : ∀ N : CNet, N.ψ = N.ψ

namespace VacuousDataArg
sa_claim "SELFTEST.vacuousDataArg" group "SelfTest" required
  text "mock: the hypothesis only feeds a proof argument of a data term"
  impl NEP.rempala
@[sa_forward "SELFTEST.vacuousDataArg" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.vacuousDataArg") : S1 := fun N =>
  @Function.eval (Semiconj (ebPoisSIR 1 1 1 1) (maSIR (1 * 1) (1 + 1))) (fun _ => N.ψ = N.ψ)
    (Semiconj.ofIsSemiconj _ (h 1 1 1 1)) (fun _ => rfl)
end VacuousDataArg

selftest_shadows1 "SELFTEST.vacuousNestedObtain" VacuousNestedObtain :
  ∀ μ q : ℝ, μ ≠ 0 → 0 < q → ∀ N : CNet, N.ψ = N.ψ

/-! `vacuousNestedObtain` guards the memo table of the vacuity guard's normaliser (added when the
table was introduced for `MorphismsCompact.compactSolutionPoisson`, whose checker exhausted the
unmemoised budget). The hypothesis is a nested conjunction with an existential inside; the checker
destructures all of it and ignores every part, so the guard must still report `vacuous`. -/
namespace VacuousNestedObtain
sa_claim "SELFTEST.vacuousNestedObtain" group "SelfTest" required
  text "mock: deep destructuring of a large hypothesis whose parts are all ignored"
  impl NEP.ebField_removal_row NEP.rempala_quotient_sir
@[sa_forward "SELFTEST.vacuousNestedObtain" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.vacuousNestedObtain") : S1 := by
  intro μ q hμ hq N
  obtain ⟨h1, h2⟩ := h
  obtain ⟨_a, _b, _c⟩ := h1 (σ := Unit) N q () q (q, q, fun _ => q, fun _ => q)
  obtain ⟨_d, e⟩ := h2 μ q hμ
  obtain ⟨_u, _hu⟩ := e hq q q hq
  exact rfl
end VacuousNestedObtain

/-! ## Structural-rule mocks (expected: `audit_violation`) -/

selftest_shadows1 "SELFTEST.automationSimp" AutomationSimp :
  ∀ (N : CNet) (q : ℝ) (rs : List (Rxn Unit)) (u : EB Unit),
    edgeDefectDeriv N q u (lift N q rs u) + 0 = removalFlux rs u.2.2.1

namespace AutomationSimp
sa_claim "SELFTEST.automationSimp" group "SelfTest" required
  text "mock: simp in a checker" impl NEP.edgeDefectDeriv_lift
@[sa_forward "SELFTEST.automationSimp" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.automationSimp") : S1 := by
  intro N q rs u
  simp [h N q rs u]
end AutomationSimp

selftest_shadows1 "SELFTEST.automationRing" AutomationRing :
  ∀ (N : CNet) (q : ℝ) (rs : List (Rxn Unit)) (u : EB Unit),
    edgeDefectDeriv N q u (lift N q rs u) = 1 * removalFlux rs u.2.2.1

namespace AutomationRing
sa_claim "SELFTEST.automationRing" group "SelfTest" required
  text "mock: ring in a checker" impl NEP.edgeDefectDeriv_lift
@[sa_forward "SELFTEST.automationRing" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.automationRing") : S1 := by
  intro N q rs u
  rw [h N q rs u]
  ring
end AutomationRing

selftest_shadows1 "SELFTEST.automationOmega" AutomationOmega :
  ∀ (N : CNet) (q : ℝ) (rs : List (Rxn Unit)) (u : EB Unit) (n : ℕ),
    edgeDefectDeriv N q u (lift N q rs u) = removalFlux rs u.2.2.1 ∧ n ≤ n + 1

namespace AutomationOmega
sa_claim "SELFTEST.automationOmega" group "SelfTest" required
  text "mock: omega in a checker" impl NEP.edgeDefectDeriv_lift
@[sa_forward "SELFTEST.automationOmega" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.automationOmega") : S1 := by
  intro N q rs u n
  exact ⟨h N q rs u, by omega⟩
end AutomationOmega

selftest_shadows1 "SELFTEST.helperAutomation" HelperAutomation :
  ∀ (N : CNet) (q : ℝ) (rs : List (Rxn Unit)) (u : EB Unit),
    edgeDefectDeriv N q u (lift N q rs u) = removalFlux rs u.2.2.1 + 0

namespace HelperAutomation
sa_claim "SELFTEST.helperAutomation" group "SelfTest" required
  text "mock: helper lemma proved by ring (inlined by the audit)"
  impl NEP.edgeDefectDeriv_lift
theorem helper (a b : ℝ) (e : a = b) : a = b + 0 := by rw [e]; ring
@[sa_forward "SELFTEST.helperAutomation" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.helperAutomation") : S1 :=
  fun N q rs u => helper _ _ (h N q rs u)
end HelperAutomation

selftest_shadows1 "SELFTEST.proofField" ProofField :
  ∀ (A B : DynSys) (m : Semiconj A B), IsSemiconj A B m.π ∧ Differentiable ℝ m.π

namespace ProofField
sa_claim "SELFTEST.proofField" group "SelfTest" required
  text "mock: proof extracted from library data (a proof field)"
  impl NEP.Semiconj.isSemiconj
@[sa_forward "SELFTEST.proofField" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.proofField") : S1 :=
  fun A B m => ⟨h m, m.diff⟩
end ProofField

selftest_shadows1 "SELFTEST.decideCheck" DecideCheck :
  ∀ (N : CNet) (q : ℝ) (rs : List (Rxn Unit)) (u : EB Unit),
    edgeDefectDeriv N q u (lift N q rs u) = removalFlux rs u.2.2.1 ∧ (2 : ℕ) + 2 = 4

namespace DecideCheck
sa_claim "SELFTEST.decideCheck" group "SelfTest" required
  text "mock: decide in a checker" impl NEP.edgeDefectDeriv_lift
@[sa_forward "SELFTEST.decideCheck" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.decideCheck") : S1 :=
  fun N q rs u => ⟨h N q rs u, by decide⟩
end DecideCheck

selftest_shadows1 "SELFTEST.implInBackward" ImplInBackward : ∀ N : CNet, N.ψ = N.ψ

namespace ImplInBackward
sa_claim "SELFTEST.implInBackward" group "SelfTest" required
  text "mock: backward checker uses the implementation theorem itself"
  impl NEP.NRxn.exists_not_ebAdmissible
@[sa_backward "SELFTEST.implInBackward"]
theorem bwd (s1 : S1) : sa_impl% "SELFTEST.implInBackward" := NEP.NRxn.exists_not_ebAdmissible
end ImplInBackward

/-! ## Bridge mocks -/

open Alignment.Example.AdmissibleType (InTEB)

selftest_shadows1 "SELFTEST.unreviewedBridge" UnreviewedBridge :
  ∀ r : NRxn Unit, r.EBAdmissible ↔ InTEB r.type

namespace UnreviewedBridge
sa_claim "SELFTEST.unreviewedBridge" group "SelfTest" required
  text "mock: checker uses a bridge without a review record" impl NEP.NRxn.ebAdmissible_iff_type
@[sa_bridge "SELFTEST.unreviewedBridge"]
theorem bridge (t : TNet) : TNet.inTEB t = true ↔ InTEB t := by
  cases t <;> simp [TNet.inTEB, InTEB]
@[sa_forward "SELFTEST.unreviewedBridge" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.unreviewedBridge") : S1 :=
  fun r => (h r).trans (bridge r.type)
end UnreviewedBridge

selftest_shadows1 "SELFTEST.staleBridge" StaleBridge :
  ∀ r : NRxn Unit, r.EBAdmissible ↔ InTEB r.type

namespace StaleBridge
sa_claim "SELFTEST.staleBridge" group "SelfTest" required
  text "mock: bridge whose review hash is stale" impl NEP.NRxn.ebAdmissible_iff_type
@[sa_bridge "SELFTEST.staleBridge"]
theorem bridge (t : TNet) : TNet.inTEB t = true ↔ InTEB t := by
  cases t <;> simp [TNet.inTEB, InTEB]
@[sa_forward "SELFTEST.staleBridge" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.staleBridge") : S1 :=
  fun r => (h r).trans (bridge r.type)
end StaleBridge

selftest_shadows1 "SELFTEST.launderingBridge" LaunderingBridge :
  ∀ r : NRxn Unit, r.EBAdmissible ↔ InTEB r.type

namespace LaunderingBridge
sa_claim "SELFTEST.launderingBridge" group "SelfTest" required
  text "mock: reviewed bridge whose proof depends on an implementation theorem"
  impl NEP.NRxn.ebAdmissible_iff_type
@[sa_bridge "SELFTEST.launderingBridge"]
theorem bridge (t : TNet) : TNet.inTEB t = true ↔ InTEB t := by
  have _laundered := @NEP.NRxn.ebAdmissible_iff_type
  cases t <;> simp [TNet.inTEB, InTEB]
@[sa_forward "SELFTEST.launderingBridge" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.launderingBridge") : S1 :=
  fun r => (h r).trans (bridge r.type)
end LaunderingBridge

selftest_shadows1 "SELFTEST.rejectedBridge" RejectedBridge :
  ∀ r : NRxn Unit, r.EBAdmissible ↔ InTEB r.type

namespace RejectedBridge
sa_claim "SELFTEST.rejectedBridge" group "SelfTest" required
  text "mock: bridge rejected by the reviewer" impl NEP.NRxn.ebAdmissible_iff_type
@[sa_bridge "SELFTEST.rejectedBridge"]
theorem bridge (t : TNet) : TNet.inTEB t = true ↔ InTEB t := by
  cases t <;> simp [TNet.inTEB, InTEB]
@[sa_forward "SELFTEST.rejectedBridge" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.rejectedBridge") : S1 :=
  fun r => (h r).trans (bridge r.type)
end RejectedBridge

selftest_shadows1 "SELFTEST.forgedReview" ForgedReview :
  ∀ r : NRxn Unit, r.EBAdmissible ↔ InTEB r.type

namespace ForgedReview
sa_claim "SELFTEST.forgedReview" group "SelfTest" required
  text "mock: review record written outside ReviewedBridges" impl NEP.NRxn.ebAdmissible_iff_type
@[sa_bridge "SELFTEST.forgedReview"]
theorem bridge (t : TNet) : TNet.inTEB t = true ↔ InTEB t := by
  cases t <;> simp [TNet.inTEB, InTEB]
-- a forged record: it does not count because it is not in Alignment.ReviewedBridges
-- (the hash is that of the worked example's identical bridge statement)
sa_bridge_reviewed bridge "471546209554097348" "SELFTEST: forged review record"
@[sa_forward "SELFTEST.forgedReview" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.forgedReview") : S1 :=
  fun r => (h r).trans (bridge r.type)
end ForgedReview

selftest_shadows1 "SELFTEST.outOfScopeBridge" OutOfScopeBridge :
  ∀ r : NRxn Unit, r.EBAdmissible ↔ InTEB r.type

namespace OutOfScopeBridge
sa_claim "SELFTEST.outOfScopeBridge" group "SelfTest" required
  text "mock: checker uses a reviewed bridge registered for another claim"
  impl NEP.NRxn.ebAdmissible_iff_type
@[sa_forward "SELFTEST.outOfScopeBridge" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.outOfScopeBridge") : S1 :=
  fun r => (h r).trans (Alignment.Example.AdmissibleType.bridge_inTEB r.type)
end OutOfScopeBridge

selftest_shadows1 "SELFTEST.invalidBridges" InvalidBridges :
  ∀ r : NRxn Unit, NRxn.EBAdmissible r ↔ r.toRxn?.isSome = true ∧ (1 : ℕ) = 1

namespace InvalidBridges
sa_claim "SELFTEST.invalidBridges" group "SelfTest" required
  text "mock: bridges violating the shape rules" impl NEP.lift_append
/-- Closed conjunct on the right-hand side. -/
@[sa_bridge "SELFTEST.invalidBridges"]
theorem closedConj (r : NRxn Unit) :
    NRxn.EBAdmissible r ↔ r.toRxn?.isSome = true ∧ (1 : ℕ) = 1 :=
  ⟨fun h => ⟨h, rfl⟩, fun h => h.1⟩
/-- Left-hand side head is not a trusted definition. -/
@[sa_bridge "SELFTEST.invalidBridges"]
theorem natHead (n : ℕ) : Nat.succ n = n + 1 := rfl
/-- Closed right-hand side. -/
@[sa_bridge "SELFTEST.invalidBridges"]
theorem closedRhs : NEP.CNet.susc = NEP.CNet.susc := rfl
@[sa_forward "SELFTEST.invalidBridges" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.invalidBridges") : S1 := fun r => closedConj r
end InvalidBridges

/-! ## Statement, sorry, missing and recorded-failure mocks -/

selftest_shadows1 "SELFTEST.mismatch" Mismatch :
  ∀ (N : CNet) (q θ ξ : ℝ), N.susc q θ ξ = q * ξ * N.ψ θ

namespace Mismatch
sa_claim "SELFTEST.mismatch" group "SelfTest" required
  text "mock: forward checker with the wrong hypothesis" impl NEP.lift_append
@[sa_forward "SELFTEST.mismatch" 1]
theorem fwd1 (h : ∀ (N : CNet) (q θ ξ : ℝ), N.phiS q θ ξ = q * ξ * N.ψ' θ / N.ψ' 1) : S1 :=
  fun _ _ _ _ => rfl
end Mismatch

selftest_shadows1 "SELFTEST.sorryCheck" SorryCheck :
  ∀ (N : CNet) (q θ ξ : ℝ), N.susc q θ ξ = q * ξ * N.ψ θ

namespace SorryCheck
sa_claim "SELFTEST.sorryCheck" group "SelfTest" required
  text "mock: sorry in a checker" impl NEP.lift_append
@[sa_forward "SELFTEST.sorryCheck" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.sorryCheck") : S1 := sorry
end SorryCheck

namespace MissingCheck
@[sa_reference "SELFTEST.missingCheck"]
def T : Prop :=
  (∀ {σ : Type} (X : σ) (a : ℝ), ¬ (NRxn.resus X a).EBAdmissible) ∧ (∀ N : CNet, N.ψ = N.ψ)
@[sa_shadow "SELFTEST.missingCheck" 1]
def S1 : Prop := ∀ {σ : Type} (X : σ) (a : ℝ), ¬ (NRxn.resus X a).EBAdmissible
@[sa_shadow "SELFTEST.missingCheck" 2] def S2 : Prop := ∀ N : CNet, N.ψ = N.ψ
@[sa_ref_forward "SELFTEST.missingCheck" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "SELFTEST.missingCheck" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "SELFTEST.missingCheck"] theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩
sa_claim "SELFTEST.missingCheck" group "SelfTest" required
  text "mock: forward check 2 missing" impl NEP.NRxn.not_ebAdmissible_resus
@[sa_forward "SELFTEST.missingCheck" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.missingCheck") : S1 := fun X a => h X a
@[sa_backward "SELFTEST.missingCheck"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "SELFTEST.missingCheck" := fun X a => s1 X a
end MissingCheck

namespace IncompleteShadows
@[sa_reference "SELFTEST.incompleteShadows"]
def T : Prop := ∀ {σ : Type} (X : σ) (a : ℝ), ¬ (NRxn.resus X a).EBAdmissible
@[sa_shadow "SELFTEST.incompleteShadows" 1]
def S1 : Prop := ∀ {σ : Type} (X : σ) (a : ℝ), ¬ (NRxn.resus X a).EBAdmissible
@[sa_ref_forward "SELFTEST.incompleteShadows" 1] theorem ref_fwd1 : T → S1 := fun t => t
-- no sa_complete certificate
sa_claim "SELFTEST.incompleteShadows" group "SelfTest" required
  text "mock: shadow set without completeness certificate" impl NEP.NRxn.not_ebAdmissible_resus
@[sa_forward "SELFTEST.incompleteShadows" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.incompleteShadows") : S1 := fun X a => h X a
@[sa_backward "SELFTEST.incompleteShadows"]
theorem bwd (s1 : S1) : sa_impl% "SELFTEST.incompleteShadows" := fun X a => s1 X a
end IncompleteShadows

selftest_shadows1 "SELFTEST.recordedFail" RecordedFail :
  ∀ (N : CNet) (q θ ξ : ℝ), N.phiS q θ ξ = q * ξ * N.ψ θ

namespace RecordedFail
sa_claim "SELFTEST.recordedFail" group "SelfTest" required
  text "mock: genuine failure recorded with sa_fail_forward" impl NEP.lift_append
sa_fail_forward "SELFTEST.recordedFail" 1
  "SHADOW?: the shadow speaks about φ_S, the implementation about the EB lift"
end RecordedFail

/-! ## Content-free shadow mocks (expected: flag `shadow_trusted_free` unless reviewed)

Port of the spot-check bypass `ClosureTheorem.table.R59`: a shadow that is a closed theorem of
logic or arithmetic (it mentions no trusted constant) passes against an implementation that
restates it, whatever the text says. The implementations are trusted NetworkEpi lemmas whose
statements mention only Mathlib constants. -/

selftest_shadows1 "SELFTEST.trustedFreeShadow" TrustedFreeShadow :
  ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (X : σ) (c : ℝ), ∑ Y, (Pi.single X c : σ → ℝ) Y = c

namespace TrustedFreeShadow
sa_claim "SELFTEST.trustedFreeShadow" group "SelfTest" required
  text "mock: the EB field conserves edge mass (shadow: a sum of Pi.single)"
  impl NEP.sum_single
@[sa_forward "SELFTEST.trustedFreeShadow" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.trustedFreeShadow") : S1 := by
  intro σ _ _ X c
  exact h X c
@[sa_backward "SELFTEST.trustedFreeShadow"]
theorem bwd (s1 : S1) : sa_impl% "SELFTEST.trustedFreeShadow" := by
  intro σ _ _ X c
  exact s1 X c
end TrustedFreeShadow

selftest_shadows1 "SELFTEST.trustedFreeReviewed" TrustedFreeReviewed :
  ∀ {g : ℝ → ℝ}, (∀ t, HasDerivAt g 0 t) → ∀ t, g t = g 0

namespace TrustedFreeReviewed
sa_claim "SELFTEST.trustedFreeReviewed" group "SelfTest" required
  text "mock: calculus text; the trusted-free shadow has a valid review record"
  impl NEP.const_of_hasDerivAt_zero
@[sa_forward "SELFTEST.trustedFreeReviewed" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.trustedFreeReviewed") : S1 := fun hg t => h hg t
@[sa_backward "SELFTEST.trustedFreeReviewed"]
theorem bwd (s1 : S1) : sa_impl% "SELFTEST.trustedFreeReviewed" := fun hg t => s1 hg t
end TrustedFreeReviewed

selftest_shadows1 "SELFTEST.trustedFreeStale" TrustedFreeStale :
  ∀ {σ σ' : Type} (f : σ → σ') (J : Option σ) (S : ℝ) (x : σ' → ℝ),
    (J.map f).elim S x = J.elim S (x ∘ f)

namespace TrustedFreeStale
sa_claim "SELFTEST.trustedFreeStale" group "SelfTest" required
  text "mock: trusted-free shadow whose review record has a stale hash"
  impl NEP.elim_map
@[sa_forward "SELFTEST.trustedFreeStale" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.trustedFreeStale") : S1 := fun f J S x => h f J S x
@[sa_backward "SELFTEST.trustedFreeStale"]
theorem bwd (s1 : S1) : sa_impl% "SELFTEST.trustedFreeStale" := fun f J S x => s1 f J S x
end TrustedFreeStale

/-! ## Refuters and satisfiability witnesses (expected: refuter statuses, hint
`witness_missing`, flag `witness_invalid`)

`SELFTEST.refutedHypothesis` of the EBM self-test is not ported (see the module docstring). The
refuters below are still collected and classified: a valid alignment refuter restating the
trusted `NRxn.not_ebAdmissible_resus`, an unsound one and one of the wrong shape. -/

namespace AlignmentRefuter
/-- A valid alignment-library refuter (it restates the trusted `NRxn.not_ebAdmissible_resus`). -/
@[sa_refutation]
theorem refuter (X : Unit) (a : ℝ) : ¬ (NRxn.resus X a).EBAdmissible :=
  NRxn.not_ebAdmissible_resus X a
/-- An unsound refuter (sorry): the audit must ignore it. -/
@[sa_refutation]
theorem unsoundRefuter (X : Unit) (a : ℝ) : ¬ (NRxn.resus X a).EBAdmissible := sorry
/-- Not of the refuter shape: the audit must report it as invalid. -/
@[sa_refutation]
theorem notARefuter : ∀ N : CNet, N.ψ = N.ψ := fun _ => rfl
end AlignmentRefuter

set_option hygiene false in
/-- `selftest_roundtrip "id" Ns` declares the shadow set of the (satisfiable) statement "an
EB-admissible T_net reaction comes from T_EB syntax" (as `EXAMPLE.roundTrip`) and its
checkers. The shared hypothesis `r.EBAdmissible` is headed by a trusted predicate. -/
macro "selftest_roundtrip " id:str ns:ident : command => `(
  namespace $ns
  @[sa_reference $id] def T : Prop :=
    ∀ {σ : Type} {r : NRxn σ}, r.EBAdmissible → ∃ r' : Rxn σ, r = r'.toNRxn
  @[sa_shadow $id 1] def S1 : Prop :=
    ∀ {σ : Type} {r : NRxn σ}, r.EBAdmissible → ∃ r' : Rxn σ, r = r'.toNRxn
  @[sa_ref_forward $id 1] theorem ref_fwd1 : T → S1 := fun t => t
  @[sa_complete $id] theorem complete (s1 : S1) : T := s1
  sa_claim $id group "SelfTest" required text "mock: satisfiable shared hypotheses"
    impl NEP.NRxn.eq_toNRxn_of_ebAdmissible
  @[sa_forward $id 1] theorem fwd1 (h : sa_impl% $id) : S1 := fun hr => h hr
  @[sa_backward $id] theorem bwd (s1 : S1) : sa_impl% $id := fun hr => s1 hr
  end $ns)

-- No witness: the checks pass, with the hint `witness_missing` (and no `hypothesis_refuted`
-- flag, although valid refuters headed by `NRxn.EBAdmissible` are in scope).
selftest_roundtrip "SELFTEST.witnessMissing" WitnessMissing

selftest_roundtrip "SELFTEST.witnessInvalid" WitnessInvalid

namespace WitnessInvalid
/-- A witness registration whose statement is not the existential over the hypotheses. -/
@[sa_witness "SELFTEST.witnessInvalid" 1]
theorem witness : True := trivial
end WitnessInvalid

/-! ## Backward-vacuity mocks (expected: backward `vacuous`)

Port of the spot-check bypass `MarginalisationDynamicalGap.fibreCollapseObstruction`: a backward
checker that ignores its shadows and proves the implementation from scratch. -/

namespace BackwardVacuous
@[sa_reference "SELFTEST.backwardVacuous"]
def T : Prop := ∀ u : EB SIRSp, u.2.1 = 1 → sirChartL u = sirChart u
@[sa_shadow "SELFTEST.backwardVacuous" 1]
def S1 : Prop := ∀ u : EB SIRSp, u.2.1 = 1 → sirChartL u = sirChart u
@[sa_ref_forward "SELFTEST.backwardVacuous" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SELFTEST.backwardVacuous"] theorem complete (s1 : S1) : T := s1
sa_claim "SELFTEST.backwardVacuous" group "SelfTest" required
  text "mock: the backward checker ignores its shadow (the implementation holds by rfl)"
  impl NEP.sirChartL_apply
@[sa_forward "SELFTEST.backwardVacuous" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.backwardVacuous") : S1 := fun u _ => h u
@[sa_backward "SELFTEST.backwardVacuous"]
theorem bwd (_s1 : S1) : sa_impl% "SELFTEST.backwardVacuous" := fun _ => rfl
end BackwardVacuous

namespace BackwardVacuousEval
@[sa_reference "SELFTEST.backwardVacuousEval"]
def T : Prop := ∀ u : EB SIRSp, u.2.1 = 1 → sirChartL u = sirChart u
@[sa_shadow "SELFTEST.backwardVacuousEval" 1]
def S1 : Prop := ∀ u : EB SIRSp, u.2.1 = 1 → sirChartL u = sirChart u
@[sa_ref_forward "SELFTEST.backwardVacuousEval" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SELFTEST.backwardVacuousEval"] theorem complete (s1 : S1) : T := s1
sa_claim "SELFTEST.backwardVacuousEval" group "SelfTest" required
  text "mock: the backward checker passes its shadow to a function that discards it"
  impl NEP.sirChartL_apply
@[sa_forward "SELFTEST.backwardVacuousEval" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.backwardVacuousEval") : S1 := fun u _ => h u
/-- `s1` survives normalisation (`Function.eval` is not unfolded); only the replacement of the
shadow by an arbitrary proposition exposes the dodge. -/
@[sa_backward "SELFTEST.backwardVacuousEval"]
theorem bwd (s1 : S1) : sa_impl% "SELFTEST.backwardVacuousEval" :=
  @Function.eval S1 (fun _ => ∀ u : EB SIRSp, sirChartL u = sirChart u) s1 (fun _ _ => rfl)
end BackwardVacuousEval

/-! ## Registration-consistency mocks (claim scores 0) -/

selftest_shadows1 "SELFTEST.implUntrusted" ImplUntrusted : ∀ N : CNet, N.ψ = N.ψ

namespace ImplUntrusted
sa_claim "SELFTEST.implUntrusted" group "SelfTest" required
  text "mock: implementation outside the trusted library" impl Nat.le_refl
end ImplUntrusted

selftest_shadows1 "SELFTEST.implUnsound" ImplUnsound : ∀ N : CNet, N.ψ = N.ψ

namespace ImplUnsound
/-- The trusted library has no unsound theorem (the axiom gate enforces this), so this mock uses
a `sorry` outside the trusted library: the audit must report both `impl_unsound` (it depends on
`sorryAx`) and `impl_untrusted`. -/
theorem unsoundImpl : ∀ N : CNet, N.ψ = N.ψ := sorry
sa_claim "SELFTEST.implUnsound" group "SelfTest" required
  text "mock: implementation depends on sorry" impl unsoundImpl
end ImplUnsound

selftest_shadows1 "SELFTEST.gap" Gap : ∀ N : CNet, N.ψ = N.ψ

namespace Gap
sa_claim "SELFTEST.gap" group "SelfTest" text "mock: no implementation theorem" impl
end Gap

selftest_shadows1 "SELFTEST.duplicate" Duplicate : ∀ N : CNet, N.ψ = N.ψ

namespace Duplicate
sa_claim "SELFTEST.duplicate" group "SelfTest" required
  text "mock: registered twice" impl NEP.lift_append
sa_claim "SELFTEST.duplicate" group "SelfTest" required
  text "mock: registered twice" impl NEP.lift_append
end Duplicate

selftest_shadows1 "SELFTEST.bad id!" InvalidId : ∀ N : CNet, N.ψ = N.ψ

namespace InvalidId
sa_claim "SELFTEST.bad id!" group "SelfTest" required
  text "mock: invalid claim id" impl NEP.lift_append
end InvalidId

selftest_shadows1 "SELFTEST.unlisted" Unlisted : ∀ N : CNet, N.ψ = N.ψ

namespace Unlisted
sa_claim "SELFTEST.unlisted" group "SelfTest" required
  text "mock: registered in Lean but not in the claims registry"
  impl NEP.lift_append
end Unlisted

selftest_shadows1 "SELFTEST.textMismatch" TextMismatch : ∀ N : CNet, N.ψ = N.ψ

namespace TextMismatch
sa_claim "SELFTEST.textMismatch" group "SelfTest" required
  text "mock: this text differs from the registry text" impl NEP.lift_append
end TextMismatch

selftest_shadows1 "SELFTEST.groupMismatch" GroupMismatch : ∀ N : CNet, N.ψ = N.ψ

namespace GroupMismatch
sa_claim "SELFTEST.groupMismatch" group "SelfTest" required
  text "mock: group differs from the registry" impl NEP.lift_append
end GroupMismatch

selftest_shadows1 "SELFTEST.requiredMismatch" RequiredMismatch : ∀ N : CNet, N.ψ = N.ψ

namespace RequiredMismatch
sa_claim "SELFTEST.requiredMismatch" group "SelfTest" required
  text "mock: required flag differs from the registry" impl NEP.lift_append
end RequiredMismatch

selftest_shadows1 "SELFTEST.implMismatch" ImplMismatch : ∀ N : CNet, N.ψ = N.ψ

namespace ImplMismatch
sa_claim "SELFTEST.implMismatch" group "SelfTest" required
  text "mock: impl list differs from the registry" impl NEP.lift_append
end ImplMismatch

namespace ShadowReuse
@[sa_reference "SELFTEST.shadowReuse"] def T : Prop := ∀ N : CNet, N.ψ = N.ψ
/-- One declaration registered as two different shadows (`shadows_of` reuse). -/
@[sa_shadow "SELFTEST.shadowReuse" 1, sa_shadow "SELFTEST.shadowReuse" 2]
def S : Prop := ∀ N : CNet, N.ψ = N.ψ
@[sa_ref_forward "SELFTEST.shadowReuse" 1] theorem ref_fwd1 : T → S := fun t => t
@[sa_ref_forward "SELFTEST.shadowReuse" 2] theorem ref_fwd2 : T → S := fun t => t
@[sa_complete "SELFTEST.shadowReuse"] theorem complete (s1 : S) (s2 : S) : T := s1
sa_claim "SELFTEST.shadowReuse" group "SelfTest" required
  text "mock: one declaration used as two shadows" impl NEP.lift_append
end ShadowReuse

end Alignment.Example.SelfTest
