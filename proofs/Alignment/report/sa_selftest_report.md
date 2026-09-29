# SA-PASS report (self-test)

Generated 2026-09-28 18:48 from `Alignment/report/sa_pass_audit.json` (Lean 4.29.0-rc4) and `Alignment/Example/claims_example.yaml`, `Alignment/Example/claims_selftest.yaml`.

Trusted modules loaded by the audit: `NetworkEpi`, `NetworkEpi.Closure.PT`, `NetworkEpi.Dyn.Basic`, `NetworkEpi.Dyn.Products`, `NetworkEpi.Morphisms.All`, `NetworkEpi.Morphisms.Common`, `NetworkEpi.Morphisms.Compact`, `NetworkEpi.Morphisms.NGM`, `NetworkEpi.Morphisms.Pairwise`, `NetworkEpi.Morphisms.Poisson`, `NetworkEpi.Morphisms.Rempala`, `NetworkEpi.Morphisms.Stoich`, `NetworkEpi.Morphisms.WellMixed`, `NetworkEpi.Semantics.EB`, `NetworkEpi.Semantics.MA`, `NetworkEpi.Semantics.PWS`, `NetworkEpi.Semantics.PoissonSIR`, `NetworkEpi.Semantics.Solutions`, `NetworkEpi.Syntax.Rxn`

Tool sanity: 3/3 worked-example claims (`EXAMPLE.*`) pass every check (run `bash scripts/sa_pass.sh --self-test` for the full self-test).

## Summary

| quantity | value |
|---|---|
| claims in registry | 49 |
| claims registered in Lean | 50 |
| registry claims not registered in Lean | 0 |
| required claims (status implemented) | 48 |
| SA-PASS = 1 (all / required) | 5 / 5 |
| mean SA-PASS_soft (registered claims) | 0.135 |
| required failures | 43 |
| check statuses | audit_violation: 14, fail: 2, missing: 51, pass: 24, sorry: 1, vacuous: 12 |
| bridges | invalid: 4, rejected: 1, reviewed: 1, stale: 1, unreviewed: 2 |
| hints (not scored) | backward_unused_shadows: 1, witness_missing: 2 |
| trusted-free shadows (by review status) | reviewed: 1, stale: 1, unreviewed: 1 |
| claims with a refuted implementation hypothesis | 0 |

## Per group

| group | registry | registered | required | SA-PASS=1 | mean soft | forward pass | backward pass | required failures |
|---|---|---|---|---|---|---|---|---|
| Example | 3 | 3 | 3 | 3 | 1.0 | 5/5 | 3/3 | 0 |
| Other | 1 | 1 | 1 | 0 | 0.0 | 0/1 | 0/1 | 1 |
| SelfTest | 45 | 46 | 44 | 2 | 0.0815 | 9/48 | 7/46 | 42 |

## Claims

| id | req | n | forward | backward | SA-PASS | soft | flags |
|---|---|---|---|---|---|---|---|
| `EXAMPLE.admissibleType` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `EXAMPLE.notAdmissible` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [0]) |
| `EXAMPLE.roundTrip` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `SELFTEST.groupMismatch` | yes | 1 | missing | missing | 0 | 0.0 | group_mismatch |
| `SELFTEST.automationOmega` | yes | 1 | audit_violation | missing | 0 | 0.0 |  |
| `SELFTEST.automationRing` | yes | 1 | audit_violation | missing | 0 | 0.0 |  |
| `SELFTEST.automationSimp` | yes | 1 | audit_violation | missing | 0 | 0.0 |  |
| `SELFTEST.backwardVacuous` | yes | 1 | pass | vacuous | 0 | 0.5 |  |
| `SELFTEST.backwardVacuousEval` | yes | 1 | pass | vacuous | 0 | 0.5 |  |
| `SELFTEST.bad id!` | yes | 1 | missing | missing | 0 | 0.0 | invalid_id |
| `SELFTEST.decideCheck` | yes | 1 | audit_violation | missing | 0 | 0.0 |  |
| `SELFTEST.duplicate` | yes | 1 | missing | missing | 0 | 0.0 | duplicate |
| `SELFTEST.forgedReview` | yes | 1 | audit_violation | missing | 0 | 0.0 |  |
| `SELFTEST.gap` | no | 1 | missing | missing | 0 | 0.0 | gap |
| `SELFTEST.helperAutomation` | yes | 1 | audit_violation | missing | 0 | 0.0 |  |
| `SELFTEST.implInBackward` | yes | 1 | missing | audit_violation | 0 | 0.0 |  |
| `SELFTEST.implMismatch` | yes | 1 | missing | missing | 0 | 0.0 | impl_mismatch |
| `SELFTEST.implUnsound` | yes | 1 | missing | missing | 0 | 0.0 | impl_unsound, impl_untrusted (identical to impl: [0, 1]) |
| `SELFTEST.implUntrusted` | yes | 1 | missing | missing | 0 | 0.0 | impl_untrusted |
| `SELFTEST.incompleteShadows` | yes | 1 | pass | pass | 0 | 0.0 | incomplete (identical to impl: [0, 1]) |
| `SELFTEST.invalidBridges` | yes | 1 | audit_violation | missing | 0 | 0.0 |  |
| `SELFTEST.launderingBridge` | yes | 1 | audit_violation | missing | 0 | 0.0 |  |
| `SELFTEST.mismatch` | yes | 1 | fail | missing | 0 | 0.0 |  |
| `SELFTEST.missingCheck` | yes | 2 | pass missing | pass | 0 | 0.75 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `SELFTEST.outOfScopeBridge` | yes | 1 | audit_violation | missing | 0 | 0.0 |  |
| `SELFTEST.proofField` | yes | 1 | audit_violation | missing | 0 | 0.0 |  |
| `SELFTEST.recordedFail` | yes | 1 | fail | missing | 0 | 0.0 |  |
| `SELFTEST.rejectedBridge` | yes | 1 | audit_violation | missing | 0 | 0.0 |  |
| `SELFTEST.requiredMismatch` | no | 1 | missing | missing | 0 | 0.0 | required_mismatch |
| `SELFTEST.shadowReuse` | yes | 2 | missing missing | missing | 0 | 0.0 | shadow_mismatch |
| `SELFTEST.sorryCheck` | yes | 1 | sorry | missing | 0 | 0.0 |  |
| `SELFTEST.staleBridge` | yes | 1 | audit_violation | missing | 0 | 0.0 |  |
| `SELFTEST.textMismatch` | yes | 1 | missing | missing | 0 | 0.0 | text_mismatch |
| `SELFTEST.trustedFreeReviewed` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `SELFTEST.trustedFreeShadow` | yes | 1 | pass | pass | 0 | 0.0 | shadow_trusted_free (identical to impl: [0, 1]) |
| `SELFTEST.trustedFreeStale` | yes | 1 | pass | pass | 0 | 0.0 | shadow_trusted_free (identical to impl: [0, 1]) |
| `SELFTEST.unlisted` | yes | 1 | missing | missing | 0 | 0.0 | unlisted |
| `SELFTEST.unreviewedBridge` | yes | 1 | audit_violation | missing | 0 | 0.0 |  |
| `SELFTEST.vacuousAndLeft` | yes | 1 | vacuous | missing | 0 | 0.0 |  |
| `SELFTEST.vacuousAuxLemma` | yes | 1 | vacuous | missing | 0 | 0.0 |  |
| `SELFTEST.vacuousBeta` | yes | 1 | vacuous | missing | 0 | 0.0 |  |
| `SELFTEST.vacuousConst` | yes | 1 | vacuous | missing | 0 | 0.0 |  |
| `SELFTEST.vacuousDataArg` | yes | 1 | vacuous | missing | 0 | 0.0 |  |
| `SELFTEST.vacuousEval` | yes | 1 | vacuous | missing | 0 | 0.0 |  |
| `SELFTEST.vacuousExistsElim` | yes | 1 | vacuous | missing | 0 | 0.0 |  |
| `SELFTEST.vacuousIgnore` | yes | 1 | vacuous | missing | 0 | 0.0 |  |
| `SELFTEST.vacuousMatch` | yes | 1 | vacuous | missing | 0 | 0.0 |  |
| `SELFTEST.vacuousNestedObtain` | yes | 1 | vacuous | missing | 0 | 0.0 |  |
| `SELFTEST.witnessInvalid` | yes | 1 | pass | pass | 0 | 0.0 | witness_invalid (identical to impl: [0, 1]) (hints: witness_missing) |
| `SELFTEST.witnessMissing` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) (hints: witness_missing) |

## Required failures

* `SELFTEST.vacuousIgnore`: forward 1: vacuous; backward: missing
* `SELFTEST.vacuousBeta`: forward 1: vacuous; backward: missing
* `SELFTEST.vacuousAndLeft`: forward 1: vacuous; backward: missing
* `SELFTEST.vacuousAuxLemma`: forward 1: vacuous; backward: missing
* `SELFTEST.vacuousEval`: forward 1: vacuous; backward: missing
* `SELFTEST.vacuousConst`: forward 1: vacuous; backward: missing
* `SELFTEST.vacuousMatch`: forward 1: vacuous; backward: missing
* `SELFTEST.vacuousExistsElim`: forward 1: vacuous; backward: missing
* `SELFTEST.vacuousDataArg`: forward 1: vacuous; backward: missing
* `SELFTEST.vacuousNestedObtain`: forward 1: vacuous; backward: missing
* `SELFTEST.automationSimp`: forward 1: audit_violation; backward: missing
* `SELFTEST.automationRing`: forward 1: audit_violation; backward: missing
* `SELFTEST.automationOmega`: forward 1: audit_violation; backward: missing
* `SELFTEST.helperAutomation`: forward 1: audit_violation; backward: missing
* `SELFTEST.proofField`: forward 1: audit_violation; backward: missing
* `SELFTEST.decideCheck`: forward 1: audit_violation; backward: missing
* `SELFTEST.implInBackward`: forward 1: missing; backward: audit_violation
* `SELFTEST.unreviewedBridge`: forward 1: audit_violation; backward: missing
* `SELFTEST.staleBridge`: forward 1: audit_violation; backward: missing
* `SELFTEST.launderingBridge`: forward 1: audit_violation; backward: missing
* `SELFTEST.rejectedBridge`: forward 1: audit_violation; backward: missing
* `SELFTEST.forgedReview`: forward 1: audit_violation; backward: missing
* `SELFTEST.outOfScopeBridge`: forward 1: audit_violation; backward: missing
* `SELFTEST.invalidBridges`: forward 1: audit_violation; backward: missing
* `SELFTEST.mismatch`: forward 1: fail; backward: missing
* `SELFTEST.sorryCheck`: forward 1: sorry; backward: missing
* `SELFTEST.missingCheck`: forward 2: missing
* `SELFTEST.incompleteShadows`: incomplete: no sa_complete
* `SELFTEST.recordedFail`: forward 1: fail; backward: missing
* `SELFTEST.trustedFreeShadow`: shadow_trusted_free: S1 (Alignment.Example.SelfTest.TrustedFreeShadow.S1) mentions no trusted-library constant after inlining alignment helpers (content hash 3140697068141844361; review: unreviewed)
* `SELFTEST.trustedFreeStale`: shadow_trusted_free: S1 (Alignment.Example.SelfTest.TrustedFreeStale.S1) mentions no trusted-library constant after inlining alignment helpers (content hash 10773187043888535830; review: stale)
* `SELFTEST.witnessInvalid`: witness_invalid: Alignment.Example.SelfTest.WitnessInvalid.witness: statement is not `∃ x₁ … xₖ, True` over the binders of NEP.NRxn.eq_toNRxn_of_ebAdmissible up to its last hypothesis
* `SELFTEST.backwardVacuous`: backward: vacuous
* `SELFTEST.backwardVacuousEval`: backward: vacuous
* `SELFTEST.implUntrusted`: impl_untrusted: Nat.le_refl is declared in Init.Prelude, not in the trusted library; forward 1: missing; backward: missing
* `SELFTEST.implUnsound`: impl_untrusted: Alignment.Example.SelfTest.ImplUnsound.unsoundImpl is declared in Alignment.Example.SelfTest, not in the trusted library; impl_unsound: Alignment.Example.SelfTest.ImplUnsound.unsoundImpl depends on [sorryAx]; forward 1: missing; backward: missing
* `SELFTEST.duplicate`: duplicate: sa_claim registered 2 times; forward 1: missing; backward: missing
* `SELFTEST.bad id!`: invalid_id: "SELFTEST.bad id!" does not match [A-Za-z0-9._-]+; registry id does not match [A-Za-z0-9._-]+; forward 1: missing; backward: missing
* `SELFTEST.unlisted`: unlisted: not in the claims registry; forward 1: missing; backward: missing
* `SELFTEST.textMismatch`: text_mismatch: sa_claim text differs from the registry text; forward 1: missing; backward: missing
* `SELFTEST.groupMismatch`: group_mismatch: registry `Other` vs Lean `SelfTest`; forward 1: missing; backward: missing
* `SELFTEST.implMismatch`: impl_mismatch: registry ['NEP.maLift_append'] vs Lean ['NEP.lift_append']; forward 1: missing; backward: missing
* `SELFTEST.shadowReuse`: shadow_mismatch: Alignment.Example.SelfTest.ShadowReuse.S is registered more than once as a shadow/reference; Alignment.Example.SelfTest.ShadowReuse.S is registered more than once as a shadow/reference; forward 1: missing; forward 2: missing; backward: missing

## Bridges

| bridge | claims | status | hash | statement | notes |
|---|---|---|---|---|---|
| `Alignment.Example.SelfTest.InvalidBridges.closedConj` | SELFTEST.invalidBridges | invalid | `13059473230251658442` | `∀ (r : NEP.NRxn Unit), r.EBAdmissible ↔ r.toRxn?.isSome = true ∧ 1 = 1` | left-hand side argument is not a bound variable; closed conjunct on the right-hand side |
| `Alignment.Example.SelfTest.InvalidBridges.closedRhs` | SELFTEST.invalidBridges | invalid | `5619294697670073018` | `NEP.CNet.susc = NEP.CNet.susc` | closed right-hand side (mentions no bound variable) |
| `Alignment.Example.SelfTest.InvalidBridges.natHead` | SELFTEST.invalidBridges | invalid | `6039523524133956966` | `∀ (n : ℕ), n.succ = n + 1` | left-hand side head Nat.succ is not a definition of the trusted library |
| `Alignment.Example.SelfTest.LaunderingBridge.bridge` | SELFTEST.launderingBridge | invalid | `471546209554097348` | `∀ (t : NEP.TNet), t.inTEB = true ↔ Alignment.Example.AdmissibleType.InTEB t` | depends on implementation theorem NEP.NRxn.ebAdmissible_iff_type (via Alignment.Example.SelfTest.LaunderingBridge.bridge → NEP.NRxn.ebAdmissible_iff_type) |
| `Alignment.Example.SelfTest.RejectedBridge.bridge` | SELFTEST.rejectedBridge | rejected | `471546209554097348` | `∀ (t : NEP.TNet), t.inTEB = true ↔ Alignment.Example.AdmissibleType.InTEB t` | SELFTEST: rejected bridge |
| `Alignment.Example.AdmissibleType.bridge_inTEB` | EXAMPLE.admissibleType | reviewed | `471546209554097348` | `∀ (t : NEP.TNet), t.inTEB = true ↔ Alignment.Example.AdmissibleType.InTEB t` | NetworkEpi/Syntax/Rxn.lean (module docstring and TNet.inTEB docstring): T_EB = {contact, exit,   progress, remove} (DESIGN §B.2). The RHS InTEB t is exactly that four-way membership, and the   proof is a case split on the six TNet constructors with no side condition |
| `Alignment.Example.SelfTest.StaleBridge.bridge` | SELFTEST.staleBridge | stale | `471546209554097348` | `∀ (t : NEP.TNet), t.inTEB = true ↔ Alignment.Example.AdmissibleType.InTEB t` | review hash 0 does not match 471546209554097348 |
| `Alignment.Example.SelfTest.ForgedReview.bridge` | SELFTEST.forgedReview | unreviewed | `471546209554097348` | `∀ (t : NEP.TNet), t.inTEB = true ↔ Alignment.Example.AdmissibleType.InTEB t` | note: 1 review record(s) outside Alignment.ReviewedBridges ignored |
| `Alignment.Example.SelfTest.UnreviewedBridge.bridge` | SELFTEST.unreviewedBridge | unreviewed | `471546209554097348` | `∀ (t : NEP.TNet), t.inTEB = true ↔ Alignment.Example.AdmissibleType.InTEB t` |  |

## Refuted implementation hypotheses (`hypothesis_refuted`)

The implementation theorem assumes a hypothesis that a sound theorem refutes, so it is vacuously true (and so is every shadow that shares the hypothesis). The refutation is kernel-checked.

None.

## Trusted-free shadows (`shadow_trusted_free`)

These shadows mention no trusted-library constant after inlining alignment helpers, so they are closed statements of logic or arithmetic. The flag zeroes the claim until an independent reviewer confirms that the source text is itself such a statement, with `sa_shadow_reviewed <shadow> "<hash>" "<reason>"` in `Alignment/ReviewedBridges.lean`.

| claim | shadow | content hash | review |
|---|---|---|---|
| `SELFTEST.trustedFreeReviewed` | S1 `Alignment.Example.SelfTest.TrustedFreeReviewed.S1` | `17292980193152741638` | reviewed |
| `SELFTEST.trustedFreeStale` | S1 `Alignment.Example.SelfTest.TrustedFreeStale.S1` | `10773187043888535830` | stale |
| `SELFTEST.trustedFreeShadow` | S1 `Alignment.Example.SelfTest.TrustedFreeShadow.S1` | `3140697068141844361` | unreviewed |

## Hints (not scored)

`witness_missing`: an implementation hypothesis headed by a trusted predicate is shared by every shadow, and no `@[sa_witness]` certificate shows it can hold. `backward_unused_shadows`: the backward checker does not use some shadows (they may be redundant). `backward_guard_unnormalised`: the backward vacuity guard exhausted its normalisation budget and ran on the unnormalised proof (a weaker check).

* `SELFTEST.missingCheck` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `SELFTEST.witnessInvalid` witness_missing: impl 1 (NEP.NRxn.eq_toNRxn_of_ebAdmissible): its hypotheses headed by [NEP.NRxn.EBAdmissible] are also assumed by every shadow, and no @[sa_witness "SELFTEST.witnessInvalid" 1] certificate shows they can hold
* `SELFTEST.witnessMissing` witness_missing: impl 1 (NEP.NRxn.eq_toNRxn_of_ebAdmissible): its hypotheses headed by [NEP.NRxn.EBAdmissible] are also assumed by every shadow, and no @[sa_witness "SELFTEST.witnessMissing" 1] certificate shows they can hold

## Refuters

Theorems used to refute implementation hypotheses: sound trusted-library theorems `∀ ys, P₁ → … → Pₘ → False` (or `→ ¬ P`, `→ a ≠ b`) and alignment-library `@[sa_refutation]` theorems.

| refuter | origin | status | premise heads | notes |
|---|---|---|---|---|
| `Alignment.Example.SelfTest.AlignmentRefuter.notARefuter` | alignment | invalid |  | statement is not `∀ ys, P₁ → … → Pₘ → False` (or `→ ¬ P`, `→ a ≠ b`) |
| `Alignment.Example.SelfTest.AlignmentRefuter.unsoundRefuter` | alignment | invalid | NEP.NRxn.EBAdmissible | uses non-standard axioms or sorry: [sorryAx] |
| `Alignment.Example.SelfTest.AlignmentRefuter.refuter` | alignment | valid | NEP.NRxn.EBAdmissible |  |
| `NEP.NRxn.not_ebAdmissible_nodeContact` | trusted | valid | NEP.NRxn.EBAdmissible |  |
| `NEP.NRxn.not_ebAdmissible_resus` | trusted | valid | NEP.NRxn.EBAdmissible |  |
| `NEP.instDecidableEqSEIRSp._proof_2` | trusted | valid | Not, Eq |  |
| `NEP.instDecidableEqSIRSp._proof_2` | trusted | valid | Not, Eq |  |
| `NEP.instDecidableEqSp._proof_2` | trusted | valid | Not, Eq |  |
| `NEP.instDecidableEqTNet._proof_2` | trusted | valid | Not, Eq |  |
| `NEP.pwS_glue_not_strict` | trusted | valid | Eq |  |

## Offending constants

| constant [reason] | checks | examples |
|---|---|---|
| `Mathlib.Meta.NormNum.isNat_ofNat [library theorem (Mathlib.Tactic.NormNum.Basic)]` | 2 | SELFTEST.automationRing forward 1, SELFTEST.helperAutomation forward 1 |
| `Mathlib.Tactic.Ring.add_pf_add_zero [library theorem (Mathlib.Tactic.Ring.Common)]` | 2 | SELFTEST.automationRing forward 1, SELFTEST.helperAutomation forward 1 |
| `Mathlib.Tactic.Ring.atom_pf [library theorem (Mathlib.Tactic.Ring.Common)]` | 2 | SELFTEST.automationRing forward 1, SELFTEST.helperAutomation forward 1 |
| `Mathlib.Tactic.Ring.of_eq [library theorem (Mathlib.Tactic.Ring.Basic)]` | 2 | SELFTEST.automationRing forward 1, SELFTEST.helperAutomation forward 1 |
| `of_decide_eq_true [library theorem (Init.Prelude)]` | 2 | SELFTEST.automationOmega forward 1, SELFTEST.decideCheck forward 1 |
| `Alignment.Example.AdmissibleType.bridge_inTEB [bridge registered for another claim (reviewed)]` | 1 | SELFTEST.outOfScopeBridge forward 1 |
| `Alignment.Example.SelfTest.ForgedReview.bridge [unreviewed bridge]` | 1 | SELFTEST.forgedReview forward 1 |
| `Alignment.Example.SelfTest.InvalidBridges.closedConj [invalid bridge]` | 1 | SELFTEST.invalidBridges forward 1 |
| `Alignment.Example.SelfTest.LaunderingBridge.bridge [invalid bridge]` | 1 | SELFTEST.launderingBridge forward 1 |
| `Alignment.Example.SelfTest.RejectedBridge.bridge [rejected bridge]` | 1 | SELFTEST.rejectedBridge forward 1 |
| `Alignment.Example.SelfTest.StaleBridge.bridge [stale bridge]` | 1 | SELFTEST.staleBridge forward 1 |
| `Alignment.Example.SelfTest.UnreviewedBridge.bridge [unreviewed bridge]` | 1 | SELFTEST.unreviewedBridge forward 1 |
| `Decidable.byContradiction [classical reasoning / decision procedure]` | 1 | SELFTEST.automationOmega forward 1 |
| `Int.add_one_le_of_lt [library theorem (Init.Data.Int.Order)]` | 1 | SELFTEST.automationOmega forward 1 |
| `Int.natCast_add [library theorem (Init.Data.Int.Lemmas)]` | 1 | SELFTEST.automationOmega forward 1 |
| `Int.sub_nonneg_of_le [library theorem (Init.Data.Int.Order)]` | 1 | SELFTEST.automationOmega forward 1 |
| `Lean.Omega.Constraint.addInequality_sat [library theorem (Init.Omega.Constraint)]` | 1 | SELFTEST.automationOmega forward 1 |
| `Lean.Omega.Constraint.not_sat'_of_isImpossible [library theorem (Init.Omega.Constraint)]` | 1 | SELFTEST.automationOmega forward 1 |
| `Lean.Omega.Int.add_congr [library theorem (Init.Omega.Int)]` | 1 | SELFTEST.automationOmega forward 1 |
| `Lean.Omega.Int.ofNat_lt_of_lt [library theorem (Init.Omega.Int)]` | 1 | SELFTEST.automationOmega forward 1 |
| `Lean.Omega.Int.sub_congr [library theorem (Init.Omega.Int)]` | 1 | SELFTEST.automationOmega forward 1 |
| `Lean.Omega.LinearCombo.add_eval [library theorem (Init.Omega.LinearCombo)]` | 1 | SELFTEST.automationOmega forward 1 |
| `Lean.Omega.LinearCombo.coordinate_eval_0 [library theorem (Init.Omega.LinearCombo)]` | 1 | SELFTEST.automationOmega forward 1 |
| `Lean.Omega.LinearCombo.sub_eval [library theorem (Init.Omega.LinearCombo)]` | 1 | SELFTEST.automationOmega forward 1 |
| `Lean.Omega.tidy_sat [library theorem (Init.Omega.Constraint)]` | 1 | SELFTEST.automationOmega forward 1 |
| `Mathlib.Tactic.Ring.add_congr [library theorem (Mathlib.Tactic.Ring.Common)]` | 1 | SELFTEST.helperAutomation forward 1 |
| `Mathlib.Tactic.Ring.add_mul [library theorem (Mathlib.Tactic.Ring.Common)]` | 1 | SELFTEST.automationRing forward 1 |
| `Mathlib.Tactic.Ring.cast_pos [library theorem (Mathlib.Tactic.Ring.Common)]` | 1 | SELFTEST.automationRing forward 1 |
| `Mathlib.Tactic.Ring.cast_zero [library theorem (Mathlib.Tactic.Ring.Common)]` | 1 | SELFTEST.helperAutomation forward 1 |
| `Mathlib.Tactic.Ring.mul_add [library theorem (Mathlib.Tactic.Ring.Common)]` | 1 | SELFTEST.automationRing forward 1 |
| `Mathlib.Tactic.Ring.mul_congr [library theorem (Mathlib.Tactic.Ring.Common)]` | 1 | SELFTEST.automationRing forward 1 |
| `Mathlib.Tactic.Ring.mul_pf_right [library theorem (Mathlib.Tactic.Ring.Common)]` | 1 | SELFTEST.automationRing forward 1 |
| `Mathlib.Tactic.Ring.mul_zero [library theorem (Mathlib.Tactic.Ring.Common)]` | 1 | SELFTEST.automationRing forward 1 |
| `Mathlib.Tactic.Ring.one_mul [library theorem (Mathlib.Tactic.Ring.Common)]` | 1 | SELFTEST.automationRing forward 1 |
| `Mathlib.Tactic.Ring.zero_mul [library theorem (Mathlib.Tactic.Ring.Common)]` | 1 | SELFTEST.automationRing forward 1 |
| `NEP.NRxn.exists_not_ebAdmissible [implementation theorem used outside the hypothesis]` | 1 | SELFTEST.implInBackward backward |
| `NEP.Semiconj.diff [proof extracted from data (projection of NEP.Semiconj)]` | 1 | SELFTEST.proofField forward 1 |
| `Nat.cast_one [library theorem (Mathlib.Data.Nat.Cast.Defs)]` | 1 | SELFTEST.automationRing forward 1 |
| `Nat.cast_zero [library theorem (Mathlib.Data.Nat.Cast.Defs)]` | 1 | SELFTEST.helperAutomation forward 1 |
| `Nat.lt_of_not_le [library theorem (Init.Prelude)]` | 1 | SELFTEST.automationOmega forward 1 |
| `add_zero [library theorem (Mathlib.Algebra.Group.Defs)]` | 1 | SELFTEST.automationSimp forward 1 |
| `congrFun' [library theorem (Init.Prelude)]` | 1 | SELFTEST.automationSimp forward 1 |
| `eq_self [library theorem (Init.SimpLemmas)]` | 1 | SELFTEST.automationSimp forward 1 |
| `le_of_le_of_eq [library theorem (Init.Core)]` | 1 | SELFTEST.automationOmega forward 1 |
| `of_eq_true [library theorem (Init.SimpLemmas)]` | 1 | SELFTEST.automationSimp forward 1 |
| `sorryAx [forbidden constant]` | 1 | SELFTEST.sorryCheck forward 1 |

## Recorded failures (`sa_fail_*`)

| claim | target | reason | SHADOW? |
|---|---|---|---|
| `SELFTEST.recordedFail` | forward 1 | SHADOW?: the shadow speaks about φ_S, the implementation about the EB lift | yes |

## Warnings

* review record for `Alignment.Example.SelfTest.ForgedReview.bridge` in `Alignment.Example.SelfTest` ignored (only `Alignment.ReviewedBridges` counts)

Check statuses: `pass` (exact statement, structural, not vacuous), `fail` (wrong statement or recorded failure), `vacuous`, `audit_violation` (offenders listed), `sorry`, `missing`. Passes whose shadows were written after seeing the implementation are weak passes.
