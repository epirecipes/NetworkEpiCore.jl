# SA-PASS summary: NetworkEpiCore Lean library (`NetworkEpi`, namespace `NEP`)

Procedure: `../../../SA-PASS_SKILL.md` as adapted in `README.md`. The spec is the design statements quoted in the
theorem docstrings (from `DESIGN_NetworkEpiCore.md` §D, §J–§M), plus module header prose. Separate agents played
each role: registrar, blind shadow author, checker author, independent bridge reviewer, audit runner, adversarial
spot-checker, triage analyst and remediator. Reports: `report/sa_pass_report.{md,json}` and
`report/sa_selftest_report.md`.

## Numbers

| quantity | round 1 (before remediation) | round 2 (after one remediation round) |
|---|---|---|
| claims in registry | 275 | 275 |
| required (registered) claims | 192 | 194 |
| **SA-PASS = 1** | **108 (56.3%)** | **163 (84.0%)** |
| mean SA-PASS_soft | 0.685 | 0.88 |
| required failures | 84 | 31 |
| bridges reviewed / rejected | 20 / 0 | 25 / 0 |
| audit_violation / vacuous / sorry | 0 / 0 / 0 | 1 / 0 / 0 |
| CITABLE coverage gate (`scripts/sa_pass_citable.sh`) | fails (24/63) | fails (54/106) |

The Lean build passes, and so do the axiom gate (106 citable theorems; only `propext`, `Classical.choice` and
`Quot.sound`) and the harness self-test (49 claim, 9 bridge and 5 refuter expectations met).

## Spot check (adversarial reviewer, round 1)

All 108 round-1 passes were examined: **27 strong, 81 weak, 0 bogus**. About 14% of the required claims are
therefore substantive statements proved as stated.

- **The strong passes include the headline results:**
  - `NEP.rempala_general`: the Rempała quotient for every T_EB model.
  - `NEP.poisson_iso` and `NEP.poisson_iso_semiconj`.
  - `NEP.eb_to_pws`: EB → S-anchored pairwise, for every PGF.
  - `NEP.pt_iff_const_closure`: Poisson-type ⇔ constant closure.
  - `NEP.wellmixed_unit`.
  - `NEP.lift_append`, and the edge-defect and node-total derivative identities.
  - `NEP.exists_local_solution`.
  - the Dyn binary products.
- **Weak** passes hold by unfolding, or restate a definition.
- **No bypass was found.** All 20 bridges were checked against the definitions, and no passing claim has an
  unsatisfiable hypothesis or a trusted-free shadow.
- **Two shadows silently drop text:**
  - `SyntaxRxn.ebAdmissibleIffType`: T_net has 6 types, not 8.
  - `SemanticsMA.maLiftAppend`: the IB and stochastic semantics are not formalised.

**Caveat on round 2.** The 55 passes gained in round 2 have **not** been spot-checked.
- 8 of them are `identical_to_impl`.
- The remediator reports that some new theorems were written after seeing the shadows (`*_table`, the SEIR decimals,
  `rempala_seir_field`, `*_of_entries`). Under the skill these count as **weak passes**.

## Remediation round (what changed)

- About 45 new trusted theorems were added; nothing was weakened.
- Docstring "Scope" paragraphs were added, together with a DESIGN §M amendment.
- About 80 claims were re-registered and re-shadowed **blind**, and the registry was re-anchored.
- 43 names were added to `CITABLE.txt`.

## Remaining failures (round 2, 31 required)

| count | kind | claims |
|---|---|---|
| 3 | stale text | DynBasic claims; the texts must be re-anchored |
| 15 | unreviewed trusted-free shadows (22 shadows); pending independent review | 8 in MorphismsNGM, 4 in SemanticsEB, `clmListSum`/`clmListSumEq`, `contDiffAtPiSingle` |
| 7 | backward-only | `prodIsLimit`, `dynClosure`, `hasFDerivAtIncl`, `ebToPwsSolution`, `pwsDomainPoisson`, `poissonIsoSolution`, `rempalaSolution` |
| 5 | forward | `edgeDefectWithRemovals`, `wellmixedUnitIic`, `wellmixedUnitSolution`, `pwSGlueNotStrict`, `rempala` |
| 1 | audit_violation | `compactSolutionPoisson` (the guard budget ran out) |

The citable gate also fails: 24 superseded names are no claim's `impl`, and the claims of 28 names fail.

## Next steps

1. Spot-check the 55 round-2 passes.
2. Get an independent review of the 22 trusted-free shadows.
3. Re-anchor the 3 stale texts.
4. Remove the superseded names from `CITABLE.txt`, or register them.
5. Raise the guard budget for `compactSolutionPoisson`.

Vignettes should cite only names whose claims have SA-PASS = 1 **and** a strong spot-check verdict.

## Reproduce

```sh
cd NetworkEpiCore.jl/proofs
perl -e 'alarm 900; exec @ARGV' lake build && bash scripts/axiom_gate.sh
bash scripts/sa_pass.sh && bash scripts/sa_pass.sh --self-test
bash scripts/sa_pass_citable.sh      # release gate (currently fails, see above)
```


## Update: final polish round (2026-09-28)


## SA-PASS summary update (round 3: bridge/shadow review, DynBasic re-anchor, CITABLE pruning)

### Numbers

| quantity | round 1 | round 2 | **round 3 (now)** |
|---|---|---|---|
| claims in registry | 275 | 275 | 275 |
| required (registered) claims | 192 | 194 | 194 |
| **SA-PASS = 1** | 108 (56.3%) | 163 (84.0%) | **175 (90.2%)** |
| mean SA-PASS_soft | 0.685 | 0.88 | **0.958** |
| required failures | 84 | 31 | **19** |
| bridges reviewed / rejected | 20 / 0 | 25 / 0 | 25 / 0 |
| trusted-free shadows reviewed / unreviewed | 0 / 0 | 0 / 22 | **22 / 0** |
| audit_violation / vacuous / sorry | 0 / 0 / 0 | 1 / 0 / 0 | 1 / 0 / 0 |
| CITABLE.txt names (axiom gate) | 63 | 106 | **90** |
| CITABLE coverage gate | fails (24/63) | fails (54/106) | **fails (55/90)** |
| strong spot-check verdicts (cumulative) | 27 | 49 | **53** |
| **GOOD** (citable, SA-PASS = 1, strong) | – | – | **37 of 90** |

The Lean build passes. The axiom gate passes with 90 citable theorems, 1158 declarations in 19 trusted modules, and only `propext`, `Classical.choice` and `Quot.sound` as axioms; its self-test also passes. The harness self-test passes (49 claim, 9 bridge and 5 refuter expectations met). `--check-sources` reports no problems.

### Spot check (adversarial reviewer, round 2)

All 55 passes gained in round 2 were examined: **22 strong, 33 weak, 0 bogus**. The 55 are the diff between the round-1 report (108 passes) and the round-2 report (163 passes), and no round-1 pass was lost.

**How the remediator produced the round-2 theorems.** The remediator was not blind: it wrote or re-registered every one of the 55 impls after reading the round-1 shadows and failure reasons. They fall into four kinds:
- **G, genuine strengthenings.** For example `pt_constants_at_one`, `eb_to_pws_pt_any`, `compact_W_invariant_any`, `*_of_entries` and `xi_const_any`.
- **C, weaker corollaries (9).** These were added so that the backward check passes; the stronger theorem was kept.
- **F, form-only restatements in the shadow's syntax (19).**
- **V, `rfl` restatements of definitions (4).** These are `lift_eq_sum`, `ebSys_F_eq_sum`, `maSys_F_eq_sum` and `ebSys1_F`.

C, F and V passes add no alignment evidence beyond round 1, so they count as weak unless their content is substantive.

**Strong (22):**
- `ClosurePT.ptClosureAtOne`
- `MorphismsNGM.{multiplexR0, multiplexR0EqSumIff}`
- `SemanticsEB.{edgeDefectDerivEbField, nodeTotalDerivEbField, xiConst, conservation}`
- `MorphismsPairwise.{ebToPwsSir, ebToPwsSeir, ebToPwsPt, ebToPwsPoisson, pwsEbField}`
- `MorphismsRempala.rempalaGeneralSolution`
- `MorphismsPoisson.{poissonIsoSir, poissonIsoSeir, poissonEbField}`
- `MorphismsCommon.ebSys1Incl`
- `MorphismsCompact.{compactWInvariant, compactConj, compactSolution}`
- `MorphismsWellMixed.wmFieldEq`
- `SemanticsPoissonSIR.rempalaLift`

**Weak (33):** definitional unfoldings, projection or chain-rule lemmas, concrete computations, and form-only restatements. Among them are `SemanticsEB.hasDerivWithinAt{Theta,Xi,Phi,Pop}`, the `MorphismsRempala` apply/fderiv/projection lemmas and the `SemanticsSolutions` field-row equations.

**No bypass was found.** Every new impl uses only the three standard axioms. The bridges `XiConst.bridge_isExit`, `CompactConj.bridge_{emb,W}`, `CompactSolution.bridge_W` and `ConservationLocal(Poisson).bridge_isRemoval` were reviewed. No pass uses an unreviewed trusted-free shadow, and none has an unsatisfiable hypothesis. The report counts 9 new identical-to-impl shadows, not 8.

**Caveats:**
- **Two claim texts were narrowed by the remediator and need owner sign-off or a §M amendment:**
  - `SemanticsPoissonSIR.rempalaLift` now says "for μ ≠ 0".
  - `MorphismsCompact.compactSolution` now says "τ ≠ 0" and "q = 1 − ρ".
- The ψ'(1) ≠ 0 proviso added to `ClosurePT.ptClosureAtOne` is mathematically necessary.
- **Two claims have no independent spec.** The blind shadows of `SemanticsSolutions.conservationLocal` and `conservationLocalPoisson` took their hypotheses from header prose that paraphrases the Lean statement.

### Spot check (round 3: the 12 passes gained from the trusted-free shadow review)

**4 strong, 8 weak, 0 bogus.** All 12 rest on independently reviewed trusted-free shadows: the statements are Mathlib-level linear algebra or analysis, and there is no trusted constant.

- **Strong:**
  - `MorphismsNGM.spectralRadiusFinTwo`: the closed form ρ([[a,b],[c,d]]) = (a+d+√((a−d)²+4bc))/2 for a, d, bc ≥ 0, via `ENNReal.ofReal`, with a non-trivial proof.
  - `MorphismsNGM.spectrumFinTwo`: the full real spectrum when the discriminant is ≥ 0.
  - `MorphismsNGM.spectrumVecMulVecSubset`: spec(u vᵀ) ⊆ {0, v·u}, via a matrix-determinant-lemma argument.
  - `MorphismsNGM.spectralRadiusFinTwoEqTraceIff`: ρ = a + d ⇔ bc = ad.
- **Weak:**
  - `MorphismsNGM.memSpectrumIffDet`: a one-line `simp` over Mathlib.
  - `MorphismsNGM.memSpectrumVecMulVec`: a direct eigenvector check.
  - `SemanticsEB.sumSingle`, `SemanticsEB.constOfHasDerivWithinAtZero`, `SemanticsEB.constOfHasDerivAtZero`: Mathlib wrappers.
  - `MorphismsCommon.clmListSum`, `MorphismsCommon.clmListSumEq`: linearity over a list sum.
  - `SemanticsSolutions.contDiffAtPiSingle`: a `fun_prop` rule.
- Only `NEP.spectralRadius_fin_two` is citable, so it joins GOOD. The other three strong names are not in `CITABLE.txt`.

**Cumulative:** 53 of the 175 passes (27% of the 194 required claims) are substantive statements proved as stated.

### What changed in round 3

1. **DynBasic texts re-anchored.**
   - Cause: the Lean-statement paragraphs leaked into the registry texts of `mapSolution`, `mapSolutionOn` and `semiconjOnMapSolutionWithin`, and from there into `claims_blind.yaml`. I restored those texts to the convention.
   - `mapSolution` and `mapSolutionOn` now fail only their recorded backward check: the impl is pointwise on any set I, which is stronger than the shadows.
   - `semiconjOnMapSolutionWithin` changed substantively in the source, so it stays `text_mismatch` until the Checks owner updates its `sa_claim` text. It then needs blind re-shadowing.
   - I also re-anchored `Docs.citable.{pendingReview, gateConfiguration}`.
2. **CITABLE.txt went from 106 to 90 names.** I removed the 16 superseded names that nothing outside `proofs/` cites. I kept the 8 that vignettes still cite.
3. **compactSolutionPoisson budget: no fix.**
   - Raising normFuel tenfold still exhausted the budget after 5m16s.
   - A probe measured about 15k ticks/s, and one with fuel 1e8 ran for over 25 minutes.
   - I reverted `Audit.lean`. A real fix needs a change to the normaliser algorithm or a rewrite of fwd5.
4. **Trusted-free shadow review.** I added 22 `sa_shadow_reviewed` records to `ReviewedBridges.lean`, together with imports of `Checks.MorphismsNGM` and `Checks.MorphismsCommon`. All 22 were accepted and none rejected. As a result, 12 of the 15 affected claims now pass.

### Remaining failures (round 3, 19 required)

| count | kind | claims |
|---|---|---|
| 10 | backward only | `DynBasic.{mapSolution, mapSolutionOn}`, `DynProducts.{prodIsLimit, header.dynClosure}`, `MorphismsNGM.spectralRadiusVecMulVec`, `MorphismsPairwise.{ebToPwsSolution, pwsDomainPoisson}`, `MorphismsPoisson.poissonIsoSolution`, `MorphismsCommon.hasFDerivAtIncl`, `SemanticsPoissonSIR.rempalaSolution` |
| 6 | forward | `Docs.readme.edgeDefectWithRemovals`, `MorphismsNGM.r0SingleEntry` (fwd3, rank = 1), `SemanticsEB.hasDerivWithinAtCompClm` (fwd1, infinite σ), `MorphismsWellMixed.{wellmixedUnitIic, wellmixedUnitSolution}`, `SemanticsPWS.pwSGlueNotStrict` |
| 1 | forward and backward | `SemanticsPoissonSIR.rempala` |
| 1 | text_mismatch | `DynBasic.semiconjOnMapSolutionWithin` |
| 1 | audit_violation | `MorphismsCompact.compactSolutionPoisson` (normaliser budget) |

The citable gate still fails: 27 citable names have failing claims and 8 have no claim. The 8 are the superseded names that vignettes still cite: `pwS_glue_not_strict`, `poisson_iso_sir`, `eb_to_pws_sir`, `eb_to_pws_seir`, `eb_to_pws_pt`, `compact_conj`, `multiplex_r0` and `multiplex_r0_eq_sum_iff`.

### GOOD list: the names vignettes may cite

GOOD holds the 37 names on the first line: each is in `CITABLE.txt`, its claim has SA-PASS = 1, and a spot-check classified that claim as strong.

- Four GOOD names depend on the narrowed texts and need owner sign-off: `rempala_lift_xi`, `rempala_lift`, `compact_solution_ic` and `compact_solution_ic_at`. Without them, the stricter list has 33 names.
- Some GOOD names are secondary impls of a strong claim, not its headline theorem:
  - `ebField_map`, `lift_map` and `lift_glue` belong to `SemanticsEB.liftAppend`.
  - `NEP.conservation` belongs to `SemanticsEB.conservation`.
- Vignettes citing the 8 superseded names should switch to their GOOD replacements:

  | superseded | GOOD replacement |
  |---|---|
  | `eb_to_pws_sir` | `eb_to_pws_sir_global` |
  | `eb_to_pws_seir` | `eb_to_pws_seir_global` |
  | `eb_to_pws_pt` | `eb_to_pws_pt_any` |
  | `compact_conj` | `compact_conj_global` |
  | `poisson_iso_sir` | `poisson_iso_sir_iso` |
  | `multiplex_r0` | `multiplex_r0_of_entries` |
  | `multiplex_r0_eq_sum_iff` | `multiplex_r0_eq_sum_iff_of_entries` |
  | `pwS_glue_not_strict` | none yet: `pwS_glue_not_strict_all` does not pass |

### Next steps

1. Sign off or amend the two narrowed texts, `rempalaLift` and `compactSolution`.
2. Update the `sa_claim` text of `semiconjOnMapSolutionWithin`, then re-shadow it blind.
3. Fix the 10 backward-only failures. Most need the missing shadow clauses added: for example the spectrum clauses of `spectralRadiusVecMulVec`, and the any-set-I variants.
4. Fix the normaliser: memoise it, or stop it normalising motives, so that `compactSolutionPoisson` can be judged.
5. Move the vignettes off the 8 superseded names, then delete those names from `CITABLE.txt`.
6. Consider adding the strong names that are not yet citable (for example `xi_const_any`, `spectrum_fin_two`) to `CITABLE.txt`.

### Reproduce

```sh
cd NetworkEpiCore.jl/proofs
perl -e 'alarm 590; exec @ARGV' bash scripts/sa_pass.sh           # rc 0: 175/194, soft 0.9579, 19 failures
bash scripts/sa_pass.sh --self-test                                # rc 0
bash scripts/sa_pass.sh --no-build --check-sources                 # rc 0
bash scripts/axiom_gate.sh && bash scripts/axiom_gate.sh --self-test   # rc 0, 90 names
bash scripts/sa_pass_citable.sh                                    # rc 1 (release gate; coverage 55/90)
```

### Spot check of the 55 round-2 passes

Result: 22 strong, 33 weak, 0 bogus. Every one of these implementation theorems was written or re-registered by the non-blind remediator after it had seen the shadows. 19 are form-only restatements, 9 are weaker corollaries, and 4 depend on `rfl` theorems. Full table: `_session_artifacts/polish_results.json` (key `lean:spot-check`).

## Round 4: final remediation (2026-09-28)

The roles were again kept separate: a non-blind remediator, a blind shadow author (2 claims whose text changed), a
checker author (18 claims), and orchestrator verification.

| quantity | value |
|---|---|
| required claims at SA-PASS = 1 | **194 / 194**, mean soft 1.0, 0 required failures |
| checks | 637, all pass; 0 fail records, 0 audit violations |
| bridges / trusted-free shadows reviewed | 25 / 22 |
| citable coverage gate (`scripts/sa_pass_citable.sh`) | **passes**: 89/89 names covered (exit 0, rerun independently) |
| axiom gate | passes (only `propext`, `Classical.choice`, `Quot.sound`) |
| harness self-test | passes (50 claim, 9 bridge, 5 refuter expectations) |

What changed:
- **CITABLE.txt:** the 8 superseded names were removed; so were 10 names more general than their claim text, each
  replaced by its exact-statement theorem; 16 new names were added (DESIGN §M.9).
- **New trusted theorems:** 18 exact-statement corollaries or strengthenings. Nothing was weakened, and no `sorry`
  was introduced.
- **Audit tool:** the `Audit.lean` normaliser is now memoised, without changing any rule, so `compactSolutionPoisson`
  is judged instead of running out of budget. A new self-test mock checks that nested destructuring is still caught.
- **Text changes:** two claim texts changed and were re-shadowed blind: `DynBasic.semiconjOnMapSolutionWithin`
  (arbitrary set of times `I`) and `MorphismsPoisson.poissonIsoSolution` (both within-`I` and two-sided solutions).
- **Citations:** the NEC docs and README, and the NBM `docs/validation.md`, now cite only passing names.

**How to read 194/194 honestly.** The skill counts a pass as *weak* when its shadows were written or its theorems
added after the implementation had been seen.
- **Rounds 1–4 are all affected.** The 19 claims newly passing in round 4, like the 55 of round 2, rest on theorems
  that the non-blind remediator wrote after reading the shadows. Most are form-only restatements, exact-statement
  corollaries, or `_global`/`_open`/`_of_dyn` specialisations.
- **They are weak passes.** They show the Lean statements now match the text, but they add little independent
  evidence.
- **The substantive core** is the claims classified *strong* by the adversarial spot-checks:
  - round 1: 27;
  - round 2: 22;
  - round 3: `spectralRadius_fin_two`.

  These include the Rempała quotient for every T_EB model, the Poisson isomorphism, EB → pairwise for every PGF,
  Poisson-type ⇔ constant closure, the well-mixed unit, and the lift laws.
- **Vignettes cite only strong names.**
- **Recommendation:** an independent spot-check of the round-4 passes. A further blind re-shadowing of the claims
  whose shadows were written in the DynBasic leak window (see the round-3 notes) would also make those passes
  independent again.
