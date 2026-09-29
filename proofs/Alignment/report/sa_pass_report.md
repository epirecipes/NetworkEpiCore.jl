# SA-PASS report (NetworkEpi)

Generated 2026-09-28 18:52 from `Alignment/report/sa_pass_audit.json` (Lean 4.29.0-rc4) and `Alignment/claims.yaml`.

Trusted modules loaded by the audit: `NetworkEpi`, `NetworkEpi.Closure.PT`, `NetworkEpi.Dyn.Basic`, `NetworkEpi.Dyn.Products`, `NetworkEpi.Morphisms.All`, `NetworkEpi.Morphisms.Common`, `NetworkEpi.Morphisms.Compact`, `NetworkEpi.Morphisms.NGM`, `NetworkEpi.Morphisms.Pairwise`, `NetworkEpi.Morphisms.Poisson`, `NetworkEpi.Morphisms.Rempala`, `NetworkEpi.Morphisms.Stoich`, `NetworkEpi.Morphisms.WellMixed`, `NetworkEpi.Semantics.EB`, `NetworkEpi.Semantics.MA`, `NetworkEpi.Semantics.PWS`, `NetworkEpi.Semantics.PoissonSIR`, `NetworkEpi.Semantics.Solutions`, `NetworkEpi.Syntax.Rxn`

Tool sanity: 3/3 worked-example claims (`EXAMPLE.*`) pass every check (run `bash scripts/sa_pass.sh --self-test` for the full self-test).

## Summary

| quantity | value |
|---|---|
| claims in registry | 275 |
| claims registered in Lean | 194 |
| registry claims not registered in Lean | 81 |
| required claims (status implemented) | 194 |
| SA-PASS = 1 (all / required) | 194 / 194 |
| mean SA-PASS_soft (registered claims) | 1.0 |
| required failures | 0 |
| check statuses | pass: 637 |
| bridges | reviewed: 25 |
| hints (not scored) | backward_guard_unnormalised: 1, backward_unused_shadows: 20 |
| trusted-free shadows (by review status) | reviewed: 22 |
| claims with a refuted implementation hypothesis | 0 |

## Per group

| group | registry | registered | required | SA-PASS=1 | mean soft | forward pass | backward pass | required failures |
|---|---|---|---|---|---|---|---|---|
| ClosurePT | 7 | 5 | 5 | 5 | 1.0 | 10/10 | 5/5 | 0 |
| Docs | 31 | 1 | 1 | 1 | 1.0 | 5/5 | 1/1 | 0 |
| DynBasic | 17 | 11 | 11 | 11 | 1.0 | 18/18 | 11/11 | 0 |
| DynProducts | 8 | 5 | 5 | 5 | 1.0 | 18/18 | 5/5 | 0 |
| MorphismsCommon | 21 | 20 | 20 | 20 | 1.0 | 40/40 | 20/20 | 0 |
| MorphismsCompact | 8 | 7 | 7 | 7 | 1.0 | 20/20 | 7/7 | 0 |
| MorphismsNGM | 12 | 10 | 10 | 10 | 1.0 | 17/17 | 10/10 | 0 |
| MorphismsPairwise | 13 | 10 | 10 | 10 | 1.0 | 20/20 | 10/10 | 0 |
| MorphismsPoisson | 17 | 15 | 15 | 15 | 1.0 | 30/30 | 15/15 | 0 |
| MorphismsRempala | 17 | 15 | 15 | 15 | 1.0 | 31/31 | 15/15 | 0 |
| MorphismsStoich | 6 | 5 | 5 | 5 | 1.0 | 16/16 | 5/5 | 0 |
| MorphismsWellMixed | 12 | 10 | 10 | 10 | 1.0 | 30/30 | 10/10 | 0 |
| SemanticsEB | 43 | 34 | 34 | 34 | 1.0 | 59/59 | 34/34 | 0 |
| SemanticsMA | 6 | 5 | 5 | 5 | 1.0 | 13/13 | 5/5 | 0 |
| SemanticsPWS | 7 | 4 | 4 | 4 | 1.0 | 9/9 | 4/4 | 0 |
| SemanticsPoissonSIR | 11 | 9 | 9 | 9 | 1.0 | 23/23 | 9/9 | 0 |
| SemanticsSolutions | 15 | 12 | 12 | 12 | 1.0 | 33/33 | 12/12 | 0 |
| SyntaxRxn | 24 | 16 | 16 | 16 | 1.0 | 51/51 | 16/16 | 0 |

## Claims

| id | req | n | forward | backward | SA-PASS | soft | flags |
|---|---|---|---|---|---|---|---|
| `ClosurePT.hasDerivWithinAtPtQuotient` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `ClosurePT.poissonClosureK` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `ClosurePT.ptClosureAtOne` | yes | 3 | pass pass pass | pass | 1 | 1.0 |  |
| `ClosurePT.ptIffClosureK` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `ClosurePT.ptIffConstClosure` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `Docs.readme.edgeDefectWithRemovals` | yes | 5 | pass pass pass pass pass | pass | 1 | 1.0 |  |
| `DynBasic.compPi` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `DynBasic.hasFDerivAtRestrictIncl` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `DynBasic.homEqSemiconj` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `DynBasic.idPi` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `DynBasic.invariantIncl` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `DynBasic.mapSolution` | yes | 5 | pass pass pass pass pass | pass | 1 | 1.0 |  |
| `DynBasic.mapSolutionOn` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `DynBasic.semiconjIsSemiconj` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `DynBasic.semiconjMapSolutionWithin` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `DynBasic.semiconjOnIsSemiconjOn` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `DynBasic.semiconjOnMapSolutionWithin` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `DynProducts.header.dynClosure` | yes | 10 | pass pass pass pass pass pass pass pass pass pass | pass | 1 | 1.0 |  |
| `DynProducts.instHasLimitPair` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `DynProducts.pointEq` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [1]) |
| `DynProducts.pointIsTerminal` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `DynProducts.prodIsLimit` | yes | 5 | pass pass pass pass pass | pass | 1 | 1.0 |  (hints: backward_unused_shadows) |
| `MorphismsCommon.clmListSum` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `MorphismsCommon.clmListSumEq` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `MorphismsCommon.dropIncl` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `MorphismsCommon.dropLApply` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `MorphismsCommon.ebCoordinateApply` | yes | 4 | pass pass pass pass | pass | 1 | 1.0 |  |
| `MorphismsCommon.ebSys1Drop` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `MorphismsCommon.ebSys1Incl` | yes | 3 | pass pass pass | pass | 1 | 1.0 |  |
| `MorphismsCommon.hasFDerivAtEbCoordinates` | yes | 8 | pass pass pass pass pass pass pass pass | pass | 1 | 1.0 |  (hints: backward_unused_shadows) |
| `MorphismsCommon.hasFDerivAtIncl` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `MorphismsCommon.hasFDerivAtSusc` | yes | 2 | pass pass | pass | 1 | 1.0 |  (hints: backward_unused_shadows) |
| `MorphismsCommon.header.ebSys1` | yes | 3 | pass pass pass | pass | 1 | 1.0 |  (hints: backward_unused_shadows) |
| `MorphismsCommon.header.perReactionCriterion` | yes | 3 | pass pass pass | pass | 1 | 1.0 |  |
| `MorphismsCommon.inclDrop` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `MorphismsCommon.inclLApply` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `MorphismsCommon.isConjOnOfInverse` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `MorphismsCommon.isSemiconjOfHasFDerivAt` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `MorphismsCommon.isSemiconjOnInverse` | yes | 2 | pass pass | pass | 1 | 1.0 |  (hints: backward_unused_shadows) |
| `MorphismsCommon.isSemiconjOnOfHasFDerivAt` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) (hints: backward_unused_shadows) |
| `MorphismsCommon.maLiftFlatMap` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `MorphismsCommon.suscDApply` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `MorphismsCompact.compactConj` | yes | 5 | pass pass pass pass pass | pass | 1 | 1.0 |  |
| `MorphismsCompact.compactEmbSemiconj` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `MorphismsCompact.compactSolution` | yes | 4 | pass pass pass pass | pass | 1 | 1.0 |  |
| `MorphismsCompact.compactSolutionPoisson` | yes | 5 | pass pass pass pass pass | pass | 1 | 1.0 |  |
| `MorphismsCompact.compactWInvariant` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `MorphismsCompact.hasFDerivAtCompactEmb` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `MorphismsCompact.sirVecApply` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [0]) |
| `MorphismsNGM.memSpectrumIffDet` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `MorphismsNGM.memSpectrumVecMulVec` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `MorphismsNGM.multiplexR0` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `MorphismsNGM.multiplexR0EqSumIff` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [0]) |
| `MorphismsNGM.r0SingleEntry` | yes | 4 | pass pass pass pass | pass | 1 | 1.0 |  |
| `MorphismsNGM.spectralRadiusFinTwo` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `MorphismsNGM.spectralRadiusFinTwoEqTraceIff` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [0]) |
| `MorphismsNGM.spectralRadiusVecMulVec` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `MorphismsNGM.spectrumFinTwo` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `MorphismsNGM.spectrumVecMulVecSubset` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `MorphismsPairwise.ebToPws` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `MorphismsPairwise.ebToPwsConst` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `MorphismsPairwise.ebToPwsPoisson` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `MorphismsPairwise.ebToPwsPt` | yes | 3 | pass pass pass | pass | 1 | 1.0 |  |
| `MorphismsPairwise.ebToPwsSeir` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `MorphismsPairwise.ebToPwsSir` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `MorphismsPairwise.ebToPwsSolution` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `MorphismsPairwise.hasFDerivAtPwImage` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `MorphismsPairwise.pwsDomainPoisson` | yes | 3 | pass pass pass | pass | 1 | 1.0 |  (identical to impl: [0]) |
| `MorphismsPairwise.pwsEbField` | yes | 3 | pass pass pass | pass | 1 | 1.0 |  (identical to impl: [0]) |
| `MorphismsPoisson.hasFDerivAtPoissonMap` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `MorphismsPoisson.poissonDLInl` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `MorphismsPoisson.poissonDLInr` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `MorphismsPoisson.poissonDLNone` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `MorphismsPoisson.poissonDSirField` | yes | 5 | pass pass pass pass pass | pass | 1 | 1.0 |  |
| `MorphismsPoisson.poissonEbField` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `MorphismsPoisson.poissonIso` | yes | 5 | pass pass pass pass pass | pass | 1 | 1.0 |  |
| `MorphismsPoisson.poissonIsoNatural` | yes | 3 | pass pass pass | pass | 1 | 1.0 |  |
| `MorphismsPoisson.poissonIsoSeir` | yes | 3 | pass pass pass | pass | 1 | 1.0 |  |
| `MorphismsPoisson.poissonIsoSemiconj` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `MorphismsPoisson.poissonIsoSir` | yes | 3 | pass pass pass | pass | 1 | 1.0 |  |
| `MorphismsPoisson.poissonIsoSolution` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `MorphismsPoisson.rxnPoissonDMap` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `MorphismsPoisson.seirRxnsNoExit` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `MorphismsPoisson.sirRxnsNoExit` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `MorphismsRempala.hasFDerivAtRempalaMap` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `MorphismsRempala.rempalaDApply` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `MorphismsRempala.rempalaDSurjective` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `MorphismsRempala.rempalaEbField` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `MorphismsRempala.rempalaGeneral` | yes | 2 | pass pass | pass | 1 | 1.0 |  (hints: backward_unused_shadows) |
| `MorphismsRempala.rempalaGeneralSir` | yes | 2 | pass pass | pass | 1 | 1.0 |  (hints: backward_unused_shadows) |
| `MorphismsRempala.rempalaGeneralSolution` | yes | 4 | pass pass pass pass | pass | 1 | 1.0 |  (hints: backward_unused_shadows) |
| `MorphismsRempala.rempalaMapPull` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `MorphismsRempala.rempalaMapPush` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `MorphismsRempala.rempalaMapSurjective` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `MorphismsRempala.rempalaNatural` | yes | 3 | pass pass pass | pass | 1 | 1.0 |  |
| `MorphismsRempala.rempalaQuotient` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `MorphismsRempala.rempalaSeirField` | yes | 4 | pass pass pass pass | pass | 1 | 1.0 |  |
| `MorphismsRempala.rempalaSirProj` | yes | 4 | pass pass pass pass | pass | 1 | 1.0 |  (hints: backward_unused_shadows) |
| `MorphismsRempala.rxnRempalaMap` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `MorphismsStoich.maEqStoich` | yes | 7 | pass pass pass pass pass pass pass | pass | 1 | 1.0 |  |
| `MorphismsStoich.maFieldToSRxn` | yes | 6 | pass pass pass pass pass pass | pass | 1 | 1.0 |  |
| `MorphismsStoich.maToSLApply` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `MorphismsStoich.sLiftAppend` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `MorphismsStoich.sLiftFlatMap` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `MorphismsWellMixed.hasFDerivAtWmMap` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `MorphismsWellMixed.wellmixedUnit` | yes | 7 | pass pass pass pass pass pass pass | pass | 1 | 1.0 |  |
| `MorphismsWellMixed.wellmixedUnitIic` | yes | 3 | pass pass pass | pass | 1 | 1.0 |  |
| `MorphismsWellMixed.wellmixedUnitQuotient` | yes | 3 | pass pass pass | pass | 1 | 1.0 |  |
| `MorphismsWellMixed.wellmixedUnitSemiconj` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `MorphismsWellMixed.wellmixedUnitSolution` | yes | 6 | pass pass pass pass pass pass | pass | 1 | 1.0 |  |
| `MorphismsWellMixed.wmDApply` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [0]) |
| `MorphismsWellMixed.wmFieldEq` | yes | 4 | pass pass pass pass | pass | 1 | 1.0 |  (identical to impl: [0]) |
| `MorphismsWellMixed.wmLiftXiEqZero` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `MorphismsWellMixed.wmSys1Incl` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `SemanticsEB.conservation` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `SemanticsEB.constOfHasDerivAtZero` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `SemanticsEB.constOfHasDerivWithinAtZero` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `SemanticsEB.edgeDefectDerivAdd` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `SemanticsEB.edgeDefectDerivEbField` | yes | 3 | pass pass pass | pass | 1 | 1.0 |  |
| `SemanticsEB.edgeDefectDerivLift` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `SemanticsEB.hasDerivAtEdgeDefectLift` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `SemanticsEB.hasDerivAtNodeTotalLift` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `SemanticsEB.hasDerivWithinAtCompClm` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `SemanticsEB.hasDerivWithinAtEdgeDefect` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `SemanticsEB.hasDerivWithinAtEdgeDefectLift` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `SemanticsEB.hasDerivWithinAtNodeTotal` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `SemanticsEB.hasDerivWithinAtNodeTotalLift` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `SemanticsEB.hasDerivWithinAtPhi` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `SemanticsEB.hasDerivWithinAtPop` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `SemanticsEB.hasDerivWithinAtTheta` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `SemanticsEB.hasDerivWithinAtXi` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `SemanticsEB.header.fieldTable` | yes | 17 | pass pass pass pass pass pass pass pass pass pass pass pass pass pass pass pass pass | pass | 1 | 1.0 |  (hints: backward_unused_shadows) |
| `SemanticsEB.liftAppend` | yes | 4 | pass pass pass pass | pass | 1 | 1.0 |  |
| `SemanticsEB.liftXiEqZero` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `SemanticsEB.nodeConservation` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `SemanticsEB.nodeTotalDerivAdd` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `SemanticsEB.nodeTotalDerivEbField` | yes | 3 | pass pass pass | pass | 1 | 1.0 |  |
| `SemanticsEB.nodeTotalDerivLift` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `SemanticsEB.pushAdd` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `SemanticsEB.pushEBAdd` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `SemanticsEB.pushEBZero` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `SemanticsEB.pushNeg` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `SemanticsEB.pushSingle` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `SemanticsEB.pushSub` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `SemanticsEB.pushZero` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `SemanticsEB.removalFluxEqZero` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `SemanticsEB.sumSingle` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `SemanticsEB.xiConst` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `SemanticsMA.elimMap` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `SemanticsMA.maFieldMap` | yes | 6 | pass pass pass pass pass pass | pass | 1 | 1.0 |  |
| `SemanticsMA.maLiftAppend` | yes | 3 | pass pass pass | pass | 1 | 1.0 |  |
| `SemanticsMA.pushMAAdd` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `SemanticsMA.pushMAZero` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `SemanticsPWS.f2GluedSV` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `SemanticsPWS.f2SumSV` | yes | 2 | pass pass | pass | 1 | 1.0 |  (hints: backward_unused_shadows) |
| `SemanticsPWS.pwSGlueNotStrict` | yes | 2 | pass pass | pass | 1 | 1.0 |  (hints: backward_guard_unnormalised, backward_unused_shadows) |
| `SemanticsPWS.pwSLiftAppend` | yes | 4 | pass pass pass pass | pass | 1 | 1.0 |  (identical to impl: [0]) |
| `SemanticsPoissonSIR.contDiffPoisMap` | yes | 4 | pass pass pass pass | pass | 1 | 1.0 |  |
| `SemanticsPoissonSIR.ebPoisSIRLift` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `SemanticsPoissonSIR.hasFDerivAtPoisMap` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `SemanticsPoissonSIR.poissonHasDerivAtPsi` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `SemanticsPoissonSIR.poissonHasDerivAtPsiPrime` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `SemanticsPoissonSIR.rempala` | yes | 6 | pass pass pass pass pass pass | pass | 1 | 1.0 |  |
| `SemanticsPoissonSIR.rempalaLift` | yes | 4 | pass pass pass pass | pass | 1 | 1.0 |  |
| `SemanticsPoissonSIR.rempalaSolution` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `SemanticsPoissonSIR.sirChartLApply` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [0]) |
| `SemanticsSolutions.conservationLocal` | yes | 2 | pass pass | pass | 1 | 1.0 |  (hints: backward_unused_shadows) |
| `SemanticsSolutions.conservationLocalPoisson` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `SemanticsSolutions.contDiffAtEbField` | yes | 6 | pass pass pass pass pass pass | pass | 1 | 1.0 |  |
| `SemanticsSolutions.contDiffAtLift` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `SemanticsSolutions.contDiffAtPiSingle` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `SemanticsSolutions.contDiffLift` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `SemanticsSolutions.ebFieldContactEq` | yes | 4 | pass pass pass pass | pass | 1 | 1.0 |  |
| `SemanticsSolutions.ebFieldExitEq` | yes | 4 | pass pass pass pass | pass | 1 | 1.0 |  |
| `SemanticsSolutions.ebFieldProgressEq` | yes | 4 | pass pass pass pass | pass | 1 | 1.0 |  |
| `SemanticsSolutions.ebFieldRemoveEq` | yes | 4 | pass pass pass pass | pass | 1 | 1.0 |  |
| `SemanticsSolutions.existsLocalSolution` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `SemanticsSolutions.seirConservationLocal` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `SyntaxRxn.ebAdmissibleIff` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `SyntaxRxn.ebAdmissibleIffType` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `SyntaxRxn.ebAdmissibleMap` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [0]) |
| `SyntaxRxn.eqToNRxnOfEbAdmissible` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `SyntaxRxn.existsNotEbAdmissible` | yes | 2 | pass pass | pass | 1 | 1.0 |  (hints: backward_unused_shadows) |
| `SyntaxRxn.nRxnMapId` | yes | 5 | pass pass pass pass pass | pass | 1 | 1.0 |  (identical to impl: [0]) |
| `SyntaxRxn.nRxnMapMap` | yes | 6 | pass pass pass pass pass pass | pass | 1 | 1.0 |  (identical to impl: [0]) |
| `SyntaxRxn.notEbAdmissibleNodeContact` | yes | 3 | pass pass pass | pass | 1 | 1.0 |  (hints: backward_unused_shadows) |
| `SyntaxRxn.notEbAdmissibleResus` | yes | 3 | pass pass pass | pass | 1 | 1.0 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `SyntaxRxn.rxnMapId` | yes | 3 | pass pass pass | pass | 1 | 1.0 |  (identical to impl: [0]) |
| `SyntaxRxn.rxnMapMap` | yes | 3 | pass pass pass | pass | 1 | 1.0 |  (identical to impl: [0]) |
| `SyntaxRxn.scaleContactsMap` | yes | 3 | pass pass pass | pass | 1 | 1.0 |  |
| `SyntaxRxn.toNRxnInjective` | yes | 3 | pass pass pass | pass | 1 | 1.0 |  (identical to impl: [0]) |
| `SyntaxRxn.toNRxnMap` | yes | 3 | pass pass pass | pass | 1 | 1.0 |  (identical to impl: [0]) |
| `SyntaxRxn.toRxnToNRxn` | yes | 3 | pass pass pass | pass | 1 | 1.0 |  (identical to impl: [0]) |
| `SyntaxRxn.typeMap` | yes | 7 | pass pass pass pass pass pass pass | pass | 1 | 1.0 |  (hints: backward_unused_shadows) |

## Registry claims without a Lean registration

| id | group | required | status | impl | registry problems |
|---|---|---|---|---|---|
| `ClosurePT.header.intervals` | ClosurePT | no | informal |  |  |
| `ClosurePT.ptOnlyExactConstant` | ClosurePT | no | missing |  |  |
| `Docs.all.aggregator` | Docs | no | informal |  |  |
| `Docs.all.moduleTable` | Docs | no | informal |  |  |
| `Docs.citable.gateConfiguration` | Docs | no | informal |  |  |
| `Docs.citable.pendingReview` | Docs | no | informal |  |  |
| `Docs.readme.admissibilityMeta` | Docs | no | informal |  |  |
| `Docs.readme.citableDocstrings` | Docs | no | informal |  |  |
| `Docs.readme.conservationRemovalFreeOnly` | Docs | no | missing |  |  |
| `Docs.readme.contDiffLift` | Docs | no | informal |  |  |
| `Docs.readme.contents.dynBasic` | Docs | no | informal |  |  |
| `Docs.readme.contents.dynProducts` | Docs | no | informal |  |  |
| `Docs.readme.contents.morphisms` | Docs | no | informal |  |  |
| `Docs.readme.contents.semanticsEB` | Docs | no | informal |  |  |
| `Docs.readme.contents.semanticsMA` | Docs | no | informal |  |  |
| `Docs.readme.contents.semanticsPWS` | Docs | no | informal |  |  |
| `Docs.readme.contents.semanticsPoissonSIR` | Docs | no | informal |  |  |
| `Docs.readme.contents.semanticsSolutions` | Docs | no | informal |  |  |
| `Docs.readme.contents.syntaxRxn` | Docs | no | informal |  |  |
| `Docs.readme.dynClosedUnderProducts` | Docs | no | missing |  |  |
| `Docs.readme.dynGeneralisation` | Docs | no | informal |  |  |
| `Docs.readme.hypothesesMet` | Docs | no | informal |  |  |
| `Docs.readme.liftLawsArbitraryPsi` | Docs | no | informal |  |  |
| `Docs.readme.rempalaSirCase` | Docs | no | informal |  |  |
| `Docs.readme.seirNoGlobalSolution` | Docs | no | missing |  |  |
| `Docs.readme.sinkSpecies` | Docs | no | missing |  |  |
| `Docs.readme.syntaxScope` | Docs | no | informal |  |  |
| `Docs.readme.timeIntervalSolutions` | Docs | no | informal |  |  |
| `Docs.readme.trustedLibrary` | Docs | no | informal |  |  |
| `Docs.root.moduleTableWP13` | Docs | no | informal |  |  |
| `Docs.root.moduleTableWP28` | Docs | no | informal |  |  |
| `Docs.root.trustedLibrary` | Docs | no | informal |  |  |
| `DynBasic.header.dynDesign` | DynBasic | no | informal |  |  |
| `DynBasic.header.dynSubcategory` | DynBasic | no | missing |  |  |
| `DynBasic.header.dynSysGeneral` | DynBasic | no | informal |  |  |
| `DynBasic.header.globalSolutions` | DynBasic | no | missing |  |  |
| `DynBasic.header.solutionDefs` | DynBasic | no | informal |  |  |
| `DynBasic.header.withinWeaker` | DynBasic | no | informal |  |  |
| `DynProducts.header.construction` | DynProducts | no | informal |  |  |
| `DynProducts.header.notFull` | DynProducts | no | missing |  |  |
| `DynProducts.prodFanIsLimit` | DynProducts | no | informal |  |  |
| `MorphismsCommon.isConjOn` | MorphismsCommon | no | missing |  |  |
| `MorphismsCompact.header.models` | MorphismsCompact | no | informal |  |  |
| `MorphismsNGM.header.ngmDerivation` | MorphismsNGM | no | missing |  |  |
| `MorphismsNGM.header.r0Definition` | MorphismsNGM | no | informal |  |  |
| `MorphismsPairwise.constClosureOnlyIf` | MorphismsPairwise | no | missing |  |  |
| `MorphismsPairwise.header.notFreeScalar` | MorphismsPairwise | no | informal |  |  |
| `MorphismsPairwise.header.target` | MorphismsPairwise | no | informal |  |  |
| `MorphismsPoisson.header.construction` | MorphismsPoisson | no | informal |  |  |
| `MorphismsPoisson.header.exitsNotConjugacy` | MorphismsPoisson | no | missing |  |  |
| `MorphismsRempala.header.construction` | MorphismsRempala | no | informal |  |  |
| `MorphismsRempala.rempalaSeirConsequence` | MorphismsRempala | no | informal |  |  |
| `MorphismsStoich.header.multisetMassAction` | MorphismsStoich | no | informal |  |  |
| `MorphismsWellMixed.header.model` | MorphismsWellMixed | no | informal |  |  |
| `MorphismsWellMixed.wellmixedUnitNaturality` | MorphismsWellMixed | no | missing |  |  |
| `SemanticsEB.conservation.b` | SemanticsEB | no | missing |  |  |
| `SemanticsEB.conservation.c` | SemanticsEB | no | informal |  |  |
| `SemanticsEB.header.coordinates` | SemanticsEB | no | informal |  |  |
| `SemanticsEB.header.degreeDataHypotheses` | SemanticsEB | no | informal |  |  |
| `SemanticsEB.header.forwardSolutions` | SemanticsEB | no | missing |  |  |
| `SemanticsEB.header.globalSolutions` | SemanticsEB | no | missing |  |  |
| `SemanticsEB.header.localSolutions` | SemanticsEB | no | informal |  |  |
| `SemanticsEB.header.observables` | SemanticsEB | no | informal |  |  |
| `SemanticsEB.header.solutionsOnInterval` | SemanticsEB | no | informal |  |  |
| `SemanticsMA.header.scope` | SemanticsMA | no | informal |  |  |
| `SemanticsPWS.header.closureKpsi` | SemanticsPWS | no | informal |  |  |
| `SemanticsPWS.header.designRow` | SemanticsPWS | no | informal |  |  |
| `SemanticsPWS.header.fieldTable` | SemanticsPWS | no | missing |  |  |
| `SemanticsPoissonSIR.header.designRow` | SemanticsPoissonSIR | no | informal |  |  |
| `SemanticsPoissonSIR.header.portScope` | SemanticsPoissonSIR | no | informal |  |  |
| `SemanticsSolutions.header.bullets` | SemanticsSolutions | no | informal |  |  |
| `SemanticsSolutions.header.hypothesesMet` | SemanticsSolutions | no | missing |  |  |
| `SemanticsSolutions.seirConservationLocal.b` | SemanticsSolutions | no | missing |  |  |
| `SyntaxRxn.decEBAdmissible` | SyntaxRxn | no | informal |  |  |
| `SyntaxRxn.header.admissibilityScope` | SyntaxRxn | no | informal |  |  |
| `SyntaxRxn.header.decidabilityExamples` | SyntaxRxn | no | missing |  |  |
| `SyntaxRxn.header.exitsToEmpty` | SyntaxRxn | no | informal |  |  |
| `SyntaxRxn.header.inertSink` | SyntaxRxn | no | missing |  |  |
| `SyntaxRxn.header.sisReason` | SyntaxRxn | no | missing |  |  |
| `SyntaxRxn.header.tebTnet` | SyntaxRxn | no | informal |  |  |
| `SyntaxRxn.header.typingTable` | SyntaxRxn | no | informal |  |  |

## Required failures

None.

## Bridges

| bridge | claims | status | hash | statement | notes |
|---|---|---|---|---|---|
| `Alignment.Shadows.Docs.EdgeDefectWithRemovals.bridge_isRemoval` | Docs.readme.edgeDefectWithRemovals | reviewed | `5031884031455682599` | `∀ {σ : Type} (r : NEP.Rxn σ), r.isRemoval = true ↔ ∃ X a, r = NEP.Rxn.trans X none a` | The LHS is the trusted Boolean test NEP.Rxn.isRemoval (NetworkEpi/Semantics/EB.lean:283): true on `.trans _ none _`, false otherwise. The RHS ∃ X a, r = Rxn.trans X none a is exactly the text's 'removal X → ∅' (Rxn docstring: trans X none a is X → ∅ at rate a); contact, exit and trans X (some Y) a are not removals. No rate condition, no species excluded; syntactic characterisation carrying none of the content of removalFlux_eq_zero, removalFlux_nonneg or the balance law. Proof isRemoval_iff_aux (Checks/Docs.lean:61) is cases+simp with standard axioms only. Same statement and hash as the reviewed SemanticsEB.RemovalFluxEqZero.bridge_isRemoval. In fwd5 it only converts S5's 'no trans X none a ∈ rs' into ∀ r ∈ rs, r.isRemoval = false. |
| `Alignment.Shadows.MorphismsCompact.CompactConj.bridge_W` | MorphismsCompact.compactConj | reviewed | `13424280360243047731` | `∀ (N : NEP.CNet) (q τ γ : ℝ), NEP.compactW N q τ γ = Alignment.Shadows.MorphismsCompact.Wp N q τ γ` | The trusted NEP.compactW (Compact.lean:70) is {u \| ξ = 1 ∧ τφ_R + γθ = γ ∧ θ = phiS q θ ξ + φ_I + φ_R ∧ susc q θ ξ + pop_I + pop_R = 1}. The RHS Wp is the text's W' = W ∩ {ξ = 1, θ = φ_S + φ_I + φ_R, S + pop_I + pop_R = 1}, with W = {τφ_R + γθ = γ} and φ_S = qξψ'(θ)/ψ'(1), S = qξψ(θ) written in primitives. That is the correct reading of DESIGN §0, where φ_S and S depend on the state's ξ, not on a fixed 1. Both sides have exactly the same four conditions: phiS and susc unfold to the same expressions, and only the first two conjuncts are swapped. No conditions are added or dropped, and no domain restriction is hidden. The RHS is a set built from the bound variables, with no closed or theorem content. The proof is ext / simp only unfolding / conjunct reorder, and it uses no impl theorem. The audit reports it as valid and unreviewed. |
| `Alignment.Shadows.MorphismsCompact.CompactConj.bridge_emb` | MorphismsCompact.compactConj | reviewed | `8726521545807369653` | `∀ (N : NEP.CNet) (q τ γ : ℝ) (w : ℝ × ℝ), NEP.compactEmb N q τ γ w = Alignment.Shadows.MorphismsCompact.emb N q τ γ w` | The trusted NEP.compactEmb (NetworkEpi/Morphisms/Compact.lean:60) is (w.1, 1, sirVec (w.1 - N.phiS q w.1 1 - γ(1-w.1)/τ) (γ(1-w.1)/τ), sirVec (1 - N.susc q w.1 1 - w.2) w.2). It uses CNet.phiS q θ ξ = q*ξ*ψ'(θ)/ψ'(1) and CNet.susc q θ ξ = q*ξ*ψ(θ) (Semantics/EB.lean:65-68, which are DESIGN §0's φ_S and S). The RHS emb is the blind transcription of the claim text's embedding (θ,R) ↦ (θ, 1, φ_I = θ − qψ'(θ)/ψ'(1) − φ_R, φ_R = γ(1−θ)/τ, 1 − qψ(θ) − R, R). The shadow helper sv is the same function as sirVec (a at I, b at R). The coordinate order (θ, ξ, φ, pop) matches DataTypes/EB. The only difference is the factor ξ = 1 (q*1*… vs q*…). Degenerate cases (τ = 0, ψ'(1) = 0) use the same Lean division convention on both sides, and the claim assumes τ ≠ 0 anyway. The RHS mentions bound variables and holds no theorem content. The proof is simp only [defs, mul_one]; rfl, and it uses no impl theorem. The audit reports the bridge as valid and unreviewed, with no reasons. |
| `Alignment.Shadows.MorphismsCompact.CompactEmbSemiconj.bridge_emb` | MorphismsCompact.compactEmbSemiconj | reviewed | `8726521545807369653` | `∀ (N : NEP.CNet) (q τ γ : ℝ) (w : ℝ × ℝ), NEP.compactEmb N q τ γ w = Alignment.Shadows.MorphismsCompact.emb N q τ γ w` | This has the same statement (same hash) as CompactConj.bridge_emb, registered for compactEmbSemiconj. In the claim text, 'the embedding' is the M9 embedding (θ,R) ↦ (θ, 1, θ − qψ'(θ)/ψ'(1) − γ(1−θ)/τ, γ(1−θ)/τ, 1 − qψ(θ) − R, R). The blind emb transcribes it, and the trusted compactEmb differs only by ξ = 1 inside phiS and susc. It has the same proof (simp only [defs, mul_one]; rfl), uses no impl theorem, and smuggles no content. The audit reports it as valid and unreviewed. |
| `Alignment.Shadows.MorphismsCompact.CompactSolution.bridge_W` | MorphismsCompact.compactSolution | reviewed | `13424280360243047731` | `∀ (N : NEP.CNet) (q τ γ : ℝ), NEP.compactW N q τ γ = Alignment.Shadows.MorphismsCompact.Wp N q τ γ` | Same statement and hash as CompactConj.bridge_W (confirmed via #sa_audit with NetworkEpi imported: unreviewed, reasons empty). The compactSolution text's 'stays in W'' is the M9 set W' = W ∩ {ξ = 1, θ = φ_S + φ_I + φ_R, S + pop_I + pop_R = 1} (DESIGN §L.2 item 2); Wp is its blind primitive transcription and trusted compactW matches it up to swapping two conjuncts. Universally quantified over q, so the instantiation q = 1 − ρ is covered. No side conditions; proof is ext / simp only unfolding / conjunct swap with no impl theorem; carries none of the invariance or solution content. |
| `Alignment.Shadows.MorphismsCompact.CompactSolutionPoisson.bridge_W` | MorphismsCompact.compactSolutionPoisson | reviewed | `13424280360243047731` | `∀ (N : NEP.CNet) (q τ γ : ℝ), NEP.compactW N q τ γ = Alignment.Shadows.MorphismsCompact.Wp N q τ γ` | Same statement and hash as CompactConj.bridge_W (confirmed via #sa_audit: unreviewed, reasons empty). The §M.4 text's 'it stays in W′' is the same M9 W' (DESIGN §L.2 item 2); Wp transcribes it exactly with φ_S = qξψ'(θ)/ψ'(1), S = qξψ(θ). Holds for every N, q, τ, γ, covering S5's CNet.poisson μ instance with arbitrary q; no μ ≠ 0 or τ ≠ 0 condition needed for the set identity. Same proof as the others, no impl dependency; the RHS is a set in bound variables with none of the existence or solution content. |
| `Alignment.Shadows.MorphismsPoisson.PoissonEbField.bridge_poissonDL` | MorphismsPoisson.poissonEbField | reviewed | `13564941002560147538` | `∀ {σ : Type} [Fintype σ] (μ q : ℝ) (u : NEP.EB σ), NEP.poissonDL μ q u = fderiv ℝ (NEP.poissonMap μ q) u` | The claim text says 'the derivative of poissonMap'. The trusted poissonDL μ q u is documented as 'The derivative of poissonMap μ q at u', and its body is ContinuousLinearMap.pi of the components suscD (CNet.poisson μ) q u (that is, q(v_ξ e^{μ(θ−1)} + ξ μ e^{μ(θ−1)} v_θ)), proj∘ebPhi and proj∘ebPop. The RHS is Mathlib's Fréchet derivative fderiv ℝ (poissonMap μ q) u, which is exactly the text's notion. Degenerate inputs: poissonMap is smooth everywhere, for every μ and q including μ = 0 and q ≤ 0, so fderiv's junk value 0 for non-differentiable maps never applies and the identity holds without side conditions. Domain: [Fintype σ] is needed for EB σ and DSp σ → ℝ to be normed spaces, so fderiv makes sense. The shadow S1 carries the same restriction, so the bridge covers every instance the shadow uses. No smuggling: the equality only identifies the definition with its textual meaning and carries none of the per-reaction field identity (poisson_ebField). The proof, hasFDerivAt_poissonMap_aux then HasFDerivAt.fderiv, uses Mathlib calculus plus unfolding/rfl-simp lemmas of trusted defs. The audit (with NetworkEpi imported) reports the bridge as structurally valid and 'unreviewed', with no impl dependency. The hash was confirmed via #sa_audit. |
| `Alignment.Shadows.MorphismsRempala.RempalaDSurjective.bridge_rempalaD` | MorphismsRempala.rempalaDSurjective | reviewed | `13913574289004458743` | `∀ {σ : Type} (μ q : ℝ) (u : NEP.EB σ), NEP.rempalaD μ q u = fderiv ℝ (NEP.rempalaMap μ q) u` | Same statement and proof as the quotient bridge. The text's 'the derivative of Rempała's map is surjective at every point' refers to fderiv ℝ (rempalaMap μ q) u, which is exactly what shadows T and S1 use. The bridge is unconditional in q, so it does not assume q ≠ 0. Surjectivity (the claim's content) stays in the impl rempalaD_surjective. Degenerate inputs are handled: at q = 0 and μ = 0 the bridge still holds, and the claim restricts to q ≠ 0 anyway. For infinite σ, EB σ carries the product topology and the TVS fderiv applies. For finite σ it agrees with the normed Fréchet derivative. |
| `Alignment.Shadows.MorphismsRempala.RempalaEbField.bridge_rempalaD` | MorphismsRempala.rempalaEbField | reviewed | `13913574289004458743` | `∀ {σ : Type} (μ q : ℝ) (u : NEP.EB σ), NEP.rempalaD μ q u = fderiv ℝ (NEP.rempalaMap μ q) u` | Same statement and proof as the quotient bridge. The text's 'the derivative of Rempała's map carries the EB field ... to the MA field' is the value of fderiv ℝ (rempalaMap μ q) u, and shadows T and S1 use exactly this. The bridge holds for all μ, q, σ and u, so the claim's μ ≠ 0 hypothesis is not affected. The per-reaction field identity (the claim's content) stays in the impl rempala_ebField. The bridge only asserts that rempalaD is the Fréchet derivative, and the helper proves that from Mathlib without any impl theorem. |
| `Alignment.Shadows.MorphismsRempala.RempalaQuotient.bridge_rempalaD` | MorphismsRempala.rempalaQuotient | reviewed | `13913574289004458743` | `∀ {σ : Type} (μ q : ℝ) (u : NEP.EB σ), NEP.rempalaD μ q u = fderiv ℝ (NEP.rempalaMap μ q) u` | The LHS is the trusted rempalaD (NetworkEpi/Morphisms/Rempala.lean:63, suscD.prod ebPhi, docstring 'The derivative of rempalaMap μ q at u'). The RHS is Mathlib's fderiv of the trusted rempalaMap, which is the claim text's 'its derivative at every point', and shadow DerivSurj uses exactly this. The bridge is proved unconditionally for every σ, μ, q and u. There is no q ≠ 0 or Fintype side condition, so no restriction is hidden. The proof goes through HasFDerivAt, so fderiv is not the junk value 0. The codomain ℝ × (σ → ℝ) is T2, so the derivative is unique. For finite σ this is the ordinary normed Fréchet derivative. No theorem content is smuggled: the bridge only identifies the derivative, and the surjectivity content stays in the impl rempala_quotient. The helper hasFDerivAt_rempalaMap_any uses Mathlib only and no impl theorem. The bridge is not registered for hasFDerivAtRempalaMap, where it would carry that claim's content. Audit status is unreviewed with reasons [] when NetworkEpi is imported. |
| `Alignment.Shadows.MorphismsStoich.MaEqStoich.bridge_isSemiconj_linear` | MorphismsStoich.maEqStoich | reviewed | `8957736475694993804` | `∀ (A B : NEP.DynSys) (π : A.V → B.V) (L : A.V →L[ℝ] B.V),   ⇑L = π → (NEP.IsSemiconj A B π ↔ ∀ (u : A.V), π (A.F u) = B.F (π u))` | LHS is the trusted predicate NEP.IsSemiconj A B π, whose body is Differentiable ℝ π ∧ ∀ u, fderiv ℝ π u (A.F u) = B.F (π u) (DESIGN §D.3, Dπ(u)·F(u) = G(π u)). It is applied to the distinct bound variables A, B, π. The RHS ∀ u, π (A.F u) = B.F (π u) mentions bound variables. It is exactly the vector-field correspondence that the claim text means by 'sSys extends / agrees with the library's mass-action semantics' and that blind shadow S7 states: sSys-field at coords u = coords of maSys-field at u, with the orientation fixed by the alignment helper fieldToOpt. The only premise is ⇑L = π for an arbitrary continuous linear map L. Under it the equivalence is a generic calculus fact: a CLM is differentiable and fderiv L u = L. It holds for all DynSys A and B, including degenerate or trivial state spaces. It says nothing specific to maSys, sSys, NRxn or maToS, so no claim content is smuggled. The RHS has no conjunct structure that could hide theorem content. Nothing is lost when the differentiability conjunct is dropped, because it is discharged by linearity, not assumed. The proof uses only subst, L.fderiv and L.differentiable from Mathlib, and no implementation theorem. The checkers instantiate L = maToSL through the helper coe_maToSL (funext + Option cases + rfl), which does not use NEP.maToSL_apply. maToSL = ContinuousLinearMap.pi maToSComp does reduce definitionally to maToS = fun i => i.elim u.1 u.2. The audit confirms the statement and hash with status unreviewed and no rule violations. |
| `Alignment.Shadows.MorphismsWellMixed.WellmixedUnitQuotient.bridge_wmD` | MorphismsWellMixed.wellmixedUnitQuotient | reviewed | `2121590584485827450` | `∀ {σ : Type} [Fintype σ] (κ q : ℝ) (u : NEP.WM σ), NEP.wmD κ q u = fderiv ℝ (NEP.wmMap κ q) u` | The LHS is the trusted def NEP.wmD (NetworkEpi/Morphisms/WellMixed.lean), whose docstring is 'The derivative of wmMap κ q at u'. It is applied to the distinct bound variables κ q u. The RHS is Mathlib's Fréchet derivative fderiv ℝ (wmMap κ q) u. That is exactly the Dπ(u) of DESIGN §D.3, where objects are finite-dimensional real normed spaces and 'a surjective submersion is a quotient', so 'submersion' means Dπ(u) is surjective. [Fintype σ] makes WM σ finite-dimensional, which matches §D.3. The fderiv depends only on the topology, so the sup-norm product convention does not matter. The equation holds for all κ and q, including q = 0 and κ = 0, so no degenerate case is excluded or assumed. It identifies which linear map is 'the derivative' and carries none of the claim's content: surjectivity of the map and of its derivative still comes from the impl (fwd3 only rewrites S3 with the bridge). Proof: wmD_eq_fderiv_aux uses only the NEP constants WM, MA, wmMap, wmD and wmD's auxiliary proofs. It uses no impl theorem, in particular not NEP.hasFDerivAt_wmMap. Axioms are propext, Classical.choice and Quot.sound. The audit status is 'unreviewed' with no shape problems when NetworkEpi is loaded. |
| `Alignment.Shadows.MorphismsWellMixed.WmFieldEq.bridge_wmD` | MorphismsWellMixed.wmFieldEq | reviewed | `2121590584485827450` | `∀ {σ : Type} [Fintype σ] (κ q : ℝ) (u : NEP.WM σ), NEP.wmD κ q u = fderiv ℝ (NEP.wmMap κ q) u` | The statement and proof are the same as the WellmixedUnitQuotient bridge (hash 2121590584485827450). Here it is registered for wmFieldEq, whose text is 'The derivative of `wmMap` carries the well-mixed EB field ... to the mass-action field of c_κ r'. 'The derivative of wmMap' at u is the §D.3 Dπ(u), which is Mathlib's fderiv ℝ (wmMap κ q) u on the finite-dimensional space WM σ (Fintype σ). The trusted wmD has the docstring 'The derivative of wmMap κ q at u'. The RHS is only the derivative operator: it contains neither wmField nor maField and says nothing about the per-reaction field identity. That identity comes entirely from the impl wm_field_eq, and fwd1-3 only rewrite with the bridge. The equation holds for all κ, q and u, with no side conditions. The helper proof depends on no impl theorem, only on WM, MA, wmMap and wmD. Axioms are standard. The audit status is 'unreviewed' with no problems when NetworkEpi is loaded. |
| `Alignment.Shadows.SemanticsEB.EdgeDefectDerivLift.bridge_removalRate` | SemanticsEB.edgeDefectDerivLift | reviewed | `7355096225778200046` | `∀ {σ : Type} (v : σ → ℝ) (r : NEP.Rxn σ), NEP.Rxn.removalRate v r = Alignment.Shadows.SemanticsEB.RemRate v r` | Trusted Rxn.removalRate φ (EB.lean:268) is `\| .trans X none a => a * φ X \| _ => 0`. Shadow RemRate has the same body, token for token: summand a·v_X for a removal (X → ∅, a) and 0 for every other reaction. That is the per-reaction summand of the text's Σ_{(X → ∅, a) ∈ rs} a φ_X. Trusted removalFlux and RemFlux are both List.map-sum, so they count repeated reactions the same way. The bridge is a definitional equation, not a theorem. |
| `Alignment.Shadows.SemanticsEB.HasDerivAtEdgeDefectLift.bridge_removalRate` | SemanticsEB.hasDerivAtEdgeDefectLift | reviewed | `7355096225778200046` | `∀ {σ : Type} (v : σ → ℝ) (r : NEP.Rxn σ), NEP.Rxn.removalRate v r = Alignment.Shadows.SemanticsEB.RemRate v r` | Same as above: the two-sided version of the edge balance law uses the same removal flux notion. The per-reaction equation is definitional. |
| `Alignment.Shadows.SemanticsEB.HasDerivAtNodeTotalLift.bridge_removalRate` | SemanticsEB.hasDerivAtNodeTotalLift | reviewed | `7355096225778200046` | `∀ {σ : Type} (v : σ → ℝ) (r : NEP.Rxn σ), NEP.Rxn.removalRate v r = Alignment.Shadows.SemanticsEB.RemRate v r` | Same as above: the two-sided version of the node balance law uses the same removal flux notion. The per-reaction equation is definitional. |
| `Alignment.Shadows.SemanticsEB.HasDerivWithinAtEdgeDefectLift.bridge_removalRate` | SemanticsEB.hasDerivWithinAtEdgeDefectLift | reviewed | `7355096225778200046` | `∀ {σ : Type} (v : σ → ℝ) (r : NEP.Rxn σ), NEP.Rxn.removalRate v r = Alignment.Shadows.SemanticsEB.RemRate v r` | Same as EdgeDefectDerivLift.bridge_removalRate. The text's Σ_{(X → ∅, a) ∈ rs} a φ_X is RemFlux rs (x t).2.2.1, which is built from RemRate. It matches the trusted removalRate case for case. |
| `Alignment.Shadows.SemanticsEB.HasDerivWithinAtNodeTotalLift.bridge_removalRate` | SemanticsEB.hasDerivWithinAtNodeTotalLift | reviewed | `7355096225778200046` | `∀ {σ : Type} (v : σ → ℝ) (r : NEP.Rxn σ), NEP.Rxn.removalRate v r = Alignment.Shadows.SemanticsEB.RemRate v r` | Same as above. The text's −Σ_{(X → ∅, a) ∈ rs} a pop_X is −RemFlux rs (x t).2.2.2, and the per-reaction summands match the trusted definition exactly. |
| `Alignment.Shadows.SemanticsEB.LiftXiEqZero.bridge_isExit` | SemanticsEB.liftXiEqZero | reviewed | `1226729191463579939` | `∀ {σ : Type} (r : NEP.Rxn σ), r.isExit = true ↔ ∃ Y ν, r = NEP.Rxn.exit Y ν` | Trusted Rxn.isExit (EB.lean:525) is true exactly on `.exit ..`. The exit Y ν constructor is s → Y at rate ν. The RHS ∃ Y ν, r = Rxn.exit Y ν is exactly the text's 'exit', with no side condition on ν and no theorem content. |
| `Alignment.Shadows.SemanticsEB.NodeConservation.bridge_isRemoval` | SemanticsEB.nodeConservation | reviewed | `5031884031455682599` | `∀ {σ : Type} (r : NEP.Rxn σ), r.isRemoval = true ↔ ∃ X a, r = NEP.Rxn.trans X none a` | Same statement and definition as RemovalFluxEqZero.bridge_isRemoval. The text's 'no removal X → ∅' is the negation of this RHS for each r in rs. Exact and faithful, and it carries no theorem content. |
| `Alignment.Shadows.SemanticsEB.NodeTotalDerivLift.bridge_removalRate` | SemanticsEB.nodeTotalDerivLift | reviewed | `7355096225778200046` | `∀ {σ : Type} (v : σ → ℝ) (r : NEP.Rxn σ), NEP.Rxn.removalRate v r = Alignment.Shadows.SemanticsEB.RemRate v r` | Same as EdgeDefectDerivLift.bridge_removalRate, applied to the pop coordinates (u.2.2.2) for 'the removal flux of pop'. Same definition and same faithfulness. |
| `Alignment.Shadows.SemanticsEB.RemovalFluxEqZero.bridge_isRemoval` | SemanticsEB.removalFluxEqZero | reviewed | `5031884031455682599` | `∀ {σ : Type} (r : NEP.Rxn σ), r.isRemoval = true ↔ ∃ X a, r = NEP.Rxn.trans X none a` | Trusted Rxn.isRemoval (NetworkEpi/Semantics/EB.lean:277) is true exactly on `.trans _ none _`. Rxn has only three constructors (contact, exit, trans X (Y : Option σ) a), and trans X none a is documented as X → ∅. So the RHS ∃ X a, r = trans X none a is exactly the text's 'removal X → ∅', with no condition on the rate (a can be any real, including 0 or negative, which matches the Boolean test). The RHS says only what form r has and carries no theorem content. |
| `Alignment.Shadows.SemanticsEB.XiConst.bridge_isExit` | SemanticsEB.xiConst | reviewed | `1226729191463579939` | `∀ {σ : Type} (r : NEP.Rxn σ), r.isExit = true ↔ ∃ Y ν, r = NEP.Rxn.exit Y ν` | Same as LiftXiEqZero.bridge_isExit. The text says 'has no exit s → Y', which is this RHS negated for each member of the list. Faithful. |
| `Alignment.Shadows.SemanticsSolutions.ConservationLocal.bridge_isRemoval` | SemanticsSolutions.conservationLocal | reviewed | `5031884031455682599` | `∀ {σ : Type} (r : NEP.Rxn σ), r.isRemoval = true ↔ ∃ X a, r = NEP.Rxn.trans X none a` | Trusted Rxn.isRemoval is true exactly on `.trans _ none _`; Rxn σ has three constructors and trans X none a is the documented T_EB shape X → ∅ (§B.2 :remove). So the RHS ∃ X a, r = trans X none a is exactly the claim's 'removal X → ∅'. Any rate (including 0) counts, matching the syntactic reading of 'removal-free' in the text and shadow. Definitional, no theorem content, proved by constructor case analysis (isRemoval_iff_aux) without impl theorems. Audit hash 5031884031455682599, empty reasons; identical to the reviewed SemanticsEB bridges. |
| `Alignment.Shadows.SemanticsSolutions.ConservationLocalPoisson.bridge_isRemoval` | SemanticsSolutions.conservationLocalPoisson | reviewed | `5031884031455682599` | `∀ {σ : Type} (r : NEP.Rxn σ), r.isRemoval = true ↔ ∃ X a, r = NEP.Rxn.trans X none a` | Same statement and hash as ConservationLocal.bridge_isRemoval. The text's 'removal-free T_EB reaction list rs' is the negation of the RHS for each r ∈ rs, as the Poisson shadow S1/T states (∀ r ∈ rs, ∀ X a, r ≠ Rxn.trans X none a). Definitional equivalence (three-constructor case split), no domain or convention mismatch, no impl dependency; audit reasons empty. |

## Refuted implementation hypotheses (`hypothesis_refuted`)

The implementation theorem assumes a hypothesis that a sound theorem refutes, so it is vacuously true (and so is every shadow that shares the hypothesis). The refutation is kernel-checked.

None.

## Trusted-free shadows (`shadow_trusted_free`)

These shadows mention no trusted-library constant after inlining alignment helpers, so they are closed statements of logic or arithmetic. The flag zeroes the claim until an independent reviewer confirms that the source text is itself such a statement, with `sa_shadow_reviewed <shadow> "<hash>" "<reason>"` in `Alignment/ReviewedBridges.lean`.

| claim | shadow | content hash | review |
|---|---|---|---|
| `MorphismsCommon.clmListSum` | S1 `Alignment.Shadows.MorphismsCommon.ClmListSum.S1` | `12041906614459084831` | reviewed |
| `MorphismsCommon.clmListSumEq` | S1 `Alignment.Shadows.MorphismsCommon.ClmListSumEq.S1` | `9158484076963380945` | reviewed |
| `MorphismsNGM.memSpectrumIffDet` | S1 `Alignment.Shadows.MorphismsNGM.MemSpectrumIffDet.S1` | `1787981358696633178` | reviewed |
| `MorphismsNGM.memSpectrumIffDet` | S2 `Alignment.Shadows.MorphismsNGM.MemSpectrumIffDet.S2` | `232812835920690492` | reviewed |
| `MorphismsNGM.memSpectrumVecMulVec` | S1 `Alignment.Shadows.MorphismsNGM.MemSpectrumVecMulVec.S1` | `10540623330198837175` | reviewed |
| `MorphismsNGM.r0SingleEntry` | S1 `Alignment.Shadows.MorphismsNGM.R0SingleEntry.S1` | `15818057461608100182` | reviewed |
| `MorphismsNGM.r0SingleEntry` | S2 `Alignment.Shadows.MorphismsNGM.R0SingleEntry.S2` | `15974062422408948211` | reviewed |
| `MorphismsNGM.r0SingleEntry` | S3 `Alignment.Shadows.MorphismsNGM.R0SingleEntry.S3` | `2415423140744252662` | reviewed |
| `MorphismsNGM.r0SingleEntry` | S4 `Alignment.Shadows.MorphismsNGM.R0SingleEntry.S4` | `7939097140091107075` | reviewed |
| `MorphismsNGM.spectralRadiusFinTwo` | S1 `Alignment.Shadows.MorphismsNGM.SpectralRadiusFinTwo.S1` | `1037359448265748064` | reviewed |
| `MorphismsNGM.spectralRadiusFinTwoEqTraceIff` | S1 `Alignment.Shadows.MorphismsNGM.SpectralRadiusFinTwoEqTraceIff.S1` | `15705274408880963938` | reviewed |
| `MorphismsNGM.spectralRadiusFinTwoEqTraceIff` | S2 `Alignment.Shadows.MorphismsNGM.SpectralRadiusFinTwoEqTraceIff.S2` | `6761357480580018513` | reviewed |
| `MorphismsNGM.spectralRadiusVecMulVec` | S1 `Alignment.Shadows.MorphismsNGM.SpectralRadiusVecMulVec.S1` | `8743359799315730361` | reviewed |
| `MorphismsNGM.spectrumFinTwo` | S1 `Alignment.Shadows.MorphismsNGM.SpectrumFinTwo.S1` | `7820572132108939725` | reviewed |
| `MorphismsNGM.spectrumFinTwo` | S2 `Alignment.Shadows.MorphismsNGM.SpectrumFinTwo.S2` | `12557155240545531676` | reviewed |
| `MorphismsNGM.spectrumVecMulVecSubset` | S1 `Alignment.Shadows.MorphismsNGM.SpectrumVecMulVecSubset.S1` | `4556973231874514112` | reviewed |
| `SemanticsEB.constOfHasDerivAtZero` | S1 `Alignment.Shadows.SemanticsEB.ConstOfHasDerivAtZero.S1` | `3890405149653438740` | reviewed |
| `SemanticsEB.constOfHasDerivWithinAtZero` | S1 `Alignment.Shadows.SemanticsEB.ConstOfHasDerivWithinAtZero.S1` | `6671946783152115107` | reviewed |
| `SemanticsEB.hasDerivWithinAtCompClm` | S2 `Alignment.Shadows.SemanticsEB.HasDerivWithinAtCompClm.S2` | `11746623573925970075` | reviewed |
| `SemanticsEB.sumSingle` | S1 `Alignment.Shadows.SemanticsEB.SumSingle.S1` | `15437155665140235158` | reviewed |
| `SemanticsSolutions.contDiffAtPiSingle` | S1 `Alignment.Shadows.SemanticsSolutions.ContDiffAtPiSingle.S1` | `5224569196807938582` | reviewed |
| `SemanticsSolutions.contDiffAtPiSingle` | S2 `Alignment.Shadows.SemanticsSolutions.ContDiffAtPiSingle.S2` | `18100630947886557903` | reviewed |

## Hints (not scored)

`witness_missing`: an implementation hypothesis headed by a trusted predicate is shared by every shadow, and no `@[sa_witness]` certificate shows it can hold. `backward_unused_shadows`: the backward checker does not use some shadows (they may be redundant). `backward_guard_unnormalised`: the backward vacuity guard exhausted its normalisation budget and ran on the unnormalised proof (a weaker check).

* `DynBasic.hasFDerivAtRestrictIncl` backward_unused_shadows: the backward checker does not use shadow(s) [1] (redundant given the others?)
* `DynBasic.invariantIncl` backward_unused_shadows: the backward checker does not use shadow(s) [1] (redundant given the others?)
* `DynProducts.prodIsLimit` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `MorphismsCommon.hasFDerivAtEbCoordinates` backward_unused_shadows: the backward checker does not use shadow(s) [1, 2, 3, 4] (redundant given the others?)
* `MorphismsCommon.hasFDerivAtSusc` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `MorphismsCommon.header.ebSys1` backward_unused_shadows: the backward checker does not use shadow(s) [3] (redundant given the others?)
* `MorphismsCommon.isSemiconjOnInverse` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `MorphismsCommon.isSemiconjOnOfHasFDerivAt` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `MorphismsRempala.rempalaGeneral` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `MorphismsRempala.rempalaGeneralSir` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `MorphismsRempala.rempalaGeneralSolution` backward_unused_shadows: the backward checker does not use shadow(s) [3, 4] (redundant given the others?)
* `MorphismsRempala.rempalaSirProj` backward_unused_shadows: the backward checker does not use shadow(s) [3, 4] (redundant given the others?)
* `SemanticsEB.header.fieldTable` backward_unused_shadows: the backward checker does not use shadow(s) [1, 2, 4, 5, 6, 9, 10, 13, 14, 15, 16] (redundant given the others?)
* `SemanticsPWS.f2SumSV` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `SemanticsPWS.pwSGlueNotStrict` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `SemanticsPWS.pwSGlueNotStrict` backward_guard_unnormalised: the backward vacuity guard exhausted its normalisation budget and ran on the unnormalised proof, which does not see through dodges such as destructuring a shadow and ignoring its parts
* `SemanticsSolutions.conservationLocal` backward_unused_shadows: the backward checker does not use shadow(s) [1] (redundant given the others?)
* `SyntaxRxn.existsNotEbAdmissible` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `SyntaxRxn.notEbAdmissibleNodeContact` backward_unused_shadows: the backward checker does not use shadow(s) [3] (redundant given the others?)
* `SyntaxRxn.notEbAdmissibleResus` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3] (redundant given the others?)
* `SyntaxRxn.typeMap` backward_unused_shadows: the backward checker does not use shadow(s) [7] (redundant given the others?)

## Refuters

Theorems used to refute implementation hypotheses: sound trusted-library theorems `∀ ys, P₁ → … → Pₘ → False` (or `→ ¬ P`, `→ a ≠ b`) and alignment-library `@[sa_refutation]` theorems.

| refuter | origin | status | premise heads | notes |
|---|---|---|---|---|
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

## Recorded failures (`sa_fail_*`)

| claim | target | reason | SHADOW? |
|---|---|---|---|

Check statuses: `pass` (exact statement, structural, not vacuous), `fail` (wrong statement or recorded failure), `vacuous`, `audit_violation` (offenders listed), `sorry`, `missing`. Passes whose shadows were written after seeing the implementation are weak passes.
