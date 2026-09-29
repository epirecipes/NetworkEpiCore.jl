# Lean: the `NetworkEpi` library

`proofs/` is a Lake project (package `NetworkEpi`, namespace `NEP`; Lean 4.29.0-rc4, Mathlib
`3a4b36f2`). The **trusted library** is exactly the modules imported by `NetworkEpi.lean`, which
is 18 module files: `Dyn/{Basic,Products}`, `Syntax/Rxn`, `Semantics/{EB,MA,PWS,PoissonSIR,Solutions}`,
`Morphisms/{Common,Rempala,WellMixed,Stoich,Poisson,Pairwise,Compact,NGM,All}` and `Closure/PT`.
This is the genuine library behind the packages. EdgeBasedModels' legacy `EBCMCategory` tree is
never cited.

- **Axiom gate** (`scripts/axiom_gate.sh`). The gate fails on any of the following:
  - a failed build;
  - any `axiom`, `sorry` or `admit`, or an escape hatch (`native_decide`, `implemented_by`, …)
    in a trusted file;
  - a `CITABLE.txt` name that is not a theorem of `NetworkEpi.*`;
  - a `CITABLE.txt` name without a docstring that quotes the design ("Design statement");
  - a `CITABLE.txt` name that depends on an axiom beyond `propext`, `Classical.choice` and
    `Quot.sound`.

  `--self-test` checks that the gate rejects deliberately bad names. The build and the gate pass.
- **`CITABLE.txt`** lists **89** theorem names. Vignettes and docs cite only these names.
- **Headline results.** They include:
  - `NEP.rempala_general`, the Rempała quotient for every T_EB model (M3);
  - `NEP.poisson_iso` and `NEP.poisson_iso_semiconj` (M2);
  - `NEP.wellmixed_unit` (M1);
  - `NEP.eb_to_pws`, EB → S-anchored pairwise for every PGF (M6);
  - `NEP.pt_iff_const_closure`, Poisson type ⇔ constant closure (M8);
  - `NEP.compact_conj_global` (M9);
  - `NEP.lift_append` and `NEP.lift_glue`, strict gluing (H1);
  - `NEP.conservation_invariant`;
  - `NEP.multiplex_r0_of_entries` and `NEP.spectralRadius_fin_two`, the two-layer R₀ = ρ(K).
- **Alignment (SA-PASS).** SA-PASS checks whether each Lean statement says what its
  natural-language text says. The figures below are from the round-4 run of 2026-09-28
  (`bash scripts/sa_pass.sh`; report in `Alignment/report/sa_pass_report.md`), taken after the
  non-blind owner's remediation and before the checker and blind-shadow updates it calls for.
  - **176 of 194 required claims (90.7%)** have SA-PASS = 1; mean SA-PASS_soft is 0.912.
    `MorphismsCompact.compactSolutionPoisson` now passes (the vacuity guard's normaliser is
    memoised).
  - **18 required claims fail**, all pending follow-up work, not new defects:
    - 16 have a new implementation list (new trusted theorems that close a forward gap, or
      exact-statement theorems where the old one was more general than the text); they report
      `impl_mismatch` until the checker author updates their `sa_claim` and checkers;
    - 2 have new claim text and wait for blind re-shadowing: `DynBasic.semiconjOnMapSolutionWithin`
      and `MorphismsPoisson.poissonIsoSolution`.
  - All 22 trusted-free shadows and all 25 bridges are reviewed.
  - The release gate `scripts/sa_pass_citable.sh` **fails**: `python3 scripts/sa_citable_coverage.py`
    reports **56 of 89** names covered. The other 33 belong to the 18 pending claims (17 have a
    failing claim, 16 new names are not yet in any `sa_claim`).

  So a `CITABLE.txt` name is guaranteed to be a real, axiom-clean theorem whose docstring
  quotes the design. It is not yet guaranteed that its statement has been independently
  aligned with that quote.

Build and check:

```sh
cd NetworkEpiCore.jl/proofs
mkdir -p .lake && cp -Rc ../../EdgeBasedModels.jl/proofs/.lake/packages .lake/   # locally; CI: lake exe cache get
lake build && bash scripts/axiom_gate.sh && bash scripts/axiom_gate.sh --self-test
bash scripts/sa_pass.sh && bash scripts/sa_pass_citable.sh
```

See `proofs/README.md` in the repository for the module table and the exact scope of each
statement.

