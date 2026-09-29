# Morphisms


A `Semiconjugacy` is a map π from a source `SymbolicODE` to a target, with a `kind`
(`:conjugacy`, `:semiconjugacy`, `:restriction` or `:lumping`), an **exactness** (`:exact`,
`:limit` or `:calibration`) and a list of `Evidence` records (`:lean`, `:symbolic`, `:paper`).
`verify(m)` checks the conjugacy equation Jπ·F = G∘π. It works symbolically first and then at
seeded numeric probes. Every term that does not cancel must be seen at some probe. An
"undecided" result is an error. Limits and calibrations are never called morphisms, and `verify`
rejects them.

EdgeBasedModels registers six natural transformations, listed by `transformations()`:
`:well_mixed_unit` (M1), `:poisson_iso` (M2), `:rempala` (M3), `:power_law` (M4),
`:general_kinetics` (M5) and `:eb_to_pws` (M6). Its README tabulates the verify results. The
Rempała map, for example, carries the evidence `NEP.rempala` (citable; its SA-PASS claim awaits a
checker update after the round-4 remediation), `NEP.rempala_lift`, Rempała 2023
Thm 1 and a symbolic test.

