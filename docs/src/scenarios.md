# Shared scenarios and validation


`scenario_ids()` lists **51 registered scenarios**. They share R₀ = 2 and r = 5/12, while their
final sizes differ: `:sir_reg6` 0.93, `:sir_pois5` 0.80, `:sir_nb4` 0.64, `:sir_bim` 0.50 and
`:sir_pl` 0.29. There are also SEIR, SEAIR, two-strain, vaccination, Erlang, clustered,
multitype, multiplex, dynamic, degree-correlated, dormant-contact, MFSH, dense and N-scaling
variants, and SIS on a 3-regular network. A `Scenario` is pure data: model, network, parameters,
seeding, time grid, a `SimConfig`, a verdict for each back end (`:exact_limit`, `:biased`,
`:approximate`, `:inadmissible`) and expected values that NEC computes. It is hashed from a
versioned canonical text (`canonical_text`, `scenario_hash`), not from `Base.hash`.

NetworkOutbreaks runs the scenarios (N = 10⁴, 200 runs, a fresh graph per run) and commits their
summaries (`NetworkOutbreaks.jl/data/scenarios`, 53 files, none missing). EdgeBasedModels and
NodeBasedModels load them with `scenario_summary` and compare with `compare(ref, curves...)`,
which reports D∞, z∞, ΔR∞ with its 95% CI, Δpeak and coverage. `comparisonplot` draws the same
ribbon and residual figure for both. The **N-scaling protocol** (N = 10³, 10⁴, 10⁵) tells an
exact large-N limit, whose error falls to the Monte Carlo floor, from a structural bias, whose
error levels off. Numbers are in the three package READMEs.

