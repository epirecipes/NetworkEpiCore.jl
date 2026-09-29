# NetworkEpi: Lean proofs for NetworkEpiCore.jl

A Lake project (package `NetworkEpi`, namespace `NEP`) holding the machine-checked parts of
the mathematics in `DESIGN_NetworkEpiCore.md` §D. The **trusted library** is exactly the modules
imported by `NetworkEpi.lean`. **Vignettes and docs cite only theorem names listed in
`CITABLE.txt`**, and every listed name passes the axiom gate.

## Contents

| module | design | what is proved |
|---|---|---|
| `NetworkEpi/Dyn/Basic.lean` | L1, §D.3 | `DynSys` (a real normed space with a vector field), `Semiconj`, `instance dynCategory : Category DynSys`, `Semiconj.map_solution`, `SemiconjOn` with `SemiconjOn.map_solution_on` and `SemiconjOn.map_solution_within` (solutions on a time interval, one-sided at end points), restriction to a tangent affine subspace with `invariant_incl` |
| `NetworkEpi/Dyn/Products.lean` | L1b, §D.3 (stretch) | in `DynSys`: `(V × W, F × G)` is the product (`prod_isLimit`), `hasBinaryProducts`, the zero-dimensional system is terminal (`hasTerminal`) |
| `NetworkEpi/Syntax/Rxn.lean` | L2, §B.2, §D.1 | `Rxn σ` (T_EB: contact, exit, progress, remove), `NRxn σ` (adds `resus` and `nodeContact`), the typing `NRxn.type`, decidable `EBAdmissible` with `ebAdmissible_iff` and `ebAdmissible_iff_type`, `Rxn.map` / `NRxn.map` (functorial, type-preserving), the rate convention `scaleContacts` |
| `NetworkEpi/Semantics/EB.lean` | L3, §D.4 | the per-reaction EB field `ebField`, with exits and ξ, on coordinates (θ, ξ, φ, pop); `lift_append`, `ebField_map`, `lift_map`, `lift_glue` (H1, strict gluing); for a solution on a time interval I ∋ 0: `conservation` (θ = φ_S + Σφ_X), `node_conservation` (S + Σ pop = 1), the balance laws with removals, `xi_const` (ξ is constant without exits) |
| `NetworkEpi/Semantics/MA.lean` | L3, §D.6 H1′ | the mass-action field `maField` on T_net reactions; `maLift_append`, `maField_map`, `maLift_map`, `maLift_glue` |
| `NetworkEpi/Semantics/PWS.lean` | L3 stretch, §D.6 F2 | the S-anchored pairwise field `pwSField` (constant closure K); `pwS_glue_not_strict`, an explicit witness that PW^S is not strict under gluing |
| `NetworkEpi/Semantics/PoissonSIR.lean` | L4c for SIR, §D.5 M3 | `rempala` (SIR EB on Poisson(μ) → MA SIR(μτ, γ+τ) via (θ, φ) ↦ (qe^{μ(θ−1)}, φ)); `ebPoisSIR_lift` (the 2-D system is the general lift on ξ = 1); `rempala_lift` (their composite); `rempala_solution` (every EB SIR solution on a time interval I ∋ 0 with ξ(0) = 1 maps to an MA SIR solution in (S, φ_I) on I) |
| `NetworkEpi/Semantics/Solutions.lean` | L3, §D.3, §D.4 | `contDiffAt_lift` / `contDiff_lift` (the EB field is C^n where ψ, ψ', ψ'' are, so EB models on Poisson networks are objects of Dyn); `exists_local_solution` (Picard–Lindelöf); `conservation_local` (a solution on some (−ε, ε) from the design's initial condition exists, and θ = φ_S + Σφ_X along it); `conservation_local_poisson`; `seir_conservation_local` (EB SEIR on Poisson(5), a model with no global solution) |
| `NetworkEpi/Morphisms/**`, `NetworkEpi/Closure/**` | L4 (WP28) | reserved for the morphism catalogue: general Rempała, PT ⇔ constant closure, WM unit, Poisson isomorphism, EB → PW^S, compact ⊂ expanded |

**Scope and precise differences from the design text** (also stated in each docstring):

- `DynSys` is more general than the design's **Dyn**. `V` is any real normed space, `F` is any
  function and morphisms need only be differentiable. **Dyn** (finite-dimensional, C¹) is a
  subcategory, so every statement about all objects or all morphisms also holds there. This does
  **not** cover the existence of limits: `hasBinaryProducts` and `hasTerminal` are proved for
  `DynSys`. That Dyn is closed under these products is true (products of finite-dimensional C¹
  systems and pairings of C¹ maps are C¹) but not formalised. `contDiff_lift` shows that EB
  models on networks with C¹ degree data (such as Poisson) are objects of Dyn.
- **Solutions live on a time interval.** `conservation`, `node_conservation`, `xi_const` and
  `rempala_solution` take any convex set of times `I ∋ 0` (for example `(a, b)`, `[0, T)`,
  `[0, ∞)`) and a curve with `HasDerivWithinAt x (F (x t)) I t` for `t ∈ I`. That derivative is
  one-sided at end points of `I`, and `HasDerivAt` implies it. The degree data need derivative
  relations only at the visited θ values, so a negative binomial PGF (pole at 1/(1 − p) > 1) is
  covered. Global solutions need not exist: numerically, EB SEIR on Poisson(5) (τ = 1/6,
  σ = 1/3, γ = 1/4, φ_I(0) = 0.01) blows up backward at t ≈ −7.33.
  `conservation_local` and `seir_conservation_local` prove that the hypotheses can be met.
- `Rxn.exit (Y : σ)` cannot express `s → ∅`, which §B.2 allows ("Y ∉ Σ (or ∅)"). Model it with
  an inert sink species `D`, one that occurs in no other reaction. No other coordinate of the EB
  field depends on φ_D or pop_D, so θ, ξ, S and the other φ, pop are unchanged.
- `NRxn.ebAdmissible_iff_type`, `not_ebAdmissible_resus` and `exists_not_ebAdmissible` are
  statements about the syntax. They hold by definition, because `EBAdmissible` and `TNet.inTEB`
  are parallel case tables. They do not prove that no EB-type semantics exists for `X → s`.
- The syntax has one implicit susceptible species `s` on an untyped, single-layer configuration
  network (|Σ| = 1). `:sus_move` and `:sus_contact` are not represented. The EB state has no `cum`
  accumulator.
- `conservation` needs **no removals `X → ∅`**. For any reaction list,
  `d/dt (θ − φ_S − Σφ_X) = Σ_{(X→∅,a)∈rs} a φ_X` (`hasDerivAt_edgeDefect_lift`). A removal leaves
  θ unchanged and lowers Σφ by aφ_X (the partner becomes inert: its edges stay in θ but leave every
  φ class; `ebField_removal_row`), so the rate is non-negative when the removal rates and the φ_X
  are non-negative (`removalFlux_nonneg`). Without removals the rate is 0 (`removalFlux_eq_zero`).
  The design's unqualified "Conservation θ = φ_S + Σφ_X holds" (§D.4) is true for removal-free
  models only. See DESIGN §M.1 and `conservation_invariant`.
- `rempala` is the SIR case of M3. Naturality in P and the general quotient are WP28's (L4c).
- The lift laws hold for arbitrary functions ψ, ψ', ψ''. Only `conservation`,
  `node_conservation` and the Poisson bridge use derivative relations.

## Build

The toolchain is `leanprover/lean4:v4.29.0-rc4`, and `lake-manifest.json` pins Mathlib
`3a4b36f2`. These are the revisions that `EdgeBasedModels.jl/proofs` builds with; move to the next
stable release once Mathlib supports it (§D.7).

```sh
cd NetworkEpiCore.jl/proofs
# locally: reuse EBM's Mathlib checkout and build cache (APFS clone, instant)
mkdir -p .lake && cp -Rc ../../EdgeBasedModels.jl/proofs/.lake/packages .lake/
# elsewhere (and in CI): lake exe cache get
lake build                                  # the trusted library NetworkEpi
bash scripts/axiom_gate.sh                  # build + gate on CITABLE.txt
bash scripts/axiom_gate.sh --self-test      # also check that the gate rejects bad names
```

Wrap long commands on macOS in `perl -e 'alarm 590; exec @ARGV' …`. CI is
`../.github/workflows/lean.yml`. The Mathlib cache server has build files for the pinned
revision and toolchain: `lake exe cache get- Mathlib.Logic.Basic` downloaded all 66 files of that
module's import closure. The workflow has not yet run on GitHub. If `lake exe cache get` fails
there, it warns and `lake build` compiles Mathlib from source (timeout 300 min).

## The gate (`scripts/axiom_gate.sh`, `GateTools/AxiomGate.lean`, `scripts/AxiomGate.lean`)

The gate fails if any of these holds:

- the build fails;
- a trusted source file declares an `axiom` or contains `sorry` / `admit`;
- a trusted source file uses an escape hatch outside comments: `unsafe`, `implemented_by`,
  `@[extern]`, `set_option debug.*` (such as `debug.skipKernelTC`), `native_decide` /
  `ofReduceBool` or `#exit`;
- a `CITABLE.txt` name is missing from the build or is not a `theorem`;
- a `CITABLE.txt` name is declared outside `NetworkEpi.*`;
- a `CITABLE.txt` name has no docstring containing `Design statement`, i.e. one that quotes the
  design;
- a `CITABLE.txt` name depends on an axiom beyond `propext`, `Classical.choice` and `Quot.sound`,
  which catches `sorryAx`;
- any declaration of the trusted library is an axiom or uses a non-standard axiom.

`scripts/AxiomGateSelfTest.lean` feeds the gate deliberately bad names: a missing name, a
non-theorem, a non-trusted name, a name with no docstring, one without a design quote, a `sorry`
theorem and one using an axiom. The gate must reject each for the stated reason. With
`--self-test` the source scan is also run on generated files: it must flag each escape hatch and
ignore the same tokens in comments.

## Citable theorems and docstrings

Each citable theorem's docstring has two parts:

- **Design statement**: a verbatim quote from `DESIGN_NetworkEpiCore.md` (§ given).
- **Lean statement**: a precise natural-language restatement of what the Lean theorem says,
  including hypotheses and scope.

These docstrings are the natural-language specification for SA-PASS. Never cite the
free-scalar pairwise identity as a semiconjugacy, or any theorem of the legacy EBM tree (§D.7,
"Never cited").

## Ownership (DESIGN §G.2)

- **WP13** owns everything here except `NetworkEpi/Morphisms/**` and `NetworkEpi/Closure/**`
  (WP28). That includes `CITABLE.txt`, `NetworkEpi.lean`, the gate and the Alignment harness.
- **WP28** adds modules under its two directories. It then requests the new `import` lines in
  `NetworkEpi.lean` (which makes them trusted) and the new names in `CITABLE.txt`, for review by
  the WP13 owner.
- Useful building blocks for WP28:
  - `NEP.pwSField` (PW^S, checked against the design's `check_pwS_general.py` and
    `check_exit_pws.py`);
  - `NEP.Rxn.scaleContacts` (c_κ);
  - `NEP.CNet.poisson`;
  - `NEP.ebSys` and `NEP.maSys`;
  - `NEP.IsSemiconj` and `NEP.IsSemiconjOn`.

## SA-PASS alignment (`Alignment/`)

The SA-PASS harness is copied from `EdgeBasedModels.jl/proofs/Alignment` (as hardened by WP4)
and adapted to trust `NetworkEpi.*`: the root module and the modules imported by
`NetworkEpi.lean`. `scripts/sa_sync_harness.py` re-syncs the shared files (`Registry.lean`,
`Audit.lean`, the scripts, the README) from upstream. The NEC worked example (3 `EXAMPLE.*`
claims) and self-test mocks live in `Alignment/Example/`. No claims are registered yet;
`Alignment/claims/` is empty. The next SA-PASS run should first register one claim per
`CITABLE.txt` name, taking the text from the docstrings.

```sh
bash scripts/sa_pass.sh --self-test      # every mock gets its expected status; EXAMPLE.* pass
bash scripts/sa_pass.sh                  # report (Alignment/report/sa_pass_report.md)
bash scripts/sa_pass.sh --strict         # exit 1 if a registered required claim lacks SA-PASS = 1
python3 scripts/sa_citable_coverage.py   # which CITABLE.txt names have a passing claim
bash scripts/sa_pass_citable.sh          # release gate: --strict AND every CITABLE name covered
```

`sa_pass.sh --strict` exits 0 when no claims are registered. The NEC-local
`sa_citable_coverage.py --strict` (run by `sa_pass_citable.sh`) exits 1 unless every name in
`CITABLE.txt` is in the `impl` of a registered required claim with SA-PASS = 1. Until the claims
are registered, it lists every name as `NO CLAIM`.

See `Alignment/README.md` for the procedure and roles, and its "Port notes" for what differs
from the EBM self-test.
