#!/usr/bin/env python3
"""Re-sync the SA-PASS harness from EdgeBasedModels.jl/proofs (its upstream) into this project.

The audit code is shared with EBM; only the trust root differs. This script copies
`Alignment/{Registry,Audit}.lean`, the scripts `sa_pass.sh`, `sa_pass_score.py`,
`sa_merge_claims.py`, `sa_claims_lib.py`, `SaPassReport.lean` and `sa_reanchor.py`, and
regenerates `Alignment/README.md`. It applies the NetworkEpi adaptations:

* trusted root `NetworkEpi`, root file `NetworkEpi.lean`;
* the root module itself is trusted too, since it is built by the `NetworkEpi` library;
* report titles;
* README text: groups, templates, examples and limitations.

The NEC-specific files are never touched: `Alignment/Example/*`, `Alignment/All.lean`,
`Alignment/ReviewedBridges.lean`, `Alignment/claims/`, `DataTypes/`, `Shadows/` and `Checks/`.
After a sync:

* run `bash scripts/sa_pass.sh --self-test`;
* update the review hashes in `ReviewedBridges.lean` if the hash function changed;
* port any new upstream mocks from `EdgeBasedModels.jl/proofs/Alignment/Example/SelfTest.lean`.

Usage: python3 scripts/sa_sync_harness.py [--upstream ../../EdgeBasedModels.jl/proofs] [--dry-run]
"""
from __future__ import annotations

import argparse
import pathlib
import re
import shutil
import sys

HERE = pathlib.Path(__file__).resolve().parent.parent

FILES = ["Alignment/Registry.lean", "Alignment/Audit.lean", "scripts/sa_pass.sh",
         "scripts/sa_pass_score.py", "scripts/sa_merge_claims.py", "scripts/sa_claims_lib.py",
         "scripts/SaPassReport.lean", "scripts/sa_reanchor.py"]


def sub(s: str, pat: str, rep: str, path: str, regex: bool = False, required: bool = True) -> str:
    if regex:
        new, n = re.subn(pat, rep, s, flags=re.S)
    else:
        n = s.count(pat)
        new = s.replace(pat, rep)
    if n == 0 and required:
        sys.exit(f"{path}: upstream changed, pattern not found: {pat[:80]!r}")
    return new


def adapt_code(path: str, s: str) -> str:
    if path == "Alignment/Audit.lean":
        s = sub(s, "def trustedRoot : Name := `EBCMCategory", "def trustedRoot : Name := `NetworkEpi", path)
        s = sub(s, r"/-- Module names imported by the trusted root file `EBCMCategory\.lean`[^\n]*\n[^\n]*-/\n"
                   r"def rootImports \(rootFile : System\.FilePath := \"EBCMCategory\.lean\"\)",
                "/-- Module names imported by the trusted root file `NetworkEpi.lean` (read from disk). -/\n"
                "def rootImports (rootFile : System.FilePath := \"NetworkEpi.lean\")", path, regex=True)
        s = sub(s, "/-- The trusted modules: the modules imported by the root file `EBCMCategory.lean` and every\n"
                   "`EBCMCategory.*` module they import (transitively), as far as they are loaded. Trust is by",
                "/-- The trusted modules: the root module `NetworkEpi` itself (it is built by the `NetworkEpi`\n"
                "library), the modules imported by the root file `NetworkEpi.lean` and every `NetworkEpi.*` module\n"
                "they import (transitively), as far as they are loaded. Trust is by", path)
        s = sub(s, "which case every loaded `EBCMCategory.*` module is trusted. -/",
                "which case every loaded `NetworkEpi.*` module is trusted. -/", path)
        s = sub(s, "  | some roots =>\n    let mut seen : NameSet := {}\n    let mut stack : Array Nat := #[]\n"
                   "    for r in roots do",
                "  | some roots =>\n    let mut seen : NameSet := {}\n    let mut stack : Array Nat := #[]\n"
                "    if let some j := env.getModuleIdx? trustedRoot then\n"
                "      seen := seen.insert trustedRoot\n      stack := stack.push j.toNat\n"
                "    for r in roots do", path)
        s = sub(s, "SA-PASS audit for EBCMCategory (Alignment/Audit.lean)",
                "SA-PASS audit for NetworkEpi (Alignment/Audit.lean)", path)
    elif path == "Alignment/Registry.lean":
        s = sub(s, "`EBCMCategory.*`. See `Alignment/README.md`", "`NetworkEpi.*`. See `Alignment/README.md`", path)
    elif path == "scripts/sa_pass.sh":
        s = sub(s, "trusted library EBCMCategory.",
                "trusted library NetworkEpi (modules imported by NetworkEpi.lean).", path)
    elif path == "scripts/sa_pass_score.py":
        s = sub(s, "else 'EBCMCategory'})", "else 'NetworkEpi'})", path)
    return s


SHADOW_TEMPLATE = '''```lean
import Alignment.Registry
import NetworkEpi.<Module>          -- only for the data types / operations listed in DataTypes

open NEP

namespace Alignment.Shadows.<Group>.<ClaimSlug>

/-- Membership of a T_net type in T_EB = {contact, exit, progress, remove}, in primitive terms. -/
def InTEB (t : TNet) : Prop := t = .contact ∨ t = .exit ∨ t = .progress ∨ t = .remove

-- the text is an iff: one shadow per direction
@[sa_reference "<Group>.ebAdmissibleIffType"]
def T : Prop := ∀ {σ : Type} (r : NRxn σ), r.EBAdmissible ↔ InTEB r.type
@[sa_shadow "<Group>.ebAdmissibleIffType" 1]
def S1 : Prop := ∀ {σ : Type} (r : NRxn σ), r.EBAdmissible → InTEB r.type
@[sa_shadow "<Group>.ebAdmissibleIffType" 2]
def S2 : Prop := ∀ {σ : Type} (r : NRxn σ), InTEB r.type → r.EBAdmissible
@[sa_ref_forward "<Group>.ebAdmissibleIffType" 1] theorem ref_fwd1 : T → S1 := fun t _ r => (t r).mp
@[sa_ref_forward "<Group>.ebAdmissibleIffType" 2] theorem ref_fwd2 : T → S2 := fun t _ r => (t r).mpr
@[sa_complete "<Group>.ebAdmissibleIffType"]
theorem complete (s1 : S1) (s2 : S2) : T := fun r => ⟨s1 r, s2 r⟩

end Alignment.Shadows.<Group>.<ClaimSlug>
```

Every shadow must be falsifiable by a wrong implementation. Split along conjunctions, the two
directions of an iff, and the readings of an ambiguity. See `Example/ExampleShadows.lean`
(`EXAMPLE.admissibleType`, `EXAMPLE.notAdmissible`, `EXAMPLE.roundTrip`).

'''

CHECKS_TEMPLATE = '''```lean
import Alignment.Registry
import Alignment.Shadows.<Group>

open NEP

namespace Alignment.Shadows.<Group>.<ClaimSlug>

sa_claim "<Group>.ebAdmissibleIffType" group "<Group>" required
  text "EB-admissibility is membership of the reaction's type in T_EB: \\"the sub-theory with no arrow into Sus\\" (DESIGN §B.2)."
  impl NEP.NRxn.ebAdmissible_iff_type

/-- Bridge (needs independent review): our `TNet.inTEB t = true` vs the text's notion. -/
@[sa_bridge "<Group>.ebAdmissibleIffType"]
theorem bridge_inTEB (t : TNet) : TNet.inTEB t = true ↔ InTEB t := by
  cases t <;> simp [TNet.inTEB, InTEB]      -- tactics are allowed in bridges only

@[sa_forward "<Group>.ebAdmissibleIffType" 1]
theorem fwd1 (h : sa_impl% "<Group>.ebAdmissibleIffType") : S1 :=
  fun r hr => (bridge_inTEB r.type).mp ((h r).mp hr)
@[sa_forward "<Group>.ebAdmissibleIffType" 2]
theorem fwd2 (h : sa_impl% "<Group>.ebAdmissibleIffType") : S2 :=
  fun r ht => (h r).mpr ((bridge_inTEB r.type).mpr ht)
@[sa_backward "<Group>.ebAdmissibleIffType"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "<Group>.ebAdmissibleIffType" :=
  fun r => ⟨fun hr => (bridge_inTEB r.type).mpr (s1 r hr), fun ht => s2 r ((bridge_inTEB r.type).mp ht)⟩
-- if a check is genuinely false:  sa_fail_forward "<Group>.<id>" 2 "impl assumes μ ≠ 0; text says nothing"

end Alignment.Shadows.<Group>.<ClaimSlug>
```

The review record goes in `ReviewedBridges.lean`, written by the reviewer:
`sa_bridge_reviewed Alignment.Shadows.<Group>.<ClaimSlug>.bridge_inTEB "<hash from report>"
"<source: why the RHS is exactly the text's notion>"`.

'''

PORT_NOTES = '''
## Port notes (NetworkEpiCore.jl)

- **Upstream.** This harness is `EdgeBasedModels.jl/proofs/Alignment`, as hardened by WP4.
  `scripts/sa_sync_harness.py` re-copies the shared files and reapplies the adaptations below.
  Re-run the self-test after every sync.
- **Adaptations.**
  - The trusted root is `NetworkEpi`: the root module itself (it is built by the `NetworkEpi`
    library), the modules imported by `NetworkEpi.lean` and their `NetworkEpi.*` imports.
  - Everything else in `Audit.lean`, `Registry.lean` and the scripts is upstream code.
- **Worked example.** `EXAMPLE.admissibleType` needs a reviewed bridge, `EXAMPLE.notAdmissible`
  has two implementation theorems, and `EXAMPLE.roundTrip` has an `@[sa_witness]` certificate.
- **Self-test.** Every upstream mock is ported with NetworkEpi constants, with two exceptions:
  - `SELFTEST.refutedHypothesis` is not ported. A sound refuter can only refute an
    unsatisfiable hypothesis, and NetworkEpi has no trusted theorem with one, by design. The
    refuter-validity mocks are kept. `SELFTEST.witnessMissing` has valid refuters headed by
    `NRxn.EBAdmissible` in scope, so it doubles as the no-false-positive control.
    Re-checked after the WP13 review: an earlier `conservation` asked for a *global* solution,
    which some models lack (EB SEIR on Poisson(5) blows up backward in finite time), so for
    those models its hypotheses could not be met. The solution theorems now take solutions on a
    time interval `I ∋ 0`. `NEP.exists_local_solution` proves that a solution on some
    `(−ε, ε)` exists for every T_EB model whose ψ, ψ', ψ'' are C¹ at the initial θ, and
    `NEP.conservation_local` shows all hypotheses of `conservation` met together.
  - The witness mocks are monomorphic, because NetworkEpi has no universe-polymorphic theorem.
- **Limitation found while porting.** Vacuity test (ii) replaces every subterm definitionally
  equal to the shadow (or to `T̂`) by the fresh proposition. So when a shadow is definitionally
  equal to `T̂`, a checker that discards its shadow is **not** detected: an earlier version of
  `SELFTEST.backwardVacuousEval` passed. The mocks therefore use shadows that differ from `T̂`,
  and such shadows are flagged only as `identical_to_impl` (weak evidence).
- **Citable theorems.** SA-PASS claims are to be registered for the names in `../CITABLE.txt`.
  Their docstrings carry a **Design statement** (a quote from DESIGN_NetworkEpiCore.md) and a
  **Lean statement** (the precise natural-language spec).
'''


def adapt_readme(s: str) -> str:
    p = "Alignment/README.md"
    s = sub(s, "SA-PASS checks that each Lean theorem of the trusted library `EBCMCategory.*` says what its",
            "SA-PASS checks that each Lean theorem of the trusted library `NetworkEpi.*` says what its", p)
    s = sub(s, r"\| trusted library `TemporalOlogs\.\*` \|[^\n]*\n",
            "| trusted library `TemporalOlogs.*` | `NetworkEpi.*`: the root module `NetworkEpi`, exactly the "
            "modules imported by `NetworkEpi.lean` (read from disk), plus their `NetworkEpi.*` imports. Trust is "
            "decided by module, never by declaration name. |\n", p, regex=True)
    s = sub(s, r"\| spec `kernel\.md`, ADRs \|[^\n]*\n",
            "| spec `kernel.md`, ADRs | theorem docstrings (the **Design statement** quote from "
            "`DESIGN_NetworkEpiCore.md` and the **Lean statement** paragraph of every citable theorem), module "
            "header text and tables, `../README.md` |\n", p, regex=True)
    s = sub(s, r"There is one group per trusted module, named after the module \(`EpiCategory`.*?The prefixes `EXAMPLE\.` and `SELFTEST\.` are reserved\.",
            "There is one group per trusted module, named after its path without dots (`DynBasic`,\n"
            "`DynProducts`, `SyntaxRxn`, `SemanticsEB`, `SemanticsMA`, `SemanticsPWS`,\n"
            "`SemanticsPoissonSIR`, and later WP28's `Morphisms…` and `Closure…`). Claims taken from\n"
            "`../README.md` form the group `Docs`. Claim ids are `<Group>.<lowerCamelTheoremName>` (split\n"
            "into `…a`, `…b`, … when a docstring makes several claims). Ids must match `[A-Za-z0-9._-]+`.\n"
            "The prefixes `EXAMPLE.` and `SELFTEST.` are reserved. Register a claim for every name in\n"
            "`../CITABLE.txt` first.", p, regex=True)
    s = sub(s, "author never opens `EBCMCategory/*.lean`", "author never opens `NetworkEpi/**/*.lean`", p)
    s = sub(s, "worked example (3 claims, SA-PASS = 1, including a reviewed bridge and a universe-polymorphic claim)",
            "worked example (3 claims, SA-PASS = 1: a reviewed bridge, two implementation theorems, a satisfiability witness)", p)
    s = sub(s, r"\| `\.\./scripts/axiom_gate\.sh`, `\.\./scripts/AxiomGate\.lean` \|[^\n]*\n",
            "| `../scripts/axiom_gate.sh`, `../GateTools/AxiomGate.lean` | CI gate: every `CITABLE.txt` name is a "
            "sorry-free trusted theorem with a design-quoting docstring and standard axioms; no trusted `axiom` "
            "(see `../README.md`) |\n| `../scripts/sa_sync_harness.py` | re-sync the shared harness files from "
            "`EdgeBasedModels.jl/proofs` |\n", p, regex=True, required=False)
    s = sub(s, "## Commands (from `EdgeBasedModels.jl/proofs`;", "## Commands (from `NetworkEpiCore.jl/proofs`;", p)
    s = sub(s, "are arguments of data terms (e.g. `PGFData.poisson κ hκ`) are skipped",
            "are arguments of data terms (e.g. `Semiconj.ofIsSemiconj π h`) are skipped", p)
    s = sub(s, "inductives that have proof fields (`Subtype`, `Fin`, `PGFData`, …), and projections of data\n"
               "  structures in a proof position (`ψ.mean_pos`, `Subtype.property`,",
            "inductives that have proof fields (`Subtype`, `Fin`, `Semiconj`, …), and projections of data\n"
            "  structures in a proof position (`m.diff` for `m : Semiconj A B`, `Subtype.property`,", p)
    s = sub(s, "declared in `EBCMCategory.*` or `Alignment.*` (their definitional logic);",
            "declared in `NetworkEpi.*` or `Alignment.*` (their definitional logic);", p)
    s = sub(s, "`witness_missing`. See `EXAMPLE.trajectoryGapZero`.", "`witness_missing`. See `EXAMPLE.roundTrip`.",
            p, required=False)
    s = sub(s, r"(## Template: `Alignment/Shadows/<Group>\.lean` \(blind\)\n\n).*?(## Template: `Alignment/Checks/<Group>\.lean`\n\n)",
            lambda m: m.group(1) + SHADOW_TEMPLATE + m.group(2), p, regex=True)
    s = sub(s, r"(## Template: `Alignment/Checks/<Group>\.lean`\n\n).*?(Writing structural proofs:)",
            lambda m: m.group(1) + CHECKS_TEMPLATE + m.group(2), p, regex=True)
    s = sub(s, "or data invariants (`ψ.mean_pos`).", "or proof fields of data (`m.diff`, `m.comm`).", p, required=False)
    s = sub(s, "* For universe-polymorphic `impl`s, declare the implementation's own level names\n"
               "  (`universe u_1 u_2`; see `#check @Thm`) and state `S1.{u_1, u_2}`.\n",
            "* For universe-polymorphic `impl`s (none in NetworkEpi yet), declare the implementation's own\n"
            "  level names (`universe u_1 u_2`; see `#check @Thm`) and state `S1.{u_1, u_2}`.\n", p, required=False)
    s = sub(s, "7. Trust follows `EBCMCategory.lean`.", "7. Trust follows `NetworkEpi.lean`.", p)
    s = sub(s, "`PGFEval.mk 1 1 1 (by norm_num) …` contain proofs.", "`Semiconj.ofIsSemiconj π h` contain proofs.",
            p, required=False)
    s = sub(s, "(`… ∧ PGFData = PGFData`)", "(`… ∧ CNet = CNet`)", p, required=False)
    rest = [m.start() for m in re.finditer("EBCMCategory|PGFData|SIRParams", s)]
    if rest:
        print(f"  WARNING README: remaining EBM-specific names at {len(rest)} place(s): "
              + "; ".join(s[max(0, i - 40):i + 40].replace("\n", " ") for i in rest[:6]))
    return s.rstrip("\n") + "\n" + PORT_NOTES


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--upstream", default=str(HERE.parent.parent / "EdgeBasedModels.jl" / "proofs"))
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()
    up = pathlib.Path(args.upstream)
    for f in FILES:
        src = up / f
        if not src.exists():
            print(f"  skip (absent upstream): {f}")
            continue
        s = adapt_code(f, src.read_text())
        left = [m.start() for m in re.finditer("EBCM", s)]
        if left:
            print(f"  WARNING {f}: {len(left)} remaining EBCM reference(s)")
        if not args.dry_run:
            dst = HERE / f
            dst.parent.mkdir(parents=True, exist_ok=True)
            dst.write_text(s)
            shutil.copymode(src, dst)
        print(f"  synced {f}")
    readme = adapt_readme((up / "Alignment" / "README.md").read_text())
    if not args.dry_run:
        (HERE / "Alignment" / "README.md").write_text(readme)
    print("  regenerated Alignment/README.md")
    return 0


if __name__ == "__main__":
    sys.exit(main())
