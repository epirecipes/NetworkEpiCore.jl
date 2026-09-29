#!/usr/bin/env python3
"""Check that every citable theorem (CITABLE.txt) is covered by a passing SA-PASS claim.

NEC-local (not synced from upstream): `sa_pass.sh --strict` fails only if a *registered*
required claim lacks SA-PASS = 1, so with no claims registered it exits 0. This check closes that
gap. A name in `CITABLE.txt` is **covered** if some claim in the SA-PASS report
(`Alignment/report/sa_pass_report.json`, written by `bash scripts/sa_pass.sh`)

* lists the name in its `impl`,
* is `required`, and
* has `sa_pass == 1`.

Usage:
    python3 scripts/sa_citable_coverage.py            report the coverage; exit 0
    python3 scripts/sa_citable_coverage.py --strict   exit 1 unless every citable name is covered

`bash scripts/sa_pass_citable.sh` runs `sa_pass.sh --strict` and then this check with --strict.
Exit codes: 0 ok, 1 uncovered names (--strict), 2 missing or unreadable input.
"""
from __future__ import annotations

import argparse
import json
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent.parent


def citable_names(path: pathlib.Path) -> list[str]:
    names = []
    for line in path.read_text(encoding="utf-8").splitlines():
        s = line.strip()
        if s and not s.startswith("#"):
            names.append(s)
    return names


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--citable", default=str(HERE / "CITABLE.txt"))
    ap.add_argument("--report", default=str(HERE / "Alignment" / "report" / "sa_pass_report.json"))
    ap.add_argument("--strict", action="store_true")
    args = ap.parse_args()

    names = citable_names(pathlib.Path(args.citable))
    rep_path = pathlib.Path(args.report)
    if not rep_path.exists():
        print(f"no SA-PASS report at {rep_path}; run `bash scripts/sa_pass.sh` first", file=sys.stderr)
        return 2
    report = json.loads(rep_path.read_text(encoding="utf-8"))
    if report.get("mode") != "report":
        print(f"{rep_path} is a {report.get('mode')!r} report, not a report-mode run", file=sys.stderr)
        return 2

    passing: dict[str, list[str]] = {}
    failing: dict[str, list[str]] = {}
    for c in report.get("claims", []):
        for impl in c.get("impl") or []:
            if c.get("required") and c.get("sa_pass") == 1:
                passing.setdefault(impl, []).append(c["id"])
            else:
                failing.setdefault(impl, []).append(c["id"])

    covered = [n for n in names if n in passing]
    weak = [n for n in names if n not in passing and n in failing]
    missing = [n for n in names if n not in passing and n not in failing]
    print(f"CITABLE coverage: {len(covered)}/{len(names)} citable name(s) covered by a required claim "
          f"with SA-PASS = 1")
    for n in weak:
        print(f"  NOT PASSING  {n}  (claims: {', '.join(failing[n])})")
    for n in missing:
        print(f"  NO CLAIM     {n}")
    if args.strict and (weak or missing):
        print(f"STRICT: {len(weak) + len(missing)} citable name(s) not covered")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
