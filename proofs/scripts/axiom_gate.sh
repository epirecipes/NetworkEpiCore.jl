#!/usr/bin/env bash
# Axiom gate for the NetworkEpi Lean library (DESIGN_NetworkEpiCore.md §D.7, "Gate").
#
#   bash scripts/axiom_gate.sh             lake build, then check CITABLE.txt and the trusted library
#   bash scripts/axiom_gate.sh --no-build  check only (reuse the last build)
#   bash scripts/axiom_gate.sh --self-test also check that the gate rejects deliberately bad names
#
# Fails (exit 1) if the build fails; if a trusted source file (NetworkEpi.lean, NetworkEpi/**)
# declares an `axiom`, contains the tokens `sorry` / `admit`, or uses an escape hatch outside
# comments (`unsafe`, `implemented_by`, `@[extern]`, `set_option debug.*` such as
# `debug.skipKernelTC`, `native_decide` / `ofReduceBool`, `#exit`); or if scripts/AxiomGate.lean
# reports a CITABLE.txt name that is missing, not a theorem, outside NetworkEpi.*, without a
# design-quoting docstring, or depending on an axiom beyond propext, Classical.choice and
# Quot.sound (which includes sorryAx). Vignettes cite only names in CITABLE.txt.
# Long commands are wrapped in `perl -e 'alarm N'` (macOS has no `timeout`).
set -uo pipefail

cd "$(dirname "$0")/.." || exit 2
BUILD=1
SELFTEST=0
for arg in "$@"; do
  case "$arg" in
    --no-build) BUILD=0 ;;
    --self-test) SELFTEST=1 ;;
    -h|--help) sed -n '2,16p' "$0"; exit 0 ;;
    *) echo "unknown option: $arg" >&2; exit 2 ;;
  esac
done
ALARM=${AXIOM_GATE_ALARM:-3000}
with_alarm() { perl -e 'alarm shift; exec @ARGV' "$ALARM" "$@"; }
status=0

# Escape hatches that bypass the kernel or the axiom check: print `file:line: token` for each use
# outside comments and docstrings (block comments are blanked, keeping line numbers); exit 1 if any.
scan_escape_hatches() {
  perl -0777 -ne '
    my $s = $_;
    $s =~ s{/-.*?-/}{ my $m = $&; $m =~ s/[^\n]//g; $m }gse;
    $s =~ s{--[^\n]*}{}g;
    my $ln = 0;
    for my $line (split /\n/, $s, -1) {
      $ln++;
      if ($line =~ /(\bunsafe\b|\bimplemented_by\b|\@\[\s*extern\b|\bset_option\s+debug\.\S*|\bnative_decide\b|\bofReduceBool\b|^\s*#exit\b)/) {
        print "$ARGV:$ln: $1\n"; $found = 1;
      }
    }
    END { exit($found ? 1 : 0) }' "$@"
}

echo "== [1/3] source scan (NetworkEpi.lean, NetworkEpi/**)"
SRC=$(find NetworkEpi.lean NetworkEpi -name '*.lean' | sort)
if grep -nE '^[[:space:]]*((private|protected|noncomputable|unsafe)[[:space:]]+)*axiom[[:space:]]' $SRC; then
  echo "FAIL: axiom declarations in the trusted library" >&2; status=1
fi
# strip line comments before looking for the tokens; block comments/docstrings are checked by
# the Lean pass (sorryAx), this scan is a fast early warning
if sed -E 's/--.*$//' $SRC | grep -nwE 'sorry|admit' ; then
  echo "FAIL: 'sorry' or 'admit' in the trusted library" >&2; status=1
fi
if ! scan_escape_hatches $SRC; then
  echo "FAIL: escape hatch (unsafe / implemented_by / extern / set_option debug.* / native_decide / #exit) in the trusted library" >&2
  status=1
fi

if [ "$SELFTEST" = 1 ]; then
  echo "== [self-test] the source scan must flag each escape hatch and ignore comments"
  TMPD=$(mktemp -d "${TMPDIR:-/tmp}/nep_gate_scan.XXXXXX")
  n=0
  while IFS= read -r bad; do
    n=$((n + 1))
    printf 'theorem ok : True := trivial\n%s\n' "$bad" >"$TMPD/bad$n.lean"
    if scan_escape_hatches "$TMPD/bad$n.lean" >/dev/null; then
      echo "GATE SELF-TEST FAILED: the source scan missed: $bad" >&2; rm -rf "$TMPD"; exit 1
    fi
  done <<'BAD'
set_option debug.skipKernelTC true in
unsafe def evil : Nat := 0
@[implemented_by evil] def f : Nat := 1
@[extern "c_fn"] opaque g : Nat
theorem h : 2 + 2 = 4 := by native_decide
theorem k : True := Lean.ofReduceBool _ _ rfl
#exit
BAD
  cat >"$TMPD/good.lean" <<'GOOD'
/-- This docstring mentions unsafe code, implemented_by, native_decide and
set_option debug.skipKernelTC, which is fine inside a comment. -/
theorem ok : True := trivial -- a trailing comment about #exit and unsafe
/- a block comment: @[extern "x"] -/
GOOD
  if ! scan_escape_hatches "$TMPD/good.lean"; then
    echo "GATE SELF-TEST FAILED: the source scan flagged a comment" >&2; rm -rf "$TMPD"; exit 1
  fi
  rm -rf "$TMPD"
  echo "source-scan self-test OK ($n escape hatches flagged; comments ignored)"
fi

if [ "$BUILD" = 1 ]; then
  echo "== [2/3] lake build"
  if ! with_alarm lake build >.lake/axiom_gate_build.log 2>&1; then
    echo "BUILD FAILED; errors:" >&2
    grep -E "error" -A6 .lake/axiom_gate_build.log | head -60 >&2
    exit 1
  fi
  tail -1 .lake/axiom_gate_build.log
else
  echo "== [2/3] --no-build: reusing the last build"
fi

if ! with_alarm lake build GateTools >.lake/axiom_gate_tools.log 2>&1; then
  echo "building GateTools failed:" >&2; tail -30 .lake/axiom_gate_tools.log >&2; exit 1
fi

if [ "$SELFTEST" = 1 ]; then
  echo "== [self-test] the gate must reject each deliberately bad name"
  with_alarm lake env lean scripts/AxiomGateSelfTest.lean >.lake/axiom_gate_selftest.log 2>&1
  rc=$?
  grep -E "gate self-test|error" .lake/axiom_gate_selftest.log
  if [ $rc -ne 0 ]; then echo "GATE SELF-TEST FAILED" >&2; exit 1; fi
  echo "gate self-test OK"
fi

echo "== [3/3] #print axioms for CITABLE.txt and every trusted declaration"
if ! with_alarm lake env lean scripts/AxiomGate.lean; then
  echo "AXIOM GATE FAILED" >&2
  exit 1
fi
if [ $status -ne 0 ]; then echo "AXIOM GATE FAILED (source scan)" >&2; exit 1; fi
echo "AXIOM GATE OK"
