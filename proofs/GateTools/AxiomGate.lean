import Lean

/-!
# Axiom gate (tooling, not trusted code)

DESIGN_NetworkEpiCore.md §D.7 ("Gate"): "`proofs/CITABLE.txt` lists the citable theorem names.
`proofs/scripts/axiom_gate.sh` builds the project, runs `#print axioms` on each listed name, and
fails on any axiom beyond {propext, Classical.choice, Quot.sound}, on `sorryAx`, or on a name
missing from the build."

`#nep_axiom_gate "CITABLE.txt"` checks, for every listed name:
1. it exists in the build and is a `theorem`;
2. it is declared in a module of the trusted library (`NetworkEpi` or `NetworkEpi.*`);
3. it has a docstring that quotes the design (it contains the marker `Design statement`);
4. `#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound` (so no `sorryAx`);

and, for every declaration of every loaded `NetworkEpi.*` module, that it is not an `axiom` and
depends on no axiom outside the standard three. `#nep_axiom_gate_expect` is the self-test hook
(`scripts/AxiomGateSelfTest.lean`).
-/

open Lean Elab Command

namespace NEPGate

/-- The standard axioms. -/
def allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- Root of the trusted library. -/
def trustedRoot : Name := `NetworkEpi

/-- Marker that a citable docstring must contain. -/
def designMarker : String := "Design statement"

/-- The module that declares `n`, if it is imported. -/
def moduleOf? (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun idx => env.header.moduleNames[idx.toNat]!

/-- Non-empty, non-comment lines of the citable list. -/
def readCitable (path : System.FilePath) : IO (Array String) := do
  let src ← IO.FS.readFile path
  let mut out := #[]
  for line in src.splitOn "\n" do
    let t := line.trimAscii.toString
    unless t.isEmpty || t.startsWith "#" do out := out.push t
  return out

/-- Failures of the per-name checks 1–4 (and an info line with the axioms of each name). -/
def citableFailures (names : Array String) (verbose := true) : CommandElabM (Array String) := do
  let env ← getEnv
  let mut fails : Array String := #[]
  for s in names do
    let n := s.toName
    match env.find? n with
    | none => fails := fails.push s!"{s}: MISSING from the build"
    | some ci =>
      unless ci matches .thmInfo _ do fails := fails.push s!"{s}: not a theorem"
      match moduleOf? env n with
      | some m =>
        unless trustedRoot.isPrefixOf m do
          fails := fails.push s!"{s}: declared in {m}, outside the trusted library"
      | none => fails := fails.push s!"{s}: not declared in an imported module"
      match ← findDocString? env n with
      | none => fails := fails.push s!"{s}: no docstring"
      | some d =>
        unless (d.splitOn designMarker).length > 1 do
          fails := fails.push s!"{s}: the docstring does not quote the design ('{designMarker}')"
      let axs ← collectAxioms n
      if verbose then
        logInfo m!"'{n}' depends on axioms: {(axs.qsort Name.lt).toList}"
      for a in axs do
        unless allowed.contains a do fails := fails.push s!"{s}: depends on the axiom {a}"
  return fails

/-- Scan every declaration of every loaded trusted module. Returns the failures, the number of
declarations, the trusted modules and the axioms used. -/
def libraryScan : CommandElabM (Array String × Nat × Array Name × Array Name) := do
  let env ← getEnv
  let mut fails : Array String := #[]
  let mut st : CollectAxioms.State := {}
  let mut count := 0
  let mut mods : Array Name := #[]
  for idx in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[idx]!
    if trustedRoot.isPrefixOf m then
      mods := mods.push m
      for c in env.header.moduleData[idx]!.constNames do
        count := count + 1
        if let some (.axiomInfo _) := env.find? c then
          fails := fails.push s!"{c}: an axiom declared in the trusted module {m}"
        let (_, st') := ((CollectAxioms.collect c).run env).run st
        st := st'
  for a in st.axioms do
    unless allowed.contains a do
      fails := fails.push s!"the trusted library depends on the axiom {a}"
  return (fails, count, mods, st.axioms.qsort Name.lt)

/-- Run the gate on a citable list; throws on any failure. -/
elab "#nep_axiom_gate " path:str : command => do
  let names ← readCitable path.getString
  let mut fails ← citableFailures names
  if names.isEmpty then fails := fails.push s!"{path.getString} lists no names"
  let (lfails, count, mods, axs) ← libraryScan
  fails := fails ++ lfails
  if mods.isEmpty then fails := fails.push "no trusted module (NetworkEpi.*) is loaded"
  logInfo m!"trusted modules: {mods.toList}"
  if fails.isEmpty then
    logInfo m!"AXIOM GATE PASSED: {names.size} citable theorems; {count} declarations in \
      {mods.size} trusted modules; axioms used: {axs.toList}"
  else
    throwError m!"AXIOM GATE FAILED ({fails.size}):\n{"\n".intercalate fails.toList}"

/-- Self-test hook: `#nep_axiom_gate_expect "name" "expected failure substring"` succeeds iff the
per-name checks on `name` report a failure containing the substring (or, with the substring
`"PASS"`, iff they report no failure). -/
elab "#nep_axiom_gate_expect " name:str expect:str : command => do
  let fails ← citableFailures #[name.getString] (verbose := false)
  let e := expect.getString
  if e == "PASS" then
    unless fails.isEmpty do
      throwError m!"gate self-test: expected {name.getString} to pass, got {fails.toList}"
  else
    unless fails.any (fun f => (f.splitOn e).length > 1) do
      throwError m!"gate self-test: expected a failure containing '{e}' for {name.getString}, \
        got {fails.toList}"
  logInfo m!"gate self-test ok: {name.getString} -> {if e == "PASS" then "pass" else e}"

end NEPGate
