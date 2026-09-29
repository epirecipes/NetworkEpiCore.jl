import NetworkEpi
import GateTools.AxiomGate

/-! Self-test of the axiom gate: every deliberately bad name must be rejected with the stated
reason, and a good one must pass. Run by `scripts/axiom_gate.sh --self-test`. The declarations
below live in this file only (not in the trusted library). -/

/-- Design statement: none (a self-test theorem proved with `sorry`). -/
theorem gateSelfTestSorry : (2 : ℕ) + 2 = 5 := by sorry

/-- A self-test axiom. -/
axiom gateSelfTestAx : False

/-- Design statement: none (a self-test theorem using a non-standard axiom). -/
theorem gateSelfTestUsesAx : (1 : ℕ) = 2 := gateSelfTestAx.elim

#nep_axiom_gate_expect "NEP.Semiconj.map_solution" "PASS"
#nep_axiom_gate_expect "NEP.conservation" "PASS"
#nep_axiom_gate_expect "NEP.noSuchTheorem" "MISSING"
#nep_axiom_gate_expect "NEP.dynCategory" "not a theorem"
#nep_axiom_gate_expect "NEP.lift" "not a theorem"
#nep_axiom_gate_expect "Nat.add_comm" "outside the trusted library"
#nep_axiom_gate_expect "NEP.Rxn.contact.injEq" "no docstring"
#nep_axiom_gate_expect "NEP.hasDerivWithinAt_edgeDefect" "does not quote the design"
#nep_axiom_gate_expect "gateSelfTestSorry" "sorryAx"
#nep_axiom_gate_expect "gateSelfTestUsesAx" "gateSelfTestAx"
#nep_axiom_gate_expect "gateSelfTestUsesAx" "not declared in an imported module"
