import Alignment.Registry
import Alignment.Example.ExampleShadows

/-!
# Worked example: claim registration, bridge and checkers (template for `Checks/<Group>.lean`)

The checker author may read everything. For each claim:

1. `sa_claim` with the verbatim `claims.yaml` text and the `impl` list;
2. bridges (`@[sa_bridge "c"]`, any tactics, must not use implementation theorems) where the
   text's notion is not definitionally our definition;
3. forward checkers `(h : sa_impl% "c") : Sᵢ` and one backward checker
   `(s₁ : S₁) … (sₙ : Sₙ) : sa_impl% "c"`, with structural proofs: hypotheses, the logic glue of
   `coreLogicWhitelist`, definitional unfolding (`show`, `change`, `unfold`, `rfl`), and reviewed
   bridges for the claim. No library lemmas, no `simp`/`ring`/`omega`/`decide`/`linarith`.
4. If a check is genuinely false, record `sa_fail_forward "c" i "<reason>"` (or
   `sa_fail_backward`) instead of forcing it.

Checkers must live in the module that runs `sa_claim`. Do not write review records here: an
independent reviewer adds them to `Alignment/ReviewedBridges.lean`.
-/

open NEP

namespace Alignment.Example.AdmissibleType

sa_claim "EXAMPLE.admissibleType" group "Example" required
  text "EB-admissibility is membership of the reaction's type in T_EB: \"the sub-theory with no arrow into Sus\" (DESIGN §B.2)."
  impl NEP.NRxn.ebAdmissible_iff_type

/-- Bridge: our `TNet.inTEB t = true` is the text's "t ∈ T_EB = {contact, exit, progress,
remove}". The right-hand side is not definitionally `TNet.inTEB t = true` (a four-way
disjunction versus a Boolean match), so the checkers need this bridge. -/
@[sa_bridge "EXAMPLE.admissibleType"]
theorem bridge_inTEB (t : TNet) : TNet.inTEB t = true ↔ InTEB t := by
  cases t <;> simp [TNet.inTEB, InTEB]

@[sa_forward "EXAMPLE.admissibleType" 1]
theorem fwd1 (h : sa_impl% "EXAMPLE.admissibleType") : S1 :=
  fun r hr => (bridge_inTEB r.type).mp ((h r).mp hr)

@[sa_forward "EXAMPLE.admissibleType" 2]
theorem fwd2 (h : sa_impl% "EXAMPLE.admissibleType") : S2 :=
  fun r ht => (h r).mpr ((bridge_inTEB r.type).mpr ht)

@[sa_backward "EXAMPLE.admissibleType"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "EXAMPLE.admissibleType" :=
  fun r => ⟨fun hr => (bridge_inTEB r.type).mpr (s1 r hr),
    fun ht => s2 r ((bridge_inTEB r.type).mp ht)⟩

end Alignment.Example.AdmissibleType

namespace Alignment.Example.NotAdmissible

sa_claim "EXAMPLE.notAdmissible" group "Example" required
  text "Resusceptibility `X → s` (§B.2 type `:resus`, e.g. SIS `I → S`) is not EB-admissible [...] A node contact `X + J → Y + J` with a node-species recipient (§B.2 type `:node_contact`) is not EB-admissible."
  impl NEP.NRxn.not_ebAdmissible_resus NEP.NRxn.not_ebAdmissible_nodeContact

@[sa_forward "EXAMPLE.notAdmissible" 1]
theorem fwd1 (h : sa_impl% "EXAMPLE.notAdmissible") : S1 := fun X a => h.1 X a

@[sa_forward "EXAMPLE.notAdmissible" 2]
theorem fwd2 (h : sa_impl% "EXAMPLE.notAdmissible") : S2 := fun X J Y τ => h.2 X J Y τ

@[sa_backward "EXAMPLE.notAdmissible"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "EXAMPLE.notAdmissible" :=
  ⟨fun X a => s1 X a, fun X J Y τ => s2 X J Y τ⟩

end Alignment.Example.NotAdmissible

namespace Alignment.Example.RoundTrip

sa_claim "EXAMPLE.roundTrip" group "Example" required
  text "An EB-admissible T_net reaction comes from T_EB syntax."
  impl NEP.NRxn.eq_toNRxn_of_ebAdmissible

@[sa_forward "EXAMPLE.roundTrip" 1]
theorem fwd1 (h : sa_impl% "EXAMPLE.roundTrip") : S1 := fun hr => h hr

@[sa_backward "EXAMPLE.roundTrip"]
theorem bwd (s1 : S1) : sa_impl% "EXAMPLE.roundTrip" := fun hr => s1 hr

/-- Satisfiability witness for the hypothesis `r.EBAdmissible`, which the implementation and the
shadow share: the contact `s + I → I + I` over `Unit` is admissible. The statement is
`∃ x₁ … xₖ, True` over the implementation's binders up to its last hypothesis; any tactic may be
used. Without it the claim gets the hint `witness_missing`. -/
@[sa_witness "EXAMPLE.roundTrip" 1]
theorem witness :
    ∃ (σ : Type) (r : NRxn σ) (_ : r.EBAdmissible), True :=
  ⟨Unit, .contact () () 1, rfl, trivial⟩

end Alignment.Example.RoundTrip
