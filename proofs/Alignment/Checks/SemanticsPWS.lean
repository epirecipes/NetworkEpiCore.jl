import Alignment.Registry
import Alignment.Shadows.SemanticsPWS

/-!
# Checkers: group `SemanticsPWS` (trusted module `NetworkEpi.Semantics.PWS`)

Checker author (SA-PASS role 3, non-blind). For the four `implemented` claims of
`NetworkEpi/Semantics/PWS.lean`, this file holds the `sa_claim` registration (verbatim registry
text, registry `impl` list), the forward checkers `sa_impl% → Sᵢ`, and the backward checker
`S₁ → … → Sₙ → sa_impl%`, or an `sa_fail_*` record.

No bridges are declared. The blind shadows state every claim with the trusted notions themselves
(`pwSLift`, `pushPW`, `pullPW`, `Rxn.map`, `f2A`, `f2B`, `f2State`) and with the alignment helper
`StrictLaw`, which is built from those notions only.

No failures are recorded. `SemanticsPWS.pwSGlueNotStrict` lists, besides the negated law
`pwS_glue_not_strict_all`, the witness theorem `pwS_glue_not_strict_witness` (a gluing cospan,
injective and jointly surjective, on which the two fields differ, for every `K`), which is S1.

`SemanticsPWS.f2SumSV` passes forward (both readings) and backward, because `f2_sum_sV_all` holds
for every `K`.
-/

open NEP

/-! ## `SemanticsPWS.pwSLiftAppend` -/

namespace Alignment.Shadows.SemanticsPWS.PwSLiftAppend

sa_claim "SemanticsPWS.pwSLiftAppend" group "SemanticsPWS" required
  text "The PW^S field is additive in the reaction list (like the EB lift)."
  impl NEP.pwSLift_append

@[sa_forward "SemanticsPWS.pwSLiftAppend" 1]
theorem fwd1 (h : sa_impl% "SemanticsPWS.pwSLiftAppend") : S1 := by
  intro σ _ K rs₁ rs₂ w
  exact congrArg (fun p : PWS σ => p.1) (h K rs₁ rs₂ w)

@[sa_forward "SemanticsPWS.pwSLiftAppend" 2]
theorem fwd2 (h : sa_impl% "SemanticsPWS.pwSLiftAppend") : S2 := by
  intro σ _ K rs₁ rs₂ w
  exact congrArg (fun p : PWS σ => p.2.1) (h K rs₁ rs₂ w)

@[sa_forward "SemanticsPWS.pwSLiftAppend" 3]
theorem fwd3 (h : sa_impl% "SemanticsPWS.pwSLiftAppend") : S3 := by
  intro σ _ K rs₁ rs₂ w Z
  exact congrArg (fun p : PWS σ => p.2.2.1 Z) (h K rs₁ rs₂ w)

@[sa_forward "SemanticsPWS.pwSLiftAppend" 4]
theorem fwd4 (h : sa_impl% "SemanticsPWS.pwSLiftAppend") : S4 := by
  intro σ _ K rs₁ rs₂ w Z
  exact congrArg (fun p : PWS σ => p.2.2.2 Z) (h K rs₁ rs₂ w)

/-- Both sides are eta-expanded as 4-tuples (structure eta is definitional), then the components
are matched with `congr`/`congrArg`/`funext`. -/
@[sa_backward "SemanticsPWS.pwSLiftAppend"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : sa_impl% "SemanticsPWS.pwSLiftAppend" := by
  intro σ _ K rs₁ rs₂ w
  show ((pwSLift K (rs₁ ++ rs₂) w).1, (pwSLift K (rs₁ ++ rs₂) w).2.1,
      (fun Z => (pwSLift K (rs₁ ++ rs₂) w).2.2.1 Z),
      (fun Z => (pwSLift K (rs₁ ++ rs₂) w).2.2.2 Z)) =
    ((pwSLift K rs₁ w).1 + (pwSLift K rs₂ w).1,
      (pwSLift K rs₁ w).2.1 + (pwSLift K rs₂ w).2.1,
      (fun Z => (pwSLift K rs₁ w).2.2.1 Z + (pwSLift K rs₂ w).2.2.1 Z),
      (fun Z => (pwSLift K rs₁ w).2.2.2 Z + (pwSLift K rs₂ w).2.2.2 Z))
  exact congr (congrArg Prod.mk (s1 K rs₁ rs₂ w))
    (congr (congrArg Prod.mk (s2 K rs₁ rs₂ w))
      (congr (congrArg Prod.mk (funext fun Z => s3 K rs₁ rs₂ w Z))
        (funext fun Z => s4 K rs₁ rs₂ w Z)))

end Alignment.Shadows.SemanticsPWS.PwSLiftAppend

/-! ## `SemanticsPWS.f2GluedSV` -/

namespace Alignment.Shadows.SemanticsPWS.F2GluedSV

sa_claim "SemanticsPWS.f2GluedSV" group "SemanticsPWS" required
  text "The `[sV]` component of the PW^S field of the glued witness model at `f2State` is `−1`."
  impl NEP.f2_glued_sV

/-- S1 is the implementation's statement. -/
@[sa_forward "SemanticsPWS.f2GluedSV" 1]
theorem fwd1 (h : sa_impl% "SemanticsPWS.f2GluedSV") : S1 := h

@[sa_backward "SemanticsPWS.f2GluedSV"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsPWS.f2GluedSV" := s1

end Alignment.Shadows.SemanticsPWS.F2GluedSV

/-! ## `SemanticsPWS.f2SumSV` -/

namespace Alignment.Shadows.SemanticsPWS.F2SumSV

sa_claim "SemanticsPWS.f2SumSV" group "SemanticsPWS" required
  text "The `[sV]` component of the sum of the pushed-forward PW^S fields of `A` and `B` is `0`."
  impl NEP.f2_sum_sV_all

/-- S1 (reading (a), every `K`): `sumSV K` unfolds definitionally to the implementation's
left-hand side at `K`. -/
@[sa_forward "SemanticsPWS.f2SumSV" 1]
theorem fwd1 (h : sa_impl% "SemanticsPWS.f2SumSV") : S1 := by
  intro K
  exact h K

/-- S2 (reading (b), `K = 1`): the implementation at `K = 1`. -/
@[sa_forward "SemanticsPWS.f2SumSV" 2]
theorem fwd2 (h : sa_impl% "SemanticsPWS.f2SumSV") : S2 := h 1

/-- S1 is the implementation up to unfolding `sumSV`; S2 (its `K = 1` instance) is not needed
(`backward_unused_shadows`). -/
@[sa_backward "SemanticsPWS.f2SumSV"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "SemanticsPWS.f2SumSV" := by
  intro K
  exact s1 K

end Alignment.Shadows.SemanticsPWS.F2SumSV

/-! ## `SemanticsPWS.pwSGlueNotStrict` -/

namespace Alignment.Shadows.SemanticsPWS.PwSGlueNotStrict

sa_claim "SemanticsPWS.pwSGlueNotStrict" group "SemanticsPWS" required
  text "**F2: the S-anchored pairwise field is not strict under gluing.** Design statement (DESIGN_NetworkEpiCore.md §D.6): \"**F2/F2′** same for PW, PW^S, PB, clustered EB | **no** (lax) | a contact drains [Z s] (or triangle pairs) for every Z | Lean witness (stretch, L3)\"; §D.4: \"A PW^S contact drains every [Z s] through the closed triple [Z s J]. When B's species are glued in, A's contacts must also drain [Z_B s], which A's system does not contain. So PW^S(glue(A,B)) ≠ glue(PW^S A, PW^S B).\""
  impl NEP.pwS_glue_not_strict_all NEP.pwS_glue_not_strict_witness

/-- S1: the witness theorem at `K` (`IsGlueCospan f g` unfolds to its first conjunct). -/
@[sa_forward "SemanticsPWS.pwSGlueNotStrict" 1]
theorem fwd1 (h : sa_impl% "SemanticsPWS.pwSGlueNotStrict") : S1 :=
  fun K => h.2 K

/-- S2: the witness theorem at `K = 1`. -/
@[sa_forward "SemanticsPWS.pwSGlueNotStrict" 2]
theorem fwd2 (h : sa_impl% "SemanticsPWS.pwSGlueNotStrict") : S2 := h.2 1

/-- Backward: a witness gluing on which the two fields differ refutes the universally quantified
law (instantiate the law at the witness and apply `funext`); the witness conjunct is S1. -/
@[sa_backward "SemanticsPWS.pwSGlueNotStrict"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "SemanticsPWS.pwSGlueNotStrict" := by
  refine ⟨?_, fun K => s1 K⟩
  intro K hlaw
  obtain ⟨σA, σB, σ, iA, dA, iB, dB, d, f, g, A, B, _hc, hne⟩ := s1 K
  exact hne (funext fun w => @hlaw σA σB σ iA dA iB dB d f g A B w)

end Alignment.Shadows.SemanticsPWS.PwSGlueNotStrict
