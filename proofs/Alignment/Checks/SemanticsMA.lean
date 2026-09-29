import Alignment.Registry
import Alignment.Shadows.SemanticsMA

/-!
# Checkers: group `SemanticsMA` (trusted module `NetworkEpi.Semantics.MA`)

Checker author (SA-PASS role 3, non-blind). For the five `implemented` claims of
`NetworkEpi/Semantics/MA.lean`, this file holds the `sa_claim` registration (verbatim registry
text, registry `impl` list), the forward checkers `sa_impl% → Sᵢ` and the backward checker
`S₁ → … → Sₙ → sa_impl%`.

No bridges are declared. The blind shadows state every claim with the trusted notions themselves
(`maLift`, `maField`, `pushMA`, `pullMA`, `NRxn.map`, `MA`), so no trusted definition has to be
identified with a notion of the text. No failures are recorded.

Remarks for the reviewer:

* `SemanticsMA.pushMAAdd`, `SemanticsMA.pushMAZero`: the single shadow is literally the
  implementation statement (the audit reports `identical_to_impl`: weak evidence of independence,
  but the text admits no other reading). The three `maLiftAppend` shadows are the three
  implementation statements, one per conjunct of `sa_impl%`, up to the order of instance binders.
* `SemanticsMA.elimMap`: the shadows are `Option.map`/`Option.elim` facts that hold by `rfl`
  and mention the trusted library only through the binder type `NEP.MA`. The checkers use `h`
  and the shadows relevantly, but the claim is weak evidence: no implementation could falsify
  the shadows.
-/

open NEP

/-! ## `SemanticsMA.maLiftAppend` -/

namespace Alignment.Shadows.SemanticsMA.MaLiftAppend

sa_claim "SemanticsMA.maLiftAppend" group "SemanticsMA" required
  text "**H1′ for mass action, part 1: the MA lift is additive in the reaction list.** Design statement (DESIGN_NetworkEpiCore.md §D.6): \"H1′ same for MA, IB, Stoch | yes | same argument\"; §D.4, table row MA, column \"Strict under gluing?\": \"**yes** (Baez–Pollard 2017)\". [...] **H1′ for mass action, part 2: the MA lift is natural in species maps.** Design statement (DESIGN_NetworkEpiCore.md §D.6): \"H1′ same for MA, IB, Stoch | yes | same argument\" (the argument of H1: \"local per-reaction fields\"). [...] **H1′ for mass action: the MA lift is strict under gluing.** Design statement (DESIGN_NetworkEpiCore.md §D.6): \"H1′ same for MA, IB, Stoch | yes | same argument\", where H1 is \"EB(glue(A,B)) = glue(EB A, EB B)\"; §D.4, table row MA, column \"Strict under gluing?\": \"**yes** (Baez–Pollard 2017)\"; §D.3 (open systems): \"composition identifies ported coordinates and **adds** vector fields\". [...] Scope: of the design's \"H1′ same for MA, IB, Stoch\", only the mass-action case is formalised; the individual-based (IB) and stochastic semantics are not part of this library."
  impl NEP.maLift_append NEP.maLift_map NEP.maLift_glue

@[sa_forward "SemanticsMA.maLiftAppend" 1]
theorem fwd1 (h : sa_impl% "SemanticsMA.maLiftAppend") : S1 := by
  intro σ _ rs₁ rs₂ u
  exact h.1 rs₁ rs₂ u

@[sa_forward "SemanticsMA.maLiftAppend" 2]
theorem fwd2 (h : sa_impl% "SemanticsMA.maLiftAppend") : S2 := by
  intro σ σ' _ _ _ f rs u
  exact h.2.1 f rs u

@[sa_forward "SemanticsMA.maLiftAppend" 3]
theorem fwd3 (h : sa_impl% "SemanticsMA.maLiftAppend") : S3 := by
  intro σA σB σ _ _ _ _ _ f g rsA rsB u
  exact h.2.2 f g rsA rsB u

@[sa_backward "SemanticsMA.maLiftAppend"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) : sa_impl% "SemanticsMA.maLiftAppend" := by
  refine ⟨?_, ?_, ?_⟩
  · intro σ _ rs rs' u
    exact s1 rs rs' u
  · intro σ σ' _ _ _ f rs u
    exact s2 f rs u
  · intro σA σB σ _ _ _ _ _ f g A B u
    exact s3 f g A B u

end Alignment.Shadows.SemanticsMA.MaLiftAppend

/-! ## `SemanticsMA.pushMAAdd` -/

namespace Alignment.Shadows.SemanticsMA.PushMAAdd

sa_claim "SemanticsMA.pushMAAdd" group "SemanticsMA" required
  text "The pushforward of MA coordinates is additive."
  impl NEP.pushMA_add

@[sa_forward "SemanticsMA.pushMAAdd" 1]
theorem fwd1 (h : sa_impl% "SemanticsMA.pushMAAdd") : S1 := by
  intro σ σ' _ _ f u v
  exact h f u v

@[sa_backward "SemanticsMA.pushMAAdd"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsMA.pushMAAdd" := by
  intro σ σ' _ _ f u v
  exact s1 f u v

end Alignment.Shadows.SemanticsMA.PushMAAdd

/-! ## `SemanticsMA.pushMAZero` -/

namespace Alignment.Shadows.SemanticsMA.PushMAZero

sa_claim "SemanticsMA.pushMAZero" group "SemanticsMA" required
  text "The pushforward of the zero MA vector is zero."
  impl NEP.pushMA_zero

@[sa_forward "SemanticsMA.pushMAZero" 1]
theorem fwd1 (h : sa_impl% "SemanticsMA.pushMAZero") : S1 := by
  intro σ σ' _ _ f
  exact h f

@[sa_backward "SemanticsMA.pushMAZero"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsMA.pushMAZero" := by
  intro σ σ' _ _ f
  exact s1 f

end Alignment.Shadows.SemanticsMA.PushMAZero

/-! ## `SemanticsMA.elimMap` -/

namespace Alignment.Shadows.SemanticsMA.ElimMap

sa_claim "SemanticsMA.elimMap" group "SemanticsMA" required
  text "Reading a catalyst density after relabelling: `J = none` (the susceptible species) gives `S`, `J = some X` gives `x (f X)`."
  impl NEP.elim_map

/-- The `none` instance of `elim_map`: its right-hand side `none.elim u.1 (u.2 ∘ f)` reduces
to `u.1`. -/
@[sa_forward "SemanticsMA.elimMap" 1]
theorem fwd1 (h : sa_impl% "SemanticsMA.elimMap") : S1 := by
  intro σ σ' f u
  exact h f none u.1 u.2

/-- The `some X` instance of `elim_map`: its right-hand side `(some X).elim u.1 (u.2 ∘ f)`
reduces to `u.2 (f X)`. -/
@[sa_forward "SemanticsMA.elimMap" 2]
theorem fwd2 (h : sa_impl% "SemanticsMA.elimMap") : S2 := by
  intro σ σ' f u X
  exact h f (some X) u.1 u.2

/-- Case split on the catalyst; each case is the corresponding shadow at the state `(S, x)`. -/
@[sa_backward "SemanticsMA.elimMap"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "SemanticsMA.elimMap" := by
  intro σ σ' f J S x
  cases J with
  | none => exact s1 f (S, x)
  | some X => exact s2 f (S, x) X

end Alignment.Shadows.SemanticsMA.ElimMap

/-! ## `SemanticsMA.maFieldMap` -/

namespace Alignment.Shadows.SemanticsMA.MaFieldMap

sa_claim "SemanticsMA.maFieldMap" group "SemanticsMA" required
  text "Naturality of the per-reaction mass-action field in species maps: the field of `r.map f` at `u` is the pushforward of the field of `r` at `pullMA f u`."
  impl NEP.maField_map

@[sa_forward "SemanticsMA.maFieldMap" 1]
theorem fwd1 (h : sa_impl% "SemanticsMA.maFieldMap") : S1 := by
  intro σ σ' _ _ _ f J X τ u
  exact h f (NRxn.contact J X τ) u

@[sa_forward "SemanticsMA.maFieldMap" 2]
theorem fwd2 (h : sa_impl% "SemanticsMA.maFieldMap") : S2 := by
  intro σ σ' _ _ _ f Y ν u
  exact h f (NRxn.exit Y ν) u

@[sa_forward "SemanticsMA.maFieldMap" 3]
theorem fwd3 (h : sa_impl% "SemanticsMA.maFieldMap") : S3 := by
  intro σ σ' _ _ _ f X Y a u
  exact h f (NRxn.trans X (some Y) a) u

@[sa_forward "SemanticsMA.maFieldMap" 4]
theorem fwd4 (h : sa_impl% "SemanticsMA.maFieldMap") : S4 := by
  intro σ σ' _ _ _ f X a u
  exact h f (NRxn.trans X none a) u

@[sa_forward "SemanticsMA.maFieldMap" 5]
theorem fwd5 (h : sa_impl% "SemanticsMA.maFieldMap") : S5 := by
  intro σ σ' _ _ _ f X a u
  exact h f (NRxn.resus X a) u

@[sa_forward "SemanticsMA.maFieldMap" 6]
theorem fwd6 (h : sa_impl% "SemanticsMA.maFieldMap") : S6 := by
  intro σ σ' _ _ _ f X J Y τ u
  exact h f (NRxn.nodeContact X J Y τ) u

/-- Case split on the reaction (and on the product of `trans`); each case is a shadow. -/
@[sa_backward "SemanticsMA.maFieldMap"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) :
    sa_impl% "SemanticsMA.maFieldMap" := by
  intro σ σ' _ _ _ f r u
  cases r with
  | contact J X τ => exact s1 f J X τ u
  | exit Y ν => exact s2 f Y ν u
  | trans X Y a =>
    cases Y with
    | none => exact s4 f X a u
    | some Y => exact s3 f X Y a u
  | resus X a => exact s5 f X a u
  | nodeContact X J Y τ => exact s6 f X J Y τ u


end Alignment.Shadows.SemanticsMA.MaFieldMap
