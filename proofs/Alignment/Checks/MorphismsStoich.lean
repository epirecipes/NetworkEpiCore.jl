import Alignment.Registry
import Alignment.Shadows.MorphismsStoich
import NetworkEpi

/-!
# Checkers: group `MorphismsStoich` (trusted module `NetworkEpi.Morphisms.Stoich`)

Checker author (SA-PASS role 3, non-blind). This file registers the five `implemented` claims of
`NetworkEpi/Morphisms/Stoich.lean` with `sa_claim` (verbatim registry text, registry `impl`
list), and holds the forward checkers `sa_impl% → Sᵢ` and the backward checkers
`S₁ → … → Sₙ → sa_impl%`.

The shadows state the coordinate identification "`none` is the susceptible species" as the
alignment-library function `optCoords` (`none ↦ S`, `some X ↦ x_X`). The module's `maToS` is
identified with it by the helper `maToS_eq_optCoords`. That helper is proved structurally
(`funext`, a case split on `Option`, `rfl`), so it needs no bridge.

There is one bridge, `MaEqStoich.bridge_isSemiconj_linear`, for `MorphismsStoich.maEqStoich`. It
needs independent review. The implementation `ma_eq_stoich` states the agreement as the trusted
Dyn morphism predicate `IsSemiconj` (differentiability plus `Dπ(u)·F(u) = G(π u)`, DESIGN §D.3).
The text and shadow S7 state it as a correspondence of vector fields, `π (F u) = G (π u)`. The
two are the same when `π` is a continuous linear map, but only calculus lemmas show it, and
those are not structural. No failures are recorded.

`import NetworkEpi` loads the trusted root. The audit computes the trusted modules by walking
the imports of `NetworkEpi.lean` from the root (`NetworkEpi.Morphisms.All` imports
`NetworkEpi.Morphisms.Stoich`). Without that import, an environment that loads only
`NetworkEpi.Morphisms.Stoich` flags every implementation as `impl_untrusted`.

Remarks for the reviewer:

* `sLiftAppend`, `sLiftFlatMap` and `maToSLApply` each have one shadow that is literally the
  implementation statement, up to binder order (`identical_to_impl`: weak evidence of
  independence, but the texts leave no other reading).
-/

open NEP

namespace Alignment.Shadows.MorphismsStoich

/-- The module's coordinate map `maToS` is the text's identification `optCoords` (`none ↦ S`,
`some X ↦ x_X`). Proved structurally by function extensionality and a case split on `Option`:
both sides reduce to `u.1` at `none` and to `u.2 X` at `some X`. -/
theorem maToS_eq_optCoords {σ : Type} (u : MA σ) : maToS u = optCoords u := by
  funext i
  cases i with
  | none => rfl
  | some X => rfl

end Alignment.Shadows.MorphismsStoich

/-! ## `MorphismsStoich.sLiftAppend` -/

namespace Alignment.Shadows.MorphismsStoich.SLiftAppend

sa_claim "MorphismsStoich.sLiftAppend" group "MorphismsStoich" required
  text "The multiset mass-action field is additive in the reaction list."
  impl NEP.sLift_append

@[sa_forward "MorphismsStoich.sLiftAppend" 1]
theorem fwd1 (h : sa_impl% "MorphismsStoich.sLiftAppend") : S1 := by
  intro ι _ rs₁ rs₂ x
  exact h rs₁ rs₂ x

@[sa_backward "MorphismsStoich.sLiftAppend"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsStoich.sLiftAppend" := by
  intro ι _ rs rs' x
  exact s1 rs rs' x

end Alignment.Shadows.MorphismsStoich.SLiftAppend

/-! ## `MorphismsStoich.sLiftFlatMap` -/

namespace Alignment.Shadows.MorphismsStoich.SLiftFlatMap

sa_claim "MorphismsStoich.sLiftFlatMap" group "MorphismsStoich" required
  text "The multiset mass-action field of `rs.flatMap g` is the sum over `r ∈ rs` of the fields of `g r`."
  impl NEP.sLift_flatMap

@[sa_forward "MorphismsStoich.sLiftFlatMap" 1]
theorem fwd1 (h : sa_impl% "MorphismsStoich.sLiftFlatMap") : S1 := by
  intro α ι _ rs g x
  exact h g rs x

@[sa_backward "MorphismsStoich.sLiftFlatMap"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsStoich.sLiftFlatMap" := by
  intro ι _ ρ g rs x
  exact s1 rs g x

end Alignment.Shadows.MorphismsStoich.SLiftFlatMap

/-! ## `MorphismsStoich.maToSLApply` -/

namespace Alignment.Shadows.MorphismsStoich.MaToSLApply

sa_claim "MorphismsStoich.maToSLApply" group "MorphismsStoich" required
  text "`maToSL` is `maToS`."
  impl NEP.maToSL_apply

@[sa_forward "MorphismsStoich.maToSLApply" 1]
theorem fwd1 (h : sa_impl% "MorphismsStoich.maToSLApply") : S1 := by
  intro σ u
  exact h u

@[sa_backward "MorphismsStoich.maToSLApply"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsStoich.maToSLApply" := by
  intro σ u
  exact s1 u

end Alignment.Shadows.MorphismsStoich.MaToSLApply

/-! ## `MorphismsStoich.maFieldToSRxn` -/

namespace Alignment.Shadows.MorphismsStoich.MaFieldToSRxn

sa_claim "MorphismsStoich.maFieldToSRxn" group "MorphismsStoich" required
  text "Per reaction, the `NRxn` mass-action field is the multiset mass-action field."
  impl NEP.maField_toSRxn

/-- Transport an implementation instance `maToS (maField r u) = field (maToS u)` to the
`optCoords` form of the shadows. -/
theorem toOpt {σ : Type} [DecidableEq σ] (r : NRxn σ) (u : MA σ)
    (e : maToS (maField r u) = (NRxn.toSRxn r).field (maToS u)) :
    optCoords (maField r u) = (NRxn.toSRxn r).field (optCoords u) := by
  rw [← maToS_eq_optCoords (maField r u), ← maToS_eq_optCoords u]
  exact e

/-- Transport a shadow instance in the `optCoords` form back to the `maToS` form. -/
theorem ofOpt {σ : Type} [DecidableEq σ] (r : NRxn σ) (u : MA σ)
    (e : optCoords (maField r u) = (NRxn.toSRxn r).field (optCoords u)) :
    maToS (maField r u) = (NRxn.toSRxn r).field (maToS u) := by
  rw [maToS_eq_optCoords (maField r u), maToS_eq_optCoords u]
  exact e

@[sa_forward "MorphismsStoich.maFieldToSRxn" 1]
theorem fwd1 (h : sa_impl% "MorphismsStoich.maFieldToSRxn") : S1 := by
  intro σ _ J X τ u
  exact toOpt (NRxn.contact J X τ) u (h (NRxn.contact J X τ) u)

@[sa_forward "MorphismsStoich.maFieldToSRxn" 2]
theorem fwd2 (h : sa_impl% "MorphismsStoich.maFieldToSRxn") : S2 := by
  intro σ _ Y ν u
  exact toOpt (NRxn.exit Y ν) u (h (NRxn.exit Y ν) u)

@[sa_forward "MorphismsStoich.maFieldToSRxn" 3]
theorem fwd3 (h : sa_impl% "MorphismsStoich.maFieldToSRxn") : S3 := by
  intro σ _ X Y a u
  exact toOpt (NRxn.trans X (some Y) a) u (h (NRxn.trans X (some Y) a) u)

@[sa_forward "MorphismsStoich.maFieldToSRxn" 4]
theorem fwd4 (h : sa_impl% "MorphismsStoich.maFieldToSRxn") : S4 := by
  intro σ _ X a u
  exact toOpt (NRxn.trans X none a) u (h (NRxn.trans X none a) u)

@[sa_forward "MorphismsStoich.maFieldToSRxn" 5]
theorem fwd5 (h : sa_impl% "MorphismsStoich.maFieldToSRxn") : S5 := by
  intro σ _ X a u
  exact toOpt (NRxn.resus X a) u (h (NRxn.resus X a) u)

@[sa_forward "MorphismsStoich.maFieldToSRxn" 6]
theorem fwd6 (h : sa_impl% "MorphismsStoich.maFieldToSRxn") : S6 := by
  intro σ _ X J Y τ u
  exact toOpt (NRxn.nodeContact X J Y τ) u (h (NRxn.nodeContact X J Y τ) u)

/-- Case split on the reaction form (and on the product of `trans`). Each case is the
corresponding shadow, moved back from `optCoords` to `maToS`. -/
@[sa_backward "MorphismsStoich.maFieldToSRxn"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) :
    sa_impl% "MorphismsStoich.maFieldToSRxn" := by
  intro σ _ r u
  cases r with
  | contact J X τ => exact ofOpt _ u (s1 J X τ u)
  | exit Y ν => exact ofOpt _ u (s2 Y ν u)
  | trans X Y a =>
    cases Y with
    | some Y => exact ofOpt _ u (s3 X Y a u)
    | none => exact ofOpt _ u (s4 X a u)
  | resus X a => exact ofOpt _ u (s5 X a u)
  | nodeContact X J Y τ => exact ofOpt _ u (s6 X J Y τ u)

end Alignment.Shadows.MorphismsStoich.MaFieldToSRxn

/-! ## `MorphismsStoich.maEqStoich` -/

namespace Alignment.Shadows.MorphismsStoich.MaEqStoich

sa_claim "MorphismsStoich.maEqStoich" group "MorphismsStoich" required
  text "**The multiset mass-action semantics agrees with `maField`.** Design statement (DESIGN_NetworkEpiCore.md §D.4, row MA): \"**MA** | Open(Petri) | x_X | total\"; §D.7, \"Honest feasibility\": \"The hard parts are [...] the multiset stoichiometry for D_μ\". [...] So `sSys` extends the library's mass-action semantics to reactions with several products. [...] every T_net reaction `NRxn σ` is a multiset reaction over `Option σ` (`none` is the susceptible species) with the same mass-action field."
  impl NEP.ma_eq_stoich NEP.maField_toSRxn

/-- Bridge (needs independent review). For a map `π` that is (the coercion of) a continuous
linear map `L`, the trusted Dyn morphism predicate `IsSemiconj A B π` (DESIGN §D.3:
"`Dπ(u)·F(u) = G(π(u))`", with `π` differentiable) is exactly the correspondence of vector
fields `π (F u) = G (π u)` for every `u`. That correspondence is how the text and shadow S7
read "`sSys` extends the library's mass-action semantics". The bridge is sound because a
continuous linear map is differentiable and is its own derivative at every point
(`ContinuousLinearMap.differentiable`, `ContinuousLinearMap.fderiv`). -/
@[sa_bridge "MorphismsStoich.maEqStoich"]
theorem bridge_isSemiconj_linear (A B : DynSys) (π : A.V → B.V) (L : A.V →L[ℝ] B.V)
    (hL : ⇑L = π) : IsSemiconj A B π ↔ ∀ u, π (A.F u) = B.F (π u) := by
  subst hL
  constructor
  · rintro ⟨_, h⟩ u
    rw [← h u, L.fderiv]
  · intro h
    exact ⟨L.differentiable, fun u => by rw [L.fderiv]; exact h u⟩

/-- The coercion of the continuous linear map `maToSL` is `maToS`, proved structurally
(function extensionality and a case split on `Option`; both sides reduce definitionally to
`u.1` at `none` and to `u.2 X` at `some X`). -/
theorem coe_maToSL {σ : Type} : ⇑(maToSL (σ := σ)) = maToS := by
  funext u i
  cases i with
  | none => rfl
  | some X => rfl

/-- The field correspondence along `maToS`, moved to the `optCoords` form of S7. -/
theorem fieldToOpt {σ : Type} [Fintype σ] [DecidableEq σ] (rs : List (NRxn σ)) (u : MA σ)
    (e : maToS ((maSys rs).F u) = (sSys (rs.map NRxn.toSRxn)).F (maToS u)) :
    (sSys (rs.map NRxn.toSRxn)).F (optCoords u) = optCoords ((maSys rs).F u) := by
  rw [← maToS_eq_optCoords ((maSys rs).F u), ← maToS_eq_optCoords u]
  exact e.symm

/-- The `optCoords` form of S7, moved back to the field correspondence along `maToS`. -/
theorem fieldOfOpt {σ : Type} [Fintype σ] [DecidableEq σ] (rs : List (NRxn σ)) (u : MA σ)
    (e : (sSys (rs.map NRxn.toSRxn)).F (optCoords u) = optCoords ((maSys rs).F u)) :
    maToS ((maSys rs).F u) = (sSys (rs.map NRxn.toSRxn)).F (maToS u) := by
  rw [maToS_eq_optCoords ((maSys rs).F u), maToS_eq_optCoords u]
  exact e.symm

@[sa_forward "MorphismsStoich.maEqStoich" 1]
theorem fwd1 (h : sa_impl% "MorphismsStoich.maEqStoich") : S1 := by
  intro σ _ J X τ u
  exact MaFieldToSRxn.toOpt (NRxn.contact J X τ) u (h.2 (NRxn.contact J X τ) u)

@[sa_forward "MorphismsStoich.maEqStoich" 2]
theorem fwd2 (h : sa_impl% "MorphismsStoich.maEqStoich") : S2 := by
  intro σ _ Y ν u
  exact MaFieldToSRxn.toOpt (NRxn.exit Y ν) u (h.2 (NRxn.exit Y ν) u)

@[sa_forward "MorphismsStoich.maEqStoich" 3]
theorem fwd3 (h : sa_impl% "MorphismsStoich.maEqStoich") : S3 := by
  intro σ _ X Y a u
  exact MaFieldToSRxn.toOpt (NRxn.trans X (some Y) a) u (h.2 (NRxn.trans X (some Y) a) u)

@[sa_forward "MorphismsStoich.maEqStoich" 4]
theorem fwd4 (h : sa_impl% "MorphismsStoich.maEqStoich") : S4 := by
  intro σ _ X a u
  exact MaFieldToSRxn.toOpt (NRxn.trans X none a) u (h.2 (NRxn.trans X none a) u)

@[sa_forward "MorphismsStoich.maEqStoich" 5]
theorem fwd5 (h : sa_impl% "MorphismsStoich.maEqStoich") : S5 := by
  intro σ _ X a u
  exact MaFieldToSRxn.toOpt (NRxn.resus X a) u (h.2 (NRxn.resus X a) u)

@[sa_forward "MorphismsStoich.maEqStoich" 6]
theorem fwd6 (h : sa_impl% "MorphismsStoich.maEqStoich") : S6 := by
  intro σ _ X J Y τ u
  exact MaFieldToSRxn.toOpt (NRxn.nodeContact X J Y τ) u (h.2 (NRxn.nodeContact X J Y τ) u)

/-- `ma_eq_stoich` gives `IsSemiconj (maSys rs) (sSys (rs.map NRxn.toSRxn)) maToS`. The
reviewed bridge (with `L = maToSL`) turns it into the field correspondence along `maToS`,
which is S7 once `maToS` is identified with `optCoords`. -/
@[sa_forward "MorphismsStoich.maEqStoich" 7]
theorem fwd7 (h : sa_impl% "MorphismsStoich.maEqStoich") : S7 := by
  intro σ _ _ rs u
  exact fieldToOpt rs u
    ((bridge_isSemiconj_linear (maSys rs) (sSys (rs.map NRxn.toSRxn)) maToS maToSL coe_maToSL).mp
      (h.1 rs) u)

/-- First conjunct (`ma_eq_stoich`): S7 and the bridge give `IsSemiconj`. Second conjunct
(`maField_toSRxn`): a case split on the reaction form, using S1–S6. -/
@[sa_backward "MorphismsStoich.maEqStoich"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) (s7 : S7) :
    sa_impl% "MorphismsStoich.maEqStoich" := by
  refine ⟨?_, ?_⟩
  · intro σ _ _ rs
    exact (bridge_isSemiconj_linear (maSys rs) (sSys (rs.map NRxn.toSRxn)) maToS maToSL
      coe_maToSL).mpr (fun u => fieldOfOpt rs u (s7 rs u))
  · intro σ _ r u
    cases r with
    | contact J X τ => exact MaFieldToSRxn.ofOpt _ u (s1 J X τ u)
    | exit Y ν => exact MaFieldToSRxn.ofOpt _ u (s2 Y ν u)
    | trans X Y a =>
      cases Y with
      | some Y => exact MaFieldToSRxn.ofOpt _ u (s3 X Y a u)
      | none => exact MaFieldToSRxn.ofOpt _ u (s4 X a u)
    | resus X a => exact MaFieldToSRxn.ofOpt _ u (s5 X a u)
    | nodeContact X J Y τ => exact MaFieldToSRxn.ofOpt _ u (s6 X J Y τ u)

end Alignment.Shadows.MorphismsStoich.MaEqStoich
