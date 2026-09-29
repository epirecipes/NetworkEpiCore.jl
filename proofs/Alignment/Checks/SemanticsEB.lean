import Alignment.Registry
import Alignment.Shadows.SemanticsEB
-- the four field lemmas cited by `SemanticsEB.header.fieldTable` live in `Semantics.Solutions`
import NetworkEpi.Semantics.Solutions

/-!
# Checkers: group `SemanticsEB` (trusted module `NetworkEpi.Semantics.EB`)

Checker author (SA-PASS role 3, non-blind). For each `implemented` claim of
`NetworkEpi/Semantics/EB.lean` (and the four field lemmas of `NetworkEpi.Semantics.Solutions`
cited by `SemanticsEB.header.fieldTable`), this file holds the `sa_claim` registration (verbatim
registry text, registry `impl` list in registry order), the bridges, the forward checkers
`sa_impl% → Sᵢ` and the backward checker `S₁ → … → Sₙ → sa_impl%`, or `sa_fail_*` records.

## Bridges (need independent review in `Alignment.ReviewedBridges`)

The blind shadows write three notions of the text in primitive terms, where the trusted library
uses a Boolean test or its own recursive definition:

* "a removal `X → ∅`": the trusted test `Rxn.isRemoval r = true` vs the text's
  `∃ X a, r = Rxn.trans X none a` (the T_EB constructor `trans X none a` is `X → ∅`,
  `NetworkEpi/Syntax/Rxn.lean`). Bridges `bridge_isRemoval` (one per claim that uses it).
* "an exit `s → Y`": `Rxn.isExit r = true` vs `∃ Y ν, r = Rxn.exit Y ν`. Bridges `bridge_isExit`.
* "the removal flux `Σ_{(X → ∅, a) ∈ rs} a φ_X`": per reaction, the trusted
  `Rxn.removalRate v r` vs the shadow helper `RemRate v r` (`a * v X` for `trans X none a`, `0`
  otherwise). Bridges `bridge_removalRate`. The list sums then agree structurally
  (`congrArg` + `funext`).

Every other notion of the shadows (`PhiS`, `Susc`, `EdgeDef`, `EdgeDefD`, `NodeTot`, `NodeTotD`,
`PushF`, `PullF`, `FibreSum`) is definitionally equal to the trusted one (`CNet.phiS`,
`CNet.susc`, `edgeDefect`, `edgeDefectDeriv`, `nodeTotal`, `nodeTotalDeriv`, `pushEB`, `pullEB`,
`push`), so no bridge is needed for them.

"Not a removal" and "not an exit" in the re-shadowed claims (`edgeDefectDerivEbField`,
`nodeTotalDerivEbField`, `conservation`) are decided structurally, by a case split on the
reaction (`isRemoval_false_of_not`, `not_of_isRemoval_false`): `Rxn.isRemoval` reduces on
constructors, so no bridge is needed there. `xiConst` keeps its reviewed `bridge_isExit`.

## Recorded failures

None. `hasDerivWithinAtCompClm` now lists `hasDerivWithinAt_clm_comp_EB` (the chain rule on
`EB σ` for every species type) alongside the normed-space chain rule, so reading (a) is covered.
-/

open NEP

/-! ## Structural helpers (inlined by the audit; bridges are passed in as arguments) -/

namespace Alignment.Checks.SemanticsEB

open Alignment.Shadows.SemanticsEB

/-- `false = true` is absurd, by kernel reduction of a `Bool` eliminator into `Prop`. -/
theorem boolFalseNeTrue (h : false = true) : False :=
  Eq.mp (congrArg (fun b : Bool => Bool.rec (motive := fun _ => Prop) True False b) h) trivial

/-- A reaction that is not of the form `trans X none a` has `isRemoval = false`, given the
Boolean characterisation `hb` (a bridge). -/
theorem isRemoval_false_of {σ : Type}
    (hb : ∀ r : Rxn σ, r.isRemoval = true ↔ ∃ (X : σ) (a : ℝ), r = Rxn.trans X none a)
    (r : Rxn σ) (hn : ∀ (X : σ) (a : ℝ), r ≠ Rxn.trans X none a) : r.isRemoval = false :=
  match hr : r.isRemoval with
  | false => rfl
  | true => False.elim (Exists.elim ((hb r).mp hr) fun X h' => Exists.elim h' fun a he => hn X a he)

/-- Conversely, `isRemoval = false` excludes the form `trans X none a`. -/
theorem notRemoval_of_isRemoval_false {σ : Type}
    (hb : ∀ r : Rxn σ, r.isRemoval = true ↔ ∃ (X : σ) (a : ℝ), r = Rxn.trans X none a)
    (r : Rxn σ) (hf : r.isRemoval = false) : ∀ (X : σ) (a : ℝ), r ≠ Rxn.trans X none a :=
  fun X a he => boolFalseNeTrue (hf.symm.trans ((hb r).mpr ⟨X, a, he⟩))

/-- A reaction that is not of the form `exit Y ν` has `isExit = false`, given `hb` (a bridge). -/
theorem isExit_false_of {σ : Type}
    (hb : ∀ r : Rxn σ, r.isExit = true ↔ ∃ (Y : σ) (ν : ℝ), r = Rxn.exit Y ν)
    (r : Rxn σ) (hn : ∀ (Y : σ) (ν : ℝ), r ≠ Rxn.exit Y ν) : r.isExit = false :=
  match hr : r.isExit with
  | false => rfl
  | true => False.elim (Exists.elim ((hb r).mp hr) fun Y h' => Exists.elim h' fun ν he => hn Y ν he)

/-- Conversely, `isExit = false` excludes the form `exit Y ν`. -/
theorem notExit_of_isExit_false {σ : Type}
    (hb : ∀ r : Rxn σ, r.isExit = true ↔ ∃ (Y : σ) (ν : ℝ), r = Rxn.exit Y ν)
    (r : Rxn σ) (hf : r.isExit = false) : ∀ (Y : σ) (ν : ℝ), r ≠ Rxn.exit Y ν :=
  fun Y ν he => boolFalseNeTrue (hf.symm.trans ((hb r).mpr ⟨Y, ν, he⟩))

/-- Structural (no bridge): a reaction that is not of the form `trans X none a` has
`isRemoval = false`, by a case split on the reaction (`Rxn.isRemoval` reduces on constructors). -/
theorem isRemoval_false_of_not {σ : Type} (r : Rxn σ)
    (hn : ∀ (X : σ) (a : ℝ), r ≠ Rxn.trans X none a) : r.isRemoval = false :=
  match r, hn with
  | .contact _ _ _, _ => rfl
  | .exit _ _, _ => rfl
  | .trans _ (some _) _, _ => rfl
  | .trans X none a, hn => False.elim (hn X a rfl)

/-- Structural (no bridge): `isRemoval = false` excludes the form `trans X none a`. -/
theorem not_of_isRemoval_false {σ : Type} (r : Rxn σ) (hf : r.isRemoval = false) :
    ∀ (X : σ) (a : ℝ), r ≠ Rxn.trans X none a :=
  fun _ _ he => boolFalseNeTrue (Eq.symm (Eq.trans (Eq.symm (congrArg Rxn.isRemoval he)) hf))

/-- The trusted removal flux equals the shadow's `RemFlux`, given the per-reaction bridge `hb`. -/
theorem removalFlux_eq_of {σ : Type}
    (hb : ∀ (v : σ → ℝ) (r : Rxn σ), Rxn.removalRate v r = RemRate v r)
    (rs : List (Rxn σ)) (v : σ → ℝ) : removalFlux rs v = RemFlux rs v :=
  congrArg (fun g : Rxn σ → ℝ => (rs.map g).sum) (funext fun r => hb v r)

/-! Proofs of the bridge statements (bridges may use any tactic; these do not depend on any
implementation theorem). -/

theorem isRemoval_iff_aux {σ : Type} (r : Rxn σ) :
    r.isRemoval = true ↔ ∃ (X : σ) (a : ℝ), r = Rxn.trans X none a := by
  cases r with
  | contact J X τ => simp [Rxn.isRemoval]
  | exit Y ν => simp [Rxn.isRemoval]
  | trans X Y a => cases Y <;> simp [Rxn.isRemoval]

theorem isExit_iff_aux {σ : Type} (r : Rxn σ) :
    r.isExit = true ↔ ∃ (Y : σ) (ν : ℝ), r = Rxn.exit Y ν := by
  cases r with
  | contact J X τ => simp [Rxn.isExit]
  | exit Y ν => simp [Rxn.isExit]
  | trans X Y a => simp [Rxn.isExit]

theorem removalRate_eq_aux {σ : Type} (v : σ → ℝ) (r : Rxn σ) :
    Rxn.removalRate v r = RemRate v r := by
  cases r with
  | contact J X τ => rfl
  | exit Y ν => rfl
  | trans X Y a => cases Y <;> rfl

end Alignment.Checks.SemanticsEB

/-! ## `SemanticsEB.header.fieldTable` -/

namespace Alignment.Shadows.SemanticsEB.FieldTable

sa_claim "SemanticsEB.header.fieldTable" group "SemanticsEB" required
  text "contact r = (s + J → X + J, τ_r): θ̇ += −τ_r φ_J φ̇_J += −τ_r φ_J φ̇_X += +τ_r φ_J · qξ ψ''(θ)/ψ'(1) pop_X' += +τ_r φ_J · qξ ψ'(θ) transition t = (X → Y | ∅, a): φ̇_X −= a φ_X; φ̇_Y += a φ_X; pop_X' −= a pop_X; pop_Y' += a pop_X (Y = ∅: no gains) exit e = (s → Y, ν_e): ξ̇ += −ν_e ξ; φ̇_Y += ν_e φ_S; pop_Y' += ν_e S initial condition: θ(0) = 1, ξ(0) = 1, φ_X(0) = pop_X(0) = ρ_X [...] `ebField N q r u` is exactly this contribution of reaction `r` at state `u`, and `lift N q rs u` is the sum of the contributions of the reactions in the list `rs`."
  impl NEP.ebField_contact_table NEP.ebField_exit_eq NEP.ebField_remove_table
    NEP.ebField_progress_table NEP.lift_eq_sum

/-! `sa_impl%` is `contact_table ∧ exit_eq ∧ remove_table ∧ progress_table ∧ lift_eq_sum`. Each
of the four row theorems is a function equality; a component of the shadow is that equality
evaluated at `u` and projected (`congrArg`). `PhiS`/`Susc` unfold to the impl's
`q * u.2.1 * N.ψ' u.1 / N.ψ' 1` and `q * u.2.1 * N.ψ u.1`. -/

@[sa_forward "SemanticsEB.header.fieldTable" 1]
theorem fwd1 (h : sa_impl% "SemanticsEB.header.fieldTable") : S1 := by
  intro σ _ N q J X τ u
  exact congrArg (fun F : EB σ → EB σ => (F u).1) (h.1 N q J X τ)

@[sa_forward "SemanticsEB.header.fieldTable" 2]
theorem fwd2 (h : sa_impl% "SemanticsEB.header.fieldTable") : S2 := by
  intro σ _ N q J X τ u
  exact congrArg (fun F : EB σ → EB σ => (F u).2.1) (h.1 N q J X τ)

@[sa_forward "SemanticsEB.header.fieldTable" 3]
theorem fwd3 (h : sa_impl% "SemanticsEB.header.fieldTable") : S3 := by
  intro σ _ N q J X τ u
  exact congrArg (fun F : EB σ → EB σ => (F u).2.2.1) (h.1 N q J X τ)

@[sa_forward "SemanticsEB.header.fieldTable" 4]
theorem fwd4 (h : sa_impl% "SemanticsEB.header.fieldTable") : S4 := by
  intro σ _ N q J X τ u
  exact congrArg (fun F : EB σ → EB σ => (F u).2.2.2) (h.1 N q J X τ)

@[sa_forward "SemanticsEB.header.fieldTable" 5]
theorem fwd5 (h : sa_impl% "SemanticsEB.header.fieldTable") : S5 := by
  intro σ _ N q X Y a u
  exact congrArg (fun F : EB σ → EB σ => (F u).1) (h.2.2.2.1 N q X Y a)

@[sa_forward "SemanticsEB.header.fieldTable" 6]
theorem fwd6 (h : sa_impl% "SemanticsEB.header.fieldTable") : S6 := by
  intro σ _ N q X Y a u
  exact congrArg (fun F : EB σ → EB σ => (F u).2.1) (h.2.2.2.1 N q X Y a)

@[sa_forward "SemanticsEB.header.fieldTable" 7]
theorem fwd7 (h : sa_impl% "SemanticsEB.header.fieldTable") : S7 := by
  intro σ _ N q X Y a u
  exact congrArg (fun F : EB σ → EB σ => (F u).2.2.1) (h.2.2.2.1 N q X Y a)

@[sa_forward "SemanticsEB.header.fieldTable" 8]
theorem fwd8 (h : sa_impl% "SemanticsEB.header.fieldTable") : S8 := by
  intro σ _ N q X Y a u
  exact congrArg (fun F : EB σ → EB σ => (F u).2.2.2) (h.2.2.2.1 N q X Y a)

@[sa_forward "SemanticsEB.header.fieldTable" 9]
theorem fwd9 (h : sa_impl% "SemanticsEB.header.fieldTable") : S9 := by
  intro σ _ N q X a u
  exact congrArg (fun F : EB σ → EB σ => (F u).1) (h.2.2.1 N q X a)

@[sa_forward "SemanticsEB.header.fieldTable" 10]
theorem fwd10 (h : sa_impl% "SemanticsEB.header.fieldTable") : S10 := by
  intro σ _ N q X a u
  exact congrArg (fun F : EB σ → EB σ => (F u).2.1) (h.2.2.1 N q X a)

@[sa_forward "SemanticsEB.header.fieldTable" 11]
theorem fwd11 (h : sa_impl% "SemanticsEB.header.fieldTable") : S11 := by
  intro σ _ N q X a u
  exact congrArg (fun F : EB σ → EB σ => (F u).2.2.1) (h.2.2.1 N q X a)

@[sa_forward "SemanticsEB.header.fieldTable" 12]
theorem fwd12 (h : sa_impl% "SemanticsEB.header.fieldTable") : S12 := by
  intro σ _ N q X a u
  exact congrArg (fun F : EB σ → EB σ => (F u).2.2.2) (h.2.2.1 N q X a)

@[sa_forward "SemanticsEB.header.fieldTable" 13]
theorem fwd13 (h : sa_impl% "SemanticsEB.header.fieldTable") : S13 := by
  intro σ _ N q Y ν u
  exact congrArg (fun F : EB σ → EB σ => (F u).1) (h.2.1 N q Y ν)

@[sa_forward "SemanticsEB.header.fieldTable" 14]
theorem fwd14 (h : sa_impl% "SemanticsEB.header.fieldTable") : S14 := by
  intro σ _ N q Y ν u
  exact congrArg (fun F : EB σ → EB σ => (F u).2.1) (h.2.1 N q Y ν)

/-- `PhiS N q u` unfolds to the impl's `q * u.2.1 * N.ψ' u.1 / N.ψ' 1`. -/
@[sa_forward "SemanticsEB.header.fieldTable" 15]
theorem fwd15 (h : sa_impl% "SemanticsEB.header.fieldTable") : S15 := by
  intro σ _ N q Y ν u
  exact congrArg (fun F : EB σ → EB σ => (F u).2.2.1) (h.2.1 N q Y ν)

/-- `Susc N q u` unfolds to the impl's `q * u.2.1 * N.ψ u.1`. -/
@[sa_forward "SemanticsEB.header.fieldTable" 16]
theorem fwd16 (h : sa_impl% "SemanticsEB.header.fieldTable") : S16 := by
  intro σ _ N q Y ν u
  exact congrArg (fun F : EB σ → EB σ => (F u).2.2.2) (h.2.1 N q Y ν)

@[sa_forward "SemanticsEB.header.fieldTable" 17]
theorem fwd17 (h : sa_impl% "SemanticsEB.header.fieldTable") : S17 := by
  intro σ _ N q rs u
  exact h.2.2.2.2 N q rs u

/-- Each row theorem from its four component shadows: `funext`, structure eta for `EB σ`
(definitional), then rewriting each component. -/
@[sa_backward "SemanticsEB.header.fieldTable"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) (s7 : S7) (s8 : S8)
    (s9 : S9) (s10 : S10) (s11 : S11) (s12 : S12) (s13 : S13) (s14 : S14) (s15 : S15)
    (s16 : S16) (s17 : S17) : sa_impl% "SemanticsEB.header.fieldTable" := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro σ _ N q J X τ
    funext u
    show ((ebField N q (Rxn.contact J X τ) u).1, (ebField N q (Rxn.contact J X τ) u).2.1,
      (ebField N q (Rxn.contact J X τ) u).2.2.1, (ebField N q (Rxn.contact J X τ) u).2.2.2) = _
    rw [s1 N q J X τ u, s2 N q J X τ u, s3 N q J X τ u, s4 N q J X τ u]
  · intro σ _ N q Y ν
    funext u
    show ((ebField N q (Rxn.exit Y ν) u).1, (ebField N q (Rxn.exit Y ν) u).2.1,
      (ebField N q (Rxn.exit Y ν) u).2.2.1, (ebField N q (Rxn.exit Y ν) u).2.2.2) = _
    rw [s13 N q Y ν u, s14 N q Y ν u, s15 N q Y ν u, s16 N q Y ν u]
    rfl
  · intro σ _ N q X a
    funext u
    show ((ebField N q (Rxn.trans X none a) u).1, (ebField N q (Rxn.trans X none a) u).2.1,
      (ebField N q (Rxn.trans X none a) u).2.2.1,
      (ebField N q (Rxn.trans X none a) u).2.2.2) = _
    rw [s9 N q X a u, s10 N q X a u, s11 N q X a u, s12 N q X a u]
  · intro σ _ N q X Y a
    funext u
    show ((ebField N q (Rxn.trans X (some Y) a) u).1,
      (ebField N q (Rxn.trans X (some Y) a) u).2.1,
      (ebField N q (Rxn.trans X (some Y) a) u).2.2.1,
      (ebField N q (Rxn.trans X (some Y) a) u).2.2.2) = _
    rw [s5 N q X Y a u, s6 N q X Y a u, s7 N q X Y a u, s8 N q X Y a u]
  · intro σ _ N q rs u
    exact s17 N q rs u

end Alignment.Shadows.SemanticsEB.FieldTable

/-! ## `SemanticsEB.liftAppend` -/

namespace Alignment.Shadows.SemanticsEB.LiftAppend

sa_claim "SemanticsEB.liftAppend" group "SemanticsEB" required
  text "**H1, part 1: the EB lift is additive in the reaction list.** Design statement (DESIGN_NetworkEpiCore.md §D.4, table row EB_N, column \"Strict under gluing?\"): \"**yes**: the per-reaction lift is additive and natural in species maps ([L] `lift_append`, `lift_map`)\"; §D.6: \"**H1** EB(glue(A,B)) = glue(EB A, EB B), for fixed N with s glued to s | **yes, strict** | local per-reaction fields | [L] `lift_append`, `lift_map` (contact/transition; the exit case is added in WP13)\". [...] **Naturality of the per-reaction EB field in species maps.** Design statement (DESIGN_NetworkEpiCore.md §D.7, L3): \"`lift_append`, `ebField_map`, `lift_map` (relabelling/gluing naturality with pushforward along fibres)\". [...] **H1, part 2: the EB lift is natural in species maps (relabelling and gluing).** Design statement (DESIGN_NetworkEpiCore.md §D.4, row EB_N): \"the per-reaction lift is additive and natural in species maps ([L] `lift_append`, `lift_map`)\"; §D.7, L3: \"`lift_map` (relabelling/gluing naturality with pushforward along fibres)\"; §D.6 H1 (quoted at `lift_append`), with the exit case included. [...] **H1: the EB lift is strict under gluing.** Design statement (DESIGN_NetworkEpiCore.md §D.6): \"**H1** EB(glue(A,B)) = glue(EB A, EB B), for fixed N with s glued to s | **yes, strict** | local per-reaction fields\"; §D.3 (open systems): \"composition identifies ported coordinates and **adds** vector fields\"."
  impl NEP.lift_append NEP.ebField_map NEP.lift_map NEP.lift_glue

@[sa_forward "SemanticsEB.liftAppend" 1]
theorem fwd1 (h : sa_impl% "SemanticsEB.liftAppend") : S1 := by
  intro σ _ N q rs rs' u
  exact h.1 N q rs rs' u

/-- `PushF`/`PullF`/`FibreSum` unfold to `pushEB`/`pullEB`/`push`. -/
@[sa_forward "SemanticsEB.liftAppend" 2]
theorem fwd2 (h : sa_impl% "SemanticsEB.liftAppend") : S2 := by
  intro σ σ' _ _ _ N q f r u
  exact h.2.1 N q f r u

@[sa_forward "SemanticsEB.liftAppend" 3]
theorem fwd3 (h : sa_impl% "SemanticsEB.liftAppend") : S3 := by
  intro σ σ' _ _ _ N q f rs u
  exact h.2.2.1 N q f rs u

@[sa_forward "SemanticsEB.liftAppend" 4]
theorem fwd4 (h : sa_impl% "SemanticsEB.liftAppend") : S4 := by
  intro σA σB σ _ _ _ _ _ N q f g A B u
  exact h.2.2.2 N q f g A B u

@[sa_backward "SemanticsEB.liftAppend"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : sa_impl% "SemanticsEB.liftAppend" := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro σ _ N q rs rs' u
    exact s1 N q rs rs' u
  · intro σ σ' _ _ _ N q f r u
    exact s2 N q f r u
  · intro σ σ' _ _ _ N q f rs u
    exact s3 N q f rs u
  · intro σ σA σB _ _ _ _ _ N q f g A B u
    exact s4 N q f g A B u

end Alignment.Shadows.SemanticsEB.LiftAppend

/-! ## Pushforward algebra (shadows are the implementation statements) -/

namespace Alignment.Shadows.SemanticsEB.PushSingle

sa_claim "SemanticsEB.pushSingle" group "SemanticsEB" required
  text "The pushforward of `Pi.single X c` is `Pi.single (f X) c`."
  impl NEP.push_single

@[sa_forward "SemanticsEB.pushSingle" 1]
theorem fwd1 (h : sa_impl% "SemanticsEB.pushSingle") : S1 := by
  intro σ σ' _ _ _ f X c
  exact h f X c

@[sa_backward "SemanticsEB.pushSingle"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsEB.pushSingle" := by
  intro σ σ' _ _ _ f X c
  exact s1 f X c

end Alignment.Shadows.SemanticsEB.PushSingle

namespace Alignment.Shadows.SemanticsEB.PushAdd

sa_claim "SemanticsEB.pushAdd" group "SemanticsEB" required
  text "The pushforward is additive."
  impl NEP.push_add

@[sa_forward "SemanticsEB.pushAdd" 1]
theorem fwd1 (h : sa_impl% "SemanticsEB.pushAdd") : S1 := by
  intro σ σ' _ _ f v w
  exact h f v w

@[sa_backward "SemanticsEB.pushAdd"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsEB.pushAdd" := by
  intro σ σ' _ _ f v w
  exact s1 f v w

end Alignment.Shadows.SemanticsEB.PushAdd

namespace Alignment.Shadows.SemanticsEB.PushNeg

sa_claim "SemanticsEB.pushNeg" group "SemanticsEB" required
  text "The pushforward commutes with negation."
  impl NEP.push_neg

@[sa_forward "SemanticsEB.pushNeg" 1]
theorem fwd1 (h : sa_impl% "SemanticsEB.pushNeg") : S1 := by
  intro σ σ' _ _ f v
  exact h f v

@[sa_backward "SemanticsEB.pushNeg"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsEB.pushNeg" := by
  intro σ σ' _ _ f v
  exact s1 f v

end Alignment.Shadows.SemanticsEB.PushNeg

namespace Alignment.Shadows.SemanticsEB.PushSub

sa_claim "SemanticsEB.pushSub" group "SemanticsEB" required
  text "The pushforward commutes with subtraction."
  impl NEP.push_sub

@[sa_forward "SemanticsEB.pushSub" 1]
theorem fwd1 (h : sa_impl% "SemanticsEB.pushSub") : S1 := by
  intro σ σ' _ _ f v w
  exact h f v w

@[sa_backward "SemanticsEB.pushSub"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsEB.pushSub" := by
  intro σ σ' _ _ f v w
  exact s1 f v w

end Alignment.Shadows.SemanticsEB.PushSub

namespace Alignment.Shadows.SemanticsEB.PushZero

sa_claim "SemanticsEB.pushZero" group "SemanticsEB" required
  text "The pushforward of zero is zero."
  impl NEP.push_zero

@[sa_forward "SemanticsEB.pushZero" 1]
theorem fwd1 (h : sa_impl% "SemanticsEB.pushZero") : S1 := by
  intro σ σ' _ _ f
  exact h f

@[sa_backward "SemanticsEB.pushZero"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsEB.pushZero" := by
  intro σ σ' _ _ f
  exact s1 f

end Alignment.Shadows.SemanticsEB.PushZero

namespace Alignment.Shadows.SemanticsEB.PushEBAdd

sa_claim "SemanticsEB.pushEBAdd" group "SemanticsEB" required
  text "The pushforward of EB coordinates is additive."
  impl NEP.pushEB_add

@[sa_forward "SemanticsEB.pushEBAdd" 1]
theorem fwd1 (h : sa_impl% "SemanticsEB.pushEBAdd") : S1 := by
  intro σ σ' _ _ f u w
  exact h f u w

@[sa_backward "SemanticsEB.pushEBAdd"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsEB.pushEBAdd" := by
  intro σ σ' _ _ f u w
  exact s1 f u w

end Alignment.Shadows.SemanticsEB.PushEBAdd

namespace Alignment.Shadows.SemanticsEB.PushEBZero

sa_claim "SemanticsEB.pushEBZero" group "SemanticsEB" required
  text "The pushforward of the zero EB vector is zero."
  impl NEP.pushEB_zero

@[sa_forward "SemanticsEB.pushEBZero" 1]
theorem fwd1 (h : sa_impl% "SemanticsEB.pushEBZero") : S1 := by
  intro σ σ' _ _ f
  exact h f

@[sa_backward "SemanticsEB.pushEBZero"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsEB.pushEBZero" := by
  intro σ σ' _ _ f
  exact s1 f

end Alignment.Shadows.SemanticsEB.PushEBZero

/-! ## `SemanticsEB.removalFluxEqZero` -/

namespace Alignment.Shadows.SemanticsEB.RemovalFluxEqZero

open Alignment.Checks.SemanticsEB

sa_claim "SemanticsEB.removalFluxEqZero" group "SemanticsEB" required
  text "Without removals `X → ∅` the removal flux vanishes."
  impl NEP.removalFlux_eq_zero

/-- Bridge (needs independent review): the trusted Boolean test `Rxn.isRemoval r = true` vs the
text's "`r` is a removal `X → ∅`", i.e. `r = trans X none a` for some `X`, `a`. -/
@[sa_bridge "SemanticsEB.removalFluxEqZero"]
theorem bridge_isRemoval {σ : Type} (r : Rxn σ) :
    r.isRemoval = true ↔ ∃ (X : σ) (a : ℝ), r = Rxn.trans X none a :=
  isRemoval_iff_aux r

@[sa_forward "SemanticsEB.removalFluxEqZero" 1]
theorem fwd1 (h : sa_impl% "SemanticsEB.removalFluxEqZero") : S1 := by
  intro σ rs v hn
  exact h rs (fun r hr => isRemoval_false_of bridge_isRemoval r (hn r hr)) v

@[sa_backward "SemanticsEB.removalFluxEqZero"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsEB.removalFluxEqZero" := by
  intro σ rs hrs v
  exact s1 rs v (fun r hr => notRemoval_of_isRemoval_false bridge_isRemoval r (hrs r hr))

end Alignment.Shadows.SemanticsEB.RemovalFluxEqZero

/-! ## `SemanticsEB.sumSingle` -/

namespace Alignment.Shadows.SemanticsEB.SumSingle

sa_claim "SemanticsEB.sumSingle" group "SemanticsEB" required
  text "The sum over all species of `Pi.single X c` is `c`."
  impl NEP.sum_single

@[sa_forward "SemanticsEB.sumSingle" 1]
theorem fwd1 (h : sa_impl% "SemanticsEB.sumSingle") : S1 := by
  intro σ _ _ X c
  exact h X c

@[sa_backward "SemanticsEB.sumSingle"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsEB.sumSingle" := by
  intro σ _ _ X c
  exact s1 X c

end Alignment.Shadows.SemanticsEB.SumSingle

/-! ## `SemanticsEB.hasDerivWithinAtCompClm` -/

namespace Alignment.Shadows.SemanticsEB.HasDerivWithinAtCompClm

sa_claim "SemanticsEB.hasDerivWithinAtCompClm" group "SemanticsEB" required
  text "Chain rule for a continuous linear map applied to a curve, within a set of times."
  impl NEP.hasDerivWithinAt_clm_comp NEP.hasDerivWithinAt_clm_comp_EB

/-- S1 (reading (a), curves in `EB σ` for any `σ`) is `hasDerivWithinAt_clm_comp_EB`. -/
@[sa_forward "SemanticsEB.hasDerivWithinAtCompClm" 1]
theorem fwd1 (h : sa_impl% "SemanticsEB.hasDerivWithinAtCompClm") : S1 := by
  intro σ F _ _ L x x' I t hx
  exact h.2 L hx

@[sa_forward "SemanticsEB.hasDerivWithinAtCompClm" 2]
theorem fwd2 (h : sa_impl% "SemanticsEB.hasDerivWithinAtCompClm") : S2 := by
  intro E F _ _ _ _ L x x' I t hx
  exact h.1 L hx

/-- The impl is reading (b) (`S2`) and reading (a) (`S1`). -/
@[sa_backward "SemanticsEB.hasDerivWithinAtCompClm"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "SemanticsEB.hasDerivWithinAtCompClm" := by
  refine ⟨?_, ?_⟩
  · intro E F _ _ _ _ L x x' I t hx
    exact s2 L x x' I t hx
  · intro σ F _ _ L x x' I t hx
    exact s1 L x x' I t hx

end Alignment.Shadows.SemanticsEB.HasDerivWithinAtCompClm

/-! ## Coordinates of a curve: `hasDerivWithinAtTheta`, `…Xi`, `…Phi`, `…Pop` -/

namespace Alignment.Shadows.SemanticsEB.HasDerivWithinAtTheta

sa_claim "SemanticsEB.hasDerivWithinAtTheta" group "SemanticsEB" required
  text "The θ-coordinate of a curve has, within `I`, the θ-coordinate of its derivative."
  impl NEP.hasDerivWithinAt_θ_any

@[sa_forward "SemanticsEB.hasDerivWithinAtTheta" 1]
theorem fwd1 (h : sa_impl% "SemanticsEB.hasDerivWithinAtTheta") : S1 := by
  intro σ x x' I t hx
  exact h hx

@[sa_backward "SemanticsEB.hasDerivWithinAtTheta"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsEB.hasDerivWithinAtTheta" := by
  intro σ x x' I t hx
  exact s1 x x' I t hx

end Alignment.Shadows.SemanticsEB.HasDerivWithinAtTheta

namespace Alignment.Shadows.SemanticsEB.HasDerivWithinAtXi

sa_claim "SemanticsEB.hasDerivWithinAtXi" group "SemanticsEB" required
  text "The ξ-coordinate of a curve has, within `I`, the ξ-coordinate of its derivative."
  impl NEP.hasDerivWithinAt_ξ_any

@[sa_forward "SemanticsEB.hasDerivWithinAtXi" 1]
theorem fwd1 (h : sa_impl% "SemanticsEB.hasDerivWithinAtXi") : S1 := by
  intro σ x x' I t hx
  exact h hx

@[sa_backward "SemanticsEB.hasDerivWithinAtXi"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsEB.hasDerivWithinAtXi" := by
  intro σ x x' I t hx
  exact s1 x x' I t hx

end Alignment.Shadows.SemanticsEB.HasDerivWithinAtXi

namespace Alignment.Shadows.SemanticsEB.HasDerivWithinAtPhi

sa_claim "SemanticsEB.hasDerivWithinAtPhi" group "SemanticsEB" required
  text "Each φ-coordinate of a curve has, within `I`, the φ-coordinate of its derivative."
  impl NEP.hasDerivWithinAt_φ_any

@[sa_forward "SemanticsEB.hasDerivWithinAtPhi" 1]
theorem fwd1 (h : sa_impl% "SemanticsEB.hasDerivWithinAtPhi") : S1 := by
  intro σ x x' I t X hx
  exact h hx X

@[sa_backward "SemanticsEB.hasDerivWithinAtPhi"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsEB.hasDerivWithinAtPhi" := by
  intro σ x x' I t hx X
  exact s1 x x' I t X hx

end Alignment.Shadows.SemanticsEB.HasDerivWithinAtPhi

namespace Alignment.Shadows.SemanticsEB.HasDerivWithinAtPop

sa_claim "SemanticsEB.hasDerivWithinAtPop" group "SemanticsEB" required
  text "Each pop-coordinate of a curve has, within `I`, the pop-coordinate of its derivative."
  impl NEP.hasDerivWithinAt_pop_any

@[sa_forward "SemanticsEB.hasDerivWithinAtPop" 1]
theorem fwd1 (h : sa_impl% "SemanticsEB.hasDerivWithinAtPop") : S1 := by
  intro σ x x' I t X hx
  exact h hx X

@[sa_backward "SemanticsEB.hasDerivWithinAtPop"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsEB.hasDerivWithinAtPop" := by
  intro σ x x' I t hx X
  exact s1 x x' I t X hx

end Alignment.Shadows.SemanticsEB.HasDerivWithinAtPop

/-! ## Chain rules: `hasDerivWithinAtEdgeDefect`, `hasDerivWithinAtNodeTotal` -/

namespace Alignment.Shadows.SemanticsEB.HasDerivWithinAtEdgeDefect

sa_claim "SemanticsEB.hasDerivWithinAtEdgeDefect" group "SemanticsEB" required
  text "Chain rule for the edge defect along a curve, within a set of times `I`, when `ψ''` is the derivative of `ψ'` at the current θ."
  impl NEP.hasDerivWithinAt_edgeDefect

/-- `EdgeDef`/`EdgeDefD` unfold to `edgeDefect`/`edgeDefectDeriv` (`PhiS N q u` is
`CNet.phiS N q u.1 u.2.1`). -/
@[sa_forward "SemanticsEB.hasDerivWithinAtEdgeDefect" 1]
theorem fwd1 (h : sa_impl% "SemanticsEB.hasDerivWithinAtEdgeDefect") : S1 := by
  intro σ _ N q x x' I t hx hψ'
  exact h N q hψ' hx

@[sa_backward "SemanticsEB.hasDerivWithinAtEdgeDefect"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsEB.hasDerivWithinAtEdgeDefect" := by
  intro σ _ N q x x' I t hψ' hx
  exact s1 N q x x' I t hx hψ'

end Alignment.Shadows.SemanticsEB.HasDerivWithinAtEdgeDefect

namespace Alignment.Shadows.SemanticsEB.HasDerivWithinAtNodeTotal

sa_claim "SemanticsEB.hasDerivWithinAtNodeTotal" group "SemanticsEB" required
  text "Chain rule for the node total along a curve, within a set of times `I`, when `ψ'` is the derivative of `ψ` at the current θ."
  impl NEP.hasDerivWithinAt_nodeTotal

/-- `NodeTot`/`NodeTotD` unfold to `nodeTotal`/`nodeTotalDeriv` (`Susc N q u` is
`CNet.susc N q u.1 u.2.1`). -/
@[sa_forward "SemanticsEB.hasDerivWithinAtNodeTotal" 1]
theorem fwd1 (h : sa_impl% "SemanticsEB.hasDerivWithinAtNodeTotal") : S1 := by
  intro σ _ N q x x' I t hx hψ
  exact h N q hψ hx

@[sa_backward "SemanticsEB.hasDerivWithinAtNodeTotal"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsEB.hasDerivWithinAtNodeTotal" := by
  intro σ _ N q x x' I t hψ hx
  exact s1 N q x x' I t hx hψ

end Alignment.Shadows.SemanticsEB.HasDerivWithinAtNodeTotal

/-! ## Additivity of the named derivatives -/

namespace Alignment.Shadows.SemanticsEB.EdgeDefectDerivAdd

sa_claim "SemanticsEB.edgeDefectDerivAdd" group "SemanticsEB" required
  text "`edgeDefectDeriv N q u` is additive in the direction."
  impl NEP.edgeDefectDeriv_add

@[sa_forward "SemanticsEB.edgeDefectDerivAdd" 1]
theorem fwd1 (h : sa_impl% "SemanticsEB.edgeDefectDerivAdd") : S1 := by
  intro σ _ N q u v w
  exact h N q u v w

@[sa_backward "SemanticsEB.edgeDefectDerivAdd"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsEB.edgeDefectDerivAdd" := by
  intro σ _ N q u v w
  exact s1 N q u v w

end Alignment.Shadows.SemanticsEB.EdgeDefectDerivAdd

namespace Alignment.Shadows.SemanticsEB.NodeTotalDerivAdd

sa_claim "SemanticsEB.nodeTotalDerivAdd" group "SemanticsEB" required
  text "`nodeTotalDeriv N q u` is additive in the direction."
  impl NEP.nodeTotalDeriv_add

@[sa_forward "SemanticsEB.nodeTotalDerivAdd" 1]
theorem fwd1 (h : sa_impl% "SemanticsEB.nodeTotalDerivAdd") : S1 := by
  intro σ _ N q u v w
  exact h N q u v w

@[sa_backward "SemanticsEB.nodeTotalDerivAdd"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsEB.nodeTotalDerivAdd" := by
  intro σ _ N q u v w
  exact s1 N q u v w

end Alignment.Shadows.SemanticsEB.NodeTotalDerivAdd

/-! ## Per reaction: `edgeDefectDerivEbField`, `nodeTotalDerivEbField` -/

namespace Alignment.Shadows.SemanticsEB.EdgeDefectDerivEbField

open Alignment.Checks.SemanticsEB

sa_claim "SemanticsEB.edgeDefectDerivEbField" group "SemanticsEB" required
  text "Per reaction, the edge defect changes only through removals."
  impl NEP.edgeDefectDeriv_ebField_eq_zero

/-! `EdgeDefD`/`edgeDefectDeriv` have the same body (definitional). A contact, exit or progression is
not a removal: `Rxn.isRemoval` reduces to `false` on it (`rfl`), so no bridge is needed. -/

@[sa_forward "SemanticsEB.edgeDefectDerivEbField" 1]
theorem fwd1 (h : sa_impl% "SemanticsEB.edgeDefectDerivEbField") : S1 := by
  intro σ _ _ N q J X τ u
  exact h N q (Rxn.contact J X τ) rfl u

@[sa_forward "SemanticsEB.edgeDefectDerivEbField" 2]
theorem fwd2 (h : sa_impl% "SemanticsEB.edgeDefectDerivEbField") : S2 := by
  intro σ _ _ N q Y ν u
  exact h N q (Rxn.exit Y ν) rfl u

@[sa_forward "SemanticsEB.edgeDefectDerivEbField" 3]
theorem fwd3 (h : sa_impl% "SemanticsEB.edgeDefectDerivEbField") : S3 := by
  intro σ _ _ N q X Y a u
  exact h N q (Rxn.trans X (some Y) a) rfl u

/-- Case split on the reaction; a removal contradicts `isRemoval r = false`. -/
@[sa_backward "SemanticsEB.edgeDefectDerivEbField"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) : sa_impl% "SemanticsEB.edgeDefectDerivEbField" := by
  intro σ _ _ N q r hr u
  match r, hr with
  | .contact J X τ, _ => exact s1 N q J X τ u
  | .exit Y ν, _ => exact s2 N q Y ν u
  | .trans X (some Y) a, _ => exact s3 N q X Y a u
  | .trans X none a, hr => exact False.elim (boolFalseNeTrue hr.symm)

end Alignment.Shadows.SemanticsEB.EdgeDefectDerivEbField

namespace Alignment.Shadows.SemanticsEB.NodeTotalDerivEbField

open Alignment.Checks.SemanticsEB

sa_claim "SemanticsEB.nodeTotalDerivEbField" group "SemanticsEB" required
  text "Per reaction, the node total changes only through removals."
  impl NEP.nodeTotalDeriv_ebField_eq_zero

/-! `NodeTotD`/`nodeTotalDeriv` have the same body (definitional). A contact, exit or progression is
not a removal: `Rxn.isRemoval` reduces to `false` on it (`rfl`), so no bridge is needed. -/

@[sa_forward "SemanticsEB.nodeTotalDerivEbField" 1]
theorem fwd1 (h : sa_impl% "SemanticsEB.nodeTotalDerivEbField") : S1 := by
  intro σ _ _ N q J X τ u
  exact h N q (Rxn.contact J X τ) rfl u

@[sa_forward "SemanticsEB.nodeTotalDerivEbField" 2]
theorem fwd2 (h : sa_impl% "SemanticsEB.nodeTotalDerivEbField") : S2 := by
  intro σ _ _ N q Y ν u
  exact h N q (Rxn.exit Y ν) rfl u

@[sa_forward "SemanticsEB.nodeTotalDerivEbField" 3]
theorem fwd3 (h : sa_impl% "SemanticsEB.nodeTotalDerivEbField") : S3 := by
  intro σ _ _ N q X Y a u
  exact h N q (Rxn.trans X (some Y) a) rfl u

/-- Case split on the reaction; a removal contradicts `isRemoval r = false`. -/
@[sa_backward "SemanticsEB.nodeTotalDerivEbField"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) : sa_impl% "SemanticsEB.nodeTotalDerivEbField" := by
  intro σ _ _ N q r hr u
  match r, hr with
  | .contact J X τ, _ => exact s1 N q J X τ u
  | .exit Y ν, _ => exact s2 N q Y ν u
  | .trans X (some Y) a, _ => exact s3 N q X Y a u
  | .trans X none a, hr => exact False.elim (boolFalseNeTrue hr.symm)

end Alignment.Shadows.SemanticsEB.NodeTotalDerivEbField

/-! ## Along the lift: `edgeDefectDerivLift`, `nodeTotalDerivLift` -/

namespace Alignment.Shadows.SemanticsEB.EdgeDefectDerivLift

open Alignment.Checks.SemanticsEB

sa_claim "SemanticsEB.edgeDefectDerivLift" group "SemanticsEB" required
  text "Along the EB field of a reaction list, the edge defect changes at the removal flux of φ."
  impl NEP.edgeDefectDeriv_lift

/-- Bridge (needs independent review): the trusted per-reaction removal rate vs the text's
summand "`a φ_X` for a removal `(X → ∅, a)`, nothing for other reactions" (shadow helper
`RemRate`). -/
@[sa_bridge "SemanticsEB.edgeDefectDerivLift"]
theorem bridge_removalRate {σ : Type} (v : σ → ℝ) (r : Rxn σ) :
    Rxn.removalRate v r = RemRate v r :=
  removalRate_eq_aux v r

@[sa_forward "SemanticsEB.edgeDefectDerivLift" 1]
theorem fwd1 (h : sa_impl% "SemanticsEB.edgeDefectDerivLift") : S1 := by
  intro σ _ _ N q rs u
  exact (h N q rs u).trans (removalFlux_eq_of bridge_removalRate rs u.2.2.1)

@[sa_backward "SemanticsEB.edgeDefectDerivLift"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsEB.edgeDefectDerivLift" := by
  intro σ _ _ N q rs u
  exact (s1 N q rs u).trans (removalFlux_eq_of bridge_removalRate rs u.2.2.1).symm

end Alignment.Shadows.SemanticsEB.EdgeDefectDerivLift

namespace Alignment.Shadows.SemanticsEB.NodeTotalDerivLift

open Alignment.Checks.SemanticsEB

sa_claim "SemanticsEB.nodeTotalDerivLift" group "SemanticsEB" required
  text "Along the EB field of a reaction list, the node total changes at minus the removal flux of pop."
  impl NEP.nodeTotalDeriv_lift

/-- Bridge (needs independent review): as `EdgeDefectDerivLift.bridge_removalRate`. -/
@[sa_bridge "SemanticsEB.nodeTotalDerivLift"]
theorem bridge_removalRate {σ : Type} (v : σ → ℝ) (r : Rxn σ) :
    Rxn.removalRate v r = RemRate v r :=
  removalRate_eq_aux v r

@[sa_forward "SemanticsEB.nodeTotalDerivLift" 1]
theorem fwd1 (h : sa_impl% "SemanticsEB.nodeTotalDerivLift") : S1 := by
  intro σ _ _ N q rs u
  exact (h N q rs u).trans
    (congrArg (fun c : ℝ => -c) (removalFlux_eq_of bridge_removalRate rs u.2.2.2))

@[sa_backward "SemanticsEB.nodeTotalDerivLift"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsEB.nodeTotalDerivLift" := by
  intro σ _ _ N q rs u
  exact (s1 N q rs u).trans
    (congrArg (fun c : ℝ => -c) (removalFlux_eq_of bridge_removalRate rs u.2.2.2)).symm

end Alignment.Shadows.SemanticsEB.NodeTotalDerivLift

/-! ## Balance laws along solutions -/

namespace Alignment.Shadows.SemanticsEB.HasDerivWithinAtEdgeDefectLift

open Alignment.Checks.SemanticsEB

sa_claim "SemanticsEB.hasDerivWithinAtEdgeDefectLift" group "SemanticsEB" required
  text "**Edge balance along EB solutions, with removals.** Let `x` solve the EB field of a T_EB reaction list `rs` within a set of times `I` at the time `t` (`HasDerivWithinAt`), and let `ψ''` be the derivative of `ψ'` at `θ(t)`. Then, within `I` at `t`, `d/dt (θ − φ_S − Σ_X φ_X) = Σ_{(X → ∅, a) ∈ rs} a φ_X`. Removals `X → ∅` make the partner inert: its edges keep `θ` but leave every φ class, so the defect grows."
  impl NEP.hasDerivWithinAt_edgeDefect_lift

/-- Bridge (needs independent review): as `EdgeDefectDerivLift.bridge_removalRate`. -/
@[sa_bridge "SemanticsEB.hasDerivWithinAtEdgeDefectLift"]
theorem bridge_removalRate {σ : Type} (v : σ → ℝ) (r : Rxn σ) :
    Rxn.removalRate v r = RemRate v r :=
  removalRate_eq_aux v r

@[sa_forward "SemanticsEB.hasDerivWithinAtEdgeDefectLift" 1]
theorem fwd1 (h : sa_impl% "SemanticsEB.hasDerivWithinAtEdgeDefectLift") : S1 := by
  intro σ _ _ N q rs x I t hx hψ'
  exact Eq.mp (congrArg (fun c : ℝ => HasDerivWithinAt (fun s => EdgeDef N q (x s)) c I t)
    (removalFlux_eq_of bridge_removalRate rs (x t).2.2.1)) (h N q rs hψ' hx)

@[sa_backward "SemanticsEB.hasDerivWithinAtEdgeDefectLift"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsEB.hasDerivWithinAtEdgeDefectLift" := by
  intro σ _ _ N q rs x I t hψ' hx
  exact Eq.mpr (congrArg (fun c : ℝ => HasDerivWithinAt (fun s => edgeDefect N q (x s)) c I t)
    (removalFlux_eq_of bridge_removalRate rs (x t).2.2.1)) (s1 N q rs x I t hx hψ')

end Alignment.Shadows.SemanticsEB.HasDerivWithinAtEdgeDefectLift

namespace Alignment.Shadows.SemanticsEB.HasDerivWithinAtNodeTotalLift

open Alignment.Checks.SemanticsEB

sa_claim "SemanticsEB.hasDerivWithinAtNodeTotalLift" group "SemanticsEB" required
  text "**Node balance along EB solutions, with removals.** Let `x` solve the EB field of a T_EB reaction list `rs` within a set of times `I` at the time `t`, and let `ψ'` be the derivative of `ψ` at `θ(t)`. Then, within `I` at `t`, `d/dt (S + Σ_X pop_X) = −Σ_{(X → ∅, a) ∈ rs} a pop_X`, where `S = qξψ(θ)`."
  impl NEP.hasDerivWithinAt_nodeTotal_lift

/-- Bridge (needs independent review): as `EdgeDefectDerivLift.bridge_removalRate`. -/
@[sa_bridge "SemanticsEB.hasDerivWithinAtNodeTotalLift"]
theorem bridge_removalRate {σ : Type} (v : σ → ℝ) (r : Rxn σ) :
    Rxn.removalRate v r = RemRate v r :=
  removalRate_eq_aux v r

@[sa_forward "SemanticsEB.hasDerivWithinAtNodeTotalLift" 1]
theorem fwd1 (h : sa_impl% "SemanticsEB.hasDerivWithinAtNodeTotalLift") : S1 := by
  intro σ _ _ N q rs x I t hx hψ
  exact Eq.mp (congrArg (fun c : ℝ => HasDerivWithinAt (fun s => NodeTot N q (x s)) (-c) I t)
    (removalFlux_eq_of bridge_removalRate rs (x t).2.2.2)) (h N q rs hψ hx)

@[sa_backward "SemanticsEB.hasDerivWithinAtNodeTotalLift"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsEB.hasDerivWithinAtNodeTotalLift" := by
  intro σ _ _ N q rs x I t hψ hx
  exact Eq.mpr (congrArg (fun c : ℝ => HasDerivWithinAt (fun s => nodeTotal N q (x s)) (-c) I t)
    (removalFlux_eq_of bridge_removalRate rs (x t).2.2.2)) (s1 N q rs x I t hx hψ)

end Alignment.Shadows.SemanticsEB.HasDerivWithinAtNodeTotalLift

namespace Alignment.Shadows.SemanticsEB.HasDerivAtEdgeDefectLift

open Alignment.Checks.SemanticsEB

sa_claim "SemanticsEB.hasDerivAtEdgeDefectLift" group "SemanticsEB" required
  text "The edge balance law for two-sided derivatives (`hasDerivWithinAt_edgeDefect_lift` with `I = ℝ`)."
  impl NEP.hasDerivAt_edgeDefect_lift

/-- Bridge (needs independent review): as `EdgeDefectDerivLift.bridge_removalRate`. -/
@[sa_bridge "SemanticsEB.hasDerivAtEdgeDefectLift"]
theorem bridge_removalRate {σ : Type} (v : σ → ℝ) (r : Rxn σ) :
    Rxn.removalRate v r = RemRate v r :=
  removalRate_eq_aux v r

@[sa_forward "SemanticsEB.hasDerivAtEdgeDefectLift" 1]
theorem fwd1 (h : sa_impl% "SemanticsEB.hasDerivAtEdgeDefectLift") : S1 := by
  intro σ _ _ N q rs x t hx hψ'
  exact Eq.mp (congrArg (fun c : ℝ => HasDerivAt (fun s => EdgeDef N q (x s)) c t)
    (removalFlux_eq_of bridge_removalRate rs (x t).2.2.1)) (h N q rs hψ' hx)

@[sa_backward "SemanticsEB.hasDerivAtEdgeDefectLift"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsEB.hasDerivAtEdgeDefectLift" := by
  intro σ _ _ N q rs x t hψ' hx
  exact Eq.mpr (congrArg (fun c : ℝ => HasDerivAt (fun s => edgeDefect N q (x s)) c t)
    (removalFlux_eq_of bridge_removalRate rs (x t).2.2.1)) (s1 N q rs x t hx hψ')

end Alignment.Shadows.SemanticsEB.HasDerivAtEdgeDefectLift

namespace Alignment.Shadows.SemanticsEB.HasDerivAtNodeTotalLift

open Alignment.Checks.SemanticsEB

sa_claim "SemanticsEB.hasDerivAtNodeTotalLift" group "SemanticsEB" required
  text "The node balance law for two-sided derivatives (`hasDerivWithinAt_nodeTotal_lift` with `I = ℝ`)."
  impl NEP.hasDerivAt_nodeTotal_lift

/-- Bridge (needs independent review): as `EdgeDefectDerivLift.bridge_removalRate`. -/
@[sa_bridge "SemanticsEB.hasDerivAtNodeTotalLift"]
theorem bridge_removalRate {σ : Type} (v : σ → ℝ) (r : Rxn σ) :
    Rxn.removalRate v r = RemRate v r :=
  removalRate_eq_aux v r

@[sa_forward "SemanticsEB.hasDerivAtNodeTotalLift" 1]
theorem fwd1 (h : sa_impl% "SemanticsEB.hasDerivAtNodeTotalLift") : S1 := by
  intro σ _ _ N q rs x t hx hψ
  exact Eq.mp (congrArg (fun c : ℝ => HasDerivAt (fun s => NodeTot N q (x s)) (-c) t)
    (removalFlux_eq_of bridge_removalRate rs (x t).2.2.2)) (h N q rs hψ hx)

@[sa_backward "SemanticsEB.hasDerivAtNodeTotalLift"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsEB.hasDerivAtNodeTotalLift" := by
  intro σ _ _ N q rs x t hψ hx
  exact Eq.mpr (congrArg (fun c : ℝ => HasDerivAt (fun s => nodeTotal N q (x s)) (-c) t)
    (removalFlux_eq_of bridge_removalRate rs (x t).2.2.2)) (s1 N q rs x t hx hψ)

end Alignment.Shadows.SemanticsEB.HasDerivAtNodeTotalLift

/-! ## Constancy lemmas -/

namespace Alignment.Shadows.SemanticsEB.ConstOfHasDerivWithinAtZero

sa_claim "SemanticsEB.constOfHasDerivWithinAtZero" group "SemanticsEB" required
  text "A real function whose derivative within a convex set `I` vanishes at every point of `I` is constant on `I`: `g t = g t₀` for all `t, t₀ ∈ I`."
  impl NEP.const_of_hasDerivWithinAt_zero

@[sa_forward "SemanticsEB.constOfHasDerivWithinAtZero" 1]
theorem fwd1 (h : sa_impl% "SemanticsEB.constOfHasDerivWithinAtZero") : S1 := by
  intro g I hI hg t ht t₀ ht₀
  exact h hI hg ht₀ ht

@[sa_backward "SemanticsEB.constOfHasDerivWithinAtZero"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsEB.constOfHasDerivWithinAtZero" := by
  intro g I hI hg t₀ t ht₀ ht
  exact s1 g I hI hg t ht t₀ ht₀

end Alignment.Shadows.SemanticsEB.ConstOfHasDerivWithinAtZero

namespace Alignment.Shadows.SemanticsEB.ConstOfHasDerivAtZero

sa_claim "SemanticsEB.constOfHasDerivAtZero" group "SemanticsEB" required
  text "A real function with derivative 0 everywhere is constant."
  impl NEP.const_of_hasDerivAt_zero

/-- The impl gives `g t = g 0` for every `t`; combine two instances. -/
@[sa_forward "SemanticsEB.constOfHasDerivAtZero" 1]
theorem fwd1 (h : sa_impl% "SemanticsEB.constOfHasDerivAtZero") : S1 := by
  intro g hg t t₀
  exact (h hg t).trans (h hg t₀).symm

@[sa_backward "SemanticsEB.constOfHasDerivAtZero"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsEB.constOfHasDerivAtZero" := by
  intro g hg t
  exact s1 g hg t 0

end Alignment.Shadows.SemanticsEB.ConstOfHasDerivAtZero

/-! ## `SemanticsEB.liftXiEqZero` -/

namespace Alignment.Shadows.SemanticsEB.LiftXiEqZero

open Alignment.Checks.SemanticsEB

sa_claim "SemanticsEB.liftXiEqZero" group "SemanticsEB" required
  text "Without exits the ξ-component of the EB field vanishes."
  impl NEP.lift_ξ_eq_zero

/-- Bridge (needs independent review): the trusted Boolean test `Rxn.isExit r = true` vs the
text's "`r` is an exit `s → Y`", i.e. `r = exit Y ν` for some `Y`, `ν`. -/
@[sa_bridge "SemanticsEB.liftXiEqZero"]
theorem bridge_isExit {σ : Type} (r : Rxn σ) :
    r.isExit = true ↔ ∃ (Y : σ) (ν : ℝ), r = Rxn.exit Y ν :=
  isExit_iff_aux r

@[sa_forward "SemanticsEB.liftXiEqZero" 1]
theorem fwd1 (h : sa_impl% "SemanticsEB.liftXiEqZero") : S1 := by
  intro σ _ N q rs u hn
  exact h N q rs (fun r hr => isExit_false_of bridge_isExit r (hn r hr)) u

@[sa_backward "SemanticsEB.liftXiEqZero"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsEB.liftXiEqZero" := by
  intro σ _ N q rs hrs u
  exact s1 N q rs u (fun r hr => notExit_of_isExit_false bridge_isExit r (hrs r hr))

end Alignment.Shadows.SemanticsEB.LiftXiEqZero

/-! ## `SemanticsEB.xiConst` -/

namespace Alignment.Shadows.SemanticsEB.XiConst

open Alignment.Checks.SemanticsEB

sa_claim "SemanticsEB.xiConst" group "SemanticsEB" required
  text "**ξ is constant along EB solutions of exit-free models.** Let `I` be a time interval (a convex set of times) with `0 ∈ I`, and let `x` solve the EB field of a T_EB reaction list `rs` that has no exit `s → Y` on `I` (`HasDerivWithinAt x (lift N q rs (x t)) I t` for `t ∈ I`). Then `ξ(t) = ξ(0)` for every `t ∈ I`. No assumption on the degree data is needed."
  impl NEP.xi_const_any

/-- Bridge (reviewed in `Alignment.ReviewedBridges`): as `LiftXiEqZero.bridge_isExit`. -/
@[sa_bridge "SemanticsEB.xiConst"]
theorem bridge_isExit {σ : Type} (r : Rxn σ) :
    r.isExit = true ↔ ∃ (Y : σ) (ν : ℝ), r = Rxn.exit Y ν :=
  isExit_iff_aux r

/-- The impl is for every species type (no `[Fintype σ]`); exit-freeness goes through the
bridge. -/
@[sa_forward "SemanticsEB.xiConst" 1]
theorem fwd1 (h : sa_impl% "SemanticsEB.xiConst") : S1 := by
  intro σ _ N q rs I x hI h0 hn hx
  exact h N q rs (fun r hr => isExit_false_of bridge_isExit r (hn r hr)) hI h0 hx

@[sa_backward "SemanticsEB.xiConst"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsEB.xiConst" := by
  intro σ _ N q rs hrs I hI h0 x hx
  exact s1 N q rs I x hI h0 (fun r hr => notExit_of_isExit_false bridge_isExit r (hrs r hr)) hx

end Alignment.Shadows.SemanticsEB.XiConst

/-! ## `SemanticsEB.conservation` -/

namespace Alignment.Shadows.SemanticsEB.Conservation

open Alignment.Checks.SemanticsEB

sa_claim "SemanticsEB.conservation" group "SemanticsEB" required
  text "**Edge conservation θ = φ_S + Σ_X φ_X is invariant along removal-free EB solutions.** Design statement (DESIGN_NetworkEpiCore.md §D.4, Evidence): \"The exit terms were checked by hand. Conservation θ = φ_S + Σφ_X holds.\"; amended by §M.1: \"For removal-free T_EB models (no `X → ∅`), θ = φ_S + Σφ_X is invariant along every solution on a time interval: if it holds at t = 0 it holds at every time of the interval. In particular, when ψ'(1) ≠ 0, it holds along solutions from the design's initial condition θ(0) = ξ(0) = 1, Σφ_X(0) = 1 − q.\""
  impl NEP.conservation_invariant NEP.conservation

/-! `sa_impl%` is `conservation_invariant ∧ conservation`. `PhiS N q u` unfolds to
`CNet.phiS N q u.1 u.2.1`. "No removal" is decided structurally (`isRemoval_false_of_not`,
`not_of_isRemoval_false`), with no bridge. -/

@[sa_forward "SemanticsEB.conservation" 1]
theorem fwd1 (h : sa_impl% "SemanticsEB.conservation") : S1 := by
  intro σ _ _ N q rs I x hn hI h0 hx hψ' hrel
  exact h.1 N q rs (fun r hr => isRemoval_false_of_not r (hn r hr)) hI h0 hx hψ' hrel

@[sa_forward "SemanticsEB.conservation" 2]
theorem fwd2 (h : sa_impl% "SemanticsEB.conservation") : S2 := by
  intro σ _ _ N q rs I x hn hI h0 hx hψ' hm hθ0 hξ0 hφ0
  exact h.2 N q hm rs (fun r hr => isRemoval_false_of_not r (hn r hr)) hI h0 hx hψ' hθ0 hξ0 hφ0

@[sa_backward "SemanticsEB.conservation"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "SemanticsEB.conservation" := by
  refine ⟨?_, ?_⟩
  · intro σ _ _ N q rs hrs I hI h0 x hx hψ' hrel
    exact s1 N q rs I x (fun r hr => not_of_isRemoval_false r (hrs r hr)) hI h0 hx hψ' hrel
  · intro σ _ _ N q hm rs hrs I hI h0 x hx hψ' hθ0 hξ0 hφ0
    exact s2 N q rs I x (fun r hr => not_of_isRemoval_false r (hrs r hr)) hI h0 hx hψ' hm
      hθ0 hξ0 hφ0

end Alignment.Shadows.SemanticsEB.Conservation

/-! ## `SemanticsEB.nodeConservation` -/

namespace Alignment.Shadows.SemanticsEB.NodeConservation

open Alignment.Checks.SemanticsEB

sa_claim "SemanticsEB.nodeConservation" group "SemanticsEB" required
  text "**Node conservation S + Σ_X pop_X = 1.** Let `N` be a configuration network with `ψ(1) = 1`, and let `rs` be a T_EB reaction list with no removal `X → ∅`. Let `I` be a time interval (a convex set of times) with `0 ∈ I` and let `x` solve the EB field of `rs` on `I` (`HasDerivWithinAt x (lift N q rs (x t)) I t` for `t ∈ I`), with `ψ'` the derivative of `ψ` at every visited `θ(t)`, `t ∈ I`, and with `θ(0) = 1`, `ξ(0) = 1` and `Σ_X pop_X(0) = 1 − q`. Then `qξ(t)ψ(θ(t)) + Σ_X pop_X(t) = 1` for every `t ∈ I`."
  impl NEP.node_conservation

/-- Bridge (needs independent review): as `RemovalFluxEqZero.bridge_isRemoval`. -/
@[sa_bridge "SemanticsEB.nodeConservation"]
theorem bridge_isRemoval {σ : Type} (r : Rxn σ) :
    r.isRemoval = true ↔ ∃ (X : σ) (a : ℝ), r = Rxn.trans X none a :=
  isRemoval_iff_aux r

/-- `q * ξ * ψ θ` is `CNet.susc N q θ ξ` by definition. -/
@[sa_forward "SemanticsEB.nodeConservation" 1]
theorem fwd1 (h : sa_impl% "SemanticsEB.nodeConservation") : S1 := by
  intro σ _ _ N q rs I x h1 hn hI h0 hx hψ hθ0 hξ0 hp0
  exact h N q h1 rs (fun r hr => isRemoval_false_of bridge_isRemoval r (hn r hr)) hI h0 hx hψ
    hθ0 hξ0 hp0

@[sa_backward "SemanticsEB.nodeConservation"]
theorem bwd (s1 : S1) : sa_impl% "SemanticsEB.nodeConservation" := by
  intro σ _ _ N q h1 rs hrs I hI h0 x hx hψ hθ0 hξ0 hp0
  exact s1 N q rs I x h1 (fun r hr => notRemoval_of_isRemoval_false bridge_isRemoval r (hrs r hr))
    hI h0 hx hψ hθ0 hξ0 hp0

end Alignment.Shadows.SemanticsEB.NodeConservation
