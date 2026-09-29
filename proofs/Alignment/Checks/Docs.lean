import Alignment.Registry
import Alignment.Shadows.Docs

/-!
# Checkers: group `Docs` (claims from `proofs/README.md`)

Checker author (SA-PASS role 3, non-blind). The only `implemented` claim of the group is
`Docs.readme.edgeDefectWithRemovals` (README lines 48–52). Its registry `impl` list is
`hasDerivAt_edgeDefect_lift`, `ebField_removal_row`, `ebField_removal_theta`,
`removalFlux_nonneg`, `removalFlux_eq_zero`, so `sa_impl%` is their right-nested conjunction in that order.

## Notions

* "the edge defect `θ − φ_S − Σφ_X`": the shadow helper `defect` has literally the body of
  `NEP.edgeDefect`, so they agree definitionally.
* "`Σ_{(X→∅,a)∈rs} a φ_X`": the shadow helper `remSum rs φ = (rs.map (remTerm φ)).sum`, where
  `remTerm` is the same case table as `NEP.Rxn.removalRate`, so `remSum` unfolds to
  `NEP.removalFlux` definitionally (the kernel accepts the identification; no bridge).
* "without removals": the shadow says `∀ X a, Rxn.trans X none a ∉ rs`; `removalFlux_eq_zero`
  says `∀ r ∈ rs, r.isRemoval = false`. The Boolean test `Rxn.isRemoval` is identified with the
  form `trans X none a` by `bridge_isRemoval` (same statement as the reviewed
  `SemanticsEB.RemovalFluxEqZero.bridge_isRemoval`, re-registered for this claim).

## Backward, pop row

`ebField_removal_row` also states that the pop-components of a removal sum to `−a pop_X`, which
the text does not mention. It follows structurally from S3: the removal row of `ebField` is
`(0, 0, −Pi.single X (aφ_X), −Pi.single X (a pop_X))`, symmetric in `φ` and `pop`, so S3 at the
state with `φ` and `pop` swapped is definitionally the pop statement.
-/

open NEP

namespace Alignment.Shadows.Docs.EdgeDefectWithRemovals

sa_claim "Docs.readme.edgeDefectWithRemovals" group "Docs" required
  text "For any reaction list, `d/dt (θ − φ_S − Σφ_X) = Σ_{(X→∅,a)∈rs} a φ_X` (`hasDerivAt_edgeDefect_lift`). A removal leaves θ unchanged and lowers Σφ by aφ_X (the partner becomes inert: its edges stay in θ but leave every φ class; `ebField_removal_row`), so the rate is non-negative when the removal rates and the φ_X are non-negative (`removalFlux_nonneg`). Without removals the rate is 0 (`removalFlux_eq_zero`)."
  impl NEP.hasDerivAt_edgeDefect_lift NEP.ebField_removal_row NEP.ebField_removal_theta
    NEP.removalFlux_nonneg NEP.removalFlux_eq_zero

/-! ### Helpers (alignment library, inlined by the audit) -/

/-- `false = true` is absurd, by kernel reduction of a `Bool` eliminator into `Prop`. -/
theorem boolFalseNeTrue (h : false = true) : False :=
  Eq.mp (congrArg (fun b : Bool => Bool.rec (motive := fun _ => Prop) True False b) h) trivial

/-- A reaction not of the form `trans X none a` has `isRemoval = false`, given `hb` (a bridge). -/
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

theorem isRemoval_iff_aux {σ : Type} (r : Rxn σ) :
    r.isRemoval = true ↔ ∃ (X : σ) (a : ℝ), r = Rxn.trans X none a := by
  cases r with
  | contact J X τ => simp [Rxn.isRemoval]
  | exit Y ν => simp [Rxn.isRemoval]
  | trans X Y a => cases Y <;> simp [Rxn.isRemoval]

/-- Bridge (needs independent review): the trusted Boolean test `Rxn.isRemoval r = true` vs the
text's "removal `X → ∅`", i.e. `r` has the form `trans X none a`. Same statement as the reviewed
`SemanticsEB.RemovalFluxEqZero.bridge_isRemoval`. -/
@[sa_bridge "Docs.readme.edgeDefectWithRemovals"]
theorem bridge_isRemoval {σ : Type} (r : Rxn σ) :
    r.isRemoval = true ↔ ∃ (X : σ) (a : ℝ), r = Rxn.trans X none a :=
  isRemoval_iff_aux r

/-! ### Forward checkers -/

/-- S1: the balance law; `defect` is `edgeDefect` and `remSum` is `removalFlux` definitionally. -/
@[sa_forward "Docs.readme.edgeDefectWithRemovals" 1]
theorem fwd1 (h : sa_impl% "Docs.readme.edgeDefectWithRemovals") : S1 := by
  intro σ _ _ N q rs x t hx hψ'
  exact h.1 N q rs hψ' hx

/-- S2: θ-component of a removal's field is 0 (`ebField_removal_theta`, any `σ`). -/
@[sa_forward "Docs.readme.edgeDefectWithRemovals" 2]
theorem fwd2 (h : sa_impl% "Docs.readme.edgeDefectWithRemovals") : S2 := by
  intro σ _ N q X a u
  exact h.2.2.1 N q X a u

/-- S3: φ-components of a removal's field sum to `−aφ_X` (second conjunct). -/
@[sa_forward "Docs.readme.edgeDefectWithRemovals" 3]
theorem fwd3 (h : sa_impl% "Docs.readme.edgeDefectWithRemovals") : S3 := by
  intro σ _ _ N q X a u
  exact (h.2.1 N q X a u).2.1

/-- S4: non-negativity of the removal sum (`removalFlux_nonneg`, `remSum` ≡ `removalFlux`). -/
@[sa_forward "Docs.readme.edgeDefectWithRemovals" 4]
theorem fwd4 (h : sa_impl% "Docs.readme.edgeDefectWithRemovals") : S4 := by
  intro σ rs φ ha hφ
  exact h.2.2.2.1 rs φ ha hφ

/-- S5: without removals the removal sum is 0 (`removalFlux_eq_zero` via `bridge_isRemoval`). -/
@[sa_forward "Docs.readme.edgeDefectWithRemovals" 5]
theorem fwd5 (h : sa_impl% "Docs.readme.edgeDefectWithRemovals") : S5 := by
  intro σ rs φ hno
  exact h.2.2.2.2 rs
    (fun r hr => isRemoval_false_of bridge_isRemoval r
      (fun X a he => hno X a (Eq.mp (congrArg (fun r' => r' ∈ rs) he) hr))) φ

/-! ### Backward checker -/

@[sa_backward "Docs.readme.edgeDefectWithRemovals"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) :
    sa_impl% "Docs.readme.edgeDefectWithRemovals" := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro σ _ _ N q rs x t hψ' hx
    exact s1 N q rs x t hx hψ'
  · intro σ _ _ N q X a u
    refine ⟨s2 N q X a u, s3 N q X a u, ?_⟩
    -- the pop row: S3 at the state with φ and pop swapped (the removal row is symmetric)
    exact s3 N q X a (u.1, u.2.1, u.2.2.2, u.2.2.1)
  · intro σ _ N q X a u
    exact s2 N q X a u
  · intro σ rs v ha hv
    exact s4 rs v ha hv
  · intro σ rs hrs v
    exact s5 rs v (fun X a hm => notRemoval_of_isRemoval_false bridge_isRemoval _ (hrs _ hm) X a rfl)

end Alignment.Shadows.Docs.EdgeDefectWithRemovals
