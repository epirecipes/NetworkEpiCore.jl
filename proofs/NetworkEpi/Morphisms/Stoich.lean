import NetworkEpi.Morphisms.Common
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

/-!
# Mass action for reaction networks with multiset stoichiometry

DESIGN_NetworkEpiCore.md §D.7, "Honest feasibility": "The hard parts are [...] the multiset
stoichiometry for D_μ". The Poisson isomorphism M2 lands in mass action of the network `D_μ P`,
whose contacts `S + Φ_J → Φ_X + X + Φ_J` have **two** products. They are not reactions of the
single-product syntax `NRxn σ`, so this module defines mass action for general Petri-net
reactions: a reaction `r : SRxn ι` over a finite species type `ι` has an input multiset `inp`, an
output multiset `out` and a rate constant `k`; its flux at `x : ι → ℝ` is `k · Π_{i ∈ inp} x_i`
(mass action) and its field is `flux · (out − inp)` (the stoichiometric vector).

`ma_eq_stoich` checks this definition against the existing mass-action semantics `maField` of
`NetworkEpi.Semantics.MA`: every T_net reaction `NRxn σ` is a multiset reaction over
`Option σ` (`none` is the susceptible species) with the same mass-action field.
-/

open scoped BigOperators

namespace NEP

/-- A reaction with multiset stoichiometry over the species type `ι`: `inp → out` at the
mass-action rate constant `k`. -/
structure SRxn (ι : Type) where
  /-- The reactant multiset. -/
  inp : Multiset ι
  /-- The product multiset. -/
  out : Multiset ι
  /-- The rate constant. -/
  k : ℝ

variable {ι ι' σ : Type}

/-- The mass-action flux `k · Π_{i ∈ inp} x_i` of a multiset reaction. -/
noncomputable def SRxn.flux (r : SRxn ι) (x : ι → ℝ) : ℝ := r.k * (r.inp.map x).prod

/-- The mass-action field of a multiset reaction: `flux · (out − inp)`, i.e. species `i` changes
at `flux · (count_i(out) − count_i(inp))`. -/
noncomputable def SRxn.field [DecidableEq ι] (r : SRxn ι) (x : ι → ℝ) : ι → ℝ :=
  fun i => r.flux x * ((r.out.count i : ℝ) - (r.inp.count i : ℝ))

/-- The mass-action field of a list of multiset reactions: the sum of the per-reaction fields. -/
noncomputable def sLift [DecidableEq ι] (rs : List (SRxn ι)) (x : ι → ℝ) : ι → ℝ :=
  (rs.map fun r => r.field x).sum

/-- The mass-action model of a list of multiset reactions as an object of `DynSys`. -/
noncomputable def sSys [Fintype ι] [DecidableEq ι] (rs : List (SRxn ι)) : DynSys where
  V := ι → ℝ
  F := sLift rs

/-- The multiset mass-action field is additive in the reaction list. -/
lemma sLift_append [DecidableEq ι] (rs rs' : List (SRxn ι)) (x : ι → ℝ) :
    sLift (rs ++ rs') x = sLift rs x + sLift rs' x := by
  simp [sLift, List.map_append, List.sum_append]

/-- The multiset mass-action field of `rs.flatMap g` is the sum over `r ∈ rs` of the fields of
`g r`. -/
lemma sLift_flatMap [DecidableEq ι] {ρ : Type} (g : ρ → List (SRxn ι)) (rs : List ρ)
    (x : ι → ℝ) : sLift (rs.flatMap g) x = (rs.map fun r => sLift (g r) x).sum := by
  induction rs with
  | nil => simp [sLift]
  | cons r rs ih => rw [List.flatMap_cons, sLift_append, ih, List.map_cons, List.sum_cons]

/-- Relabel the species of a multiset reaction along `g` (image multisets). -/
def SRxn.map (g : ι → ι') (r : SRxn ι) : SRxn ι' := ⟨r.inp.map g, r.out.map g, r.k⟩

/-! ## Agreement with the mass-action semantics of `NRxn` -/

/-- A T_net reaction as a multiset reaction over `Option σ`, where `none` is the susceptible
species `s`: `s + J → X + J` is `{s, J} → {X, J}`, `s → Y` is `{s} → {Y}`, `X → Y` is
`{X} → {Y}`, `X → ∅` is `{X} → 0`, `X → s` is `{X} → {s}` and `X + J → Y + J` is
`{X, J} → {Y, J}` (with `J = none` the susceptible catalyst). -/
def NRxn.toSRxn : NRxn σ → SRxn (Option σ)
  | .contact J X k => ⟨{none, some J}, {some X, some J}, k⟩
  | .exit Y ν => ⟨{none}, {some Y}, ν⟩
  | .trans X (some Y) a => ⟨{some X}, {some Y}, a⟩
  | .trans X none a => ⟨{some X}, 0, a⟩
  | .resus X a => ⟨{some X}, {none}, a⟩
  | .nodeContact X J Y k => ⟨{some X, J}, {some Y, J}, k⟩

/-- The mass-action coordinates `(S, x)` as a function on `Option σ` (`none ↦ S`). -/
def maToS (u : MA σ) : Option σ → ℝ := fun i => i.elim u.1 u.2

/-- The components of `maToS` as continuous linear maps. -/
noncomputable def maToSComp : Option σ → (MA σ →L[ℝ] ℝ)
  | none => ContinuousLinearMap.fst ℝ ℝ _
  | some Z => (ContinuousLinearMap.proj Z).comp (ContinuousLinearMap.snd ℝ ℝ _)

/-- `maToS` as a continuous linear map. -/
noncomputable def maToSL : MA σ →L[ℝ] (Option σ → ℝ) := ContinuousLinearMap.pi maToSComp

/-- `maToSL` is `maToS`. -/
lemma maToSL_apply (u : MA σ) : maToSL u = maToS u := by
  funext i
  cases i <;> rfl

section Agreement
variable [DecidableEq σ]

/-- Per reaction, the `NRxn` mass-action field is the multiset mass-action field. -/
theorem maField_toSRxn (r : NRxn σ) (u : MA σ) :
    maToS (maField r u) = r.toSRxn.field (maToS u) := by
  obtain ⟨S, x⟩ := u
  funext i
  cases r with
  | contact J X k =>
      cases i with
      | none =>
          simp [maToS, maField, NRxn.toSRxn, SRxn.field, SRxn.flux]
          ring
      | some Z =>
          simp only [maToS, maField, NRxn.toSRxn, SRxn.field, SRxn.flux, Option.elim,
            Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
            Multiset.prod_cons, Multiset.prod_singleton, Multiset.count_cons,
            Multiset.count_singleton, Option.some.injEq, reduceCtorEq, if_false, Pi.single_apply]
          split_ifs <;> push_cast <;> ring
  | exit Y ν =>
      cases i with
      | none => simp [maToS, maField, NRxn.toSRxn, SRxn.field, SRxn.flux]
      | some Z =>
          simp only [maToS, maField, NRxn.toSRxn, SRxn.field, SRxn.flux, Option.elim,
            Multiset.map_singleton, Multiset.prod_singleton, Multiset.count_singleton,
            Option.some.injEq, reduceCtorEq, if_false, Pi.single_apply]
          split_ifs <;> push_cast <;> ring
  | trans X Y a =>
      cases Y with
      | none =>
          cases i with
          | none => simp [maToS, maField, NRxn.toSRxn, SRxn.field, SRxn.flux]
          | some Z =>
              simp only [maToS, maField, NRxn.toSRxn, SRxn.field, SRxn.flux, Option.elim,
                Multiset.map_singleton, Multiset.prod_singleton, Multiset.count_singleton,
                Multiset.count_zero, Option.some.injEq, Pi.neg_apply, Pi.single_apply]
              split_ifs <;> push_cast <;> ring
      | some Y =>
          cases i with
          | none => simp [maToS, maField, NRxn.toSRxn, SRxn.field, SRxn.flux]
          | some Z =>
              simp only [maToS, maField, NRxn.toSRxn, SRxn.field, SRxn.flux, Option.elim,
                Multiset.map_singleton, Multiset.prod_singleton, Multiset.count_singleton,
                Option.some.injEq, Pi.sub_apply, Pi.single_apply]
              split_ifs <;> push_cast <;> ring
  | resus X a =>
      cases i with
      | none => simp [maToS, maField, NRxn.toSRxn, SRxn.field, SRxn.flux]
      | some Z =>
          simp only [maToS, maField, NRxn.toSRxn, SRxn.field, SRxn.flux, Option.elim,
            Multiset.map_singleton, Multiset.prod_singleton, Multiset.count_singleton,
            Option.some.injEq, reduceCtorEq, if_false, Pi.neg_apply, Pi.single_apply]
          split_ifs <;> push_cast <;> ring
  | nodeContact X J Y k =>
      cases i with
      | none =>
          cases J <;> simp [maToS, maField, NRxn.toSRxn, SRxn.field, SRxn.flux]
      | some Z =>
          cases J with
          | none =>
              simp only [maToS, maField, NRxn.toSRxn, SRxn.field, SRxn.flux, Option.elim,
                Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
                Multiset.prod_cons, Multiset.prod_singleton, Multiset.count_cons,
                Multiset.count_singleton, Option.some.injEq, reduceCtorEq, if_false,
                Pi.sub_apply, Pi.single_apply]
              split_ifs <;> push_cast <;> ring
          | some J =>
              simp only [maToS, maField, NRxn.toSRxn, SRxn.field, SRxn.flux, Option.elim,
                Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
                Multiset.prod_cons, Multiset.prod_singleton, Multiset.count_cons,
                Multiset.count_singleton, Option.some.injEq, Pi.sub_apply, Pi.single_apply]
              split_ifs <;> push_cast <;> ring

/-- **The multiset mass-action semantics agrees with `maField`.**

Design statement (DESIGN_NetworkEpiCore.md §D.4, row MA): "**MA** | Open(Petri) | x_X | total";
§D.7, "Honest feasibility": "The hard parts are [...] the multiset stoichiometry for D_μ".

Lean statement: for every T_net reaction list `rs` over a finite type of node species (contacts,
exits, progressions, removals, resusceptibility, node contacts), the linear isomorphism
`(S, x) ↦ (none ↦ S, some X ↦ x_X)` is a global semiconjugacy from the mass-action model
`maSys rs` (per-reaction fields `maField`) to the multiset mass-action model of
`rs.map NRxn.toSRxn` (flux `k·Π_{i ∈ inp} x_i`, field `flux·(out − inp)`). So `sSys` extends the
library's mass-action semantics to reactions with several products. -/
theorem ma_eq_stoich [Fintype σ] (rs : List (NRxn σ)) :
    IsSemiconj (maSys rs) (sSys (rs.map NRxn.toSRxn)) maToS := by
  have hL : (maToS (σ := σ)) = ⇑(maToSL (σ := σ)) := funext fun u => (maToSL_apply u).symm
  refine isSemiconj_of_hasFDerivAt (A := maSys rs) (B := sSys (rs.map NRxn.toSRxn))
    (fun _ => maToSL) (fun u => hL ▸ maToSL.hasFDerivAt) fun u => ?_
  change maToSL (maLift rs u) = sLift (rs.map NRxn.toSRxn) (maToS u)
  rw [maLift, clm_list_sum_eq maToSL rs (fun r => maField r u) (fun r => r.toSRxn.field (maToS u))
    fun r _ => by rw [maToSL_apply, maField_toSRxn], sLift, List.map_map]
  rfl

end Agreement

end NEP
