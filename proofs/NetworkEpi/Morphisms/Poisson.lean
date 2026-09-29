import NetworkEpi.Morphisms.Stoich

/-!
# L4b: the Poisson isomorphism EB_{Pois μ}(P) ≅ MA(D_μ P) (M2)

DESIGN_NetworkEpiCore.md §D.5, row **M2**: "Poisson isomorphism | EB_{Pois μ}(P) ≅ MA(D_μ P) via
π(θ, φ, pop) = (qξe^{μ(θ−1)}, Φ = φ, X = pop), natural in P. D_μ: contacts S + Φ_J → Φ_X + X + Φ_J
at rate μτ; Φ_J → ∅ at τ; transitions on both copies | natural iso onto S > 0"; §J.10: "**Exits in
D_μ** (§D.5 M2) are `s → Φ_Y + Y`".

## The construction

The species of `D_μ P` (`DSp σ = Option (σ ⊕ σ)`) are `S` (`none`), an *edge copy* `Φ_X`
(`some (inl X)`) and a *node copy* `X` (`some (inr X)`) of every node species `X`. `D_μ` acts
reaction by reaction (`Rxn.poissonD`), with multiset stoichiometry (`NetworkEpi.Morphisms.Stoich`):

| T_EB reaction of P | reactions of D_μ P |
|---|---|
| contact `s + J → X + J` at τ | `S + Φ_J → Φ_X + X + Φ_J` at `μτ`, and `Φ_J → ∅` at `τ` |
| exit `s → Y` at ν | `S → Φ_Y + Y` at ν |
| transition `X → Y` at a | `Φ_X → Φ_Y` and `X → Y`, both at a |
| removal `X → ∅` at a | `Φ_X → ∅` and `X → ∅`, both at a |

The map is `poissonMap μ q (θ, ξ, φ, pop) = (S = qξe^{μ(θ−1)}, Φ = φ, X = pop)`.

## Results

* `poisson_iso_semiconj`: for every T_EB model (exits allowed) and `μ ≠ 0`, `poissonMap` is a global
  semiconjugacy from EB on Poisson(μ) to MA(D_μ P).
* `poisson_iso`: for every **exit-free** T_EB model, `μ ≠ 0` and `q > 0`, the EB model in the design's
  coordinates `(θ, φ, pop)` is conjugate to MA(D_μ P) restricted to the open set `S > 0`, with
  inverse `(S, Φ, X) ↦ (1 + log(S/q)/μ, Φ, X)`.
* `poisson_iso_natural`: `D_μ` commutes with relabelling species, and the map commutes with the
  pullback and pushforward of coordinates along species maps.
* `poisson_iso_sir`, `poisson_iso_seir`, `poissonD_sir_field`: the SIR and SEIR instances, and the
  explicit mass-action equations of `D_μ(SIR)`.

**With exits** the EB coordinates contain both θ and ξ, and the map `(θ, ξ) ↦ qξe^{μ(θ−1)}` has
one-dimensional fibres, so `poisson_iso_semiconj` is a semiconjugacy but not a conjugacy; the
design's "iso" is the exit-free statement `poisson_iso` (as in M1, whose exit case the design calls
a quotient).
-/

open scoped BigOperators

namespace NEP

variable {σ σ' : Type}

/-- Species of `D_μ P`: `none` is `S`, `some (inl X)` the edge copy `Φ_X`, `some (inr X)` the
node copy `X`. -/
abbrev DSp (σ : Type) := Option (σ ⊕ σ)

/-- `D_μ` of one T_EB reaction (DESIGN §D.5 M2 and §J.10), with multiset stoichiometry. -/
def Rxn.poissonD (μ : ℝ) : Rxn σ → List (SRxn (DSp σ))
  | .contact J X τ =>
      [⟨{none, some (.inl J)}, {some (.inl X), some (.inr X), some (.inl J)}, μ * τ⟩,
        ⟨{some (.inl J)}, 0, τ⟩]
  | .exit Y ν => [⟨{none}, {some (.inl Y), some (.inr Y)}, ν⟩]
  | .trans X (some Y) a =>
      [⟨{some (.inl X)}, {some (.inl Y)}, a⟩, ⟨{some (.inr X)}, {some (.inr Y)}, a⟩]
  | .trans X none a => [⟨{some (.inl X)}, 0, a⟩, ⟨{some (.inr X)}, 0, a⟩]

/-- `D_μ P` for a T_EB reaction list `P`. -/
def poissonRxns (μ : ℝ) (rs : List (Rxn σ)) : List (SRxn (DSp σ)) := rs.flatMap (Rxn.poissonD μ)

/-- The map `(θ, ξ, φ, pop) ↦ (S = qξe^{μ(θ−1)}, Φ = φ, X = pop)`. -/
noncomputable def poissonMap (μ q : ℝ) (u : EB σ) : DSp σ → ℝ :=
  fun i => i.elim ((CNet.poisson μ).susc q u.1 u.2.1) (Sum.elim u.2.2.1 u.2.2.2)

/-- The components of the derivative of `poissonMap μ q` at `u`. -/
noncomputable def poissonDComp (μ q : ℝ) (u : EB σ) : DSp σ → (EB σ →L[ℝ] ℝ)
  | none => suscD (CNet.poisson μ) q u
  | some (.inl X) => (ContinuousLinearMap.proj X).comp ebPhi
  | some (.inr X) => (ContinuousLinearMap.proj X).comp ebPop

/-- The derivative of `poissonMap μ q` at `u`. -/
noncomputable def poissonDL (μ q : ℝ) (u : EB σ) : EB σ →L[ℝ] (DSp σ → ℝ) :=
  ContinuousLinearMap.pi (poissonDComp μ q u)

/-- The `S`-component of `poissonDL`: `q (v_ξ e^{μ(θ−1)} + ξ μ e^{μ(θ−1)} v_θ)`. -/
lemma poissonDL_none (μ q : ℝ) (u v : EB σ) :
    poissonDL μ q u v none =
      q * (v.2.1 * Real.exp (μ * (u.1 - 1)) + u.2.1 * (μ * Real.exp (μ * (u.1 - 1)) * v.1)) := by
  simp only [poissonDL, ContinuousLinearMap.pi_apply, poissonDComp, suscD_apply]
  rfl

/-- The `Φ_X`-component of `poissonDL` is `v_{φ_X}`. -/
lemma poissonDL_inl (μ q : ℝ) (u v : EB σ) (X : σ) :
    poissonDL μ q u v (some (.inl X)) = v.2.2.1 X := rfl

/-- The node-copy `X`-component of `poissonDL` is `v_{pop_X}`. -/
lemma poissonDL_inr (μ q : ℝ) (u v : EB σ) (X : σ) :
    poissonDL μ q u v (some (.inr X)) = v.2.2.2 X := rfl

/-- `poissonMap μ q` has derivative `poissonDL μ q u` at every `u`. -/
lemma hasFDerivAt_poissonMap [Fintype σ] (μ q : ℝ) (u : EB σ) :
    HasFDerivAt (poissonMap μ q) (poissonDL μ q u) u := by
  refine hasFDerivAt_pi'.2 fun i => ?_
  rw [poissonDL, ContinuousLinearMap.proj_pi]
  rcases i with _ | X | X
  · exact hasFDerivAt_susc (CNet.poisson μ) q (CNet.poisson_hasDerivAt_ψ μ u.1)
  · exact ((ContinuousLinearMap.proj X).comp ebPhi).hasFDerivAt
  · exact ((ContinuousLinearMap.proj X).comp ebPop).hasFDerivAt

/-- `poissonMap μ q` has derivative `poissonDL μ q u` at every `u`, for every type `σ` of node
species (no finiteness: the coordinates carry the product topology). -/
theorem hasFDerivAt_poissonMap_all (μ q : ℝ) (u : EB σ) :
    HasFDerivAt (poissonMap μ q) (poissonDL μ q u) u := by
  refine ⟨Asymptotics.IsLittleOTVS.pi fun i => ?_⟩
  rcases i with _ | X | X
  · exact HasFDerivAtFilter.isLittleOTVS
      (hasFDerivAt_susc_any (CNet.poisson μ) q (CNet.poisson_hasDerivAt_ψ μ u.1))
  · refine (Asymptotics.IsLittleOTVS.zero _ _).congr_left ?_
    intro p
    simp [poissonMap, poissonDL, poissonDComp, ebPhi]
  · refine (Asymptotics.IsLittleOTVS.zero _ _).congr_left ?_
    intro p
    simp [poissonMap, poissonDL, poissonDComp, ebPop]

/-- The `S`-component of `poissonDL`, with the products in the order written:
`q (v_ξ e^{μ(θ−1)} + ξ μ e^{μ(θ−1)} v_θ)` (left-associated `ξ μ e^{μ(θ−1)} v_θ`). -/
theorem poissonDL_none_left (μ q : ℝ) (u v : EB σ) :
    poissonDL μ q u v none =
      q * (v.2.1 * Real.exp (μ * (u.1 - 1)) + u.2.1 * μ * Real.exp (μ * (u.1 - 1)) * v.1) := by
  rw [poissonDL_none]
  ring

section Field
variable [DecidableEq σ]

/-- **Per-reaction identity behind M2.** On the Poisson(μ) network with `μ ≠ 0`, the derivative of
`poissonMap` carries the EB field of each T_EB reaction `r` to the multiset mass-action field of
`D_μ r` at the image point. -/
theorem poisson_ebField (μ q : ℝ) (hμ : μ ≠ 0) (r : Rxn σ) (u : EB σ) :
    poissonDL μ q u (ebField (CNet.poisson μ) q r u) = sLift (r.poissonD μ) (poissonMap μ q u) := by
  obtain ⟨θ, ξ, φ, p⟩ := u
  funext i
  cases r with
  | contact J X τ =>
      rcases i with _ | Z | Z
      · simp only [poissonDL_none, ebField, Rxn.poissonD, sLift, SRxn.field, SRxn.flux,
          poissonMap, CNet.susc, CNet.poisson, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, Pi.add_apply, add_zero, Multiset.insert_eq_cons,
          Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton,
          Multiset.count_cons, Multiset.count_singleton, Multiset.count_zero, reduceCtorEq,
          if_true, if_false, Option.elim, Sum.elim_inl]
        push_cast
        ring
      · simp only [poissonDL_inl, ebField, Rxn.poissonD, sLift, SRxn.field, SRxn.flux,
          poissonMap, CNet.susc, CNet.poisson, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, Pi.add_apply, add_zero, Multiset.insert_eq_cons,
          Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton,
          Multiset.count_cons, Multiset.count_singleton, Multiset.count_zero, reduceCtorEq,
          Option.some.injEq, Sum.inl.injEq, if_false, Option.elim, Sum.elim_inl, Pi.sub_apply,
          Pi.single_apply, sub_self, mul_zero, Real.exp_zero, mul_one]
        split_ifs <;> push_cast <;> field_simp <;> ring
      · simp only [poissonDL_inr, ebField, Rxn.poissonD, sLift, SRxn.field, SRxn.flux,
          poissonMap, CNet.susc, CNet.poisson, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, Pi.add_apply, add_zero, Multiset.insert_eq_cons,
          Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton,
          Multiset.count_cons, Multiset.count_singleton, Multiset.count_zero, reduceCtorEq,
          Option.some.injEq, Sum.inr.injEq, if_false, Option.elim, Sum.elim_inl,
          Pi.single_apply]
        split_ifs <;> push_cast <;> ring
  | exit Y ν =>
      rcases i with _ | Z | Z
      · simp only [poissonDL_none, ebField, Rxn.poissonD, sLift, SRxn.field, SRxn.flux,
          poissonMap, CNet.susc, CNet.poisson, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, add_zero, Multiset.insert_eq_cons, Multiset.map_singleton,
          Multiset.prod_singleton, Multiset.count_cons, Multiset.count_singleton, reduceCtorEq,
          if_true, if_false, Option.elim]
        push_cast
        ring
      · simp only [poissonDL_inl, ebField, Rxn.poissonD, sLift, SRxn.field, SRxn.flux,
          poissonMap, CNet.susc, CNet.phiS, CNet.poisson, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, add_zero, Multiset.insert_eq_cons, Multiset.map_singleton,
          Multiset.prod_singleton, Multiset.count_cons, Multiset.count_singleton, reduceCtorEq,
          Option.some.injEq, Sum.inl.injEq, if_false, Option.elim, Pi.single_apply, sub_self,
          mul_zero, Real.exp_zero, mul_one]
        split_ifs <;> push_cast <;> field_simp <;> ring
      · simp only [poissonDL_inr, ebField, Rxn.poissonD, sLift, SRxn.field, SRxn.flux,
          poissonMap, CNet.susc, CNet.poisson, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, add_zero, Multiset.insert_eq_cons, Multiset.map_singleton,
          Multiset.prod_singleton, Multiset.count_cons, Multiset.count_singleton, reduceCtorEq,
          Option.some.injEq, Sum.inr.injEq, if_false, Option.elim, Pi.single_apply]
        split_ifs <;> push_cast <;> ring
  | trans X Y a =>
      cases Y with
      | none =>
          rcases i with _ | Z | Z <;>
            simp only [poissonDL_none, poissonDL_inl, poissonDL_inr, ebField, Rxn.poissonD,
              sLift, SRxn.field, SRxn.flux, poissonMap, List.map_cons, List.map_nil,
              List.sum_cons, List.sum_nil, Pi.add_apply, add_zero,
              Multiset.map_singleton, Multiset.prod_singleton, Multiset.count_singleton,
              Multiset.count_zero, reduceCtorEq, Option.some.injEq, Sum.inl.injEq,
              Sum.inr.injEq, if_false, Option.elim, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply,
              Pi.single_apply, mul_zero, zero_mul, add_zero, Nat.cast_zero, sub_zero,
              zero_sub] <;>
            split_ifs <;> push_cast <;> ring
      | some Y =>
          rcases i with _ | Z | Z <;>
            simp only [poissonDL_none, poissonDL_inl, poissonDL_inr, ebField, Rxn.poissonD,
              sLift, SRxn.field, SRxn.flux, poissonMap, List.map_cons, List.map_nil,
              List.sum_cons, List.sum_nil, Pi.add_apply, add_zero,
              Multiset.map_singleton, Multiset.prod_singleton, Multiset.count_singleton,
              reduceCtorEq, Option.some.injEq, Sum.inl.injEq, Sum.inr.injEq, if_false,
              Option.elim, Sum.elim_inl, Sum.elim_inr, Pi.sub_apply, Pi.single_apply, mul_zero,
              zero_mul, Nat.cast_zero, sub_self] <;>
            split_ifs <;> push_cast <;> ring

/-- **Per-reaction identity behind M2, with the derivative `fderiv`.** For a finite type of node
species, on the Poisson(μ) network with `μ ≠ 0`, the derivative `Dπ(u)` of the Poisson map carries
the EB field of each T_EB reaction `r` to the multiset mass-action field of `D_μ r` at `π(u)`. -/
theorem poisson_ebField_fderiv [Fintype σ] (μ q : ℝ) (hμ : μ ≠ 0) (r : Rxn σ)
    (u : EB σ) :
    fderiv ℝ (poissonMap μ q) u (ebField (CNet.poisson μ) q r u) =
      sLift (r.poissonD μ) (poissonMap μ q u) := by
  rw [(hasFDerivAt_poissonMap μ q u).fderiv]
  exact poisson_ebField μ q hμ r u

/-- **The Poisson map is a semiconjugacy for every T_EB model (M2, with exits).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M2): "Poisson isomorphism | EB_{Pois μ}(P) ≅
MA(D_μ P) via π(θ, φ, pop) = (qξe^{μ(θ−1)}, Φ = φ, X = pop), natural in P. D_μ: contacts
S + Φ_J → Φ_X + X + Φ_J at rate μτ; Φ_J → ∅ at τ; transitions on both copies"; §J.10: "**Exits in
D_μ** (§D.5 M2) are `s → Φ_Y + Y`".

Lean statement: let `σ` be a finite type of node species, `rs` any T_EB reaction list over `σ`
(contacts, exits, progressions and removals), `μ ≠ 0` and `q` real. Then the map
`(θ, ξ, φ, pop) ↦ (S, Φ, X) = (qξe^{μ(θ−1)}, φ, pop)` is a global semiconjugacy from the
per-reaction EB model of `rs` on the Poisson(μ) configuration network with seed factor `q`
(`ebSys`) to the mass-action model, with multiset stoichiometry, of `D_μ rs` (`sSys
(poissonRxns μ rs)`): each contact `s + J → X + J` at τ becomes `S + Φ_J → Φ_X + X + Φ_J` at `μτ`
and `Φ_J → ∅` at `τ`; each exit `s → Y` at ν becomes `S → Φ_Y + Y` at ν; each transition
`X → Y` (or `X → ∅`) at `a` acts on both copies, `Φ_X → Φ_Y` and `X → Y` at `a`.

Scope: with exits this is a semiconjugacy, not a conjugacy (θ and ξ enter only through S); the
isomorphism for exit-free models is `poisson_iso`. -/
theorem poisson_iso_semiconj [Fintype σ] (μ q : ℝ) (hμ : μ ≠ 0) (rs : List (Rxn σ)) :
    IsSemiconj (ebSys (CNet.poisson μ) q rs) (sSys (poissonRxns μ rs)) (poissonMap μ q) := by
  refine isSemiconj_of_hasFDerivAt (A := ebSys (CNet.poisson μ) q rs)
    (B := sSys (poissonRxns μ rs)) (poissonDL μ q) (hasFDerivAt_poissonMap μ q) fun u => ?_
  change poissonDL μ q u (lift (CNet.poisson μ) q rs u) = sLift (poissonRxns μ rs) (poissonMap μ q u)
  rw [poissonRxns, sLift_flatMap, lift]
  exact clm_list_sum_eq _ rs _ _ fun r _ => poisson_ebField μ q hμ r u

/-- The inverse of the Poisson map on `S > 0` for exit-free models:
`(S, Φ, X) ↦ (θ, φ, pop) = (1 + log(S/q)/μ, Φ, X)`. -/
noncomputable def poissonInv (μ q : ℝ) (v : DSp σ → ℝ) : EB1 σ :=
  (1 + Real.log (v none / q) / μ, fun X => v (some (.inl X)), fun X => v (some (.inr X)))

/-- **The Poisson isomorphism for exit-free models (M2).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M2): "Poisson isomorphism | EB_{Pois μ}(P) ≅
MA(D_μ P) via π(θ, φ, pop) = (qξe^{μ(θ−1)}, Φ = φ, X = pop), natural in P. D_μ: contacts
S + Φ_J → Φ_X + X + Φ_J at rate μτ; Φ_J → ∅ at τ; transitions on both copies | natural iso onto
S > 0".

Lean statement: let `σ` be a finite type of node species, `rs` a T_EB reaction list over `σ` with
**no exits** (contacts, progressions and removals), `μ ≠ 0` and `q > 0`. Let `A` be the EB model
of `rs` on the Poisson(μ) network in the coordinates `(θ, φ, pop)` (on the invariant slice ξ = 1,
`ebSys1`), and `B` the multiset mass-action model of `D_μ rs`. Then
`h(θ, φ, pop) = (S, Φ, X) = (q e^{μ(θ−1)}, φ, pop)` and
`g(S, Φ, X) = (1 + log(S/q)/μ, Φ, X)` form a conjugacy between `A` (on all of its state space)
and `B` restricted to the open set `{S > 0}`: `h` is a global semiconjugacy with values in
`{S > 0}`, `g` is a local semiconjugacy on `{S > 0}` with values in the state space of `A`,
`g ∘ h = id` and `h ∘ g = id` on `{S > 0}` (`IsConjOn`).

Scope: exits are excluded (see `poisson_iso_semiconj`); `q > 0` makes `h` land in `S > 0`.
The conjugacy is the same formula for every exit-free P; its compatibility with relabelling is
`poisson_iso_natural`. -/
theorem poisson_iso [Fintype σ] (μ q : ℝ) (hμ : μ ≠ 0) (hq : 0 < q) (rs : List (Rxn σ))
    (hrs : ∀ r ∈ rs, r.isExit = false) :
    IsConjOn (ebSys1 (CNet.poisson μ) q rs) (sSys (poissonRxns μ rs)) Set.univ
      {v | 0 < v none} (poissonMap μ q ∘ EB1.incl) (poissonInv μ q) := by
  have hh : IsSemiconj (ebSys1 (CNet.poisson μ) q rs) (sSys (poissonRxns μ rs))
      (poissonMap μ q ∘ EB1.incl) :=
    ((Semiconj.ofIsSemiconj _ (ebSys1_incl (CNet.poisson μ) q rs hrs)).comp
      (Semiconj.ofIsSemiconj _ (poisson_iso_semiconj μ q hμ rs))).isSemiconj
  refine isConjOn_of_inverse hh (fun v hv => ?_) (fun w => ?_) (fun w => ?_) (fun v hv => ?_)
  · have hv' : v none / q ≠ 0 := (div_pos hv hq).ne'
    change DifferentiableAt ℝ (fun v : DSp σ → ℝ => ((1 + Real.log (v none / q) / μ,
      fun X => v (some (.inl X)), fun X => v (some (.inr X))) : EB1 σ)) v
    fun_prop (disch := exact hv')
  · change 0 < q * 1 * Real.exp (μ * (w.1 - 1))
    positivity
  · obtain ⟨θ, φ, p⟩ := w
    change ((1 + Real.log (q * 1 * Real.exp (μ * (θ - 1)) / q) / μ, φ, p) : EB1 σ) = (θ, φ, p)
    have : q * 1 * Real.exp (μ * (θ - 1)) / q = Real.exp (μ * (θ - 1)) := by
      field_simp
    rw [this, Real.log_exp]
    refine Prod.ext ?_ rfl
    field_simp
    ring
  · simp only [Set.mem_setOf_eq] at hv
    funext i
    rcases i with _ | X | X
    · change q * 1 * Real.exp (μ * (1 + Real.log (v none / q) / μ - 1)) = v none
      have : μ * (1 + Real.log (v none / q) / μ - 1) = Real.log (v none / q) := by
        field_simp
        ring
      rw [this, Real.exp_log (div_pos hv hq)]
      field_simp
    · rfl
    · rfl

/-- **The Poisson isomorphism on trajectories (M2).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M2): "EB_{Pois μ}(P) ≅ MA(D_μ P) via
π(θ, φ, pop) = (qξe^{μ(θ−1)}, Φ = φ, X = pop)"; §D.3: "semiconjugacies map solution curves to
solution curves".

Lean statement: let `rs` be any T_EB reaction list over a finite type of node species (exits
allowed), `μ ≠ 0`, `q` real, and `I` any set of times. If `x : ℝ → EB σ` solves the EB model of
`rs` on the Poisson(μ) network within `I` at every `t ∈ I`, then
`t ↦ (S, Φ, X)(t) = (qξ(t)e^{μ(θ(t)−1)}, φ(t), pop(t))` solves the multiset mass-action model of
`D_μ rs` within `I` at every `t ∈ I`.

Scope: the Poisson(μ) network is taken with `μ ≠ 0`, as in the design, whose Poisson degree
distributions have mean μ > 0 (for `μ = 0` the PGF has `ψ' ≡ 0` and the network has no edges).
Solutions are mapped on any set of times `I`, both for derivatives within `I` (this theorem) and for
two-sided derivatives at every `t ∈ I` (`poisson_iso_solution_at`), as amended by §M.5 and §M.10. -/
theorem poisson_iso_solution [Fintype σ] (μ q : ℝ) (hμ : μ ≠ 0) (rs : List (Rxn σ))
    {I : Set ℝ} {x : ℝ → EB σ}
    (hx : ∀ t ∈ I, HasDerivWithinAt x (lift (CNet.poisson μ) q rs (x t)) I t) :
    ∀ t ∈ I, HasDerivWithinAt (fun t => poissonMap μ q (x t))
      (sLift (poissonRxns μ rs) (poissonMap μ q (x t))) I t :=
  (Semiconj.ofIsSemiconj _ (poisson_iso_semiconj μ q hμ rs)).map_solution_within
    (A := ebSys (CNet.poisson μ) q rs) hx

/-- **The Poisson isomorphism on trajectories with two-sided derivatives (M2).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M2): "EB_{Pois μ}(P) ≅ MA(D_μ P) via
π(θ, φ, pop) = (qξe^{μ(θ−1)}, Φ = φ, X = pop)"; §D.3: "semiconjugacies map solution curves to
solution curves".

Lean statement: let `rs` be any T_EB reaction list over a finite type of node species (exits
allowed), `μ ≠ 0`, `q` real, and `I` any set of times. If `x : ℝ → EB σ` has the two-sided
derivative given by the EB model of `rs` on the Poisson(μ) network at every `t ∈ I`, then
`t ↦ (qξ(t)e^{μ(θ(t)−1)}, φ(t), pop(t))` has the derivative given by the multiset mass-action
model of `D_μ rs` at every `t ∈ I`. (`poisson_iso_solution` is the within-`I` version.) -/
theorem poisson_iso_solution_at [Fintype σ] (μ q : ℝ) (hμ : μ ≠ 0) (rs : List (Rxn σ))
    {I : Set ℝ} {x : ℝ → EB σ}
    (hx : ∀ t ∈ I, HasDerivAt x (lift (CNet.poisson μ) q rs (x t)) t) :
    ∀ t ∈ I, HasDerivAt (fun t => poissonMap μ q (x t))
      (sLift (poissonRxns μ rs) (poissonMap μ q (x t))) t :=
  (Semiconj.ofIsSemiconj _ (poisson_iso_semiconj μ q hμ rs)).map_solution
    (A := ebSys (CNet.poisson μ) q rs) hx

end Field

/-! ## Naturality in P -/

section Natural

/-- The species map of `D_μ` induced by a node-species map `f`. -/
def dMap (f : σ → σ') : DSp σ → DSp σ' := Option.map (Sum.map f f)

/-- `D_μ` commutes with relabelling the node species of one reaction. -/
lemma Rxn.poissonD_map (μ : ℝ) (f : σ → σ') (r : Rxn σ) :
    (r.map f).poissonD μ = (r.poissonD μ).map (SRxn.map (dMap f)) := by
  cases r with
  | contact J X τ =>
      simp [Rxn.map, Rxn.poissonD, SRxn.map, dMap, Multiset.insert_eq_cons]
  | exit Y ν =>
      simp [Rxn.map, Rxn.poissonD, SRxn.map, dMap, Multiset.insert_eq_cons]
  | trans X Y a =>
      cases Y <;> simp [Rxn.map, Rxn.poissonD, SRxn.map, dMap]

/-- **The Poisson isomorphism is natural in P (M2).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M2): "EB_{Pois μ}(P) ≅ MA(D_μ P) via
π(θ, φ, pop) = (qξe^{μ(θ−1)}, Φ = φ, X = pop), natural in P".

Lean statement: for every species map `f : σ → σ'` between finite types and all `μ, q`:
(1) `D_μ` commutes with relabelling: `D_μ (rs.map f) = (D_μ rs).map (dMap f)` for every T_EB
reaction list `rs` over `σ`, where `dMap f` sends `S ↦ S`, `Φ_X ↦ Φ_{f X}` and `X ↦ f X`;
(2) the map commutes with the pullback of coordinates: `π(θ, ξ, φ ∘ f, pop ∘ f) = π(θ, ξ, φ, pop)
∘ dMap f`; (3) it commutes with the pushforward (sums over the fibres of `f`, respectively of
`dMap f`): `π (pushEB f u) = push (dMap f) (π u)`.

Scope: naturality with respect to the species maps of the syntax (relabelling and gluing), as for
`rempala_natural`; it is not stated as a natural transformation of functors into `DynSys`. -/
theorem poisson_iso_natural [Fintype σ] [DecidableEq σ'] (μ q : ℝ) (f : σ → σ') :
    (∀ rs : List (Rxn σ), poissonRxns μ (rs.map (Rxn.map f)) =
      (poissonRxns μ rs).map (SRxn.map (dMap f))) ∧
    (∀ u : EB σ', poissonMap μ q (pullEB f u) = poissonMap μ q u ∘ dMap f) ∧
    (∀ u : EB σ, poissonMap μ q (pushEB f u) = push (dMap f) (poissonMap μ q u)) := by
  refine ⟨fun rs => ?_, fun u => ?_, fun u => ?_⟩
  · induction rs with
    | nil => rfl
    | cons r rs ih =>
        simp only [poissonRxns, List.map_cons, List.flatMap_cons, List.map_append] at ih ⊢
        rw [ih, Rxn.poissonD_map]
  · funext i
    rcases i with _ | X | X <;> rfl
  · funext j
    rcases j with _ | Y | Y <;>
      simp [push, poissonMap, pushEB, dMap, Finset.sum_filter, Fintype.sum_option,
        Fintype.sum_sum_type]

/-- **The Poisson isomorphism is natural in P (M2), with minimal instance assumptions.**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M2): "EB_{Pois μ}(P) ≅ MA(D_μ P) via
π(θ, φ, pop) = (qξe^{μ(θ−1)}, Φ = φ, X = pop), natural in P".

Lean statement: as `poisson_iso_natural`, for every species map `f : σ → σ'` and all `μ, q`, with
each conjunct under only the instances it needs: (1) `D_μ (rs.map f) = (D_μ rs).map (dMap f)`
(any σ, σ'); (2) `π(pullEB f u) = π(u) ∘ dMap f` (any σ, σ'); (3) for finite σ and σ' with
decidable equality, `π(pushEB f u) = push (dMap f) (π u)`. -/
theorem poisson_iso_natural_min (μ q : ℝ) (f : σ → σ') :
    (∀ rs : List (Rxn σ), poissonRxns μ (rs.map (Rxn.map f)) =
      (poissonRxns μ rs).map (SRxn.map (dMap f))) ∧
    (∀ u : EB σ', poissonMap μ q (pullEB f u) = poissonMap μ q u ∘ dMap f) ∧
    (∀ [Fintype σ] [DecidableEq σ'] (u : EB σ),
      poissonMap μ q (pushEB f u) = push (dMap f) (poissonMap μ q u)) := by
  refine ⟨fun rs => ?_, fun u => ?_, fun u => ?_⟩
  · induction rs with
    | nil => rfl
    | cons r rs ih =>
        simp only [poissonRxns, List.map_cons, List.flatMap_cons, List.map_append] at ih ⊢
        rw [ih, Rxn.poissonD_map]
  · funext i
    rcases i with _ | X | X <;> rfl
  · exact (poisson_iso_natural μ q f).2.2 u

end Natural

/-! ## SIR and SEIR -/

section Instances

/-- SIR has no exits. -/
lemma sirRxns_noExit (τ γ : ℝ) : ∀ r ∈ sirRxns τ γ, r.isExit = false := by
  intro r hr
  simp only [sirRxns, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl <;> rfl

/-- SEIR has no exits. -/
lemma seirRxns_noExit (τ a γ : ℝ) : ∀ r ∈ seirRxns τ a γ, r.isExit = false := by
  intro r hr
  simp only [seirRxns, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> rfl

/-- **The mass-action equations of `D_μ(SIR)` (M2, SIR).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M2): "D_μ: contacts S + Φ_J → Φ_X + X + Φ_J at
rate μτ; Φ_J → ∅ at τ; transitions on both copies".

Lean statement: for all real `μ, τ, γ` and every state `v` of the species of `D_μ(SIR)`, with
`S = v none`, `Φ_I, Φ_R` the edge copies and `I, R` the node copies, the multiset mass-action
field of `D_μ(SIR)` (SIR: `s + I → I + I` at per-contact rate τ, `I → R` at γ) is
`Ṡ = −μτSΦ_I`, `Φ̇_I = μτSΦ_I − τΦ_I − γΦ_I`, `Φ̇_R = γΦ_I`, `İ = μτSΦ_I − γI` and `Ṙ = γI`. -/
theorem poissonD_sir_field (μ τ γ : ℝ) (v : DSp SIRSp → ℝ) :
    let F := sLift (poissonRxns μ (sirRxns τ γ)) v
    let S := v none
    let ΦI := v (some (.inl .I))
    let I := v (some (.inr .I))
    F none = -(μ * τ * S * ΦI) ∧
    F (some (.inl .I)) = μ * τ * S * ΦI - τ * ΦI - γ * ΦI ∧
    F (some (.inl .R)) = γ * ΦI ∧
    F (some (.inr .I)) = μ * τ * S * ΦI - γ * I ∧
    F (some (.inr .R)) = γ * I := by
  simp only [poissonRxns, sirRxns, Rxn.poissonD, List.flatMap_cons, List.flatMap_nil,
    List.cons_append, List.nil_append, List.append_nil, sLift, SRxn.field, SRxn.flux,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Pi.add_apply, Pi.zero_apply,
    Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, Multiset.count_cons, Multiset.count_singleton, Multiset.count_zero,
    reduceCtorEq, Option.some.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp <;> ring

/-- **The Poisson isomorphism for SIR (M2, SIR instance).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M2): "Poisson isomorphism | EB_{Pois μ}(P) ≅
MA(D_μ P) via π(θ, φ, pop) = (qξe^{μ(θ−1)}, Φ = φ, X = pop) [...] | natural iso onto S > 0";
§D.7, L4b: "SIR/SEIR concrete first".

Lean statement: for all real `μ ≠ 0`, `τ`, `γ` and `q > 0`, EB SIR (`s + I → I + I` at
per-contact rate τ, `I → R` at γ) on the Poisson(μ) network in the coordinates
`(θ, φ_I, φ_R, pop_I, pop_R)` is conjugate, via `(θ, φ, pop) ↦ (q e^{μ(θ−1)}, φ, pop)` with inverse
`(S, Φ, X) ↦ (1 + log(S/q)/μ, Φ, X)`, to the multiset mass-action model of `D_μ(SIR)` restricted
to `S > 0`, whose equations are those of `poissonD_sir_field`. -/
theorem poisson_iso_sir (μ τ γ q : ℝ) (hμ : μ ≠ 0) (hq : 0 < q) :
    IsConjOn (ebSys1 (CNet.poisson μ) q (sirRxns τ γ)) (sSys (poissonRxns μ (sirRxns τ γ)))
      Set.univ {v | 0 < v none} (poissonMap μ q ∘ EB1.incl) (poissonInv μ q) :=
  poisson_iso μ q hμ hq _ (sirRxns_noExit τ γ)

/-- **The Poisson isomorphism for SEIR (M2, SEIR instance).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M2): "Poisson isomorphism | EB_{Pois μ}(P) ≅
MA(D_μ P) via π(θ, φ, pop) = (qξe^{μ(θ−1)}, Φ = φ, X = pop) [...] | natural iso onto S > 0";
§D.7, L4b: "SIR/SEIR concrete first".

Lean statement: for all real `μ ≠ 0`, `τ`, `σ` (the rate `a` of `E → I`), `γ` and `q > 0`, EB SEIR
(`s + I → E + I` at per-contact rate τ, `E → I` at `a`, `I → R` at γ) on the Poisson(μ) network in
the coordinates `(θ, φ, pop)` is conjugate, via `(θ, φ, pop) ↦ (q e^{μ(θ−1)}, φ, pop)` with inverse
`(S, Φ, X) ↦ (1 + log(S/q)/μ, Φ, X)`, to the multiset mass-action model of `D_μ(SEIR)`
(`S + Φ_I → Φ_E + E + Φ_I` at `μτ`, `Φ_I → ∅` at τ, `Φ_E → Φ_I` and `E → I` at `a`,
`Φ_I → Φ_R` and `I → R` at γ) restricted to `S > 0`. -/
theorem poisson_iso_seir (μ τ a γ q : ℝ) (hμ : μ ≠ 0) (hq : 0 < q) :
    IsConjOn (ebSys1 (CNet.poisson μ) q (seirRxns τ a γ)) (sSys (poissonRxns μ (seirRxns τ a γ)))
      Set.univ {v | 0 < v none} (poissonMap μ q ∘ EB1.incl) (poissonInv μ q) :=
  poisson_iso μ q hμ hq _ (seirRxns_noExit τ a γ)

/-- An `IsConjOn` on all of the source space, unpacked: `h` is a semiconjugacy on the whole space
with values in `U`, and some map is a semiconjugacy on `U` that inverts `h` on both sides. -/
lemma exists_inverse_of_isConjOn {A B : DynSys} {U : Set B.V} {h : A.V → B.V} {g : B.V → A.V}
    (hc : IsConjOn A B Set.univ U h g) :
    IsSemiconjOn A B Set.univ h ∧ (∀ w, h w ∈ U) ∧
      ∃ g' : B.V → A.V, IsSemiconjOn B A U g' ∧ (∀ w, g' (h w) = w) ∧ ∀ v ∈ U, h (g' v) = v :=
  ⟨hc.1, fun w => hc.2.2.1 w trivial,
    ⟨g, hc.2.1, fun w => hc.2.2.2.2.1 w trivial, hc.2.2.2.2.2⟩⟩

/-- **The Poisson isomorphism for SIR, in the form "an isomorphism onto S > 0" (M2, SIR).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M2): "Poisson isomorphism | EB_{Pois μ}(P) ≅
MA(D_μ P) via π(θ, φ, pop) = (qξe^{μ(θ−1)}, Φ = φ, X = pop) [...] | natural iso onto S > 0";
§D.7, L4b: "SIR/SEIR concrete first".

Lean statement: for all real `μ ≠ 0`, `τ`, `γ` and `q > 0`, the map
`h(θ, φ, pop) = (q e^{μ(θ−1)}, φ, pop)` is a semiconjugacy from EB SIR on the Poisson(μ) network
in the coordinates `(θ, φ, pop)` (on all of its state space) to the multiset mass-action model of
`D_μ(SIR)`, it takes values in `{S > 0}`, and there is a map `g` that is a local semiconjugacy on
`{S > 0}` back to EB SIR with `g ∘ h = id` and `h ∘ g = id` on `{S > 0}`. (The inverse is
`poissonInv`, see `poisson_iso_sir`.) -/
theorem poisson_iso_sir_iso (μ τ γ q : ℝ) (hμ : μ ≠ 0) (hq : 0 < q) :
    IsSemiconjOn (ebSys1 (CNet.poisson μ) q (sirRxns τ γ)) (sSys (poissonRxns μ (sirRxns τ γ)))
        Set.univ (poissonMap μ q ∘ EB1.incl) ∧
      (∀ w : EB1 SIRSp, 0 < (poissonMap μ q ∘ EB1.incl) w none) ∧
      ∃ g : (DSp SIRSp → ℝ) → EB1 SIRSp,
        IsSemiconjOn (sSys (poissonRxns μ (sirRxns τ γ))) (ebSys1 (CNet.poisson μ) q (sirRxns τ γ))
          {v | 0 < v none} g ∧
        (∀ w : EB1 SIRSp, g ((poissonMap μ q ∘ EB1.incl) w) = w) ∧
        ∀ v ∈ {v : DSp SIRSp → ℝ | 0 < v none}, (poissonMap μ q ∘ EB1.incl) (g v) = v :=
  exists_inverse_of_isConjOn (poisson_iso_sir μ τ γ q hμ hq)

/-- **The Poisson isomorphism for SEIR, in the form "an isomorphism onto S > 0" (M2, SEIR).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M2): "Poisson isomorphism | EB_{Pois μ}(P) ≅
MA(D_μ P) via π(θ, φ, pop) = (qξe^{μ(θ−1)}, Φ = φ, X = pop) [...] | natural iso onto S > 0";
§D.7, L4b: "SIR/SEIR concrete first".

Lean statement: for all real `μ ≠ 0`, `τ`, `a`, `γ` and `q > 0`, the map
`h(θ, φ, pop) = (q e^{μ(θ−1)}, φ, pop)` is a semiconjugacy from EB SEIR on the Poisson(μ) network
in the coordinates `(θ, φ, pop)` (on all of its state space) to the multiset mass-action model of
`D_μ(SEIR)`, it takes values in `{S > 0}`, and there is a map `g` that is a local semiconjugacy on
`{S > 0}` back to EB SEIR with `g ∘ h = id` and `h ∘ g = id` on `{S > 0}`. -/
theorem poisson_iso_seir_iso (μ τ a γ q : ℝ) (hμ : μ ≠ 0) (hq : 0 < q) :
    IsSemiconjOn (ebSys1 (CNet.poisson μ) q (seirRxns τ a γ))
        (sSys (poissonRxns μ (seirRxns τ a γ))) Set.univ (poissonMap μ q ∘ EB1.incl) ∧
      (∀ w : EB1 SEIRSp, 0 < (poissonMap μ q ∘ EB1.incl) w none) ∧
      ∃ g : (DSp SEIRSp → ℝ) → EB1 SEIRSp,
        IsSemiconjOn (sSys (poissonRxns μ (seirRxns τ a γ)))
          (ebSys1 (CNet.poisson μ) q (seirRxns τ a γ)) {v | 0 < v none} g ∧
        (∀ w : EB1 SEIRSp, g ((poissonMap μ q ∘ EB1.incl) w) = w) ∧
        ∀ v ∈ {v : DSp SEIRSp → ℝ | 0 < v none}, (poissonMap μ q ∘ EB1.incl) (g v) = v :=
  exists_inverse_of_isConjOn (poisson_iso_seir μ τ a γ q hμ hq)

end Instances

end NEP
