import NetworkEpi.Morphisms.Common

/-!
# L4c: Rempała's quotient for every T_EB model (M3)

DESIGN_NetworkEpiCore.md §D.5, row **M3**: "**Rempała quotient** ("back to mass action on the same
species") | EB_{Pois μ}(P) → MA(E_μ P), E_μ P = c_μ P + {J_r → ∅ at τ_r} on the edge copies;
π = (θ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ). For SIR: MA(β = μτ, γ_MA = γ + τ). **The MA "I" is φ_I, not
prevalence** | natural semiconjugacy (surjective submersion)"; §J.10: "**Exits in D_μ** (§D.5 M2) are
`s → Φ_Y + Y`; in E_μ they stay `S → V`."

## The construction

`E_μ` acts reaction by reaction (`Rxn.rempala`):

| T_EB reaction of P | reactions of E_μ P (T_net, mass action) |
|---|---|
| contact `s + J → X + J` at τ | contact `S + J → X + J` at `μτ`, and removal `J → ∅` at `τ` |
| exit `s → Y` at ν | exit `S → Y` at ν |
| transition `X → Y` / `X → ∅` at a | the same transition |

The map is `rempalaMap μ q (θ, ξ, φ, pop) = (qξe^{μ(θ−1)}, φ)`: the MA species `X` carries the
EB edge probability `φ_X`, not the node fraction `pop_X`.

## Results

* `rempala_general`: for every T_EB reaction list `P` (contacts, exits, progressions, removals;
  any number of infectors and entry states) and every `μ ≠ 0`, `rempalaMap μ q` is a global
  semiconjugacy from the EB model of `P` on a Poisson(μ) configuration network to the mass-action
  model of `E_μ P`.
* `rempala_general_solution`, `rempala_general_solution_at`: EB solutions on any set of times I
  (for example a time interval) map to MA solutions, both for derivatives within I and for
  two-sided derivatives at every time of I.
* `rempala_natural`: `E_μ` commutes with relabelling species, and the map commutes with the
  pushforward and pullback of coordinates along species maps.
* `rempalaMap_surjective`, `rempalaD_surjective`: for `q ≠ 0` the map and its derivative at every
  point are surjective (a surjective submersion, i.e. a quotient).
* `rempala_general_sir`: for SIR, composing with the projection `(S, x) ↦ (S, x_I)` gives
  mass-action SIR with `β = μτ`, `ρ = γ + τ`, the SIR case `NEP.rempala`, now without the
  restriction `ξ = 1`.
-/

open scoped BigOperators

namespace NEP

variable {σ σ' : Type}

/-- `E_μ` of one T_EB reaction (DESIGN §D.5 M3 and §J.10): a contact `s + J → X + J` at τ becomes
the mass-action contact `S + J → X + J` at `μτ` together with the removal `J → ∅` at `τ` on the
edge copy; exits and transitions are unchanged. -/
def Rxn.rempala (μ : ℝ) : Rxn σ → List (NRxn σ)
  | .contact J X τ => [.contact J X (μ * τ), .trans J none τ]
  | .exit Y ν => [.exit Y ν]
  | .trans X Y a => [.trans X Y a]

/-- `E_μ P` for a T_EB reaction list `P`: the concatenation of `E_μ` of its reactions. -/
def rempalaRxns (μ : ℝ) (rs : List (Rxn σ)) : List (NRxn σ) := rs.flatMap (Rxn.rempala μ)

/-- Rempała's map `(θ, ξ, φ, pop) ↦ (S, x) = (qξe^{μ(θ−1)}, φ)`. -/
noncomputable def rempalaMap (μ q : ℝ) (u : EB σ) : MA σ :=
  ((CNet.poisson μ).susc q u.1 u.2.1, u.2.2.1)

/-- The derivative of `rempalaMap μ q` at `u`. -/
noncomputable def rempalaD (μ q : ℝ) (u : EB σ) : EB σ →L[ℝ] MA σ :=
  (suscD (CNet.poisson μ) q u).prod ebPhi

/-- `rempalaD μ q u v = (q (v_ξ e^{μ(θ−1)} + ξ μ e^{μ(θ−1)} v_θ), v_φ)`. -/
lemma rempalaD_apply (μ q : ℝ) (u v : EB σ) :
    rempalaD μ q u v =
      (q * (v.2.1 * Real.exp (μ * (u.1 - 1)) + u.2.1 * (μ * Real.exp (μ * (u.1 - 1)) * v.1)),
        v.2.2.1) := by
  simp only [rempalaD, ContinuousLinearMap.prod_apply, suscD_apply, ebPhi_apply]
  rfl

/-- `rempalaMap μ q` has derivative `rempalaD μ q u` at every `u`. -/
lemma hasFDerivAt_rempalaMap [Fintype σ] (μ q : ℝ) (u : EB σ) :
    HasFDerivAt (rempalaMap μ q) (rempalaD μ q u) u :=
  (hasFDerivAt_susc (CNet.poisson μ) q (CNet.poisson_hasDerivAt_ψ μ u.1)).prodMk
    (hasFDerivAt_ebPhi u)

/-- `rempalaMap μ q` has derivative `rempalaD μ q u` at every `u`, for every type `σ` of node
species (no finiteness: the φ and pop coordinates carry the product topology). -/
theorem hasFDerivAt_rempalaMap_all (μ q : ℝ) (u : EB σ) :
    HasFDerivAt (rempalaMap μ q) (rempalaD μ q u) u := by
  have h1 := hasFDerivAt_susc_any (CNet.poisson μ) q (CNet.poisson_hasDerivAt_ψ μ u.1)
  have h2 := (hasFDerivAt_ebCoordinates_any u).2.2.1
  refine ⟨?_⟩
  exact (HasFDerivAtFilter.isLittleOTVS h1).prodMk (HasFDerivAtFilter.isLittleOTVS h2)

/-- `rempalaD μ q u v = (q (v_ξ e^{μ(θ−1)} + ξ μ e^{μ(θ−1)} v_θ), v_φ)`, componentwise, with the
products in the order written (left-associated `ξ μ e^{μ(θ−1)} v_θ`). -/
theorem rempalaD_apply_left (μ q : ℝ) (u v : EB σ) :
    (rempalaD μ q u v).1 =
        q * (v.2.1 * Real.exp (μ * (u.1 - 1)) + u.2.1 * μ * Real.exp (μ * (u.1 - 1)) * v.1) ∧
      (rempalaD μ q u v).2 = v.2.2.1 := by
  rw [rempalaD_apply]
  exact ⟨by ring, rfl⟩

section Field
variable [Fintype σ] [DecidableEq σ]

omit [Fintype σ] in
/-- **Per-reaction identity behind M3.** On the Poisson(μ) network with `μ ≠ 0`, the derivative of
Rempała's map carries the EB field of each T_EB reaction `r` to the mass-action field of
`E_μ r` at the image point. -/
theorem rempala_ebField (μ q : ℝ) (hμ : μ ≠ 0) (r : Rxn σ) (u : EB σ) :
    rempalaD μ q u (ebField (CNet.poisson μ) q r u) = maLift (r.rempala μ) (rempalaMap μ q u) := by
  obtain ⟨θ, ξ, φ, p⟩ := u
  cases r with
  | contact J X τ =>
      simp only [rempalaD_apply, ebField, Rxn.rempala, maLift, maField, rempalaMap, CNet.susc,
        CNet.poisson, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        sub_self, mul_zero, Real.exp_zero, mul_one]
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add]
        ring
      · funext Z
        simp only [Prod.snd_add, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.single_apply]
        split_ifs <;> field_simp <;> ring
  | exit Y ν =>
      simp only [rempalaD_apply, ebField, Rxn.rempala, maLift, maField, rempalaMap, CNet.susc,
        CNet.phiS, CNet.poisson, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, sub_self, mul_zero, Real.exp_zero, mul_one]
      refine Prod.ext ?_ ?_
      · ring
      · funext Z
        simp only [Pi.single_apply]
        split_ifs <;> field_simp
  | trans X Y a =>
      cases Y <;>
        simp [rempalaD_apply, ebField, Rxn.rempala, maLift, maField, rempalaMap]

/-- **Rempała's quotient for every T_EB model (M3, general P).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M3): "**Rempała quotient** ("back to mass
action on the same species") | EB_{Pois μ}(P) → MA(E_μ P), E_μ P = c_μ P + {J_r → ∅ at τ_r} on
the edge copies; π = (θ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ). For SIR: MA(β = μτ, γ_MA = γ + τ). **The MA
"I" is φ_I, not prevalence** | natural semiconjugacy (surjective submersion)"; §J.10: "**Exits in D_μ** (§D.5 M2) are
`s → Φ_Y + Y`; in E_μ they stay `S → V`."

Lean statement: let `σ` be a finite type of node species, `rs` any T_EB reaction list over `σ`
(contacts `s + J → X + J` at per-contact rates τ, exits `s → Y`, progressions `X → Y` and
removals `X → ∅`, in any number), `μ ≠ 0` and `q` real. Then the map
`(θ, ξ, φ, pop) ↦ (S, x) = (qξe^{μ(θ−1)}, φ)` is a global semiconjugacy (differentiable, with
`Dπ(u)·F(u) = G(π(u))` at every state `u`) from the per-reaction EB model of `rs` on the Poisson(μ)
configuration network `ψ(x) = e^{μ(x−1)}` with seed factor `q` (`ebSys`) to the mass-action model
(`maSys`) of `E_μ rs = rempalaRxns μ rs`, in which each contact `s + J → X + J` at τ becomes
`S + J → X + J` at `μτ` plus `J → ∅` at `τ`, and exits and transitions are unchanged.

Scope: the MA coordinate `x_X` is the EB edge probability `φ_X`, not the node fraction `pop_X`,
which the map forgets. The surjective-submersion property is `rempala_quotient`; naturality is
`rempala_natural`. -/
theorem rempala_general (μ q : ℝ) (hμ : μ ≠ 0) (rs : List (Rxn σ)) :
    IsSemiconj (ebSys (CNet.poisson μ) q rs) (maSys (rempalaRxns μ rs)) (rempalaMap μ q) := by
  refine isSemiconj_of_hasFDerivAt (A := ebSys (CNet.poisson μ) q rs)
    (B := maSys (rempalaRxns μ rs)) (rempalaD μ q) (hasFDerivAt_rempalaMap μ q) fun u => ?_
  change rempalaD μ q u (lift (CNet.poisson μ) q rs u) =
    maLift (rempalaRxns μ rs) (rempalaMap μ q u)
  rw [rempalaRxns, maLift_flatMap, lift]
  exact clm_list_sum_eq _ rs _ _ fun r _ => rempala_ebField μ q hμ r u

/-- **Rempała's quotient on trajectories (M3, general P).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M3): "EB_{Pois μ}(P) → MA(E_μ P), E_μ P = c_μ P
+ {J_r → ∅ at τ_r} on the edge copies; π = (θ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ)"; §D.3:
"semiconjugacies map solution curves to solution curves".

Lean statement: let `rs` be any T_EB reaction list over a finite type of node species, `μ ≠ 0`
and `q` real, and let `I` be any set of times (for example a time interval `[0, T)`). If
`x : ℝ → EB σ` solves the EB model of `rs` on the Poisson(μ) network within `I` at every `t ∈ I`
(`HasDerivWithinAt x (lift … (x t)) I t`), then `t ↦ (qξ(t)e^{μ(θ(t)−1)}, φ(t))` solves the
mass-action model of `E_μ rs` within `I` at every `t ∈ I`. No condition on `ξ(0)` is needed. -/
theorem rempala_general_solution (μ q : ℝ) (hμ : μ ≠ 0) (rs : List (Rxn σ)) {I : Set ℝ}
    {x : ℝ → EB σ}
    (hx : ∀ t ∈ I, HasDerivWithinAt x (lift (CNet.poisson μ) q rs (x t)) I t) :
    ∀ t ∈ I, HasDerivWithinAt (fun t => rempalaMap μ q (x t))
      (maLift (rempalaRxns μ rs) (rempalaMap μ q (x t))) I t :=
  (Semiconj.ofIsSemiconj _ (rempala_general μ q hμ rs)).map_solution_within
    (A := ebSys (CNet.poisson μ) q rs) hx

/-- **Rempała's quotient on trajectories with two-sided derivatives (M3, general P).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M3): "EB_{Pois μ}(P) → MA(E_μ P), E_μ P = c_μ P
+ {J_r → ∅ at τ_r} on the edge copies; π = (θ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ)"; §D.3:
"semiconjugacies map solution curves to solution curves".

Lean statement: let `rs` be any T_EB reaction list over a finite type of node species, `μ ≠ 0`
and `q` real, and let `I` be any set of times. If `x : ℝ → EB σ` has the two-sided derivative
`x'(t) = lift … (x(t))` of the EB model of `rs` on the Poisson(μ) network at every `t ∈ I`, then
`t ↦ (qξ(t)e^{μ(θ(t)−1)}, φ(t))` has the derivative given by the mass-action model of `E_μ rs`
at every `t ∈ I`. (`rempala_general_solution` is the within-`I` version.) No condition on `ξ(0)`
is needed. -/
theorem rempala_general_solution_at (μ q : ℝ) (hμ : μ ≠ 0) (rs : List (Rxn σ)) {I : Set ℝ}
    {x : ℝ → EB σ} (hx : ∀ t ∈ I, HasDerivAt x (lift (CNet.poisson μ) q rs (x t)) t) :
    ∀ t ∈ I, HasDerivAt (fun t => rempalaMap μ q (x t))
      (maLift (rempalaRxns μ rs) (rempalaMap μ q (x t))) t :=
  (Semiconj.ofIsSemiconj _ (rempala_general μ q hμ rs)).map_solution
    (A := ebSys (CNet.poisson μ) q rs) hx

end Field

/-! ## Naturality in P and the quotient property -/

section Natural

/-- `E_μ` commutes with relabelling the node species of one reaction. -/
lemma Rxn.rempala_map (μ : ℝ) (f : σ → σ') (r : Rxn σ) :
    (r.map f).rempala μ = (r.rempala μ).map (NRxn.map f) := by
  cases r with
  | trans X Y a => cases Y <;> rfl
  | _ => rfl

/-- The pullback of Rempała's map: `π(θ, ξ, φ ∘ f, pop ∘ f) = pullMA f (π(θ, ξ, φ, pop))`. -/
lemma rempalaMap_pull (μ q : ℝ) (f : σ → σ') (u : EB σ') :
    rempalaMap μ q (pullEB f u) = pullMA f (rempalaMap μ q u) := rfl

/-- The pushforward of Rempała's map: `π(pushEB f u) = pushMA f (π u)`. -/
lemma rempalaMap_push [Fintype σ] [DecidableEq σ'] (μ q : ℝ) (f : σ → σ') (u : EB σ) :
    rempalaMap μ q (pushEB f u) = pushMA f (rempalaMap μ q u) := rfl

/-- **Rempała's quotient is natural in P (M3).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M3): "EB_{Pois μ}(P) → MA(E_μ P), E_μ P = c_μ P
+ {J_r → ∅ at τ_r} on the edge copies; π = (θ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ) [...] | natural
semiconjugacy (surjective submersion)".

Lean statement: for every species map `f : σ → σ'` (σ finite) and all `μ, q`:
(1) `E_μ` commutes with relabelling: `E_μ (rs.map f) = (E_μ rs).map f` for every T_EB reaction
list `rs` over `σ`; (2) the map commutes with the pushforward of coordinates along `f`
(θ, ξ kept, φ and pop summed over fibres; `S` kept, `x` summed over fibres):
`π (pushEB f u) = pushMA f (π u)`; (3) it commutes with the pullback (precomposition with `f`):
`π (pullEB f u) = pullMA f (π u)`. Together with `lift_map` and `maLift_map` these say that the
components `π` of M3 are compatible with relabelling and gluing species.

Scope: this is naturality with respect to the species maps of the syntax (relabelling and
gluing, DESIGN §D.1); it is not stated as a natural transformation of functors into `DynSys`. -/
theorem rempala_natural [Fintype σ] [DecidableEq σ'] (μ q : ℝ) (f : σ → σ') :
    (∀ rs : List (Rxn σ), rempalaRxns μ (rs.map (Rxn.map f)) =
      (rempalaRxns μ rs).map (NRxn.map f)) ∧
    (∀ u : EB σ, rempalaMap μ q (pushEB f u) = pushMA f (rempalaMap μ q u)) ∧
    (∀ u : EB σ', rempalaMap μ q (pullEB f u) = pullMA f (rempalaMap μ q u)) := by
  refine ⟨fun rs => ?_, fun u => rfl, fun u => rfl⟩
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      simp only [rempalaRxns, List.map_cons, List.flatMap_cons, List.map_append] at ih ⊢
      rw [ih, Rxn.rempala_map]

/-- **Rempała's quotient is natural in P (M3), with minimal instance assumptions.**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M3): "EB_{Pois μ}(P) → MA(E_μ P), E_μ P = c_μ P
+ {J_r → ∅ at τ_r} on the edge copies; π = (θ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ) [...] | natural
semiconjugacy (surjective submersion)".

Lean statement: as `rempala_natural`, for every species map `f : σ → σ'` and all `μ, q`, but
each conjunct with only the instances it needs: (1) `E_μ (rs.map f) = (E_μ rs).map f` for every
T_EB list `rs` (any σ, σ'); (2) for finite σ and σ' with decidable equality,
`π (pushEB f u) = pushMA f (π u)`; (3) `π (pullEB f u) = pullMA f (π u)` (any σ, σ'). -/
theorem rempala_natural_min (μ q : ℝ) (f : σ → σ') :
    (∀ rs : List (Rxn σ), rempalaRxns μ (rs.map (Rxn.map f)) =
      (rempalaRxns μ rs).map (NRxn.map f)) ∧
    (∀ [Fintype σ] [DecidableEq σ'] (u : EB σ),
      rempalaMap μ q (pushEB f u) = pushMA f (rempalaMap μ q u)) ∧
    (∀ u : EB σ', rempalaMap μ q (pullEB f u) = pullMA f (rempalaMap μ q u)) := by
  refine ⟨fun rs => ?_, fun _ => rfl, fun _ => rfl⟩
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      simp only [rempalaRxns, List.map_cons, List.flatMap_cons, List.map_append] at ih ⊢
      rw [ih, Rxn.rempala_map]

/-- For `q ≠ 0` Rempała's map is surjective: `(S, x)` is the image of
`(1, S/q, x, 0)` (θ = 1, ξ = S/q, φ = x). -/
theorem rempalaMap_surjective (μ q : ℝ) (hq : q ≠ 0) :
    Function.Surjective (rempalaMap (σ := σ) μ q) := by
  intro v
  refine ⟨(1, v.1 / q, v.2, 0), ?_⟩
  simp only [rempalaMap, CNet.susc, CNet.poisson, sub_self, mul_zero, Real.exp_zero, mul_one]
  refine Prod.ext ?_ rfl
  field_simp

/-- For `q ≠ 0` Rempała's map is surjective, and `(S, x)` is the image of `(1, S/q, x, 0)`
(θ = 1, ξ = S/q, φ = x, pop = 0). -/
theorem rempalaMap_surjective_preimage (μ q : ℝ) (hq : q ≠ 0) :
    Function.Surjective (rempalaMap (σ := σ) μ q) ∧
      ∀ (S : ℝ) (x : σ → ℝ), rempalaMap μ q ((1, S / q, x, 0) : EB σ) = (S, x) := by
  refine ⟨rempalaMap_surjective μ q hq, fun S x => ?_⟩
  simp only [rempalaMap, CNet.susc, CNet.poisson, sub_self, mul_zero, Real.exp_zero, mul_one]
  refine Prod.ext ?_ rfl
  field_simp

/-- For `q ≠ 0` the derivative of Rempała's map is surjective at every point (the map is a
submersion). -/
theorem rempalaD_surjective (μ q : ℝ) (hq : q ≠ 0) (u : EB σ) :
    Function.Surjective (rempalaD μ q u) := by
  intro v
  refine ⟨(0, v.1 / (q * Real.exp (μ * (u.1 - 1))), v.2, 0), ?_⟩
  rw [rempalaD_apply]
  refine Prod.ext ?_ rfl
  have he : Real.exp (μ * (u.1 - 1)) ≠ 0 := (Real.exp_pos _).ne'
  simp only [mul_zero, add_zero]
  field_simp

/-- **Rempała's map is a surjective submersion (M3).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M3): "π = (θ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ) [...]
| natural semiconjugacy (surjective submersion)".

Lean statement: for all real `μ` and `q ≠ 0` and every finite type of node species, the map
`(θ, ξ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ)` from `EB σ` to `MA σ` is surjective, and its derivative
`(dθ, dξ, dφ, dpop) ↦ (q(e^{μ(θ−1)} dξ + ξμe^{μ(θ−1)} dθ), dφ)` is surjective at every point. -/
theorem rempala_quotient (μ q : ℝ) (hq : q ≠ 0) :
    Function.Surjective (rempalaMap (σ := σ) μ q) ∧
      ∀ u : EB σ, Function.Surjective (rempalaD μ q u) :=
  ⟨rempalaMap_surjective μ q hq, rempalaD_surjective μ q hq⟩

/-! ## The SIR case -/

/-- The projection `(S, x) ↦ (S, x_I)` from mass action on the SIR species to the `(S, I)`
plane. -/
def sirProj (v : MA SIRSp) : ℝ × ℝ := (v.1, v.2 .I)

/-- `sirProj` as a continuous linear map. -/
noncomputable def sirProjL : MA SIRSp →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ _).prod ((ContinuousLinearMap.proj SIRSp.I).comp
    (ContinuousLinearMap.snd ℝ ℝ _))

/-- `E_μ` of SIR, projected to `(S, x_I)`, is mass-action SIR with `β = μτ` and `ρ = γ + τ`,
pointwise: the projection of the mass-action field of `E_μ(SIR)` at `v` is the field of
mass-action SIR at the projected point. -/
theorem rempala_sir_proj_field (μ τ γ : ℝ) (v : MA SIRSp) :
    sirProj (maLift (rempalaRxns μ (sirRxns τ γ)) v) = (maSIR (μ * τ) (γ + τ)).F (sirProj v) := by
  obtain ⟨S, x⟩ := v
  have hIR : (SIRSp.I : SIRSp) ≠ SIRSp.R := by decide
  simp only [sirProj, maSIR, rempalaRxns, sirRxns, Rxn.rempala, List.flatMap_cons,
    List.flatMap_nil, List.cons_append, List.nil_append, List.append_nil, maLift, maField,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst_add, Prod.snd_add,
    Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.single_eq_same, Pi.single_eq_of_ne hIR,
    Prod.fst_zero, Prod.snd_zero, Pi.zero_apply]
  refine Prod.ext ?_ ?_
  · simp only
    ring
  · simp only
    ring

/-- `E_μ` of SIR, projected to `(S, x_I)`, is mass-action SIR with `β = μτ` and `ρ = γ + τ`. -/
theorem rempala_sir_proj (μ τ γ : ℝ) :
    IsSemiconj (maSys (rempalaRxns μ (sirRxns τ γ))) (maSIR (μ * τ) (γ + τ)) sirProj := by
  refine isSemiconj_of_hasFDerivAt (A := maSys (rempalaRxns μ (sirRxns τ γ)))
    (B := maSIR (μ * τ) (γ + τ)) (fun _ => sirProjL) (fun _ => sirProjL.hasFDerivAt)
    fun v => ?_
  obtain ⟨S, x⟩ := v
  have hIR : (SIRSp.I : SIRSp) ≠ SIRSp.R := by decide
  change sirProj (maLift (rempalaRxns μ (sirRxns τ γ)) (S, x)) = _
  simp only [sirProj, maSIR, rempalaRxns, sirRxns, Rxn.rempala, List.flatMap_cons,
    List.flatMap_nil, List.cons_append, List.nil_append, List.append_nil, maLift, maField,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst_add, Prod.snd_add,
    Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.single_eq_same, Pi.single_eq_of_ne hIR,
    Prod.fst_zero, Prod.snd_zero, Pi.zero_apply]
  refine Prod.ext ?_ ?_
  · simp only
    ring
  · simp only
    ring

/-- **Rempała's theorem for SIR from the general quotient, without `ξ = 1` (M3, SIR).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M3): "EB_{Pois μ}(P) → MA(E_μ P) [...] π =
(θ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ). For SIR: MA(β = μτ, γ_MA = γ + τ). **The MA "I" is φ_I, not
prevalence**".

Lean statement: for all real `μ ≠ 0`, `τ`, `γ`, `q`, the map
`(θ, ξ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ_I)` is a global semiconjugacy from the general per-reaction EB
model of SIR (`s + I → I + I` at per-contact rate τ, `I → R` at rate γ) on the Poisson(μ)
configuration network with seed factor `q` to mass-action SIR `Ṡ = −βSI`, `İ = βSI − ρI` with
`β = μτ` and `ρ = γ + τ`. It is the composite of `rempala_general` for SIR with the projection
`(S, x) ↦ (S, x_I)` (`rempala_sir_proj`). Unlike `NEP.rempala_lift`, it holds at every state,
not only on `ξ = 1`. -/
theorem rempala_general_sir (μ τ γ q : ℝ) (hμ : μ ≠ 0) :
    IsSemiconj (ebSys (CNet.poisson μ) q (sirRxns τ γ)) (maSIR (μ * τ) (γ + τ))
      (sirProj ∘ rempalaMap μ q) :=
  ((Semiconj.ofIsSemiconj _ (rempala_general μ q hμ (sirRxns τ γ))).comp
    (Semiconj.ofIsSemiconj _ (rempala_sir_proj μ τ γ))).isSemiconj

/-- **Rempała's quotient from the general SIR lift, with the design's map
`(qξe^{μ(θ−1)}, φ_I)`, for `μ ≠ 0` (M3, SIR case).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M3): "EB_{Pois μ}(P) → MA(E_μ P), E_μ P =
c_μ P + {J_r → ∅ at τ_r} on the edge copies; π = (θ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ). For SIR:
MA(β = μτ, γ_MA = γ + τ). **The MA "I" is φ_I, not prevalence**".

Lean statement: for all real `μ ≠ 0`, `τ`, `γ`, `q`, the map
`(θ, ξ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ_I)` is a global semiconjugacy (at every state, any ξ) from the
general per-reaction EB model of SIR (`s + I → I + I` at per-contact rate τ, `I → R` at γ) on the
Poisson(μ) network with seed factor `q` to mass-action SIR with `β = μτ`, `ρ = γ + τ`. On the slice
`ξ = 1` the map is `(q e^{μ(θ−1)}, φ_I)` (`NEP.rempala_lift`). -/
theorem rempala_lift_xi (μ τ γ q : ℝ) (hμ : μ ≠ 0) :
    IsSemiconj (ebSys (CNet.poisson μ) q (sirRxns τ γ)) (maSIR (μ * τ) (γ + τ))
      (fun u => (q * u.2.1 * Real.exp (μ * (u.1 - 1)), u.2.2.1 .I)) :=
  rempala_general_sir μ τ γ q hμ

/-- **Rempała's theorem on trajectories with the design's map `(qξe^{μ(θ−1)}, φ_I)`, for
`μ ≠ 0` (M3, SIR).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M3): "EB_{Pois μ}(P) → MA(E_μ P) [...] π = (θ,
φ, pop) ↦ (qξe^{μ(θ−1)}, φ). For SIR: MA(β = μτ, γ_MA = γ + τ). **The MA "I" is φ_I, not
prevalence**"; §D.3: "semiconjugacies map solution curves to solution curves".

Lean statement: let `μ ≠ 0`, `τ`, `γ`, `q` be real and `I` any set of times. If
`x : ℝ → EB SIRSp` solves the general per-reaction EB model of SIR on the Poisson(μ) network with
seed factor `q` within `I` at every `t ∈ I`, then
`t ↦ (qξ(t)e^{μ(θ(t)−1)}, φ_I(t))` solves mass-action SIR `Ṡ = −μτSI`, `İ = μτSI − (γ + τ)I`
within `I` at every `t ∈ I`; and the same holds for two-sided derivatives at every `t ∈ I`. No
condition on `ξ(0)` is needed. -/
theorem rempala_solution_xi (μ τ γ q : ℝ) (hμ : μ ≠ 0) {I : Set ℝ} {x : ℝ → EB SIRSp} :
    ((∀ t ∈ I, HasDerivWithinAt x (lift (CNet.poisson μ) q (sirRxns τ γ) (x t)) I t) →
      ∀ t ∈ I, HasDerivWithinAt
        (fun t => (q * (x t).2.1 * Real.exp (μ * ((x t).1 - 1)), (x t).2.2.1 .I))
        ((maSIR (μ * τ) (γ + τ)).F
          (q * (x t).2.1 * Real.exp (μ * ((x t).1 - 1)), (x t).2.2.1 .I)) I t) ∧
    ((∀ t ∈ I, HasDerivAt x (lift (CNet.poisson μ) q (sirRxns τ γ) (x t)) t) →
      ∀ t ∈ I, HasDerivAt
        (fun t => (q * (x t).2.1 * Real.exp (μ * ((x t).1 - 1)), (x t).2.2.1 .I))
        ((maSIR (μ * τ) (γ + τ)).F
          (q * (x t).2.1 * Real.exp (μ * ((x t).1 - 1)), (x t).2.2.1 .I)) t) :=
  ⟨fun hx => (Semiconj.ofIsSemiconj _ (rempala_lift_xi μ τ γ q hμ)).map_solution_within
      (A := ebSys (CNet.poisson μ) q (sirRxns τ γ)) hx,
    fun hx => (Semiconj.ofIsSemiconj _ (rempala_lift_xi μ τ γ q hμ)).map_solution
      (A := ebSys (CNet.poisson μ) q (sirRxns τ γ)) hx⟩

/-- **Rempała's theorem on trajectories, whatever `ξ(0)` is (M3, SIR).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M3): "EB_{Pois μ}(P) → MA(E_μ P) [...] π = (θ,
φ, pop) ↦ (qξe^{μ(θ−1)}, φ). For SIR: MA(β = μτ, γ_MA = γ + τ). **The MA "I" is φ_I, not
prevalence**"; §D.3: "semiconjugacies map solution curves to solution curves".

Lean statement: the within-`I` part of `rempala_solution_xi`, stated separately for solutions
with `ξ(0) = 1` and with `ξ(0) ≠ 1`: for all real `μ ≠ 0`, `τ`, `γ`, `q`, every set of times `I`
and every `x : ℝ → EB SIRSp` with `ξ(0) = 1` (first conjunct) or `ξ(0) ≠ 1` (second conjunct) that
solves the general per-reaction EB model of SIR on the Poisson(μ) network with seed factor `q`
within `I` at every `t ∈ I`, the curve `t ↦ (qξ(t)e^{μ(θ(t)−1)}, φ_I(t))` solves mass-action SIR
`Ṡ = −μτSI`, `İ = μτSI − (γ + τ)I` within `I` at every `t ∈ I`. -/
theorem rempala_solution_any_xi0 :
    (∀ μ τ γ q : ℝ, μ ≠ 0 → ∀ I : Set ℝ, ∀ x : ℝ → EB SIRSp, (x 0).2.1 = 1 →
      (∀ t ∈ I, HasDerivWithinAt x ((ebSys (CNet.poisson μ) q (sirRxns τ γ)).F (x t)) I t) →
        ∀ t ∈ I, HasDerivWithinAt
          (fun s => (q * (x s).2.1 * Real.exp (μ * ((x s).1 - 1)), (x s).2.2.1 .I))
          ((maSIR (μ * τ) (γ + τ)).F
            (q * (x t).2.1 * Real.exp (μ * ((x t).1 - 1)), (x t).2.2.1 .I)) I t) ∧
    (∀ μ τ γ q : ℝ, μ ≠ 0 → ∀ I : Set ℝ, ∀ x : ℝ → EB SIRSp, (x 0).2.1 ≠ 1 →
      (∀ t ∈ I, HasDerivWithinAt x ((ebSys (CNet.poisson μ) q (sirRxns τ γ)).F (x t)) I t) →
        ∀ t ∈ I, HasDerivWithinAt
          (fun s => (q * (x s).2.1 * Real.exp (μ * ((x s).1 - 1)), (x s).2.2.1 .I))
          ((maSIR (μ * τ) (γ + τ)).F
            (q * (x t).2.1 * Real.exp (μ * ((x t).1 - 1)), (x t).2.2.1 .I)) I t) :=
  ⟨fun μ τ γ q hμ _ _ _ hx => (rempala_solution_xi μ τ γ q hμ).1 hx,
    fun μ τ γ q hμ _ _ _ hx => (rempala_solution_xi μ τ γ q hμ).1 hx⟩

/-- **Rempała's quotient for SEIR: the mass-action equations of `E_μ(SEIR)` (M3, SEIR).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M3): "EB_{Pois μ}(P) → MA(E_μ P), E_μ P = c_μ P
+ {J_r → ∅ at τ_r} on the edge copies; π = (θ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ)".

Lean statement: for all real `μ, τ, a, γ` and every mass-action state `(S, x)` over the SEIR node
species, the mass-action field of `E_μ(SEIR)` (SEIR: `s + I → E + I` at per-contact rate τ,
`E → I` at `a`, `I → R` at γ) is `Ṡ = −μτSx_I`, `ẋ_E = μτSx_I − a x_E`,
`ẋ_I = a x_E − (γ + τ)x_I`, `ẋ_R = γx_I`. With `rempala_general`, EB SEIR on Poisson(μ) maps to
this system by `(θ, ξ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ)`: mass-action SEIR with `β = μτ` and removal
rate `γ + τ` from I, whose E and I are the edge probabilities `φ_E`, `φ_I`. -/
theorem rempala_seir_field (μ τ a γ : ℝ) (S : ℝ) (x : SEIRSp → ℝ) :
    let F := maLift (rempalaRxns μ (seirRxns τ a γ)) (S, x)
    F.1 = -(μ * τ * S * x .I) ∧
    F.2 .E = μ * τ * S * x .I - a * x .E ∧
    F.2 .I = a * x .E - (γ + τ) * x .I ∧
    F.2 .R = γ * x .I := by
  have hEI : (SEIRSp.E : SEIRSp) ≠ SEIRSp.I := by decide
  have hIE : (SEIRSp.I : SEIRSp) ≠ SEIRSp.E := by decide
  have hER : (SEIRSp.E : SEIRSp) ≠ SEIRSp.R := by decide
  have hRE : (SEIRSp.R : SEIRSp) ≠ SEIRSp.E := by decide
  have hIR : (SEIRSp.I : SEIRSp) ≠ SEIRSp.R := by decide
  have hRI : (SEIRSp.R : SEIRSp) ≠ SEIRSp.I := by decide
  simp only [rempalaRxns, seirRxns, Rxn.rempala, List.flatMap_cons, List.flatMap_nil,
    List.cons_append, List.nil_append, List.append_nil, maLift, maField, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Prod.fst_add, Prod.snd_add, Pi.add_apply,
    Pi.sub_apply, Pi.neg_apply, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne hEI, Pi.single_eq_of_ne hIE, Pi.single_eq_of_ne hER,
    Pi.single_eq_of_ne hRE, Pi.single_eq_of_ne hIR, Pi.single_eq_of_ne hRI]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- **Rempała's quotient for SEIR: the mass-action equations of `E_μ(SEIR)`, as written (M3,
SEIR).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M3): "EB_{Pois μ}(P) → MA(E_μ P), E_μ P = c_μ P
+ {J_r → ∅ at τ_r} on the edge copies; π = (θ, φ, pop) ↦ (qξe^{μ(θ−1)}, φ)".

Lean statement: as `rempala_seir_field`, for every mass-action state `v = (S, x)` over the SEIR
node species, with the first equation in the product form `Ṡ = −(μτ) S x_I`:
`Ṡ = −(μτ)·S·x_I`, `ẋ_E = μτSx_I − a x_E`, `ẋ_I = a x_E − (γ + τ)x_I`, `ẋ_R = γx_I`. -/
theorem rempala_seir_field_eqns (μ τ a γ : ℝ) (v : MA SEIRSp) :
    (maLift (rempalaRxns μ (seirRxns τ a γ)) v).1 = -(μ * τ) * v.1 * v.2 .I ∧
    (maLift (rempalaRxns μ (seirRxns τ a γ)) v).2 .E = μ * τ * v.1 * v.2 .I - a * v.2 .E ∧
    (maLift (rempalaRxns μ (seirRxns τ a γ)) v).2 .I = a * v.2 .E - (γ + τ) * v.2 .I ∧
    (maLift (rempalaRxns μ (seirRxns τ a γ)) v).2 .R = γ * v.2 .I := by
  obtain ⟨h1, h2, h3, h4⟩ := rempala_seir_field μ τ a γ v.1 v.2
  exact ⟨by rw [h1]; ring, h2, h3, h4⟩

end Natural

end NEP
