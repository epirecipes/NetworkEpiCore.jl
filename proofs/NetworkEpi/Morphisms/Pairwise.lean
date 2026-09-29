import NetworkEpi.Morphisms.Common
import NetworkEpi.Semantics.PWS
import NetworkEpi.Closure.PT

/-!
# L4e: EB → S-anchored pairwise with the PGF closure, for every ψ and every T_EB model (M6)

DESIGN_NetworkEpiCore.md §D.5, row **M6**: "**EB → S-anchored pairwise** | π^PW(θ, ξ, φ, pop) =
(θ, [s] = qξψ(θ), [sX] = qξψ'(θ)φ_X, [ss] = q²ξ²ψ'(θ)²/ψ'(1), [X] = pop_X) onto PW^S with closure
[Z s J] = K_ψ(θ)[Zs][sJ]/[s], K_ψ = ψψ''/ψ'². It holds **for every C² ψ and every T_EB model**, on
U = {ψ ≠ 0, ψ' ≠ 0} (the DSA closure, Kiss, Kenah & Rempała 2023) | natural semiconjugacy";
§A.4: "`PGFClosure()`: the S-anchored subsystem with closure K_ψ(θ) = ψ(θ)ψ''(θ)/ψ'(θ)² and an
auxiliary θ, where θ̇ = −Σ_r τ_r [s J_r]/(qξψ'(θ)). It is exact against EB for every ψ (M6)".

## The target system `pgfSys N rs`

The state is `(θ, w)` with `w = ([s], [ss], [sZ], [Z]) : PWS σ`. The PW^S part is the per-reaction
field `pwSField K` of `NetworkEpi.Semantics.PWS` (checked there against the design's
`check_pwS_general.py` and `check_exit_pws.py`), evaluated at the degree-dependent closure
`K = K_ψ(θ) = ψ(θ)ψ''(θ)/ψ'(θ)²`. The auxiliary θ evolves by
`θ̇ = −(ψ(θ)/ψ'(θ)) Σ_contacts τ_r [s J_r]/[s]`. On the image of π^PW, `[s] = qξψ(θ)`, so this is
the design's `θ̇ = −Σ_r τ_r [s J_r]/(qξψ'(θ))` written in the coordinates of the target (ξ is not
a coordinate of PW^S, so the target must not refer to it).

## Results

* `eb_to_pws`: for every T_EB reaction list (contacts, exits, progressions, removals), every
  configuration network and every set Θ of θ values at which ψ' and ψ'' are the derivatives of ψ
  and ψ', π^PW is a local semiconjugacy from EB to `pgfSys` on
  `U = {θ ∈ Θ, ψ(θ) ≠ 0, ψ'(θ) ≠ 0, ξ ≠ 0}` (for `q ≠ 0`).
* `eb_to_pws_solution`: EB solutions that stay in `U` map to PGF-closure solutions.
* `eb_to_pws_sir`, `eb_to_pws_seir`: the SIR and SEIR instances.
* `eb_to_pws_const`: if `K_ψ ≡ κ` on Θ, the PW^S part alone, with the **constant** closure κ, is
  the image of EB: the constant-closure pairwise model is exact. `eb_to_pws_pt`: the same for a
  Poisson-type ψ (`ψ' = αψ^κ` on an interval, `NetworkEpi.Closure.PT`).

**Not** the free-scalar identity: the legacy "pointwise pairwise identity" (§D.7 "Never cited")
is a statement about free scalars; here the derivatives of ψ enter only through the `HasDerivAt`
hypotheses, and the statement is a semiconjugacy of vector fields.
-/

open scoped BigOperators

namespace NEP

variable {σ : Type}

/-- S-anchored pairwise coordinates with the auxiliary θ: `(θ, ([s], [ss], [sZ], [Z]))`. -/
abbrev PWSθ (σ : Type) := ℝ × PWS σ

section Field
variable [DecidableEq σ]

/-- The θ-component of the PGF-closure field of one reaction:
`−(ψ(θ)/ψ'(θ)) τ [sJ]/[s]` for a contact `s + J → X + J` at τ, and 0 otherwise. -/
noncomputable def pgfThetaField (N : CNet) : Rxn σ → PWSθ σ → ℝ
  | .contact J _ τ, z => -(N.ψ z.1 / N.ψ' z.1) * (τ * z.2.2.2.1 J / z.2.1)
  | _, _ => 0

/-- The PGF-closure field of one reaction: the auxiliary θ-component and the S-anchored pairwise
field `pwSField` at the closure `K_ψ(θ)`. -/
noncomputable def pgfField (N : CNet) (r : Rxn σ) (z : PWSθ σ) : PWSθ σ :=
  (pgfThetaField N r z, pwSField (N.closureK z.1) r z.2)

/-- The PGF-closure vector field of a reaction list. -/
noncomputable def pgfLift (N : CNet) (rs : List (Rxn σ)) (z : PWSθ σ) : PWSθ σ :=
  (rs.map fun r => pgfField N r z).sum

/-- The S-anchored pairwise model with the PGF closure (NBM's `PGFClosure`) as an object of
`DynSys`. -/
noncomputable def pgfSys [Fintype σ] (N : CNet) (rs : List (Rxn σ)) : DynSys where
  V := PWSθ σ
  F := pgfLift N rs

end Field

/-- **The pairwise image π^PW** (DESIGN §D.5 M6): `(θ, ξ, φ, pop) ↦ (θ, [s], [ss], [sX], [X]) =
(θ, qξψ(θ), q²ξ²ψ'(θ)²/ψ'(1), qξψ'(θ)φ_X, pop_X)`. -/
noncomputable def pwImage (N : CNet) (q : ℝ) (u : EB σ) : PWSθ σ :=
  (u.1, (q * u.2.1 * N.ψ u.1, q ^ 2 * u.2.1 ^ 2 * N.ψ' u.1 ^ 2 / N.ψ' 1,
    fun X => q * u.2.1 * N.ψ' u.1 * u.2.2.1 X, u.2.2.2))

/-- The components `[sZ]` of the derivative of π^PW at `u`. -/
noncomputable def pwDsZ (N : CNet) (q : ℝ) (u : EB σ) : EB σ →L[ℝ] (σ → ℝ) :=
  ContinuousLinearMap.pi fun Z =>
    (q * N.ψ' u.1 * u.2.2.1 Z) • ebXi + (q * u.2.1 * N.ψ'' u.1 * u.2.2.1 Z) • ebTheta +
      (q * u.2.1 * N.ψ' u.1) • ((ContinuousLinearMap.proj Z).comp ebPhi)

/-- The derivative of π^PW at `u`. -/
noncomputable def pwD (N : CNet) (q : ℝ) (u : EB σ) : EB σ →L[ℝ] PWSθ σ :=
  ebTheta.prod ((suscD N q u).prod
    (((q ^ 2 * (2 * u.2.1 * N.ψ' u.1 ^ 2) / N.ψ' 1) • ebXi +
        (q ^ 2 * (2 * u.2.1 ^ 2 * N.ψ' u.1 * N.ψ'' u.1) / N.ψ' 1) • ebTheta).prod
      ((pwDsZ N q u).prod ebPop)))

/-- `pwD N q u` applied to a direction `v`, componentwise. -/
lemma pwD_apply (N : CNet) (q : ℝ) (u v : EB σ) :
    pwD N q u v = (v.1, (q * (v.2.1 * N.ψ u.1 + u.2.1 * (N.ψ' u.1 * v.1)),
      q ^ 2 * (2 * u.2.1 * N.ψ' u.1 ^ 2) / N.ψ' 1 * v.2.1 +
        q ^ 2 * (2 * u.2.1 ^ 2 * N.ψ' u.1 * N.ψ'' u.1) / N.ψ' 1 * v.1,
      fun Z => q * N.ψ' u.1 * u.2.2.1 Z * v.2.1 + q * u.2.1 * N.ψ'' u.1 * u.2.2.1 Z * v.1 +
        q * u.2.1 * N.ψ' u.1 * v.2.2.1 Z,
      v.2.2.2)) := by
  simp only [pwD, pwDsZ, ContinuousLinearMap.prod_apply, suscD_apply, ebTheta_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ebXi_apply, smul_eq_mul,
    ContinuousLinearMap.coe_pi', ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    ebPhi_apply, ebPop_apply]

/-- π^PW has derivative `pwD N q u` at every state whose θ is a point where ψ' and ψ'' are the
derivatives of ψ and ψ'. -/
lemma hasFDerivAt_pwImage [Fintype σ] (N : CNet) (q : ℝ) {u : EB σ}
    (hψ : HasDerivAt N.ψ (N.ψ' u.1) u.1) (hψ' : HasDerivAt N.ψ' (N.ψ'' u.1) u.1) :
    HasFDerivAt (pwImage N q) (pwD N q u) u := by
  have hθ := hasFDerivAt_ebTheta (σ := σ) u
  have hξ := hasFDerivAt_ebXi (σ := σ) u
  have h1 : HasFDerivAt (fun u : EB σ => N.ψ' u.1) (N.ψ'' u.1 • (ebTheta (σ := σ))) u :=
    hψ'.comp_hasFDerivAt u hθ
  have hg := hξ.mul h1
  have hss : HasFDerivAt (fun u : EB σ => q ^ 2 * u.2.1 ^ 2 * N.ψ' u.1 ^ 2 / N.ψ' 1)
      (((q ^ 2 * (2 * u.2.1 * N.ψ' u.1 ^ 2) / N.ψ' 1) • ebXi +
        (q ^ 2 * (2 * u.2.1 ^ 2 * N.ψ' u.1 * N.ψ'' u.1) / N.ψ' 1) • ebTheta)) u := by
    have e : (fun u : EB σ => q ^ 2 * u.2.1 ^ 2 * N.ψ' u.1 ^ 2 / N.ψ' 1) =
        fun u => q ^ 2 / N.ψ' 1 * ((u.2.1 * N.ψ' u.1) * (u.2.1 * N.ψ' u.1)) := by
      funext u
      ring
    rw [e]
    refine ((hg.mul hg).const_mul (q ^ 2 / N.ψ' 1)).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, smul_eq_mul,
      ebXi_apply, ebTheta_apply, Pi.mul_apply]
    ring
  have hsZ : HasFDerivAt (fun u : EB σ => fun X => q * u.2.1 * N.ψ' u.1 * u.2.2.1 X)
      (pwDsZ N q u) u := by
    refine hasFDerivAt_pi'.2 fun Z => ?_
    have hφ : HasFDerivAt (fun u : EB σ => u.2.2.1 Z)
        ((ContinuousLinearMap.proj Z).comp (ebPhi (σ := σ))) u :=
      ((ContinuousLinearMap.proj Z).comp ebPhi).hasFDerivAt
    refine (((hξ.const_mul q).mul h1).mul hφ).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [pwDsZ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.pi_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.add_apply, smul_eq_mul, ebXi_apply, ebTheta_apply, ebPhi_apply,
      Pi.mul_apply]
    ring
  exact hθ.prodMk ((hasFDerivAt_susc N q hψ).prodMk (hss.prodMk (hsZ.prodMk
    (hasFDerivAt_ebPop u))))

/-- The domain of M6: states whose θ lies in `Θ` and satisfies `ψ(θ) ≠ 0`, `ψ'(θ) ≠ 0`, and whose
`ξ ≠ 0`. -/
def pwsDomain (N : CNet) (Θ : Set ℝ) : Set (EB σ) :=
  {u | u.1 ∈ Θ ∧ N.ψ u.1 ≠ 0 ∧ N.ψ' u.1 ≠ 0 ∧ u.2.1 ≠ 0}

section Semiconj
variable [DecidableEq σ]

/-- **Per-reaction identity behind M6.** At a state with `ψ(θ) ≠ 0`, `ψ'(θ) ≠ 0` and `qξ ≠ 0`,
the derivative of π^PW carries the EB field of each T_EB reaction `r` to the PGF-closure field of
`r` at the image point. -/
theorem pws_ebField (N : CNet) (q : ℝ) (r : Rxn σ) (u : EB σ) (h0 : N.ψ u.1 ≠ 0)
    (h1 : N.ψ' u.1 ≠ 0) (hq : q ≠ 0) (hξ : u.2.1 ≠ 0) :
    pwD N q u (ebField N q r u) = pgfField N r (pwImage N q u) := by
  obtain ⟨θ, ξ, φ, p⟩ := u
  simp only at h0 h1 hξ
  rw [pwD_apply]
  cases r with
  | contact J X τ =>
      simp only [ebField, pgfField, pgfThetaField, pwSField, pwImage, CNet.closureK]
      refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
      · simp only
        field_simp
      · simp only
        ring
      · simp only
        field_simp
        ring
      · funext Z
        simp only [Pi.sub_apply, Pi.single_apply]
        split_ifs <;> field_simp <;> ring
      · funext Z
        simp only [Pi.single_apply]
        split_ifs <;> ring
  | exit Y ν =>
      simp only [ebField, pgfField, pgfThetaField, pwSField, pwImage, CNet.phiS, CNet.susc]
      refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
      · rfl
      · simp only
        ring
      · simp only
        field_simp
        ring
      · funext Z
        simp only [Pi.sub_apply, Pi.single_apply]
        split_ifs <;> field_simp <;> ring
      · rfl
  | trans X Y a =>
      cases Y with
      | none =>
          simp only [ebField, pgfField, pgfThetaField, pwSField, pwImage]
          refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
          · rfl
          · simp only
            ring
          · simp only
            ring
          · funext Z
            simp only [Pi.neg_apply, Pi.single_apply]
            split_ifs <;> ring
          · rfl
      | some Y =>
          simp only [ebField, pgfField, pgfThetaField, pwSField, pwImage]
          refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
          · rfl
          · simp only
            ring
          · simp only
            ring
          · funext Z
            simp only [Pi.sub_apply, Pi.single_apply]
            split_ifs <;> ring
          · rfl

variable [Fintype σ]

/-- **EB → S-anchored pairwise with the PGF closure, for every ψ and every T_EB model (M6).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M6): "**EB → S-anchored pairwise** |
π^PW(θ, ξ, φ, pop) = (θ, [s] = qξψ(θ), [sX] = qξψ'(θ)φ_X, [ss] = q²ξ²ψ'(θ)²/ψ'(1), [X] = pop_X)
onto PW^S with closure [Z s J] = K_ψ(θ)[Zs][sJ]/[s], K_ψ = ψψ''/ψ'². It holds **for every C² ψ and
every T_EB model**, on U = {ψ ≠ 0, ψ' ≠ 0} (the DSA closure, Kiss, Kenah & Rempała 2023) |
natural semiconjugacy"; §A.4: "`PGFClosure()`: the S-anchored subsystem with closure
K_ψ(θ) = ψ(θ)ψ''(θ)/ψ'(θ)² and an auxiliary θ, where θ̇ = −Σ_r τ_r [s J_r]/(qξψ'(θ)). It is exact
against EB for every ψ (M6)".

Lean statement: let `σ` be a finite type of node species, `rs` any T_EB reaction list over `σ`
(contacts, exits, progressions and removals), `N` a configuration network (functions ψ, ψ', ψ''),
`q ≠ 0`, and `Θ ⊆ ℝ` a set of θ values at which ψ' is the derivative of ψ and ψ'' the derivative
of ψ'. Then π^PW `(θ, ξ, φ, pop) ↦ (θ, [s], [ss], [sX], [X]) = (θ, qξψ(θ), q²ξ²ψ'(θ)²/ψ'(1),
qξψ'(θ)φ_X, pop_X)` is a local semiconjugacy, on `U = {θ ∈ Θ, ψ(θ) ≠ 0, ψ'(θ) ≠ 0, ξ ≠ 0}`, from
the per-reaction EB model of `rs` on `N` with seed factor `q` to the S-anchored pairwise model with
the PGF closure (`pgfSys N rs`): per contact `s + J → X + J` at τ, `[s]' −= τ[sJ]`,
`[ss]' −= 2τ[ssJ]`, `[sZ]' −= τ[ZsJ]` for every Z, `[sJ]' −= τ[sJ]`, `[sX]' += τ[ssJ]`,
`[X]' += τ[sJ]`; per exit `s → Y` at ν, `[s]' −= ν[s]`, `[ss]' −= 2ν[ss]`, `[sZ]' −= ν[sZ]` for
every Z, `[sY]' += ν[ss]`, `[Y]' += ν[s]`; per transition `X → Y | ∅` at a, `[sX]' −= a[sX]`,
`[sY]' += a[sX]`, `[X]' −= a[X]`, `[Y]' += a[X]`; triples closed as
`[A s B] = K_ψ(θ)[As][sB]/[s]` with `K_ψ = ψψ''/ψ'²`; and the auxiliary
`θ̇ = −(ψ(θ)/ψ'(θ)) Σ_contacts τ[sJ]/[s]`.

Scope: ψ need not be C² on all of ℝ: only the two derivative relations on Θ are used (for a C²
PGF take Θ = ℝ; for a negative binomial PGF, the θ below the pole). `ξ ≠ 0` and `q ≠ 0` make
`[s] ≠ 0` on U, which the target's division by `[s]` needs (the design's U leaves this implicit:
physical states have ξ > 0 and q > 0). No condition on ψ'(1) is needed. -/
theorem eb_to_pws (N : CNet) (q : ℝ) (hq : q ≠ 0) (Θ : Set ℝ)
    (hψ : ∀ θ ∈ Θ, HasDerivAt N.ψ (N.ψ' θ) θ) (hψ' : ∀ θ ∈ Θ, HasDerivAt N.ψ' (N.ψ'' θ) θ)
    (rs : List (Rxn σ)) :
    IsSemiconjOn (ebSys N q rs) (pgfSys N rs) (pwsDomain N Θ) (pwImage N q) := by
  refine isSemiconjOn_of_hasFDerivAt (A := ebSys N q rs) (B := pgfSys N rs) (pwD N q)
    (fun u hu => hasFDerivAt_pwImage N q (hψ u.1 hu.1) (hψ' u.1 hu.1)) fun u hu => ?_
  change pwD N q u (lift N q rs u) = pgfLift N rs (pwImage N q u)
  rw [lift, pgfLift]
  exact clm_list_sum_eq _ rs _ _ fun r _ => pws_ebField N q r u hu.2.1 hu.2.2.1 hq hu.2.2.2

/-- **EB → PW^S on trajectories (M6).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M6): "π^PW(θ, ξ, φ, pop) = (θ, [s] = qξψ(θ),
[sX] = qξψ'(θ)φ_X, [ss] = q²ξ²ψ'(θ)²/ψ'(1), [X] = pop_X) onto PW^S with closure
[Z s J] = K_ψ(θ)[Zs][sJ]/[s], K_ψ = ψψ''/ψ'². It holds **for every C² ψ and every T_EB model**,
on U = {ψ ≠ 0, ψ' ≠ 0}"; §D.3: "solutions that stay in U are mapped".

Lean statement: under the hypotheses of `eb_to_pws` (finite σ, any T_EB list `rs`, `q ≠ 0`, the
derivative relations of ψ, ψ', ψ'' on Θ), let `I` be any set of times and `x : ℝ → EB σ` a solution
of the EB model of `rs` within `I` at every `t ∈ I` that stays in
`U = {θ ∈ Θ, ψ(θ) ≠ 0, ψ'(θ) ≠ 0, ξ ≠ 0}`. Then `t ↦ π^PW(x(t))` solves the PGF-closure S-anchored
pairwise model within `I` at every `t ∈ I`. -/
theorem eb_to_pws_solution (N : CNet) (q : ℝ) (hq : q ≠ 0) (Θ : Set ℝ)
    (hψ : ∀ θ ∈ Θ, HasDerivAt N.ψ (N.ψ' θ) θ) (hψ' : ∀ θ ∈ Θ, HasDerivAt N.ψ' (N.ψ'' θ) θ)
    (rs : List (Rxn σ)) {I : Set ℝ} {x : ℝ → EB σ}
    (hx : ∀ t ∈ I, HasDerivWithinAt x (lift N q rs (x t)) I t)
    (hU : ∀ t ∈ I, x t ∈ pwsDomain N Θ) :
    ∀ t ∈ I, HasDerivWithinAt (fun t => pwImage N q (x t))
      (pgfLift N rs (pwImage N q (x t))) I t :=
  (SemiconjOn.ofIsSemiconjOn _ (eb_to_pws N q hq Θ hψ hψ' rs)).map_solution_within
    (A := ebSys N q rs) hx hU

/-- **EB → PW^S for SIR (M6, SIR instance).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M6): "It holds **for every C² ψ and every T_EB
model**, on U = {ψ ≠ 0, ψ' ≠ 0}"; §D.7, L4e: "SIR and SEIR with generic C² ψ via `HasDerivAt`
hypotheses".

Lean statement: `eb_to_pws` for SIR (`s + I → I + I` at per-contact rate τ, `I → R` at γ): for
every configuration network `N`, `q ≠ 0` and every set Θ on which ψ' and ψ'' are the derivatives of
ψ and ψ', π^PW is a local semiconjugacy on `{θ ∈ Θ, ψ(θ) ≠ 0, ψ'(θ) ≠ 0, ξ ≠ 0}` from EB SIR on `N`
to the PGF-closure S-anchored pairwise SIR model. -/
theorem eb_to_pws_sir (N : CNet) (q τ γ : ℝ) (hq : q ≠ 0) (Θ : Set ℝ)
    (hψ : ∀ θ ∈ Θ, HasDerivAt N.ψ (N.ψ' θ) θ) (hψ' : ∀ θ ∈ Θ, HasDerivAt N.ψ' (N.ψ'' θ) θ) :
    IsSemiconjOn (ebSys N q (sirRxns τ γ)) (pgfSys N (sirRxns τ γ)) (pwsDomain N Θ)
      (pwImage N q) :=
  eb_to_pws N q hq Θ hψ hψ' _

/-- **EB → PW^S for SEIR (M6, SEIR instance).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M6): "It holds **for every C² ψ and every T_EB
model**, on U = {ψ ≠ 0, ψ' ≠ 0}"; §D.7, L4e: "SIR and SEIR with generic C² ψ via `HasDerivAt`
hypotheses".

Lean statement: `eb_to_pws` for SEIR (`s + I → E + I` at per-contact rate τ, `E → I` at `a`,
`I → R` at γ): for every configuration network `N`, `q ≠ 0` and every set Θ on which ψ' and ψ''
are the derivatives of ψ and ψ', π^PW is a local semiconjugacy on
`{θ ∈ Θ, ψ(θ) ≠ 0, ψ'(θ) ≠ 0, ξ ≠ 0}` from EB SEIR on `N` to the PGF-closure S-anchored pairwise
SEIR model. -/
theorem eb_to_pws_seir (N : CNet) (q τ a γ : ℝ) (hq : q ≠ 0) (Θ : Set ℝ)
    (hψ : ∀ θ ∈ Θ, HasDerivAt N.ψ (N.ψ' θ) θ) (hψ' : ∀ θ ∈ Θ, HasDerivAt N.ψ' (N.ψ'' θ) θ) :
    IsSemiconjOn (ebSys N q (seirRxns τ a γ)) (pgfSys N (seirRxns τ a γ)) (pwsDomain N Θ)
      (pwImage N q) :=
  eb_to_pws N q hq Θ hψ hψ' _

/-! ## Constant closure -/

/-- The PW^S model with a constant closure coefficient `K` (NBM's heterogeneous constant
closure) as an object of `DynSys`. -/
noncomputable def pwSSys (K : ℝ) (rs : List (Rxn σ)) : DynSys where
  V := PWS σ
  F := pwSLift K rs

/-- **The constant-closure pairwise model is exact when K_ψ is constant (M6 with M8).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M8): "So NBM's constant closure ⟨k(k−1)⟩/⟨k⟩²
is exact **iff** the degree distribution is PT"; M6: "onto PW^S with closure
[Z s J] = K_ψ(θ)[Zs][sJ]/[s], K_ψ = ψψ''/ψ'²".

Lean statement: under the hypotheses of `eb_to_pws` (finite σ, any T_EB list `rs`, `q ≠ 0`,
derivative relations on Θ), assume moreover that `K_ψ(θ) = ψ(θ)ψ''(θ)/ψ'(θ)² = κ` for every
`θ ∈ Θ`. Then `(θ, ξ, φ, pop) ↦ ([s], [ss], [sX], [X])` (π^PW without θ) is a local
semiconjugacy on `{θ ∈ Θ, ψ(θ) ≠ 0, ψ'(θ) ≠ 0, ξ ≠ 0}` from the EB model to the S-anchored
pairwise model with the **constant** closure `[A s B] = κ[As][sB]/[s]` (`pwSSys κ rs`).

Scope: this is the "if" direction of the design's "exact iff PT", combined with
`NEP.pt_iff_const_closure` (PT ⇔ K_ψ constant). The "only if" direction for trajectories (that a
non-constant K_ψ makes the constant closure inexact along some solution) is not formalised. -/
theorem eb_to_pws_const (N : CNet) (q κ : ℝ) (hq : q ≠ 0) (Θ : Set ℝ)
    (hψ : ∀ θ ∈ Θ, HasDerivAt N.ψ (N.ψ' θ) θ) (hψ' : ∀ θ ∈ Θ, HasDerivAt N.ψ' (N.ψ'' θ) θ)
    (hK : ∀ θ ∈ Θ, N.closureK θ = κ) (rs : List (Rxn σ)) :
    IsSemiconjOn (ebSys N q rs) (pwSSys κ rs) (pwsDomain N Θ) (fun u => (pwImage N q u).2) := by
  refine isSemiconjOn_of_hasFDerivAt (A := ebSys N q rs) (B := pwSSys κ rs)
    (fun u => (ContinuousLinearMap.snd ℝ ℝ (PWS σ)).comp (pwD N q u))
    (fun u hu => (hasFDerivAt_pwImage N q (hψ u.1 hu.1) (hψ' u.1 hu.1)).snd) fun u hu => ?_
  change ((ContinuousLinearMap.snd ℝ ℝ (PWS σ)).comp (pwD N q u)) (lift N q rs u) =
    pwSLift κ rs (pwImage N q u).2
  rw [lift, pwSLift]
  refine clm_list_sum_eq _ rs _ _ fun r _ => ?_
  rw [ContinuousLinearMap.comp_apply, pws_ebField N q r u hu.2.1 hu.2.2.1 hq hu.2.2.2]
  change pwSField (N.closureK u.1) r (pwImage N q u).2 = pwSField κ r (pwImage N q u).2
  rw [hK u.1 hu.1]

/-- **For a Poisson-type degree distribution the constant closure is exact (M8 ⇒ M6).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M8): "PT ⇔ constant closure | On an interval I
with ψ > 0: K_ψ ≡ κ ⇔ ψ' = αψ^κ [...] So NBM's constant closure ⟨k(k−1)⟩/⟨k⟩² is exact **iff**
the degree distribution is PT"; §C.3: "heterogeneous pairwise with constant K =
closure_constant(d) (exact iff PT, M8)".

Lean statement: let `σ` be a finite type of node species, `rs` any T_EB reaction list, `N` a
configuration network, `q ≠ 0`, and `Θ ⊆ ℝ` convex with nonempty interior such that at every
`θ ∈ Θ`: ψ' and ψ'' are the derivatives of ψ and ψ', `ψ(θ) > 0` and `ψ'(θ) ≠ 0`. If ψ is of
Poisson type on Θ, `ψ'(θ) = αψ(θ)^κ` for all `θ ∈ Θ`, then
`(θ, ξ, φ, pop) ↦ ([s], [ss], [sX], [X]) = (qξψ(θ), q²ξ²ψ'(θ)²/ψ'(1), qξψ'(θ)φ_X, pop_X)` is a
local semiconjugacy on `pwsDomain N Θ = {θ ∈ Θ, ψ(θ) ≠ 0, ψ'(θ) ≠ 0, ξ ≠ 0}` (here simply
`{θ ∈ Θ, ξ ≠ 0}`) from the EB model of `rs` on `N` to the S-anchored pairwise model with the
constant closure `[A s B] = κ[As][sB]/[s]`.

Scope: the "if" direction of "exact iff PT"; with `pt_closure_at_one`, κ is NBM's
`ψ''(1)/ψ'(1)²` whenever `1 ∈ Θ` and `ψ(1) = 1`. -/
theorem eb_to_pws_pt (N : CNet) (q α κ : ℝ) (hq : q ≠ 0) (Θ : Set ℝ) (hΘ : Convex ℝ Θ)
    (hΘi : (interior Θ).Nonempty) (hψ : ∀ θ ∈ Θ, HasDerivAt N.ψ (N.ψ' θ) θ)
    (hψ' : ∀ θ ∈ Θ, HasDerivAt N.ψ' (N.ψ'' θ) θ) (hpos : ∀ θ ∈ Θ, 0 < N.ψ θ)
    (hne : ∀ θ ∈ Θ, N.ψ' θ ≠ 0) (hPT : ∀ θ ∈ Θ, N.ψ' θ = α * N.ψ θ ^ κ) (rs : List (Rxn σ)) :
    IsSemiconjOn (ebSys N q rs) (pwSSys κ rs) (pwsDomain N Θ) (fun u => (pwImage N q u).2) := by
  have hK := (pt_iff_closureK N hΘ hΘi hpos hne (fun θ hθ => (hψ θ hθ).hasDerivWithinAt)
    (fun θ hθ => (hψ' θ hθ).hasDerivWithinAt) κ).2 ⟨α, hPT⟩
  exact eb_to_pws_const N q κ hq Θ hψ hψ' hK rs

omit [DecidableEq σ] [Fintype σ] in
/-- The domain of M6 on a Poisson(μ) network with `μ ≠ 0` is `{ξ ≠ 0}`: ψ > 0 and ψ' ≠ 0
everywhere. -/
lemma pwsDomain_poisson (μ : ℝ) (hμ : μ ≠ 0) :
    pwsDomain (σ := σ) (CNet.poisson μ) Set.univ = {u | u.2.1 ≠ 0} := by
  ext u
  simp only [pwsDomain, CNet.poisson, Set.mem_univ, true_and, Set.mem_setOf_eq]
  have he : Real.exp (μ * (u.1 - 1)) ≠ 0 := (Real.exp_pos _).ne'
  exact ⟨fun h => h.2.2, fun h => ⟨he, mul_ne_zero hμ he, h⟩⟩

/-- **On a Poisson network the constant closure K = 1 is exact (M6, M8, Poisson instance).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M8): "So NBM's constant closure ⟨k(k−1)⟩/⟨k⟩² is
exact **iff** the degree distribution is PT"; §0: "This covers Poisson (κ = 1)".

Lean statement: for every finite type of node species, every T_EB reaction list `rs`, `μ ≠ 0` and
`q ≠ 0`, the map `(θ, ξ, φ, pop) ↦ ([s], [ss], [sX], [X]) = (qξe^{μ(θ−1)}, q²ξ²μe^{2μ(θ−1)},
qξμe^{μ(θ−1)}φ_X, pop_X)` (π^PW without θ, with `ψ'(1) = μ`) is a local semiconjugacy on
`{ξ ≠ 0}` from the EB model of `rs` on the Poisson(μ) network to the S-anchored pairwise model
with the constant closure `[A s B] = [As][sB]/[s]` (K = 1). -/
theorem eb_to_pws_poisson (μ q : ℝ) (hμ : μ ≠ 0) (hq : q ≠ 0) (rs : List (Rxn σ)) :
    IsSemiconjOn (ebSys (CNet.poisson μ) q rs) (pwSSys 1 rs) {u | u.2.1 ≠ 0}
      (fun u => (pwImage (CNet.poisson μ) q u).2) := by
  have h := eb_to_pws_const (CNet.poisson μ) q 1 hq Set.univ
    (fun θ _ => CNet.poisson_hasDerivAt_ψ μ θ) (fun θ _ => CNet.poisson_hasDerivAt_ψ' μ θ)
    (fun θ _ => (poisson_closureK μ hμ θ).2) rs
  rwa [pwsDomain_poisson μ hμ] at h

/-! ## Restatements in the form of the design text (SA-PASS remediation) -/

omit [Fintype σ] in
/-- **Per-reaction identity behind M6, with the hypothesis `qξ ≠ 0`.**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M6): "π^PW(θ, ξ, φ, pop) = (θ, [s] = qξψ(θ),
[sX] = qξψ'(θ)φ_X, [ss] = q²ξ²ψ'(θ)²/ψ'(1), [X] = pop_X) onto PW^S with closure
[Z s J] = K_ψ(θ)[Zs][sJ]/[s], K_ψ = ψψ''/ψ'²".

Lean statement: at a state `u = (θ, ξ, φ, pop)` with `ψ(θ) ≠ 0`, `ψ'(θ) ≠ 0` and `qξ ≠ 0`, the
linear map `pwD N q u` (the derivative of π^PW) carries the EB field of every T_EB reaction `r`
to the PGF-closure field of `r` at `π^PW(u)`. (As `pws_ebField`, with the single hypothesis
`qξ ≠ 0` in place of `q ≠ 0` and `ξ ≠ 0`.) -/
theorem pws_ebField_of_mul (N : CNet) (q : ℝ) (r : Rxn σ) (u : EB σ) (h0 : N.ψ u.1 ≠ 0)
    (h1 : N.ψ' u.1 ≠ 0) (hqξ : q * u.2.1 ≠ 0) :
    pwD N q u (ebField N q r u) = pgfField N r (pwImage N q u) :=
  pws_ebField N q r u h0 h1 (left_ne_zero_of_mul hqξ) (right_ne_zero_of_mul hqξ)

/-- **EB → PW^S on trajectories with two-sided derivatives (M6).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M6): "π^PW(θ, ξ, φ, pop) = (θ, [s] = qξψ(θ),
[sX] = qξψ'(θ)φ_X, [ss] = q²ξ²ψ'(θ)²/ψ'(1), [X] = pop_X) onto PW^S with closure
[Z s J] = K_ψ(θ)[Zs][sJ]/[s], K_ψ = ψψ''/ψ'². It holds **for every C² ψ and every T_EB model**,
on U = {ψ ≠ 0, ψ' ≠ 0}"; §D.3: "solutions that stay in U are mapped".

Lean statement: under the hypotheses of `eb_to_pws` (finite σ, any T_EB list `rs`, `q ≠ 0`, the
derivative relations of ψ, ψ', ψ'' on Θ), let `I` be any set of times and `x : ℝ → EB σ` a curve
with `x'(t) = lift N q rs (x(t))` (two-sided derivative) at every `t ∈ I` that stays in
`U = {θ ∈ Θ, ψ(θ) ≠ 0, ψ'(θ) ≠ 0, ξ ≠ 0}`. Then `t ↦ π^PW(x(t))` has derivative
`pgfLift N rs (π^PW(x(t)))` at every `t ∈ I`. (`eb_to_pws_solution` is the within-`I` version.) -/
theorem eb_to_pws_solution_at (N : CNet) (q : ℝ) (hq : q ≠ 0) (Θ : Set ℝ)
    (hψ : ∀ θ ∈ Θ, HasDerivAt N.ψ (N.ψ' θ) θ) (hψ' : ∀ θ ∈ Θ, HasDerivAt N.ψ' (N.ψ'' θ) θ)
    (rs : List (Rxn σ)) {I : Set ℝ} {x : ℝ → EB σ}
    (hx : ∀ t ∈ I, HasDerivAt x (lift N q rs (x t)) t)
    (hU : ∀ t ∈ I, x t ∈ pwsDomain N Θ) :
    ∀ t ∈ I, HasDerivAt (fun t => pwImage N q (x t)) (pgfLift N rs (pwImage N q (x t))) t :=
  (SemiconjOn.ofIsSemiconjOn _ (eb_to_pws N q hq Θ hψ hψ' rs)).map_solution_on
    (A := ebSys N q rs) hx hU

omit [DecidableEq σ] [Fintype σ] in
/-- The M6 domain with no restriction on θ: `pwsDomain N ℝ = {ψ(θ) ≠ 0, ψ'(θ) ≠ 0, ξ ≠ 0}`. -/
lemma pwsDomain_univ (N : CNet) :
    pwsDomain (σ := σ) N Set.univ = {u | N.ψ u.1 ≠ 0 ∧ N.ψ' u.1 ≠ 0 ∧ u.2.1 ≠ 0} := by
  ext u
  simp [pwsDomain]

/-- **EB → PW^S for every C² ψ and every T_EB model, on U = {ψ ≠ 0, ψ' ≠ 0, ξ ≠ 0} (M6).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M6): "It holds **for every C² ψ and every T_EB
model**, on U = {ψ ≠ 0, ψ' ≠ 0} (the DSA closure, Kiss, Kenah & Rempała 2023) | natural
semiconjugacy"; §L.3: "Domain U = {ψ ≠ 0, ψ' ≠ 0, ξ ≠ 0} with q ≠ 0".

Lean statement: let `σ` be a finite type of node species, `rs` any T_EB reaction list, `N` a
configuration network with `ψ'` the derivative of `ψ` and `ψ''` the derivative of `ψ'` at every
real θ, and `q ≠ 0`. Then π^PW is a local semiconjugacy on
`U = {u | ψ(θ) ≠ 0, ψ'(θ) ≠ 0, ξ ≠ 0}` from the EB model of `rs` to the PGF-closure S-anchored
pairwise model (`eb_to_pws` with Θ = ℝ). -/
theorem eb_to_pws_global (N : CNet) (q : ℝ) (hq : q ≠ 0)
    (hψ : ∀ θ, HasDerivAt N.ψ (N.ψ' θ) θ) (hψ' : ∀ θ, HasDerivAt N.ψ' (N.ψ'' θ) θ)
    (rs : List (Rxn σ)) :
    IsSemiconjOn (ebSys N q rs) (pgfSys N rs) {u | N.ψ u.1 ≠ 0 ∧ N.ψ' u.1 ≠ 0 ∧ u.2.1 ≠ 0}
      (pwImage N q) := by
  have h := eb_to_pws N q hq Set.univ (fun θ _ => hψ θ) (fun θ _ => hψ' θ) rs
  rwa [pwsDomain_univ] at h

/-- **EB → PW^S on trajectories with two-sided derivatives, for every C² ψ (M6).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M6): "π^PW(θ, ξ, φ, pop) = (θ, [s] = qξψ(θ),
[sX] = qξψ'(θ)φ_X, [ss] = q²ξ²ψ'(θ)²/ψ'(1), [X] = pop_X) onto PW^S with closure
[Z s J] = K_ψ(θ)[Zs][sJ]/[s], K_ψ = ψψ''/ψ'². It holds **for every C² ψ and every T_EB model**,
on U = {ψ ≠ 0, ψ' ≠ 0}"; §D.3: "solutions that stay in U are mapped".

Lean statement: let `σ` be a finite type of node species, `rs` any T_EB reaction list, `q ≠ 0`,
`N` a configuration network with `ψ'` the derivative of `ψ` and `ψ''` the derivative of `ψ'` at
every real θ, and `I` any set of times. If `x : ℝ → EB σ` has the two-sided derivative given by the
EB model of `rs` at every `t ∈ I` and stays in `U = {ψ(θ) ≠ 0, ψ'(θ) ≠ 0, ξ ≠ 0}`, then
`t ↦ π^PW(x(t))` has the derivative given by the PGF-closure S-anchored pairwise model at every
`t ∈ I`. (`eb_to_pws_solution_at` with Θ = ℝ.) -/
theorem eb_to_pws_solution_at_global (N : CNet) (q : ℝ) (rs : List (Rxn σ)) (I : Set ℝ)
    (x : ℝ → EB σ) (hq : q ≠ 0)
    (hC2 : ∀ θ : ℝ, HasDerivAt N.ψ (N.ψ' θ) θ ∧ HasDerivAt N.ψ' (N.ψ'' θ) θ)
    (hx : ∀ t ∈ I, HasDerivAt x ((ebSys N q rs).F (x t)) t)
    (hU : ∀ t ∈ I, x t ∈ {u : EB σ | N.ψ u.1 ≠ 0 ∧ N.ψ' u.1 ≠ 0 ∧ u.2.1 ≠ 0}) :
    ∀ t ∈ I, HasDerivAt (fun s => pwImage N q (x s)) ((pgfSys N rs).F (pwImage N q (x t))) t :=
  eb_to_pws_solution_at N q hq Set.univ (fun θ _ => (hC2 θ).1) (fun θ _ => (hC2 θ).2) rs hx
    (fun t ht => ⟨Set.mem_univ _, hU t ht⟩)

/-- **EB → PW^S on trajectories within a set of times, for every C² ψ (M6).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M6): "π^PW(θ, ξ, φ, pop) = (θ, [s] = qξψ(θ),
[sX] = qξψ'(θ)φ_X, [ss] = q²ξ²ψ'(θ)²/ψ'(1), [X] = pop_X) onto PW^S with closure
[Z s J] = K_ψ(θ)[Zs][sJ]/[s], K_ψ = ψψ''/ψ'². It holds **for every C² ψ and every T_EB model**,
on U = {ψ ≠ 0, ψ' ≠ 0}"; §D.3: "solutions that stay in U are mapped".

Lean statement: as `eb_to_pws_solution_at_global`, for solutions within `I`: if `x` solves the EB
model of `rs` within `I` at every `t ∈ I` and stays in `U = {ψ(θ) ≠ 0, ψ'(θ) ≠ 0, ξ ≠ 0}`, then
`t ↦ π^PW(x(t))` solves the PGF-closure S-anchored pairwise model within `I` at every `t ∈ I`.
(`eb_to_pws_solution` with Θ = ℝ.) -/
theorem eb_to_pws_solution_global (N : CNet) (q : ℝ) (rs : List (Rxn σ)) (I : Set ℝ)
    (x : ℝ → EB σ) (hq : q ≠ 0)
    (hC2 : ∀ θ : ℝ, HasDerivAt N.ψ (N.ψ' θ) θ ∧ HasDerivAt N.ψ' (N.ψ'' θ) θ)
    (hx : ∀ t ∈ I, HasDerivWithinAt x ((ebSys N q rs).F (x t)) I t)
    (hU : ∀ t ∈ I, x t ∈ {u : EB σ | N.ψ u.1 ≠ 0 ∧ N.ψ' u.1 ≠ 0 ∧ u.2.1 ≠ 0}) :
    ∀ t ∈ I, HasDerivWithinAt (fun s => pwImage N q (x s))
      ((pgfSys N rs).F (pwImage N q (x t))) I t :=
  eb_to_pws_solution N q hq Set.univ (fun θ _ => (hC2 θ).1) (fun θ _ => (hC2 θ).2) rs hx
    (fun t ht => ⟨Set.mem_univ _, hU t ht⟩)

/-- **EB → PW^S for SIR, for every C² ψ (M6, SIR instance).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M6): "It holds **for every C² ψ and every T_EB
model**, on U = {ψ ≠ 0, ψ' ≠ 0}"; §D.7, L4e: "SIR and SEIR with generic C² ψ via `HasDerivAt`
hypotheses".

Lean statement: for every configuration network `N` with `ψ'`, `ψ''` the derivatives of `ψ`, `ψ'`
at every real θ, all rates τ, γ and `q ≠ 0`, π^PW is a local semiconjugacy on
`{ψ(θ) ≠ 0, ψ'(θ) ≠ 0, ξ ≠ 0}` from EB SIR on `N` to the PGF-closure S-anchored pairwise SIR
model. -/
theorem eb_to_pws_sir_global (N : CNet) (q τ γ : ℝ) (hq : q ≠ 0)
    (hψ : ∀ θ, HasDerivAt N.ψ (N.ψ' θ) θ) (hψ' : ∀ θ, HasDerivAt N.ψ' (N.ψ'' θ) θ) :
    IsSemiconjOn (ebSys N q (sirRxns τ γ)) (pgfSys N (sirRxns τ γ))
      {u | N.ψ u.1 ≠ 0 ∧ N.ψ' u.1 ≠ 0 ∧ u.2.1 ≠ 0} (pwImage N q) :=
  eb_to_pws_global N q hq hψ hψ' _

/-- **EB → PW^S for SEIR, for every C² ψ (M6, SEIR instance).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M6): "It holds **for every C² ψ and every T_EB
model**, on U = {ψ ≠ 0, ψ' ≠ 0}"; §D.7, L4e: "SIR and SEIR with generic C² ψ via `HasDerivAt`
hypotheses".

Lean statement: for every configuration network `N` with `ψ'`, `ψ''` the derivatives of `ψ`, `ψ'`
at every real θ, all rates τ, a, γ and `q ≠ 0`, π^PW is a local semiconjugacy on
`{ψ(θ) ≠ 0, ψ'(θ) ≠ 0, ξ ≠ 0}` from EB SEIR on `N` to the PGF-closure S-anchored pairwise SEIR
model. -/
theorem eb_to_pws_seir_global (N : CNet) (q τ a γ : ℝ) (hq : q ≠ 0)
    (hψ : ∀ θ, HasDerivAt N.ψ (N.ψ' θ) θ) (hψ' : ∀ θ, HasDerivAt N.ψ' (N.ψ'' θ) θ) :
    IsSemiconjOn (ebSys N q (seirRxns τ a γ)) (pgfSys N (seirRxns τ a γ))
      {u | N.ψ u.1 ≠ 0 ∧ N.ψ' u.1 ≠ 0 ∧ u.2.1 ≠ 0} (pwImage N q) :=
  eb_to_pws_global N q hq hψ hψ' _

/-- **For a Poisson-type degree distribution the constant closure κ is exact, with no
condition on ψ' (M8 ⇒ M6).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M8): "PT ⇔ constant closure | On an interval I
with ψ > 0: K_ψ ≡ κ ⇔ ψ' = αψ^κ [...] So NBM's constant closure ⟨k(k−1)⟩/⟨k⟩² is exact **iff**
the degree distribution is PT"; §C.3: "heterogeneous pairwise with constant K =
closure_constant(d) (exact iff PT, M8)".

Lean statement: as `eb_to_pws_pt` without the hypothesis `ψ' ≠ 0` on Θ: let `σ` be finite, `rs`
any T_EB list, `q ≠ 0`, `Θ` convex with nonempty interior, ψ' and ψ'' the derivatives of ψ and ψ'
on Θ, ψ > 0 on Θ and `ψ' = αψ^κ` on Θ. Then `u ↦ ([s], [ss], [sX], [X])` is a local
semiconjugacy on `pwsDomain N Θ = {θ ∈ Θ, ψ(θ) ≠ 0, ψ'(θ) ≠ 0, ξ ≠ 0}` from EB to the S-anchored
pairwise model with the constant closure κ. (If `α = 0` the domain is empty.) -/
theorem eb_to_pws_pt_any (N : CNet) (q α κ : ℝ) (hq : q ≠ 0) (Θ : Set ℝ) (hΘ : Convex ℝ Θ)
    (hΘi : (interior Θ).Nonempty) (hψ : ∀ θ ∈ Θ, HasDerivAt N.ψ (N.ψ' θ) θ)
    (hψ' : ∀ θ ∈ Θ, HasDerivAt N.ψ' (N.ψ'' θ) θ) (hpos : ∀ θ ∈ Θ, 0 < N.ψ θ)
    (hPT : ∀ θ ∈ Θ, N.ψ' θ = α * N.ψ θ ^ κ) (rs : List (Rxn σ)) :
    IsSemiconjOn (ebSys N q rs) (pwSSys κ rs) (pwsDomain N Θ) (fun u => (pwImage N q u).2) := by
  by_cases hα : α = 0
  · have h0 : ∀ u ∈ pwsDomain (σ := σ) N Θ, False := fun u hu =>
      hu.2.2.1 (by rw [hPT u.1 hu.1, hα, zero_mul])
    exact ⟨fun u hu => (h0 u hu).elim, fun u hu => (h0 u hu).elim⟩
  · have hne : ∀ θ ∈ Θ, N.ψ' θ ≠ 0 := fun θ hθ => by
      rw [hPT θ hθ]
      exact mul_ne_zero hα (Real.rpow_pos_of_pos (hpos θ hθ) κ).ne'
    exact eb_to_pws_pt N q α κ hq Θ hΘ hΘi hψ hψ' hpos hne hPT rs

/-- **For a Poisson-type degree distribution NBM's constant closure ψ''(1)/ψ'(1)² is exact
(M8 ⇒ M6).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M8): "So NBM's constant closure ⟨k(k−1)⟩/⟨k⟩²
is exact **iff** the degree distribution is PT"; §C.1: "closure_constant(d) # K_ψ(1) =
ψ''(1)/ψ'(1)²  (NBM's heterogeneous constant closure)"; §C.3: "heterogeneous pairwise with
constant K = closure_constant(d) (exact iff PT, M8)".

Lean statement: under the hypotheses of `eb_to_pws_pt_any` (finite σ, any T_EB list, `q ≠ 0`,
Θ convex with nonempty interior, derivative relations on Θ, ψ > 0 on Θ, `ψ' = αψ^κ` on Θ), assume
moreover `1 ∈ Θ` and `ψ(1) = 1`. Then `u ↦ ([s], [ss], [sX], [X])` is a local semiconjugacy on
`pwsDomain N Θ` from EB to the S-anchored pairwise model with NBM's constant closure
`K = ψ''(1)/ψ'(1)²`. (If `ψ'(1) = 0` then `α = 0` and the domain is empty; otherwise
`κ = ψ''(1)/ψ'(1)²` by `pt_constants_at_one`.) -/
theorem eb_to_pws_pt_closure_one (N : CNet) (q α κ : ℝ) (hq : q ≠ 0) (Θ : Set ℝ)
    (hΘ : Convex ℝ Θ) (hΘi : (interior Θ).Nonempty) (hψ : ∀ θ ∈ Θ, HasDerivAt N.ψ (N.ψ' θ) θ)
    (hψ' : ∀ θ ∈ Θ, HasDerivAt N.ψ' (N.ψ'' θ) θ) (hpos : ∀ θ ∈ Θ, 0 < N.ψ θ)
    (hPT : ∀ θ ∈ Θ, N.ψ' θ = α * N.ψ θ ^ κ) (h1 : (1 : ℝ) ∈ Θ) (hψ1 : N.ψ 1 = 1)
    (rs : List (Rxn σ)) :
    IsSemiconjOn (ebSys N q rs) (pwSSys (N.ψ'' 1 / N.ψ' 1 ^ 2) rs) (pwsDomain N Θ)
      (fun u => (pwImage N q u).2) := by
  obtain ⟨hα1, hκ1, -⟩ := pt_constants_at_one N hΘ hΘi hpos
    (fun θ hθ => (hψ θ hθ).hasDerivWithinAt) (fun θ hθ => (hψ' θ hθ).hasDerivWithinAt) h1 hψ1 hPT
  by_cases hm : N.ψ' 1 = 0
  · have h0 : ∀ u ∈ pwsDomain (σ := σ) N Θ, False := fun u hu =>
      hu.2.2.1 (by rw [hPT u.1 hu.1, hα1, hm, zero_mul])
    exact ⟨fun u hu => (h0 u hu).elim, fun u hu => (h0 u hu).elim⟩
  · rw [← hκ1 hm]
    exact eb_to_pws_pt_any N q α κ hq Θ hΘ hΘi hψ hψ' hpos hPT rs

/-- **On a Poisson network the constant closure K = 1 is exact, for every μ (M6, M8, Poisson
instance).**

Design statement (DESIGN_NetworkEpiCore.md §D.5, M8): "So NBM's constant closure ⟨k(k−1)⟩/⟨k⟩² is
exact **iff** the degree distribution is PT"; §0: "This covers Poisson (κ = 1)".

Lean statement: for every finite type of node species, every T_EB reaction list `rs`, every real
`μ` and `q ≠ 0`, the map `u ↦ ([s], [ss], [sX], [X])` (π^PW without θ) is a local semiconjugacy
on the M6 domain `{ψ(θ) ≠ 0, ψ'(θ) ≠ 0, ξ ≠ 0}` of the Poisson(μ) network from the EB model of
`rs` on Poisson(μ) to the S-anchored pairwise model with the constant closure K = 1. (For `μ = 0`,
`ψ' ≡ 0` and the domain is empty; for `μ ≠ 0` it is `{ξ ≠ 0}`, see `eb_to_pws_poisson`.) -/
theorem eb_to_pws_poisson_any (μ q : ℝ) (hq : q ≠ 0) (rs : List (Rxn σ)) :
    IsSemiconjOn (ebSys (CNet.poisson μ) q rs) (pwSSys 1 rs)
      {u | (CNet.poisson μ).ψ u.1 ≠ 0 ∧ (CNet.poisson μ).ψ' u.1 ≠ 0 ∧ u.2.1 ≠ 0}
      (fun u => (pwImage (CNet.poisson μ) q u).2) := by
  by_cases hμ : μ = 0
  · have h0 : ∀ u ∈ {u : EB σ | (CNet.poisson μ).ψ u.1 ≠ 0 ∧ (CNet.poisson μ).ψ' u.1 ≠ 0 ∧
        u.2.1 ≠ 0}, False := fun u hu => hu.2.1 (by simp [CNet.poisson, hμ])
    exact ⟨fun u hu => (h0 u hu).elim, fun u hu => (h0 u hu).elim⟩
  · have h := eb_to_pws_const (CNet.poisson μ) q 1 hq Set.univ
      (fun θ _ => CNet.poisson_hasDerivAt_ψ μ θ) (fun θ _ => CNet.poisson_hasDerivAt_ψ' μ θ)
      (fun θ _ => (poisson_closureK μ hμ θ).2) rs
    rwa [pwsDomain_univ] at h

omit [DecidableEq σ] [Fintype σ] in
/-- **The M6 domain on a Poisson network, with its reason.**

Design statement (DESIGN_NetworkEpiCore.md §L.3): "Domain U = {ψ ≠ 0, ψ' ≠ 0, ξ ≠ 0} with q ≠ 0".

Lean statement: for every real `μ`, the Poisson(μ) PGF is positive everywhere; for `μ ≠ 0` its
derivative `ψ'` vanishes nowhere, and hence the M6 domain over all θ is `{ξ ≠ 0}`. -/
theorem pwsDomain_poisson_spec (μ : ℝ) :
    (μ ≠ 0 → pwsDomain (σ := σ) (CNet.poisson μ) Set.univ = {u | u.2.1 ≠ 0}) ∧
      (∀ x : ℝ, 0 < (CNet.poisson μ).ψ x) ∧
      (μ ≠ 0 → ∀ x : ℝ, (CNet.poisson μ).ψ' x ≠ 0) :=
  ⟨pwsDomain_poisson μ, fun _ => Real.exp_pos _,
    fun hμ _ => mul_ne_zero hμ (Real.exp_pos _).ne'⟩

/-- **The M6 domain on a Poisson(μ) network with `μ ≠ 0`, with its reason.**

Design statement (DESIGN_NetworkEpiCore.md §L.3): "Domain U = {ψ ≠ 0, ψ' ≠ 0, ξ ≠ 0} with q ≠ 0".

Lean statement: for `μ ≠ 0`, the M6 domain of the Poisson(μ) network over all θ is `{ξ ≠ 0}` (for
every species type), the Poisson(μ) PGF ψ is positive everywhere, and its derivative ψ' vanishes
nowhere. (`pwsDomain_poisson_spec` also gives ψ > 0 for `μ = 0`.) -/
theorem pwsDomain_poisson_of_ne (μ : ℝ) (hμ : μ ≠ 0) :
    (∀ {σ : Type}, pwsDomain (σ := σ) (CNet.poisson μ) Set.univ = {u : EB σ | u.2.1 ≠ 0}) ∧
      (∀ x : ℝ, 0 < (CNet.poisson μ).ψ x) ∧ (∀ x : ℝ, (CNet.poisson μ).ψ' x ≠ 0) :=
  ⟨fun {σ} => (pwsDomain_poisson_spec (σ := σ) μ).1 hμ,
    (pwsDomain_poisson_spec (σ := Unit) μ).2.1, (pwsDomain_poisson_spec (σ := Unit) μ).2.2 hμ⟩

end Semiconj

end NEP
