import NetworkEpi.Dyn.Basic
import NetworkEpi.Syntax.Rxn
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.MeanValue

/-!
# L3: the per-reaction edge-based (EB) field on a configuration network

DESIGN_NetworkEpiCore.md §D.4 ("The EB field of one reaction on a configuration network. This is
the assembler's contract (WP17)") and §D.7 module L3 `NEP/Semantics/{MA,EB}`: "`maField`,
`ebField` (with ξ); `lift_append`, `ebField_map`, `lift_map` (relabelling/gluing naturality with
pushforward along fibres); `conservation`".

## Coordinates

One susceptible species `s` (implicit) on an untyped, single-layer configuration network with
degree PGF ψ. The state `u : EB σ` is `(θ, ξ, φ, pop)`:
* `θ`: the probability that a random edge has not transmitted to the test node;
* `ξ`: the exit survival factor (ξ ≡ 1 if there are no exits);
* `φ X` (for node species `X : σ`): the probability that a random edge has not transmitted and
  its partner is in `X`;
* `pop X`: the fraction of nodes in `X`.

The seed factor `q = 1 − Σ_X ρ_X` is a parameter. The susceptible observables are
`S = qξψ(θ)` (`CNet.susc`) and `φ_S = qξψ'(θ)/ψ'(1)` (`CNet.phiS`). The design's cumulative
incidence accumulator `cum` is not a state variable here.

## The field (DESIGN §D.4, quoted)

```
contact  r = (s + J → X + J, τ_r):  θ̇     += −τ_r φ_J
                                     φ̇_J   += −τ_r φ_J
                                     φ̇_X   += +τ_r φ_J · qξ ψ''(θ)/ψ'(1)
                                     pop_X' += +τ_r φ_J · qξ ψ'(θ)
transition t = (X → Y | ∅, a):       φ̇_X −= a φ_X; φ̇_Y += a φ_X; pop_X' −= a pop_X; pop_Y' += a pop_X
                                     (Y = ∅: no gains)
exit     e = (s → Y, ν_e):           ξ̇ += −ν_e ξ;  φ̇_Y += ν_e φ_S;  pop_Y' += ν_e S
initial condition:                   θ(0) = 1, ξ(0) = 1, φ_X(0) = pop_X(0) = ρ_X
```

`ebField N q r u` is exactly this contribution of reaction `r` at state `u`, and `lift N q rs u`
is the sum of the contributions of the reactions in the list `rs`.
-/

open scoped BigOperators

namespace NEP

/-- Degree data of a configuration network: the degree PGF `ψ` and two functions `ψ'`, `ψ''`
standing for its first and second derivatives. The lift laws (`lift_append`, `lift_map`,
`lift_glue`) hold for arbitrary functions; results that differentiate along solutions
(`conservation`, `node_conservation`) assume `HasDerivAt` relations between them. -/
structure CNet where
  /-- The degree PGF ψ. -/
  ψ : ℝ → ℝ
  /-- ψ' (the first derivative of ψ where assumed). -/
  ψ' : ℝ → ℝ
  /-- ψ'' (the second derivative of ψ where assumed). -/
  ψ'' : ℝ → ℝ

/-- The fraction of susceptible nodes, `S = qξψ(θ)` (DESIGN §0). -/
noncomputable def CNet.susc (N : CNet) (q θ ξ : ℝ) : ℝ := q * ξ * N.ψ θ

/-- The susceptible edge probability, `φ_S = qξψ'(θ)/ψ'(1)` (DESIGN §0). -/
noncomputable def CNet.phiS (N : CNet) (q θ ξ : ℝ) : ℝ := q * ξ * N.ψ' θ / N.ψ' 1

/-- EB coordinates `(θ, ξ, φ, pop)` over node species `σ`. -/
abbrev EB (σ : Type) := ℝ × ℝ × (σ → ℝ) × (σ → ℝ)

variable {σ σ' σA σB : Type}

section Field
variable [DecidableEq σ]

/-- **The EB field of one reaction** (DESIGN §D.4; see the module docstring for the quoted
table). For `contact J X τ` (s + J → X + J): `θ̇ = −τφ_J`, `φ̇_J −= τφ_J`,
`φ̇_X += τφ_J·qξψ''(θ)/ψ'(1)`, `pop_X' += τφ_J·qξψ'(θ)`. For `exit Y ν` (s → Y):
`ξ̇ = −νξ`, `φ̇_Y += νφ_S`, `pop_Y' += νS`. For `trans X Y a`: `φ̇_X −= aφ_X`, `φ̇_Y += aφ_X`,
`pop_X' −= a pop_X`, `pop_Y' += a pop_X` (no gains when `Y = none`, i.e. `X → ∅`). -/
noncomputable def ebField (N : CNet) (q : ℝ) : Rxn σ → EB σ → EB σ
  | .contact J X τ, (θ, ξ, φ, _) =>
      (-(τ * φ J), 0,
        Pi.single X (τ * φ J * (q * ξ * N.ψ'' θ / N.ψ' 1)) - Pi.single J (τ * φ J),
        Pi.single X (τ * φ J * (q * ξ * N.ψ' θ)))
  | .exit Y ν, (θ, ξ, _, _) =>
      (0, -(ν * ξ), Pi.single Y (ν * N.phiS q θ ξ), Pi.single Y (ν * N.susc q θ ξ))
  | .trans X none a, (_, _, φ, p) =>
      (0, 0, -Pi.single X (a * φ X), -Pi.single X (a * p X))
  | .trans X (some Y) a, (_, _, φ, p) =>
      (0, 0, Pi.single Y (a * φ X) - Pi.single X (a * φ X),
        Pi.single Y (a * p X) - Pi.single X (a * p X))

/-- The EB vector field of a reaction list: the sum of the per-reaction fields. -/
noncomputable def lift (N : CNet) (q : ℝ) (rs : List (Rxn σ)) (u : EB σ) : EB σ :=
  (rs.map fun r => ebField N q r u).sum

/-- `lift N q rs u` is the sum of the contributions `ebField N q r u` of the reactions `r` in the
list `rs` (the definition of `lift`, stated as a theorem). -/
theorem lift_eq_sum (N : CNet) (q : ℝ) (rs : List (Rxn σ)) (u : EB σ) :
    lift N q rs u = (rs.map fun r => ebField N q r u).sum :=
  rfl

/-- The EB model of `rs` on the configuration network `N` as an object of `DynSys`. -/
noncomputable def ebSys [Fintype σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)) : DynSys where
  V := EB σ
  F := lift N q rs

/-- **H1, part 1: the EB lift is additive in the reaction list.**

Design statement (DESIGN_NetworkEpiCore.md §D.4, table row EB_N, column "Strict under gluing?"):
"**yes**: the per-reaction lift is additive and natural in species maps ([L] `lift_append`,
`lift_map`)"; §D.6:
"**H1** EB(glue(A,B)) = glue(EB A, EB B), for fixed N with s glued to s | **yes, strict** |
local per-reaction fields | [L] `lift_append`, `lift_map` (contact/transition; the exit case is
added in WP13)".

Lean statement: for every configuration network `N` (arbitrary functions ψ, ψ', ψ''), every seed
factor `q`, all T_EB reaction lists `rs`, `rs'` (contacts, exits, progressions and removals) and
every state `u = (θ, ξ, φ, pop)`, the EB field of the concatenation `rs ++ rs'` at `u` is the sum
of the EB fields of `rs` and of `rs'` at `u`. -/
theorem lift_append (N : CNet) (q : ℝ) (rs rs' : List (Rxn σ)) (u : EB σ) :
    lift N q (rs ++ rs') u = lift N q rs u + lift N q rs' u := by
  simp [lift, List.map_append, List.sum_append]

end Field

/-! ## Relabelling and gluing species -/

section Push
variable [Fintype σ] [DecidableEq σ']

/-- Pushforward of species-indexed coordinates along a species map `f`: the value at `y` is the
sum over the fibre `f⁻¹(y)`. -/
def push (f : σ → σ') (v : σ → ℝ) : σ' → ℝ :=
  fun y => ∑ x ∈ Finset.univ.filter (fun x => f x = y), v x

/-- The pushforward of `Pi.single X c` is `Pi.single (f X) c`. -/
lemma push_single [DecidableEq σ] (f : σ → σ') (X : σ) (c : ℝ) : push f (Pi.single X c) = Pi.single (f X) c := by
  funext y
  simp only [push, Pi.single_apply]
  rw [Finset.sum_ite_eq' (Finset.univ.filter fun x => f x = y) X (fun _ => c)]
  by_cases h : f X = y <;> simp [h, eq_comm]

/-- The pushforward is additive. -/
lemma push_add (f : σ → σ') (v w : σ → ℝ) : push f (v + w) = push f v + push f w := by
  funext y; simp [push, Finset.sum_add_distrib]

/-- The pushforward commutes with negation. -/
lemma push_neg (f : σ → σ') (v : σ → ℝ) : push f (-v) = -push f v := by
  funext y; simp [push]

/-- The pushforward commutes with subtraction. -/
lemma push_sub (f : σ → σ') (v w : σ → ℝ) : push f (v - w) = push f v - push f w := by
  rw [sub_eq_add_neg, push_add, push_neg, ← sub_eq_add_neg]

/-- The pushforward of zero is zero. -/
lemma push_zero (f : σ → σ') : push f (0 : σ → ℝ) = 0 := by
  funext y; simp [push]

/-- Pushforward of EB coordinates along a species map: `θ` and `ξ` are kept (the susceptible
species is glued to itself), `φ` and `pop` are summed over fibres. -/
def pushEB (f : σ → σ') (u : EB σ) : EB σ' := (u.1, u.2.1, push f u.2.2.1, push f u.2.2.2)

/-- The pushforward of EB coordinates is additive. -/
lemma pushEB_add (f : σ → σ') (u v : EB σ) : pushEB f (u + v) = pushEB f u + pushEB f v := by
  obtain ⟨θ, ξ, φ, p⟩ := u
  obtain ⟨θ', ξ', φ', p'⟩ := v
  simp only [pushEB, Prod.mk_add_mk, push_add]

/-- The pushforward of the zero EB vector is zero. -/
lemma pushEB_zero (f : σ → σ') : pushEB f (0 : EB σ) = 0 := by
  simp only [pushEB, Prod.fst_zero, Prod.snd_zero, push_zero, Prod.mk_zero_zero]

end Push

/-- Pullback of EB coordinates along a species map: `θ` and `ξ` are kept, `φ` and `pop` are
precomposed with `f`. -/
def pullEB (f : σ → σ') (u : EB σ') : EB σ := (u.1, u.2.1, u.2.2.1 ∘ f, u.2.2.2 ∘ f)

section Naturality
variable [Fintype σ] [DecidableEq σ] [DecidableEq σ']

/-- **Naturality of the per-reaction EB field in species maps.**

Design statement (DESIGN_NetworkEpiCore.md §D.7, L3): "`lift_append`, `ebField_map`, `lift_map`
(relabelling/gluing naturality with pushforward along fibres)".

Lean statement: for every species map `f : σ → σ'`, every T_EB reaction `r` over `σ` and every
state `u` over `σ'`, the field of the relabelled reaction `r.map f` at `u` equals the pushforward
along `f` of the field of `r` at the pulled-back state `pullEB f u`. -/
theorem ebField_map (N : CNet) (q : ℝ) (f : σ → σ') (r : Rxn σ) (u : EB σ') :
    ebField N q (r.map f) u = pushEB f (ebField N q r (pullEB f u)) := by
  obtain ⟨θ, ξ, φ, p⟩ := u
  cases r with
  | contact J X τ =>
      simp only [Rxn.map, ebField, pushEB, pullEB, Function.comp, push_sub, push_single]
  | exit Y ν =>
      simp only [Rxn.map, ebField, pushEB, pullEB, push_single]
  | trans X Y a =>
      cases Y <;>
        simp only [Rxn.map, Option.map, ebField, pushEB, pullEB, Function.comp, push_sub,
          push_neg, push_single]

/-- **H1, part 2: the EB lift is natural in species maps (relabelling and gluing).**

Design statement (DESIGN_NetworkEpiCore.md §D.4, row EB_N): "the per-reaction lift is additive
and natural in species maps ([L] `lift_append`, `lift_map`)"; §D.7, L3: "`lift_map`
(relabelling/gluing naturality with pushforward along fibres)"; §D.6 H1 (quoted at
`lift_append`), with the exit case included.

Lean statement: for every configuration network `N`, seed factor `q`, species map
`f : σ → σ'` (σ finite), T_EB reaction list `rs` over `σ` (contacts, exits, progressions and
removals) and state `u` over `σ'`, the EB field of the relabelled list `rs.map (Rxn.map f)` at
`u` equals the pushforward along `f` (θ, ξ kept; φ, pop summed over the fibres of `f`) of the EB
field of `rs` at the pulled-back state `(θ, ξ, φ ∘ f, pop ∘ f)`. -/
theorem lift_map (N : CNet) (q : ℝ) (f : σ → σ') (rs : List (Rxn σ)) (u : EB σ') :
    lift N q (rs.map (Rxn.map f)) u = pushEB f (lift N q rs (pullEB f u)) := by
  induction rs with
  | nil => simp only [lift, List.map_nil, List.sum_nil, pushEB_zero]
  | cons r rs ih =>
      simp only [lift, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih, ebField_map, pushEB_add]

end Naturality

/-- **H1: the EB lift is strict under gluing.**

Design statement (DESIGN_NetworkEpiCore.md §D.6): "**H1** EB(glue(A,B)) = glue(EB A, EB B), for
fixed N with s glued to s | **yes, strict** | local per-reaction fields"; §D.3 (open systems):
"composition identifies ported coordinates and **adds** vector fields".

Lean statement: let `f : σA → σ` and `g : σB → σ` be a cospan of finite species types (the
gluing of the species of `A` and `B` along shared species; the susceptible species is glued to
itself). For every configuration network `N`, seed factor `q`, T_EB reaction lists `A` over `σA`
and `B` over `σB` and every state `u` over `σ`, the EB field of the glued model
`A.map f ++ B.map g` at `u` equals the sum of the pushforward along `f` of the EB field of `A` at
`pullEB f u` and the pushforward along `g` of the EB field of `B` at `pullEB g u`. -/
theorem lift_glue [DecidableEq σ] [Fintype σA] [Fintype σB] [DecidableEq σA] [DecidableEq σB]
    (N : CNet) (q : ℝ) (f : σA → σ) (g : σB → σ) (A : List (Rxn σA)) (B : List (Rxn σB))
    (u : EB σ) :
    lift N q (A.map (Rxn.map f) ++ B.map (Rxn.map g)) u =
      pushEB f (lift N q A (pullEB f u)) + pushEB g (lift N q B (pullEB g u)) := by
  rw [lift_append, lift_map, lift_map]

/-! ## Conservation laws

**Solutions on a time interval.** The results below are stated for a solution on a *time
interval*: a convex set `I ⊆ ℝ` of times with `0 ∈ I`, such as `(a, b)` with `a < 0 < b`, `[0, T)`,
`[0, ∞)` or `ℝ`. A curve `x : ℝ → EB σ` *solves the EB model of `rs` on `I`* if
`HasDerivWithinAt x (lift N q rs (x t)) I t` for every `t ∈ I`. At an end point of `I` that lies
in `I` (for example `t = 0` for `I = [0, T)`) this is a one-sided derivative. A curve with
`HasDerivAt x (lift N q rs (x t)) t` at every `t ∈ I` satisfies it (`HasDerivAt.hasDerivWithinAt`).
Only the values of `x` on `I` matter.

Global solutions (`I = ℝ`) need not exist. For example, integrated numerically, EB SEIR on a
Poisson(5) network (τ = 1/6, σ = 1/3, γ = 1/4, θ(0) = ξ(0) = 1, φ_E(0) = 0, φ_I(0) = 0.01,
q = 0.99) blows up backward in time at t ≈ −7.33. Such a model still has local solutions on an
interval `(−ε, ε)`: `NetworkEpi.Semantics.Solutions` proves that they exist for every T_EB model
whose ψ, ψ', ψ'' are C¹ at the initial θ (`exists_local_solution`). From physical states it
also has forward solutions on `[0, ∞)`, since the coordinates stay bounded; that is not
formalised here.

The degree data enter only through derivative relations at the θ values that the solution
visits (`∀ t ∈ I, HasDerivAt N.ψ' (N.ψ'' θ(t)) θ(t)`), so a PGF with a pole away from the
visited θ values (for example a negative binomial PGF, pole at `1/(1 − p) > 1`) is covered. -/

section Conservation

/-- `rs.removalFlux φ = Σ_{(X → ∅, a) ∈ rs} a φ_X`, the rate at which edge mass leaves the φ
classes through removals `X → ∅`. -/
noncomputable def Rxn.removalRate (φ : σ → ℝ) : Rxn σ → ℝ
  | .trans X none a => a * φ X
  | _ => 0

/-- The total removal rate of a reaction list, evaluated on species-indexed coordinates `v`. -/
noncomputable def removalFlux (rs : List (Rxn σ)) (v : σ → ℝ) : ℝ :=
  (rs.map fun r => r.removalRate v).sum

/-- A reaction is a removal `X → ∅`. -/
def Rxn.isRemoval : Rxn σ → Bool
  | .trans _ none _ => true
  | _ => false

/-- Without removals `X → ∅` the removal flux vanishes. -/
lemma removalFlux_eq_zero (rs : List (Rxn σ)) (hrs : ∀ r ∈ rs, r.isRemoval = false)
    (v : σ → ℝ) : removalFlux rs v = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      have hr := hrs r (by simp)
      have ht : r.removalRate v = 0 := by
        cases r with
        | trans X Y a => cases Y <;> simp_all [Rxn.isRemoval, Rxn.removalRate]
        | _ => rfl
      simp only [removalFlux, List.map_cons, List.sum_cons] at ih ⊢
      rw [ht, ih (fun r' hr' => hrs r' (by simp [hr']))]
      ring

/-- The removal flux is non-negative when every removal rate and every coordinate is: if
`a ≥ 0` for every removal `(X → ∅, a)` in `rs` and `v X ≥ 0` for every `X`, then
`Σ_{(X → ∅, a) ∈ rs} a v_X ≥ 0`. -/
theorem removalFlux_nonneg (rs : List (Rxn σ)) (v : σ → ℝ)
    (ha : ∀ X a, Rxn.trans X none a ∈ rs → 0 ≤ a) (hv : ∀ X, 0 ≤ v X) :
    0 ≤ removalFlux rs v := by
  induction rs with
  | nil => exact le_refl 0
  | cons r rs ih =>
      have ht : 0 ≤ r.removalRate v := by
        cases r with
        | trans X Y a =>
            cases Y with
            | none => exact mul_nonneg (ha X a (by simp)) (hv X)
            | some Y => exact le_refl 0
        | _ => exact le_refl 0
      simp only [removalFlux, List.map_cons, List.sum_cons] at ih ⊢
      exact add_nonneg ht (ih fun X a h => ha X a (List.mem_cons_of_mem _ h))

/-- **Chain rule for a continuous linear map applied to a curve, within a set of times** (for
curves in any real normed space `E`): if `x'` is the derivative of `x : ℝ → E` within `I` at `t`
and `L : E →L[ℝ] F`, then `L x'` is the derivative of `t ↦ L (x t)` within `I` at `t`. -/
theorem hasDerivWithinAt_clm_comp {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) {x : ℝ → E} {x' : E} {I : Set ℝ}
    {t : ℝ} (hx : HasDerivWithinAt x x' I t) :
    HasDerivWithinAt (fun t => L (x t)) (L x') I t :=
  L.hasFDerivAt.comp_hasDerivWithinAt t hx

/-- Chain rule for a continuous linear map applied to a curve in a topological vector space
(used for `EB σ` with `σ` infinite, where `σ → ℝ` carries the product topology). -/
lemma hasDerivWithinAt_clm_comp_tvs {E F : Type} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [AddCommGroup F]
    [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] (L : E →L[ℝ] F)
    {x : ℝ → E} {x' : E} {I : Set ℝ} {t : ℝ} (hx : HasDerivWithinAt x x' I t) :
    HasDerivWithinAt (fun t => L (x t)) (L x') I t := by
  obtain ⟨h⟩ := hx
  refine ⟨?_⟩
  have := (L.isBigOTVS_id (l := Filter.map (fun p : ℝ × ℝ => x p.1 - x p.2 -
    (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) x') (p.1 - p.2))
      (nhdsWithin t I ×ˢ pure t))).comp_tendsto Filter.tendsto_map
  refine (this.trans_isLittleOTVS h).congr_left ?_
  intro p
  simp

/-- The θ-coordinate of a curve in `EB σ` (any species type `σ`, product topology) has, within
`I`, the θ-coordinate of its derivative. -/
theorem hasDerivWithinAt_θ_any {x : ℝ → EB σ} {x' : EB σ} {I : Set ℝ} {t : ℝ}
    (hx : HasDerivWithinAt x x' I t) : HasDerivWithinAt (fun t => (x t).1) x'.1 I t :=
  hasDerivWithinAt_clm_comp_tvs (E := EB σ) (ContinuousLinearMap.fst ℝ ℝ _) hx

/-- The ξ-coordinate of a curve in `EB σ` (any species type `σ`) has, within `I`, the
ξ-coordinate of its derivative. -/
theorem hasDerivWithinAt_ξ_any {x : ℝ → EB σ} {x' : EB σ} {I : Set ℝ} {t : ℝ}
    (hx : HasDerivWithinAt x x' I t) : HasDerivWithinAt (fun t => (x t).2.1) x'.2.1 I t :=
  hasDerivWithinAt_clm_comp_tvs (E := EB σ)
    ((ContinuousLinearMap.fst ℝ ℝ _).comp (ContinuousLinearMap.snd ℝ ℝ _)) hx

/-- Each φ-coordinate of a curve in `EB σ` (any species type `σ`) has, within `I`, the
φ-coordinate of its derivative. -/
theorem hasDerivWithinAt_φ_any {x : ℝ → EB σ} {x' : EB σ} {I : Set ℝ} {t : ℝ}
    (hx : HasDerivWithinAt x x' I t) (X : σ) :
    HasDerivWithinAt (fun t => (x t).2.2.1 X) (x'.2.2.1 X) I t :=
  hasDerivWithinAt_clm_comp_tvs (E := EB σ) ((ContinuousLinearMap.proj X).comp
    ((ContinuousLinearMap.fst ℝ _ _).comp
      ((ContinuousLinearMap.snd ℝ ℝ _).comp (ContinuousLinearMap.snd ℝ ℝ _)))) hx

/-- Each pop-coordinate of a curve in `EB σ` (any species type `σ`) has, within `I`, the
pop-coordinate of its derivative. -/
theorem hasDerivWithinAt_pop_any {x : ℝ → EB σ} {x' : EB σ} {I : Set ℝ} {t : ℝ}
    (hx : HasDerivWithinAt x x' I t) (X : σ) :
    HasDerivWithinAt (fun t => (x t).2.2.2 X) (x'.2.2.2 X) I t :=
  hasDerivWithinAt_clm_comp_tvs (E := EB σ) ((ContinuousLinearMap.proj X).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp
      ((ContinuousLinearMap.snd ℝ ℝ _).comp (ContinuousLinearMap.snd ℝ ℝ _)))) hx

/-- **Chain rule for a continuous linear map applied to a curve in the EB state space, within a
set of times**, for every species type `σ` (for infinite `σ`, `EB σ` carries the product topology
and is not a normed space) and every real normed target `F`. -/
theorem hasDerivWithinAt_clm_comp_EB {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : EB σ →L[ℝ] F) {x : ℝ → EB σ} {x' : EB σ} {I : Set ℝ} {t : ℝ}
    (hx : HasDerivWithinAt x x' I t) : HasDerivWithinAt (fun s => L (x s)) (L x') I t :=
  hasDerivWithinAt_clm_comp_tvs L hx

variable [Fintype σ]

/-- The sum over all species of `Pi.single X c` is `c`. -/
lemma sum_single [DecidableEq σ] (X : σ) (c : ℝ) : ∑ Y, (Pi.single X c : σ → ℝ) Y = c := by
  rw [Finset.sum_pi_single' X c Finset.univ]
  simp

/-- The *edge defect* `θ − φ_S − Σ_X φ_X`. The design's conservation law says it vanishes. -/
noncomputable def edgeDefect (N : CNet) (q : ℝ) (u : EB σ) : ℝ :=
  u.1 - N.phiS q u.1 u.2.1 - ∑ X, u.2.2.1 X

/-- The derivative of `edgeDefect` at `u` in the direction `v`, when `ψ''` is the derivative of
`ψ'` at `u.1`. -/
noncomputable def edgeDefectDeriv (N : CNet) (q : ℝ) (u v : EB σ) : ℝ :=
  v.1 - q * (v.2.1 * N.ψ' u.1 + u.2.1 * (N.ψ'' u.1 * v.1)) / N.ψ' 1 - ∑ X, v.2.2.1 X

/-- The node total `S + Σ_X pop_X = qξψ(θ) + Σ_X pop_X`. -/
noncomputable def nodeTotal (N : CNet) (q : ℝ) (u : EB σ) : ℝ :=
  N.susc q u.1 u.2.1 + ∑ X, u.2.2.2 X

/-- The derivative of `nodeTotal` at `u` in the direction `v`, when `ψ'` is the derivative of
`ψ` at `u.1`. -/
noncomputable def nodeTotalDeriv (N : CNet) (q : ℝ) (u v : EB σ) : ℝ :=
  q * (v.2.1 * N.ψ u.1 + u.2.1 * (N.ψ' u.1 * v.1)) + ∑ X, v.2.2.2 X

/-- Chain rule for a continuous linear map applied to a curve, within a set of times. -/
lemma hasDerivWithinAt_comp_clm {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : EB σ →L[ℝ] F) {x : ℝ → EB σ} {x' : EB σ} {I : Set ℝ} {t : ℝ}
    (hx : HasDerivWithinAt x x' I t) : HasDerivWithinAt (fun t => L (x t)) (L x') I t :=
  L.hasFDerivAt.comp_hasDerivWithinAt t hx

/-- The θ-coordinate of a curve has, within `I`, the θ-coordinate of its derivative. -/
lemma hasDerivWithinAt_θ {x : ℝ → EB σ} {x' : EB σ} {I : Set ℝ} {t : ℝ}
    (hx : HasDerivWithinAt x x' I t) : HasDerivWithinAt (fun t => (x t).1) x'.1 I t :=
  hasDerivWithinAt_comp_clm (ContinuousLinearMap.fst ℝ ℝ _) hx

/-- The ξ-coordinate of a curve has, within `I`, the ξ-coordinate of its derivative. -/
lemma hasDerivWithinAt_ξ {x : ℝ → EB σ} {x' : EB σ} {I : Set ℝ} {t : ℝ}
    (hx : HasDerivWithinAt x x' I t) : HasDerivWithinAt (fun t => (x t).2.1) x'.2.1 I t :=
  hasDerivWithinAt_comp_clm
    ((ContinuousLinearMap.fst ℝ ℝ _).comp (ContinuousLinearMap.snd ℝ ℝ _)) hx

/-- Each φ-coordinate of a curve has, within `I`, the φ-coordinate of its derivative. -/
lemma hasDerivWithinAt_φ {x : ℝ → EB σ} {x' : EB σ} {I : Set ℝ} {t : ℝ}
    (hx : HasDerivWithinAt x x' I t) (X : σ) :
    HasDerivWithinAt (fun t => (x t).2.2.1 X) (x'.2.2.1 X) I t :=
  hasDerivWithinAt_comp_clm ((ContinuousLinearMap.proj X).comp
    ((ContinuousLinearMap.fst ℝ _ _).comp
      ((ContinuousLinearMap.snd ℝ ℝ _).comp (ContinuousLinearMap.snd ℝ ℝ _)))) hx

/-- Each pop-coordinate of a curve has, within `I`, the pop-coordinate of its derivative. -/
lemma hasDerivWithinAt_pop {x : ℝ → EB σ} {x' : EB σ} {I : Set ℝ} {t : ℝ}
    (hx : HasDerivWithinAt x x' I t) (X : σ) :
    HasDerivWithinAt (fun t => (x t).2.2.2 X) (x'.2.2.2 X) I t :=
  hasDerivWithinAt_comp_clm ((ContinuousLinearMap.proj X).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp
      ((ContinuousLinearMap.snd ℝ ℝ _).comp (ContinuousLinearMap.snd ℝ ℝ _)))) hx

/-- Chain rule for the edge defect along a curve, within a set of times `I`, when `ψ''` is the
derivative of `ψ'` at the current θ. -/
theorem hasDerivWithinAt_edgeDefect (N : CNet) (q : ℝ) {x : ℝ → EB σ} {x' : EB σ} {I : Set ℝ}
    {t : ℝ} (hψ' : HasDerivAt N.ψ' (N.ψ'' (x t).1) (x t).1) (hx : HasDerivWithinAt x x' I t) :
    HasDerivWithinAt (fun t => edgeDefect N q (x t)) (edgeDefectDeriv N q (x t) x') I t := by
  have hθ := hasDerivWithinAt_θ hx
  have hξ := hasDerivWithinAt_ξ hx
  have hd : HasDerivWithinAt (fun t => N.ψ' (x t).1) (N.ψ'' (x t).1 * x'.1) I t :=
    hψ'.comp_hasDerivWithinAt t hθ
  have hS : HasDerivWithinAt (fun t => N.phiS q (x t).1 (x t).2.1)
      (q * (x'.2.1 * N.ψ' (x t).1 + (x t).2.1 * (N.ψ'' (x t).1 * x'.1)) / N.ψ' 1) I t := by
    have := ((hξ.mul hd).const_mul q).div_const (N.ψ' 1)
    simpa [CNet.phiS, mul_assoc] using this
  have hsum : HasDerivWithinAt (fun t => ∑ X, (x t).2.2.1 X) (∑ X, x'.2.2.1 X) I t :=
    HasDerivWithinAt.fun_sum (fun X _ => hasDerivWithinAt_φ hx X)
  exact (hθ.sub hS).sub hsum

/-- Chain rule for the node total along a curve, within a set of times `I`, when `ψ'` is the
derivative of `ψ` at the current θ. -/
theorem hasDerivWithinAt_nodeTotal (N : CNet) (q : ℝ) {x : ℝ → EB σ} {x' : EB σ} {I : Set ℝ}
    {t : ℝ} (hψ : HasDerivAt N.ψ (N.ψ' (x t).1) (x t).1) (hx : HasDerivWithinAt x x' I t) :
    HasDerivWithinAt (fun t => nodeTotal N q (x t)) (nodeTotalDeriv N q (x t) x') I t := by
  have hθ := hasDerivWithinAt_θ hx
  have hξ := hasDerivWithinAt_ξ hx
  have hd : HasDerivWithinAt (fun t => N.ψ (x t).1) (N.ψ' (x t).1 * x'.1) I t :=
    hψ.comp_hasDerivWithinAt t hθ
  have hS : HasDerivWithinAt (fun t => N.susc q (x t).1 (x t).2.1)
      (q * (x'.2.1 * N.ψ (x t).1 + (x t).2.1 * (N.ψ' (x t).1 * x'.1))) I t := by
    have := (hξ.mul hd).const_mul q
    simpa [CNet.susc, mul_assoc] using this
  have hsum : HasDerivWithinAt (fun t => ∑ X, (x t).2.2.2 X) (∑ X, x'.2.2.2 X) I t :=
    HasDerivWithinAt.fun_sum (fun X _ => hasDerivWithinAt_pop hx X)
  exact hS.add hsum

/-- `edgeDefectDeriv N q u` is additive in the direction. -/
lemma edgeDefectDeriv_add (N : CNet) (q : ℝ) (u v w : EB σ) :
    edgeDefectDeriv N q u (v + w) = edgeDefectDeriv N q u v + edgeDefectDeriv N q u w := by
  simp only [edgeDefectDeriv, Prod.fst_add, Prod.snd_add, Pi.add_apply, Finset.sum_add_distrib]
  ring

/-- `nodeTotalDeriv N q u` is additive in the direction. -/
lemma nodeTotalDeriv_add (N : CNet) (q : ℝ) (u v w : EB σ) :
    nodeTotalDeriv N q u (v + w) = nodeTotalDeriv N q u v + nodeTotalDeriv N q u w := by
  simp only [nodeTotalDeriv, Prod.fst_add, Prod.snd_add, Pi.add_apply, Finset.sum_add_distrib]
  ring

/-- Per reaction, the edge defect changes only through removals. -/
lemma edgeDefectDeriv_ebField [DecidableEq σ] (N : CNet) (q : ℝ) (r : Rxn σ) (u : EB σ) :
    edgeDefectDeriv N q u (ebField N q r u) = r.removalRate u.2.2.1 := by
  obtain ⟨θ, ξ, φ, p⟩ := u
  cases r with
  | contact J X τ =>
      simp only [ebField, edgeDefectDeriv, Pi.sub_apply, Finset.sum_sub_distrib, sum_single,
        Rxn.removalRate]
      ring
  | exit Y ν =>
      simp only [ebField, edgeDefectDeriv, sum_single, Rxn.removalRate, CNet.phiS]
      ring
  | trans X Y a =>
      cases Y with
      | none =>
          simp only [ebField, edgeDefectDeriv, Pi.neg_apply, Finset.sum_neg_distrib, sum_single,
            Rxn.removalRate]
          ring
      | some Y =>
          simp only [ebField, edgeDefectDeriv, Pi.sub_apply, Finset.sum_sub_distrib, sum_single,
            Rxn.removalRate]
          ring

/-- Per reaction, the node total changes only through removals. -/
lemma nodeTotalDeriv_ebField [DecidableEq σ] (N : CNet) (q : ℝ) (r : Rxn σ) (u : EB σ) :
    nodeTotalDeriv N q u (ebField N q r u) = -r.removalRate u.2.2.2 := by
  obtain ⟨θ, ξ, φ, p⟩ := u
  cases r with
  | contact J X τ =>
      simp only [ebField, nodeTotalDeriv, sum_single, Rxn.removalRate]
      ring
  | exit Y ν =>
      simp only [ebField, nodeTotalDeriv, sum_single, Rxn.removalRate, CNet.susc]
      ring
  | trans X Y a =>
      cases Y with
      | none =>
          simp only [ebField, nodeTotalDeriv, Pi.neg_apply, Finset.sum_neg_distrib, sum_single,
            Rxn.removalRate]
          ring
      | some Y =>
          simp only [ebField, nodeTotalDeriv, Pi.sub_apply, Finset.sum_sub_distrib, sum_single,
            Rxn.removalRate]
          ring

omit [Fintype σ] in
/-- **A removal leaves θ unchanged**, for every species type `σ` (finite or not): for a removal
`X → ∅` at rate `a`, the θ-component of its EB field is 0. (The θ-conjunct of
`ebField_removal_row`, without its finiteness assumption.) -/
theorem ebField_removal_theta [DecidableEq σ] (N : CNet) (q : ℝ) (X : σ) (a : ℝ) (u : EB σ) :
    (ebField N q (.trans X none a) u).1 = 0 :=
  rfl

/-- **A removal keeps its edges in θ but takes them out of every φ class.** For a removal
`X → ∅` at rate `a`, the θ-component of its EB field is 0 and the φ-components sum to `−aφ_X`
(and the pop-components to `−a pop_X`). -/
theorem ebField_removal_row [DecidableEq σ] (N : CNet) (q : ℝ) (X : σ) (a : ℝ) (u : EB σ) :
    (ebField N q (.trans X none a) u).1 = 0 ∧
      ∑ Y, (ebField N q (.trans X none a) u).2.2.1 Y = -(a * u.2.2.1 X) ∧
      ∑ Y, (ebField N q (.trans X none a) u).2.2.2 Y = -(a * u.2.2.2 X) := by
  obtain ⟨θ, ξ, φ, p⟩ := u
  refine ⟨rfl, ?_, ?_⟩
  · simp only [ebField, Pi.neg_apply, Finset.sum_neg_distrib, sum_single]
  · simp only [ebField, Pi.neg_apply, Finset.sum_neg_distrib, sum_single]

/-- Per reaction, the edge defect changes only through removals: a reaction that is not a
removal `X → ∅` contributes 0 to `d/dt (θ − φ_S − Σ_X φ_X)`. -/
theorem edgeDefectDeriv_ebField_eq_zero [DecidableEq σ] (N : CNet) (q : ℝ) (r : Rxn σ)
    (hr : r.isRemoval = false) (u : EB σ) : edgeDefectDeriv N q u (ebField N q r u) = 0 := by
  rw [edgeDefectDeriv_ebField]
  cases r with
  | trans X Y a => cases Y <;> simp_all [Rxn.isRemoval, Rxn.removalRate]
  | _ => rfl

/-- Per reaction, the node total changes only through removals: a reaction that is not a
removal `X → ∅` contributes 0 to `d/dt (S + Σ_X pop_X)`. -/
theorem nodeTotalDeriv_ebField_eq_zero [DecidableEq σ] (N : CNet) (q : ℝ) (r : Rxn σ)
    (hr : r.isRemoval = false) (u : EB σ) : nodeTotalDeriv N q u (ebField N q r u) = 0 := by
  rw [nodeTotalDeriv_ebField]
  cases r with
  | trans X Y a => cases Y <;> simp_all [Rxn.isRemoval, Rxn.removalRate]
  | _ => simp [Rxn.removalRate]

/-- Along the EB field of a reaction list, the edge defect changes at the removal flux of φ. -/
lemma edgeDefectDeriv_lift [DecidableEq σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)) (u : EB σ) :
    edgeDefectDeriv N q u (lift N q rs u) = removalFlux rs u.2.2.1 := by
  induction rs with
  | nil =>
      simp [lift, removalFlux, edgeDefectDeriv]
  | cons r rs ih =>
      simp only [lift, removalFlux, List.map_cons, List.sum_cons] at ih ⊢
      rw [edgeDefectDeriv_add, ih, edgeDefectDeriv_ebField]

/-- Along the EB field of a reaction list, the node total changes at minus the removal flux of
pop. -/
lemma nodeTotalDeriv_lift [DecidableEq σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)) (u : EB σ) :
    nodeTotalDeriv N q u (lift N q rs u) = -removalFlux rs u.2.2.2 := by
  induction rs with
  | nil =>
      simp [lift, removalFlux, nodeTotalDeriv]
  | cons r rs ih =>
      simp only [lift, removalFlux, List.map_cons, List.sum_cons] at ih ⊢
      rw [nodeTotalDeriv_add, ih, nodeTotalDeriv_ebField]
      ring

/-- **Edge balance along EB solutions, with removals.** Let `x` solve the EB field of a T_EB
reaction list `rs` within a set of times `I` at the time `t` (`HasDerivWithinAt`), and let `ψ''`
be the derivative of `ψ'` at `θ(t)`. Then, within `I` at `t`,
`d/dt (θ − φ_S − Σ_X φ_X) = Σ_{(X → ∅, a) ∈ rs} a φ_X`. Removals `X → ∅` make the partner inert:
its edges keep `θ` but leave every φ class, so the defect grows. -/
theorem hasDerivWithinAt_edgeDefect_lift [DecidableEq σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ))
    {x : ℝ → EB σ} {I : Set ℝ} {t : ℝ} (hψ' : HasDerivAt N.ψ' (N.ψ'' (x t).1) (x t).1)
    (hx : HasDerivWithinAt x (lift N q rs (x t)) I t) :
    HasDerivWithinAt (fun t => edgeDefect N q (x t)) (removalFlux rs (x t).2.2.1) I t := by
  have h := hasDerivWithinAt_edgeDefect N q hψ' hx
  rwa [edgeDefectDeriv_lift] at h

/-- **Node balance along EB solutions, with removals.** Let `x` solve the EB field of a T_EB
reaction list `rs` within a set of times `I` at the time `t`, and let `ψ'` be the derivative of
`ψ` at `θ(t)`. Then, within `I` at `t`, `d/dt (S + Σ_X pop_X) = −Σ_{(X → ∅, a) ∈ rs} a pop_X`,
where `S = qξψ(θ)`. -/
theorem hasDerivWithinAt_nodeTotal_lift [DecidableEq σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ))
    {x : ℝ → EB σ} {I : Set ℝ} {t : ℝ} (hψ : HasDerivAt N.ψ (N.ψ' (x t).1) (x t).1)
    (hx : HasDerivWithinAt x (lift N q rs (x t)) I t) :
    HasDerivWithinAt (fun t => nodeTotal N q (x t)) (-removalFlux rs (x t).2.2.2) I t := by
  have h := hasDerivWithinAt_nodeTotal N q hψ hx
  rwa [nodeTotalDeriv_lift] at h

/-- The edge balance law for two-sided derivatives (`hasDerivWithinAt_edgeDefect_lift` with
`I = ℝ`). -/
theorem hasDerivAt_edgeDefect_lift [DecidableEq σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ))
    {x : ℝ → EB σ} {t : ℝ} (hψ' : HasDerivAt N.ψ' (N.ψ'' (x t).1) (x t).1)
    (hx : HasDerivAt x (lift N q rs (x t)) t) :
    HasDerivAt (fun t => edgeDefect N q (x t)) (removalFlux rs (x t).2.2.1) t := by
  rw [← hasDerivWithinAt_univ] at hx ⊢
  exact hasDerivWithinAt_edgeDefect_lift N q rs hψ' hx

/-- The node balance law for two-sided derivatives (`hasDerivWithinAt_nodeTotal_lift` with
`I = ℝ`). -/
theorem hasDerivAt_nodeTotal_lift [DecidableEq σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ))
    {x : ℝ → EB σ} {t : ℝ} (hψ : HasDerivAt N.ψ (N.ψ' (x t).1) (x t).1)
    (hx : HasDerivAt x (lift N q rs (x t)) t) :
    HasDerivAt (fun t => nodeTotal N q (x t)) (-removalFlux rs (x t).2.2.2) t := by
  rw [← hasDerivWithinAt_univ] at hx ⊢
  exact hasDerivWithinAt_nodeTotal_lift N q rs hψ hx

omit [Fintype σ] in
/-- A real function whose derivative within a convex set `I` vanishes at every point of `I` is
constant on `I`: `g t = g t₀` for all `t, t₀ ∈ I`. -/
lemma const_of_hasDerivWithinAt_zero {g : ℝ → ℝ} {I : Set ℝ} (hI : Convex ℝ I)
    (hg : ∀ t ∈ I, HasDerivWithinAt g 0 I t) {t₀ t : ℝ} (h₀ : t₀ ∈ I) (ht : t ∈ I) :
    g t = g t₀ := by
  have h := hI.norm_image_sub_le_of_norm_hasDerivWithin_le (f' := fun _ => (0 : ℝ)) (C := 0) hg
    (fun _ _ => by simp) h₀ ht
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at h
  exact h

omit [Fintype σ] in
/-- A real function with derivative 0 everywhere is constant. -/
lemma const_of_hasDerivAt_zero {g : ℝ → ℝ} (hg : ∀ t, HasDerivAt g 0 t) (t : ℝ) : g t = g 0 :=
  is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) t 0

/-- A reaction is an exit `s → Y`. -/
def Rxn.isExit : Rxn σ → Bool
  | .exit .. => true
  | _ => false

omit [Fintype σ] in
/-- Without exits the ξ-component of the EB field vanishes. -/
lemma lift_ξ_eq_zero [DecidableEq σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ))
    (hrs : ∀ r ∈ rs, r.isExit = false) (u : EB σ) : (lift N q rs u).2.1 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      have hr := hrs r (by simp)
      have h0 : (ebField N q r u).2.1 = 0 := by
        obtain ⟨θ, ξ, φ, p⟩ := u
        cases r with
        | contact J X τ => rfl
        | exit Y ν => simp [Rxn.isExit] at hr
        | trans X Y a => cases Y <;> rfl
      simp only [lift, List.map_cons, List.sum_cons, Prod.snd_add, Prod.fst_add] at ih ⊢
      rw [h0, ih (fun r' hr' => hrs r' (by simp [hr'])), add_zero]

/-- **ξ is constant along EB solutions of exit-free models.** Let `I` be a time interval (a
convex set of times) with `0 ∈ I`, and let `x` solve the EB field of a T_EB reaction list `rs`
that has no exit `s → Y` on `I` (`HasDerivWithinAt x (lift N q rs (x t)) I t` for `t ∈ I`).
Then `ξ(t) = ξ(0)` for every `t ∈ I`. No assumption on the degree data is needed. -/
theorem xi_const [DecidableEq σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ))
    (hrs : ∀ r ∈ rs, r.isExit = false) {I : Set ℝ} (hI : Convex ℝ I) (h0 : (0 : ℝ) ∈ I)
    {x : ℝ → EB σ} (hx : ∀ t ∈ I, HasDerivWithinAt x (lift N q rs (x t)) I t) :
    ∀ t ∈ I, (x t).2.1 = (x 0).2.1 := by
  have hd : ∀ t ∈ I, HasDerivWithinAt (fun t => (x t).2.1) 0 I t := by
    intro t ht
    have h := hasDerivWithinAt_ξ (hx t ht)
    rwa [lift_ξ_eq_zero N q rs hrs] at h
  exact fun t ht => const_of_hasDerivWithinAt_zero (g := fun t => (x t).2.1) hI hd h0 ht

omit [Fintype σ] in
/-- **ξ is constant along EB solutions of exit-free models, for any species type.** As
`xi_const`, without finiteness of the species type `σ` (the φ and pop coordinates then carry the
product topology): let `I` be a convex set of times with `0 ∈ I`, and let `x` solve the EB field
of a T_EB reaction list `rs` that has no exit `s → Y` on `I`. Then `ξ(t) = ξ(0)` for every
`t ∈ I`. -/
theorem xi_const_any [DecidableEq σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ))
    (hrs : ∀ r ∈ rs, r.isExit = false) {I : Set ℝ} (hI : Convex ℝ I) (h0 : (0 : ℝ) ∈ I)
    {x : ℝ → EB σ} (hx : ∀ t ∈ I, HasDerivWithinAt x (lift N q rs (x t)) I t) :
    ∀ t ∈ I, (x t).2.1 = (x 0).2.1 := by
  have hd : ∀ t ∈ I, HasDerivWithinAt (fun t => (x t).2.1) 0 I t := by
    intro t ht
    have h := hasDerivWithinAt_ξ_any (hx t ht)
    rwa [lift_ξ_eq_zero N q rs hrs] at h
  exact fun t ht => const_of_hasDerivWithinAt_zero (g := fun t => (x t).2.1) hI hd h0 ht

/-- **Edge conservation θ = φ_S + Σ_X φ_X is invariant along removal-free EB solutions.**

Design statement (DESIGN_NetworkEpiCore.md §D.4, Evidence): "The exit terms were checked by hand.
Conservation θ = φ_S + Σφ_X holds."; amended by §M.1: "For removal-free T_EB models (no
`X → ∅`), θ = φ_S + Σφ_X is invariant along every solution on a time interval: if it holds at
t = 0 it holds at every time of the interval. In particular, when ψ'(1) ≠ 0, it holds along
solutions from the design's initial condition θ(0) = ξ(0) = 1, Σφ_X(0) = 1 − q."

Lean statement: let `N` be a configuration network (no hypothesis on `ψ'(1)`), `q` a seed factor
and `rs` a T_EB reaction list with **no removal `X → ∅`**. Let `I` be a convex set of times with
`0 ∈ I`, and let `x : ℝ → EB σ` solve the EB field of `rs` on `I`
(`HasDerivWithinAt x (lift N q rs (x t)) I t` for every `t ∈ I`), with `ψ''` the derivative of
`ψ'` at every visited `θ(t)`, `t ∈ I`. If `θ(0) = φ_S(0) + Σ_X φ_X(0)` (with
`φ_S = qξψ'(θ)/ψ'(1)`), then `θ(t) = φ_S(t) + Σ_X φ_X(t)` for every `t ∈ I`. -/
theorem conservation_invariant [DecidableEq σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ))
    (hrs : ∀ r ∈ rs, r.isRemoval = false) {I : Set ℝ} (hI : Convex ℝ I) (h0 : (0 : ℝ) ∈ I)
    {x : ℝ → EB σ} (hx : ∀ t ∈ I, HasDerivWithinAt x (lift N q rs (x t)) I t)
    (hψ' : ∀ t ∈ I, HasDerivAt N.ψ' (N.ψ'' (x t).1) (x t).1)
    (hrel : (x 0).1 = N.phiS q (x 0).1 (x 0).2.1 + ∑ X, (x 0).2.2.1 X) :
    ∀ t ∈ I, (x t).1 = N.phiS q (x t).1 (x t).2.1 + ∑ X, (x t).2.2.1 X := by
  have hd : ∀ t ∈ I, HasDerivWithinAt (fun t => edgeDefect N q (x t)) 0 I t := by
    intro t ht
    have h := hasDerivWithinAt_edgeDefect_lift N q rs (hψ' t ht) (hx t ht)
    rwa [removalFlux_eq_zero rs hrs] at h
  have e0 : edgeDefect N q (x 0) = 0 := by
    simp only [edgeDefect]
    linarith
  intro t ht
  have : edgeDefect N q (x t) = edgeDefect N q (x 0) :=
    const_of_hasDerivWithinAt_zero (g := fun t => edgeDefect N q (x t)) hI hd h0 ht
  rw [e0] at this
  simp only [edgeDefect] at this
  linarith

/-- **Edge conservation θ = φ_S + Σ_X φ_X.**

Design statement (DESIGN_NetworkEpiCore.md §D.4, Evidence): "The exit terms were checked by hand.
Conservation θ = φ_S + Σφ_X holds."; §D.7, L3: "`conservation`".

Lean statement: let `N` be a configuration network with `ψ'(1) ≠ 0`, let `q` be the seed factor,
and let `rs` be a T_EB reaction list (contacts, exits and progressions `X → Y`) that contains
**no removal `X → ∅`**. Let `I` be a time interval, i.e. any convex set of times with `0 ∈ I`
(for example `(a, b)` with `a < 0 < b`, `[0, T)`, `[0, ∞)` or `ℝ`), and let `x : ℝ → EB σ` solve
the EB field of `rs` on `I`: `HasDerivWithinAt x (lift N q rs (x t)) I t` for every `t ∈ I`
(one-sided at end points of `I` in `I`; implied by `HasDerivAt` at every `t ∈ I`). Assume that
`ψ''` is the derivative of `ψ'` at every value `θ(t)`, `t ∈ I`, that the solution visits, and
that `x(0)` satisfies `θ(0) = 1`, `ξ(0) = 1` and `Σ_X φ_X(0) = 1 − q` (the part of the design's
initial condition that is used; it follows from `φ_X(0) = ρ_X` with `q = 1 − Σρ`). Then
`θ(t) = φ_S(t) + Σ_X φ_X(t)` with `φ_S = qξψ'(θ)/ψ'(1)` for every `t ∈ I`.

Scope: global solutions are not required, and need not exist (numerically, EB SEIR on Poisson(5)
with τ = 1/6, σ = 1/3, γ = 1/4 and φ_I(0) = 0.01 blows up backward at t ≈ −7.33). Forward
solutions on `[0, T)` and local solutions on `(−ε, ε)` are covered, and `NEP.conservation_local`
proves that a local solution meeting all the hypotheses exists. The no-removal hypothesis is
necessary: with removals `hasDerivWithinAt_edgeDefect_lift` gives
`d/dt (θ − φ_S − Σφ) = Σ a φ_X` instead. -/
theorem conservation [DecidableEq σ] (N : CNet) (q : ℝ) (hm : N.ψ' 1 ≠ 0) (rs : List (Rxn σ))
    (hrs : ∀ r ∈ rs, r.isRemoval = false) {I : Set ℝ} (hI : Convex ℝ I) (h0 : (0 : ℝ) ∈ I)
    {x : ℝ → EB σ} (hx : ∀ t ∈ I, HasDerivWithinAt x (lift N q rs (x t)) I t)
    (hψ' : ∀ t ∈ I, HasDerivAt N.ψ' (N.ψ'' (x t).1) (x t).1)
    (hθ0 : (x 0).1 = 1) (hξ0 : (x 0).2.1 = 1) (hφ0 : ∑ X, (x 0).2.2.1 X = 1 - q) :
    ∀ t ∈ I, (x t).1 = N.phiS q (x t).1 (x t).2.1 + ∑ X, (x t).2.2.1 X := by
  have hd : ∀ t ∈ I, HasDerivWithinAt (fun t => edgeDefect N q (x t)) 0 I t := by
    intro t ht
    have h := hasDerivWithinAt_edgeDefect_lift N q rs (hψ' t ht) (hx t ht)
    rwa [removalFlux_eq_zero rs hrs] at h
  have e0 : edgeDefect N q (x 0) = 0 := by
    simp only [edgeDefect, CNet.phiS, hθ0, hξ0, hφ0]
    field_simp
    ring
  intro t ht
  have : edgeDefect N q (x t) = edgeDefect N q (x 0) :=
    const_of_hasDerivWithinAt_zero (g := fun t => edgeDefect N q (x t)) hI hd h0 ht
  rw [e0] at this
  simp only [edgeDefect] at this
  linarith

/-- **Node conservation S + Σ_X pop_X = 1.** Let `N` be a configuration network with
`ψ(1) = 1`, and let `rs` be a T_EB reaction list with no removal `X → ∅`. Let `I` be a time
interval (a convex set of times) with `0 ∈ I` and let `x` solve the EB field of `rs` on `I`
(`HasDerivWithinAt x (lift N q rs (x t)) I t` for `t ∈ I`), with `ψ'` the derivative of `ψ` at
every visited `θ(t)`, `t ∈ I`, and with `θ(0) = 1`, `ξ(0) = 1` and `Σ_X pop_X(0) = 1 − q`. Then
`qξ(t)ψ(θ(t)) + Σ_X pop_X(t) = 1` for every `t ∈ I`. -/
theorem node_conservation [DecidableEq σ] (N : CNet) (q : ℝ) (h1 : N.ψ 1 = 1)
    (rs : List (Rxn σ)) (hrs : ∀ r ∈ rs, r.isRemoval = false) {I : Set ℝ} (hI : Convex ℝ I)
    (h0 : (0 : ℝ) ∈ I) {x : ℝ → EB σ} (hx : ∀ t ∈ I, HasDerivWithinAt x (lift N q rs (x t)) I t)
    (hψ : ∀ t ∈ I, HasDerivAt N.ψ (N.ψ' (x t).1) (x t).1)
    (hθ0 : (x 0).1 = 1) (hξ0 : (x 0).2.1 = 1) (hp0 : ∑ X, (x 0).2.2.2 X = 1 - q) :
    ∀ t ∈ I, N.susc q (x t).1 (x t).2.1 + ∑ X, (x t).2.2.2 X = 1 := by
  have hd : ∀ t ∈ I, HasDerivWithinAt (fun t => nodeTotal N q (x t)) 0 I t := by
    intro t ht
    have h := hasDerivWithinAt_nodeTotal_lift N q rs (hψ t ht) (hx t ht)
    rwa [removalFlux_eq_zero rs hrs, neg_zero] at h
  have e0 : nodeTotal N q (x 0) = 1 := by
    simp only [nodeTotal, CNet.susc, hθ0, hξ0, hp0, h1]
    ring
  intro t ht
  have : nodeTotal N q (x t) = nodeTotal N q (x 0) :=
    const_of_hasDerivWithinAt_zero (g := fun t => nodeTotal N q (x t)) hI hd h0 ht
  rw [e0] at this
  exact this

end Conservation

end NEP
