import NetworkEpi.Semantics.EB

/-!
# L3: mass-action (MA) semantics of T_net reactions

DESIGN_NetworkEpiCore.md §D.4, row **MA** ("Open(Petri) | x_X | total | **yes**
(Baez–Pollard 2017)") and §D.7 L3 (`maField`). This module covers the T_net reactions of `NRxn σ`
(one susceptible species `s`, node species `σ`) in coordinates `(S, x)`, where `S` is the
susceptible fraction and `x X` the fraction in node species `X`. Mass action is total on
`NRxn σ`, so no admissibility condition is needed. The rate of each reaction is its written
constant times the product of the reactant fractions (per DESIGN §D.2, a rate convention `c_λ`
must be applied to the syntax before `maField` when the constants are per-contact rates).
-/

open scoped BigOperators

namespace NEP

/-- Mass-action coordinates `(S, x)` over node species `σ`. -/
abbrev MA (σ : Type) := ℝ × (σ → ℝ)

variable {σ σ' σA σB : Type}

section Field
variable [DecidableEq σ]

/-- The mass-action field of one T_net reaction, with flux `k·Π(reactant fractions)`:
* `contact J X k` (s + J → X + J): flux `k S x_J`, `S −= flux`, `x_X += flux`;
* `exit Y ν` (s → Y): flux `ν S`, `S −= flux`, `x_Y += flux`;
* `trans X (some Y) a` (X → Y): flux `a x_X`, `x_X −= flux`, `x_Y += flux`;
* `trans X none a` (X → ∅): `x_X −= a x_X`;
* `resus X a` (X → s): flux `a x_X`, `x_X −= flux`, `S += flux`;
* `nodeContact X J Y k` (X + J → Y + J): flux `k x_X x_J` (`x_J = S` when `J = none`),
  `x_X −= flux`, `x_Y += flux`. -/
noncomputable def maField : NRxn σ → MA σ → MA σ
  | .contact J X k, (S, x) => (-(k * S * x J), Pi.single X (k * S * x J))
  | .exit Y ν, (S, _) => (-(ν * S), Pi.single Y (ν * S))
  | .trans X none a, (_, x) => (0, -Pi.single X (a * x X))
  | .trans X (some Y) a, (_, x) => (0, Pi.single Y (a * x X) - Pi.single X (a * x X))
  | .resus X a, (_, x) => (a * x X, -Pi.single X (a * x X))
  | .nodeContact X J Y k, (S, x) =>
      (0, Pi.single Y (k * x X * J.elim S x) - Pi.single X (k * x X * J.elim S x))

/-- The mass-action vector field of a T_net reaction list: the sum of the per-reaction fields. -/
noncomputable def maLift (rs : List (NRxn σ)) (u : MA σ) : MA σ :=
  (rs.map fun r => maField r u).sum

/-- The mass-action model of `rs` as an object of `DynSys`. -/
noncomputable def maSys [Fintype σ] (rs : List (NRxn σ)) : DynSys where
  V := MA σ
  F := maLift rs

/-- **H1′ for mass action, part 1: the MA lift is additive in the reaction list.**

Design statement (DESIGN_NetworkEpiCore.md §D.6): "H1′ same for MA, IB, Stoch | yes | same
argument"; §D.4, table row MA, column "Strict under gluing?": "**yes** (Baez–Pollard 2017)".

Lean statement: for all T_net reaction lists `rs`, `rs'` (single susceptible species) and every
state `u = (S, x)`, the mass-action field of `rs ++ rs'` at `u` is the sum of the mass-action
fields of `rs` and of `rs'` at `u`. -/
theorem maLift_append (rs rs' : List (NRxn σ)) (u : MA σ) :
    maLift (rs ++ rs') u = maLift rs u + maLift rs' u := by
  simp [maLift, List.map_append, List.sum_append]

end Field

section Push
variable [Fintype σ] [DecidableEq σ']

/-- Pushforward of MA coordinates along a species map: `S` is kept, `x` is summed over fibres. -/
def pushMA (f : σ → σ') (u : MA σ) : MA σ' := (u.1, push f u.2)

/-- The pushforward of MA coordinates is additive. -/
lemma pushMA_add (f : σ → σ') (u v : MA σ) : pushMA f (u + v) = pushMA f u + pushMA f v := by
  obtain ⟨S, x⟩ := u
  obtain ⟨S', x'⟩ := v
  simp only [pushMA, Prod.mk_add_mk, push_add]

/-- The pushforward of the zero MA vector is zero. -/
lemma pushMA_zero (f : σ → σ') : pushMA f (0 : MA σ) = 0 := by
  simp only [pushMA, Prod.fst_zero, Prod.snd_zero, push_zero, Prod.mk_zero_zero]

end Push

/-- Pullback of MA coordinates along a species map: `S` is kept, `x` is precomposed with `f`. -/
def pullMA (f : σ → σ') (u : MA σ') : MA σ := (u.1, u.2 ∘ f)

section Naturality
variable [Fintype σ] [DecidableEq σ] [DecidableEq σ']

omit [Fintype σ] [DecidableEq σ] [DecidableEq σ'] in
/-- Reading a catalyst density after relabelling: `J = none` (the susceptible species) gives
`S`, `J = some X` gives `x (f X)`. -/
lemma elim_map (f : σ → σ') (J : Option σ) (S : ℝ) (x : σ' → ℝ) :
    (J.map f).elim S x = J.elim S (x ∘ f) := by
  cases J <;> rfl

/-- Naturality of the per-reaction mass-action field in species maps: the field of `r.map f` at
`u` is the pushforward of the field of `r` at `pullMA f u`. -/
theorem maField_map (f : σ → σ') (r : NRxn σ) (u : MA σ') :
    maField (r.map f) u = pushMA f (maField r (pullMA f u)) := by
  obtain ⟨S, x⟩ := u
  cases r with
  | contact J X k =>
      simp only [NRxn.map, maField, pushMA, pullMA, Function.comp, push_single]
  | exit Y ν =>
      simp only [NRxn.map, maField, pushMA, pullMA, push_single]
  | trans X Y a =>
      cases Y <;>
        simp only [NRxn.map, Option.map, maField, pushMA, pullMA, Function.comp, push_sub,
          push_neg, push_single]
  | resus X a =>
      simp only [NRxn.map, maField, pushMA, pullMA, Function.comp, push_neg, push_single]
  | nodeContact X J Y k =>
      simp only [NRxn.map, maField, pushMA, pullMA, elim_map, Function.comp, push_sub,
        push_single]

/-- **H1′ for mass action, part 2: the MA lift is natural in species maps.**

Design statement (DESIGN_NetworkEpiCore.md §D.6): "H1′ same for MA, IB, Stoch | yes | same
argument" (the argument of H1: "local per-reaction fields").

Lean statement: for every species map `f : σ → σ'` (σ finite), every T_net reaction list `rs`
over `σ` and every state `u = (S, x)` over `σ'`, the mass-action field of `rs.map (NRxn.map f)`
at `u` equals the pushforward along `f` (S kept, x summed over the fibres of `f`) of the
mass-action field of `rs` at `(S, x ∘ f)`. -/
theorem maLift_map (f : σ → σ') (rs : List (NRxn σ)) (u : MA σ') :
    maLift (rs.map (NRxn.map f)) u = pushMA f (maLift rs (pullMA f u)) := by
  induction rs with
  | nil => simp only [maLift, List.map_nil, List.sum_nil, pushMA_zero]
  | cons r rs ih =>
      simp only [maLift, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih, maField_map, pushMA_add]

end Naturality

/-- **H1′ for mass action: the MA lift is strict under gluing.**

Design statement (DESIGN_NetworkEpiCore.md §D.6): "H1′ same for MA, IB, Stoch | yes | same
argument", where H1 is "EB(glue(A,B)) = glue(EB A, EB B)"; §D.4, table row MA, column "Strict
under gluing?": "**yes** (Baez–Pollard 2017)"; §D.3 (open systems): "composition identifies
ported coordinates and **adds** vector fields".

Lean statement: let `f : σA → σ` and `g : σB → σ` be a cospan of finite species types (the
susceptible species is glued to itself). For all T_net reaction lists `A` over `σA` and `B` over
`σB` and every state `u = (S, x)` over `σ`, the mass-action field of the glued list
`A.map f ++ B.map g` at `u` equals the pushforward along `f` of the mass-action field of `A` at
`(S, x ∘ f)` plus the pushforward along `g` of the mass-action field of `B` at `(S, x ∘ g)`.

Scope: of the design's "H1′ same for MA, IB, Stoch", only the mass-action case is formalised;
the individual-based (IB) and stochastic semantics are not part of this library. -/
theorem maLift_glue [DecidableEq σ] [Fintype σA] [Fintype σB] [DecidableEq σA] [DecidableEq σB]
    (f : σA → σ) (g : σB → σ) (A : List (NRxn σA)) (B : List (NRxn σB)) (u : MA σ) :
    maLift (A.map (NRxn.map f) ++ B.map (NRxn.map g)) u =
      pushMA f (maLift A (pullMA f u)) + pushMA g (maLift B (pullMA g u)) := by
  rw [maLift_append, maLift_map, maLift_map]

end NEP
