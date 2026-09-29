# DataTypes — group `SemanticsMA`

Blind-safe vocabulary for shadow authors of group `SemanticsMA` (SA-PASS). It lists the Lean imports, the
data types (structures and inductives with their fields) and the operations under test as **opaque
signatures with their docstrings only**. It contains no theorem statements, no proofs, no definition
bodies and no instance bodies. Where a docstring spells out a formula, that formula is the author's
*intent text*, not a guarantee about the body. Claim texts: `Alignment/claims_blind.yaml` (group
`SemanticsMA`).

Trusted module under test: `NetworkEpi.Semantics.MA` (file `NetworkEpi/Semantics/MA.lean`). Everything is in namespace `NEP`
(write `open NEP`). Numbers are real (`ℝ`) unless stated.

## (a) Imports

```lean
import NetworkEpi.Semantics.MA   -- imports NetworkEpi.Semantics.EB (for `push`)
open NEP
```

## (b)–(c) Data types and operations under test

### From `NetworkEpi.Semantics.MA` (mass action on T_net)

```lean
/-- Mass-action coordinates `(S, x)` over node species `σ`. -/
abbrev MA (σ : Type) := ℝ × (σ → ℝ)
-- access: for u : MA σ, S = u.1 (susceptible fraction), x = u.2 (fraction in each node species)
```

| signature (opaque) | docstring |
|---|---|
| `maField {σ : Type} [DecidableEq σ] : NRxn σ → MA σ → MA σ` | The mass-action field of one T_net reaction, with flux `k·Π(reactant fractions)`: `contact J X k` (s + J → X + J): flux `k S x_J`, `S −= flux`, `x_X += flux`; `exit Y ν` (s → Y): flux `ν S`, `S −= flux`, `x_Y += flux`; `trans X (some Y) a` (X → Y): flux `a x_X`, `x_X −= flux`, `x_Y += flux`; `trans X none a` (X → ∅): `x_X −= a x_X`; `resus X a` (X → s): flux `a x_X`, `x_X −= flux`, `S += flux`; `nodeContact X J Y k` (X + J → Y + J): flux `k x_X x_J` (`x_J = S` when `J = none`), `x_X −= flux`, `x_Y += flux`. |
| `maLift {σ : Type} [DecidableEq σ] (rs : List (NRxn σ)) (u : MA σ) : MA σ` | The mass-action vector field of a T_net reaction list: the sum of the per-reaction fields. |
| `maSys {σ : Type} [DecidableEq σ] [Fintype σ] (rs : List (NRxn σ)) : DynSys` | The mass-action model of `rs` as an object of `DynSys`. |
| `pushMA {σ σ' : Type} [Fintype σ] [DecidableEq σ'] (f : σ → σ') (u : MA σ) : MA σ'` | Pushforward of MA coordinates along a species map: `S` is kept, `x` is summed over fibres. |
| `pullMA {σ σ' : Type} (f : σ → σ') (u : MA σ') : MA σ` | Pullback of MA coordinates along a species map: `S` is kept, `x` is precomposed with `f`. |

Module header: mass action is total on `NRxn σ` (no admissibility condition); the rate of each
reaction is its written constant times the product of the reactant fractions (per DESIGN §D.2, a
rate convention `c_λ` must be applied to the syntax before `maField` when the constants are
per-contact rates). The library has **no** individual-based (IB) or stochastic (Stoch) semantics.

### From `NetworkEpi.Syntax.Rxn` (typed reaction syntax, one implicit susceptible species `s`)

```lean
/-- T_EB reactions over node species `σ` (the susceptible species `s` is implicit):
* `contact J X τ` is `s + J → X + J` at per-contact rate `τ` (DESIGN §0: "τ is always a
  per-contact (per-edge) rate");
* `exit Y ν` is `s → Y` at rate `ν` (for example vaccination);
* `trans X (some Y) a` is `X → Y` and `trans X none a` is `X → ∅`, at rate `a`. -/
inductive Rxn (σ : Type) where
  | contact (J X : σ) (τ : ℝ)       -- s + J → X + J at per-contact rate τ
  | exit (Y : σ) (ν : ℝ)            -- s → Y at rate ν
  | trans (X : σ) (Y : Option σ) (a : ℝ)   -- X → Y (or X → ∅ when Y = none) at rate a

/-- T_net reactions over node species `σ` (single susceptible species `s`): `NRxn σ` has the
T_EB constructors of `Rxn σ` and adds
* `resus X a`: `X → s` at rate `a` (§B.2 type `:resus`, e.g. SIS `I → S`, SIRS `R → S`);
* `nodeContact X J Y τ`: `X + J → Y + J` at rate `τ`, with recipient `X` a node species and
  catalyst `J` (`J = none` means the catalyst is `s`) (§B.2 type `:node_contact`). -/
inductive NRxn (σ : Type) where
  | contact (J X : σ) (τ : ℝ)
  | exit (Y : σ) (ν : ℝ)
  | trans (X : σ) (Y : Option σ) (a : ℝ)
  | resus (X : σ) (a : ℝ)                          -- X → s at rate a
  | nodeContact (X : σ) (J : Option σ) (Y : σ) (τ : ℝ)   -- X + J → Y + J; J = none is s

/-- The transition types of the theory T_net that `NRxn` represents (DESIGN §B.2). -/
inductive TNet where
  | contact | exit | progress | remove | resus | nodeContact
  deriving DecidableEq, Repr
```

| signature (opaque) | docstring |
|---|---|
| `TNet.inTEB : TNet → Bool` | Membership of a T_net type in the sub-theory T_EB = {contact, exit, progress, remove}. |
| `NRxn.type {σ : Type} : NRxn σ → TNet` | The typing of a T_net reaction (DESIGN §B.2). (Module header table: `contact` ↦ `:contact`, `exit` ↦ `:exit`, `trans X (some Y)` ↦ `:progress`, `trans X none` ↦ `:remove`, `resus` ↦ `:resus`, `nodeContact` ↦ `:node_contact`.) |
| `Rxn.toNRxn {σ : Type} : Rxn σ → NRxn σ` | The inclusion of T_EB syntax into T_net syntax. |
| `NRxn.toRxn? {σ : Type} : NRxn σ → Option (Rxn σ)` | The partial inverse of `Rxn.toNRxn`: `some r` on T_EB reactions, `none` otherwise. |
| `NRxn.EBAdmissible {σ : Type} (r : NRxn σ) : Prop` | A T_net reaction is *EB-admissible* if it is one of the T_EB types contact, exit, progress or remove (DESIGN §B.2: EB is defined on Petri/T_EB). |
| `instance NRxn.decEBAdmissible {σ : Type} : DecidablePred (NRxn.EBAdmissible (σ := σ))` | EB-admissibility is decidable. |
| `NRxn.EBAdmissibleList {σ : Type} (rs : List (NRxn σ)) : Prop` | A reaction list is EB-admissible if every reaction is. |
| `instance NRxn.decEBAdmissibleList {σ : Type} (rs : List (NRxn σ)) : Decidable (NRxn.EBAdmissibleList rs)` | EB-admissibility of a reaction list is decidable. |
| `Rxn.map {σ σ' : Type} (f : σ → σ') : Rxn σ → Rxn σ'` | Relabel the node species of a T_EB reaction along `f` (DESIGN §D.1: "Morphisms of syntax are type-preserving species maps that carry reactions to reactions"). Gluing species along a cospan is relabelling along the cospan legs. |
| `NRxn.map {σ σ' : Type} (f : σ → σ') : NRxn σ → NRxn σ'` | Relabel the node species of a T_net reaction along `f`. |
| `Rxn.scaleContacts {σ : Type} (κ : ℝ) : Rxn σ → Rxn σ` | The rate convention `c_κ`: multiply every contact rate by `κ`, leaving exits and transitions unchanged (DESIGN §D.5 M1 uses `c_κ` for the well-mixed unit, M3 uses `c_μ`). |

### From `NetworkEpi.Dyn.Basic` (category of vector fields)

```lean
/-- An object of the design's category **Dyn** (DESIGN §D.3), generalised: a real normed space
`V` with a vector field `F : V → V`. The ODE is `u̇ = F u`. -/
structure DynSys where
  V : Type                      -- the state space
  [ng : NormedAddCommGroup V]
  [ns : NormedSpace ℝ V]
  F : V → V                     -- the vector field
-- `DynSys.ng` and `DynSys.ns` are instances, so `A.V` is a real normed space for `A : DynSys`.

/-- A morphism of `DynSys` (a *semiconjugacy*, DESIGN §D.3): a differentiable map `π` with
`Dπ(u)·F(u) = G(π(u))` for every `u`. -/
@[ext] structure Semiconj (A B : DynSys) where
  π : A.V → B.V                                   -- the underlying map of state spaces
  diff : Differentiable ℝ π                       -- `π` is differentiable everywhere
  comm : ∀ u, fderiv ℝ π u (A.F u) = B.F (π u)    -- the semiconjugacy identity

/-- A *local semiconjugacy on `U`* (DESIGN §D.3, "Local version `SemiconjOn U`"): a map
`π : A.V → B.V` that is differentiable at every point of `U` and satisfies
`Dπ(u)·F(u) = G(π(u))` for every `u ∈ U`. The design's use is an open `U` such as
`{ψ(θ) ≠ 0, ψ'(θ) ≠ 0}`; openness is not required here because differentiability is asked for
at each point of `U`. -/
structure SemiconjOn (A B : DynSys) (U : Set A.V) where
  π : A.V → B.V
  diff : ∀ u ∈ U, DifferentiableAt ℝ π u
  comm : ∀ u ∈ U, fderiv ℝ π u (A.F u) = B.F (π u)
```

| signature (opaque) | docstring |
|---|---|
| `IsSemiconj (A B : DynSys) (π : A.V → B.V) : Prop` | `IsSemiconj A B π`: the map `π : A.V → B.V` is differentiable and carries the vector field of `A` to that of `B`, i.e. `Dπ(u)·F(u) = G(π(u))` for every `u` (DESIGN §D.3). |
| `IsSemiconjOn (A B : DynSys) (U : Set A.V) (π : A.V → B.V) : Prop` | `IsSemiconjOn A B U π`: `π` is differentiable at every point of `U` and `Dπ(u)·F(u) = G(π(u))` for every `u ∈ U`. |
| `Semiconj.ofIsSemiconj {A B : DynSys} (π : A.V → B.V) (h : IsSemiconj A B π) : Semiconj A B` | Bundle a map satisfying `IsSemiconj` as a morphism. |
| `Semiconj.id (A : DynSys) : Semiconj A A` | The identity semiconjugacy. |
| `Semiconj.comp {A B C : DynSys} (f : Semiconj A B) (g : Semiconj B C) : Semiconj A C` | Composition of semiconjugacies, `(f ≫ g).π = g.π ∘ f.π`; the identity holds by the chain rule. |
| `instance dynCategory : CategoryTheory.Category DynSys` | **The category `DynSys`** (DESIGN §D.3: "[L] `instance : Category DynSys`"). Objects are `DynSys`, morphisms `A ⟶ B` are `Semiconj A B`, the identity is `id` and composition is composition of maps. |
| `SemiconjOn.ofIsSemiconjOn {A B : DynSys} {U : Set A.V} (π : A.V → B.V) (h : IsSemiconjOn A B U π) : SemiconjOn A B U` | Bundle a map satisfying `IsSemiconjOn` as a local semiconjugacy. |
| `Semiconj.toSemiconjOn {A B : DynSys} (m : Semiconj A B) (U : Set A.V) : SemiconjOn A B U` | A global semiconjugacy is a local one on every set. |
| `SemiconjOn.mono {A B : DynSys} {U U' : Set A.V} (m : SemiconjOn A B U) (h : U' ⊆ U) : SemiconjOn A B U'` | Restricting a local semiconjugacy to a smaller set. |
| `SemiconjOn.comp {A B C : DynSys} {U : Set A.V} {W : Set B.V} (f : SemiconjOn A B U) (g : SemiconjOn B C W) : SemiconjOn A C (U ∩ f.π ⁻¹' W)` | Composition of local semiconjugacies: `g ∘ f` is a local semiconjugacy on the set of points of `U` that `f` sends into `W`. |
| `DynSys.restrict (A : DynSys) (p₀ : A.V) (W : Submodule ℝ A.V) (hW : ∀ w ∈ W, A.F (p₀ + w) ∈ W) : DynSys` | The *restriction* of `A` to the affine subspace `p₀ + W`, in the chart `w ↦ p₀ + w` (DESIGN §D.3: "The inclusion of an invariant subsystem is a restriction"). The hypothesis `hW` says that `F` is tangent to `p₀ + W`: `F(p₀ + w) ∈ W` for every `w ∈ W`. The restricted system lives on `W` with vector field `w ↦ F(p₀ + w)`. With `p₀ = 0` this is the restriction to an invariant linear subspace. |
| `DynSys.restrictIncl (A : DynSys) (p₀ : A.V) (W : Submodule ℝ A.V) : ↥W → A.V` | The chart of the restriction, `w ↦ p₀ + w`. |
| `invariantIncl (A : DynSys) (p₀ : A.V) (W : Submodule ℝ A.V) (hW : ∀ w ∈ W, A.F (p₀ + w) ∈ W) : A.restrict p₀ W hW ⟶ A` | The restriction morphism `(W, F\|_W) ⟶ A`. |

### Also used from `NetworkEpi.Semantics.EB`

| signature (opaque) | docstring |
|---|---|
| `push {σ σ' : Type} [Fintype σ] [DecidableEq σ'] (f : σ → σ') (v : σ → ℝ) : σ' → ℝ` | Pushforward of species-indexed coordinates along a species map `f`: the value at `y` is the sum over the fibre `f⁻¹(y)`. |

## (d) What is not defined (usage notes)

* There is **no** Lean definition of the design's category **Dyn** (finite-dimensional state space,
  C¹ field, C¹ morphisms); `DynSys` is more general (any real normed space, any function `F`,
  morphisms differentiable everywhere). A claim about Dyn has to be phrased with `DynSys` plus
  explicit `FiniteDimensional ℝ A.V` / `ContDiff ℝ 1` conditions.
* There is no predicate "is a solution": spell out `HasDerivAt x (A.F (x t)) t` or
  `HasDerivWithinAt x (A.F (x t)) I t` for the times `t` concerned.
* Petri nets, open systems, decorated cospans and functors between categories of models are **not**
  formalised. Gluing of models is expressed on the syntax: relabel two reaction lists along the legs
  `f : σA → σ`, `g : σB → σ` of a cospan (`List.map (Rxn.map f)`) and concatenate them (`++`).

## (e) Mathlib notions a faithful formalisation may need

* `Option.elim` (`J.elim S x` is `S` for `J = none` and `x X` for `J = some X`), `Option.map`.

* Calculus: `HasDerivAt`, `HasDerivWithinAt`, `deriv`, `fderiv`, `HasFDerivAt`, `Differentiable`,
  `DifferentiableAt`, `ContDiff`, `ContDiffAt` (smoothness index `n : WithTop ℕ∞`; in current Mathlib
  `(⊤ : WithTop ℕ∞)` is `ω`, analytic, and `∞` is `((⊤ : ℕ∞) : WithTop ℕ∞)`; `open scoped ContDiff`
  for the notations), `ContinuousLinearMap` (`→L[ℝ]`), `Convex ℝ I`, `Set.Ioo`, `Set.Ici`, `Set.univ`.
* Filters: `Filter.Eventually`, `nhds` (`𝓝`, `open Topology`).
* Finite sums over species: `Finset.univ`, `∑ X, f X` (needs `[Fintype σ]`), `Pi.single X c`.
