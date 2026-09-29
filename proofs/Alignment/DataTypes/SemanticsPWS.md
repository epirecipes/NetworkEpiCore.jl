# DataTypes — group `SemanticsPWS`

Blind-safe vocabulary for shadow authors of group `SemanticsPWS` (SA-PASS). It lists the Lean imports, the
data types (structures and inductives with their fields) and the operations under test as **opaque
signatures with their docstrings only**. It contains no theorem statements, no proofs, no definition
bodies and no instance bodies. Where a docstring spells out a formula, that formula is the author's
*intent text*, not a guarantee about the body. Claim texts: `Alignment/claims_blind.yaml` (group
`SemanticsPWS`).

Trusted module under test: `NetworkEpi.Semantics.PWS` (file `NetworkEpi/Semantics/PWS.lean`). Everything is in namespace `NEP`
(write `open NEP`). Numbers are real (`ℝ`) unless stated.

## (a) Imports

```lean
import NetworkEpi.Semantics.PWS   -- imports NetworkEpi.Semantics.EB
open NEP
```

## (b)–(c) Data types and operations under test

### From `NetworkEpi.Semantics.PWS` (S-anchored pairwise field PW^S, constant closure `K`)

```lean
/-- S-anchored pairwise coordinates `([s], [ss], [sZ], [Z])` over node species `σ`. -/
abbrev PWS (σ : Type) := ℝ × ℝ × (σ → ℝ) × (σ → ℝ)
-- access: for w : PWS σ, [s] = w.1, [ss] = w.2.1, [sZ] = w.2.2.1 Z, [Z] = w.2.2.2 Z
```

| signature (opaque) | docstring |
|---|---|
| `pwSField {σ : Type} [DecidableEq σ] (K : ℝ) : Rxn σ → PWS σ → PWS σ` | The S-anchored pairwise field of one T_EB reaction with constant triple closure `[A s B] = K [As][sB]/[s]` (see the module docstring for the quoted equations). |
| `pwSLift {σ : Type} [DecidableEq σ] (K : ℝ) (rs : List (Rxn σ)) (w : PWS σ) : PWS σ` | The S-anchored pairwise vector field of a reaction list: the sum of the per-reaction fields. |
| `pushPW {σ σ' : Type} [Fintype σ] [DecidableEq σ'] (f : σ → σ') (w : PWS σ) : PWS σ'` | Pushforward of PW^S coordinates along a species map: `[s]`, `[ss]` kept; `[sZ]` and `[Z]` summed over fibres. |
| `pullPW {σ σ' : Type} (f : σ → σ') (w : PWS σ') : PWS σ` | Pullback of PW^S coordinates along a species map. |
| `f2A : List (Rxn Unit)` | The F2 witness: an infection model `A` (`s + I → I + I` at τ = 1) over one node species `I`, and a vaccination model `B` (`s → V` at ν = 1) over one node species `V`. |
| `f2B : List (Rxn Unit)` | See `f2A`. |
| `f2State : PWS (Unit ⊕ Unit)` | The witness state: `[s] = [ss] = 1`, `[sI] = [sV] = 1`, `[I] = [V] = 0`. |

Module header (the per-reaction field "checked symbolically in the design pass", with the closed
triples `[A s B] = K [As][sB]/[s]`):

```
contact (s + J → X + J, τ):  [s]' −= τ[sJ];  [ss]' −= 2τ[ssJ];  [X]' += τ[sJ]
                              [sZ]' −= τ[Z s J] for every Z;  [sJ]' −= τ[sJ];  [sX]' += τ[s s J]
exit    (s → Y, ν):           [s]' −= ν[s];  [ss]' −= 2ν[ss];  [sZ]' −= ν[sZ] for every Z;
                              [sY]' += ν[ss];  [Y]' += ν[s]
trans   (X → Y | ∅, a):       [sX]' −= a[sX]; [sY]' += a[sX]; [X]' −= a[X]; [Y]' += a[X]
```

In `f2State : PWS (Unit ⊕ Unit)`, the node species `I` is `Sum.inl ()` and `V` is `Sum.inr ()`. The library
has **no** Lean PW (unanchored pairwise), PB, clustered EB or degree-dependent closure `K_ψ`, and no
notion of a lax comparison map.

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

### From `NetworkEpi.Semantics.EB` (per-reaction edge-based field)

```lean
/-- Degree data of a configuration network: the degree PGF `ψ` and two functions `ψ'`, `ψ''`
standing for its first and second derivatives. [...] -/
structure CNet where
  ψ : ℝ → ℝ      -- the degree PGF ψ
  ψ' : ℝ → ℝ     -- ψ' (the first derivative of ψ where assumed)
  ψ'' : ℝ → ℝ    -- ψ'' (the second derivative of ψ where assumed)

/-- EB coordinates `(θ, ξ, φ, pop)` over node species `σ`. -/
abbrev EB (σ : Type) := ℝ × ℝ × (σ → ℝ) × (σ → ℝ)
-- access: for u : EB σ, θ = u.1, ξ = u.2.1, φ = u.2.2.1, pop = u.2.2.2
```

`ψ`, `ψ'`, `ψ''` are three independent fields: nothing in `CNet` makes `ψ'` the derivative of `ψ`
or `ψ''` that of `ψ'`, and `ψ` need not be a PGF. A statement that needs such a relation must state
it (e.g. with `HasDerivAt`). Module header (coordinates): `θ` is the probability that a random edge
has not transmitted to the test node; `ξ` the exit survival factor (ξ ≡ 1 without exits); `φ X`
the probability that a random edge has not transmitted and its partner is in `X`; `pop X` the
fraction of nodes in `X`. The seed factor `q = 1 − Σ_X ρ_X` is a parameter (a free real argument).

| signature (opaque) | docstring |
|---|---|
| `CNet.susc (N : CNet) (q θ ξ : ℝ) : ℝ` | The fraction of susceptible nodes, `S = qξψ(θ)` (DESIGN §0). |
| `CNet.phiS (N : CNet) (q θ ξ : ℝ) : ℝ` | The susceptible edge probability, `φ_S = qξψ'(θ)/ψ'(1)` (DESIGN §0). |
| `ebField {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) : Rxn σ → EB σ → EB σ` | **The EB field of one reaction** (DESIGN §D.4). For `contact J X τ` (s + J → X + J): `θ̇ = −τφ_J`, `φ̇_J −= τφ_J`, `φ̇_X += τφ_J·qξψ''(θ)/ψ'(1)`, `pop_X' += τφ_J·qξψ'(θ)`. For `exit Y ν` (s → Y): `ξ̇ = −νξ`, `φ̇_Y += νφ_S`, `pop_Y' += νS`. For `trans X Y a`: `φ̇_X −= aφ_X`, `φ̇_Y += aφ_X`, `pop_X' −= a pop_X`, `pop_Y' += a pop_X` (no gains when `Y = none`, i.e. `X → ∅`). |
| `lift {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)) (u : EB σ) : EB σ` | The EB vector field of a reaction list: the sum of the per-reaction fields. |
| `ebSys {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)) : DynSys` | The EB model of `rs` on the configuration network `N` as an object of `DynSys` (state space `EB σ`, field `lift N q rs`). |
| `push {σ σ' : Type} [Fintype σ] [DecidableEq σ'] (f : σ → σ') (v : σ → ℝ) : σ' → ℝ` | Pushforward of species-indexed coordinates along a species map `f`: the value at `y` is the sum over the fibre `f⁻¹(y)`. |
| `pushEB {σ σ' : Type} [Fintype σ] [DecidableEq σ'] (f : σ → σ') (u : EB σ) : EB σ'` | Pushforward of EB coordinates along a species map: `θ` and `ξ` are kept (the susceptible species is glued to itself), `φ` and `pop` are summed over fibres. |
| `pullEB {σ σ' : Type} (f : σ → σ') (u : EB σ') : EB σ` | Pullback of EB coordinates along a species map: `θ` and `ξ` are kept, `φ` and `pop` are precomposed with `f`. |
| `Rxn.removalRate {σ : Type} (φ : σ → ℝ) : Rxn σ → ℝ` | `rs.removalFlux φ = Σ_{(X → ∅, a) ∈ rs} a φ_X`, the rate at which edge mass leaves the φ classes through removals `X → ∅`. (This docstring, attached to the per-reaction function, describes the list-level sum `removalFlux`; `Rxn.removalRate φ r` is the contribution of the single reaction `r`.) |
| `removalFlux {σ : Type} (rs : List (Rxn σ)) (v : σ → ℝ) : ℝ` | The total removal rate of a reaction list, evaluated on species-indexed coordinates `v`. |
| `Rxn.isRemoval {σ : Type} : Rxn σ → Bool` | A reaction is a removal `X → ∅`. |
| `Rxn.isExit {σ : Type} : Rxn σ → Bool` | A reaction is an exit `s → Y`. |
| `edgeDefect {σ : Type} [Fintype σ] (N : CNet) (q : ℝ) (u : EB σ) : ℝ` | The *edge defect* `θ − φ_S − Σ_X φ_X`. The design's conservation law says it vanishes. |
| `edgeDefectDeriv {σ : Type} [Fintype σ] (N : CNet) (q : ℝ) (u v : EB σ) : ℝ` | The derivative of `edgeDefect` at `u` in the direction `v`, when `ψ''` is the derivative of `ψ'` at `u.1`. |
| `nodeTotal {σ : Type} [Fintype σ] (N : CNet) (q : ℝ) (u : EB σ) : ℝ` | The node total `S + Σ_X pop_X = qξψ(θ) + Σ_X pop_X`. |
| `nodeTotalDeriv {σ : Type} [Fintype σ] (N : CNet) (q : ℝ) (u v : EB σ) : ℝ` | The derivative of `nodeTotal` at `u` in the direction `v`, when `ψ'` is the derivative of `ψ` at `u.1`. |

Solutions in the EB module are not a Lean predicate: a statement about a solution on a time
interval `I` spells out `∀ t ∈ I, HasDerivWithinAt x (lift N q rs (x t)) I t` (or `HasDerivAt` at
each `t`) for a curve `x : ℝ → EB σ`.

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

* `Sum.inl`, `Sum.inr`, `Unit ⊕ Unit`, `Unit`, `()`; `≠` on product types.

* Calculus: `HasDerivAt`, `HasDerivWithinAt`, `deriv`, `fderiv`, `HasFDerivAt`, `Differentiable`,
  `DifferentiableAt`, `ContDiff`, `ContDiffAt` (smoothness index `n : WithTop ℕ∞`; in current Mathlib
  `(⊤ : WithTop ℕ∞)` is `ω`, analytic, and `∞` is `((⊤ : ℕ∞) : WithTop ℕ∞)`; `open scoped ContDiff`
  for the notations), `ContinuousLinearMap` (`→L[ℝ]`), `Convex ℝ I`, `Set.Ioo`, `Set.Ici`, `Set.univ`.
* Filters: `Filter.Eventually`, `nhds` (`𝓝`, `open Topology`).
* Finite sums over species: `Finset.univ`, `∑ X, f X` (needs `[Fintype σ]`), `Pi.single X c`.
