# DataTypes — MorphismsPoisson

Blind-safe vocabulary for shadow authors of group `MorphismsPoisson` (SA-PASS, NetworkEpi library, namespace
`NEP`). It lists the imports, the data types (structures, inductives and type abbreviations, with
their fields) and the operations as **opaque signatures with their docstrings only** (signatures
as printed by `#check`). It contains no theorem statements, no proofs and no definition bodies
(type abbreviations excepted). Where a docstring spells out a formula, that formula is the
author's *intent text*, not a guarantee about the body. All signatures live in namespace `NEP`.

Module under test: `NetworkEpi.Morphisms.Poisson` (DESIGN §D.5 row M2, §J.10, §L.1): the Poisson isomorphism EB_{Pois μ}(P) ≅ MA(D_μ P).

## (a) Imports

```lean
import Alignment.Registry
import NetworkEpi.Morphisms.Poisson

open NEP
```

## (b) Data types

### `DynSys` (from `NetworkEpi.Dyn.Basic`)

```lean
structure DynSys where
  V : Type                       -- the state space
  [ng : NormedAddCommGroup V]
  [ns : NormedSpace ℝ V]
  F : V → V                      -- the vector field; the ODE is u̇ = F u
```
Docstring: "An object of the design's category **Dyn** (DESIGN §D.3), generalised: a real normed space `V` with a vector field `F : V → V`. The ODE is `u̇ = F u`."

### `Semiconj` (from `NetworkEpi.Dyn.Basic`)

```lean
@[ext] structure Semiconj (A B : DynSys) where
  π : A.V → B.V
  diff : Differentiable ℝ π
  comm : ∀ u, fderiv ℝ π u (A.F u) = B.F (π u)
```
Docstring: "A morphism of `DynSys` (a *semiconjugacy*, DESIGN §D.3): a differentiable map `π` with `Dπ(u)·F(u) = G(π(u))` for every `u`."

### `SemiconjOn` (from `NetworkEpi.Dyn.Basic`)

```lean
structure SemiconjOn (A B : DynSys) (U : Set A.V) where
  π : A.V → B.V
  diff : ∀ u ∈ U, DifferentiableAt ℝ π u
  comm : ∀ u ∈ U, fderiv ℝ π u (A.F u) = B.F (π u)
```
Docstring: "A *local semiconjugacy on `U`* (DESIGN §D.3, "Local version `SemiconjOn U`"): a map `π : A.V → B.V` that is differentiable at every point of `U` and satisfies `Dπ(u)·F(u) = G(π(u))` for every `u ∈ U`. The design's use is an open `U` such as `{ψ(θ) ≠ 0, ψ'(θ) ≠ 0}`; openness is not required here because differentiability is asked for at each point of `U`."

### `Rxn` (from `NetworkEpi.Syntax.Rxn`)

```lean
inductive Rxn (σ : Type) where
  | contact (J X : σ) (τ : ℝ)        -- s + J → X + J at per-contact rate τ
  | exit (Y : σ) (ν : ℝ)             -- s → Y at rate ν
  | trans (X : σ) (Y : Option σ) (a : ℝ)   -- X → Y (Y = some _) or X → ∅ (Y = none) at rate a
```
Docstring: "T_EB reactions over node species `σ` (the susceptible species `s` is implicit): * `contact J X τ` is `s + J → X + J` at per-contact rate `τ` (DESIGN §0: "τ is always a per-contact (per-edge) rate"); * `exit Y ν` is `s → Y` at rate `ν` (for example vaccination); * `trans X (some Y) a` is `X → Y` and `trans X none a` is `X → ∅`, at rate `a`."

### `NRxn` (from `NetworkEpi.Syntax.Rxn`)

```lean
inductive NRxn (σ : Type) where
  | contact (J X : σ) (τ : ℝ)
  | exit (Y : σ) (ν : ℝ)
  | trans (X : σ) (Y : Option σ) (a : ℝ)
  | resus (X : σ) (a : ℝ)                          -- X → s
  | nodeContact (X : σ) (J : Option σ) (Y : σ) (τ : ℝ)   -- X + J → Y + J (J = none: catalyst s)
```
Docstring: "T_net reactions over node species `σ` (single susceptible species `s`): `NRxn σ` has the T_EB constructors of `Rxn σ` and adds * `resus X a`: `X → s` at rate `a` (§B.2 type `:resus`, e.g. SIS `I → S`, SIRS `R → S`); * `nodeContact X J Y τ`: `X + J → Y + J` at rate `τ`, with recipient `X` a node species and catalyst `J` (`J = none` means the catalyst is `s`) (§B.2 type `:node_contact`)."

### `CNet` (from `NetworkEpi.Semantics.EB`)

```lean
structure CNet where
  ψ : ℝ → ℝ      -- the degree PGF
  ψ' : ℝ → ℝ     -- stands for ψ' (a free function; related to ψ only where a hypothesis says so)
  ψ'' : ℝ → ℝ    -- stands for ψ''
```
Docstring: "Degree data of a configuration network: the degree PGF `ψ` and two functions `ψ'`, `ψ''` standing for its first and second derivatives. The lift laws (`lift_append`, `lift_map`, `lift_glue`) hold for arbitrary functions; results that differentiate along solutions (`conservation`, `node_conservation`) assume `HasDerivAt` relations between them."

### `EB` (from `NetworkEpi.Semantics.EB`)

```lean
abbrev EB (σ : Type) := ℝ × ℝ × (σ → ℝ) × (σ → ℝ)   -- (θ, ξ, φ, pop); u.1 = θ, u.2.1 = ξ, u.2.2.1 = φ, u.2.2.2 = pop
```
Docstring: "EB coordinates `(θ, ξ, φ, pop)` over node species `σ`."

### `MA` (from `NetworkEpi.Semantics.MA`)

```lean
abbrev MA (σ : Type) := ℝ × (σ → ℝ)   -- (S, x); v.1 = S, v.2 X = x_X
```
Docstring: "Mass-action coordinates `(S, x)` over node species `σ`."

### `SIRSp` (from `NetworkEpi.Semantics.PoissonSIR`)

```lean
inductive SIRSp where | I | R   deriving DecidableEq, Fintype
```
Docstring: "Node species of SIR (the susceptible species is implicit)."

### `SEIRSp` (from `NetworkEpi.Semantics.Solutions`)

```lean
inductive SEIRSp where | E | I | R   deriving DecidableEq, Fintype
```
Docstring: "Node species of SEIR (the susceptible species is implicit)."

### `SRxn` (from `NetworkEpi.Morphisms.Stoich`)

```lean
structure SRxn (ι : Type) where
  inp : Multiset ι   -- the reactant multiset
  out : Multiset ι   -- the product multiset
  k : ℝ              -- the rate constant
```
Docstring: "A reaction with multiset stoichiometry over the species type `ι`: `inp → out` at the mass-action rate constant `k`."

### `DSp` (from `NetworkEpi.Morphisms.Poisson`)

```lean
abbrev DSp (σ : Type) := Option (σ ⊕ σ)   -- none = S, some (inl X) = edge copy Φ_X, some (inr X) = node copy X
```
Docstring: "Species of `D_μ P`: `none` is `S`, `some (inl X)` the edge copy `Φ_X`, `some (inr X)` the node copy `X`."

### `EB1` (from `NetworkEpi.Morphisms.Common`)

```lean
abbrev EB1 (σ : Type) := ℝ × (σ → ℝ) × (σ → ℝ)   -- (θ, φ, pop), the slice ξ = 1
```
Docstring: "The design's EB coordinates `(θ, φ, pop)` of an exit-free model (ξ ≡ 1 is dropped)."

## (c) Operations of this module (opaque signatures + docstrings)

* `NEP.Rxn.poissonD {σ : Type} (μ : ℝ) : Rxn σ → List (SRxn (DSp σ))`
  — `D_μ` of one T_EB reaction (DESIGN §D.5 M2 and §J.10), with multiset stoichiometry.

* `NEP.poissonRxns {σ : Type} (μ : ℝ) (rs : List (Rxn σ)) : List (SRxn (DSp σ))`
  — `D_μ P` for a T_EB reaction list `P`.

* `NEP.poissonMap {σ : Type} (μ q : ℝ) (u : EB σ) : DSp σ → ℝ`
  — The map `(θ, ξ, φ, pop) ↦ (S = qξe^{μ(θ−1)}, Φ = φ, X = pop)`.

* `NEP.poissonDComp {σ : Type} (μ q : ℝ) (u : EB σ) : DSp σ → EB σ →L[ℝ] ℝ`
  — The components of the derivative of `poissonMap μ q` at `u`.

* `NEP.poissonDL {σ : Type} (μ q : ℝ) (u : EB σ) : EB σ →L[ℝ] DSp σ → ℝ`
  — The derivative of `poissonMap μ q` at `u`.

* `NEP.poissonInv {σ : Type} (μ q : ℝ) (v : DSp σ → ℝ) : EB1 σ`
  — The inverse of the Poisson map on `S > 0` for exit-free models: `(S, Φ, X) ↦ (θ, φ, pop) = (1 + log(S/q)/μ, Φ, X)`.

* `NEP.dMap {σ σ' : Type} (f : σ → σ') : DSp σ → DSp σ'`
  — The species map of `D_μ` induced by a node-species map `f`.


## (d) Operations from other trusted modules (opaque signatures + docstrings)

* `NEP.IsSemiconj (A B : DynSys) (π : A.V → B.V) : Prop`
  — `IsSemiconj A B π`: the map `π : A.V → B.V` is differentiable and carries the vector field of `A` to that of `B`, i.e. `Dπ(u)·F(u) = G(π(u))` for every `u` (DESIGN §D.3).

* `NEP.IsSemiconjOn (A B : DynSys) (U : Set A.V) (π : A.V → B.V) : Prop`
  — `IsSemiconjOn A B U π`: `π` is differentiable at every point of `U` and `Dπ(u)·F(u) = G(π(u))` for every `u ∈ U`.

* `NEP.Semiconj.ofIsSemiconj {A B : DynSys} (π : A.V → B.V) (h : IsSemiconj A B π) : Semiconj A B`
  — Bundle a map satisfying `IsSemiconj` as a morphism.

* `NEP.SemiconjOn.ofIsSemiconjOn {A B : DynSys} {U : Set A.V} (π : A.V → B.V) (h : IsSemiconjOn A B U π) : SemiconjOn A B U`
  — Bundle a map satisfying `IsSemiconjOn` as a local semiconjugacy.

* `NEP.Rxn.map {σ σ' : Type} (f : σ → σ') : Rxn σ → Rxn σ'`
  — Relabel the node species of a T_EB reaction along `f` (DESIGN §D.1: "Morphisms of syntax are type-preserving species maps that carry reactions to reactions"). Gluing species along a cospan is relabelling along the cospan legs.

* `NEP.NRxn.map {σ σ' : Type} (f : σ → σ') : NRxn σ → NRxn σ'`
  — Relabel the node species of a T_net reaction along `f`.

* `NEP.Rxn.toNRxn {σ : Type} : Rxn σ → NRxn σ`
  — The inclusion of T_EB syntax into T_net syntax.

* `NEP.Rxn.scaleContacts {σ : Type} (κ : ℝ) : Rxn σ → Rxn σ`
  — The rate convention `c_κ`: multiply every contact rate by `κ`, leaving exits and transitions unchanged (DESIGN §D.5 M1 uses `c_κ` for the well-mixed unit, M3 uses `c_μ`).

* `NEP.Rxn.isExit {σ : Type} : Rxn σ → Bool`
  — A reaction is an exit `s → Y`.

* `NEP.Rxn.isRemoval {σ : Type} : Rxn σ → Bool`
  — A reaction is a removal `X → ∅`.

* `NEP.CNet.susc (N : CNet) (q θ ξ : ℝ) : ℝ`
  — The fraction of susceptible nodes, `S = qξψ(θ)` (DESIGN §0).

* `NEP.CNet.phiS (N : CNet) (q θ ξ : ℝ) : ℝ`
  — The susceptible edge probability, `φ_S = qξψ'(θ)/ψ'(1)` (DESIGN §0).

* `NEP.ebField {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) : Rxn σ → EB σ → EB σ`
  — **The EB field of one reaction** (DESIGN §D.4; see the module docstring for the quoted table). For `contact J X τ` (s + J → X + J): `θ̇ = −τφ_J`, `φ̇_J −= τφ_J`, `φ̇_X += τφ_J·qξψ''(θ)/ψ'(1)`, `pop_X' += τφ_J·qξψ'(θ)`. For `exit Y ν` (s → Y): `ξ̇ = −νξ`, `φ̇_Y += νφ_S`, `pop_Y' += νS`. For `trans X Y a`: `φ̇_X −= aφ_X`, `φ̇_Y += aφ_X`, `pop_X' −= a pop_X`, `pop_Y' += a pop_X` (no gains when `Y = none`, i.e. `X → ∅`).

* `NEP.lift {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)) (u : EB σ) : EB σ`
  — The EB vector field of a reaction list: the sum of the per-reaction fields.

* `NEP.ebSys {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)) : DynSys`
  — The EB model of `rs` on the configuration network `N` as an object of `DynSys`.

* `NEP.push {σ σ' : Type} [Fintype σ] [DecidableEq σ'] (f : σ → σ') (v : σ → ℝ) : σ' → ℝ`
  — Pushforward of species-indexed coordinates along a species map `f`: the value at `y` is the sum over the fibre `f⁻¹(y)`.

* `NEP.pushEB {σ σ' : Type} [Fintype σ] [DecidableEq σ'] (f : σ → σ') (u : EB σ) : EB σ'`
  — Pushforward of EB coordinates along a species map: `θ` and `ξ` are kept (the susceptible species is glued to itself), `φ` and `pop` are summed over fibres.

* `NEP.pullEB {σ σ' : Type} (f : σ → σ') (u : EB σ') : EB σ`
  — Pullback of EB coordinates along a species map: `θ` and `ξ` are kept, `φ` and `pop` are precomposed with `f`.

* `NEP.maField {σ : Type} [DecidableEq σ] : NRxn σ → MA σ → MA σ`
  — The mass-action field of one T_net reaction, with flux `k·Π(reactant fractions)`: * `contact J X k` (s + J → X + J): flux `k S x_J`, `S −= flux`, `x_X += flux`; * `exit Y ν` (s → Y): flux `ν S`, `S −= flux`, `x_Y += flux`; * `trans X (some Y) a` (X → Y): flux `a x_X`, `x_X −= flux`, `x_Y += flux`; * `trans X none a` (X → ∅): `x_X −= a x_X`; * `resus X a` (X → s): flux `a x_X`, `x_X −= flux`, `S += flux`; * `nodeContact X J Y k` (X + J → Y + J): flux `k x_X x_J` (`x_J = S` when `J = none`), `x_X −= flux`, `x_Y += flux`.

* `NEP.maLift {σ : Type} [DecidableEq σ] (rs : List (NRxn σ)) (u : MA σ) : MA σ`
  — The mass-action vector field of a T_net reaction list: the sum of the per-reaction fields.

* `NEP.maSys {σ : Type} [DecidableEq σ] [Fintype σ] (rs : List (NRxn σ)) : DynSys`
  — The mass-action model of `rs` as an object of `DynSys`.

* `NEP.pushMA {σ σ' : Type} [Fintype σ] [DecidableEq σ'] (f : σ → σ') (u : MA σ) : MA σ'`
  — Pushforward of MA coordinates along a species map: `S` is kept, `x` is summed over fibres.

* `NEP.pullMA {σ σ' : Type} (f : σ → σ') (u : MA σ') : MA σ`
  — Pullback of MA coordinates along a species map: `S` is kept, `x` is precomposed with `f`.

* `NEP.CNet.poisson (μ : ℝ) : CNet`
  — The Poisson(μ) configuration network: `ψ(x) = e^{μ(x−1)}`, `ψ'(x) = μe^{μ(x−1)}`, `ψ''(x) = μ²e^{μ(x−1)}`.

* `NEP.sirRxns (τ γ : ℝ) : List (Rxn SIRSp)`
  — SIR as a T_EB reaction list: `s + I → I + I` at per-contact rate `τ`, `I → R` at rate `γ`.

* `NEP.maSIR (β ρ : ℝ) : DynSys`
  — Mass-action SIR in coordinates `(S, I)` with contact rate `β` and removal rate `ρ`: `Ṡ = −βSI`, `İ = βSI − ρI`.

* `NEP.seirRxns (τ a γ : ℝ) : List (Rxn SEIRSp)`
  — SEIR as a T_EB reaction list: `s + I → E + I` at per-contact rate `τ`, `E → I` at rate `σ` (named `a` here) and `I → R` at rate `γ`.

* `NEP.SRxn.flux {ι : Type} (r : SRxn ι) (x : ι → ℝ) : ℝ`
  — The mass-action flux `k · Π_{i ∈ inp} x_i` of a multiset reaction.

* `NEP.SRxn.field {ι : Type} [DecidableEq ι] (r : SRxn ι) (x : ι → ℝ) : ι → ℝ`
  — The mass-action field of a multiset reaction: `flux · (out − inp)`, i.e. species `i` changes at `flux · (count_i(out) − count_i(inp))`.

* `NEP.sLift {ι : Type} [DecidableEq ι] (rs : List (SRxn ι)) (x : ι → ℝ) : ι → ℝ`
  — The mass-action field of a list of multiset reactions: the sum of the per-reaction fields.

* `NEP.sSys {ι : Type} [Fintype ι] [DecidableEq ι] (rs : List (SRxn ι)) : DynSys`
  — The mass-action model of a list of multiset reactions as an object of `DynSys`.

* `NEP.SRxn.map {ι ι' : Type} (g : ι → ι') (r : SRxn ι) : SRxn ι'`
  — Relabel the species of a multiset reaction along `g` (image multisets).

* `NEP.IsConjOn (A B : DynSys) (V : Set A.V) (U : Set B.V) (h : A.V → B.V) (g : B.V → A.V) : Prop`
  — `IsConjOn A B V U h g`: `h` is a local semiconjugacy on `V` from `A` to `B` with `h(V) ⊆ U`, `g` is a local semiconjugacy on `U` from `B` to `A` with `g(U) ⊆ V`, and they are inverse to each other on these sets (`g (h u) = u` for `u ∈ V`, `h (g v) = v` for `v ∈ U`). When `V` and `U` are invariant, this is a conjugacy (an isomorphism of `DynSys`) between the restrictions of `A` to `V` and of `B` to `U`: `h` maps solutions that stay in `V` to solutions, and `g` maps solutions that stay in `U` back.

* `NEP.EB1.incl {σ : Type} (w : EB1 σ) : EB σ`
  — The inclusion `(θ, φ, pop) ↦ (θ, 1, φ, pop)` of the slice `ξ = 1`.

* `NEP.EB.drop {σ : Type} (u : EB σ) : EB1 σ`
  — The chart `(θ, ξ, φ, pop) ↦ (θ, φ, pop)`.

* `NEP.ebSys1 {σ : Type} [Fintype σ] [DecidableEq σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)) : DynSys`
  — The EB model on the slice `ξ = 1`, in the design's coordinates `(θ, φ, pop)`: `F(θ, φ, pop) = drop (lift N q rs (θ, 1, φ, pop))`. For an exit-free model this is the EB model itself (`ebSys1_incl`).


## (e) Notation used in the claim texts

* Species: node species form a type `σ` (finite, with decidable equality where required); the
  susceptible species `s` is implicit (it is not an element of `σ`). T_EB = the reactions of `Rxn σ`
  (contacts, exits, progressions `X → Y`, removals `X → ∅`); T_net = `NRxn σ`.
* "The EB model of `rs` on the configuration network `N` with seed factor `q`" is `ebSys N q rs`
  (state `EB σ` = (θ, ξ, φ, pop), field `lift N q rs`); `S = qξψ(θ)` is `N.susc q θ ξ` and
  `φ_S = qξψ'(θ)/ψ'(1)` is `N.phiS q θ ξ`.
* "Poisson(μ)" is the configuration network `CNet.poisson μ` (ψ(x) = e^{μ(x−1)}, ψ' = μψ, ψ'' = μ²ψ).
* "The mass-action model MA(P)" of a T_net list `P` is `maSys P` (state `MA σ` = (S, x)); a T_EB list
  is turned into T_net syntax by `List.map Rxn.toNRxn`.
* "Semiconjugacy" (global) is `IsSemiconj A B π`; "local semiconjugacy on U" is `IsSemiconjOn A B U π`;
  `Semiconj A B` is the bundled morphism of the category `DynSys`.
* Relabelling/gluing species along `f : σ → σ'` acts on syntax by `Rxn.map f` / `NRxn.map f` and on
  coordinates by `pushEB f`, `pullEB f`, `pushMA f`, `pullMA f` (push sums over fibres, pull precomposes).
* SIR: `sirRxns τ γ` over `SIRSp`; mass-action SIR in (S, I): `maSIR β ρ`. SEIR: `seirRxns τ a γ` over `SEIRSp`
  (the rate of `E → I` is called σ in the design and `a` here).
* "Conjugacy" of `A` on `V` with `B` on `U` via `h`, `g` is `IsConjOn A B V U h g` (see its docstring).
* D_μ P = `poissonRxns μ P : List (SRxn (DSp σ))` (multiset reactions over S, the edge copies Φ_X and the node copies X);
  MA(D_μ P) = `sSys (poissonRxns μ P)` (multiset mass action, field `sLift`).
* π(θ, ξ, φ, pop) = (S = qξe^{μ(θ−1)}, Φ = φ, X = pop) is `poissonMap μ q`; `poissonDL μ q u` is the explicit linear map
  intended as its derivative at `u`; the candidate inverse (S, Φ, X) ↦ (1 + log(S/q)/μ, Φ, X) is `poissonInv μ q`
  (values in `EB1 σ`, the design's coordinates (θ, φ, pop) on ξ = 1, with inclusion `EB1.incl`).
* The EB model of an exit-free P in the design's coordinates (θ, φ, pop): `ebSys1 (CNet.poisson μ) q P`.
* Species maps of D_μ induced by `f : σ → σ'`: `dMap f`; relabelling multiset reactions: `SRxn.map`; pushforward of
  `DSp`-indexed coordinates: `push (dMap f)`.



## (f) Mathlib notions a faithful formalisation may need

* Calculus: `HasFDerivAt f f' x`, `fderiv ℝ f x`, `DifferentiableAt ℝ f x`, `Differentiable ℝ f`,
  `HasDerivAt`, `HasDerivWithinAt f f' I t` (one-sided at end points of `I` that lie in `I`),
  continuous linear maps `E →L[ℝ] F` (applied as functions).
* Lists: `List.map`, `List.sum`, `List.flatMap`, `++`, membership `r ∈ rs`.
* Sets and functions: `Set.univ`, `{u | P u}`, `Set.Ioo a b`, `Convex ℝ I`, `interior`, `Set.Nonempty`,
  `Function.Surjective`, `Function.Injective`, `∘`, `Pi.single X c` (the function that is `c` at `X`
  and 0 elsewhere).
* Real functions: `Real.exp`, `Real.log`, `Real.sqrt` (`√`), `Real.rpow` (`x ^ (κ : ℝ)`).
* A *solution* of `A : DynSys` on a set of times `I` is a curve `x : ℝ → A.V` with
  `∀ t ∈ I, HasDerivAt x (A.F (x t)) t` or, within `I`, `∀ t ∈ I, HasDerivWithinAt x (A.F (x t)) I t`.
* `Option`, `Sum` (`⊕`, `Sum.inl`, `Sum.inr`, `Sum.elim`, `Sum.map`), `Option.map`, `Real.log`.
