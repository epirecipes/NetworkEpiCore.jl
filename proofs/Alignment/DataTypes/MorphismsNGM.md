# DataTypes — MorphismsNGM

Blind-safe vocabulary for shadow authors of group `MorphismsNGM` (SA-PASS, NetworkEpi library, namespace
`NEP`). It lists the imports, the data types (structures, inductives and type abbreviations, with
their fields) and the operations as **opaque signatures with their docstrings only** (signatures
as printed by `#check`). It contains no theorem statements, no proofs and no definition bodies
(type abbreviations excepted). Where a docstring spells out a formula, that formula is the
author's *intent text*, not a guarantee about the body. All signatures live in namespace `NEP`.

Module under test: `NetworkEpi.Morphisms.NGM` (DESIGN §D.7 row L5, §C.3 `MultiplexNetwork`, §J.5): R₀ as a spectral radius. This module imports only Mathlib (no epidemic data types).

## (a) Imports

```lean
import Alignment.Registry
import NetworkEpi.Morphisms.NGM

open NEP
```

## (b) Data types

None beyond Mathlib (real matrices `Matrix n n ℝ` over a finite index type).

## (c) Operations of this module (opaque signatures + docstrings)

* `NEP.multiplexNGM (T₁ T₂ k₁ k₂ e₁ e₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ`
  — The two-layer multiplex next-generation matrix of `ngm.jl` for a single entry state: `K_{ℓ ← m} = M_{mℓ} T_ℓ` with `M_{ℓℓ} = e_ℓ` (the excess degree `ψ_ℓ''(1)/ψ_ℓ'(1)` of layer ℓ), `M_{mℓ} = k_ℓ` (the mean degree `ψ_ℓ'(1)` of layer ℓ, m ≠ ℓ) and `T_ℓ` the per-edge transmissibility of layer ℓ: `K = [[T₁e₁, T₁k₁], [T₂k₂, T₂e₂]]`.


## (e) Notation used in the claim texts

* R₀ = ρ(K) is `spectralRadius ℝ K : ENNReal` for `K : Matrix n n ℝ` (the supremum of `‖λ‖₊` over the real spectrum
  `spectrum ℝ K`). A non-negative real value r is compared as `ENNReal.ofReal r`; |x| as `(‖x‖₊ : ENNReal)`.
* The rank-one matrix u vᵀ is `Matrix.vecMulVec u v`; v·u is `v ⬝ᵥ u` (`dotProduct`); e_E is `Pi.single E 1`;
  wᵀV⁻¹ is `w ᵥ* V⁻¹` (`Matrix.vecMul`); `V⁻¹` is Mathlib's matrix inverse (`Ring.inverse V.det • V.adjugate`,
  the zero matrix when `V` is singular). A 2 × 2 matrix [[a, b], [c, d]] is `!![a, b; c, d]`.
* The two-layer multiplex NGM K = [[T₁e₁, T₁k₁], [T₂k₂, T₂e₂]] is `multiplexNGM T₁ T₂ k₁ k₂ e₁ e₂`; the layer R₀s are
  T₁e₁ and T₂e₂.



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
* `Matrix n n ℝ` with `[Fintype n] [DecidableEq n]`, `Matrix.det`, `Matrix.diagonal`, `spectrum ℝ`, `spectralRadius ℝ`,
  `ENNReal`, `ENNReal.ofReal`, `nnnorm` (`‖·‖₊`), `Real.sqrt` (`√`), `Fin 2`.
