import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# L5 (stretch): R₀ as a spectral radius — rank-one NGMs and the two-layer multiplex

DESIGN_NetworkEpiCore.md §D.7 table: "L5 (stretch) | R₀ | rank-one NGM for a single entry state;
2-layer multiplex R₀ = ρ(K) | medium–hard"; §C.3, `MultiplexNetwork`: "R₀ = ρ(K)"; §J.5 and
`NetworkEpiCore.jl/src/analysis/ngm.jl` ("R₀ = ρ(K), **not** the sum of the layer R₀s (verified
issue E12)").

(This module sits under `NetworkEpi/Morphisms/` because WP28 owns only `Morphisms/**` and
`Closure/**`; it is linear algebra, not a morphism.)

R₀ is the spectral radius `spectralRadius ℝ K` (Mathlib: the supremum of `‖λ‖₊` over the real
spectrum of `K`, an extended non-negative real) of a next-generation matrix `K`.

## Results

* `spectralRadius_vecMulVec`: a rank-one matrix `u vᵀ` (`u ≠ 0`) has real spectrum inside
  `{0, v·u}` containing `v·u`, so its spectral radius is `|v·u|`.
* `r0_single_entry`, `r0_single_entry_rank`: if every new infection enters one state `E`
  (`F = e_E wᵀ`), the next-generation matrix `K = F V⁻¹ = e_E (wᵀV⁻¹)` has rank at most one and
  `R₀ = ρ(K) = |(wᵀV⁻¹)_E|`: the expected number of new infections produced by one individual that
  enters `E`. This is why NEC's NGM over
  entry-state blocks is a 1 × 1 matrix for a single entry state.
* `spectralRadius_fin_two`: for a 2 × 2 matrix `[[a, b], [c, d]]` with `a, d ≥ 0` and `bc ≥ 0`
  (for example a non-negative NGM), `ρ = (a + d + √((a − d)² + 4bc))/2`.
* `multiplex_r0`, `multiplex_r0_eq_sum_iff`: for the two-layer multiplex NGM
  `K = [[T₁e₁, T₁k₁], [T₂k₂, T₂e₂]]` (as in `ngm.jl`: `M_ℓℓ = κ_ex,ℓ`, `M_mℓ = ⟨k_ℓ⟩`),
  `R₀ = ρ(K)` has the closed form above, and it equals the sum `T₁e₁ + T₂e₂` of the layer R₀s iff
  `T₁T₂k₁k₂ = T₁T₂e₁e₂`.

**Scope.** These are statements about given matrices. That these matrices are the
next-generation matrices of the EB models (the linearisation of the EB field at the disease-free
state, the per-edge transmissibilities `T`) is not formalised here.
-/

open Matrix

namespace NEP

section Spectrum
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `r` is in the real spectrum of `K` iff `det(r·1 − K) = 0`, with `r·1` written as the scalar
multiple `r • 1` of the identity matrix. -/
theorem mem_spectrum_iff_det_smul (K : Matrix n n ℝ) (r : ℝ) :
    r ∈ spectrum ℝ K ↔ (r • (1 : Matrix n n ℝ) - K).det = 0 := by
  simp [spectrum.mem_iff, isUnit_iff_isUnit_det, Algebra.algebraMap_eq_smul_one]

/-- `r` is in the real spectrum of `K` iff `det(r·1 − K) = 0`. -/
lemma mem_spectrum_iff_det (K : Matrix n n ℝ) (r : ℝ) :
    r ∈ spectrum ℝ K ↔ (diagonal (fun _ => r) - K).det = 0 := by
  simp [spectrum.mem_iff, isUnit_iff_isUnit_det, algebraMap_eq_diagonal, Pi.algebraMap_def]

/-- The real spectrum of the rank-one matrix `u vᵀ` lies in `{0, v·u}`. -/
theorem spectrum_vecMulVec_subset (u v : n → ℝ) :
    spectrum ℝ (vecMulVec u v) ⊆ {0, v ⬝ᵥ u} := by
  intro r hr
  rw [mem_spectrum_iff_det] at hr
  by_contra h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h
  obtain ⟨h0, hc⟩ := h
  have e : diagonal (fun _ => r) - vecMulVec u v =
      r • (1 + replicateCol Unit (-(r⁻¹) • u) * replicateRow Unit v) := by
    rw [← vecMulVec_eq Unit]
    ext i j
    simp only [sub_apply, diagonal_apply, smul_apply, add_apply, one_apply, vecMulVec_apply,
      Pi.smul_apply, smul_eq_mul]
    split_ifs <;> field_simp <;> ring
  rw [e, det_smul, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, smul_eq_mul]
    at hr
  have hpow : r ^ Fintype.card n ≠ 0 := pow_ne_zero _ h0
  have h1 : 1 + -r⁻¹ * (v ⬝ᵥ u) ≠ 0 := by
    intro h1
    apply hc
    field_simp at h1
    linarith
  exact mul_ne_zero hpow h1 hr

/-- `v·u` is in the real spectrum of `u vᵀ` when `u ≠ 0` (`u` is an eigenvector). -/
theorem mem_spectrum_vecMulVec (u v : n → ℝ) (hu : u ≠ 0) :
    v ⬝ᵥ u ∈ spectrum ℝ (vecMulVec u v) := by
  rw [mem_spectrum_iff_det, ← exists_mulVec_eq_zero_iff]
  refine ⟨u, hu, ?_⟩
  rw [sub_mulVec, vecMulVec_mulVec]
  ext i
  simp [mul_comm]

/-- **The spectral radius of a rank-one matrix (L5).**

Design statement (DESIGN_NetworkEpiCore.md §D.7 table): "L5 (stretch) | R₀ | rank-one NGM for a
single entry state".

Lean statement: for every finite index type `n` and vectors `u, v : n → ℝ` with `u ≠ 0`, the
spectral radius (over ℝ) of the rank-one matrix `u vᵀ` (`vecMulVec u v`) is `|v·u|`
(`‖v ⬝ᵥ u‖₊`); its real spectrum lies in `{0, v·u}` and contains `v·u`. -/
theorem spectralRadius_vecMulVec (u v : n → ℝ) (hu : u ≠ 0) :
    spectralRadius ℝ (vecMulVec u v) = ‖v ⬝ᵥ u‖₊ := by
  apply le_antisymm
  · refine iSup₂_le fun r hr => ?_
    rcases spectrum_vecMulVec_subset u v hr with h | h
    · simp [Set.mem_singleton_iff.mp h]
    · rw [Set.mem_singleton_iff.mp h]
  · exact le_iSup₂ (f := fun k (_ : k ∈ spectrum ℝ (vecMulVec u v)) => (‖k‖₊ : ENNReal))
      (v ⬝ᵥ u) (mem_spectrum_vecMulVec u v hu)

/-- **R₀ for a single entry state: the spectral radius of the next-generation matrix (L5).**

Design statement (DESIGN_NetworkEpiCore.md §D.7 table): "L5 (stretch) | R₀ | rank-one NGM for a
single entry state; 2-layer multiplex R₀ = ρ(K)".

Lean statement: let `n` be a finite type of infected states, `E : n` the entry state,
`w : n → ℝ` any vector and `V` any real `n × n` matrix (in applications, the transition matrix of
the infected states, so that `(V⁻¹)_{J E}` is the expected time spent in `J` by an individual that
enters `E`). Let `F = e_E wᵀ` be the new-infection matrix in which every new infection enters `E`
(`F_{X J} = w_J` if `X = E` and 0 otherwise). Then the next-generation matrix `K = F V⁻¹` has
spectral radius `ρ(K) = |(wᵀV⁻¹)_E| = |Σ_J w_J (V⁻¹)_{J E}|`.

Scope: linear algebra only. For a non-negative NGM the absolute value can be dropped. That `F` and
`V` are the linearisation of a given EB model is not formalised. -/
theorem r0_single_entry (E : n) (w : n → ℝ) (V : Matrix n n ℝ) :
    spectralRadius ℝ (vecMulVec (Pi.single E 1) w * V⁻¹) = ‖(w ᵥ* V⁻¹) E‖₊ := by
  rw [vecMulVec_mul, spectralRadius_vecMulVec _ _ (by simp), dotProduct_single, mul_one]

/-- **R₀ for a single entry state: the next-generation matrix `e_E (wᵀV⁻¹)` has rank at most one
(L5).**

Design statement (DESIGN_NetworkEpiCore.md §D.7 table): "L5 (stretch) | R₀ | rank-one NGM for a
single entry state; 2-layer multiplex R₀ = ρ(K)"; amended by §M.2: "for a single entry state E the
next-generation matrix K = F V⁻¹ = e_E (wᵀV⁻¹) has rank at most one (rank one unless wᵀV⁻¹ = 0),
and R₀ = ρ(K) = |(wᵀV⁻¹)_E|".

Lean statement: let `n` be a finite type of infected states, `E : n` the entry state,
`w : n → ℝ` any vector and `V` any real `n × n` matrix (`V⁻¹` is Mathlib's inverse, the zero
matrix when `V` is singular). For `F = e_E wᵀ` (`vecMulVec (Pi.single E 1) w`), the
next-generation matrix `K = F V⁻¹` equals the outer product `e_E (wᵀV⁻¹)`
(`vecMulVec (Pi.single E 1) (w ᵥ* V⁻¹)`), has rank at most one, and has spectral radius
`ρ(K) = |(wᵀV⁻¹)_E|`. -/
theorem r0_single_entry_rank (E : n) (w : n → ℝ) (V : Matrix n n ℝ) :
    vecMulVec (Pi.single E 1) w * V⁻¹ = vecMulVec (Pi.single E 1) (w ᵥ* V⁻¹) ∧
      (vecMulVec (Pi.single E 1) w * V⁻¹).rank ≤ 1 ∧
      spectralRadius ℝ (vecMulVec (Pi.single E 1) w * V⁻¹) = ‖(w ᵥ* V⁻¹) E‖₊ := by
  refine ⟨vecMulVec_mul _ _ _, ?_, r0_single_entry E w V⟩
  rw [vecMulVec_mul, vecMulVec_eq Unit]
  refine (rank_mul_le_left _ _).trans ?_
  simpa using rank_le_card_width (replicateCol Unit (Pi.single E (1 : ℝ) : n → ℝ))

/-- **R₀ for a single entry state: the next-generation matrix `e_E (wᵀV⁻¹)` has rank one unless
`wᵀV⁻¹ = 0` (L5).**

Design statement (DESIGN_NetworkEpiCore.md §D.7 table): "L5 (stretch) | R₀ | rank-one NGM for a
single entry state; 2-layer multiplex R₀ = ρ(K)"; amended by §M.2: "for a single entry state E the
next-generation matrix K = F V⁻¹ = e_E (wᵀV⁻¹) has rank at most one (rank one unless wᵀV⁻¹ = 0),
and R₀ = ρ(K) = |(wᵀV⁻¹)_E|".

Lean statement: let `n` be a finite type of infected states, `E : n`, `w : n → ℝ` and `V` a real
`n × n` matrix (`V⁻¹` is Mathlib's inverse). If `wᵀV⁻¹ ≠ 0` (`w ᵥ* V⁻¹ ≠ 0`), then for
`F = e_E wᵀ` the next-generation matrix `K = F V⁻¹` has rank exactly one. (With
`r0_single_entry_rank`, which gives `K = e_E (wᵀV⁻¹)`, rank at most one and `ρ(K)`.) -/
theorem r0_single_entry_rank_one (E : n) (w : n → ℝ) (V : Matrix n n ℝ) (h : w ᵥ* V⁻¹ ≠ 0) :
    (vecMulVec (Pi.single E 1) w * V⁻¹).rank = 1 := by
  obtain ⟨_, hle, _⟩ := r0_single_entry_rank E w V
  refine le_antisymm hle ?_
  rw [Nat.one_le_iff_ne_zero, Ne, Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
  intro h0
  apply h
  funext j
  have := congrArg (fun f => f (Pi.single j 1) E) h0
  simp only [mulVecLin_apply, LinearMap.zero_apply, Pi.zero_apply] at this
  rw [vecMulVec_mul, mulVec_single_one] at this
  simpa [vecMulVec_apply] using this

end Spectrum

section TwoByTwo

/-- The real spectrum of a 2 × 2 matrix with non-negative discriminant
`D = (a − d)² + 4bc`: the two roots `(a + d ± √D)/2` of `λ² − (a + d)λ + (ad − bc)`. -/
theorem spectrum_fin_two (a b c d : ℝ) (hD : 0 ≤ (a - d) ^ 2 + 4 * b * c) :
    spectrum ℝ !![a, b; c, d] =
      {(a + d + √((a - d) ^ 2 + 4 * b * c)) / 2, (a + d - √((a - d) ^ 2 + 4 * b * c)) / 2} := by
  ext r
  rw [mem_spectrum_iff_det, det_fin_two]
  simp only [sub_apply, diagonal_apply_eq, of_apply, cons_val', cons_val_zero, cons_val_one,
    empty_val', cons_val_fin_one, Set.mem_insert_iff, Set.mem_singleton_iff]
  simp only [diagonal_apply_ne _ (show (0 : Fin 2) ≠ 1 by decide),
    diagonal_apply_ne _ (show (1 : Fin 2) ≠ 0 by decide), zero_sub]
  have hs := Real.sq_sqrt hD
  set s := √((a - d) ^ 2 + 4 * b * c)
  have e : (r - a) * (r - d) - -b * -c = (r - (a + d + s) / 2) * (r - (a + d - s) / 2) := by
    nlinarith [hs]
  rw [e, mul_eq_zero, sub_eq_zero, sub_eq_zero]

/-- **The spectral radius of a non-negative 2 × 2 matrix (L5).**

Design statement (DESIGN_NetworkEpiCore.md §D.7 table): "2-layer multiplex R₀ = ρ(K)".

Lean statement: for real `a, b, c, d` with `a ≥ 0`, `d ≥ 0` and `bc ≥ 0` (for example a
non-negative 2 × 2 next-generation matrix), the spectral radius over ℝ of `[[a, b], [c, d]]` is
`(a + d + √((a − d)² + 4bc))/2`. -/
theorem spectralRadius_fin_two (a b c d : ℝ) (ha : 0 ≤ a) (hd : 0 ≤ d) (hbc : 0 ≤ b * c) :
    spectralRadius ℝ !![a, b; c, d] =
      ENNReal.ofReal ((a + d + √((a - d) ^ 2 + 4 * b * c)) / 2) := by
  have hD : 0 ≤ (a - d) ^ 2 + 4 * b * c := by nlinarith [sq_nonneg (a - d)]
  set s := √((a - d) ^ 2 + 4 * b * c) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hp : 0 ≤ (a + d + s) / 2 := by linarith
  have hm : |(a + d - s) / 2| ≤ (a + d + s) / 2 := by
    rw [abs_le]
    constructor <;> linarith
  rw [spectralRadius, spectrum_fin_two a b c d hD, iSup_insert, iSup_singleton]
  have e1 : ((‖(a + d + s) / 2‖₊ : NNReal) : ENNReal) = ENNReal.ofReal ((a + d + s) / 2) := by
    rw [Real.nnnorm_of_nonneg hp, ENNReal.ofReal, Real.toNNReal_of_nonneg hp]
  have hle : ((‖(a + d - s) / 2‖₊ : NNReal) : ENNReal) ≤ ‖(a + d + s) / 2‖₊ := by
    rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg hp]
    exact hm
  rw [sup_eq_left.2 hle, e1]

/-- For real `a, d ≥ 0`, `bc ≥ 0`: the spectral radius of `[[a, b], [c, d]]` is the trace `a + d`
iff `bc = ad` (the determinant vanishes). -/
theorem spectralRadius_fin_two_eq_trace_iff (a b c d : ℝ) (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hbc : 0 ≤ b * c) :
    spectralRadius ℝ !![a, b; c, d] = ENNReal.ofReal (a + d) ↔ b * c = a * d := by
  have hD : 0 ≤ (a - d) ^ 2 + 4 * b * c := by nlinarith [sq_nonneg (a - d)]
  have hs0 : 0 ≤ √((a - d) ^ 2 + 4 * b * c) := Real.sqrt_nonneg _
  rw [spectralRadius_fin_two a b c d ha hd hbc,
    ENNReal.ofReal_eq_ofReal_iff (by linarith) (by linarith)]
  constructor
  · intro h
    have hs : √((a - d) ^ 2 + 4 * b * c) = a + d := by linarith
    rw [Real.sqrt_eq_iff_mul_self_eq hD (by linarith)] at hs
    nlinarith [hs]
  · intro h
    have hs : √((a - d) ^ 2 + 4 * b * c) = a + d := by
      rw [Real.sqrt_eq_iff_mul_self_eq hD (by linarith)]
      nlinarith [h]
    rw [hs]
    ring

/-- The two-layer multiplex next-generation matrix of `ngm.jl` for a single entry state:
`K_{ℓ ← m} = M_{mℓ} T_ℓ` with `M_{ℓℓ} = e_ℓ` (the excess degree `ψ_ℓ''(1)/ψ_ℓ'(1)` of layer ℓ),
`M_{mℓ} = k_ℓ` (the mean degree `ψ_ℓ'(1)` of layer ℓ, m ≠ ℓ) and `T_ℓ` the per-edge
transmissibility of layer ℓ: `K = [[T₁e₁, T₁k₁], [T₂k₂, T₂e₂]]`. -/
def multiplexNGM (T₁ T₂ k₁ k₂ e₁ e₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![T₁ * e₁, T₁ * k₁; T₂ * k₂, T₂ * e₂]

/-- **The two-layer multiplex R₀ = ρ(K) (L5).**

Design statement (DESIGN_NetworkEpiCore.md §D.7 table): "L5 (stretch) | R₀ | rank-one NGM for a
single entry state; 2-layer multiplex R₀ = ρ(K)"; §C.3, `MultiplexNetwork`: "R₀ = ρ(K)".

Lean statement: for all non-negative reals `T₁, T₂` (layer transmissibilities), `k₁, k₂` (layer
mean degrees) and `e₁, e₂` (layer excess degrees), the spectral radius of the two-layer
multiplex next-generation matrix `K = [[T₁e₁, T₁k₁], [T₂k₂, T₂e₂]]` is
`ρ(K) = (T₁e₁ + T₂e₂ + √((T₁e₁ − T₂e₂)² + 4T₁k₁T₂k₂))/2`.

Scope: the matrix is taken as given (`multiplexNGM`, as in `NetworkEpiCore.jl/src/analysis/ngm.jl`
for a single entry state, independent layers); its derivation from the multiplex EB model is not
formalised. -/
theorem multiplex_r0 (T₁ T₂ k₁ k₂ e₁ e₂ : ℝ) (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂) (hk₁ : 0 ≤ k₁)
    (hk₂ : 0 ≤ k₂) (he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂) :
    spectralRadius ℝ (multiplexNGM T₁ T₂ k₁ k₂ e₁ e₂) = ENNReal.ofReal
      ((T₁ * e₁ + T₂ * e₂ + √((T₁ * e₁ - T₂ * e₂) ^ 2 + 4 * (T₁ * k₁) * (T₂ * k₂))) / 2) :=
  spectralRadius_fin_two _ _ _ _ (mul_nonneg hT₁ he₁) (mul_nonneg hT₂ he₂)
    (mul_nonneg (mul_nonneg hT₁ hk₁) (mul_nonneg hT₂ hk₂))

/-- **The multiplex R₀ is the sum of the layer R₀s only in a degenerate case (L5).**

Design statement (DESIGN_NetworkEpiCore.md §D.7 table): "2-layer multiplex R₀ = ρ(K)";
`NetworkEpiCore.jl/src/analysis/ngm.jl`: "R₀ = ρ(K), **not** the sum of the layer R₀s (verified
issue E12)".

Lean statement: for all non-negative reals `T₁, T₂, k₁, k₂, e₁, e₂`, the spectral radius of
`K = [[T₁e₁, T₁k₁], [T₂k₂, T₂e₂]]` equals the sum `T₁e₁ + T₂e₂` of the single-layer R₀s if and
only if `(T₁k₁)(T₂k₂) = (T₁e₁)(T₂e₂)`; when `T₁T₂ ≠ 0` this is `k₁k₂ = e₁e₂` (mean degrees versus
excess degrees; for independent Poisson layers `k_ℓ = e_ℓ`, so the sum is then exact).

Scope: the matrix is taken as given (see `multiplex_r0`). -/
theorem multiplex_r0_eq_sum_iff (T₁ T₂ k₁ k₂ e₁ e₂ : ℝ) (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂)
    (hk₁ : 0 ≤ k₁) (hk₂ : 0 ≤ k₂) (he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂) :
    spectralRadius ℝ (multiplexNGM T₁ T₂ k₁ k₂ e₁ e₂) = ENNReal.ofReal (T₁ * e₁ + T₂ * e₂) ↔
      T₁ * k₁ * (T₂ * k₂) = T₁ * e₁ * (T₂ * e₂) :=
  spectralRadius_fin_two_eq_trace_iff _ _ _ _ (mul_nonneg hT₁ he₁) (mul_nonneg hT₂ he₂)
    (mul_nonneg (mul_nonneg hT₁ hk₁) (mul_nonneg hT₂ hk₂))

/-- **The two-layer multiplex R₀ = ρ(K), under the entry conditions of the closed form (L5).**

Design statement (DESIGN_NetworkEpiCore.md §D.7 table): "L5 (stretch) | R₀ | rank-one NGM for a
single entry state; 2-layer multiplex R₀ = ρ(K)"; §C.3, `MultiplexNetwork`: "R₀ = ρ(K)".

Lean statement: for all reals `T₁, T₂, k₁, k₂, e₁, e₂` such that the entries of the two-layer
multiplex next-generation matrix `K = [[T₁e₁, T₁k₁], [T₂k₂, T₂e₂]]` satisfy `T₁e₁ ≥ 0`,
`T₂e₂ ≥ 0` and `(T₁k₁)(T₂k₂) ≥ 0` (the conditions `a, d ≥ 0`, `bc ≥ 0` of
`spectralRadius_fin_two`; for example all six parameters non-negative), the spectral radius is
`ρ(K) = (T₁e₁ + T₂e₂ + √((T₁e₁ − T₂e₂)² + 4T₁k₁T₂k₂))/2`. -/
theorem multiplex_r0_of_entries (T₁ T₂ k₁ k₂ e₁ e₂ : ℝ) (ha : 0 ≤ T₁ * e₁) (hd : 0 ≤ T₂ * e₂)
    (hbc : 0 ≤ (T₁ * k₁) * (T₂ * k₂)) :
    spectralRadius ℝ (multiplexNGM T₁ T₂ k₁ k₂ e₁ e₂) = ENNReal.ofReal
      ((T₁ * e₁ + T₂ * e₂ + √((T₁ * e₁ - T₂ * e₂) ^ 2 + 4 * (T₁ * k₁) * (T₂ * k₂))) / 2) :=
  spectralRadius_fin_two _ _ _ _ ha hd hbc

/-- **The multiplex R₀ is the sum of the layer R₀s iff `T₁T₂k₁k₂ = T₁T₂e₁e₂` (L5).**

Design statement (DESIGN_NetworkEpiCore.md §D.7 table): "2-layer multiplex R₀ = ρ(K)";
`NetworkEpiCore.jl/src/analysis/ngm.jl`: "R₀ = ρ(K), **not** the sum of the layer R₀s (verified
issue E12)".

Lean statement: for all reals `T₁, T₂, k₁, k₂, e₁, e₂` with `T₁e₁ ≥ 0`, `T₂e₂ ≥ 0` and
`(T₁k₁)(T₂k₂) ≥ 0` (the entry conditions of the closed form), the spectral radius of
`K = [[T₁e₁, T₁k₁], [T₂k₂, T₂e₂]]` equals `T₁e₁ + T₂e₂` if and only if
`T₁T₂k₁k₂ = T₁T₂e₁e₂`. -/
theorem multiplex_r0_eq_sum_iff_of_entries (T₁ T₂ k₁ k₂ e₁ e₂ : ℝ) (ha : 0 ≤ T₁ * e₁)
    (hd : 0 ≤ T₂ * e₂) (hbc : 0 ≤ (T₁ * k₁) * (T₂ * k₂)) :
    spectralRadius ℝ (multiplexNGM T₁ T₂ k₁ k₂ e₁ e₂) = ENNReal.ofReal (T₁ * e₁ + T₂ * e₂) ↔
      T₁ * T₂ * k₁ * k₂ = T₁ * T₂ * e₁ * e₂ := by
  rw [multiplexNGM, spectralRadius_fin_two_eq_trace_iff _ _ _ _ ha hd hbc]
  constructor <;> intro h <;> linarith

end TwoByTwo

end NEP
