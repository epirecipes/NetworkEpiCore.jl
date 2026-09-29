import Alignment.Registry
import Alignment.Shadows.MorphismsNGM

/-!
# Checkers: group `MorphismsNGM` (trusted module `NetworkEpi.Morphisms.NGM`)

Checker author (SA-PASS role 3, non-blind). For each of the ten `implemented` claims of
`NetworkEpi/Morphisms/NGM.lean` this file holds the `sa_claim` registration (verbatim registry
text, registry `impl` list in registry order), the structural forward checkers `sa_impl% → Sᵢ`,
the backward checker `S₁ → … → Sₙ → sa_impl%`, and an `sa_fail_*` record wherever a check is not
derivable. The non-required entries `MorphismsNGM.header.r0Definition` (informal) and
`MorphismsNGM.header.ngmDerivation` (missing, declared scope gap) are not registered.

No bridges are declared: the only trusted definition, `NEP.multiplexNGM`, occurs identically in
the shadows and the implementations; all other notions are Mathlib's. The remaining gaps are
claimed text the implementation omits, not notions to identify, so no bridge applies.

Universes: the trusted module now declares `variable {n : Type*}`, so the general-`n` impls are
universe-polymorphic (`.{u_1}`), as are the blind shadows (`.{u}`). Checkers state `Sᵢ.{u_1}`.

No failures are recorded for `spectralRadiusVecMulVec` (impl now the spectral radius alone) or
`r0SingleEntry` (impl now also `NEP.r0_single_entry_rank_one`, the rank-one conjunct).

Re-shadowed claims after the registry remediation (`r0SingleEntry` → `NEP.r0_single_entry_rank`,
`multiplexR0` → `NEP.multiplex_r0_of_entries`, `multiplexR0EqSumIff` →
`NEP.multiplex_r0_eq_sum_iff_of_entries`, `memSpectrumIffDet` → `NEP.mem_spectrum_iff_det_smul`):
all other checks of these four claims are structural (instantiation, projection, `rw [hF]`).
-/

open NEP Matrix

universe u_1

/-! ## `MorphismsNGM.spectralRadiusVecMulVec` -/

namespace Alignment.Shadows.MorphismsNGM.SpectralRadiusVecMulVec

sa_claim "MorphismsNGM.spectralRadiusVecMulVec" group "MorphismsNGM" required
  text "**The spectral radius of a rank-one matrix (L5).** Design statement (DESIGN_NetworkEpiCore.md §D.7 table): \"L5 (stretch) | R₀ | rank-one NGM for a single entry state\". [...] a rank-one matrix `u vᵀ` (`u ≠ 0`) has real spectrum inside `{0, v·u}` containing `v·u`, so its spectral radius is `|v·u|`."
  impl NEP.spectralRadius_vecMulVec

@[sa_forward "MorphismsNGM.spectralRadiusVecMulVec" 1]
theorem fwd1 (h : sa_impl% "MorphismsNGM.spectralRadiusVecMulVec") : S1.{u_1} := by
  intro n _ _ u v hu
  exact h u v hu

@[sa_backward "MorphismsNGM.spectralRadiusVecMulVec"]
theorem bwd (s1 : S1.{u_1}) : sa_impl% "MorphismsNGM.spectralRadiusVecMulVec" := by
  intro n _ _ u v hu
  exact s1 u v hu


end Alignment.Shadows.MorphismsNGM.SpectralRadiusVecMulVec

/-! ## `MorphismsNGM.r0SingleEntry` -/

namespace Alignment.Shadows.MorphismsNGM.R0SingleEntry

sa_claim "MorphismsNGM.r0SingleEntry" group "MorphismsNGM" required
  text "**R₀ for a single entry state: the next-generation matrix `e_E (wᵀV⁻¹)` has rank at most one (L5).** Design statement (DESIGN_NetworkEpiCore.md §D.7 table): \"L5 (stretch) | R₀ | rank-one NGM for a single entry state; 2-layer multiplex R₀ = ρ(K)\"; amended by §M.2: \"for a single entry state E the next-generation matrix K = F V⁻¹ = e_E (wᵀV⁻¹) has rank at most one (rank one unless wᵀV⁻¹ = 0), and R₀ = ρ(K) = |(wᵀV⁻¹)_E|\". [...] if every new infection enters one state `E` (`F = e_E wᵀ`), the next-generation matrix `K = F V⁻¹ = e_E (wᵀV⁻¹)` has rank at most one and `R₀ = ρ(K) = |(wᵀV⁻¹)_E|`"
  impl NEP.r0_single_entry_rank NEP.r0_single_entry_rank_one

@[sa_forward "MorphismsNGM.r0SingleEntry" 1]
theorem fwd1 (h : sa_impl% "MorphismsNGM.r0SingleEntry") : S1.{u_1} := by
  intro n _ _ E w V F hF
  rw [hF]
  exact (h.1 E w V).1

@[sa_forward "MorphismsNGM.r0SingleEntry" 2]
theorem fwd2 (h : sa_impl% "MorphismsNGM.r0SingleEntry") : S2.{u_1} := by
  intro n _ _ E w V F hF
  rw [hF]
  exact (h.1 E w V).2.1

@[sa_forward "MorphismsNGM.r0SingleEntry" 3]
theorem fwd3 (h : sa_impl% "MorphismsNGM.r0SingleEntry") : S3.{u_1} := by
  intro n _ _ E w V F hF hne
  rw [hF]
  exact h.2 E w V hne

@[sa_forward "MorphismsNGM.r0SingleEntry" 4]
theorem fwd4 (h : sa_impl% "MorphismsNGM.r0SingleEntry") : S4.{u_1} := by
  intro n _ _ E w V F hF
  rw [hF]
  exact (h.1 E w V).2.2

@[sa_backward "MorphismsNGM.r0SingleEntry"]
theorem bwd (s1 : S1.{u_1}) (s2 : S2.{u_1}) (s3 : S3.{u_1}) (s4 : S4.{u_1}) :
    sa_impl% "MorphismsNGM.r0SingleEntry" := by
  refine ⟨?_, ?_⟩
  · intro n _ _ E w V
    exact ⟨s1 E w V (vecMulVec (Pi.single E 1) w) rfl, s2 E w V (vecMulVec (Pi.single E 1) w) rfl,
      s4 E w V (vecMulVec (Pi.single E 1) w) rfl⟩
  · intro n _ _ E w V hne
    exact s3 E w V (vecMulVec (Pi.single E 1) w) rfl hne

end Alignment.Shadows.MorphismsNGM.R0SingleEntry

/-! ## `MorphismsNGM.spectralRadiusFinTwo`

The shadow is literally the impl statement. -/

namespace Alignment.Shadows.MorphismsNGM.SpectralRadiusFinTwo

sa_claim "MorphismsNGM.spectralRadiusFinTwo" group "MorphismsNGM" required
  text "**The spectral radius of a non-negative 2 × 2 matrix (L5).** Design statement (DESIGN_NetworkEpiCore.md §D.7 table): \"2-layer multiplex R₀ = ρ(K)\". [...] for a 2 × 2 matrix `[[a, b], [c, d]]` with `a, d ≥ 0` and `bc ≥ 0` (for example a non-negative NGM), `ρ = (a + d + √((a − d)² + 4bc))/2`."
  impl NEP.spectralRadius_fin_two

@[sa_forward "MorphismsNGM.spectralRadiusFinTwo" 1]
theorem fwd1 (h : sa_impl% "MorphismsNGM.spectralRadiusFinTwo") : S1 :=
  fun a b c d ha hd hbc => h a b c d ha hd hbc

@[sa_backward "MorphismsNGM.spectralRadiusFinTwo"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsNGM.spectralRadiusFinTwo" :=
  fun a b c d ha hd hbc => s1 a b c d ha hd hbc

end Alignment.Shadows.MorphismsNGM.SpectralRadiusFinTwo

/-! ## `MorphismsNGM.multiplexR0` -/

namespace Alignment.Shadows.MorphismsNGM.MultiplexR0

sa_claim "MorphismsNGM.multiplexR0" group "MorphismsNGM" required
  text "**The two-layer multiplex R₀ = ρ(K) (L5).** Design statement (DESIGN_NetworkEpiCore.md §D.7 table): \"L5 (stretch) | R₀ | rank-one NGM for a single entry state; 2-layer multiplex R₀ = ρ(K)\"; §C.3, `MultiplexNetwork`: \"R₀ = ρ(K)\". [...] with `a, d ≥ 0` and `bc ≥ 0` (for example a non-negative NGM), `ρ = (a + d + √((a − d)² + 4bc))/2`. [...] for the two-layer multiplex NGM `K = [[T₁e₁, T₁k₁], [T₂k₂, T₂e₂]]` (as in `ngm.jl`: `M_ℓℓ = κ_ex,ℓ`, `M_mℓ = ⟨k_ℓ⟩`), `R₀ = ρ(K)` has the closed form above"
  impl NEP.multiplex_r0_of_entries

@[sa_forward "MorphismsNGM.multiplexR0" 1]
theorem fwd1 (h : sa_impl% "MorphismsNGM.multiplexR0") : S1 :=
  fun T₁ T₂ k₁ k₂ e₁ e₂ ha hd hbc => h T₁ T₂ k₁ k₂ e₁ e₂ ha hd hbc

@[sa_backward "MorphismsNGM.multiplexR0"]
theorem bwd (s1 : S1) : sa_impl% "MorphismsNGM.multiplexR0" :=
  fun T₁ T₂ k₁ k₂ e₁ e₂ ha hd hbc => s1 T₁ T₂ k₁ k₂ e₁ e₂ ha hd hbc

end Alignment.Shadows.MorphismsNGM.MultiplexR0

/-! ## `MorphismsNGM.multiplexR0EqSumIff` -/

namespace Alignment.Shadows.MorphismsNGM.MultiplexR0EqSumIff

sa_claim "MorphismsNGM.multiplexR0EqSumIff" group "MorphismsNGM" required
  text "**The multiplex R₀ is the sum of the layer R₀s only in a degenerate case (L5).** Design statement (DESIGN_NetworkEpiCore.md §D.7 table): \"2-layer multiplex R₀ = ρ(K)\"; `NetworkEpiCore.jl/src/analysis/ngm.jl`: \"R₀ = ρ(K), **not** the sum of the layer R₀s (verified issue E12)\". [...] for the two-layer multiplex NGM `K = [[T₁e₁, T₁k₁], [T₂k₂, T₂e₂]]` (as in `ngm.jl`: `M_ℓℓ = κ_ex,ℓ`, `M_mℓ = ⟨k_ℓ⟩`), [...] it equals the sum `T₁e₁ + T₂e₂` of the layer R₀s iff `T₁T₂k₁k₂ = T₁T₂e₁e₂`."
  impl NEP.multiplex_r0_eq_sum_iff_of_entries

@[sa_forward "MorphismsNGM.multiplexR0EqSumIff" 1]
theorem fwd1 (h : sa_impl% "MorphismsNGM.multiplexR0EqSumIff") : S1 :=
  fun T₁ T₂ k₁ k₂ e₁ e₂ ha hd hbc => (h T₁ T₂ k₁ k₂ e₁ e₂ ha hd hbc).mp

@[sa_forward "MorphismsNGM.multiplexR0EqSumIff" 2]
theorem fwd2 (h : sa_impl% "MorphismsNGM.multiplexR0EqSumIff") : S2 :=
  fun T₁ T₂ k₁ k₂ e₁ e₂ ha hd hbc => (h T₁ T₂ k₁ k₂ e₁ e₂ ha hd hbc).mpr

@[sa_backward "MorphismsNGM.multiplexR0EqSumIff"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "MorphismsNGM.multiplexR0EqSumIff" :=
  fun T₁ T₂ k₁ k₂ e₁ e₂ ha hd hbc =>
    ⟨s1 T₁ T₂ k₁ k₂ e₁ e₂ ha hd hbc, s2 T₁ T₂ k₁ k₂ e₁ e₂ ha hd hbc⟩

end Alignment.Shadows.MorphismsNGM.MultiplexR0EqSumIff

/-! ## `MorphismsNGM.memSpectrumIffDet` -/

namespace Alignment.Shadows.MorphismsNGM.MemSpectrumIffDet

sa_claim "MorphismsNGM.memSpectrumIffDet" group "MorphismsNGM" required
  text "`r` is in the real spectrum of `K` iff `det(r·1 − K) = 0`."
  impl NEP.mem_spectrum_iff_det_smul

@[sa_forward "MorphismsNGM.memSpectrumIffDet" 1]
theorem fwd1 (h : sa_impl% "MorphismsNGM.memSpectrumIffDet") : S1.{u_1} := by
  intro n _ _ K r
  exact (h K r).mp

@[sa_forward "MorphismsNGM.memSpectrumIffDet" 2]
theorem fwd2 (h : sa_impl% "MorphismsNGM.memSpectrumIffDet") : S2.{u_1} := by
  intro n _ _ K r
  exact (h K r).mpr

@[sa_backward "MorphismsNGM.memSpectrumIffDet"]
theorem bwd (s1 : S1.{u_1}) (s2 : S2.{u_1}) : sa_impl% "MorphismsNGM.memSpectrumIffDet" := by
  intro n _ _ K r
  exact ⟨s1 K r, s2 K r⟩

end Alignment.Shadows.MorphismsNGM.MemSpectrumIffDet

/-! ## `MorphismsNGM.spectrumVecMulVecSubset` -/

namespace Alignment.Shadows.MorphismsNGM.SpectrumVecMulVecSubset

sa_claim "MorphismsNGM.spectrumVecMulVecSubset" group "MorphismsNGM" required
  text "The real spectrum of the rank-one matrix `u vᵀ` lies in `{0, v·u}`."
  impl NEP.spectrum_vecMulVec_subset

@[sa_forward "MorphismsNGM.spectrumVecMulVecSubset" 1]
theorem fwd1 (h : sa_impl% "MorphismsNGM.spectrumVecMulVecSubset") : S1.{u_1} := by
  intro n _ _ u v
  exact h u v

@[sa_backward "MorphismsNGM.spectrumVecMulVecSubset"]
theorem bwd (s1 : S1.{u_1}) : sa_impl% "MorphismsNGM.spectrumVecMulVecSubset" := by
  intro n _ _ u v
  exact s1 u v

end Alignment.Shadows.MorphismsNGM.SpectrumVecMulVecSubset

/-! ## `MorphismsNGM.memSpectrumVecMulVec` -/

namespace Alignment.Shadows.MorphismsNGM.MemSpectrumVecMulVec

sa_claim "MorphismsNGM.memSpectrumVecMulVec" group "MorphismsNGM" required
  text "`v·u` is in the real spectrum of `u vᵀ` when `u ≠ 0` (`u` is an eigenvector)."
  impl NEP.mem_spectrum_vecMulVec

@[sa_forward "MorphismsNGM.memSpectrumVecMulVec" 1]
theorem fwd1 (h : sa_impl% "MorphismsNGM.memSpectrumVecMulVec") : S1.{u_1} := by
  intro n _ _ u v hu
  exact h u v hu

@[sa_backward "MorphismsNGM.memSpectrumVecMulVec"]
theorem bwd (s1 : S1.{u_1}) : sa_impl% "MorphismsNGM.memSpectrumVecMulVec" := by
  intro n _ _ u v hu
  exact s1 u v hu

end Alignment.Shadows.MorphismsNGM.MemSpectrumVecMulVec

/-! ## `MorphismsNGM.spectrumFinTwo`

The impl is the set equality; the shadows are its two inclusions. Membership in a set is
function application, so the backward direction is `funext` + `propext`. -/

namespace Alignment.Shadows.MorphismsNGM.SpectrumFinTwo

sa_claim "MorphismsNGM.spectrumFinTwo" group "MorphismsNGM" required
  text "The real spectrum of a 2 × 2 matrix with non-negative discriminant `D = (a − d)² + 4bc`: the two roots `(a + d ± √D)/2` of `λ² − (a + d)λ + (ad − bc)`."
  impl NEP.spectrum_fin_two

@[sa_forward "MorphismsNGM.spectrumFinTwo" 1]
theorem fwd1 (h : sa_impl% "MorphismsNGM.spectrumFinTwo") : S1 := by
  intro a b c d hD x hx
  exact Eq.mp (congrArg (fun s : Set ℝ => x ∈ s) (h a b c d hD)) hx

@[sa_forward "MorphismsNGM.spectrumFinTwo" 2]
theorem fwd2 (h : sa_impl% "MorphismsNGM.spectrumFinTwo") : S2 := by
  intro a b c d hD x hx
  exact Eq.mpr (congrArg (fun s : Set ℝ => x ∈ s) (h a b c d hD)) hx

@[sa_backward "MorphismsNGM.spectrumFinTwo"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "MorphismsNGM.spectrumFinTwo" := by
  intro a b c d hD
  exact funext fun x => propext ⟨fun hx => s1 a b c d hD hx, fun hx => s2 a b c d hD hx⟩

end Alignment.Shadows.MorphismsNGM.SpectrumFinTwo

/-! ## `MorphismsNGM.spectralRadiusFinTwoEqTraceIff` -/

namespace Alignment.Shadows.MorphismsNGM.SpectralRadiusFinTwoEqTraceIff

sa_claim "MorphismsNGM.spectralRadiusFinTwoEqTraceIff" group "MorphismsNGM" required
  text "For real `a, d ≥ 0`, `bc ≥ 0`: the spectral radius of `[[a, b], [c, d]]` is the trace `a + d` iff `bc = ad` (the determinant vanishes)."
  impl NEP.spectralRadius_fin_two_eq_trace_iff

@[sa_forward "MorphismsNGM.spectralRadiusFinTwoEqTraceIff" 1]
theorem fwd1 (h : sa_impl% "MorphismsNGM.spectralRadiusFinTwoEqTraceIff") : S1 :=
  fun a b c d ha hd hbc => (h a b c d ha hd hbc).mp

@[sa_forward "MorphismsNGM.spectralRadiusFinTwoEqTraceIff" 2]
theorem fwd2 (h : sa_impl% "MorphismsNGM.spectralRadiusFinTwoEqTraceIff") : S2 :=
  fun a b c d ha hd hbc => (h a b c d ha hd hbc).mpr

@[sa_backward "MorphismsNGM.spectralRadiusFinTwoEqTraceIff"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "MorphismsNGM.spectralRadiusFinTwoEqTraceIff" :=
  fun a b c d ha hd hbc => ⟨s1 a b c d ha hd hbc, s2 a b c d ha hd hbc⟩

end Alignment.Shadows.MorphismsNGM.SpectralRadiusFinTwoEqTraceIff
