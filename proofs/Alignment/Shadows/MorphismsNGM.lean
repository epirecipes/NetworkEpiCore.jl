import Alignment.Registry
import NetworkEpi.Morphisms.NGM

/-!
# Blind shadow sets — group `MorphismsNGM` (`NetworkEpi.Morphisms.NGM`, DESIGN §D.7 row L5)

Written blind: from the entries in `Alignment/claims_blind.yaml`, `Alignment/DataTypes/MorphismsNGM.md`,
`Alignment/README.md`, `Alignment/Example/ExampleShadows.lean` and DESIGN_NetworkEpiCore.md
(§C.3 `MultiplexNetwork`, §D.7 table row L5).

Notation (DataTypes §e): R₀ = ρ(K) is `spectralRadius ℝ K : ENNReal`; a non-negative real value `r`
is compared as `ENNReal.ofReal r`, `|x|` as `(‖x‖₊ : ENNReal)`; `u vᵀ` is `vecMulVec u v`; `v·u` is
`v ⬝ᵥ u`; `e_E` is `Pi.single E 1`; `wᵀV⁻¹` is `w ᵥ* V⁻¹`; `[[a, b], [c, d]]` is `!![a, b; c, d]`;
the two-layer multiplex NGM is `multiplexNGM T₁ T₂ k₁ k₂ e₁ e₂`.

General conventions of this file:
* The texts speak of arbitrary (finite) matrices, so general-`n` statements quantify over every
  finite index type `n : Type u` with decidable equality, universe-polymorphically.
  -- AMBIGUITY: universe of the index type is not in the text; the most general reading is taken.
* Most claims of this module are about Mathlib notions only (the module imports no epidemic data
  types), so their shadows cannot mention a trusted constant without doing so trivially (forbidden,
  README limitation 10). They are expected to be flagged `shadow_trusted_free` and need a reviewer's
  `sa_shadow_reviewed` record; only the `multiplexNGM` claims mention a trusted constant.
-/

open NEP Matrix

universe u

/-! ## `MorphismsNGM.spectralRadiusVecMulVec`

Text: "a rank-one matrix `u vᵀ` (`u ≠ 0`) has real spectrum inside `{0, v·u}` containing `v·u`, so
its spectral radius is `|v·u|`." (title: "The spectral radius of a rank-one matrix (L5).")

-- AMBIGUITY: the sentence first recalls the spectrum facts (registered separately as
-- `MorphismsNGM.spectrumVecMulVecSubset` and `MorphismsNGM.memSpectrumVecMulVec`) and then concludes
-- "so its spectral radius is |v·u|"; the theorem's title is the spectral radius. The claim is read
-- as the conclusion: for `u ≠ 0`, ρ(u vᵀ) = |v·u|. -/
namespace Alignment.Shadows.MorphismsNGM.SpectralRadiusVecMulVec

/-- Intended statement: for every finite index type and all real vectors `u ≠ 0`, `v`,
the spectral radius of `u vᵀ` is `|v·u|`. -/
@[sa_reference "MorphismsNGM.spectralRadiusVecMulVec"]
def T : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n] (u v : n → ℝ), u ≠ 0 →
    spectralRadius ℝ (vecMulVec u v) = (‖v ⬝ᵥ u‖₊ : ENNReal)

/-- S1: ρ(u vᵀ) = |v·u| for `u ≠ 0` (a single atomic requirement). -/
@[sa_shadow "MorphismsNGM.spectralRadiusVecMulVec" 1]
def S1 : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n] (u v : n → ℝ), u ≠ 0 →
    spectralRadius ℝ (vecMulVec u v) = (‖v ⬝ᵥ u‖₊ : ENNReal)

@[sa_ref_forward "MorphismsNGM.spectralRadiusVecMulVec" 1]
theorem ref_fwd1 : T.{u} → S1.{u} := fun t => t

@[sa_complete "MorphismsNGM.spectralRadiusVecMulVec"]
theorem complete (s1 : S1.{u}) : T.{u} := s1

end Alignment.Shadows.MorphismsNGM.SpectralRadiusVecMulVec

/-! ## `MorphismsNGM.r0SingleEntry`

Text (title): "R₀ for a single entry state: the next-generation matrix `e_E (wᵀV⁻¹)` has rank at most
one (L5)." Design statement (§M.2): "for a single entry state E the next-generation matrix
K = F V⁻¹ = e_E (wᵀV⁻¹) has rank at most one (rank one unless wᵀV⁻¹ = 0), and
R₀ = ρ(K) = |(wᵀV⁻¹)_E|". Module text: "if every new infection enters one state `E` (`F = e_E wᵀ`),
the next-generation matrix `K = F V⁻¹ = e_E (wᵀV⁻¹)` has rank at most one and
`R₀ = ρ(K) = |(wᵀV⁻¹)_E|`".

Four requirements (conjunction), for every finite index type, entry state `E`, vector `w`,
matrix `V` and `F = e_E wᵀ`:
(1) `K = F V⁻¹ = e_E (wᵀV⁻¹)` (`vecMulVec (Pi.single E 1) (w ᵥ* V⁻¹)`);
(2) `rank K ≤ 1` (`Matrix.rank`);
(3) `rank K = 1` when `wᵀV⁻¹ ≠ 0` ("rank one unless wᵀV⁻¹ = 0");
(4) `ρ(K) = |(wᵀV⁻¹)_E|`.
-- AMBIGUITY: "(rank one unless wᵀV⁻¹ = 0)" appears only in the design statement (§M.2), which the
-- docstring quotes as the binding amendment; it is read as a requirement (3). Its converse
-- (rank 0 when wᵀV⁻¹ = 0) follows from (1) and is not stated separately.
-- AMBIGUITY: the text puts no hypothesis on `V` (no invertibility); `V⁻¹` is Mathlib's inverse
-- (zero when `V` is singular), so no hypothesis is added. `F` is quantified with the defining
-- equation `F = e_E wᵀ` as a hypothesis, as the text states it ("if … (`F = e_E wᵀ`)"). -/
namespace Alignment.Shadows.MorphismsNGM.R0SingleEntry

/-- Intended statement: for every finite index type, entry state `E`, vector `w`, matrix `V`,
and `F = e_E wᵀ`: `F V⁻¹ = e_E (wᵀV⁻¹)`, `rank (F V⁻¹) ≤ 1`, `rank (F V⁻¹) = 1` when
`wᵀV⁻¹ ≠ 0`, and `ρ(F V⁻¹) = |(wᵀV⁻¹)_E|`. -/
@[sa_reference "MorphismsNGM.r0SingleEntry"]
def T : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n] (E : n) (w : n → ℝ) (V F : Matrix n n ℝ),
    F = vecMulVec (Pi.single E 1) w →
      F * V⁻¹ = vecMulVec (Pi.single E 1) (w ᵥ* V⁻¹) ∧
      (F * V⁻¹).rank ≤ 1 ∧
      (w ᵥ* V⁻¹ ≠ 0 → (F * V⁻¹).rank = 1) ∧
      spectralRadius ℝ (F * V⁻¹) = (‖(w ᵥ* V⁻¹) E‖₊ : ENNReal)

/-- S1: the next-generation matrix `K = F V⁻¹` is `e_E (wᵀV⁻¹)`. -/
@[sa_shadow "MorphismsNGM.r0SingleEntry" 1]
def S1 : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n] (E : n) (w : n → ℝ) (V F : Matrix n n ℝ),
    F = vecMulVec (Pi.single E 1) w →
      F * V⁻¹ = vecMulVec (Pi.single E 1) (w ᵥ* V⁻¹)

/-- S2: `K = F V⁻¹` has rank at most one. -/
@[sa_shadow "MorphismsNGM.r0SingleEntry" 2]
def S2 : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n] (E : n) (w : n → ℝ) (V F : Matrix n n ℝ),
    F = vecMulVec (Pi.single E 1) w →
      (F * V⁻¹).rank ≤ 1

/-- S3: `K = F V⁻¹` has rank exactly one unless `wᵀV⁻¹ = 0`. -/
@[sa_shadow "MorphismsNGM.r0SingleEntry" 3]
def S3 : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n] (E : n) (w : n → ℝ) (V F : Matrix n n ℝ),
    F = vecMulVec (Pi.single E 1) w →
      w ᵥ* V⁻¹ ≠ 0 → (F * V⁻¹).rank = 1

/-- S4: `R₀ = ρ(F V⁻¹) = |(wᵀV⁻¹)_E|`. -/
@[sa_shadow "MorphismsNGM.r0SingleEntry" 4]
def S4 : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n] (E : n) (w : n → ℝ) (V F : Matrix n n ℝ),
    F = vecMulVec (Pi.single E 1) w →
      spectralRadius ℝ (F * V⁻¹) = (‖(w ᵥ* V⁻¹) E‖₊ : ENNReal)

@[sa_ref_forward "MorphismsNGM.r0SingleEntry" 1]
theorem ref_fwd1 : T.{u} → S1.{u} := by
  intro t n _ _ E w V F hF
  exact (t E w V F hF).1

@[sa_ref_forward "MorphismsNGM.r0SingleEntry" 2]
theorem ref_fwd2 : T.{u} → S2.{u} := by
  intro t n _ _ E w V F hF
  exact (t E w V F hF).2.1

@[sa_ref_forward "MorphismsNGM.r0SingleEntry" 3]
theorem ref_fwd3 : T.{u} → S3.{u} := by
  intro t n _ _ E w V F hF
  exact (t E w V F hF).2.2.1

@[sa_ref_forward "MorphismsNGM.r0SingleEntry" 4]
theorem ref_fwd4 : T.{u} → S4.{u} := by
  intro t n _ _ E w V F hF
  exact (t E w V F hF).2.2.2

@[sa_complete "MorphismsNGM.r0SingleEntry"]
theorem complete (s1 : S1.{u}) (s2 : S2.{u}) (s3 : S3.{u}) (s4 : S4.{u}) : T.{u} := by
  intro n _ _ E w V F hF
  exact ⟨s1 E w V F hF, s2 E w V F hF, s3 E w V F hF, s4 E w V F hF⟩

end Alignment.Shadows.MorphismsNGM.R0SingleEntry

/-! ## `MorphismsNGM.spectralRadiusFinTwo`

Text: "for a 2 × 2 matrix `[[a, b], [c, d]]` with `a, d ≥ 0` and `bc ≥ 0` (for example a non-negative
NGM), `ρ = (a + d + √((a − d)² + 4bc))/2`." -/
namespace Alignment.Shadows.MorphismsNGM.SpectralRadiusFinTwo

/-- Intended statement: for all reals with `a ≥ 0`, `d ≥ 0`, `bc ≥ 0`,
`ρ([[a, b], [c, d]]) = (a + d + √((a − d)² + 4bc))/2`. -/
@[sa_reference "MorphismsNGM.spectralRadiusFinTwo"]
def T : Prop :=
  ∀ a b c d : ℝ, 0 ≤ a → 0 ≤ d → 0 ≤ b * c →
    spectralRadius ℝ !![a, b; c, d] = ENNReal.ofReal ((a + d + √((a - d) ^ 2 + 4 * b * c)) / 2)

/-- S1: the closed form (a single atomic requirement). -/
@[sa_shadow "MorphismsNGM.spectralRadiusFinTwo" 1]
def S1 : Prop :=
  ∀ a b c d : ℝ, 0 ≤ a → 0 ≤ d → 0 ≤ b * c →
    spectralRadius ℝ !![a, b; c, d] = ENNReal.ofReal ((a + d + √((a - d) ^ 2 + 4 * b * c)) / 2)

@[sa_ref_forward "MorphismsNGM.spectralRadiusFinTwo" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MorphismsNGM.spectralRadiusFinTwo"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MorphismsNGM.SpectralRadiusFinTwo

/-! ## `MorphismsNGM.multiplexR0`

Text: "**The two-layer multiplex R₀ = ρ(K) (L5).** Design statement: \"… 2-layer multiplex
R₀ = ρ(K)\"; §C.3, `MultiplexNetwork`: \"R₀ = ρ(K)\". [...] with `a, d ≥ 0` and `bc ≥ 0` (for example
a non-negative NGM), `ρ = (a + d + √((a − d)² + 4bc))/2`. [...] for the two-layer multiplex NGM
`K = [[T₁e₁, T₁k₁], [T₂k₂, T₂e₂]]` (as in `ngm.jl`: `M_ℓℓ = κ_ex,ℓ`, `M_mℓ = ⟨k_ℓ⟩`), `R₀ = ρ(K)` has
the closed form above".

"R₀ = ρ(K)" fixes the notion (R₀ is `spectralRadius ℝ K`, DataTypes §e); the requirement is the
closed form. With `a = T₁e₁`, `b = T₁k₁`, `c = T₂k₂`, `d = T₂e₂` the closed form's conditions are
`T₁e₁ ≥ 0`, `T₂e₂ ≥ 0` and `(T₁k₁)(T₂k₂) ≥ 0`; `K` is `multiplexNGM T₁ T₂ k₁ k₂ e₁ e₂`
(DataTypes §c/§e).
-- AMBIGUITY: "with `a, d ≥ 0` and `bc ≥ 0` (for example a non-negative NGM)": the conditions are on
-- the entries, a non-negative NGM being only an example; so the hypotheses are stated on the
-- entries (the most general reading), not as non-negativity of all six parameters.
-- The identification `multiplexNGM … = [[T₁e₁, T₁k₁], [T₂k₂, T₂e₂]]` is a definitional fact
-- (a bridge matter), not a separate shadow. -/
namespace Alignment.Shadows.MorphismsNGM.MultiplexR0

/-- Intended statement: for all real parameters with `T₁e₁ ≥ 0`, `T₂e₂ ≥ 0`, `(T₁k₁)(T₂k₂) ≥ 0`,
the multiplex `R₀ = ρ(multiplexNGM T₁ T₂ k₁ k₂ e₁ e₂)` equals
`(T₁e₁ + T₂e₂ + √((T₁e₁ − T₂e₂)² + 4(T₁k₁)(T₂k₂)))/2`. -/
@[sa_reference "MorphismsNGM.multiplexR0"]
def T : Prop :=
  ∀ T₁ T₂ k₁ k₂ e₁ e₂ : ℝ, 0 ≤ T₁ * e₁ → 0 ≤ T₂ * e₂ → 0 ≤ (T₁ * k₁) * (T₂ * k₂) →
    spectralRadius ℝ (multiplexNGM T₁ T₂ k₁ k₂ e₁ e₂) =
      ENNReal.ofReal
        ((T₁ * e₁ + T₂ * e₂ + √((T₁ * e₁ - T₂ * e₂) ^ 2 + 4 * (T₁ * k₁) * (T₂ * k₂))) / 2)

/-- S1: the closed form (a single atomic requirement). -/
@[sa_shadow "MorphismsNGM.multiplexR0" 1]
def S1 : Prop :=
  ∀ T₁ T₂ k₁ k₂ e₁ e₂ : ℝ, 0 ≤ T₁ * e₁ → 0 ≤ T₂ * e₂ → 0 ≤ (T₁ * k₁) * (T₂ * k₂) →
    spectralRadius ℝ (multiplexNGM T₁ T₂ k₁ k₂ e₁ e₂) =
      ENNReal.ofReal
        ((T₁ * e₁ + T₂ * e₂ + √((T₁ * e₁ - T₂ * e₂) ^ 2 + 4 * (T₁ * k₁) * (T₂ * k₂))) / 2)

@[sa_ref_forward "MorphismsNGM.multiplexR0" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MorphismsNGM.multiplexR0"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MorphismsNGM.MultiplexR0

/-! ## `MorphismsNGM.multiplexR0EqSumIff`

Text: "**The multiplex R₀ is the sum of the layer R₀s only in a degenerate case (L5).** Design
statement: \"2-layer multiplex R₀ = ρ(K)\"; `ngm.jl`: \"R₀ = ρ(K), **not** the sum of the layer R₀s
(verified issue E12)\". [...] for the two-layer multiplex NGM `K = [[T₁e₁, T₁k₁], [T₂k₂, T₂e₂]]` (as
in `ngm.jl`: `M_ℓℓ = κ_ex,ℓ`, `M_mℓ = ⟨k_ℓ⟩`), [...] it equals the sum `T₁e₁ + T₂e₂` of the layer R₀s
iff `T₁T₂k₁k₂ = T₁T₂e₁e₂`."

"it" is the multiplex `R₀ = ρ(K)`; the layer R₀s are `T₁e₁`, `T₂e₂` (DataTypes §e); the sum is a
real number compared as `ENNReal.ofReal (T₁e₁ + T₂e₂)` (DataTypes §e). Split along the iff.
-- AMBIGUITY: the quoted fragments carry no hypothesis, but without one the iff is false
-- (e.g. `T₁ = 1, e₁ = -1, k₁ = 0, e₂ = 0`: `K = [[-1, 0], [T₂k₂, 0]]`, ρ(K) = 1 ≠ ofReal(-1) = 0,
-- while `T₁T₂k₁k₂ = T₁T₂e₁e₂ = 0`). The elided "[...]" is "`R₀ = ρ(K)` has the closed form above",
-- the closed form stated under `a, d ≥ 0`, `bc ≥ 0` on the entries; "it" is read as R₀ under those
-- conditions (`T₁e₁ ≥ 0`, `T₂e₂ ≥ 0`, `(T₁k₁)(T₂k₂) ≥ 0`), the most general hypotheses under which
-- the text is meaningful. The reading "all six parameters non-negative" (physical NGM) is implied
-- by this one, so the conjunction of both readings is this reading. -/
namespace Alignment.Shadows.MorphismsNGM.MultiplexR0EqSumIff

/-- Intended statement: under `T₁e₁ ≥ 0`, `T₂e₂ ≥ 0`, `(T₁k₁)(T₂k₂) ≥ 0`,
`ρ(multiplexNGM …) = T₁e₁ + T₂e₂ ↔ T₁T₂k₁k₂ = T₁T₂e₁e₂`. -/
@[sa_reference "MorphismsNGM.multiplexR0EqSumIff"]
def T : Prop :=
  ∀ T₁ T₂ k₁ k₂ e₁ e₂ : ℝ, 0 ≤ T₁ * e₁ → 0 ≤ T₂ * e₂ → 0 ≤ (T₁ * k₁) * (T₂ * k₂) →
    (spectralRadius ℝ (multiplexNGM T₁ T₂ k₁ k₂ e₁ e₂) = ENNReal.ofReal (T₁ * e₁ + T₂ * e₂) ↔
      T₁ * T₂ * k₁ * k₂ = T₁ * T₂ * e₁ * e₂)

/-- S1: if R₀ is the sum of the layer R₀s then `T₁T₂k₁k₂ = T₁T₂e₁e₂`. -/
@[sa_shadow "MorphismsNGM.multiplexR0EqSumIff" 1]
def S1 : Prop :=
  ∀ T₁ T₂ k₁ k₂ e₁ e₂ : ℝ, 0 ≤ T₁ * e₁ → 0 ≤ T₂ * e₂ → 0 ≤ (T₁ * k₁) * (T₂ * k₂) →
    spectralRadius ℝ (multiplexNGM T₁ T₂ k₁ k₂ e₁ e₂) = ENNReal.ofReal (T₁ * e₁ + T₂ * e₂) →
      T₁ * T₂ * k₁ * k₂ = T₁ * T₂ * e₁ * e₂

/-- S2: if `T₁T₂k₁k₂ = T₁T₂e₁e₂` then R₀ is the sum of the layer R₀s. -/
@[sa_shadow "MorphismsNGM.multiplexR0EqSumIff" 2]
def S2 : Prop :=
  ∀ T₁ T₂ k₁ k₂ e₁ e₂ : ℝ, 0 ≤ T₁ * e₁ → 0 ≤ T₂ * e₂ → 0 ≤ (T₁ * k₁) * (T₂ * k₂) →
    T₁ * T₂ * k₁ * k₂ = T₁ * T₂ * e₁ * e₂ →
      spectralRadius ℝ (multiplexNGM T₁ T₂ k₁ k₂ e₁ e₂) = ENNReal.ofReal (T₁ * e₁ + T₂ * e₂)

@[sa_ref_forward "MorphismsNGM.multiplexR0EqSumIff" 1]
theorem ref_fwd1 : T → S1 :=
  fun t T₁ T₂ k₁ k₂ e₁ e₂ ha hd hbc => (t T₁ T₂ k₁ k₂ e₁ e₂ ha hd hbc).mp

@[sa_ref_forward "MorphismsNGM.multiplexR0EqSumIff" 2]
theorem ref_fwd2 : T → S2 :=
  fun t T₁ T₂ k₁ k₂ e₁ e₂ ha hd hbc => (t T₁ T₂ k₁ k₂ e₁ e₂ ha hd hbc).mpr

@[sa_complete "MorphismsNGM.multiplexR0EqSumIff"]
theorem complete (s1 : S1) (s2 : S2) : T :=
  fun T₁ T₂ k₁ k₂ e₁ e₂ ha hd hbc =>
    ⟨s1 T₁ T₂ k₁ k₂ e₁ e₂ ha hd hbc, s2 T₁ T₂ k₁ k₂ e₁ e₂ ha hd hbc⟩

end Alignment.Shadows.MorphismsNGM.MultiplexR0EqSumIff

/-! ## `MorphismsNGM.memSpectrumIffDet`

Text: "`r` is in the real spectrum of `K` iff `det(r·1 − K) = 0`." For every finite square real
matrix `K` (any finite index type) and real `r`; `r·1` is `r • 1`. Split along the iff. -/
namespace Alignment.Shadows.MorphismsNGM.MemSpectrumIffDet

/-- Intended statement: for every finite square real matrix `K` and real `r`,
`r ∈ spectrum ℝ K ↔ det(r • 1 − K) = 0`. -/
@[sa_reference "MorphismsNGM.memSpectrumIffDet"]
def T : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n] (K : Matrix n n ℝ) (r : ℝ),
    r ∈ spectrum ℝ K ↔ (r • (1 : Matrix n n ℝ) - K).det = 0

/-- S1: spectral values are roots of the characteristic determinant. -/
@[sa_shadow "MorphismsNGM.memSpectrumIffDet" 1]
def S1 : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n] (K : Matrix n n ℝ) (r : ℝ),
    r ∈ spectrum ℝ K → (r • (1 : Matrix n n ℝ) - K).det = 0

/-- S2: roots of the characteristic determinant are spectral values. -/
@[sa_shadow "MorphismsNGM.memSpectrumIffDet" 2]
def S2 : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n] (K : Matrix n n ℝ) (r : ℝ),
    (r • (1 : Matrix n n ℝ) - K).det = 0 → r ∈ spectrum ℝ K

@[sa_ref_forward "MorphismsNGM.memSpectrumIffDet" 1]
theorem ref_fwd1 : T.{u} → S1.{u} := by
  intro t n _ _ K r
  exact (t K r).mp

@[sa_ref_forward "MorphismsNGM.memSpectrumIffDet" 2]
theorem ref_fwd2 : T.{u} → S2.{u} := by
  intro t n _ _ K r
  exact (t K r).mpr

@[sa_complete "MorphismsNGM.memSpectrumIffDet"]
theorem complete (s1 : S1.{u}) (s2 : S2.{u}) : T.{u} := by
  intro n _ _ K r
  exact ⟨s1 K r, s2 K r⟩

end Alignment.Shadows.MorphismsNGM.MemSpectrumIffDet

/-! ## `MorphismsNGM.spectrumVecMulVecSubset`

Text: "The real spectrum of the rank-one matrix `u vᵀ` lies in `{0, v·u}`." No hypothesis on `u`
in this text (none is added). -/
namespace Alignment.Shadows.MorphismsNGM.SpectrumVecMulVecSubset

/-- Intended statement: for all real vectors `u`, `v`, `spectrum ℝ (u vᵀ) ⊆ {0, v·u}`. -/
@[sa_reference "MorphismsNGM.spectrumVecMulVecSubset"]
def T : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n] (u v : n → ℝ),
    spectrum ℝ (vecMulVec u v) ⊆ ({0, v ⬝ᵥ u} : Set ℝ)

/-- S1: the inclusion (a single atomic requirement). -/
@[sa_shadow "MorphismsNGM.spectrumVecMulVecSubset" 1]
def S1 : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n] (u v : n → ℝ),
    spectrum ℝ (vecMulVec u v) ⊆ ({0, v ⬝ᵥ u} : Set ℝ)

@[sa_ref_forward "MorphismsNGM.spectrumVecMulVecSubset" 1]
theorem ref_fwd1 : T.{u} → S1.{u} := fun t => t

@[sa_complete "MorphismsNGM.spectrumVecMulVecSubset"]
theorem complete (s1 : S1.{u}) : T.{u} := s1

end Alignment.Shadows.MorphismsNGM.SpectrumVecMulVecSubset

/-! ## `MorphismsNGM.memSpectrumVecMulVec`

Text: "`v·u` is in the real spectrum of `u vᵀ` when `u ≠ 0` (`u` is an eigenvector)."
-- AMBIGUITY: "(`u` is an eigenvector)" is read as the justification of the membership, not as a
-- separate claim. -/
namespace Alignment.Shadows.MorphismsNGM.MemSpectrumVecMulVec

/-- Intended statement: for `u ≠ 0`, `v·u ∈ spectrum ℝ (u vᵀ)`. -/
@[sa_reference "MorphismsNGM.memSpectrumVecMulVec"]
def T : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n] (u v : n → ℝ), u ≠ 0 →
    v ⬝ᵥ u ∈ spectrum ℝ (vecMulVec u v)

/-- S1: the membership (a single atomic requirement). -/
@[sa_shadow "MorphismsNGM.memSpectrumVecMulVec" 1]
def S1 : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n] (u v : n → ℝ), u ≠ 0 →
    v ⬝ᵥ u ∈ spectrum ℝ (vecMulVec u v)

@[sa_ref_forward "MorphismsNGM.memSpectrumVecMulVec" 1]
theorem ref_fwd1 : T.{u} → S1.{u} := fun t => t

@[sa_complete "MorphismsNGM.memSpectrumVecMulVec"]
theorem complete (s1 : S1.{u}) : T.{u} := s1

end Alignment.Shadows.MorphismsNGM.MemSpectrumVecMulVec

/-! ## `MorphismsNGM.spectrumFinTwo`

Text: "The real spectrum of a 2 × 2 matrix with non-negative discriminant `D = (a − d)² + 4bc`: the
two roots `(a + d ± √D)/2` of `λ² − (a + d)λ + (ad − bc)`."

Read as a set equality `spectrum ℝ [[a, b], [c, d]] = {(a + d + √D)/2, (a + d − √D)/2}` under
`D ≥ 0`, split into the two inclusions.
-- AMBIGUITY: "the two roots … of λ² − (a + d)λ + (ad − bc)" is read as describing the two values
-- (a fact of real arithmetic about `a, b, c, d` only, which would be a trusted-free shadow), not as
-- a separate requirement on the spectrum. -/
namespace Alignment.Shadows.MorphismsNGM.SpectrumFinTwo

/-- Intended statement: for `D = (a − d)² + 4bc ≥ 0`,
`spectrum ℝ [[a, b], [c, d]] = {(a + d + √D)/2, (a + d − √D)/2}`. -/
@[sa_reference "MorphismsNGM.spectrumFinTwo"]
def T : Prop :=
  ∀ a b c d : ℝ, 0 ≤ (a - d) ^ 2 + 4 * b * c →
    spectrum ℝ !![a, b; c, d] =
      ({(a + d + √((a - d) ^ 2 + 4 * b * c)) / 2, (a + d - √((a - d) ^ 2 + 4 * b * c)) / 2} : Set ℝ)

/-- S1: every real eigenvalue is one of the two roots. -/
@[sa_shadow "MorphismsNGM.spectrumFinTwo" 1]
def S1 : Prop :=
  ∀ a b c d : ℝ, 0 ≤ (a - d) ^ 2 + 4 * b * c →
    spectrum ℝ !![a, b; c, d] ⊆
      ({(a + d + √((a - d) ^ 2 + 4 * b * c)) / 2, (a + d - √((a - d) ^ 2 + 4 * b * c)) / 2} : Set ℝ)

/-- S2: both roots are real eigenvalues. -/
@[sa_shadow "MorphismsNGM.spectrumFinTwo" 2]
def S2 : Prop :=
  ∀ a b c d : ℝ, 0 ≤ (a - d) ^ 2 + 4 * b * c →
    ({(a + d + √((a - d) ^ 2 + 4 * b * c)) / 2, (a + d - √((a - d) ^ 2 + 4 * b * c)) / 2} : Set ℝ) ⊆
      spectrum ℝ !![a, b; c, d]

@[sa_ref_forward "MorphismsNGM.spectrumFinTwo" 1]
theorem ref_fwd1 : T → S1 := fun t a b c d hD => (t a b c d hD).le

@[sa_ref_forward "MorphismsNGM.spectrumFinTwo" 2]
theorem ref_fwd2 : T → S2 := fun t a b c d hD => (t a b c d hD).ge

@[sa_complete "MorphismsNGM.spectrumFinTwo"]
theorem complete (s1 : S1) (s2 : S2) : T :=
  fun a b c d hD => Set.Subset.antisymm (s1 a b c d hD) (s2 a b c d hD)

end Alignment.Shadows.MorphismsNGM.SpectrumFinTwo

/-! ## `MorphismsNGM.spectralRadiusFinTwoEqTraceIff`

Text: "For real `a, d ≥ 0`, `bc ≥ 0`: the spectral radius of `[[a, b], [c, d]]` is the trace `a + d`
iff `bc = ad` (the determinant vanishes)." Split along the iff; the parenthesis restates `bc = ad`. -/
namespace Alignment.Shadows.MorphismsNGM.SpectralRadiusFinTwoEqTraceIff

/-- Intended statement: for `a, d ≥ 0`, `bc ≥ 0`, `ρ([[a, b], [c, d]]) = a + d ↔ bc = ad`. -/
@[sa_reference "MorphismsNGM.spectralRadiusFinTwoEqTraceIff"]
def T : Prop :=
  ∀ a b c d : ℝ, 0 ≤ a → 0 ≤ d → 0 ≤ b * c →
    (spectralRadius ℝ !![a, b; c, d] = ENNReal.ofReal (a + d) ↔ b * c = a * d)

/-- S1: spectral radius equal to the trace forces `bc = ad`. -/
@[sa_shadow "MorphismsNGM.spectralRadiusFinTwoEqTraceIff" 1]
def S1 : Prop :=
  ∀ a b c d : ℝ, 0 ≤ a → 0 ≤ d → 0 ≤ b * c →
    spectralRadius ℝ !![a, b; c, d] = ENNReal.ofReal (a + d) → b * c = a * d

/-- S2: `bc = ad` makes the spectral radius equal to the trace. -/
@[sa_shadow "MorphismsNGM.spectralRadiusFinTwoEqTraceIff" 2]
def S2 : Prop :=
  ∀ a b c d : ℝ, 0 ≤ a → 0 ≤ d → 0 ≤ b * c →
    b * c = a * d → spectralRadius ℝ !![a, b; c, d] = ENNReal.ofReal (a + d)

@[sa_ref_forward "MorphismsNGM.spectralRadiusFinTwoEqTraceIff" 1]
theorem ref_fwd1 : T → S1 := fun t a b c d ha hd hbc => (t a b c d ha hd hbc).mp

@[sa_ref_forward "MorphismsNGM.spectralRadiusFinTwoEqTraceIff" 2]
theorem ref_fwd2 : T → S2 := fun t a b c d ha hd hbc => (t a b c d ha hd hbc).mpr

@[sa_complete "MorphismsNGM.spectralRadiusFinTwoEqTraceIff"]
theorem complete (s1 : S1) (s2 : S2) : T :=
  fun a b c d ha hd hbc => ⟨s1 a b c d ha hd hbc, s2 a b c d ha hd hbc⟩

end Alignment.Shadows.MorphismsNGM.SpectralRadiusFinTwoEqTraceIff
