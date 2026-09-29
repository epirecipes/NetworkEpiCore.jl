import Alignment.Registry
import NetworkEpi.Morphisms.Common

/-!
# Blind shadow sets: group `MorphismsCommon` (module `NetworkEpi.Morphisms.Common`)

Written by the blind shadow author. Files read: `SA-PASS_SKILL.md`, `Alignment/README.md`,
`Alignment/Example/ExampleShadows.lean`, `Alignment/DataTypes/MorphismsCommon.md`, the
`MorphismsCommon.*` entries of `Alignment/claims_blind.yaml`, and `DESIGN_NetworkEpiCore.md`
(§0, §D.1–§D.7, §J–§L). No trusted source, checker, registry fragment or report was opened;
`#check` was used only on the DataTypes vocabulary.
Re-shadow after the text remediation (blocks `header.perReactionCriterion`,
`hasFDerivAtEbCoordinates`, `suscDApply`, `hasFDerivAtSusc`, `hasFDerivAtIncl`, `ebSys1Incl`,
`header.ebSys1`): re-derived blind from the current `claims_blind.yaml` texts, the DataTypes file
and DESIGN §D.3–§D.4 under the same reading rules.

Conventions of this file.
* "Exit-free" for `rs : List (Rxn σ)` is `∀ r ∈ rs, r.isExit = false` (DataTypes §e).
* "Semiconjugacy" is `IsSemiconj`, "local semiconjugacy on `U`" is `IsSemiconjOn`, "conjugacy of
  `A` on `V` with `B` on `U`" is `IsConjOn` (DataTypes §e).
* Where the text writes a map by a formula (`(θ, φ, pop) ↦ (θ, 1, φ, pop)`, the chart
  `(θ, ξ, φ, pop) ↦ (θ, φ, pop)`, `S = qξψ(θ)`), the shadow uses that formula literally.
* A *solution on an interval* `I` is a curve `x` with `∀ t ∈ I, HasDerivWithinAt x (F (x t)) I t`
  and `Convex ℝ I` (DataTypes §f).
* Certificates may use any tactic; they only have to be sorry-free.

The claim `MorphismsCommon.isConjOn` (a definition docstring) is not in this author's assignment
and is not shadowed here.
-/

open NEP

namespace Alignment.Shadows.MorphismsCommon

/-- "Exit-free" (DataTypes §e): no reaction of the list is an exit `s → Y`. -/
def ExitFree {σ : Type} (rs : List (Rxn σ)) : Prop := ∀ r ∈ rs, r.isExit = false

/-- The inclusion of the slice `ξ = 1`, written by the text's formula
`(θ, φ, pop) ↦ (θ, 1, φ, pop)`. -/
def inclF {σ : Type} (w : EB1 σ) : EB σ := (w.1, 1, w.2.1, w.2.2)

/-- The chart written by the text's formula `(θ, ξ, φ, pop) ↦ (θ, φ, pop)`. -/
def dropF {σ : Type} (u : EB σ) : EB1 σ := (u.1, u.2.2.1, u.2.2.2)

/-- The slice `{ξ = 1}` of EB coordinates. -/
def sliceXi1 (σ : Type) : Set (EB σ) := {u | u.2.1 = 1}

end Alignment.Shadows.MorphismsCommon

/-! ## `MorphismsCommon.header.perReactionCriterion`

Blind text: "Every field in this library is a sum of per-reaction fields, and the derivative of a
map is linear, so a map is a semiconjugacy as soon as its derivative carries each per-reaction
source field to the corresponding per-reaction target field."

(Re-derived blind after the text remediation.) Split along "A, and B, so C":
* A, per representation built from reactions: S1 the EB model `ebSys N q rs` has field
  `Σ_{r ∈ rs} ebField N q r` (DESIGN §D.4 "the per-reaction lift is additive"), S2 the mass-action
  model `maSys rs` has field `Σ_{r ∈ rs} maField r` (DataTypes: "the sum of the per-reaction
  fields").
* B, "the derivative of a map is linear", holds by typing (`fderiv ℝ π u : _ →L[ℝ] _`); it is the
  reason for C, not a separate falsifiable requirement.
* C (S3): the criterion, for arbitrary objects whose fields are sums over one common list of
  reaction indices ("corresponding" = same index), and an arbitrary differentiable map whose
  derivative carries each source summand at `u` to the corresponding target summand at `π u`.

AMBIGUITY: "Every field in this library". Read as the representations assembled from reactions,
`ebSys` and `maSys`. `maSIR` is a closed-form concrete model, and `ebSys1` is derived from `lift`
(its own claims are below).
AMBIGUITY: "its derivative" is read as the Fréchet derivative `fderiv ℝ π u` of a differentiable
map (a semiconjugacy is differentiable by definition, DESIGN §D.3); the explicit-derivative form
is the separate claim `isSemiconjOfHasFDerivAt`.
-/

namespace Alignment.Shadows.MorphismsCommon.HeaderPerReactionCriterion

/-- S1: the EB model's field is the sum over the reaction list of the per-reaction EB fields. -/
@[sa_shadow "MorphismsCommon.header.perReactionCriterion" 1]
def S1 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)) (u : EB σ),
    (ebSys N q rs).F u = (rs.map fun r => ebField N q r u).sum

/-- S2: the mass-action model's field is the sum over the reaction list of the per-reaction
mass-action fields. -/
@[sa_shadow "MorphismsCommon.header.perReactionCriterion" 2]
def S2 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (rs : List (NRxn σ)) (u : MA σ),
    (maSys rs).F u = (rs.map fun r => maField r u).sum

/-- S3: the per-reaction criterion. If the source field is the sum of per-reaction fields `f i`
and the target field the sum of the corresponding `g i` over the same list, then a differentiable
map whose derivative carries each `f i u` to `g i (π u)` is a semiconjugacy. -/
@[sa_shadow "MorphismsCommon.header.perReactionCriterion" 3]
def S3 : Prop :=
  ∀ (A B : DynSys) {ι : Type} (l : List ι) (f : ι → A.V → A.V) (g : ι → B.V → B.V)
    (π : A.V → B.V),
    (∀ u, A.F u = (l.map fun i => f i u).sum) →
    (∀ w, B.F w = (l.map fun i => g i w).sum) →
    Differentiable ℝ π →
    (∀ i ∈ l, ∀ u, fderiv ℝ π u (f i u) = g i (π u)) →
    IsSemiconj A B π

/-- Intended statement: the conjunction of the three requirements. -/
@[sa_reference "MorphismsCommon.header.perReactionCriterion"]
def T : Prop := S1 ∧ S2 ∧ S3

@[sa_ref_forward "MorphismsCommon.header.perReactionCriterion" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "MorphismsCommon.header.perReactionCriterion" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1

@[sa_ref_forward "MorphismsCommon.header.perReactionCriterion" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2

@[sa_complete "MorphismsCommon.header.perReactionCriterion"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.MorphismsCommon.HeaderPerReactionCriterion

/-! ## `MorphismsCommon.isSemiconjOfHasFDerivAt`

Blind text: "A map with an explicit derivative `D u` at every point is a semiconjugacy if `D u`
carries the source field at `u` to the target field at `π u`."

One atomic requirement, for all objects `A B : DynSys`, all maps `π` and all derivative
families `D`. -/

namespace Alignment.Shadows.MorphismsCommon.IsSemiconjOfHasFDerivAt

/-- Intended statement. -/
@[sa_reference "MorphismsCommon.isSemiconjOfHasFDerivAt"]
def T : Prop :=
  ∀ (A B : DynSys) (π : A.V → B.V) (D : A.V → (A.V →L[ℝ] B.V)),
    (∀ u, HasFDerivAt π (D u) u) →
    (∀ u, D u (A.F u) = B.F (π u)) →
    IsSemiconj A B π

/-- S1: the whole statement. -/
@[sa_shadow "MorphismsCommon.isSemiconjOfHasFDerivAt" 1]
def S1 : Prop :=
  ∀ (A B : DynSys) (π : A.V → B.V) (D : A.V → (A.V →L[ℝ] B.V)),
    (∀ u, HasFDerivAt π (D u) u) →
    (∀ u, D u (A.F u) = B.F (π u)) →
    IsSemiconj A B π

@[sa_ref_forward "MorphismsCommon.isSemiconjOfHasFDerivAt" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MorphismsCommon.isSemiconjOfHasFDerivAt"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MorphismsCommon.IsSemiconjOfHasFDerivAt

/-! ## `MorphismsCommon.isSemiconjOnOfHasFDerivAt`

Blind text: "Local version of `isSemiconj_of_hasFDerivAt` on a set `U`. [...] A map with an
explicit derivative `D u` at every point is a semiconjugacy if `D u` carries the source field at
`u` to the target field at `π u`."

The local version on an arbitrary set `U` (no openness is asked for): if `π` has the explicit
derivative `D u` at every point `u ∈ U` and `D u` carries `A.F u` to `B.F (π u)` for `u ∈ U`,
then `π` is a local semiconjugacy on `U`.

AMBIGUITY: "Local version … on a set `U`" of "an explicit derivative `D u` at every point". The
most defensible reading localises both hypotheses to `U` (S1). S2 is the weaker reading (derivative
at every point of `A.V`, carrying only on `U`); it follows from S1 and is kept to separate the two
readings in the checks. -/

namespace Alignment.Shadows.MorphismsCommon.IsSemiconjOnOfHasFDerivAt

/-- S1: both hypotheses on `U` only. -/
@[sa_shadow "MorphismsCommon.isSemiconjOnOfHasFDerivAt" 1]
def S1 : Prop :=
  ∀ (A B : DynSys) (U : Set A.V) (π : A.V → B.V) (D : A.V → (A.V →L[ℝ] B.V)),
    (∀ u ∈ U, HasFDerivAt π (D u) u) →
    (∀ u ∈ U, D u (A.F u) = B.F (π u)) →
    IsSemiconjOn A B U π

/-- S2: the derivative at every point, carrying on `U`. -/
@[sa_shadow "MorphismsCommon.isSemiconjOnOfHasFDerivAt" 2]
def S2 : Prop :=
  ∀ (A B : DynSys) (U : Set A.V) (π : A.V → B.V) (D : A.V → (A.V →L[ℝ] B.V)),
    (∀ u, HasFDerivAt π (D u) u) →
    (∀ u ∈ U, D u (A.F u) = B.F (π u)) →
    IsSemiconjOn A B U π

/-- Intended statement (the reading S1). -/
@[sa_reference "MorphismsCommon.isSemiconjOnOfHasFDerivAt"]
def T : Prop :=
  ∀ (A B : DynSys) (U : Set A.V) (π : A.V → B.V) (D : A.V → (A.V →L[ℝ] B.V)),
    (∀ u ∈ U, HasFDerivAt π (D u) u) →
    (∀ u ∈ U, D u (A.F u) = B.F (π u)) →
    IsSemiconjOn A B U π

@[sa_ref_forward "MorphismsCommon.isSemiconjOnOfHasFDerivAt" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_ref_forward "MorphismsCommon.isSemiconjOnOfHasFDerivAt" 2]
theorem ref_fwd2 : T → S2 :=
  fun t A B U π D hD hc => t A B U π D (fun u _ => hD u) hc

@[sa_complete "MorphismsCommon.isSemiconjOnOfHasFDerivAt"]
theorem complete (s1 : S1) (_s2 : S2) : T := s1

end Alignment.Shadows.MorphismsCommon.IsSemiconjOnOfHasFDerivAt

/-! ## `MorphismsCommon.clmListSum`

Blind text: "A continuous linear map commutes with the sum of a mapped list."

For every continuous linear map `L : E →L[ℝ] F` between real normed spaces, every list `l` and
every `f`: `L (Σ_{i ∈ l} f i) = Σ_{i ∈ l} L (f i)`.

AMBIGUITY: the scalars and spaces are not named. Read as real normed spaces, the setting of every
`DynSys` state space in this library.
NOTE: the text is pure linear algebra and names no notion of the trusted library, so this shadow is
necessarily `shadow_trusted_free`; it needs an independent `sa_shadow_reviewed` record. It is not
padded with a trusted constant (README, limitation 10). -/

namespace Alignment.Shadows.MorphismsCommon.ClmListSum

/-- Intended statement. -/
@[sa_reference "MorphismsCommon.clmListSum"]
def T : Prop :=
  ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L : E →L[ℝ] F) {ι : Type} (l : List ι) (f : ι → E),
    L (l.map f).sum = (l.map fun i => L (f i)).sum

/-- S1: the whole statement. -/
@[sa_shadow "MorphismsCommon.clmListSum" 1]
def S1 : Prop :=
  ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L : E →L[ℝ] F) {ι : Type} (l : List ι) (f : ι → E),
    L (l.map f).sum = (l.map fun i => L (f i)).sum

@[sa_ref_forward "MorphismsCommon.clmListSum" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MorphismsCommon.clmListSum"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MorphismsCommon.ClmListSum

/-! ## `MorphismsCommon.clmListSumEq`

Blind text: "**The per-reaction criterion.** If a continuous linear map `L` carries each
per-reaction source term `f r` to the per-reaction target term `g r`, it carries the sum over the
reaction list to the sum."

For every continuous linear map `L` between real normed spaces, every list `rs` and all
`f`, `g`: if `L (f r) = g r` for every `r ∈ rs`, then `L (Σ_{r ∈ rs} f r) = Σ_{r ∈ rs} g r`.

AMBIGUITY: "the reaction list" is read as a list over an arbitrary index type, so that it covers
T_EB lists, T_net lists and any other reaction syntax; "each per-reaction source term" is each
member of the list (`∀ r ∈ rs`). Scalars: real normed spaces, as in `clmListSum`.
NOTE: necessarily `shadow_trusted_free` (pure linear algebra; see `clmListSum`). -/

namespace Alignment.Shadows.MorphismsCommon.ClmListSumEq

/-- Intended statement. -/
@[sa_reference "MorphismsCommon.clmListSumEq"]
def T : Prop :=
  ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L : E →L[ℝ] F) {ι : Type} (rs : List ι) (f : ι → E) (g : ι → F),
    (∀ r ∈ rs, L (f r) = g r) → L (rs.map f).sum = (rs.map g).sum

/-- S1: the whole statement. -/
@[sa_shadow "MorphismsCommon.clmListSumEq" 1]
def S1 : Prop :=
  ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L : E →L[ℝ] F) {ι : Type} (rs : List ι) (f : ι → E) (g : ι → F),
    (∀ r ∈ rs, L (f r) = g r) → L (rs.map f).sum = (rs.map g).sum

@[sa_ref_forward "MorphismsCommon.clmListSumEq" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MorphismsCommon.clmListSumEq"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MorphismsCommon.ClmListSumEq

/-! ## `MorphismsCommon.isSemiconjOnInverse`

Blind text: "**A differentiable inverse of a semiconjugacy is a semiconjugacy.** Let `h` be a
local semiconjugacy on `V` from `A` to `B`, and let `g : B.V → A.V` be a global left inverse of
`h` (`g ∘ h = id`) that is differentiable at every point of `U`, maps `U` into `V` and is a right
inverse on `U` (`h (g v) = v` for `v ∈ U`). Then `g` is a local semiconjugacy on `U` from `B` to
`A`. [...] the fact that a differentiable two-sided inverse of a semiconjugacy is one"

* S1: the precise local statement of the first fragment, for all `A B`, all sets `V`, `U`.
* S2: the second fragment (module header) read literally with the vocabulary's global notions:
  a differentiable two-sided inverse `g` of a (global) semiconjugacy `h` is a (global)
  semiconjugacy.

AMBIGUITY: the header fragment "a differentiable two-sided inverse of a semiconjugacy is one" may
only paraphrase S1; its literal global reading is kept as S2 (split along readings). -/

namespace Alignment.Shadows.MorphismsCommon.IsSemiconjOnInverse

/-- S1: the local statement. -/
@[sa_shadow "MorphismsCommon.isSemiconjOnInverse" 1]
def S1 : Prop :=
  ∀ (A B : DynSys) (V : Set A.V) (U : Set B.V) (h : A.V → B.V) (g : B.V → A.V),
    IsSemiconjOn A B V h →
    g ∘ h = id →
    (∀ v ∈ U, DifferentiableAt ℝ g v) →
    (∀ v ∈ U, g v ∈ V) →
    (∀ v ∈ U, h (g v) = v) →
    IsSemiconjOn B A U g

/-- S2: the global reading of the header fragment. -/
@[sa_shadow "MorphismsCommon.isSemiconjOnInverse" 2]
def S2 : Prop :=
  ∀ (A B : DynSys) (h : A.V → B.V) (g : B.V → A.V),
    IsSemiconj A B h → Differentiable ℝ g → g ∘ h = id → h ∘ g = id → IsSemiconj B A g

/-- Intended statement: both fragments. -/
@[sa_reference "MorphismsCommon.isSemiconjOnInverse"]
def T : Prop := S1 ∧ S2

@[sa_ref_forward "MorphismsCommon.isSemiconjOnInverse" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "MorphismsCommon.isSemiconjOnInverse" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "MorphismsCommon.isSemiconjOnInverse"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.MorphismsCommon.IsSemiconjOnInverse

/-! ## `MorphismsCommon.isConjOnOfInverse`

Blind text: "A conjugacy with `V = univ` built from a global semiconjugacy `h` and a
differentiable inverse `g` on `U`: `IsConjOn A B univ U h g`."

For all `A B`, `U`, `h`, `g`: if `h` is a (global) semiconjugacy and `g` is a differentiable
inverse of `h` on `U`, then `IsConjOn A B univ U h g`.

AMBIGUITY: "a differentiable inverse `g` on `U`" with `V = univ`. Read as: `g` is differentiable
at every point of `U`, and `h`, `g` are mutually inverse between `univ` and `U`, i.e. `h` maps
everything into `U`, `g (h u) = u` for every `u`, and `h (g v) = v` for `v ∈ U` (`g` maps `U`
into `univ` trivially). Without `h(univ) ⊆ U` no map pair is inverse "between `univ` and `U`",
and `IsConjOn` asks for `h(V) ⊆ U` (DataTypes). Differentiability of `g` only on `U` is the
weakest reading of "differentiable … on `U`". -/

namespace Alignment.Shadows.MorphismsCommon.IsConjOnOfInverse

/-- Intended statement. -/
@[sa_reference "MorphismsCommon.isConjOnOfInverse"]
def T : Prop :=
  ∀ (A B : DynSys) (U : Set B.V) (h : A.V → B.V) (g : B.V → A.V),
    IsSemiconj A B h →
    (∀ v ∈ U, DifferentiableAt ℝ g v) →
    (∀ u, h u ∈ U) →
    (∀ u, g (h u) = u) →
    (∀ v ∈ U, h (g v) = v) →
    IsConjOn A B Set.univ U h g

/-- S1: the whole statement. -/
@[sa_shadow "MorphismsCommon.isConjOnOfInverse" 1]
def S1 : Prop :=
  ∀ (A B : DynSys) (U : Set B.V) (h : A.V → B.V) (g : B.V → A.V),
    IsSemiconj A B h →
    (∀ v ∈ U, DifferentiableAt ℝ g v) →
    (∀ u, h u ∈ U) →
    (∀ u, g (h u) = u) →
    (∀ v ∈ U, h (g v) = v) →
    IsConjOn A B Set.univ U h g

@[sa_ref_forward "MorphismsCommon.isConjOnOfInverse" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MorphismsCommon.isConjOnOfInverse"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MorphismsCommon.IsConjOnOfInverse

/-! ## `MorphismsCommon.ebCoordinateApply`

Blind text: "`ebTheta` is the θ-coordinate. [...] `ebXi` is the ξ-coordinate. [...] `ebPhi` is
the φ-coordinate. [...] `ebPop` is the pop-coordinate."

Four requirements, one per coordinate of `EB σ = (θ, ξ, φ, pop)` (`u.1 = θ`, `u.2.1 = ξ`,
`u.2.2.1 = φ`, `u.2.2.2 = pop`, DataTypes). -/

namespace Alignment.Shadows.MorphismsCommon.EbCoordinateApply

/-- S1: `ebTheta` is the θ-coordinate. -/
@[sa_shadow "MorphismsCommon.ebCoordinateApply" 1]
def S1 : Prop := ∀ {σ : Type} (u : EB σ), ebTheta u = u.1

/-- S2: `ebXi` is the ξ-coordinate. -/
@[sa_shadow "MorphismsCommon.ebCoordinateApply" 2]
def S2 : Prop := ∀ {σ : Type} (u : EB σ), ebXi u = u.2.1

/-- S3: `ebPhi` is the φ-coordinate. -/
@[sa_shadow "MorphismsCommon.ebCoordinateApply" 3]
def S3 : Prop := ∀ {σ : Type} (u : EB σ), ebPhi u = u.2.2.1

/-- S4: `ebPop` is the pop-coordinate. -/
@[sa_shadow "MorphismsCommon.ebCoordinateApply" 4]
def S4 : Prop := ∀ {σ : Type} (u : EB σ), ebPop u = u.2.2.2

/-- Intended statement: the four coordinate identities. -/
@[sa_reference "MorphismsCommon.ebCoordinateApply"]
def T : Prop := S1 ∧ S2 ∧ S3 ∧ S4

@[sa_ref_forward "MorphismsCommon.ebCoordinateApply" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "MorphismsCommon.ebCoordinateApply" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1

@[sa_ref_forward "MorphismsCommon.ebCoordinateApply" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2.1

@[sa_ref_forward "MorphismsCommon.ebCoordinateApply" 4]
theorem ref_fwd4 : T → S4 := fun t => t.2.2.2

@[sa_complete "MorphismsCommon.ebCoordinateApply"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.MorphismsCommon.EbCoordinateApply

/-! ## `MorphismsCommon.hasFDerivAtEbCoordinates`

Blind text: "The coordinate projections are their own derivatives."

(Re-derived blind after the text remediation.) For each of the four coordinate projections of
`EB σ = (θ, ξ, φ, pop)` and every point `u`, the projection has itself as Fréchet derivative at
`u`.

AMBIGUITY: "the coordinate projections" may name the continuous linear maps `ebTheta`, `ebXi`,
`ebPhi`, `ebPop` (reading A: `HasFDerivAt ⇑ebTheta ebTheta u`), or the raw projections
`v ↦ v.1`, … whose "own" derivative is that projection as a continuous linear map (reading B:
`HasFDerivAt (fun v => v.1) ebTheta u`). Reading A alone holds for any continuous linear map, so
reading B is what pins the projections down. Both readings are shadowed (S1–S4 reading A, S5–S8
reading B). -/

namespace Alignment.Shadows.MorphismsCommon.HasFDerivAtEbCoordinates

/-- S1 (reading A): `ebTheta` is its own derivative. -/
@[sa_shadow "MorphismsCommon.hasFDerivAtEbCoordinates" 1]
def S1 : Prop :=
  ∀ {σ : Type} (u : EB σ), HasFDerivAt (fun v : EB σ => ebTheta v) (ebTheta : EB σ →L[ℝ] ℝ) u

/-- S2 (reading A): `ebXi` is its own derivative. -/
@[sa_shadow "MorphismsCommon.hasFDerivAtEbCoordinates" 2]
def S2 : Prop :=
  ∀ {σ : Type} (u : EB σ), HasFDerivAt (fun v : EB σ => ebXi v) (ebXi : EB σ →L[ℝ] ℝ) u

/-- S3 (reading A): `ebPhi` is its own derivative. -/
@[sa_shadow "MorphismsCommon.hasFDerivAtEbCoordinates" 3]
def S3 : Prop :=
  ∀ {σ : Type} (u : EB σ), HasFDerivAt (fun v : EB σ => ebPhi v) (ebPhi : EB σ →L[ℝ] σ → ℝ) u

/-- S4 (reading A): `ebPop` is its own derivative. -/
@[sa_shadow "MorphismsCommon.hasFDerivAtEbCoordinates" 4]
def S4 : Prop :=
  ∀ {σ : Type} (u : EB σ), HasFDerivAt (fun v : EB σ => ebPop v) (ebPop : EB σ →L[ℝ] σ → ℝ) u

/-- S5 (reading B): the θ-projection has derivative `ebTheta`. -/
@[sa_shadow "MorphismsCommon.hasFDerivAtEbCoordinates" 5]
def S5 : Prop :=
  ∀ {σ : Type} (u : EB σ), HasFDerivAt (fun v : EB σ => v.1) (ebTheta : EB σ →L[ℝ] ℝ) u

/-- S6 (reading B): the ξ-projection has derivative `ebXi`. -/
@[sa_shadow "MorphismsCommon.hasFDerivAtEbCoordinates" 6]
def S6 : Prop :=
  ∀ {σ : Type} (u : EB σ), HasFDerivAt (fun v : EB σ => v.2.1) (ebXi : EB σ →L[ℝ] ℝ) u

/-- S7 (reading B): the φ-projection has derivative `ebPhi`. -/
@[sa_shadow "MorphismsCommon.hasFDerivAtEbCoordinates" 7]
def S7 : Prop :=
  ∀ {σ : Type} (u : EB σ), HasFDerivAt (fun v : EB σ => v.2.2.1) (ebPhi : EB σ →L[ℝ] σ → ℝ) u

/-- S8 (reading B): the pop-projection has derivative `ebPop`. -/
@[sa_shadow "MorphismsCommon.hasFDerivAtEbCoordinates" 8]
def S8 : Prop :=
  ∀ {σ : Type} (u : EB σ), HasFDerivAt (fun v : EB σ => v.2.2.2) (ebPop : EB σ →L[ℝ] σ → ℝ) u

/-- Intended statement: both readings, for all four coordinates. -/
@[sa_reference "MorphismsCommon.hasFDerivAtEbCoordinates"]
def T : Prop := S1 ∧ S2 ∧ S3 ∧ S4 ∧ S5 ∧ S6 ∧ S7 ∧ S8

@[sa_ref_forward "MorphismsCommon.hasFDerivAtEbCoordinates" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "MorphismsCommon.hasFDerivAtEbCoordinates" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1

@[sa_ref_forward "MorphismsCommon.hasFDerivAtEbCoordinates" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2.1

@[sa_ref_forward "MorphismsCommon.hasFDerivAtEbCoordinates" 4]
theorem ref_fwd4 : T → S4 := fun t => t.2.2.2.1

@[sa_ref_forward "MorphismsCommon.hasFDerivAtEbCoordinates" 5]
theorem ref_fwd5 : T → S5 := fun t => t.2.2.2.2.1

@[sa_ref_forward "MorphismsCommon.hasFDerivAtEbCoordinates" 6]
theorem ref_fwd6 : T → S6 := fun t => t.2.2.2.2.2.1

@[sa_ref_forward "MorphismsCommon.hasFDerivAtEbCoordinates" 7]
theorem ref_fwd7 : T → S7 := fun t => t.2.2.2.2.2.2.1

@[sa_ref_forward "MorphismsCommon.hasFDerivAtEbCoordinates" 8]
theorem ref_fwd8 : T → S8 := fun t => t.2.2.2.2.2.2.2

@[sa_complete "MorphismsCommon.hasFDerivAtEbCoordinates"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) (s7 : S7)
    (s8 : S8) : T :=
  ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩

end Alignment.Shadows.MorphismsCommon.HasFDerivAtEbCoordinates

/-! ## `MorphismsCommon.suscDApply`

Blind text: "`suscD N q u v = q (v_ξ ψ(θ) + ξ ψ'(θ) v_θ)` with `(θ, ξ) = (u.1, u.2.1)`."

(Re-derived blind after the text remediation.) For every network `N` (arbitrary `ψ`, `ψ'`), seed
factor `q` and points `u v : EB σ`, with `v_θ = v.1` and `v_ξ = v.2.1` (the EB coordinate order
`(θ, ξ, φ, pop)`). A single equation: one atomic requirement. -/

namespace Alignment.Shadows.MorphismsCommon.SuscDApply

/-- Intended statement. -/
@[sa_reference "MorphismsCommon.suscDApply"]
def T : Prop :=
  ∀ {σ : Type} (N : CNet) (q : ℝ) (u v : EB σ),
    suscD N q u v = q * (v.2.1 * N.ψ u.1 + u.2.1 * N.ψ' u.1 * v.1)

/-- S1: the whole formula. -/
@[sa_shadow "MorphismsCommon.suscDApply" 1]
def S1 : Prop :=
  ∀ {σ : Type} (N : CNet) (q : ℝ) (u v : EB σ),
    suscD N q u v = q * (v.2.1 * N.ψ u.1 + u.2.1 * N.ψ' u.1 * v.1)

@[sa_ref_forward "MorphismsCommon.suscDApply" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MorphismsCommon.suscDApply"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MorphismsCommon.SuscDApply

/-! ## `MorphismsCommon.hasFDerivAtSusc`

Blind text: "`S = qξψ(θ)` has derivative `suscD N q u` at `u` when `ψ'(θ)` is the derivative of
`ψ` at `θ = u.1`."

(Re-derived blind after the text remediation.) For every network `N` (arbitrary `ψ`, `ψ'`), seed
factor `q` and point `u : EB σ`: if `HasDerivAt N.ψ (N.ψ' u.1) u.1` (the only hypothesis the text
states), the function `v ↦ S(v)` has Fréchet derivative `suscD N q u` at `u`.

AMBIGUITY: `S = qξψ(θ)` is the vocabulary's `N.susc q θ ξ` (DataTypes §e, "S = qξψ(θ) is
`N.susc q θ ξ`") and literally the function `(θ, ξ) ↦ q ξ ψ(θ)`. Both are shadowed: S1 with
`CNet.susc`, S2 with the formula. -/

namespace Alignment.Shadows.MorphismsCommon.HasFDerivAtSusc

/-- S1: the susceptible fraction `CNet.susc` has derivative `suscD N q u`. -/
@[sa_shadow "MorphismsCommon.hasFDerivAtSusc" 1]
def S1 : Prop :=
  ∀ {σ : Type} (N : CNet) (q : ℝ) (u : EB σ),
    HasDerivAt N.ψ (N.ψ' u.1) u.1 →
    HasFDerivAt (fun v : EB σ => N.susc q v.1 v.2.1) (suscD N q u) u

/-- S2: the function `v ↦ q ξ ψ(θ)` (the text's formula) has derivative `suscD N q u`. -/
@[sa_shadow "MorphismsCommon.hasFDerivAtSusc" 2]
def S2 : Prop :=
  ∀ {σ : Type} (N : CNet) (q : ℝ) (u : EB σ),
    HasDerivAt N.ψ (N.ψ' u.1) u.1 →
    HasFDerivAt (fun v : EB σ => q * v.2.1 * N.ψ v.1) (suscD N q u) u

/-- Intended statement: both readings of `S`. -/
@[sa_reference "MorphismsCommon.hasFDerivAtSusc"]
def T : Prop := S1 ∧ S2

@[sa_ref_forward "MorphismsCommon.hasFDerivAtSusc" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "MorphismsCommon.hasFDerivAtSusc" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "MorphismsCommon.hasFDerivAtSusc"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.MorphismsCommon.HasFDerivAtSusc

/-! ## `MorphismsCommon.dropLApply`

Blind text: "`dropL` is `EB.drop`." -/

namespace Alignment.Shadows.MorphismsCommon.DropLApply

/-- Intended statement: `dropL` and `EB.drop` agree at every point. -/
@[sa_reference "MorphismsCommon.dropLApply"]
def T : Prop := ∀ {σ : Type} (u : EB σ), dropL u = EB.drop u

/-- S1: the whole statement. -/
@[sa_shadow "MorphismsCommon.dropLApply" 1]
def S1 : Prop := ∀ {σ : Type} (u : EB σ), dropL u = EB.drop u

@[sa_ref_forward "MorphismsCommon.dropLApply" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MorphismsCommon.dropLApply"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MorphismsCommon.DropLApply

/-! ## `MorphismsCommon.inclLApply`

Blind text: "`inclL (θ, φ, pop) = (θ, 0, φ, pop)`." -/

namespace Alignment.Shadows.MorphismsCommon.InclLApply

/-- Intended statement, for all `θ`, `φ`, `pop`. -/
@[sa_reference "MorphismsCommon.inclLApply"]
def T : Prop :=
  ∀ {σ : Type} (θ : ℝ) (φ pop : σ → ℝ), inclL ((θ, φ, pop) : EB1 σ) = ((θ, 0, φ, pop) : EB σ)

/-- S1: the whole statement. -/
@[sa_shadow "MorphismsCommon.inclLApply" 1]
def S1 : Prop :=
  ∀ {σ : Type} (θ : ℝ) (φ pop : σ → ℝ), inclL ((θ, φ, pop) : EB1 σ) = ((θ, 0, φ, pop) : EB σ)

@[sa_ref_forward "MorphismsCommon.inclLApply" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MorphismsCommon.inclLApply"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MorphismsCommon.InclLApply

/-! ## `MorphismsCommon.dropIncl`

Blind text: "`EB.drop` is a left inverse of `EB1.incl`." -/

namespace Alignment.Shadows.MorphismsCommon.DropIncl

/-- Intended statement: `EB.drop (EB1.incl w) = w` for every `w`. -/
@[sa_reference "MorphismsCommon.dropIncl"]
def T : Prop := ∀ {σ : Type} (w : EB1 σ), EB.drop (EB1.incl w) = w

/-- S1: the whole statement. -/
@[sa_shadow "MorphismsCommon.dropIncl" 1]
def S1 : Prop := ∀ {σ : Type} (w : EB1 σ), EB.drop (EB1.incl w) = w

@[sa_ref_forward "MorphismsCommon.dropIncl" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MorphismsCommon.dropIncl"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MorphismsCommon.DropIncl

/-! ## `MorphismsCommon.inclDrop`

Blind text: "On `ξ = 1`, `EB1.incl` is a left inverse of `EB.drop`." -/

namespace Alignment.Shadows.MorphismsCommon.InclDrop

/-- Intended statement: `EB1.incl (EB.drop u) = u` for every `u` with `ξ = u.2.1 = 1`. -/
@[sa_reference "MorphismsCommon.inclDrop"]
def T : Prop := ∀ {σ : Type} (u : EB σ), u.2.1 = 1 → EB1.incl (EB.drop u) = u

/-- S1: the whole statement. -/
@[sa_shadow "MorphismsCommon.inclDrop" 1]
def S1 : Prop := ∀ {σ : Type} (u : EB σ), u.2.1 = 1 → EB1.incl (EB.drop u) = u

@[sa_ref_forward "MorphismsCommon.inclDrop" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MorphismsCommon.inclDrop"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MorphismsCommon.InclDrop

/-! ## `MorphismsCommon.hasFDerivAtIncl`

Blind text: "`EB1.incl` is affine with derivative `inclL`."

(Re-derived blind after the text remediation.) Split along "affine with derivative …":
* S1: `EB1.incl` is affine with linear part `inclL`: `EB1.incl w = inclL w + c` for one constant
  `c` (the text does not name `c`, so it is existential);
* S2: at every point, `EB1.incl` has Fréchet derivative `inclL`. -/

namespace Alignment.Shadows.MorphismsCommon.HasFDerivAtIncl

/-- S1: affine with linear part `inclL`. -/
@[sa_shadow "MorphismsCommon.hasFDerivAtIncl" 1]
def S1 : Prop := ∀ {σ : Type}, ∃ c : EB σ, ∀ w : EB1 σ, EB1.incl w = inclL w + c

/-- S2: derivative `inclL` at every point. -/
@[sa_shadow "MorphismsCommon.hasFDerivAtIncl" 2]
def S2 : Prop :=
  ∀ {σ : Type} (w : EB1 σ), HasFDerivAt (EB1.incl (σ := σ)) (inclL : EB1 σ →L[ℝ] EB σ) w

/-- Intended statement. -/
@[sa_reference "MorphismsCommon.hasFDerivAtIncl"]
def T : Prop := S1 ∧ S2

@[sa_ref_forward "MorphismsCommon.hasFDerivAtIncl" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "MorphismsCommon.hasFDerivAtIncl" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "MorphismsCommon.hasFDerivAtIncl"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.MorphismsCommon.HasFDerivAtIncl

/-! ## `MorphismsCommon.ebSys1Incl`

Blind text: "**For an exit-free model, the EB model on `(θ, φ, pop)` is the restriction of the EB
model to the invariant slice `ξ = 1`**: `(θ, φ, pop) ↦ (θ, 1, φ, pop)` is a semiconjugacy from
`ebSys1` to `ebSys` (the ξ-component of the EB field vanishes without exits)."

(Re-derived blind after the text remediation.) For every species type, every network `N`
(arbitrary `ψ`, `ψ'`, `ψ''`), every `q` and every exit-free T_EB list `rs`:
* S1 (the explicit claim after the colon): the map `(θ, φ, pop) ↦ (θ, 1, φ, pop)` (the text's
  formula) is a semiconjugacy `ebSys1 N q rs → ebSys N q rs`;
* S2 (the parenthesis): the ξ-component of the EB field `lift N q rs` vanishes at every point
  (DESIGN §D.4: "ξ̇ = −(Σ_e ν_e)ξ (ξ ≡ 1 if there are no exits)");
* S3 ("the invariant slice `ξ = 1`"): a solution of the EB model on an interval `I` that meets the
  slice at some time of `I` stays in it throughout `I` (DESIGN §D.3: "The inclusion of an
  invariant subsystem is a restriction"; solutions are taken on intervals, DataTypes §f).

AMBIGUITY: "invariant" is read as invariance for solutions of `ebSys N q rs` on a convex time set,
in both time directions (ξ̇ ≡ 0 without exits). -/

namespace Alignment.Shadows.MorphismsCommon.EbSys1Incl

/-- S1: the slice inclusion (by the text's formula) is a semiconjugacy from `ebSys1` to `ebSys`
for every exit-free model. -/
@[sa_shadow "MorphismsCommon.ebSys1Incl" 1]
def S1 : Prop :=
  ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)),
    ExitFree rs → IsSemiconj (ebSys1 N q rs) (ebSys N q rs) (inclF (σ := σ))

/-- S2: without exits, the ξ-component of the EB field vanishes everywhere. -/
@[sa_shadow "MorphismsCommon.ebSys1Incl" 2]
def S2 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)),
    ExitFree rs → ∀ u : EB σ, (lift N q rs u).2.1 = 0

/-- S3: without exits, the slice `ξ = 1` is invariant for solutions of the EB model on
intervals. -/
@[sa_shadow "MorphismsCommon.ebSys1Incl" 3]
def S3 : Prop :=
  ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)),
    ExitFree rs →
    ∀ (I : Set ℝ) (x : ℝ → EB σ), Convex ℝ I →
      (∀ t ∈ I, HasDerivWithinAt x ((ebSys N q rs).F (x t)) I t) →
      ∀ t₀ ∈ I, (x t₀).2.1 = 1 → ∀ t ∈ I, (x t).2.1 = 1

/-- Intended statement: the three requirements. -/
@[sa_reference "MorphismsCommon.ebSys1Incl"]
def T : Prop := S1 ∧ S2 ∧ S3

@[sa_ref_forward "MorphismsCommon.ebSys1Incl" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "MorphismsCommon.ebSys1Incl" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1

@[sa_ref_forward "MorphismsCommon.ebSys1Incl" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2

@[sa_complete "MorphismsCommon.ebSys1Incl"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.MorphismsCommon.EbSys1Incl

/-! ## `MorphismsCommon.ebSys1Drop`

Blind text: "The chart `(θ, ξ, φ, pop) ↦ (θ, φ, pop)` is a local semiconjugacy on `{ξ = 1}` from
`ebSys` to `ebSys1` (for every T_EB model)."

For every species type, network `N`, seed factor `q` and T_EB list `rs` (exits allowed). -/

namespace Alignment.Shadows.MorphismsCommon.EbSys1Drop

/-- Intended statement. -/
@[sa_reference "MorphismsCommon.ebSys1Drop"]
def T : Prop :=
  ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)),
    IsSemiconjOn (ebSys N q rs) (ebSys1 N q rs) (sliceXi1 σ) (dropF (σ := σ))

/-- S1: the whole statement. -/
@[sa_shadow "MorphismsCommon.ebSys1Drop" 1]
def S1 : Prop :=
  ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)),
    IsSemiconjOn (ebSys N q rs) (ebSys1 N q rs) (sliceXi1 σ) (dropF (σ := σ))

@[sa_ref_forward "MorphismsCommon.ebSys1Drop" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MorphismsCommon.ebSys1Drop"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MorphismsCommon.EbSys1Drop

/-! ## `MorphismsCommon.header.ebSys1`

Blind text: "the reduced EB system `ebSys1` on `ξ = 1` in coordinates `(θ, φ, pop)`, which is the
EB model of an exit-free T_EB model in the design's coordinates"

(Re-derived blind after the text remediation.)
* S1 ("the reduced EB system on ξ = 1 in coordinates (θ, φ, pop)"): for every T_EB list, the field
  of `ebSys1` at `(θ, φ, pop)` is the `(θ, φ, pop)`-part of the EB field at `(θ, 1, φ, pop)`.
* S2 ("which is the EB model of an exit-free T_EB model in the design's coordinates", read as a
  change of coordinates): for every exit-free list, `ebSys1` on all of `EB1 σ` is conjugate to
  the EB model on the slice `ξ = 1`, via the slice inclusion and the chart
  (`IsConjOn … univ {ξ = 1} incl drop`, text formulas; DESIGN §D.3: "Conjugacies … are
  isomorphisms").
* S3 (the weaker "restriction" reading of the same phrase): for every exit-free list, the slice
  inclusion is a semiconjugacy from `ebSys1` to the EB model.

AMBIGUITY: "is the EB model … in the design's coordinates". Read as a conjugacy with the EB model
on the slice `ξ = 1` (S2) and, as a weaker reading, as the restriction semiconjugacy (S3). The
invariance of the slice is shadowed under `ebSys1Incl` and not repeated here. -/

namespace Alignment.Shadows.MorphismsCommon.HeaderEbSys1

/-- S1: the reduced field. -/
@[sa_shadow "MorphismsCommon.header.ebSys1" 1]
def S1 : Prop :=
  ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)) (w : EB1 σ),
    (ebSys1 N q rs).F w = dropF (lift N q rs (inclF w))

/-- S2: for exit-free models, `ebSys1` is conjugate to the EB model on the slice `ξ = 1`. -/
@[sa_shadow "MorphismsCommon.header.ebSys1" 2]
def S2 : Prop :=
  ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)),
    ExitFree rs →
    IsConjOn (ebSys1 N q rs) (ebSys N q rs) Set.univ (sliceXi1 σ) (inclF (σ := σ))
      (dropF (σ := σ))

/-- S3: for exit-free models, the slice inclusion is a semiconjugacy from `ebSys1` to the EB
model. -/
@[sa_shadow "MorphismsCommon.header.ebSys1" 3]
def S3 : Prop :=
  ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)),
    ExitFree rs → IsSemiconj (ebSys1 N q rs) (ebSys N q rs) (inclF (σ := σ))

/-- Intended statement: the reduced field, and both readings of "is the EB model". -/
@[sa_reference "MorphismsCommon.header.ebSys1"]
def T : Prop := S1 ∧ S2 ∧ S3

@[sa_ref_forward "MorphismsCommon.header.ebSys1" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "MorphismsCommon.header.ebSys1" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1

@[sa_ref_forward "MorphismsCommon.header.ebSys1" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2

@[sa_complete "MorphismsCommon.header.ebSys1"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.MorphismsCommon.HeaderEbSys1

/-! ## `MorphismsCommon.maLiftFlatMap`

Blind text: "The mass-action field of `rs.flatMap g` is the sum over `r ∈ rs` of the fields of
`g r`."

For every list `rs` and every `g` sending its members to T_net reaction lists, at every point
`u : MA σ`: `maLift (rs.flatMap g) u = Σ_{r ∈ rs} maLift (g r) u`.

AMBIGUITY: the element type of `rs` is not named; it is read as arbitrary (T_EB reactions,
T_net reactions or anything else that `g` expands into T_net lists). -/

namespace Alignment.Shadows.MorphismsCommon.MaLiftFlatMap

/-- Intended statement. -/
@[sa_reference "MorphismsCommon.maLiftFlatMap"]
def T : Prop :=
  ∀ {σ : Type} [DecidableEq σ] {α : Type} (rs : List α) (g : α → List (NRxn σ)) (u : MA σ),
    maLift (rs.flatMap g) u = (rs.map fun r => maLift (g r) u).sum

/-- S1: the whole statement. -/
@[sa_shadow "MorphismsCommon.maLiftFlatMap" 1]
def S1 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] {α : Type} (rs : List α) (g : α → List (NRxn σ)) (u : MA σ),
    maLift (rs.flatMap g) u = (rs.map fun r => maLift (g r) u).sum

@[sa_ref_forward "MorphismsCommon.maLiftFlatMap" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MorphismsCommon.maLiftFlatMap"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MorphismsCommon.MaLiftFlatMap
