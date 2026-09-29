import NetworkEpi.Semantics.PoissonSIR
import NetworkEpi.Semantics.MA
import NetworkEpi.Semantics.Solutions

/-!
# L4: shared tools for the morphism catalogue (WP28)

DESIGN_NetworkEpiCore.md §D.5 (the morphism catalogue M1–M9) and §D.7 (modules L4a–L4g). This
module holds the pieces that several morphisms use:

* `isSemiconj_of_hasFDerivAt`, `isSemiconjOn_of_hasFDerivAt`: a (local) semiconjugacy from an
  explicit derivative;
* `clm_list_sum_eq`: the **per-reaction criterion**. Every field in this library is a sum of
  per-reaction fields, and the derivative of a map is linear, so a map is a semiconjugacy as soon
  as its derivative carries each per-reaction source field to the corresponding per-reaction
  target field. This is how the general-P theorems are proved;
* `IsConjOn` and `isSemiconjOn_inverse`: conjugacies (isomorphisms of `DynSys` between
  restrictions), and the fact that a differentiable two-sided inverse of a semiconjugacy is one;
* the coordinate projections of `EB σ` as continuous linear maps, and the derivative `suscD` of
  the susceptible fraction `S = qξψ(θ)`;
* the reduced EB system `ebSys1` on `ξ = 1` in coordinates `(θ, φ, pop)`, which is the EB model of
  an exit-free T_EB model in the design's coordinates (`ebSys1_incl`, `ebSys1_drop`).
-/

open scoped BigOperators

namespace NEP

section Tools

/-- A map with an explicit derivative `D u` at every point is a semiconjugacy if `D u` carries
the source field at `u` to the target field at `π u`. -/
theorem isSemiconj_of_hasFDerivAt {A B : DynSys} {π : A.V → B.V} (D : A.V → A.V →L[ℝ] B.V)
    (hD : ∀ u, HasFDerivAt π (D u) u) (hc : ∀ u, D u (A.F u) = B.F (π u)) :
    IsSemiconj A B π :=
  ⟨fun u => (hD u).differentiableAt, fun u => by rw [(hD u).fderiv]; exact hc u⟩

/-- Local version of `isSemiconj_of_hasFDerivAt` on a set `U`. -/
theorem isSemiconjOn_of_hasFDerivAt {A B : DynSys} {U : Set A.V} {π : A.V → B.V}
    (D : A.V → A.V →L[ℝ] B.V) (hD : ∀ u ∈ U, HasFDerivAt π (D u) u)
    (hc : ∀ u ∈ U, D u (A.F u) = B.F (π u)) : IsSemiconjOn A B U π :=
  ⟨fun u hu => (hD u hu).differentiableAt, fun u hu => by rw [(hD u hu).fderiv]; exact hc u hu⟩

/-- A continuous linear map commutes with the sum of a mapped list. -/
lemma clm_list_sum {E F ρ : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (rs : List ρ) (f : ρ → E) :
    L (rs.map f).sum = (rs.map fun r => L (f r)).sum := by
  induction rs with
  | nil => simp
  | cons r rs ih => simp [ih]

/-- **The per-reaction criterion.** If a continuous linear map `L` carries each per-reaction
source term `f r` to the per-reaction target term `g r`, it carries the sum over the reaction
list to the sum. -/
lemma clm_list_sum_eq {E F ρ : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (rs : List ρ) (f : ρ → E)
    (g : ρ → F) (h : ∀ r ∈ rs, L (f r) = g r) : L (rs.map f).sum = (rs.map g).sum := by
  rw [clm_list_sum]
  exact congrArg List.sum (List.map_congr_left h)

/-- **The per-reaction criterion, as one statement.** Let the fields of `A` and `B` be sums over
the same list `l` of per-reaction fields, `A.F u = Σ_{i ∈ l} f i u` and
`B.F w = Σ_{i ∈ l} g i w`. If `π : A.V → B.V` is differentiable and its derivative carries each
per-reaction source field to the corresponding target field,
`Dπ(u)·(f i u) = g i (π u)` for every `i ∈ l` and every `u`, then `π` is a semiconjugacy. -/
theorem isSemiconj_of_perReaction (A B : DynSys) {ι : Type} (l : List ι) (f : ι → A.V → A.V)
    (g : ι → B.V → B.V) (π : A.V → B.V) (hA : ∀ u, A.F u = (l.map fun i => f i u).sum)
    (hB : ∀ w, B.F w = (l.map fun i => g i w).sum) (hπ : Differentiable ℝ π)
    (hc : ∀ i ∈ l, ∀ u, fderiv ℝ π u (f i u) = g i (π u)) : IsSemiconj A B π := by
  refine ⟨hπ, fun u => ?_⟩
  rw [hA, hB]
  exact clm_list_sum_eq _ _ _ _ fun i hi => hc i hi u

/-- `IsConjOn A B V U h g`: `h` is a local semiconjugacy on `V` from `A` to `B` with
`h(V) ⊆ U`, `g` is a local semiconjugacy on `U` from `B` to `A` with `g(U) ⊆ V`, and they are
inverse to each other on these sets (`g (h u) = u` for `u ∈ V`, `h (g v) = v` for `v ∈ U`).
When `V` and `U` are invariant, this is a conjugacy (an isomorphism of `DynSys`) between the
restrictions of `A` to `V` and of `B` to `U`: `h` maps solutions that stay in `V` to solutions,
and `g` maps solutions that stay in `U` back. -/
def IsConjOn (A B : DynSys) (V : Set A.V) (U : Set B.V) (h : A.V → B.V) (g : B.V → A.V) :
    Prop :=
  IsSemiconjOn A B V h ∧ IsSemiconjOn B A U g ∧ (∀ u ∈ V, h u ∈ U) ∧ (∀ v ∈ U, g v ∈ V) ∧
    (∀ u ∈ V, g (h u) = u) ∧ ∀ v ∈ U, h (g v) = v

/-- **A differentiable inverse of a semiconjugacy is a semiconjugacy.** Let `h` be a local
semiconjugacy on `V` from `A` to `B`, and let `g : B.V → A.V` be a global left inverse of `h`
(`g ∘ h = id`) that is differentiable at every point of `U`, maps `U` into `V` and is a right
inverse on `U` (`h (g v) = v` for `v ∈ U`). Then `g` is a local semiconjugacy on `U` from `B` to
`A`. (Chain rule: `Dg(h w)·Dh(w) = id`, applied to `A.F w` with `w = g v`.) -/
theorem isSemiconjOn_inverse {A B : DynSys} {V : Set A.V} {U : Set B.V} {h : A.V → B.V}
    {g : B.V → A.V} (hh : IsSemiconjOn A B V h) (hg : ∀ v ∈ U, DifferentiableAt ℝ g v)
    (hgV : ∀ v ∈ U, g v ∈ V) (hgh : ∀ u, g (h u) = u) (hhg : ∀ v ∈ U, h (g v) = v) :
    IsSemiconjOn B A U g := by
  refine ⟨hg, fun v hv => ?_⟩
  have hvw : h (g v) = v := hhg v hv
  have hwV : g v ∈ V := hgV v hv
  have hgd : DifferentiableAt ℝ g (h (g v)) := by rw [hvw]; exact hg v hv
  have hd := fderiv_comp (g v) hgd (hh.1 (g v) hwV)
  have hcomp : g ∘ h = id := funext hgh
  rw [hcomp, fderiv_id] at hd
  have e := congrArg (fun L : A.V →L[ℝ] A.V => L (A.F (g v))) hd
  simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply] at e
  rw [hh.2 (g v) hwV, hvw] at e
  exact e.symm

/-- A conjugacy with `V = univ` built from a global semiconjugacy `h` and a differentiable
inverse `g` on `U`: `IsConjOn A B univ U h g`. -/
theorem isConjOn_of_inverse {A B : DynSys} {U : Set B.V} {h : A.V → B.V} {g : B.V → A.V}
    (hh : IsSemiconj A B h) (hg : ∀ v ∈ U, DifferentiableAt ℝ g v) (hU : ∀ u, h u ∈ U)
    (hgh : ∀ u, g (h u) = u) (hhg : ∀ v ∈ U, h (g v) = v) :
    IsConjOn A B Set.univ U h g := by
  have hh' : IsSemiconjOn A B Set.univ h := ⟨fun u _ => hh.1 u, fun u _ => hh.2 u⟩
  exact ⟨hh', isSemiconjOn_inverse hh' hg (fun _ _ => Set.mem_univ _) hgh hhg,
    fun u _ => hU u, fun _ _ => Set.mem_univ _, fun u _ => hgh u, hhg⟩

/-- Chain rule for `g ∘ P` with `P` a continuous linear map out of a topological vector space
`E` (for example `EB σ` with `σ` infinite, product topology) into a normed space. -/
theorem hasFDerivAt_comp_clm_tvs {E F G : Type} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] (P : E →L[ℝ] F) {g : F → G} {g' : F →L[ℝ] G} {u : E}
    (hg : HasFDerivAt g g' (P u)) : HasFDerivAt (fun v => g (P v)) (g'.comp P) u := by
  have hT : Filter.Tendsto (Prod.map P P) (nhds u ×ˢ pure u) (nhds (P u) ×ˢ pure (P u)) :=
    (P.continuous.tendsto u).prodMap (Filter.tendsto_pure_pure _ _)
  have h1 := (HasFDerivAtFilter.isLittleOTVS hg).comp_tendsto hT
  have hO : (fun p : E × E => P p.1 - P p.2) =O[ℝ; nhds u ×ˢ pure u]
      (fun p : E × E => p.1 - p.2) := by
    have := (P.isBigOTVS_id
      (l := Filter.map (fun p : E × E => p.1 - p.2) (nhds u ×ˢ pure u))).comp_tendsto
        Filter.tendsto_map
    refine this.congr_left ?_
    intro p; simp
  refine ⟨(h1.trans_isBigOTVS hO).congr_left ?_⟩
  intro p
  simp

end Tools

/-! ## Coordinates of `EB σ` as continuous linear maps -/

section Coordinates
variable {σ : Type}

/-- The coordinate `θ` of `EB σ = ℝ × ℝ × (σ → ℝ) × (σ → ℝ)` as a continuous linear map. -/
noncomputable def ebTheta : EB σ →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ _

/-- The coordinate `ξ` of `EB σ` as a continuous linear map. -/
noncomputable def ebXi : EB σ →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ _).comp (ContinuousLinearMap.snd ℝ ℝ _)

/-- The coordinates `φ` of `EB σ` as a continuous linear map. -/
noncomputable def ebPhi : EB σ →L[ℝ] (σ → ℝ) :=
  (ContinuousLinearMap.fst ℝ _ _).comp
    ((ContinuousLinearMap.snd ℝ ℝ _).comp (ContinuousLinearMap.snd ℝ ℝ _))

/-- The coordinates `pop` of `EB σ` as a continuous linear map. -/
noncomputable def ebPop : EB σ →L[ℝ] (σ → ℝ) :=
  (ContinuousLinearMap.snd ℝ _ _).comp
    ((ContinuousLinearMap.snd ℝ ℝ _).comp (ContinuousLinearMap.snd ℝ ℝ _))

/-- `ebTheta` is the θ-coordinate. -/
@[simp] lemma ebTheta_apply (u : EB σ) : ebTheta u = u.1 := rfl
/-- `ebXi` is the ξ-coordinate. -/
@[simp] lemma ebXi_apply (u : EB σ) : ebXi u = u.2.1 := rfl
/-- `ebPhi` is the φ-coordinate. -/
@[simp] lemma ebPhi_apply (u : EB σ) : ebPhi u = u.2.2.1 := rfl
/-- `ebPop` is the pop-coordinate. -/
@[simp] lemma ebPop_apply (u : EB σ) : ebPop u = u.2.2.2 := rfl

/-- The coordinate projections are their own derivatives. -/
lemma hasFDerivAt_ebTheta [Fintype σ] (u : EB σ) : HasFDerivAt (fun u : EB σ => u.1) (ebTheta (σ := σ)) u :=
  ebTheta.hasFDerivAt

/-- See `hasFDerivAt_ebTheta`. -/
lemma hasFDerivAt_ebXi [Fintype σ] (u : EB σ) : HasFDerivAt (fun u : EB σ => u.2.1) (ebXi (σ := σ)) u :=
  ebXi.hasFDerivAt

/-- See `hasFDerivAt_ebTheta`. -/
lemma hasFDerivAt_ebPhi [Fintype σ] (u : EB σ) : HasFDerivAt (fun u : EB σ => u.2.2.1) (ebPhi (σ := σ)) u :=
  ebPhi.hasFDerivAt

/-- See `hasFDerivAt_ebTheta`. -/
lemma hasFDerivAt_ebPop [Fintype σ] (u : EB σ) : HasFDerivAt (fun u : EB σ => u.2.2.2) (ebPop (σ := σ)) u :=
  ebPop.hasFDerivAt

/-- **The coordinate projections of `EB σ` are their own derivatives, for every species type
`σ`** (the φ and pop coordinates carry the product topology when `σ` is infinite):
`u ↦ θ`, `u ↦ ξ`, `u ↦ φ`, `u ↦ pop` have derivatives `ebTheta`, `ebXi`, `ebPhi`, `ebPop` at every
point. -/
theorem hasFDerivAt_ebCoordinates_any (u : EB σ) :
    HasFDerivAt (fun u : EB σ => u.1) (ebTheta (σ := σ)) u ∧
      HasFDerivAt (fun u : EB σ => u.2.1) (ebXi (σ := σ)) u ∧
      HasFDerivAt (fun u : EB σ => u.2.2.1) (ebPhi (σ := σ)) u ∧
      HasFDerivAt (fun u : EB σ => u.2.2.2) (ebPop (σ := σ)) u :=
  ⟨ebTheta.hasFDerivAt, ebXi.hasFDerivAt, ebPhi.hasFDerivAt, ebPop.hasFDerivAt⟩

/-- The derivative of the susceptible fraction `S = qξψ(θ)` at `u`, when `ψ'` is the derivative
of `ψ` at `θ`: `v ↦ q (v_ξ ψ(θ) + ξ ψ'(θ) v_θ)` (the same expression as `nodeTotalDeriv`). -/
noncomputable def suscD (N : CNet) (q : ℝ) (u : EB σ) : EB σ →L[ℝ] ℝ :=
  (q * N.ψ u.1) • ebXi + (q * u.2.1 * N.ψ' u.1) • ebTheta

/-- `suscD N q u v = q (v_ξ ψ(θ) + ξ ψ'(θ) v_θ)` with `(θ, ξ) = (u.1, u.2.1)`. -/
lemma suscD_apply (N : CNet) (q : ℝ) (u v : EB σ) :
    suscD N q u v = q * (v.2.1 * N.ψ u.1 + u.2.1 * (N.ψ' u.1 * v.1)) := by
  simp only [suscD, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ebXi_apply,
    ebTheta_apply, smul_eq_mul]
  ring

/-- `suscD N q u v = q (v_ξ ψ(θ) + ξ ψ'(θ) v_θ)`, products associated from the left as written. -/
lemma suscD_apply_left (N : CNet) (q : ℝ) (u v : EB σ) :
    suscD N q u v = q * (v.2.1 * N.ψ u.1 + u.2.1 * N.ψ' u.1 * v.1) := by
  rw [suscD_apply, mul_assoc (u.2.1)]

/-- `S = qξψ(θ)` has derivative `suscD N q u` at `u` when `ψ'(θ)` is the derivative of `ψ` at
`θ = u.1`. -/
lemma hasFDerivAt_susc [Fintype σ] (N : CNet) (q : ℝ) {u : EB σ} (hψ : HasDerivAt N.ψ (N.ψ' u.1) u.1) :
    HasFDerivAt (fun u : EB σ => N.susc q u.1 u.2.1) (suscD N q u) u := by
  have hψθ : HasFDerivAt (fun u : EB σ => N.ψ u.1) (N.ψ' u.1 • (ebTheta (σ := σ))) u :=
    hψ.comp_hasFDerivAt u (hasFDerivAt_ebTheta u)
  have h := ((hasFDerivAt_ebXi u).const_mul q).mul hψθ
  refine h.congr_fderiv ?_
  ext v <;> simp [suscD]
  ring

/-- `S = qξψ(θ)` has derivative `suscD N q u` at `u` when `ψ'(θ)` is the derivative of `ψ` at
`θ = u.1`, for every species type `σ` (product topology when `σ` is infinite). -/
theorem hasFDerivAt_susc_any (N : CNet) (q : ℝ) {u : EB σ}
    (hψ : HasDerivAt N.ψ (N.ψ' u.1) u.1) :
    HasFDerivAt (fun u : EB σ => N.susc q u.1 u.2.1) (suscD N q u) u := by
  let P : EB σ →L[ℝ] ℝ × ℝ := ebTheta.prod ebXi
  let g : ℝ × ℝ → ℝ := fun v => q * v.2 * N.ψ v.1
  let g' : ℝ × ℝ →L[ℝ] ℝ :=
    (q * N.ψ u.1) • ContinuousLinearMap.snd ℝ ℝ ℝ +
      (q * u.2.1 * N.ψ' u.1) • ContinuousLinearMap.fst ℝ ℝ ℝ
  have hg : HasFDerivAt g g' (P u) := by
    have h1 : HasFDerivAt (fun v : ℝ × ℝ => N.ψ v.1) (N.ψ' u.1 • ContinuousLinearMap.fst ℝ ℝ ℝ)
        (P u) := hψ.comp_hasFDerivAt (P u) (hasFDerivAt_fst (p := P u))
    have h2 := ((hasFDerivAt_snd (𝕜 := ℝ) (p := P u)).const_mul q).mul h1
    refine h2.congr_fderiv ?_
    ext <;> simp [g', P] <;> ring
  have h := hasFDerivAt_comp_clm_tvs P hg
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  rw [suscD_apply]
  simp only [g', P, ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.prod_apply, ebTheta_apply, ebXi_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  ring

end Coordinates

/-! ## The reduced EB system on `ξ = 1` -/

section Reduced
variable {σ : Type}

/-- The design's EB coordinates `(θ, φ, pop)` of an exit-free model (ξ ≡ 1 is dropped). -/
abbrev EB1 (σ : Type) := ℝ × (σ → ℝ) × (σ → ℝ)

/-- The inclusion `(θ, φ, pop) ↦ (θ, 1, φ, pop)` of the slice `ξ = 1`. -/
def EB1.incl (w : EB1 σ) : EB σ := (w.1, 1, w.2.1, w.2.2)

/-- The chart `(θ, ξ, φ, pop) ↦ (θ, φ, pop)`. -/
def EB.drop (u : EB σ) : EB1 σ := (u.1, u.2.2.1, u.2.2.2)

/-- `EB.drop` as a continuous linear map. -/
noncomputable def dropL : EB σ →L[ℝ] EB1 σ := ebTheta.prod (ebPhi.prod ebPop)

/-- `dropL` is `EB.drop`. -/
@[simp] lemma dropL_apply (u : EB σ) : dropL u = EB.drop u := rfl

/-- The linear part `(θ, φ, pop) ↦ (θ, 0, φ, pop)` of `EB1.incl`. -/
noncomputable def inclL : EB1 σ →L[ℝ] EB σ :=
  (ContinuousLinearMap.fst ℝ ℝ _).prod
    ((0 : EB1 σ →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ _))

/-- `inclL (θ, φ, pop) = (θ, 0, φ, pop)`. -/
@[simp] lemma inclL_apply (w : EB1 σ) : inclL w = (w.1, 0, w.2.1, w.2.2) := rfl

/-- `EB.drop` is a left inverse of `EB1.incl`. -/
lemma drop_incl (w : EB1 σ) : EB.drop (EB1.incl w) = w := rfl

/-- On `ξ = 1`, `EB1.incl` is a left inverse of `EB.drop`. -/
lemma incl_drop {u : EB σ} (hu : u.2.1 = 1) : EB1.incl (EB.drop u) = u := by
  obtain ⟨θ, ξ, φ, p⟩ := u
  simp only [EB1.incl, EB.drop]
  simp only at hu
  rw [hu]

/-- `EB1.incl` is affine with derivative `inclL`. -/
lemma hasFDerivAt_incl [Fintype σ] (w : EB1 σ) : HasFDerivAt (EB1.incl (σ := σ)) (inclL (σ := σ)) w := by
  have h : (EB1.incl (σ := σ)) = fun w => ((0 : ℝ), (1 : ℝ), (0 : σ → ℝ), (0 : σ → ℝ)) + inclL w := by
    funext w
    simp [EB1.incl]
  rw [h]
  exact inclL.hasFDerivAt.const_add _

/-- **`EB1.incl` is affine**: `EB1.incl w = inclL w + (0, 1, 0, 0)` for every `w`. -/
theorem incl_eq_inclL_add (w : EB1 σ) :
    EB1.incl w = inclL w + ((0 : ℝ), (1 : ℝ), (0 : σ → ℝ), (0 : σ → ℝ)) := by
  obtain ⟨θ, φ, p⟩ := w
  simp [EB1.incl]

/-- **`EB1.incl` is affine with linear part `inclL`**: there is a constant `c` with
`EB1.incl w = inclL w + c` for every `w` (namely `c = (0, 1, 0, 0)`, `incl_eq_inclL_add`). -/
theorem incl_affine : ∃ c : EB σ, ∀ w : EB1 σ, EB1.incl w = inclL w + c :=
  ⟨_, incl_eq_inclL_add⟩

/-- `EB1.incl` is affine with derivative `inclL`, for every species type `σ` (the φ and pop
coordinates carry the product topology when `σ` is infinite). -/
theorem hasFDerivAt_incl_any (w : EB1 σ) :
    HasFDerivAt (EB1.incl (σ := σ)) (inclL (σ := σ)) w := by
  have h : (EB1.incl (σ := σ)) = fun w => inclL w + ((0 : ℝ), (1 : ℝ), (0 : σ → ℝ), (0 : σ → ℝ)) :=
    funext incl_eq_inclL_add
  rw [h]
  obtain ⟨hL⟩ := (inclL (σ := σ)).hasFDerivAt (x := w)
  refine ⟨hL.congr_left fun p => ?_⟩
  simp only [map_sub]
  abel

variable [Fintype σ] [DecidableEq σ]

/-- The EB model on the slice `ξ = 1`, in the design's coordinates `(θ, φ, pop)`:
`F(θ, φ, pop) = drop (lift N q rs (θ, 1, φ, pop))`. For an exit-free model this is the EB model
itself (`ebSys1_incl`). -/
noncomputable def ebSys1 (N : CNet) (q : ℝ) (rs : List (Rxn σ)) : DynSys where
  V := EB1 σ
  F w := EB.drop (lift N q rs (EB1.incl w))

/-- **For an exit-free model, the EB model on `(θ, φ, pop)` is the restriction of the EB model to
the invariant slice `ξ = 1`**: `(θ, φ, pop) ↦ (θ, 1, φ, pop)` is a semiconjugacy from `ebSys1` to
`ebSys` (the ξ-component of the EB field vanishes without exits). -/
theorem ebSys1_incl (N : CNet) (q : ℝ) (rs : List (Rxn σ))
    (hrs : ∀ r ∈ rs, r.isExit = false) :
    IsSemiconj (ebSys1 N q rs) (ebSys N q rs) EB1.incl := by
  refine isSemiconj_of_hasFDerivAt (A := ebSys1 N q rs) (B := ebSys N q rs)
    (fun _ => inclL) hasFDerivAt_incl fun w => ?_
  change inclL (EB.drop (lift N q rs (EB1.incl w))) = lift N q rs (EB1.incl w)
  have h0 := lift_ξ_eq_zero N q rs hrs (EB1.incl w)
  simp only [inclL_apply, EB.drop]
  exact Prod.ext rfl (Prod.ext h0.symm rfl)

/-- The chart `(θ, ξ, φ, pop) ↦ (θ, φ, pop)` is a local semiconjugacy on `{ξ = 1}` from `ebSys`
to `ebSys1` (for every T_EB model). -/
theorem ebSys1_drop (N : CNet) (q : ℝ) (rs : List (Rxn σ)) :
    IsSemiconjOn (ebSys N q rs) (ebSys1 N q rs) {u | u.2.1 = 1} EB.drop := by
  refine isSemiconjOn_of_hasFDerivAt (A := ebSys N q rs) (B := ebSys1 N q rs)
    (fun _ => dropL) (fun u _ => dropL.hasFDerivAt) fun u hu => ?_
  change EB.drop (lift N q rs u) = EB.drop (lift N q rs (EB1.incl (EB.drop u)))
  rw [incl_drop hu]

/-- The field of `ebSys1` is `(θ, φ, pop) ↦ drop (lift N q rs (θ, 1, φ, pop))` (its definition,
stated as a theorem). -/
theorem ebSys1_F (N : CNet) (q : ℝ) (rs : List (Rxn σ)) (w : EB1 σ) :
    (ebSys1 N q rs).F w = EB.drop (lift N q rs (EB1.incl w)) :=
  rfl

/-- **Without exits, the slice `ξ = 1` is invariant.** Let `rs` have no exit, let `I` be a
convex set of times and let `x` solve the EB model of `rs` within `I` at every `t ∈ I`. If
`ξ(t₀) = 1` for some `t₀ ∈ I`, then `ξ(t) = 1` for every `t ∈ I`. -/
theorem ebSys_xi_slice_invariant (N : CNet) (q : ℝ) (rs : List (Rxn σ))
    (hrs : ∀ r ∈ rs, r.isExit = false) {I : Set ℝ} (hI : Convex ℝ I) {x : ℝ → EB σ}
    (hx : ∀ t ∈ I, HasDerivWithinAt x ((ebSys N q rs).F (x t)) I t) {t₀ : ℝ} (ht₀ : t₀ ∈ I)
    (h1 : (x t₀).2.1 = 1) : ∀ t ∈ I, (x t).2.1 = 1 := by
  have hd : ∀ t ∈ I, HasDerivWithinAt (fun t => (x t).2.1) 0 I t := by
    intro t ht
    have h := hasDerivWithinAt_ξ (hx t ht)
    rwa [show ((ebSys N q rs).F (x t)).2.1 = 0 from lift_ξ_eq_zero N q rs hrs (x t)] at h
  intro t ht
  rw [const_of_hasDerivWithinAt_zero (g := fun t => (x t).2.1) hI hd ht₀ ht, h1]

/-- **For an exit-free model, `ebSys1` is conjugate to the EB model on the slice `ξ = 1`.** The
inclusion `(θ, φ, pop) ↦ (θ, 1, φ, pop)` and the chart `(θ, ξ, φ, pop) ↦ (θ, φ, pop)` form an
`IsConjOn (ebSys1 N q rs) (ebSys N q rs) univ {ξ = 1}` pair: both are (local) semiconjugacies,
they map `univ` and `{ξ = 1}` into each other, and they are mutually inverse there. -/
theorem ebSys1_conj (N : CNet) (q : ℝ) (rs : List (Rxn σ)) (hrs : ∀ r ∈ rs, r.isExit = false) :
    IsConjOn (ebSys1 N q rs) (ebSys N q rs) Set.univ {u | u.2.1 = 1} EB1.incl EB.drop := by
  have hi := ebSys1_incl N q rs hrs
  exact ⟨⟨fun u _ => hi.1 u, fun u _ => hi.2 u⟩, ebSys1_drop N q rs,
    fun _ _ => rfl, fun _ _ => Set.mem_univ _, fun w _ => drop_incl w, fun u hu => incl_drop hu⟩

end Reduced

/-- The field of the EB model is the sum of the per-reaction EB fields over the reaction list. -/
theorem ebSys_F_eq_sum {σ : Type} [Fintype σ] [DecidableEq σ] (N : CNet) (q : ℝ)
    (rs : List (Rxn σ)) (u : EB σ) :
    (ebSys N q rs).F u = (rs.map fun r => ebField N q r u).sum :=
  rfl

/-- The field of the mass-action model is the sum of the per-reaction mass-action fields over the
reaction list. -/
theorem maSys_F_eq_sum {σ : Type} [Fintype σ] [DecidableEq σ] (rs : List (NRxn σ)) (u : MA σ) :
    (maSys rs).F u = (rs.map fun r => maField r u).sum :=
  rfl

/-! ## Mass action of concatenated reaction lists -/

section MAFlat
variable {σ ρ : Type} [DecidableEq σ]

/-- The mass-action field of `rs.flatMap g` is the sum over `r ∈ rs` of the fields of `g r`. -/
lemma maLift_flatMap (g : ρ → List (NRxn σ)) (rs : List ρ) (v : MA σ) :
    maLift (rs.flatMap g) v = (rs.map fun r => maLift (g r) v).sum := by
  induction rs with
  | nil => simp [maLift]
  | cons r rs ih => rw [List.flatMap_cons, maLift_append, ih, List.map_cons, List.sum_cons]

end MAFlat

end NEP
