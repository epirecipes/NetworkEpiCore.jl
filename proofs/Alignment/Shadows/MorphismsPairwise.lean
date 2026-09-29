import Alignment.Registry
import NetworkEpi.Morphisms.Pairwise

/-!
# Blind shadow sets: group `MorphismsPairwise` (DESIGN §D.5 M6, M8; §A.4; §L.3)

Written blind: from the entries of `Alignment/claims_blind.yaml` for the ids below,
`Alignment/DataTypes/MorphismsPairwise.md`, `Alignment/README.md`,
`Alignment/Example/ExampleShadows.lean` and `DESIGN_NetworkEpiCore.md` (§0, §C.3, §D.3, §D.5
M6/M8, §L.3). No trusted statement, definition body or checker was read.

Re-shadowed blind after the text remediation (ids `ebToPwsSolution`, `ebToPwsSir`,
`ebToPwsSeir`, `ebToPwsPt`, `ebToPwsPoisson`, `pwsEbField`, `pwsDomainPoisson`): the M6 texts now
say "for every C² ψ and every T_EB model", so these shadows use the global `C2 N` and the
unrestricted domain `DomU0 N`; local semiconjugacies are split into `DiffOnU` and `CommOnU`.

Shared primitive notions (in namespace `Alignment.Shadows.MorphismsPairwise`):

* `Derivs N Θ`: "ψ' and ψ'' are the derivatives of ψ and ψ'" at every θ ∈ Θ, as `HasDerivAt`.
* `C2 N`: "C² ψ" via `HasDerivAt` hypotheses at every θ (§D.7 L4e: "generic C² ψ via
  `HasDerivAt` hypotheses").
* `DomU N Θ`: the M6 domain written out, `U = {θ ∈ Θ, ψ(θ) ≠ 0, ψ'(θ) ≠ 0, ξ ≠ 0}` (§L.3:
  "Domain U = {ψ ≠ 0, ψ' ≠ 0, ξ ≠ 0} with q ≠ 0").
* `DomU0 N`: the same domain without a restriction on θ (for "every C² ψ").
-/

open NEP

namespace Alignment.Shadows.MorphismsPairwise

/-- ψ' and ψ'' are the derivatives of ψ and ψ' at every θ ∈ Θ. -/
def Derivs (N : CNet) (Θ : Set ℝ) : Prop :=
  ∀ θ ∈ Θ, HasDerivAt N.ψ (N.ψ' θ) θ ∧ HasDerivAt N.ψ' (N.ψ'' θ) θ

/-- "C² ψ", via `HasDerivAt` relations between the free functions ψ, ψ', ψ'' at every θ. -/
def C2 (N : CNet) : Prop :=
  ∀ θ : ℝ, HasDerivAt N.ψ (N.ψ' θ) θ ∧ HasDerivAt N.ψ' (N.ψ'' θ) θ

/-- The M6 domain `U = {θ ∈ Θ, ψ(θ) ≠ 0, ψ'(θ) ≠ 0, ξ ≠ 0}` in primitive terms
(`u = (θ, ξ, φ, pop)`, so `u.1 = θ`, `u.2.1 = ξ`). -/
def DomU {σ : Type} (N : CNet) (Θ : Set ℝ) : Set (EB σ) :=
  {u | u.1 ∈ Θ ∧ N.ψ u.1 ≠ 0 ∧ N.ψ' u.1 ≠ 0 ∧ u.2.1 ≠ 0}

/-- The M6 domain `U = {ψ(θ) ≠ 0, ψ'(θ) ≠ 0, ξ ≠ 0}` (no restriction on θ). -/
def DomU0 {σ : Type} (N : CNet) : Set (EB σ) :=
  {u | N.ψ u.1 ≠ 0 ∧ N.ψ' u.1 ≠ 0 ∧ u.2.1 ≠ 0}

/-- "PT (Poisson type) of ψ on Θ with exponent κ": `ψ' = αψ^κ` on Θ for some α (real power). -/
def PT (N : CNet) (Θ : Set ℝ) (κ : ℝ) : Prop :=
  ∃ α : ℝ, ∀ θ ∈ Θ, N.ψ' θ = α * N.ψ θ ^ κ

end Alignment.Shadows.MorphismsPairwise

/-! ### Shared notions added by the re-shadow of the M6 instances (text remediation)

"π is a local semiconjugacy A → B on U" (DESIGN §D.3, "Local version `SemiconjOn U`. The
identity holds on an open set U") is split into its two requirements, as the DataTypes
docstring of `IsSemiconjOn` describes them: differentiability at every point of U (`DiffOnU`)
and the conjugacy identity `Dπ(u)·F(u) = G(π(u))` at every point of U (`CommOnU`). -/
namespace Alignment.Shadows.MorphismsPairwise

/-- `π` is differentiable at every point of `U`. -/
def DiffOnU (A B : DynSys) (U : Set A.V) (π : A.V → B.V) : Prop :=
  ∀ u ∈ U, DifferentiableAt ℝ π u

/-- `Dπ(u)·F(u) = G(π(u))` at every point of `U` (the semiconjugacy identity). -/
def CommOnU (A B : DynSys) (U : Set A.V) (π : A.V → B.V) : Prop :=
  ∀ u ∈ U, fderiv ℝ π u (A.F u) = B.F (π u)

end Alignment.Shadows.MorphismsPairwise

/-! ## `MorphismsPairwise.ebToPws`

Blind text (Lean statement part): "for every T_EB reaction list (contacts, exits, progressions,
removals), every configuration network and every set Θ of θ values at which ψ' and ψ'' are the
derivatives of ψ and ψ', π^PW is a local semiconjugacy from EB to `pgfSys` on
`U = {θ ∈ Θ, ψ(θ) ≠ 0, ψ'(θ) ≠ 0, ξ ≠ 0}` (for `q ≠ 0`)." plus "No condition on ψ'(1) is
needed" (hence: no hypothesis on ψ'(1)). -/
namespace Alignment.Shadows.MorphismsPairwise.EbToPws
open Alignment.Shadows.MorphismsPairwise

@[sa_reference "MorphismsPairwise.ebToPws"]
def T : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)) (Θ : Set ℝ),
    q ≠ 0 → Derivs N Θ →
      IsSemiconjOn (ebSys N q rs) (pgfSys N rs) (DomU N Θ) (pwImage N q)

/-- S1: the whole (atomic) statement: π^PW is a local semiconjugacy EB → `pgfSys` on U. -/
@[sa_shadow "MorphismsPairwise.ebToPws" 1]
def S1 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)) (Θ : Set ℝ),
    q ≠ 0 → Derivs N Θ →
      IsSemiconjOn (ebSys N q rs) (pgfSys N rs) (DomU N Θ) (pwImage N q)

@[sa_ref_forward "MorphismsPairwise.ebToPws" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MorphismsPairwise.ebToPws"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MorphismsPairwise.EbToPws

/-! ## `MorphismsPairwise.ebToPwsSolution`

Blind text (re-shadowed after text remediation): Design statement (§D.5, M6): "π^PW(θ, ξ, φ,
pop) = (θ, [s] = qξψ(θ), [sX] = qξψ'(θ)φ_X, [ss] = q²ξ²ψ'(θ)²/ψ'(1), [X] = pop_X) onto PW^S
with closure [Z s J] = K_ψ(θ)[Zs][sJ]/[s], K_ψ = ψψ''/ψ'². It holds **for every C² ψ and every
T_EB model**, on U = {ψ ≠ 0, ψ' ≠ 0}"; §D.3: "solutions that stay in U are mapped". [...] "EB
solutions that stay in `U` map to PGF-closure solutions."

Formalisation:
* "every T_EB model": every finite species type σ (with decidable equality) and every reaction
  list `rs : List (Rxn σ)`; the EB model is `ebSys N q rs`, the PGF-closure model `pgfSys N rs`,
  π^PW is `pwImage N q`.
* "every C² ψ": `C2 N`, the `HasDerivAt` relations ψ → ψ' → ψ'' at every θ (DataTypes (e)).
  No other condition on ψ (in particular none on ψ(1) or ψ'(1)).
* U: AMBIGUITY: the quoted U = {ψ ≠ 0, ψ' ≠ 0} vs the binding amendment §L.3 "Domain
  U = {ψ ≠ 0, ψ' ≠ 0, ξ ≠ 0} with q ≠ 0" (which supersedes §D.5). The amended domain `DomU0 N`
  and `q ≠ 0` are adopted (the unamended one divides by [s] = qξψ(θ) = 0).
* "solutions": AMBIGUITY: DataTypes (f) gives two notions of a solution on a set of times `I`
  (two-sided `HasDerivAt` at every `t ∈ I`, or `HasDerivWithinAt … I t`); the text fixes
  neither and puts no condition on `I` (interval, 0 ∈ I, …). Both readings are required, for
  an arbitrary set `I` and an arbitrary curve `x`. "Stay in U": `x t ∈ U` for every `t ∈ I`. -/
namespace Alignment.Shadows.MorphismsPairwise.EbToPwsSolution
open Alignment.Shadows.MorphismsPairwise

/-- Reading 1: solutions with two-sided derivatives at every time of `I`. -/
def R1 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ))
    (I : Set ℝ) (x : ℝ → EB σ),
    q ≠ 0 → C2 N →
      (∀ t ∈ I, HasDerivAt x ((ebSys N q rs).F (x t)) t) →
      (∀ t ∈ I, x t ∈ DomU0 N) →
        ∀ t ∈ I, HasDerivAt (fun s => pwImage N q (x s))
          ((pgfSys N rs).F (pwImage N q (x t))) t

/-- Reading 2: solutions with derivatives within `I` at every time of `I`. -/
def R2 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ))
    (I : Set ℝ) (x : ℝ → EB σ),
    q ≠ 0 → C2 N →
      (∀ t ∈ I, HasDerivWithinAt x ((ebSys N q rs).F (x t)) I t) →
      (∀ t ∈ I, x t ∈ DomU0 N) →
        ∀ t ∈ I, HasDerivWithinAt (fun s => pwImage N q (x s))
          ((pgfSys N rs).F (pwImage N q (x t))) I t

@[sa_reference "MorphismsPairwise.ebToPwsSolution"]
def T : Prop := R1 ∧ R2

/-- S1: every C² ψ, every T_EB model: an EB solution (two-sided derivatives on `I`) that stays
in U maps under π^PW to a `pgfSys` solution on `I`. -/
@[sa_shadow "MorphismsPairwise.ebToPwsSolution" 1]
def S1 : Prop := R1

/-- S2: the same for solutions in the within-`I` sense. -/
@[sa_shadow "MorphismsPairwise.ebToPwsSolution" 2]
def S2 : Prop := R2

@[sa_ref_forward "MorphismsPairwise.ebToPwsSolution" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "MorphismsPairwise.ebToPwsSolution" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "MorphismsPairwise.ebToPwsSolution"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.MorphismsPairwise.EbToPwsSolution

/-! ## `MorphismsPairwise.ebToPwsSir`

Blind text: "**EB → PW^S for SIR (M6, SIR instance).** Design statement (§D.5, M6): "It holds
**for every C² ψ and every T_EB model**, on U = {ψ ≠ 0, ψ' ≠ 0}"; §D.7, L4e: "SIR and SEIR with
generic C² ψ via `HasDerivAt` hypotheses"."

"It" is M6: π^PW is a (local) semiconjugacy EB → PW^S with the PGF closure K_ψ(θ) (`pgfSys`,
which carries the auxiliary θ, DataTypes (e)). SIR instance: `sirRxns τ γ` for all rates τ, γ.
"Generic C² ψ via `HasDerivAt` hypotheses": `C2 N`. U: the §L.3 amendment (see
`ebToPwsSolution`): `DomU0 N` with `q ≠ 0`. The local semiconjugacy is split into
differentiability of π^PW on U (S1) and the identity Dπ·F_EB = F_PGF∘π on U (S2). -/
namespace Alignment.Shadows.MorphismsPairwise.EbToPwsSir
open Alignment.Shadows.MorphismsPairwise

@[sa_reference "MorphismsPairwise.ebToPwsSir"]
def T : Prop :=
  ∀ (N : CNet) (q τ γ : ℝ), q ≠ 0 → C2 N →
    DiffOnU (ebSys N q (sirRxns τ γ)) (pgfSys N (sirRxns τ γ)) (DomU0 N) (pwImage N q) ∧
      CommOnU (ebSys N q (sirRxns τ γ)) (pgfSys N (sirRxns τ γ)) (DomU0 N) (pwImage N q)

/-- S1: π^PW is differentiable at every point of U (SIR, every C² ψ, all rates). -/
@[sa_shadow "MorphismsPairwise.ebToPwsSir" 1]
def S1 : Prop :=
  ∀ (N : CNet) (q τ γ : ℝ), q ≠ 0 → C2 N →
    DiffOnU (ebSys N q (sirRxns τ γ)) (pgfSys N (sirRxns τ γ)) (DomU0 N) (pwImage N q)

/-- S2: Dπ^PW carries the EB SIR field to the PGF-closure SIR field at every point of U. -/
@[sa_shadow "MorphismsPairwise.ebToPwsSir" 2]
def S2 : Prop :=
  ∀ (N : CNet) (q τ γ : ℝ), q ≠ 0 → C2 N →
    CommOnU (ebSys N q (sirRxns τ γ)) (pgfSys N (sirRxns τ γ)) (DomU0 N) (pwImage N q)

@[sa_ref_forward "MorphismsPairwise.ebToPwsSir" 1]
theorem ref_fwd1 : T → S1 := fun t N q τ γ hq hc => (t N q τ γ hq hc).1

@[sa_ref_forward "MorphismsPairwise.ebToPwsSir" 2]
theorem ref_fwd2 : T → S2 := fun t N q τ γ hq hc => (t N q τ γ hq hc).2

@[sa_complete "MorphismsPairwise.ebToPwsSir"]
theorem complete (s1 : S1) (s2 : S2) : T :=
  fun N q τ γ hq hc => ⟨s1 N q τ γ hq hc, s2 N q τ γ hq hc⟩

end Alignment.Shadows.MorphismsPairwise.EbToPwsSir

/-! ## `MorphismsPairwise.ebToPwsSeir`

Blind text: same design statement as `ebToPwsSir`, SEIR instance: `seirRxns τ a γ` for all rates
(the E → I rate is σ in the design, `a` here). Same reading and split as `ebToPwsSir`. -/
namespace Alignment.Shadows.MorphismsPairwise.EbToPwsSeir
open Alignment.Shadows.MorphismsPairwise

@[sa_reference "MorphismsPairwise.ebToPwsSeir"]
def T : Prop :=
  ∀ (N : CNet) (q τ a γ : ℝ), q ≠ 0 → C2 N →
    DiffOnU (ebSys N q (seirRxns τ a γ)) (pgfSys N (seirRxns τ a γ)) (DomU0 N) (pwImage N q) ∧
      CommOnU (ebSys N q (seirRxns τ a γ)) (pgfSys N (seirRxns τ a γ)) (DomU0 N) (pwImage N q)

/-- S1: π^PW is differentiable at every point of U (SEIR, every C² ψ, all rates). -/
@[sa_shadow "MorphismsPairwise.ebToPwsSeir" 1]
def S1 : Prop :=
  ∀ (N : CNet) (q τ a γ : ℝ), q ≠ 0 → C2 N →
    DiffOnU (ebSys N q (seirRxns τ a γ)) (pgfSys N (seirRxns τ a γ)) (DomU0 N) (pwImage N q)

/-- S2: Dπ^PW carries the EB SEIR field to the PGF-closure SEIR field at every point of U. -/
@[sa_shadow "MorphismsPairwise.ebToPwsSeir" 2]
def S2 : Prop :=
  ∀ (N : CNet) (q τ a γ : ℝ), q ≠ 0 → C2 N →
    CommOnU (ebSys N q (seirRxns τ a γ)) (pgfSys N (seirRxns τ a γ)) (DomU0 N) (pwImage N q)

@[sa_ref_forward "MorphismsPairwise.ebToPwsSeir" 1]
theorem ref_fwd1 : T → S1 := fun t N q τ a γ hq hc => (t N q τ a γ hq hc).1

@[sa_ref_forward "MorphismsPairwise.ebToPwsSeir" 2]
theorem ref_fwd2 : T → S2 := fun t N q τ a γ hq hc => (t N q τ a γ hq hc).2

@[sa_complete "MorphismsPairwise.ebToPwsSeir"]
theorem complete (s1 : S1) (s2 : S2) : T :=
  fun N q τ a γ hq hc => ⟨s1 N q τ a γ hq hc, s2 N q τ a γ hq hc⟩

end Alignment.Shadows.MorphismsPairwise.EbToPwsSeir

/-! ## `MorphismsPairwise.ebToPwsConst`

Blind text: "if `K_ψ ≡ κ` on Θ, the PW^S part alone, with the **constant** closure κ, is the
image of EB: the constant-closure pairwise model is exact." (M6 context: every T_EB list, every
network, Θ where ψ', ψ'' are the derivatives, U as in `ebToPws`, `q ≠ 0`.)
"The PW^S part alone" is π^PW without θ, `(pwImage N q u).2`; "is the image of EB" / "exact" is
read as a local semiconjugacy on U onto `pwSSys κ rs`. -/
namespace Alignment.Shadows.MorphismsPairwise.EbToPwsConst
open Alignment.Shadows.MorphismsPairwise

@[sa_reference "MorphismsPairwise.ebToPwsConst"]
def T : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)) (Θ : Set ℝ)
    (κ : ℝ),
    q ≠ 0 → Derivs N Θ → (∀ θ ∈ Θ, N.closureK θ = κ) →
      IsSemiconjOn (ebSys N q rs) (pwSSys κ rs) (DomU N Θ) (fun u => (pwImage N q u).2)

/-- S1: the whole (atomic) statement. -/
@[sa_shadow "MorphismsPairwise.ebToPwsConst" 1]
def S1 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)) (Θ : Set ℝ)
    (κ : ℝ),
    q ≠ 0 → Derivs N Θ → (∀ θ ∈ Θ, N.closureK θ = κ) →
      IsSemiconjOn (ebSys N q rs) (pwSSys κ rs) (DomU N Θ) (fun u => (pwImage N q u).2)

@[sa_ref_forward "MorphismsPairwise.ebToPwsConst" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MorphismsPairwise.ebToPwsConst"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MorphismsPairwise.EbToPwsConst

/-! ## `MorphismsPairwise.ebToPwsPt`

Blind text: "**For a Poisson-type degree distribution the constant closure is exact (M8 ⇒ M6).**
Design statement (§D.5, M8): "PT ⇔ constant closure | On an interval I with ψ > 0: K_ψ ≡ κ ⇔
ψ' = αψ^κ [...] So NBM's constant closure ⟨k(k−1)⟩/⟨k⟩² is exact **iff** the degree
distribution is PT"; §C.3: "heterogeneous pairwise with constant K = closure_constant(d) (exact
iff PT, M8)". [...] the "if" direction of "exact iff PT""

Formalisation:
* Hypotheses from the text: Θ an interval (`Convex ℝ Θ`, non-degenerate: `(interior Θ).Nonempty`),
  ψ > 0 on Θ, ψ PT on Θ with exponent κ (`PT N Θ κ`: ψ' = αψ^κ for some α), ψ', ψ'' the
  derivatives of ψ, ψ' on Θ (`Derivs N Θ`, the C² content), `q ≠ 0`; every T_EB model.
* "exact": the PW^S part of π^PW, `u ↦ (pwImage N q u).2` (π^PW without θ), is a local
  semiconjugacy EB → PW^S with the constant closure (`pwSSys K rs`) on the M6 domain restricted
  to Θ, `DomU N Θ` (§L.3: U = {ψ ≠ 0, ψ' ≠ 0, ξ ≠ 0}). Split into differentiability and the
  semiconjugacy identity.
* AMBIGUITY: "the constant closure". Reading 1: the closure constant is the PT exponent κ (M8:
  K_ψ ≡ κ ⇔ ψ' = αψ^κ). Reading 2: NBM's constant closure ⟨k(k−1)⟩/⟨k⟩² = ψ''(1)/ψ'(1)²
  (§C.1 `closure_constant(d)`, DataTypes (e)); for this reading ψ must be a PGF at 1
  (`1 ∈ Θ`, `ψ(1) = 1`). Both identities are required (S2, S3); differentiability (S1) is
  common to both readings. -/
namespace Alignment.Shadows.MorphismsPairwise.EbToPwsPt
open Alignment.Shadows.MorphismsPairwise

/-- The hypotheses of the text (reading 1). -/
def Hyp (N : CNet) (q : ℝ) (Θ : Set ℝ) (κ : ℝ) : Prop :=
  q ≠ 0 ∧ Derivs N Θ ∧ Convex ℝ Θ ∧ (interior Θ).Nonempty ∧ (∀ θ ∈ Θ, 0 < N.ψ θ) ∧ PT N Θ κ

/-- Reading 1: PT with exponent κ ⇒ PW^S with constant closure κ is the image of EB. -/
def R1 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)) (Θ : Set ℝ)
    (κ : ℝ), Hyp N q Θ κ →
      DiffOnU (ebSys N q rs) (pwSSys κ rs) (DomU N Θ) (fun u => (pwImage N q u).2) ∧
        CommOnU (ebSys N q rs) (pwSSys κ rs) (DomU N Θ) (fun u => (pwImage N q u).2)

/-- Reading 2: PT ⇒ NBM's constant closure ψ''(1)/ψ'(1)² is exact (ψ a PGF: 1 ∈ Θ, ψ(1) = 1). -/
def R2 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)) (Θ : Set ℝ)
    (κ : ℝ), Hyp N q Θ κ → (1 : ℝ) ∈ Θ → N.ψ 1 = 1 →
      DiffOnU (ebSys N q rs) (pwSSys (N.ψ'' 1 / N.ψ' 1 ^ 2) rs) (DomU N Θ)
          (fun u => (pwImage N q u).2) ∧
        CommOnU (ebSys N q rs) (pwSSys (N.ψ'' 1 / N.ψ' 1 ^ 2) rs) (DomU N Θ)
          (fun u => (pwImage N q u).2)

@[sa_reference "MorphismsPairwise.ebToPwsPt"]
def T : Prop := R1 ∧ R2

/-- S1: under the text's hypotheses the PW^S part of π^PW is differentiable on U. -/
@[sa_shadow "MorphismsPairwise.ebToPwsPt" 1]
def S1 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)) (Θ : Set ℝ)
    (κ : ℝ), Hyp N q Θ κ →
      DiffOnU (ebSys N q rs) (pwSSys κ rs) (DomU N Θ) (fun u => (pwImage N q u).2)

/-- S2: PT with exponent κ on an interval with ψ > 0 ⇒ the semiconjugacy identity onto PW^S
with constant closure κ holds on U. -/
@[sa_shadow "MorphismsPairwise.ebToPwsPt" 2]
def S2 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)) (Θ : Set ℝ)
    (κ : ℝ), Hyp N q Θ κ →
      CommOnU (ebSys N q rs) (pwSSys κ rs) (DomU N Θ) (fun u => (pwImage N q u).2)

/-- S3: PT ⇒ the semiconjugacy identity onto PW^S with NBM's constant closure ψ''(1)/ψ'(1)²
holds on U. -/
@[sa_shadow "MorphismsPairwise.ebToPwsPt" 3]
def S3 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (N : CNet) (q : ℝ) (rs : List (Rxn σ)) (Θ : Set ℝ)
    (κ : ℝ), Hyp N q Θ κ → (1 : ℝ) ∈ Θ → N.ψ 1 = 1 →
      CommOnU (ebSys N q rs) (pwSSys (N.ψ'' 1 / N.ψ' 1 ^ 2) rs) (DomU N Θ)
        (fun u => (pwImage N q u).2)

@[sa_ref_forward "MorphismsPairwise.ebToPwsPt" 1]
theorem ref_fwd1 : T → S1 := by
  intro t σ _ _ N q rs Θ κ h; exact (t.1 N q rs Θ κ h).1

@[sa_ref_forward "MorphismsPairwise.ebToPwsPt" 2]
theorem ref_fwd2 : T → S2 := by
  intro t σ _ _ N q rs Θ κ h; exact (t.1 N q rs Θ κ h).2

@[sa_ref_forward "MorphismsPairwise.ebToPwsPt" 3]
theorem ref_fwd3 : T → S3 := by
  intro t σ _ _ N q rs Θ κ h h1 h2; exact (t.2 N q rs Θ κ h h1 h2).2

@[sa_complete "MorphismsPairwise.ebToPwsPt"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := by
  refine ⟨?_, ?_⟩
  · intro σ _ _ N q rs Θ κ h
    exact ⟨s1 N q rs Θ κ h, s2 N q rs Θ κ h⟩
  · intro σ _ _ N q rs Θ κ h h1 h2
    -- differentiability does not depend on the target's closure constant
    exact ⟨s1 N q rs Θ κ h, s3 N q rs Θ κ h h1 h2⟩

end Alignment.Shadows.MorphismsPairwise.EbToPwsPt

/-! ## `MorphismsPairwise.ebToPwsPoisson`

Blind text: "**On a Poisson network the constant closure K = 1 is exact (M6, M8, Poisson
instance).** Design statement (§D.5, M8): "So NBM's constant closure ⟨k(k−1)⟩/⟨k⟩² is exact
**iff** the degree distribution is PT"; §0: "This covers Poisson (κ = 1)"."

Read as: for every μ, every T_EB model and `q ≠ 0`, the PW^S part of π^PW is a local
semiconjugacy from EB on Poisson(μ) to `pwSSys 1 rs` on the M6 domain
`U = {ψ ≠ 0, ψ' ≠ 0, ξ ≠ 0}` (§L.3; no θ restriction: Poisson's ψ is smooth everywhere).
Split into differentiability (S1) and the identity (S2).
AMBIGUITY: the text places no condition on μ; the statement is required for every μ (for μ = 0,
ψ' ≡ 0 and the domain is empty). -/
namespace Alignment.Shadows.MorphismsPairwise.EbToPwsPoisson
open Alignment.Shadows.MorphismsPairwise

@[sa_reference "MorphismsPairwise.ebToPwsPoisson"]
def T : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (μ q : ℝ) (rs : List (Rxn σ)), q ≠ 0 →
    DiffOnU (ebSys (CNet.poisson μ) q rs) (pwSSys 1 rs) (DomU0 (CNet.poisson μ))
        (fun u => (pwImage (CNet.poisson μ) q u).2) ∧
      CommOnU (ebSys (CNet.poisson μ) q rs) (pwSSys 1 rs) (DomU0 (CNet.poisson μ))
        (fun u => (pwImage (CNet.poisson μ) q u).2)

/-- S1: on Poisson(μ) the PW^S part of π^PW is differentiable at every point of U. -/
@[sa_shadow "MorphismsPairwise.ebToPwsPoisson" 1]
def S1 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (μ q : ℝ) (rs : List (Rxn σ)), q ≠ 0 →
    DiffOnU (ebSys (CNet.poisson μ) q rs) (pwSSys 1 rs) (DomU0 (CNet.poisson μ))
      (fun u => (pwImage (CNet.poisson μ) q u).2)

/-- S2: on Poisson(μ) the semiconjugacy identity onto PW^S with constant closure K = 1 holds at
every point of U. -/
@[sa_shadow "MorphismsPairwise.ebToPwsPoisson" 2]
def S2 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] [Fintype σ] (μ q : ℝ) (rs : List (Rxn σ)), q ≠ 0 →
    CommOnU (ebSys (CNet.poisson μ) q rs) (pwSSys 1 rs) (DomU0 (CNet.poisson μ))
      (fun u => (pwImage (CNet.poisson μ) q u).2)

@[sa_ref_forward "MorphismsPairwise.ebToPwsPoisson" 1]
theorem ref_fwd1 : T → S1 := by
  intro t σ _ _ μ q rs hq; exact (t μ q rs hq).1

@[sa_ref_forward "MorphismsPairwise.ebToPwsPoisson" 2]
theorem ref_fwd2 : T → S2 := by
  intro t σ _ _ μ q rs hq; exact (t μ q rs hq).2

@[sa_complete "MorphismsPairwise.ebToPwsPoisson"]
theorem complete (s1 : S1) (s2 : S2) : T := by
  intro σ _ _ μ q rs hq; exact ⟨s1 μ q rs hq, s2 μ q rs hq⟩

end Alignment.Shadows.MorphismsPairwise.EbToPwsPoisson

/-! ## `MorphismsPairwise.hasFDerivAtPwImage`

Blind text: "π^PW has derivative `pwD N q u` at every state whose θ is a point where ψ' and ψ''
are the derivatives of ψ and ψ'."
AMBIGUITY: the text does not mention finiteness of σ; DataTypes (e) fixes the convention that
node species form a finite type, so `[Fintype σ]` is assumed (the normed structure on `EB σ`). -/
namespace Alignment.Shadows.MorphismsPairwise.HasFDerivAtPwImage
open Alignment.Shadows.MorphismsPairwise

@[sa_reference "MorphismsPairwise.hasFDerivAtPwImage"]
def T : Prop :=
  ∀ {σ : Type} [Fintype σ] (N : CNet) (q : ℝ) (u : EB σ),
    HasDerivAt N.ψ (N.ψ' u.1) u.1 → HasDerivAt N.ψ' (N.ψ'' u.1) u.1 →
      HasFDerivAt (pwImage N q) (pwD N q u) u

/-- S1: the whole (atomic) statement. -/
@[sa_shadow "MorphismsPairwise.hasFDerivAtPwImage" 1]
def S1 : Prop :=
  ∀ {σ : Type} [Fintype σ] (N : CNet) (q : ℝ) (u : EB σ),
    HasDerivAt N.ψ (N.ψ' u.1) u.1 → HasDerivAt N.ψ' (N.ψ'' u.1) u.1 →
      HasFDerivAt (pwImage N q) (pwD N q u) u

@[sa_ref_forward "MorphismsPairwise.hasFDerivAtPwImage" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MorphismsPairwise.hasFDerivAtPwImage"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MorphismsPairwise.HasFDerivAtPwImage

/-! ## `MorphismsPairwise.pwsEbField`

Blind text: "**Per-reaction identity behind M6.** At a state with `ψ(θ) ≠ 0`, `ψ'(θ) ≠ 0` and
`qξ ≠ 0`, the derivative of π^PW carries the EB field of each T_EB reaction `r` to the
PGF-closure field of `r` at the image point."

"The derivative of π^PW" is `pwD N q u` (DataTypes (e): "the explicit linear map intended as its
derivative at `u`"); the text states no derivative hypothesis, so none is assumed.
AMBIGUITY: reading it as `fderiv ℝ (pwImage N q) u` would need `HasDerivAt` hypotheses the text
does not state; not adopted. Split along "each T_EB reaction": contacts, exits, transitions
(progressions and removals). -/
namespace Alignment.Shadows.MorphismsPairwise.PwsEbField
open Alignment.Shadows.MorphismsPairwise

@[sa_reference "MorphismsPairwise.pwsEbField"]
def T : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (r : Rxn σ) (u : EB σ),
    N.ψ u.1 ≠ 0 → N.ψ' u.1 ≠ 0 → q * u.2.1 ≠ 0 →
      pwD N q u (ebField N q r u) = pgfField N r (pwImage N q u)

/-- S1: contacts `s + J → X + J`. -/
@[sa_shadow "MorphismsPairwise.pwsEbField" 1]
def S1 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (J X : σ) (τ : ℝ) (u : EB σ),
    N.ψ u.1 ≠ 0 → N.ψ' u.1 ≠ 0 → q * u.2.1 ≠ 0 →
      pwD N q u (ebField N q (Rxn.contact J X τ) u) = pgfField N (Rxn.contact J X τ) (pwImage N q u)

/-- S2: exits `s → Y`. -/
@[sa_shadow "MorphismsPairwise.pwsEbField" 2]
def S2 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (Y : σ) (ν : ℝ) (u : EB σ),
    N.ψ u.1 ≠ 0 → N.ψ' u.1 ≠ 0 → q * u.2.1 ≠ 0 →
      pwD N q u (ebField N q (Rxn.exit Y ν) u) = pgfField N (Rxn.exit Y ν) (pwImage N q u)

/-- S3: progressions `X → Y` and removals `X → ∅`. -/
@[sa_shadow "MorphismsPairwise.pwsEbField" 3]
def S3 : Prop :=
  ∀ {σ : Type} [DecidableEq σ] (N : CNet) (q : ℝ) (X : σ) (Y : Option σ) (a : ℝ) (u : EB σ),
    N.ψ u.1 ≠ 0 → N.ψ' u.1 ≠ 0 → q * u.2.1 ≠ 0 →
      pwD N q u (ebField N q (Rxn.trans X Y a) u) = pgfField N (Rxn.trans X Y a) (pwImage N q u)

@[sa_ref_forward "MorphismsPairwise.pwsEbField" 1]
theorem ref_fwd1 : T → S1 := by
  intro t σ _ N q J X τ u h1 h2 h3; exact t N q _ u h1 h2 h3

@[sa_ref_forward "MorphismsPairwise.pwsEbField" 2]
theorem ref_fwd2 : T → S2 := by
  intro t σ _ N q Y ν u h1 h2 h3; exact t N q _ u h1 h2 h3

@[sa_ref_forward "MorphismsPairwise.pwsEbField" 3]
theorem ref_fwd3 : T → S3 := by
  intro t σ _ N q X Y a u h1 h2 h3; exact t N q _ u h1 h2 h3

@[sa_complete "MorphismsPairwise.pwsEbField"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := by
  intro σ _ N q r u h1 h2 h3
  cases r with
  | contact J X τ => exact s1 N q J X τ u h1 h2 h3
  | exit Y ν => exact s2 N q Y ν u h1 h2 h3
  | trans X Y a => exact s3 N q X Y a u h1 h2 h3

end Alignment.Shadows.MorphismsPairwise.PwsEbField

/-! ## `MorphismsPairwise.pwsDomainPoisson`

Blind text: "The domain of M6 on a Poisson(μ) network with `μ ≠ 0` is `{ξ ≠ 0}`: ψ > 0 and
ψ' ≠ 0 everywhere."

"The domain of M6" is `pwsDomain N Θ` (DataTypes); the M6 domain of §L.3 has no θ restriction
and "everywhere" confirms none applies, so Θ = `Set.univ`. The context "with `μ ≠ 0`" scopes the
whole sentence, including the justification after the colon. Split along the conjunction: the
set equality (S1), ψ > 0 everywhere (S2), ψ' ≠ 0 everywhere (S3), each for μ ≠ 0.
AMBIGUITY: a restricted domain `pwsDomain N Θ` for other Θ is not what the text describes
("everywhere"); not required. -/
namespace Alignment.Shadows.MorphismsPairwise.PwsDomainPoisson
open Alignment.Shadows.MorphismsPairwise

@[sa_reference "MorphismsPairwise.pwsDomainPoisson"]
def T : Prop :=
  ∀ μ : ℝ, μ ≠ 0 →
    (∀ {σ : Type}, pwsDomain (σ := σ) (CNet.poisson μ) Set.univ = {u : EB σ | u.2.1 ≠ 0}) ∧
      (∀ x : ℝ, 0 < (CNet.poisson μ).ψ x) ∧ (∀ x : ℝ, (CNet.poisson μ).ψ' x ≠ 0)

/-- S1: for μ ≠ 0 the M6 domain on Poisson(μ) is `{ξ ≠ 0}`. -/
@[sa_shadow "MorphismsPairwise.pwsDomainPoisson" 1]
def S1 : Prop :=
  ∀ μ : ℝ, μ ≠ 0 →
    ∀ {σ : Type}, pwsDomain (σ := σ) (CNet.poisson μ) Set.univ = {u : EB σ | u.2.1 ≠ 0}

/-- S2: for μ ≠ 0, Poisson's ψ is positive everywhere. -/
@[sa_shadow "MorphismsPairwise.pwsDomainPoisson" 2]
def S2 : Prop := ∀ μ : ℝ, μ ≠ 0 → ∀ x : ℝ, 0 < (CNet.poisson μ).ψ x

/-- S3: for μ ≠ 0, Poisson's ψ' vanishes nowhere. -/
@[sa_shadow "MorphismsPairwise.pwsDomainPoisson" 3]
def S3 : Prop := ∀ μ : ℝ, μ ≠ 0 → ∀ x : ℝ, (CNet.poisson μ).ψ' x ≠ 0

@[sa_ref_forward "MorphismsPairwise.pwsDomainPoisson" 1]
theorem ref_fwd1 : T → S1 := fun t μ hμ => (t μ hμ).1

@[sa_ref_forward "MorphismsPairwise.pwsDomainPoisson" 2]
theorem ref_fwd2 : T → S2 := fun t μ hμ => (t μ hμ).2.1

@[sa_ref_forward "MorphismsPairwise.pwsDomainPoisson" 3]
theorem ref_fwd3 : T → S3 := fun t μ hμ => (t μ hμ).2.2

@[sa_complete "MorphismsPairwise.pwsDomainPoisson"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T :=
  fun μ hμ => ⟨s1 μ hμ, s2 μ hμ, s3 μ hμ⟩

end Alignment.Shadows.MorphismsPairwise.PwsDomainPoisson
