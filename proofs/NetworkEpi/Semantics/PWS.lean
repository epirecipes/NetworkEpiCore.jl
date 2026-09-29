import NetworkEpi.Semantics.EB

/-!
# L3 (stretch): the S-anchored pairwise field PW^S and the failure of strict gluing (F2)

DESIGN_NetworkEpiCore.md §D.4, row **PW^S_{N,K}**: "Petri/T_EB | [X], [sX], [ss] (+ θ for
`PGFClosure`) | closes only on T_EB | lax: a contact drains [Z s] for *every* Z"; §D.6: "**F2/F2′**
same for PW, PW^S, PB, clustered EB | **no** (lax) | a contact drains [Z s] (or triangle pairs)
for every Z | Lean witness (stretch, L3)".

## Coordinates and field

The state `w : PWS σ` is `([s], [ss], [sZ], [Z])`: the susceptible singles, the susceptible–
susceptible pairs, the pairs `[sZ]` for node species `Z` and the singles `[Z]`. Triples are closed
with a constant closure coefficient `K`: `[A s B] = K [As][sB]/[s]`. The per-reaction field is
the one checked symbolically in the design pass (`check_pwS_general.py` for contacts and
transitions, `check_exit_pws.py` for exits):

```
contact (s + J → X + J, τ):  [s]' −= τ[sJ];  [ss]' −= 2τ[ssJ];  [X]' += τ[sJ]
                              [sZ]' −= τ[Z s J] for every Z;  [sJ]' −= τ[sJ];  [sX]' += τ[s s J]
exit    (s → Y, ν):           [s]' −= ν[s];  [ss]' −= 2ν[ss];  [sZ]' −= ν[sZ] for every Z;
                              [sY]' += ν[ss];  [Y]' += ν[s]
trans   (X → Y | ∅, a):       [sX]' −= a[sX]; [sY]' += a[sX]; [X]' −= a[X]; [Y]' += a[X]
```

For the degree-dependent closure `K_ψ(θ) = ψψ''/ψ'²` of the design's M6, evaluate this field at
`K = K_ψ(θ)`. The terms "for every Z" are what make PW^S lax under gluing (`pwS_glue_not_strict`).
-/

open scoped BigOperators

namespace NEP

/-- S-anchored pairwise coordinates `([s], [ss], [sZ], [Z])` over node species `σ`. -/
abbrev PWS (σ : Type) := ℝ × ℝ × (σ → ℝ) × (σ → ℝ)

variable {σ σA σB : Type}

section Field
variable [DecidableEq σ]

/-- The S-anchored pairwise field of one T_EB reaction with constant triple closure
`[A s B] = K [As][sB]/[s]` (see the module docstring for the quoted equations). -/
noncomputable def pwSField (K : ℝ) : Rxn σ → PWS σ → PWS σ
  | .contact J X τ, (S, SS, SX, _) =>
      (-(τ * SX J), -(2 * τ * (K * SS * SX J / S)),
        Pi.single X (τ * (K * SS * SX J / S)) - (fun Z => τ * (K * SX Z * SX J / S))
          - Pi.single J (τ * SX J),
        Pi.single X (τ * SX J))
  | .exit Y ν, (S, SS, SX, _) =>
      (-(ν * S), -(2 * ν * SS), Pi.single Y (ν * SS) - (fun Z => ν * SX Z), Pi.single Y (ν * S))
  | .trans X none a, (_, _, SX, P) =>
      (0, 0, -Pi.single X (a * SX X), -Pi.single X (a * P X))
  | .trans X (some Y) a, (_, _, SX, P) =>
      (0, 0, Pi.single Y (a * SX X) - Pi.single X (a * SX X),
        Pi.single Y (a * P X) - Pi.single X (a * P X))

/-- The S-anchored pairwise vector field of a reaction list: the sum of the per-reaction fields. -/
noncomputable def pwSLift (K : ℝ) (rs : List (Rxn σ)) (w : PWS σ) : PWS σ :=
  (rs.map fun r => pwSField K r w).sum

/-- The PW^S field is additive in the reaction list (like the EB lift). -/
theorem pwSLift_append (K : ℝ) (rs rs' : List (Rxn σ)) (w : PWS σ) :
    pwSLift K (rs ++ rs') w = pwSLift K rs w + pwSLift K rs' w := by
  simp [pwSLift, List.map_append, List.sum_append]

end Field

section Push
variable {σ' : Type} [Fintype σ] [DecidableEq σ']

/-- Pushforward of PW^S coordinates along a species map: `[s]`, `[ss]` kept; `[sZ]` and `[Z]`
summed over fibres. -/
def pushPW (f : σ → σ') (w : PWS σ) : PWS σ' := (w.1, w.2.1, push f w.2.2.1, push f w.2.2.2)

end Push

/-- Pullback of PW^S coordinates along a species map. -/
def pullPW {σ' : Type} (f : σ → σ') (w : PWS σ') : PWS σ := (w.1, w.2.1, w.2.2.1 ∘ f, w.2.2.2 ∘ f)

/-- The F2 witness: an infection model `A` (`s + I → I + I` at τ = 1) over one node species `I`,
and a vaccination model `B` (`s → V` at ν = 1) over one node species `V`. -/
def f2A : List (Rxn Unit) := [.contact () () 1]

/-- See `f2A`. -/
def f2B : List (Rxn Unit) := [.exit () 1]

/-- The witness state: `[s] = [ss] = 1`, `[sI] = [sV] = 1`, `[I] = [V] = 0`. -/
def f2State : PWS (Unit ⊕ Unit) := (1, 1, fun _ => 1, fun _ => 0)

/-- The `[sV]` component of the PW^S field of the glued witness model at `f2State` is `−1`. -/
theorem f2_glued_sV :
    (pwSLift 1 (f2A.map (Rxn.map Sum.inl) ++ f2B.map (Rxn.map Sum.inr)) f2State).2.2.1
      (Sum.inr ()) = -1 := by
  simp [pwSLift, f2A, f2B, f2State, pwSField, Rxn.map]

/-- The `[sV]` component of the sum of the pushed-forward PW^S fields of `A` and `B` is `0`. -/
theorem f2_sum_sV :
    (pushPW Sum.inl (pwSLift 1 f2A (pullPW Sum.inl f2State)) +
      pushPW Sum.inr (pwSLift 1 f2B (pullPW Sum.inr f2State))).2.2.1 (Sum.inr ()) = 0 := by
  simp [pwSLift, f2A, f2B, f2State, pwSField, pushPW, pullPW, push, Finset.filter_true_of_mem,
    Finset.filter_false_of_mem]

/-- **F2: the S-anchored pairwise field is not strict under gluing.**

Design statement (DESIGN_NetworkEpiCore.md §D.6): "**F2/F2′** same for PW, PW^S, PB, clustered
EB | **no** (lax) | a contact drains [Z s] (or triangle pairs) for every Z | Lean witness
(stretch, L3)"; §D.4: "A PW^S contact drains every [Z s] through the closed triple [Z s J]. When
B's species are glued in, A's contacts must also drain [Z_B s], which A's system does not contain.
So PW^S(glue(A,B)) ≠ glue(PW^S A, PW^S B)."

Lean statement: with closure coefficient `K = 1`, let `A` be `s + I → I + I` at τ = 1 (node
species `I`) and `B` be the exit `s → V` at ν = 1 (node species `V`), glued along the susceptible
species only (`I ↦ inl ()`, `V ↦ inr ()`). At the state `[s] = [ss] = [sI] = [sV] = 1`,
`[I] = [V] = 0`, the PW^S field of the glued model differs from the sum of the pushforwards of the
PW^S fields of `A` and `B` evaluated at the pulled-back states (the analogue of the right-hand side
of `lift_glue`, which holds for EB). The `[sV]` components are −1 and 0: the contact of `A` drains
`[sV]` through the triple `[V s I]` in the glued system only. -/
theorem pwS_glue_not_strict :
    pwSLift 1 (f2A.map (Rxn.map Sum.inl) ++ f2B.map (Rxn.map Sum.inr)) f2State ≠
      pushPW Sum.inl (pwSLift 1 f2A (pullPW Sum.inl f2State)) +
        pushPW Sum.inr (pwSLift 1 f2B (pullPW Sum.inr f2State)) := by
  intro h
  have h' := congrArg (fun w : PWS (Unit ⊕ Unit) => w.2.2.1 (Sum.inr ())) h
  simp only [f2_glued_sV, f2_sum_sV] at h'
  norm_num at h'

/-- The `[sV]` component of the sum of the pushed-forward PW^S fields of `A` and `B` is `0`, for
every closure coefficient `K` (`B` has no contact, and `A` pushes nothing onto `V`). -/
theorem f2_sum_sV_all (K : ℝ) :
    (pushPW Sum.inl (pwSLift K f2A (pullPW Sum.inl f2State)) +
      pushPW Sum.inr (pwSLift K f2B (pullPW Sum.inr f2State))).2.2.1 (Sum.inr ()) = 0 := by
  simp [pwSLift, f2A, f2B, f2State, pwSField, pushPW, pullPW, push, Finset.filter_true_of_mem,
    Finset.filter_false_of_mem]

/-- **F2: the S-anchored pairwise field is not strict under gluing, for every closure
coefficient.**

Design statement (DESIGN_NetworkEpiCore.md §D.6): "**F2/F2′** same for PW, PW^S, PB, clustered
EB | **no** (lax) | a contact drains [Z s] (or triangle pairs) for every Z | Lean witness
(stretch, L3)"; §D.4: "A PW^S contact drains every [Z s] through the closed triple [Z s J]. When
B's species are glued in, A's contacts must also drain [Z_B s], which A's system does not contain.
So PW^S(glue(A,B)) ≠ glue(PW^S A, PW^S B)."

Lean statement: for every closure coefficient `K`, the gluing law of `lift_glue` fails for the
PW^S field: it is not the case that for all finite species types `σA`, `σB` (with decidable
equality), every species type `σ` with decidable equality, every cospan `f : σA → σ ← σB : g`,
all T_EB lists `A`, `B` and every state `w`, the PW^S field of the glued model
`A.map f ++ B.map g` at `w` equals `pushPW f (PW^S_A (pullPW f w)) + pushPW g (PW^S_B (pullPW g w))`.
(Witness: the F2 models at `f2State`; the `[sI]` components are −2 and −1, because in the glued
model the vaccination exit also drains `[sI]`.) Only the failure of the strict law is formalised,
not the lax comparison map. -/
theorem pwS_glue_not_strict_all (K : ℝ) :
    ¬ ∀ {σA σB σ : Type} [Fintype σA] [DecidableEq σA] [Fintype σB] [DecidableEq σB]
        [DecidableEq σ] (f : σA → σ) (g : σB → σ) (A : List (Rxn σA)) (B : List (Rxn σB))
        (w : PWS σ),
        pwSLift K (A.map (Rxn.map f) ++ B.map (Rxn.map g)) w =
          pushPW f (pwSLift K A (pullPW f w)) + pushPW g (pwSLift K B (pullPW g w)) := by
  intro h
  have h' := congrArg (fun w : PWS (Unit ⊕ Unit) => w.2.2.1 (Sum.inl ()))
    (h Sum.inl Sum.inr f2A f2B f2State)
  simp [pwSLift, f2A, f2B, f2State, pwSField, pushPW, pullPW, push, Rxn.map,
    Finset.filter_true_of_mem, Finset.filter_false_of_mem] at h'

/-- **F2: the S-anchored pairwise field is not strict under gluing: a witness gluing, for every
closure coefficient.**

Design statement (DESIGN_NetworkEpiCore.md §D.6): "**F2/F2′** same for PW, PW^S, PB, clustered
EB | **no** (lax) | a contact drains [Z s] (or triangle pairs) for every Z | Lean witness
(stretch, L3)"; §D.4: "A PW^S contact drains every [Z s] through the closed triple [Z s J]. When
B's species are glued in, A's contacts must also drain [Z_B s], which A's system does not contain.
So PW^S(glue(A,B)) ≠ glue(PW^S A, PW^S B)."

Lean statement: for every closure coefficient `K` there are finite species types `σA`, `σB` (with
decidable equality), a species type `σ` with decidable equality, a gluing cospan
`f : σA → σ ← σB : g` whose legs are injective and jointly surjective (a pushout on the identified
species), and T_EB lists `A`, `B`, such that the PW^S field `w ↦ PW^S(A.map f ++ B.map g)(w)` of
the glued model differs from
`w ↦ pushPW f (PW^S_A (pullPW f w)) + pushPW g (PW^S_B (pullPW g w))`. (Witness: the F2 models
`f2A`, `f2B` along `Sum.inl`, `Sum.inr`; at `f2State` the `[sI]` components differ.) Only the
failure of strictness is formalised, not the lax comparison map. -/
theorem pwS_glue_not_strict_witness (K : ℝ) :
    ∃ (σA σB σ : Type) (_ : Fintype σA) (_ : DecidableEq σA) (_ : Fintype σB)
      (_ : DecidableEq σB) (_ : DecidableEq σ) (f : σA → σ) (g : σB → σ) (A : List (Rxn σA))
      (B : List (Rxn σB)),
      (Function.Injective f ∧ Function.Injective g ∧
        ∀ y : σ, (∃ a, f a = y) ∨ (∃ b, g b = y)) ∧
      (fun w : PWS σ => pwSLift K (A.map (Rxn.map f) ++ B.map (Rxn.map g)) w) ≠
        (fun w : PWS σ => pushPW f (pwSLift K A (pullPW f w)) +
          pushPW g (pwSLift K B (pullPW g w))) := by
  refine ⟨Unit, Unit, Unit ⊕ Unit, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, Sum.inl, Sum.inr, f2A, f2B,
    ⟨Sum.inl_injective, Sum.inr_injective, fun y => ?_⟩, fun h => ?_⟩
  · rcases y with a | b
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr ⟨b, rfl⟩
  · have h' := congrArg (fun w : PWS (Unit ⊕ Unit) => w.2.2.1 (Sum.inl ())) (congrFun h f2State)
    simp [pwSLift, f2A, f2B, f2State, pwSField, pushPW, pullPW, push, Rxn.map,
      Finset.filter_true_of_mem, Finset.filter_false_of_mem] at h'

end NEP
