import Alignment.Registry
import Alignment.Shadows.DynBasic

/-!
# Checkers: group `DynBasic` (trusted module `NetworkEpi.Dyn.Basic`)

Checker author (SA-PASS role 3, non-blind). For each of the eleven `implemented` claims of
`NetworkEpi/Dyn/Basic.lean` that the blind author shadowed, this file holds the `sa_claim`
registration (verbatim registry text, registry `impl` list in registry order), the forward
checkers `sa_impl% → Sᵢ`, and the backward checker `S₁ → … → Sₙ → sa_impl%` or an
`sa_fail_backward` record.

No bridges are declared. The blind shadows state every claim with the trusted notions themselves
(`Semiconj`, `SemiconjOn`, `IsSemiconj`, `IsSemiconjOn`, the instance `dynCategory`,
`DynSys.restrict`, `DynSys.restrictIncl`) or with alignment helpers (`chart`, `subsys`) that are
definitionally equal to the trusted ones (`fun w => p₀ + (w : A.V)` and the structure literal
`⟨↥W, fun w => ⟨A.F (p₀ + w), hW w w.2⟩⟩`). Definitional unfolding is free, so no trusted
definition needs to be identified with a differently phrased notion.

No failures are recorded. `DynBasic.mapSolution` and `DynBasic.mapSolutionOn` use the
exact-statement corollaries (`…_global`, `…_open`) as impl; `DynBasic.semiconjOnMapSolutionWithin`
was re-shadowed for an arbitrary set of times `I`.
-/

open NEP CategoryTheory

/-! ## `DynBasic.semiconjIsSemiconj` -/

namespace Alignment.Shadows.DynBasic.SemiconjIsSemiconj

sa_claim "DynBasic.semiconjIsSemiconj" group "DynBasic" required
  text "A bundled semiconjugacy satisfies `IsSemiconj`."
  impl NEP.Semiconj.isSemiconj

/-- S1 is the implementation's statement. -/
@[sa_forward "DynBasic.semiconjIsSemiconj" 1]
theorem fwd1 (h : sa_impl% "DynBasic.semiconjIsSemiconj") : S1 := by
  intro A B m
  exact h m

@[sa_backward "DynBasic.semiconjIsSemiconj"]
theorem bwd (s1 : S1) : sa_impl% "DynBasic.semiconjIsSemiconj" := by
  intro A B m
  exact s1 m

end Alignment.Shadows.DynBasic.SemiconjIsSemiconj

/-! ## `DynBasic.semiconjOnIsSemiconjOn` -/

namespace Alignment.Shadows.DynBasic.SemiconjOnIsSemiconjOn

sa_claim "DynBasic.semiconjOnIsSemiconjOn" group "DynBasic" required
  text "A bundled local semiconjugacy satisfies `IsSemiconjOn`."
  impl NEP.SemiconjOn.isSemiconjOn

/-- S1 is the implementation's statement. -/
@[sa_forward "DynBasic.semiconjOnIsSemiconjOn" 1]
theorem fwd1 (h : sa_impl% "DynBasic.semiconjOnIsSemiconjOn") : S1 := by
  intro A B U m
  exact h m

@[sa_backward "DynBasic.semiconjOnIsSemiconjOn"]
theorem bwd (s1 : S1) : sa_impl% "DynBasic.semiconjOnIsSemiconjOn" := by
  intro A B U m
  exact s1 m

end Alignment.Shadows.DynBasic.SemiconjOnIsSemiconjOn

/-! ## `DynBasic.homEqSemiconj` -/

namespace Alignment.Shadows.DynBasic.HomEqSemiconj

sa_claim "DynBasic.homEqSemiconj" group "DynBasic" required
  text "The morphisms of `DynSys` are exactly the semiconjugacies."
  impl NEP.hom_eq_semiconj

/-- S1 is the implementation's statement. -/
@[sa_forward "DynBasic.homEqSemiconj" 1]
theorem fwd1 (h : sa_impl% "DynBasic.homEqSemiconj") : S1 := by
  intro A B
  exact h A B

@[sa_backward "DynBasic.homEqSemiconj"]
theorem bwd (s1 : S1) : sa_impl% "DynBasic.homEqSemiconj" := by
  intro A B
  exact s1 A B

end Alignment.Shadows.DynBasic.HomEqSemiconj

/-! ## `DynBasic.idPi` -/

namespace Alignment.Shadows.DynBasic.IdPi

sa_claim "DynBasic.idPi" group "DynBasic" required
  text "In `DynSys` the identity morphism is the identity map."
  impl NEP.id_π

/-- S1 is the implementation's statement. -/
@[sa_forward "DynBasic.idPi" 1]
theorem fwd1 (h : sa_impl% "DynBasic.idPi") : S1 := by
  intro A
  exact h A

@[sa_backward "DynBasic.idPi"]
theorem bwd (s1 : S1) : sa_impl% "DynBasic.idPi" := by
  intro A
  exact s1 A

end Alignment.Shadows.DynBasic.IdPi

/-! ## `DynBasic.compPi` -/

namespace Alignment.Shadows.DynBasic.CompPi

sa_claim "DynBasic.compPi" group "DynBasic" required
  text "In `DynSys` composition of morphisms is composition of the underlying maps."
  impl NEP.comp_π

/-- S1 is the implementation's statement. -/
@[sa_forward "DynBasic.compPi" 1]
theorem fwd1 (h : sa_impl% "DynBasic.compPi") : S1 := by
  intro A B C f g
  exact h f g

@[sa_backward "DynBasic.compPi"]
theorem bwd (s1 : S1) : sa_impl% "DynBasic.compPi" := by
  intro A B C f g
  exact s1 f g

end Alignment.Shadows.DynBasic.CompPi

/-! ## `DynBasic.mapSolution` -/

namespace Alignment.Shadows.DynBasic.MapSolution

sa_claim "DynBasic.mapSolution" group "DynBasic" required
  text "**Semiconjugacies map solutions to solutions.** Design statement (DESIGN_NetworkEpiCore.md §D.3): \"[L] `instance : Category DynSys` and `Semiconj.map_solution` (semiconjugacies map solution curves to solution curves)\". [...] **The category `DynSys`** (DESIGN §D.3: \"[L] `instance : Category DynSys`\"). Objects are `DynSys`, morphisms `A ⟶ B` are `Semiconj A B`, the identity is `id` and composition is composition of maps (`comp_π`, `id_π`)."
  impl NEP.Semiconj.map_solution_global NEP.Semiconj.map_solution_open NEP.hom_eq_semiconj NEP.id_π NEP.comp_π

@[sa_forward "DynBasic.mapSolution" 1]
theorem fwd1 (h : sa_impl% "DynBasic.mapSolution") : S1 := by
  intro A B m x hx
  exact h.1 m x hx

@[sa_forward "DynBasic.mapSolution" 2]
theorem fwd2 (h : sa_impl% "DynBasic.mapSolution") : S2 := by
  intro A B m J hJo hJc x hx
  exact h.2.1 m J hJo hJc x hx

@[sa_forward "DynBasic.mapSolution" 3]
theorem fwd3 (h : sa_impl% "DynBasic.mapSolution") : S3 := by
  intro A B
  exact h.2.2.1 A B

@[sa_forward "DynBasic.mapSolution" 4]
theorem fwd4 (h : sa_impl% "DynBasic.mapSolution") : S4 := by
  intro A
  exact h.2.2.2.1 A

@[sa_forward "DynBasic.mapSolution" 5]
theorem fwd5 (h : sa_impl% "DynBasic.mapSolution") : S5 := by
  intro A B C f g
  exact h.2.2.2.2 f g

@[sa_backward "DynBasic.mapSolution"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) :
    sa_impl% "DynBasic.mapSolution" :=
  ⟨fun m x hx => s1 m x hx, fun m J hJo hJc x hx => s2 m J hJo hJc x hx, fun A B => s3 A B,
    fun A => s4 A, fun f g => s5 f g⟩

end Alignment.Shadows.DynBasic.MapSolution

/-! ## `DynBasic.semiconjMapSolutionWithin` -/

namespace Alignment.Shadows.DynBasic.SemiconjMapSolutionWithin

sa_claim "DynBasic.semiconjMapSolutionWithin" group "DynBasic" required
  text "Semiconjugacies map solutions within a set of times to solutions within it: if `x'(t) = F(x(t))` within `I` (`HasDerivWithinAt`) at every `t ∈ I`, then `(π ∘ x)'(t) = G(π(x(t)))` within `I` at every `t ∈ I`."
  impl NEP.Semiconj.map_solution_within

/-- S1 is the implementation's statement. -/
@[sa_forward "DynBasic.semiconjMapSolutionWithin" 1]
theorem fwd1 (h : sa_impl% "DynBasic.semiconjMapSolutionWithin") : S1 := by
  intro A B m I x hx
  exact h m hx

@[sa_backward "DynBasic.semiconjMapSolutionWithin"]
theorem bwd (s1 : S1) : sa_impl% "DynBasic.semiconjMapSolutionWithin" := by
  intro A B m x I hx
  exact s1 m I x hx

end Alignment.Shadows.DynBasic.SemiconjMapSolutionWithin

/-! ## `DynBasic.mapSolutionOn` -/

namespace Alignment.Shadows.DynBasic.MapSolutionOn

sa_claim "DynBasic.mapSolutionOn" group "DynBasic" required
  text "**Local semiconjugacies map solutions that stay in `U` to solutions.** Design statement (DESIGN_NetworkEpiCore.md §D.3): \"**Local version `SemiconjOn U`.** The identity holds on an open set U, and solutions that stay in U are mapped. This is needed for maps that divide by ψ(θ) or ψ'(θ).\""
  impl NEP.SemiconjOn.map_solution_on_global NEP.SemiconjOn.map_solution_on_open

@[sa_forward "DynBasic.mapSolutionOn" 1]
theorem fwd1 (h : sa_impl% "DynBasic.mapSolutionOn") : S1 := by
  intro A B U m x hU hx
  exact h.1 m x hU hx

@[sa_forward "DynBasic.mapSolutionOn" 2]
theorem fwd2 (h : sa_impl% "DynBasic.mapSolutionOn") : S2 := by
  intro A B U m J hJo hJc x hU hx
  exact h.2 m J hJo hJc x hU hx

@[sa_backward "DynBasic.mapSolutionOn"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "DynBasic.mapSolutionOn" :=
  ⟨fun m x hU hx => s1 m x hU hx, fun m J hJo hJc x hU hx => s2 m J hJo hJc x hU hx⟩

end Alignment.Shadows.DynBasic.MapSolutionOn

/-! ## `DynBasic.semiconjOnMapSolutionWithin` -/

namespace Alignment.Shadows.DynBasic.SemiconjOnMapSolutionWithin

sa_claim "DynBasic.semiconjOnMapSolutionWithin" group "DynBasic" required
  text "**Local semiconjugacies map solutions within a set of times `I` that stay in `U` to solutions within `I`.** Design statement (DESIGN_NetworkEpiCore.md §D.3): \"**Local version `SemiconjOn U`.** The identity holds on an open set U, and solutions that stay in U are mapped. This is needed for maps that divide by ψ(θ) or ψ'(θ).\""
  impl NEP.SemiconjOn.map_solution_within

/-- S1 is the implementation's statement (argument order differs). -/
@[sa_forward "DynBasic.semiconjOnMapSolutionWithin" 1]
theorem fwd1 (h : sa_impl% "DynBasic.semiconjOnMapSolutionWithin") : S1 := by
  intro A B U m I x hU hx
  exact h m hx hU

@[sa_backward "DynBasic.semiconjOnMapSolutionWithin"]
theorem bwd (s1 : S1) : sa_impl% "DynBasic.semiconjOnMapSolutionWithin" := by
  intro A B U m x I hx hU
  exact s1 m I x hU hx

end Alignment.Shadows.DynBasic.SemiconjOnMapSolutionWithin

/-! ## `DynBasic.hasFDerivAtRestrictIncl` -/

namespace Alignment.Shadows.DynBasic.HasFDerivAtRestrictIncl

sa_claim "DynBasic.hasFDerivAtRestrictIncl" group "DynBasic" required
  text "The chart `w ↦ p₀ + w` has derivative the inclusion `W →L[ℝ] V` at every point."
  impl NEP.DynSys.hasFDerivAt_restrictIncl

/-- S1 is the implementation's statement. -/
@[sa_forward "DynBasic.hasFDerivAtRestrictIncl" 1]
theorem fwd1 (h : sa_impl% "DynBasic.hasFDerivAtRestrictIncl") : S1 := by
  intro A p₀ W w
  exact h A p₀ W w

/-- The helper `chart A p₀ W` is `fun w => p₀ + (w : A.V)`, definitionally the trusted
`A.restrictIncl p₀ W`, so the same term proves S2. -/
@[sa_forward "DynBasic.hasFDerivAtRestrictIncl" 2]
theorem fwd2 (h : sa_impl% "DynBasic.hasFDerivAtRestrictIncl") : S2 := by
  intro A p₀ W w
  exact h A p₀ W w

@[sa_backward "DynBasic.hasFDerivAtRestrictIncl"]
theorem bwd (_s1 : S1) (s2 : S2) : sa_impl% "DynBasic.hasFDerivAtRestrictIncl" := by
  intro A p₀ W w
  exact s2 A p₀ W w

end Alignment.Shadows.DynBasic.HasFDerivAtRestrictIncl

/-! ## `DynBasic.invariantIncl` -/

namespace Alignment.Shadows.DynBasic.InvariantIncl

sa_claim "DynBasic.invariantIncl" group "DynBasic" required
  text "**The inclusion of an invariant subsystem is a semiconjugacy (a restriction).** Design statement (DESIGN_NetworkEpiCore.md §D.3): \"The inclusion of an invariant subsystem is a restriction. \"Model A is exact for initial conditions in W\" is a morphism *out of* (W, F|_W).\""
  impl NEP.invariant_incl

/-- S1 is the implementation's statement. -/
@[sa_forward "DynBasic.invariantIncl" 1]
theorem fwd1 (h : sa_impl% "DynBasic.invariantIncl") : S1 := by
  intro A p₀ W hW
  exact h A p₀ W hW

/-- `subsys A p₀ W hW` is the same structure literal as the trusted `A.restrict p₀ W hW`, and
`chart` is `A.restrictIncl p₀ W`, both definitionally, so the same term proves S2. -/
@[sa_forward "DynBasic.invariantIncl" 2]
theorem fwd2 (h : sa_impl% "DynBasic.invariantIncl") : S2 := by
  intro A p₀ W hW
  exact h A p₀ W hW

@[sa_backward "DynBasic.invariantIncl"]
theorem bwd (_s1 : S1) (s2 : S2) : sa_impl% "DynBasic.invariantIncl" := by
  intro A p₀ W hW
  exact s2 A p₀ W hW

end Alignment.Shadows.DynBasic.InvariantIncl
