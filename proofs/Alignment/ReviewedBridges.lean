import Alignment.Registry
import Alignment.Example.ExampleChecks
import Alignment.Example.SelfTest
import Alignment.Checks.SemanticsEB
import Alignment.Checks.MorphismsRempala
import Alignment.Checks.MorphismsWellMixed
import Alignment.Checks.MorphismsStoich
import Alignment.Checks.MorphismsPoisson
import Alignment.Checks.MorphismsCompact
import Alignment.Checks.Docs
import Alignment.Checks.SemanticsSolutions
import Alignment.Checks.MorphismsNGM
import Alignment.Checks.MorphismsCommon

/-!
# Reviewed bridges

This is the ONLY module whose `sa_bridge_reviewed` / `sa_bridge_rejected` / `sa_shadow_reviewed`
records count. Changes here need trusted-library-level review: a record asserts that the bridge's
right-hand side is exactly the source text's notion and smuggles no theorem content.

Procedure (independent reviewer, never the checker author):

1. Run `bash scripts/sa_pass.sh`; the report lists every `unreviewed` / `stale` bridge with its
   statement and stable hash.
2. Compare the statement with the cited source text: infinities and degenerate inputs, strict
   versus non-strict inequalities, which variable is which, hidden side conditions.
3. Accept with `sa_bridge_reviewed <decl> "<hash>" "<source: why RHS is the text's notion>"`
   or reject with `sa_bridge_rejected <decl> "<reason>"`.
4. A record whose hash no longer matches the bridge's statement is reported as `stale` and does
   not count: re-review before updating a hash.

Import every `Checks/<Group>` module that declares bridges above this comment.

## Rejected bridges (reasons)

* (none yet)
-/

/-! ## Worked example -/

sa_bridge_reviewed Alignment.Example.AdmissibleType.bridge_inTEB "471546209554097348"
  "NetworkEpi/Syntax/Rxn.lean (module docstring and TNet.inTEB docstring): T_EB = {contact, exit,
  progress, remove} (DESIGN §B.2). The RHS InTEB t is exactly that four-way membership, and the
  proof is a case split on the six TNet constructors with no side condition"


/-! ## NetworkEpiCore bridges (round 1 review) -/

sa_bridge_reviewed Alignment.Shadows.SemanticsEB.RemovalFluxEqZero.bridge_isRemoval "5031884031455682599"
  "Trusted Rxn.isRemoval (NetworkEpi/Semantics/EB.lean:277) is true exactly on `.trans _ none _`. Rxn has only three constructors (contact, exit, trans X (Y : Option σ) a), and trans X none a is documented as X → ∅. So the RHS ∃ X a, r = trans X none a is exactly the text's 'removal X → ∅', with no condition on the rate (a can be any real, including 0 or negative, which matches the Boolean test). The RHS says only what form r has and carries no theorem content."

sa_bridge_reviewed Alignment.Shadows.SemanticsEB.NodeConservation.bridge_isRemoval "5031884031455682599"
  "Same statement and definition as RemovalFluxEqZero.bridge_isRemoval. The text's 'no removal X → ∅' is the negation of this RHS for each r in rs. Exact and faithful, and it carries no theorem content."

sa_bridge_reviewed Alignment.Shadows.SemanticsEB.LiftXiEqZero.bridge_isExit "1226729191463579939"
  "Trusted Rxn.isExit (EB.lean:525) is true exactly on `.exit ..`. The exit Y ν constructor is s → Y at rate ν. The RHS ∃ Y ν, r = Rxn.exit Y ν is exactly the text's 'exit', with no side condition on ν and no theorem content."

sa_bridge_reviewed Alignment.Shadows.SemanticsEB.XiConst.bridge_isExit "1226729191463579939"
  "Same as LiftXiEqZero.bridge_isExit. The text says 'has no exit s → Y', which is this RHS negated for each member of the list. Faithful."

sa_bridge_reviewed Alignment.Shadows.SemanticsEB.EdgeDefectDerivLift.bridge_removalRate "7355096225778200046"
  "Trusted Rxn.removalRate φ (EB.lean:268) is `| .trans X none a => a * φ X | _ => 0`. Shadow RemRate has the same body, token for token: summand a·v_X for a removal (X → ∅, a) and 0 for every other reaction. That is the per-reaction summand of the text's Σ_{(X → ∅, a) ∈ rs} a φ_X. Trusted removalFlux and RemFlux are both List.map-sum, so they count repeated reactions the same way. The bridge is a definitional equation, not a theorem."

sa_bridge_reviewed Alignment.Shadows.SemanticsEB.NodeTotalDerivLift.bridge_removalRate "7355096225778200046"
  "Same as EdgeDefectDerivLift.bridge_removalRate, applied to the pop coordinates (u.2.2.2) for 'the removal flux of pop'. Same definition and same faithfulness."

sa_bridge_reviewed Alignment.Shadows.SemanticsEB.HasDerivWithinAtEdgeDefectLift.bridge_removalRate "7355096225778200046"
  "Same as EdgeDefectDerivLift.bridge_removalRate. The text's Σ_{(X → ∅, a) ∈ rs} a φ_X is RemFlux rs (x t).2.2.1, which is built from RemRate. It matches the trusted removalRate case for case."

sa_bridge_reviewed Alignment.Shadows.SemanticsEB.HasDerivWithinAtNodeTotalLift.bridge_removalRate "7355096225778200046"
  "Same as above. The text's −Σ_{(X → ∅, a) ∈ rs} a pop_X is −RemFlux rs (x t).2.2.2, and the per-reaction summands match the trusted definition exactly."

sa_bridge_reviewed Alignment.Shadows.SemanticsEB.HasDerivAtEdgeDefectLift.bridge_removalRate "7355096225778200046"
  "Same as above: the two-sided version of the edge balance law uses the same removal flux notion. The per-reaction equation is definitional."

sa_bridge_reviewed Alignment.Shadows.SemanticsEB.HasDerivAtNodeTotalLift.bridge_removalRate "7355096225778200046"
  "Same as above: the two-sided version of the node balance law uses the same removal flux notion. The per-reaction equation is definitional."

sa_bridge_reviewed Alignment.Shadows.MorphismsRempala.RempalaQuotient.bridge_rempalaD "13913574289004458743"
  "The LHS is the trusted rempalaD (NetworkEpi/Morphisms/Rempala.lean:63, suscD.prod ebPhi, docstring 'The derivative of rempalaMap μ q at u'). The RHS is Mathlib's fderiv of the trusted rempalaMap, which is the claim text's 'its derivative at every point', and shadow DerivSurj uses exactly this. The bridge is proved unconditionally for every σ, μ, q and u. There is no q ≠ 0 or Fintype side condition, so no restriction is hidden. The proof goes through HasFDerivAt, so fderiv is not the junk value 0. The codomain ℝ × (σ → ℝ) is T2, so the derivative is unique. For finite σ this is the ordinary normed Fréchet derivative. No theorem content is smuggled: the bridge only identifies the derivative, and the surjectivity content stays in the impl rempala_quotient. The helper hasFDerivAt_rempalaMap_any uses Mathlib only and no impl theorem. The bridge is not registered for hasFDerivAtRempalaMap, where it would carry that claim's content. Audit status is unreviewed with reasons [] when NetworkEpi is imported."

sa_bridge_reviewed Alignment.Shadows.MorphismsRempala.RempalaEbField.bridge_rempalaD "13913574289004458743"
  "Same statement and proof as the quotient bridge. The text's 'the derivative of Rempała's map carries the EB field ... to the MA field' is the value of fderiv ℝ (rempalaMap μ q) u, and shadows T and S1 use exactly this. The bridge holds for all μ, q, σ and u, so the claim's μ ≠ 0 hypothesis is not affected. The per-reaction field identity (the claim's content) stays in the impl rempala_ebField. The bridge only asserts that rempalaD is the Fréchet derivative, and the helper proves that from Mathlib without any impl theorem."

sa_bridge_reviewed Alignment.Shadows.MorphismsRempala.RempalaDSurjective.bridge_rempalaD "13913574289004458743"
  "Same statement and proof as the quotient bridge. The text's 'the derivative of Rempała's map is surjective at every point' refers to fderiv ℝ (rempalaMap μ q) u, which is exactly what shadows T and S1 use. The bridge is unconditional in q, so it does not assume q ≠ 0. Surjectivity (the claim's content) stays in the impl rempalaD_surjective. Degenerate inputs are handled: at q = 0 and μ = 0 the bridge still holds, and the claim restricts to q ≠ 0 anyway. For infinite σ, EB σ carries the product topology and the TVS fderiv applies. For finite σ it agrees with the normed Fréchet derivative."

sa_bridge_reviewed Alignment.Shadows.MorphismsWellMixed.WellmixedUnitQuotient.bridge_wmD "2121590584485827450"
  "The LHS is the trusted def NEP.wmD (NetworkEpi/Morphisms/WellMixed.lean), whose docstring is 'The derivative of wmMap κ q at u'. It is applied to the distinct bound variables κ q u. The RHS is Mathlib's Fréchet derivative fderiv ℝ (wmMap κ q) u. That is exactly the Dπ(u) of DESIGN §D.3, where objects are finite-dimensional real normed spaces and 'a surjective submersion is a quotient', so 'submersion' means Dπ(u) is surjective. [Fintype σ] makes WM σ finite-dimensional, which matches §D.3. The fderiv depends only on the topology, so the sup-norm product convention does not matter. The equation holds for all κ and q, including q = 0 and κ = 0, so no degenerate case is excluded or assumed. It identifies which linear map is 'the derivative' and carries none of the claim's content: surjectivity of the map and of its derivative still comes from the impl (fwd3 only rewrites S3 with the bridge). Proof: wmD_eq_fderiv_aux uses only the NEP constants WM, MA, wmMap, wmD and wmD's auxiliary proofs. It uses no impl theorem, in particular not NEP.hasFDerivAt_wmMap. Axioms are propext, Classical.choice and Quot.sound. The audit status is 'unreviewed' with no shape problems when NetworkEpi is loaded."

sa_bridge_reviewed Alignment.Shadows.MorphismsWellMixed.WmFieldEq.bridge_wmD "2121590584485827450"
  "The statement and proof are the same as the WellmixedUnitQuotient bridge (hash 2121590584485827450). Here it is registered for wmFieldEq, whose text is 'The derivative of `wmMap` carries the well-mixed EB field ... to the mass-action field of c_κ r'. 'The derivative of wmMap' at u is the §D.3 Dπ(u), which is Mathlib's fderiv ℝ (wmMap κ q) u on the finite-dimensional space WM σ (Fintype σ). The trusted wmD has the docstring 'The derivative of wmMap κ q at u'. The RHS is only the derivative operator: it contains neither wmField nor maField and says nothing about the per-reaction field identity. That identity comes entirely from the impl wm_field_eq, and fwd1-3 only rewrite with the bridge. The equation holds for all κ, q and u, with no side conditions. The helper proof depends on no impl theorem, only on WM, MA, wmMap and wmD. Axioms are standard. The audit status is 'unreviewed' with no problems when NetworkEpi is loaded."

sa_bridge_reviewed Alignment.Shadows.MorphismsStoich.MaEqStoich.bridge_isSemiconj_linear "8957736475694993804"
  "LHS is the trusted predicate NEP.IsSemiconj A B π, whose body is Differentiable ℝ π ∧ ∀ u, fderiv ℝ π u (A.F u) = B.F (π u) (DESIGN §D.3, Dπ(u)·F(u) = G(π u)). It is applied to the distinct bound variables A, B, π. The RHS ∀ u, π (A.F u) = B.F (π u) mentions bound variables. It is exactly the vector-field correspondence that the claim text means by 'sSys extends / agrees with the library's mass-action semantics' and that blind shadow S7 states: sSys-field at coords u = coords of maSys-field at u, with the orientation fixed by the alignment helper fieldToOpt. The only premise is ⇑L = π for an arbitrary continuous linear map L. Under it the equivalence is a generic calculus fact: a CLM is differentiable and fderiv L u = L. It holds for all DynSys A and B, including degenerate or trivial state spaces. It says nothing specific to maSys, sSys, NRxn or maToS, so no claim content is smuggled. The RHS has no conjunct structure that could hide theorem content. Nothing is lost when the differentiability conjunct is dropped, because it is discharged by linearity, not assumed. The proof uses only subst, L.fderiv and L.differentiable from Mathlib, and no implementation theorem. The checkers instantiate L = maToSL through the helper coe_maToSL (funext + Option cases + rfl), which does not use NEP.maToSL_apply. maToSL = ContinuousLinearMap.pi maToSComp does reduce definitionally to maToS = fun i => i.elim u.1 u.2. The audit confirms the statement and hash with status unreviewed and no rule violations."

sa_bridge_reviewed Alignment.Shadows.MorphismsPoisson.PoissonEbField.bridge_poissonDL "13564941002560147538"
  "The claim text says 'the derivative of poissonMap'. The trusted poissonDL μ q u is documented as 'The derivative of poissonMap μ q at u', and its body is ContinuousLinearMap.pi of the components suscD (CNet.poisson μ) q u (that is, q(v_ξ e^{μ(θ−1)} + ξ μ e^{μ(θ−1)} v_θ)), proj∘ebPhi and proj∘ebPop. The RHS is Mathlib's Fréchet derivative fderiv ℝ (poissonMap μ q) u, which is exactly the text's notion. Degenerate inputs: poissonMap is smooth everywhere, for every μ and q including μ = 0 and q ≤ 0, so fderiv's junk value 0 for non-differentiable maps never applies and the identity holds without side conditions. Domain: [Fintype σ] is needed for EB σ and DSp σ → ℝ to be normed spaces, so fderiv makes sense. The shadow S1 carries the same restriction, so the bridge covers every instance the shadow uses. No smuggling: the equality only identifies the definition with its textual meaning and carries none of the per-reaction field identity (poisson_ebField). The proof, hasFDerivAt_poissonMap_aux then HasFDerivAt.fderiv, uses Mathlib calculus plus unfolding/rfl-simp lemmas of trusted defs. The audit (with NetworkEpi imported) reports the bridge as structurally valid and 'unreviewed', with no impl dependency. The hash was confirmed via #sa_audit."

sa_bridge_reviewed Alignment.Shadows.MorphismsCompact.CompactConj.bridge_emb "8726521545807369653"
  "The trusted NEP.compactEmb (NetworkEpi/Morphisms/Compact.lean:60) is (w.1, 1, sirVec (w.1 - N.phiS q w.1 1 - γ(1-w.1)/τ) (γ(1-w.1)/τ), sirVec (1 - N.susc q w.1 1 - w.2) w.2). It uses CNet.phiS q θ ξ = q*ξ*ψ'(θ)/ψ'(1) and CNet.susc q θ ξ = q*ξ*ψ(θ) (Semantics/EB.lean:65-68, which are DESIGN §0's φ_S and S). The RHS emb is the blind transcription of the claim text's embedding (θ,R) ↦ (θ, 1, φ_I = θ − qψ'(θ)/ψ'(1) − φ_R, φ_R = γ(1−θ)/τ, 1 − qψ(θ) − R, R). The shadow helper sv is the same function as sirVec (a at I, b at R). The coordinate order (θ, ξ, φ, pop) matches DataTypes/EB. The only difference is the factor ξ = 1 (q*1*… vs q*…). Degenerate cases (τ = 0, ψ'(1) = 0) use the same Lean division convention on both sides, and the claim assumes τ ≠ 0 anyway. The RHS mentions bound variables and holds no theorem content. The proof is simp only [defs, mul_one]; rfl, and it uses no impl theorem. The audit reports the bridge as valid and unreviewed, with no reasons."

sa_bridge_reviewed Alignment.Shadows.MorphismsCompact.CompactConj.bridge_W "13424280360243047731"
  "The trusted NEP.compactW (Compact.lean:70) is {u | ξ = 1 ∧ τφ_R + γθ = γ ∧ θ = phiS q θ ξ + φ_I + φ_R ∧ susc q θ ξ + pop_I + pop_R = 1}. The RHS Wp is the text's W' = W ∩ {ξ = 1, θ = φ_S + φ_I + φ_R, S + pop_I + pop_R = 1}, with W = {τφ_R + γθ = γ} and φ_S = qξψ'(θ)/ψ'(1), S = qξψ(θ) written in primitives. That is the correct reading of DESIGN §0, where φ_S and S depend on the state's ξ, not on a fixed 1. Both sides have exactly the same four conditions: phiS and susc unfold to the same expressions, and only the first two conjuncts are swapped. No conditions are added or dropped, and no domain restriction is hidden. The RHS is a set built from the bound variables, with no closed or theorem content. The proof is ext / simp only unfolding / conjunct reorder, and it uses no impl theorem. The audit reports it as valid and unreviewed."

sa_bridge_reviewed Alignment.Shadows.MorphismsCompact.CompactEmbSemiconj.bridge_emb "8726521545807369653"
  "This has the same statement (same hash) as CompactConj.bridge_emb, registered for compactEmbSemiconj. In the claim text, 'the embedding' is the M9 embedding (θ,R) ↦ (θ, 1, θ − qψ'(θ)/ψ'(1) − γ(1−θ)/τ, γ(1−θ)/τ, 1 − qψ(θ) − R, R). The blind emb transcribes it, and the trusted compactEmb differs only by ξ = 1 inside phiS and susc. It has the same proof (simp only [defs, mul_one]; rfl), uses no impl theorem, and smuggles no content. The audit reports it as valid and unreviewed."

/-! ## NetworkEpiCore bridges (round 2 review, after remediation)

Re-confirmed without change (existing records above, hashes unchanged): SemanticsEB.XiConst.bridge_isExit,
MorphismsPoisson.PoissonEbField.bridge_poissonDL, MorphismsCompact.CompactConj.bridge_emb,
MorphismsCompact.CompactConj.bridge_W. -/

sa_bridge_reviewed Alignment.Shadows.Docs.EdgeDefectWithRemovals.bridge_isRemoval "5031884031455682599"
  "The LHS is the trusted Boolean test NEP.Rxn.isRemoval (NetworkEpi/Semantics/EB.lean:283): true on `.trans _ none _`, false otherwise. The RHS ∃ X a, r = Rxn.trans X none a is exactly the text's 'removal X → ∅' (Rxn docstring: trans X none a is X → ∅ at rate a); contact, exit and trans X (some Y) a are not removals. No rate condition, no species excluded; syntactic characterisation carrying none of the content of removalFlux_eq_zero, removalFlux_nonneg or the balance law. Proof isRemoval_iff_aux (Checks/Docs.lean:61) is cases+simp with standard axioms only. Same statement and hash as the reviewed SemanticsEB.RemovalFluxEqZero.bridge_isRemoval. In fwd5 it only converts S5's 'no trans X none a ∈ rs' into ∀ r ∈ rs, r.isRemoval = false."

sa_bridge_reviewed Alignment.Shadows.SemanticsSolutions.ConservationLocal.bridge_isRemoval "5031884031455682599"
  "Trusted Rxn.isRemoval is true exactly on `.trans _ none _`; Rxn σ has three constructors and trans X none a is the documented T_EB shape X → ∅ (§B.2 :remove). So the RHS ∃ X a, r = trans X none a is exactly the claim's 'removal X → ∅'. Any rate (including 0) counts, matching the syntactic reading of 'removal-free' in the text and shadow. Definitional, no theorem content, proved by constructor case analysis (isRemoval_iff_aux) without impl theorems. Audit hash 5031884031455682599, empty reasons; identical to the reviewed SemanticsEB bridges."

sa_bridge_reviewed Alignment.Shadows.SemanticsSolutions.ConservationLocalPoisson.bridge_isRemoval "5031884031455682599"
  "Same statement and hash as ConservationLocal.bridge_isRemoval. The text's 'removal-free T_EB reaction list rs' is the negation of the RHS for each r ∈ rs, as the Poisson shadow S1/T states (∀ r ∈ rs, ∀ X a, r ≠ Rxn.trans X none a). Definitional equivalence (three-constructor case split), no domain or convention mismatch, no impl dependency; audit reasons empty."

sa_bridge_reviewed Alignment.Shadows.MorphismsCompact.CompactSolution.bridge_W "13424280360243047731"
  "Same statement and hash as CompactConj.bridge_W (confirmed via #sa_audit with NetworkEpi imported: unreviewed, reasons empty). The compactSolution text's 'stays in W'' is the M9 set W' = W ∩ {ξ = 1, θ = φ_S + φ_I + φ_R, S + pop_I + pop_R = 1} (DESIGN §L.2 item 2); Wp is its blind primitive transcription and trusted compactW matches it up to swapping two conjuncts. Universally quantified over q, so the instantiation q = 1 − ρ is covered. No side conditions; proof is ext / simp only unfolding / conjunct swap with no impl theorem; carries none of the invariance or solution content."

sa_bridge_reviewed Alignment.Shadows.MorphismsCompact.CompactSolutionPoisson.bridge_W "13424280360243047731"
  "Same statement and hash as CompactConj.bridge_W (confirmed via #sa_audit: unreviewed, reasons empty). The §M.4 text's 'it stays in W′' is the same M9 W' (DESIGN §L.2 item 2); Wp transcribes it exactly with φ_S = qξψ'(θ)/ψ'(1), S = qξψ(θ). Holds for every N, q, τ, γ, covering S5's CNet.poisson μ instance with arbitrary q; no μ ≠ 0 or τ ≠ 0 condition needed for the set identity. Same proof as the others, no impl dependency; the RHS is a set in bound variables with none of the existence or solution content."

/-! ## Self-test records (deliberately broken; `--self-test` checks that they do not count) -/

-- stale: the hash does not match the bridge's statement
sa_bridge_reviewed Alignment.Example.SelfTest.StaleBridge.bridge "0"
  "SELFTEST: stale review record"
-- valid hash, but the bridge's proof depends on an implementation theorem (laundering)
sa_bridge_reviewed Alignment.Example.SelfTest.LaunderingBridge.bridge "471546209554097348"
  "SELFTEST: laundering bridge with a matching hash"
-- rejected by the reviewer
sa_bridge_rejected Alignment.Example.SelfTest.RejectedBridge.bridge
  "SELFTEST: rejected bridge"
-- reviewed with a matching hash, but the checker using it belongs to another claim
-- (`SELFTEST.outOfScopeBridge` uses the worked example's bridge above)

/-! ## Self-test shadow reviews (`sa_shadow_reviewed`) -/

-- valid: the mock's text is calculus, so a trusted-free shadow is appropriate
sa_shadow_reviewed Alignment.Example.SelfTest.TrustedFreeReviewed.S1 "17292980193152741638"
  "SELFTEST: the mock text is a statement of real analysis (zero derivative implies constant)"
-- stale: the hash does not match the shadow's content
sa_shadow_reviewed Alignment.Example.SelfTest.TrustedFreeStale.S1 "0"
  "SELFTEST: stale shadow review record"

/-! ## Trusted-free shadow reviews (independent shadow reviewer, 2026-09-28)

Each record below was checked against the claim's registry text (Alignment/claims.yaml) and the
cited source lines. All 22 flagged shadows state facts of linear algebra, finite sums or real
analysis about Mathlib notions only, and each formalises its text faithfully (quantifiers,
hypotheses, strictness, codomain conversions checked). None rejected. -/

sa_shadow_reviewed Alignment.Shadows.MorphismsNGM.SpectralRadiusVecMulVec.S1 "8743359799315730361"
  "NetworkEpi/Morphisms/NGM.lean:23-24 (Mathlib linear algebra, no epidemic notion): 'a rank-one matrix u vT (u /= 0) ... its spectral radius is |v.u|'. vecMulVec u v is (u vT)_ij = u_i v_j, v dotProduct u is v.u, |.| as the nnnorm in ENNReal is Mathlib's spectralRadius codomain; u /= 0 kept; every finite index type. Correct formalisation of the conclusion. NOTE: the 'spectrum inside {0, v.u} containing v.u' clauses of the same sentence are not in this shadow set (they are the separate claims spectrumVecMulVecSubset / memSpectrumVecMulVec, reviewed below)"
sa_shadow_reviewed Alignment.Shadows.MorphismsNGM.R0SingleEntry.S1 "15818057461608100182"
  "NGM.lean:25-27 and DESIGN §M.2 quoted in the claim: 'K = F V^-1 = e_E (wT V^-1)' for F = e_E wT. F = vecMulVec (Pi.single E 1) w is e_E wT; w vecMul V^-1 is wT V^-1; Mathlib inverse, no hypothesis on V (text states none). Pure matrix algebra, correct"
sa_shadow_reviewed Alignment.Shadows.MorphismsNGM.R0SingleEntry.S2 "15974062422408948211"
  "NGM.lean:25-27 / §M.2: 'has rank at most one'. Matrix.rank (F V^-1) <= 1 under F = e_E wT. Pure linear algebra, correct"
sa_shadow_reviewed Alignment.Shadows.MorphismsNGM.R0SingleEntry.S3 "2415423140744252662"
  "DESIGN §M.2 quoted in the claim text: '(rank one unless wT V^-1 = 0)'. wT V^-1 /= 0 -> rank (F V^-1) = 1 is exactly that clause (the converse is implied by S1). True linear algebra (e_E xT with x /= 0 has rank 1); correct reading of the binding amendment"
sa_shadow_reviewed Alignment.Shadows.MorphismsNGM.R0SingleEntry.S4 "7939097140091107075"
  "NGM.lean:25-27 / §M.2: 'R0 = rho(K) = |(wT V^-1)_E|'. spectralRadius R (F V^-1) = nnnorm ((w vecMul V^-1) E) with R0 = rho(K) by the module's stated convention (NGM.lean:18-19). Pure linear algebra, correct"
sa_shadow_reviewed Alignment.Shadows.MorphismsNGM.SpectralRadiusFinTwo.S1 "1037359448265748064"
  "NGM.lean:30-31: 'for a 2x2 matrix [[a, b], [c, d]] with a, d >= 0 and bc >= 0, rho = (a + d + sqrt((a - d)^2 + 4bc))/2'. Hypotheses 0 <= a, 0 <= d, 0 <= b*c exactly; !![a, b; c, d] is the matrix; the closed form is >= 0 under these hypotheses so ENNReal.ofReal loses nothing. Correct"
sa_shadow_reviewed Alignment.Shadows.MorphismsNGM.MemSpectrumIffDet.S1 "1787981358696633178"
  "NGM.lean:55: 'r is in the real spectrum of K iff det(r.1 - K) = 0', direction ->. spectrum R K, r • 1 - K, Matrix.det, every finite index type. Correct"
sa_shadow_reviewed Alignment.Shadows.MorphismsNGM.MemSpectrumIffDet.S2 "232812835920690492"
  "NGM.lean:55: same text, direction <-. Correct"
sa_shadow_reviewed Alignment.Shadows.MorphismsNGM.SpectrumVecMulVecSubset.S1 "4556973231874514112"
  "NGM.lean:60: 'The real spectrum of the rank-one matrix u vT lies in {0, v.u}'. spectrum R (vecMulVec u v) ⊆ {0, v dotProduct u}, no hypothesis on u (text has none; the inclusion holds for u = 0 too). Correct"
sa_shadow_reviewed Alignment.Shadows.MorphismsNGM.MemSpectrumVecMulVec.S1 "10540623330198837175"
  "NGM.lean:85: 'v.u is in the real spectrum of u vT when u /= 0'. v dotProduct u ∈ spectrum R (vecMulVec u v) under u /= 0; the eigenvector parenthesis is justification. Correct"
sa_shadow_reviewed Alignment.Shadows.MorphismsNGM.SpectrumFinTwo.S1 "7820572132108939725"
  "NGM.lean:157-158: 'The real spectrum of a 2x2 matrix with non-negative discriminant D = (a - d)^2 + 4bc: the two roots (a + d ± sqrt D)/2'. Inclusion spectrum ⊆ {(a+d+sqrt D)/2, (a+d-sqrt D)/2} under D >= 0. The characteristic-polynomial parenthesis is a true description of those values ((a+d)^2 - 4(ad-bc) = D), not an extra requirement. Correct"
sa_shadow_reviewed Alignment.Shadows.MorphismsNGM.SpectrumFinTwo.S2 "12557155240545531676"
  "NGM.lean:157-158: same text, reverse inclusion (both roots are real eigenvalues). Correct"
sa_shadow_reviewed Alignment.Shadows.MorphismsNGM.SpectralRadiusFinTwoEqTraceIff.S1 "15705274408880963938"
  "NGM.lean:200-201: 'For real a, d >= 0, bc >= 0: the spectral radius of [[a, b], [c, d]] is the trace a + d iff bc = ad', direction ->. ENNReal.ofReal (a + d) with a + d >= 0 is faithful; same hypotheses. Correct"
sa_shadow_reviewed Alignment.Shadows.MorphismsNGM.SpectralRadiusFinTwoEqTraceIff.S2 "6761357480580018513"
  "NGM.lean:200-201: same text, direction <-. Correct"
sa_shadow_reviewed Alignment.Shadows.SemanticsEB.SumSingle.S1 "15437155665140235158"
  "NetworkEpi/Semantics/EB.lean:379: 'The sum over all species of Pi.single X c is c'. Finset.univ sum over a finite species type of (Pi.single X c : σ -> R) Y = c, real c (species vectors are real). Finite-sum arithmetic, correct"
sa_shadow_reviewed Alignment.Shadows.SemanticsEB.HasDerivWithinAtCompClm.S2 "11746623573925970075"
  "EB.lean:402: 'Chain rule for a continuous linear map applied to a curve, within a set of times'. Reading (b): for L : E ->L[R] F between real normed spaces, HasDerivWithinAt x x' I t -> HasDerivWithinAt (L ∘ x) (L x') I t, every set I and time t. Pure calculus, exactly the text; S1 (reading (a), on EB σ) carries the trusted constant"
sa_shadow_reviewed Alignment.Shadows.SemanticsEB.ConstOfHasDerivWithinAtZero.S1 "6671946783152115107"
  "EB.lean:620-621: 'A real function whose derivative within a convex set I vanishes at every point of I is constant on I: g t = g t0 for all t, t0 ∈ I'. g : R -> R, Convex R I, ∀ t ∈ I, HasDerivWithinAt g 0 I t, conclusion verbatim. Real analysis, correct"
sa_shadow_reviewed Alignment.Shadows.SemanticsEB.ConstOfHasDerivAtZero.S1 "3890405149653438740"
  "EB.lean:631: 'A real function with derivative 0 everywhere is constant'. g : R -> R, ∀ t, HasDerivAt g 0 t -> ∀ t t0, g t = g t0. Real analysis, correct"
sa_shadow_reviewed Alignment.Shadows.MorphismsCommon.ClmListSum.S1 "12041906614459084831"
  "NetworkEpi/Morphisms/Common.lean:44: 'A continuous linear map commutes with the sum of a mapped list'. L ((l.map f).sum) = (l.map (L ∘ f)).sum for L : E ->L[R] F between real normed spaces, any list over any index type. Linear algebra, correct (real scalars are the library's setting)"
sa_shadow_reviewed Alignment.Shadows.MorphismsCommon.ClmListSumEq.S1 "9158484076963380945"
  "Common.lean:52-54: 'If a continuous linear map L carries each per-reaction source term f r to the per-reaction target term g r, it carries the sum over the reaction list to the sum'. (∀ r ∈ rs, L (f r) = g r) -> L ((rs.map f).sum) = (rs.map g).sum; 'each' read as each list member (the stronger, list-local hypothesis), index type arbitrary. Linear algebra, correct"
sa_shadow_reviewed Alignment.Shadows.SemanticsSolutions.ContDiffAtPiSingle.S1 "5224569196807938582"
  "NetworkEpi/Semantics/Solutions.lean:35: 'Pi.single Y applied to a C^n function is C^n (a fun_prop rule)'. Pointwise (fun_prop) form: ContDiffAt R n f x -> ContDiffAt R n (fun y => Pi.single Y (f y) : σ -> R) x for n : ℕ∞ (classical C^n incl. C^∞), f : E -> R. Calculus, correct"
sa_shadow_reviewed Alignment.Shadows.SemanticsSolutions.ContDiffAtPiSingle.S2 "18100630947886557903"
  "Solutions.lean:35: same text at Mathlib's analytic level ω = ⊤ : WithTop ℕ∞ (S1 and S2 together cover every n : WithTop ℕ∞). Calculus, correct"
