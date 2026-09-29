import Alignment.Registry
-- Worked example and self-test mocks (ids EXAMPLE.* / SELFTEST.*, excluded from normal reports)
import Alignment.Example.ExampleShadows
import Alignment.Example.ExampleChecks
import Alignment.Example.SelfTest
-- Groups: add `import Alignment.Shadows.<Group>` and `import Alignment.Checks.<Group>` here
-- (one group per trusted module, e.g. `Semantics.EB` → group `SemanticsEB`)
import Alignment.Shadows.DynBasic
import Alignment.Checks.DynBasic
import Alignment.Shadows.DynProducts
import Alignment.Checks.DynProducts
import Alignment.Shadows.SyntaxRxn
import Alignment.Checks.SyntaxRxn
import Alignment.Shadows.MorphismsStoich
import Alignment.Checks.MorphismsStoich
import Alignment.Shadows.Docs
import Alignment.Checks.Docs
import Alignment.Shadows.ClosurePT
import Alignment.Checks.ClosurePT
import Alignment.Shadows.MorphismsNGM
import Alignment.Checks.MorphismsNGM
import Alignment.Shadows.SemanticsEB
import Alignment.Checks.SemanticsEB
import Alignment.Shadows.MorphismsPairwise
import Alignment.Checks.MorphismsPairwise
import Alignment.Shadows.MorphismsRempala
import Alignment.Checks.MorphismsRempala
import Alignment.Shadows.MorphismsPoisson
import Alignment.Checks.MorphismsPoisson
import Alignment.Shadows.MorphismsCommon
import Alignment.Checks.MorphismsCommon
import Alignment.Shadows.MorphismsCompact
import Alignment.Checks.MorphismsCompact
import Alignment.Shadows.MorphismsWellMixed
import Alignment.Checks.MorphismsWellMixed
import Alignment.Shadows.SemanticsMA
import Alignment.Checks.SemanticsMA
import Alignment.Shadows.SemanticsPoissonSIR
import Alignment.Checks.SemanticsPoissonSIR
import Alignment.Shadows.SemanticsPWS
import Alignment.Checks.SemanticsPWS
import Alignment.Shadows.SemanticsSolutions
import Alignment.Checks.SemanticsSolutions
-- Review records (must come last: it imports the modules that declare bridges)
import Alignment.ReviewedBridges
