module

public import GraphMinor.GM19.Conditional
public import GraphMinor.GM20.Cited
import GraphMinor.GM19.ThinningProved
import GraphMinor.GM19.Section15b

/-!
# The main theorem of Graph Minors XIX

The proofs of the feature, inflation, wheel, and linkage steps supply (4.1).
The topology and thinning proofs then give (2.1), in the form used by XX.
-/

public section
namespace GraphMinor.GM19
universe u w

/-- Graph Minors XIX, (4.1), with its preceding deductions supplied by their proofs. -/
theorem theorem_4_1_main : Theorem41Statement.{u, w} := theorem_4_1_proof

/-- The main theorem of Graph Minors XIX, (2.1), in the form used by XX. -/
theorem gm19_main : GM20.GM19Theorem21Statement.{w} := gm19Theorem21'

end GraphMinor.GM19
