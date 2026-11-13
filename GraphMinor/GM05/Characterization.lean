module

public import GraphMinor.GM05.Statements
import GraphMinor.GM05.ErdosPosaPlanar
import GraphMinor.GM05.ErdosPosaNonplanar

/-!
# Combining the two directions of the Erdős–Pósa characterization

Graph Minors V, (8.2), follows from (8.8) and (8.14), exactly as stated at
the end of Section 8, page 113. Both directions are proved.
-/

public section

namespace GraphMinor.GM05

open Graph

universe u v u' v'

/-- Graph Minors V, (8.2), page 110:
"A graph has the Erdös-Pósa property if and only if it is planar."
This uses the proved (8.8) and (8.14), as in
the last sentence of their proof on page 113. -/
theorem theorem_8_2_proof {α' : Type u'} {β' : Type v'} (H : Graph α' β')
    (hV : V(H).Finite) (hE : E(H).Finite) :
    HasErdosPosaProperty.{u,v,u',v'} H ↔ IsPlanar H := by
  classical
  constructor
  · intro hEP
    by_contra hn
    exact theorem_8_14_proof.{u,v,u',v'} H hV hE hn hEP
  · exact theorem_8_8_proof

end GraphMinor.GM05
