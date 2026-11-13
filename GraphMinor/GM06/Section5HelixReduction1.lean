module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5SinglePathHelixDeletion
import GraphMinor.GM06.Section5MultiplePathHelixDeletion

/-!
# The edge-deletion case of the helix comparison

This proves Reduction 1 of VI (5.5), pages 130–132, for every
positive path count. The one-path case retains the clockwise side
in the cut cylinder. With at least two paths, the closed strip
projects injectively. Both cases use claim (1), the old-region
approach, and the direct auxiliary-curve crossing count.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Surface

/-- Graph Minors VI (5.5), the complete Reduction 1 case, with the
corrected clockwise condition when there is one linkage path. -/
theorem theorem_5_5_red1
    {k : ℕ} {G G' : Drawing ClosedCylinder} (L : CylinderLinkage k G) (L' : CylinderLinkage k G')
    (hG : IsCylinderSection5Drawing k G) (hG' : IsCylinderSection5Drawing k G')
    (hRed : Section5Reduction1Step k G L G' L')
    (f' : Curve ClosedCylinder) (hf' : IsHelix k G' f') :
    ∃ f : Curve ClosedCylinder, IsHelix k G f ∧ curvePhi k G f ≤ curvePhi k G' f' := by
  by_cases hk1 : k = 1
  · subst k
    exact theorem_5_5_red1_of_one L L' hG hG' hRed f' hf'
  · have hk : 1 < k := by have := hG.1; omega
    exact theorem_5_5_red1_of_two_le L L' hk hG hG' hRed f' hf'

end GraphMinor.GM06
