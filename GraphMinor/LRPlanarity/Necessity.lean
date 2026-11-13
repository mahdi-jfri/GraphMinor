module

public import GraphMinor.LRPlanarity.Statements
import GraphMinor.LRPlanarity.NecessityGeometric

/-!
# Geometric necessity of the fork constraints

Part IV, opening and Section 7 of the planarity note first obtains a
nonalternating contour from the plane embedding. The opening fork
comparison then shows that the contour coloring satisfies the fork
constraints. Only that comparison is supplied as a hypothesis here.
-/

public section
namespace GraphMinor.LRPlanarity

/-- Part IV, opening and Section 7 of the planarity note: every plane
embedding gives a fork coloring for every DFS forest. The sole hypothesis
is the separate contour-to-fork comparison. -/
theorem necessityStatement_of (hCF : ContourForkStatement) : NecessityStatement := by
  intro N G T hT hdrawing
  obtain ⟨order,hvalid,hword,hnonalt⟩ := geometricContourStatement N G T hT hdrawing
  exact ⟨contourColor T order,hCF N G T order hT hvalid hword hnonalt⟩

end GraphMinor.LRPlanarity
