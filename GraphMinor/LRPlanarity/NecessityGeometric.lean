module

public import GraphMinor.LRPlanarity.Statements
import GraphMinor.LRPlanarity.Polygonalization
import GraphMinor.LRPlanarity.NecessityPolygonalContour

/-!
# Geometric embeddings give nonalternating contours

Part IV, Section 7 of the planarity note first replaces the continuous
edge arcs by polygonal arcs. The graph and its DFS forest stay the same.
The polygonal neighborhood construction then supplies valid local orders
whose whole-forest contour is a nonalternating port word.
-/

public section
namespace GraphMinor.LRPlanarity

/-- Part IV, Section 7 of the planarity note: a geometric plane embedding
gives a nonalternating contour for every DFS forest, by polygonalization
followed by the polygonal contour construction. -/
theorem geometricContourStatement : GeometricContourStatement := by
  intro N G T hT hdrawing
  obtain ⟨drawing⟩ := hdrawing
  obtain ⟨polygonal,hpolygonal,_⟩ := polygonalizationStatement N G drawing
  exact polygonalContourStatement N G T polygonal hT hpolygonal

end GraphMinor.LRPlanarity
