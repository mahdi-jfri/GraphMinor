module

public import GraphMinor.Compute.CrossingTopCoreProved
public import GraphMinor.Compute.Algorithm99Complete
public import GraphMinor.Compute.Join13
import GraphMinor.Compute.SpecsCrossingReductionProved

/-! The disjoint-paths assembly uses the proved crossing extractor and its
Shiloach reduction together with the XIII algorithm. -/

public section
namespace GraphMinor.Compute.Crossing

/-- **The main result of Graph Minors XIII, from planarity** (with explicit
`ReplaceRecProgClaim` and `LoopRecProgClaim` hypotheses). -/
theorem disjointPathsStatement_of_planarity_full (hPl : PlanarityTestStatement)
    (hC3 : Case3StepsClaim) (hR : ReplaceRecProgClaim) (hCl : ClassifyProgClaim)
    (hLoop : LoopRecProgClaim) (hLift : LiftRecHistProgClaim) :
    DisjointPathsStatement :=
  disjointPathsStatement_of_shiloach
    shiloach80Statement_of_crossingExtractor
    (fun hSh h72 h97 => algorithm_9_9_of_case3Steps hSh h72 h97 hC3)

/-- **The main result of Graph Minors XIII, from planarity**:
combines `crossingExtractor_of`, `shiloach80Statement_of_crossingExtractor`,
`algorithm_9_9_of_case3Steps`, and `disjointPathsStatement_of_shiloach`. -/
theorem disjointPathsStatement_of_planarity (hPl : PlanarityTestStatement)
    (hC3 : Case3StepsClaim) (hCl : ClassifyProgClaim) (hLift : LiftRecHistProgClaim) :
    DisjointPathsStatement :=
  disjointPathsStatement_of_shiloach
    shiloach80Statement_of_crossingExtractor
    (fun hSh h72 h97 => algorithm_9_9_of_case3Steps hSh h72 h97 hC3)

end GraphMinor.Compute.Crossing
