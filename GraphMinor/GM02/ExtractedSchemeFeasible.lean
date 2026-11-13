module

public import GraphMinor.GM02.ExtractedCrossingScheme
import GraphMinor.GM02.DeletePairPath

/-!
# Feasibility of the extracted induced graphs

The side-piece paths survive both kinds of deletion in the corrected
induced graphs. Transfer these paths after deleting the forbidden set.
Their supports stay unchanged, so disjointness on each side gives the
two feasible induced terminated graphs in the forward proof of II (2.9).
-/

public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set Classical
universe u v
variable {α : Type u} {β : Type v} (G H H' : Graph α β) (A : Termination V(G))
variable (P : ∀ p : {p // p ∈ A.pairs}, PairPath (pathGraph G) p.val)
variable (hP : ∀ p q, p ≠ q → Disjoint (P p).vertices (P q).vertices)
variable (hsep : IsSeparation G H H')

/-- First-side pieces realize the first corrected induced termination. -/
theorem extractedCrossingScheme_left_feasible :
    (extractedCrossingScheme G H H' A P hP hsep).left.Feasible
      (extractedCrossingScheme G H H' A P hP hsep).inducedLeft := by
  let C := extractedCrossingScheme G H H' A P hP hsep
  let X := C.reservedLeft ∪ ((A.support ∩ (V(H) ∩ V(H'))) \ C.left.support)
  have havoid (i : RunPieceIndex A G H P) (hc : i.color A G H P = true) :
      Disjoint (i.leftPath A G H P hc).vertices X := by
    rw [i.leftPath_vertices A G H P hc]
    exact i.avoids_extractedLeft G H H' A P hP hsep hc
  change (sideTermination A G H P hP true).Feasible (H.deleteVerts X)
  apply sideTermination_feasible_of_paths A G H P hP true (H.deleteVerts X)
    (fun i hc => (i.leftPath A G H P hc).deleteVerts X (havoid i hc))
  intro i hc
  rw [PairPath.deleteVerts_vertices, i.leftPath_vertices A G H P hc]

/-- Second-side pieces realize the second corrected induced termination. -/
theorem extractedCrossingScheme_right_feasible :
    (extractedCrossingScheme G H H' A P hP hsep).right.Feasible
      (extractedCrossingScheme G H H' A P hP hsep).inducedRight := by
  let C := extractedCrossingScheme G H H' A P hP hsep
  let X := C.reservedRight ∪ ((A.support ∩ (V(H) ∩ V(H'))) \ C.right.support)
  have havoid (i : RunPieceIndex A G H P) (hc : i.color A G H P = false) :
      Disjoint (i.rightPath A G H P hsep hc).vertices X := by
    rw [i.rightPath_vertices A G H P hsep hc]
    exact i.avoids_extractedRight G H H' A P hP hsep hc
  change (sideTermination A G H P hP false).Feasible (H'.deleteVerts X)
  apply sideTermination_feasible_of_paths A G H P hP false (H'.deleteVerts X)
    (fun i hc => (i.rightPath A G H P hsep hc).deleteVerts X (havoid i hc))
  intro i hc
  rw [PairPath.deleteVerts_vertices, i.rightPath_vertices A G H P hsep hc]

end GraphMinor.GM02
