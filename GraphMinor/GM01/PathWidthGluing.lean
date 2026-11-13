module

public import GraphMinor.GM01.PathBagBoundaries
import GraphMinor.GM01.PathBagRefinement
import GraphMinor.GM01.PathDecompositionRefinement

/-!
# Gluing path-width bounds across small bag overlaps

Graph Minors I, (1.6), page 40, starts with a path-decomposition
whose neighboring overlaps have size at most `k`. Each bag's shared
boundary has size at most `2k`. Refine its exclusive part using the
assumed width bound `k'`, keep the boundary in every new bag, and
concatenate the refinements. This gives the bound `k' + 2k`.
-/

public section

namespace GraphMinor.GM01

open Set Graph

/-- Graph Minors I, (1.6), page 40. If consecutive bag intersections
have size at most `k`, and deleting all other bags leaves width at
most `k'` for each chosen bag, the whole graph has width at most
`k' + 2k`. The proof refines each bag and concatenates the refinements. -/
theorem theorem_1_6_proof {α β : Type*} {G : Graph α β} (hfin : V(G).Finite)
    (D : PathDecomposition G) {k k' : ℕ}
    (hOverlap : ∀ i j : Fin D.length, j.val = i.val + 1 → (D.bag i ∩ D.bag j).ncard ≤ k)
    (hLocal : ∀ i : Fin D.length, HasPathWidthLE (G.deleteVerts (D.otherBags i)) k') :
    HasPathWidthLE G (k' + 2 * k) := by
  classical
  choose E hpos hsize hboundary hcover using
    (fun i ↦ exists_path_bag_refinement hfin (D.bag i) (D.otherBags i) (D.bag_subset i) (hLocal i))
  apply hasPathWidthLE_of_bag_refinements D E hpos ?_ hboundary
  intro i j
  have hBound := (D.boundary_ncard_le hfin hOverlap i).2
  change (D.bag i ∩ D.otherBags i).ncard ≤ 2 * k at hBound
  have hSize := (hsize i j).2
  exact ⟨(hsize i j).1, by omega⟩

end GraphMinor.GM01
