module

public import GraphMinor.Compute.GM02CanonicalChildGraphs
public import GraphMinor.Compute.GM02FilteredChildMeaning

/-!
# Plain recursive inputs for canonical crossing-scheme children

Restrict each scheme termination to its surviving child vertices and
compact its canonical filtered graph. The resulting plain input is the
actual induced child's numbered representation. Feasibility and every
width bound are therefore preserved in both recursive calls.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set Classical GraphMinor.GM02

variable {n : ℕ} (F : SimpleGraph (Fin n)) (L R : Finset (Fin n))
  (A : Termination V(Graph.ofSimpleGraph F))
  (C : CrossingScheme (Graph.ofSimpleGraph F)
    ((Graph.ofSimpleGraph F).induce (L : Set (Fin n)))
    (((Graph.ofSimpleGraph F).induce (R : Set (Fin n))).deleteEdges
      E((Graph.ofSimpleGraph F).induce (L : Set (Fin n)))) A)

/-- The plain compact input for the corrected left child of a canonical scheme. -/
noncomputable def gm02CanonicalLeftInput : GM02SimpleTerminatedInput :=
  gm02FilteredChildInput F ∅ (gm02ChildVertices L R A.support.toFinset C.reservedLeft.toFinset C.left.support.toFinset)
    (C.left.rebase (gm02CanonicalChild_left_support F L R A C))

/-- The executable left child input is its actual induced graph with compact names. -/
theorem gm02CanonicalLeftInput_eq_numbered :
    gm02CanonicalLeftInput F L R A C =
      gm02CompactNumberedInstance C.inducedLeft (C.left.rebase C.left_support_subset_induced) (gm02ChildVertices L R A.support.toFinset C.reservedLeft.toFinset C.left.support.toFinset)ᶜ
        (gm02CanonicalChild_left_vertexSet F L R A C) := by
  have hi := gm02FilteredChildInput_eq_numbered F ∅ (gm02ChildVertices L R A.support.toFinset C.reservedLeft.toFinset C.left.support.toFinset)
    C.inducedLeft (C.left.rebase C.left_support_subset_induced) (gm02CanonicalChild_left_vertexSet F L R A C)
    (gm02CanonicalChild_left_pathGraph F L R A C)
  convert hi using 1
  unfold gm02CanonicalLeftInput
  congr 1

/-- The left recursive feasibility answer is exactly the induced-side answer of (2.9). -/
theorem gm02CanonicalLeftInput_feasible_iff :
    (gm02CanonicalLeftInput F L R A C).A.Feasible
      (Graph.ofSimpleGraph (gm02CanonicalLeftInput F L R A C).G) ↔
        C.left.Feasible C.inducedLeft := by
  rw [gm02CanonicalLeftInput_eq_numbered]
  exact (gm02CompactNumberedInstance_feasible_iff _ _ _ _).trans
    (C.left.feasible_rebase_iff _ _)

/-- The left recursive graph and the actual induced child have the same width bounds. -/
theorem gm02CanonicalLeftInput_treeWidthLE_iff (k : ℕ) :
    TreeWidthLE (Graph.ofSimpleGraph (gm02CanonicalLeftInput F L R A C).G) k ↔
      TreeWidthLE C.inducedLeft k := by
  rw [gm02CanonicalLeftInput_eq_numbered]
  exact gm02CompactNumberedInstance_treeWidthLE_iff _ _ _ _ k

/-- The plain compact input for the corrected right child of a canonical scheme. -/
noncomputable def gm02CanonicalRightInput : GM02SimpleTerminatedInput :=
  gm02FilteredChildInput F L (gm02ChildVertices R L A.support.toFinset C.reservedRight.toFinset C.right.support.toFinset)
    (C.right.rebase (gm02CanonicalChild_right_support F L R A C))

/-- The executable right child input is its actual induced graph with compact names. -/
theorem gm02CanonicalRightInput_eq_numbered :
    gm02CanonicalRightInput F L R A C =
      gm02CompactNumberedInstance C.inducedRight (C.right.rebase C.right_support_subset_induced) (gm02ChildVertices R L A.support.toFinset C.reservedRight.toFinset C.right.support.toFinset)ᶜ
        (gm02CanonicalChild_right_vertexSet F L R A C) := by
  have hi := gm02FilteredChildInput_eq_numbered F L (gm02ChildVertices R L A.support.toFinset C.reservedRight.toFinset C.right.support.toFinset)
    C.inducedRight (C.right.rebase C.right_support_subset_induced) (gm02CanonicalChild_right_vertexSet F L R A C)
    (gm02CanonicalChild_right_pathGraph F L R A C)
  convert hi using 1
  unfold gm02CanonicalRightInput
  congr 1

/-- The right recursive feasibility answer is exactly the induced-side answer of (2.9). -/
theorem gm02CanonicalRightInput_feasible_iff :
    (gm02CanonicalRightInput F L R A C).A.Feasible
      (Graph.ofSimpleGraph (gm02CanonicalRightInput F L R A C).G) ↔
        C.right.Feasible C.inducedRight := by
  rw [gm02CanonicalRightInput_eq_numbered]
  exact (gm02CompactNumberedInstance_feasible_iff _ _ _ _).trans
    (C.right.feasible_rebase_iff _ _)

/-- The right recursive graph and the actual induced child have the same width bounds. -/
theorem gm02CanonicalRightInput_treeWidthLE_iff (k : ℕ) :
    TreeWidthLE (Graph.ofSimpleGraph (gm02CanonicalRightInput F L R A C).G) k ↔
      TreeWidthLE C.inducedRight k := by
  rw [gm02CanonicalRightInput_eq_numbered]
  exact gm02CompactNumberedInstance_treeWidthLE_iff _ _ _ _ k

end GraphMinor.Compute
