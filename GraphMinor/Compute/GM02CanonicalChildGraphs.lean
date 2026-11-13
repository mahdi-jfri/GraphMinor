module

public import GraphMinor.Compute.GM02ChildGraphNormalization
public import GraphMinor.Compute.GM02ChildVertexSets

/-!
# The path graphs of corrected canonical children

Give every separator edge to the first vertex side. For a crossing
scheme on those canonical sides, remove its corrected deletion sets.
The resulting first path graph keeps all parent edges on its surviving
vertices. The second also omits edges assigned to the first side. These
are exactly the two executable edge-filter configurations.
-/

public section
namespace GraphMinor.Compute
open Graph Set Classical GraphMinor.GM02

variable {n : ℕ} (F : SimpleGraph (Fin n)) (L R : Finset (Fin n))
  (A : Termination V(Graph.ofSimpleGraph F))
  (C : CrossingScheme (Graph.ofSimpleGraph F)
    ((Graph.ofSimpleGraph F).induce (L : Set (Fin n)))
    (((Graph.ofSimpleGraph F).induce (R : Set (Fin n))).deleteEdges
      E((Graph.ofSimpleGraph F).induce (L : Set (Fin n)))) A)

/-- The corrected first child is induced by its computed vertex set. -/
theorem gm02CanonicalChild_left_graph :
    C.inducedLeft = (Graph.ofSimpleGraph F).induce
      (gm02ChildVertices L R A.support.toFinset C.reservedLeft.toFinset
        C.left.support.toFinset : Set (Fin n)) := by
  have hV := gm02ChildVertices_eq_inducedLeft C L R A.support.toFinset
    C.reservedLeft.toFinset C.left.support.toFinset rfl rfl
    (Set.coe_toFinset _) (Set.coe_toFinset _) (Set.coe_toFinset _)
  calc
    C.inducedLeft = (Graph.ofSimpleGraph F).induce V(C.inducedLeft) := by
      simp only [CrossingScheme.inducedLeft, gm02Induce_deleteVerts]
      rfl
    _ = _ := congrArg (Graph.induce (Graph.ofSimpleGraph F)) hV.symm

/-- The corrected second child keeps the same canonical edge exclusions. -/
theorem gm02CanonicalChild_right_graph :
    C.inducedRight = ((Graph.ofSimpleGraph F).induce
      (gm02ChildVertices R L A.support.toFinset C.reservedRight.toFinset
        C.right.support.toFinset : Set (Fin n))).deleteEdges
          E((Graph.ofSimpleGraph F).induce (L : Set (Fin n))) := by
  have hV := gm02ChildVertices_eq_inducedRight C R L A.support.toFinset
    C.reservedRight.toFinset C.right.support.toFinset rfl rfl
    (Set.coe_toFinset _) (Set.coe_toFinset _) (Set.coe_toFinset _)
  calc
    C.inducedRight = ((Graph.ofSimpleGraph F).induce V(C.inducedRight)).deleteEdges
        E((Graph.ofSimpleGraph F).induce (L : Set (Fin n))) := by
      simp only [CrossingScheme.inducedRight, gm02Induce_deleteEdges_deleteVerts]
      rfl
    _ = _ := congrArg (fun S => ((Graph.ofSimpleGraph F).induce S).deleteEdges
      E((Graph.ofSimpleGraph F).induce (L : Set (Fin n)))) hV.symm

/-- Every first-side endpoint belongs to the computed surviving vertex set. -/
theorem gm02CanonicalChild_left_support :
    C.left.support ⊆ {v : Fin n | v ∉
      (gm02ChildVertices L R A.support.toFinset C.reservedLeft.toFinset C.left.support.toFinset)ᶜ} := by
  intro v hv
  have hmem := C.left_support_subset_induced hv
  rw [gm02CanonicalChild_left_graph F L R A C] at hmem
  change v ∈ gm02ChildVertices L R A.support.toFinset C.reservedLeft.toFinset
    C.left.support.toFinset at hmem
  simpa only [Set.mem_ofPred_eq, Finset.mem_compl, not_not] using hmem

/-- Every second-side endpoint belongs to the computed surviving vertex set. -/
theorem gm02CanonicalChild_right_support :
    C.right.support ⊆ {v : Fin n | v ∉
      (gm02ChildVertices R L A.support.toFinset C.reservedRight.toFinset C.right.support.toFinset)ᶜ} := by
  intro v hv
  have hmem := C.right_support_subset_induced hv
  rw [gm02CanonicalChild_right_graph F L R A C] at hmem
  change v ∈ gm02ChildVertices R L A.support.toFinset C.reservedRight.toFinset
    C.right.support.toFinset at hmem
  simpa only [Set.mem_ofPred_eq, Finset.mem_compl, not_not] using hmem

/-- The computed first-child deletion complement is exactly its actual vertex set. -/
theorem gm02CanonicalChild_left_vertexSet :
    V(C.inducedLeft) = {v : Fin n | v ∉
      (gm02ChildVertices L R A.support.toFinset C.reservedLeft.toFinset C.left.support.toFinset)ᶜ} := by
  rw [gm02CanonicalChild_left_graph F L R A C]
  change (gm02ChildVertices L R A.support.toFinset C.reservedLeft.toFinset
    C.left.support.toFinset : Set (Fin n)) = _
  ext v
  simp only [Finset.mem_coe, Set.mem_ofPred_eq, Finset.mem_compl, not_not]

/-- The computed second-child deletion complement is exactly its actual vertex set. -/
theorem gm02CanonicalChild_right_vertexSet :
    V(C.inducedRight) = {v : Fin n | v ∉
      (gm02ChildVertices R L A.support.toFinset C.reservedRight.toFinset C.right.support.toFinset)ᶜ} := by
  rw [gm02CanonicalChild_right_graph F L R A C]
  change (gm02ChildVertices R L A.support.toFinset C.reservedRight.toFinset
    C.right.support.toFinset : Set (Fin n)) = _
  ext v
  simp only [Finset.mem_coe, Set.mem_ofPred_eq, Finset.mem_compl, not_not]

/-- The first canonical child has the first executable filtered path graph. -/
theorem gm02CanonicalChild_left_pathGraph :
    pathGraph C.inducedLeft = gm02FilteredSide F ∅
      (gm02ChildVertices L R A.support.toFinset C.reservedLeft.toFinset C.left.support.toFinset) := by
  rw [gm02CanonicalChild_left_graph F L R A C, gm02InducedSimple_pathGraph]

/-- The second canonical child has the second executable filtered path graph. -/
theorem gm02CanonicalChild_right_pathGraph :
    pathGraph C.inducedRight = gm02FilteredSide F L
      (gm02ChildVertices R L A.support.toFinset C.reservedRight.toFinset C.right.support.toFinset) := by
  rw [gm02CanonicalChild_right_graph F L R A C, gm02FilteredSide_pathGraph]

end GraphMinor.Compute
