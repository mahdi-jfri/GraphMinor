module

public import GraphMinor.Compute.GM02ChildVertexBits
public import GraphMinor.GM02.InducedTerminatedGraphs

/-!
# Relating computed child vertex sets to crossing schemes

The vertex-bit loop removes the corrected deletion set. On its chosen
side, membership in the opposite side is membership in the separator.
This identifies the computed set with the vertex set of the actual
induced child graph.
-/

public section
namespace GraphMinor.Compute
open Graph Set Classical GraphMinor.GM02

/-- Inside the chosen side, the opposite-side test is exactly the separator test. -/
theorem gm02ChildVertices_coe {n : ℕ} (S O Q Z P : Finset (Fin n)) :
    (gm02ChildVertices S O Q Z P : Set (Fin n)) =
      (S : Set (Fin n)) \ ((Z : Set (Fin n)) ∪
        (((Q : Set (Fin n)) ∩ ((S : Set (Fin n)) ∩ (O : Set (Fin n)))) \ P)) := by
  ext v
  simp only [gm02ChildVertices, Finset.mem_coe, Finset.mem_sdiff, Finset.mem_union,
    Finset.mem_inter, Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff]
  tauto

/-- The first computed child set is exactly the first corrected induced vertex set. -/
theorem gm02ChildVertices_eq_inducedLeft {n : ℕ} {β : Type*}
    {G H H' : Graph (Fin n) β} {A : Termination V(G)} (C : CrossingScheme G H H' A)
    (S O Q Z P : Finset (Fin n))
    (hS : (S : Set (Fin n)) = V(H)) (hO : (O : Set (Fin n)) = V(H'))
    (hQ : (Q : Set (Fin n)) = A.support) (hZ : (Z : Set (Fin n)) = C.reservedLeft)
    (hP : (P : Set (Fin n)) = C.left.support) :
    (gm02ChildVertices S O Q Z P : Set (Fin n)) = V(C.inducedLeft) := by
  rw [gm02ChildVertices_coe, hS, hO, hQ, hZ, hP]
  exact (Graph.vertexSet_deleteVerts _ _).symm

/-- The second computed child set is exactly the second corrected induced vertex set. -/
theorem gm02ChildVertices_eq_inducedRight {n : ℕ} {β : Type*}
    {G H H' : Graph (Fin n) β} {A : Termination V(G)} (C : CrossingScheme G H H' A)
    (S O Q Z P : Finset (Fin n))
    (hS : (S : Set (Fin n)) = V(H')) (hO : (O : Set (Fin n)) = V(H))
    (hQ : (Q : Set (Fin n)) = A.support) (hZ : (Z : Set (Fin n)) = C.reservedRight)
    (hP : (P : Set (Fin n)) = C.right.support) :
    (gm02ChildVertices S O Q Z P : Set (Fin n)) = V(C.inducedRight) := by
  rw [gm02ChildVertices_coe, hS, hO, hQ, hZ, hP]
  rw [CrossingScheme.inducedRight, Graph.vertexSet_deleteVerts, Set.inter_comm V(H') V(H)]

end GraphMinor.Compute
