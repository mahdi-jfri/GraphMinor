module

public import GraphMinor.Compute.Algorithm99Relabel
public import GraphMinor.Compute.Bridge3

/-!
# The individual edge order after compacting a deleted graph

Deleting the same vertex set twice changes nothing. The active pairs of the
compact graph, mapped back to their original endpoints, are therefore exactly
the active pairs of the deleted graph. Expanding multiplicities keeps this
identity and gives equal edge counts and matching endpoints at every index.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Deleting a vertex set twice is the same as deleting it once. -/
theorem alg99_deleteVertices_idem {n : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n)) :
    (G.deleteVertices Z).deleteVertices Z = G.deleteVertices Z := by
  ext u v
  simp only [MultiDigraph.deleteVertices_edgeMult]
  split_ifs <;> rfl

/-- Compacting the deleted graph preserves individual edge order under the
order-preserving endpoint map. -/
theorem alg99_compact_edgeList {n : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n)) :
    (G.deleteVertices Z).edgeListWithMult =
      ((G.deleteVertices Z).deleteVerticesCompact Z).edgeListWithMult.map
        (Prod.map (compactEmb Z) (compactEmb Z)) := by
  have hp := (G.deleteVertices Z).activePairsList_deleteVertices_eq_map Z
  rw [alg99_deleteVertices_idem] at hp
  unfold MultiDigraph.edgeListWithMult
  rw [hp, List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  intro p _
  simp only [List.map_replicate]
  rfl

/-- No individual edge is lost when the already deleted vertices are removed
from the vertex index set. -/
theorem alg99_numEdges_compact {n : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n)) :
    ((G.deleteVertices Z).deleteVerticesCompact Z).numEdges =
      (G.deleteVertices Z).numEdges := by
  have h := congrArg List.length (alg99_compact_edgeList G Z)
  simpa only [MultiDigraph.length_edgeListWithMult, List.length_map] using h.symm

/-- Corresponding source indices have the same endpoints in the original
labels. The correspondence is the identity on the natural-number edge index. -/
theorem alg99_compact_edgeEndpoints {n : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n))
    (i : Fin ((G.deleteVertices Z).deleteVerticesCompact Z).numEdges) :
    (G.deleteVertices Z).edgeEndpoints
      ((finCongr (alg99_numEdges_compact G Z)) i) =
      Prod.map (compactEmb Z) (compactEmb Z)
        (((G.deleteVertices Z).deleteVerticesCompact Z).edgeEndpoints i) := by
  have hi : i.1 < ((G.deleteVertices Z).deleteVerticesCompact Z).edgeListWithMult.length := by
    simpa only [MultiDigraph.length_edgeListWithMult] using i.2
  have hi' : i.1 < (G.deleteVertices Z).edgeListWithMult.length := by
    rw [alg99_compact_edgeList, List.length_map]
    exact hi
  have h := congrArg (fun l => l[i.1]?) (alg99_compact_edgeList G Z)
  rw [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi'] at h
  exact Option.some.inj h

end GraphMinor.Compute
