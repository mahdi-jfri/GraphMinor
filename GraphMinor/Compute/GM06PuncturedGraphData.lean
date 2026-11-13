module

public import GraphMinor.Compute.GM06PuncturedEdgeMark

/-!
# The finite graph searched after removing an initial vertex

For Reduction 2 in VI (5.7), page 133, the component search uses
only active edges whose ends avoid the removed vertex. Filtering
the supplied pairs gives that finite graph. The guarded row marks
are exactly its adjacency matrix, so ordinary breadth-first search
applies without a geometric component oracle. The removed label
stays as an isolated index. Searches from other labels compute
the components after deleting that vertex.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Retain the active endpoint pairs that avoid the removed vertex. -/
def gm06PuncturedPairs {n : ℕ} (tagged : List ((Fin n × Fin n) × ℕ)) (cut : Fin n) :
    List (Fin n × Fin n) :=
  tagged.filterMap fun p =>
    if p.2 = 1 then if p.1.1 = cut then none else if p.1.2 = cut then none else some p.1 else none

/-- The finite graph data used only for the punctured component search. -/
def gm06PuncturedGraphData {n : ℕ} (tagged : List ((Fin n × Fin n) × ℕ)) (cut : Fin n) :
    GM06DrawingData where
  n := n
  ends := gm06PuncturedPairs tagged cut
  regions := []
  cuffs := []
  division := []

/-- The guarded row scan is the row list of the filtered endpoint graph. -/
theorem gm06PuncturedRows_eq {n : ℕ} (tagged : List ((Fin n × Fin n) × ℕ)) (cut : Fin n) :
    tagged.flatMap (fun p => gm06PuncturedEdgeRows p.1 p.2 cut) =
      (gm06PuncturedPairs tagged cut).flatMap gm06VertexEdgeRows := by
  induction tagged with
  | nil => rfl
  | cons p tagged ih =>
    by_cases hb : p.2 = 1
    · by_cases hA : p.1.1 = cut
      · simp [gm06PuncturedPairs, gm06PuncturedEdgeRows, hb, hA] at ih ⊢
        exact ih
      · by_cases hB : p.1.2 = cut
        · simp [gm06PuncturedPairs, gm06PuncturedEdgeRows, hb, hA, hB] at ih ⊢
          exact ih
        · simpa [gm06PuncturedPairs, gm06PuncturedEdgeRows, hb, hA, hB] using
            congrArg (fun l => gm06VertexEdgeRows p.1 ++ l) ih
    · simp [gm06PuncturedPairs, gm06PuncturedEdgeRows, hb] at ih ⊢
      exact ih

/-- The exact matrix produced by the punctured endpoint scan. -/
def gm06PuncturedMatrixData {n : ℕ} (tagged : List ((Fin n × Fin n) × ℕ)) (cut : Fin n) :
    List ℕ :=
  (tagged.flatMap (fun p => gm06PuncturedEdgeRows p.1 p.2 cut)).foldl (gm06MatrixMarkRow n)
    (List.replicate (n * n) 0)

/-- The guarded matrix marks represent exactly the finite punctured graph. -/
theorem gm06PuncturedMatrixData_isAdjMatrixList {n : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (cut : Fin n) :
    IsAdjMatrixList (gm06PuncturedGraphData tagged cut).vertexGraph
      (gm06PuncturedMatrixData tagged cut) := by
  have h := gm06VertexMatrixData_isAdjMatrixList (gm06PuncturedGraphData tagged cut)
  simpa only [gm06VertexMatrixData, gm06PuncturedGraphData, gm06PuncturedMatrixData,
    gm06PuncturedRows_eq] using h

end GraphMinor.Compute
