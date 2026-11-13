module

public import GraphMinor.Compute.GM02FullPortIncidence
public import GraphMinor.Compute.GM02PortAssignment
public import GraphMinor.Compute.GM02PortPositions

/-!
# Numeric adjacency for the retained active split vertices

At retained old vertices the branch test is already false. At terminals
of active pattern edges both activity tests are already true. The two
numeric adjacency formulas thus reduce to the actual incidence and
chosen-edge equality in the abstract port graph.
-/

public section
namespace GraphMinor.Compute
open Graph Set GraphMinor.GM02

/-- A retained old split vertex is outside the supplied branch-vertex set. -/
theorem gm02PortOld_not_pattern (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    (k : ℕ) (a : Fin x.G.n)
    (ha : portOld a.val ∈ portVertexSet (gm02ActiveGraph x.G.graph gflags)
      (gm02ActiveGraph x.H hflags) k) : a ∉ x.vertices := by
  have hnot := ((portOld_mem_vertexSet_iff _ _ _ _).1 ha).2
  intro ham
  apply hnot
  exact Finset.mem_image.2 ⟨a, ham, rfl⟩

/-- An active retained old vertex has exactly the original active incidences. -/
theorem gm02FullPortGraph_retained_old_edge (x : GM02TopologicalInput)
    (gflags hflags : List ℕ) (code K k : ℕ) (a : Fin x.G.n) (e : Fin x.G.edges.length)
    (ha : portOld a.val ∈ portVertexSet (gm02ActiveGraph x.G.graph gflags)
      (gm02ActiveGraph x.H hflags) k) :
    (gm02FullPortGraph x gflags hflags code K).Adj
      (gm02FullPortOld x K a) (gm02FullPortEdge x K e) ↔
      (gm02ActiveGraph x.G.graph gflags).Inc e.val a.val := by
  rw [gm02FullPortGraph_old_edge_inc]
  exact and_iff_right (gm02PortOld_not_pattern x gflags hflags k a ha)

/-- A retained host-edge vertex carries an active supplied flag. -/
theorem gm02PortEdge_active_flag (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    (k e : ℕ) (he : portEdge e ∈ portVertexSet (gm02ActiveGraph x.G.graph gflags)
      (gm02ActiveGraph x.H hflags) k) : gflags[e]? = some 1 := by
  have hmem : e ∈ E(gm02ActiveGraph x.G.graph gflags) := by
    simpa [portVertexSet, portOld, portEdge, portTerminal] using he
  exact hmem.2

/-- At an active pattern terminal, numeric adjacency is exactly the abstract choice equality. -/
theorem gm02FullPortGraph_edge_activeTerminal (x : GM02TopologicalInput)
    (gflags hflags : List ℕ) (code K : ℕ) (hK : x.edges.length ≤ K) {k : ℕ}
    (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags))
    (hvalid : gm02PortAssignmentValid x gflags hflags (gm02PortAssignmentOfCode x code))
    (e : Fin x.G.edges.length) (p : Fin k × Bool)
    (he : portEdge e.val ∈ portVertexSet (gm02ActiveGraph x.G.graph gflags)
      (gm02ActiveGraph x.H hflags) k) :
    (gm02FullPortGraph x gflags hflags code K).Adj (gm02FullPortEdge x K e)
      (gm02FullPortPatternTerminal x K hK (gm02ActivePatternIndex x hflags (edge p.1), p.2)) ↔
      ((gm02PortChoiceOfAssignment x gflags hflags edge (gm02PortAssignmentOfCode x code) hvalid).edge p).val = e.val := by
  rw [gm02FullPortGraph_edge_patternTerminal, gm02PortChoiceOfAssignment_edge_val]
  simp only [gm02ActivePatternIndex_flag, gm02PortEdge_active_flag x gflags hflags k e.val he, true_and]

end GraphMinor.Compute
