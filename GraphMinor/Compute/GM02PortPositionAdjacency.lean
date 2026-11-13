module

public import GraphMinor.Compute.GM02PortPositionEmbedding
public import GraphMinor.Compute.GM02FullPortActiveAdjacency
public import GraphMinor.Compute.GM02FullPortNonadjacency

/-!
# The numeric embedding preserves and reflects split adjacency

Compare the three vertex types in both constructions. The two possible
edge types use active incidence or chosen-edge equality. All other
pairs have no edge in either construction. The resulting equivalence
identifies the induced numeric graph on the retained positions.
-/

public section
namespace GraphMinor.Compute
open Graph Set GraphMinor.GM02

/-- The numeric embedding has precisely the abstract split adjacency on its image. -/
theorem gm02PortPositionEmbedding_adj_iff (x : GM02TopologicalInput)
    (gflags hflags : List ℕ) (code K : ℕ) (hK : x.edges.length ≤ K) {k : ℕ}
    (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags))
    (hvalid : gm02PortAssignmentValid x gflags hflags (gm02PortAssignmentOfCode x code))
    (a b : portVertexSet (gm02ActiveGraph x.G.graph gflags) (gm02ActiveGraph x.H hflags) k) :
    (gm02FullPortGraph x gflags hflags code K).Adj
      (gm02PortPositionEmbedding x gflags hflags edge hK a)
      (gm02PortPositionEmbedding x gflags hflags edge hK b) ↔
      portAdj (gm02ActiveGraph x.G.graph gflags)
        (fun p => ((gm02PortChoiceOfAssignment x gflags hflags edge
          (gm02PortAssignmentOfCode x code) hvalid).edge p).val) a.val b.val := by
  let slot (p : Fin k × Bool) : Fin (2 * K) :=
    ⟨(gm02PortSlotEquiv x.edges.length (gm02ActivePatternIndex x hflags (edge p.1), p.2)).val, by
      have := (gm02PortSlotEquiv x.edges.length (gm02ActivePatternIndex x hflags (edge p.1), p.2)).isLt
      omega⟩
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  rcases a with (a | e) | p <;> rcases b with (b | f) | q
  · let a' : Fin x.G.n := ⟨a, gm02PortPosition_old_bound x gflags hflags k a ha⟩
    let b' : Fin x.G.n := ⟨b, gm02PortPosition_old_bound x gflags hflags k b hb⟩
    change (gm02FullPortGraph x gflags hflags code K).Adj
      (gm02FullPortOld x K a') (gm02FullPortOld x K b') ↔ False
    exact iff_false_intro (gm02FullPortGraph_not_adj_old_old x gflags hflags code K a' b')
  · let a' : Fin x.G.n := ⟨a, gm02PortPosition_old_bound x gflags hflags k a ha⟩
    let f' : Fin x.G.edges.length := ⟨f, gm02PortPosition_edge_bound x gflags hflags k f hb⟩
    change (gm02FullPortGraph x gflags hflags code K).Adj
      (gm02FullPortOld x K a') (gm02FullPortEdge x K f') ↔ _
    exact gm02FullPortGraph_retained_old_edge x gflags hflags code K k a' f' ha
  · let a' : Fin x.G.n := ⟨a, gm02PortPosition_old_bound x gflags hflags k a ha⟩
    change (gm02FullPortGraph x gflags hflags code K).Adj
      (gm02FullPortOld x K a') (gm02FullPortTerminal x K (slot q)) ↔ False
    exact iff_false_intro (gm02FullPortGraph_not_adj_old_terminal x gflags hflags code K a' (slot q))
  · let e' : Fin x.G.edges.length := ⟨e, gm02PortPosition_edge_bound x gflags hflags k e ha⟩
    let b' : Fin x.G.n := ⟨b, gm02PortPosition_old_bound x gflags hflags k b hb⟩
    change (gm02FullPortGraph x gflags hflags code K).Adj
      (gm02FullPortEdge x K e') (gm02FullPortOld x K b') ↔ _
    rw [SimpleGraph.adj_comm]
    exact gm02FullPortGraph_retained_old_edge x gflags hflags code K k b' e' hb
  · let e' : Fin x.G.edges.length := ⟨e, gm02PortPosition_edge_bound x gflags hflags k e ha⟩
    let f' : Fin x.G.edges.length := ⟨f, gm02PortPosition_edge_bound x gflags hflags k f hb⟩
    change (gm02FullPortGraph x gflags hflags code K).Adj
      (gm02FullPortEdge x K e') (gm02FullPortEdge x K f') ↔ False
    exact iff_false_intro (gm02FullPortGraph_not_adj_edge_edge x gflags hflags code K e' f')
  · let e' : Fin x.G.edges.length := ⟨e, gm02PortPosition_edge_bound x gflags hflags k e ha⟩
    change (gm02FullPortGraph x gflags hflags code K).Adj
      (gm02FullPortEdge x K e')
      (gm02FullPortPatternTerminal x K hK (gm02ActivePatternIndex x hflags (edge q.1), q.2)) ↔ _
    exact gm02FullPortGraph_edge_activeTerminal x gflags hflags code K hK edge hvalid e' q ha
  · let b' : Fin x.G.n := ⟨b, gm02PortPosition_old_bound x gflags hflags k b hb⟩
    change (gm02FullPortGraph x gflags hflags code K).Adj
      (gm02FullPortTerminal x K (slot p)) (gm02FullPortOld x K b') ↔ False
    rw [SimpleGraph.adj_comm]
    exact iff_false_intro (gm02FullPortGraph_not_adj_old_terminal x gflags hflags code K b' (slot p))
  · let f' : Fin x.G.edges.length := ⟨f, gm02PortPosition_edge_bound x gflags hflags k f hb⟩
    change (gm02FullPortGraph x gflags hflags code K).Adj
      (gm02FullPortPatternTerminal x K hK (gm02ActivePatternIndex x hflags (edge p.1), p.2))
      (gm02FullPortEdge x K f') ↔ _
    rw [SimpleGraph.adj_comm]
    exact gm02FullPortGraph_edge_activeTerminal x gflags hflags code K hK edge hvalid f' p hb
  · change (gm02FullPortGraph x gflags hflags code K).Adj
      (gm02FullPortTerminal x K (slot p)) (gm02FullPortTerminal x K (slot q)) ↔ False
    exact iff_false_intro (gm02FullPortGraph_not_adj_terminal_terminal x gflags hflags code K (slot p) (slot q))

end GraphMinor.Compute
