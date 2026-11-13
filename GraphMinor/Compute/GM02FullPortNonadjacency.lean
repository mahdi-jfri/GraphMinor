module

public import GraphMinor.Compute.GM02FullPortVertices

/-!
# The absent edges of the numeric split graph

Only old-to-edge and edge-to-terminal pairs can be adjacent. The numeric
range inequalities rule out old-to-old, edge-to-edge, terminal-to-terminal,
and old-to-terminal edges. These facts complete the category cases for
comparing the machine's graph with the abstract split graph.
-/

public section
namespace GraphMinor.Compute

/-- No two old numeric vertices are adjacent. -/
theorem gm02FullPortGraph_not_adj_old_old (x : GM02TopologicalInput)
    (gflags hflags : List ℕ) (code K : ℕ) (a b : Fin x.G.n) :
    ¬ (gm02FullPortGraph x gflags hflags code K).Adj
      (gm02FullPortOld x K a) (gm02FullPortOld x K b) := by
  intro h
  have ha := a.isLt
  have hb := b.isLt
  simp only [gm02FullPortGraph, SimpleGraph.fromRel_adj, gm02FullPortForward, gm02FullPortOld] at h
  omega

/-- No two host-edge numeric vertices are adjacent. -/
theorem gm02FullPortGraph_not_adj_edge_edge (x : GM02TopologicalInput)
    (gflags hflags : List ℕ) (code K : ℕ) (e f : Fin x.G.edges.length) :
    ¬ (gm02FullPortGraph x gflags hflags code K).Adj
      (gm02FullPortEdge x K e) (gm02FullPortEdge x K f) := by
  intro h
  have he := e.isLt
  have hf := f.isLt
  simp only [gm02FullPortGraph, SimpleGraph.fromRel_adj, gm02FullPortForward, gm02FullPortEdge] at h
  omega

/-- No two numeric terminals are adjacent. -/
theorem gm02FullPortGraph_not_adj_terminal_terminal (x : GM02TopologicalInput)
    (gflags hflags : List ℕ) (code K : ℕ) (p q : Fin (2 * K)) :
    ¬ (gm02FullPortGraph x gflags hflags code K).Adj
      (gm02FullPortTerminal x K p) (gm02FullPortTerminal x K q) := by
  intro h
  simp only [gm02FullPortGraph, SimpleGraph.fromRel_adj, gm02FullPortForward, gm02FullPortTerminal] at h
  omega

/-- An old numeric vertex is never adjacent directly to a terminal. -/
theorem gm02FullPortGraph_not_adj_old_terminal (x : GM02TopologicalInput)
    (gflags hflags : List ℕ) (code K : ℕ) (a : Fin x.G.n) (p : Fin (2 * K)) :
    ¬ (gm02FullPortGraph x gflags hflags code K).Adj
      (gm02FullPortOld x K a) (gm02FullPortTerminal x K p) := by
  intro h
  have ha := a.isLt
  simp only [gm02FullPortGraph, SimpleGraph.fromRel_adj, gm02FullPortForward,
    gm02FullPortOld, gm02FullPortTerminal] at h
  omega

end GraphMinor.Compute
