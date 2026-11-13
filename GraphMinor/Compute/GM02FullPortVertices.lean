module

public import GraphMinor.Compute.GM02FullPortGraph

/-!
# The three numeric vertex ranges of the split graph

Old vertices retain their supplied names. Host-edge vertices start at
the vertex count, and terminal slots start after all host-edge positions.
The increasing pairs tested by the graph builder therefore have fixed,
explicit offsets.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The numeric copy of a supplied old vertex. -/
def gm02FullPortOld (x : GM02TopologicalInput) (K : ℕ) (a : Fin x.G.n) :
    Fin (gm02FullPortSize x K) := ⟨a.val, by have := a.isLt; unfold gm02FullPortSize; omega⟩

/-- The numeric vertex for a supplied host-edge position. -/
def gm02FullPortEdge (x : GM02TopologicalInput) (K : ℕ) (e : Fin x.G.edges.length) :
    Fin (gm02FullPortSize x K) := ⟨x.G.n + e.val, by have := e.isLt; unfold gm02FullPortSize; omega⟩

/-- The numeric vertex for one fixed terminal slot. -/
def gm02FullPortTerminal (x : GM02TopologicalInput) (K : ℕ) (p : Fin (2 * K)) :
    Fin (gm02FullPortSize x K) :=
  ⟨x.G.n + x.G.edges.length + p.val, by have := p.isLt; unfold gm02FullPortSize; omega⟩

/-- Old vertices precede every host-edge vertex. -/
theorem gm02FullPortOld_lt_edge (x : GM02TopologicalInput) (K : ℕ)
    (a : Fin x.G.n) (e : Fin x.G.edges.length) :
    (gm02FullPortOld x K a).val < (gm02FullPortEdge x K e).val := by
  have := a.isLt
  change a.val < x.G.n + e.val
  omega

/-- Host-edge vertices precede every terminal slot. -/
theorem gm02FullPortEdge_lt_terminal (x : GM02TopologicalInput) (K : ℕ)
    (e : Fin x.G.edges.length) (p : Fin (2 * K)) :
    (gm02FullPortEdge x K e).val < (gm02FullPortTerminal x K p).val := by
  have := e.isLt
  change x.G.n + e.val < x.G.n + x.G.edges.length + p.val
  omega

/-- The old-to-edge adjacency test reads precisely the original edge's endpoints and flags. -/
theorem gm02FullPortGraph_old_edge (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    (code K : ℕ) (a : Fin x.G.n) (e : Fin x.G.edges.length) :
    (gm02FullPortGraph x gflags hflags code K).Adj
      (gm02FullPortOld x K a) (gm02FullPortEdge x K e) ↔
      (bitSetList x.vertices)[a.val]? = some 0 ∧ gflags[e.val]? = some 1 ∧
        ((x.G.edges[e.val]'e.isLt).1.val = a.val ∨ (x.G.edges[e.val]'e.isLt).2.val = a.val) := by
  rw [gm02FullPortGraph_adj_of_lt x gflags hflags code K _ _ (gm02FullPortOld_lt_edge x K a e)]
  have hn : ¬ x.G.n ≤ a.val := Nat.not_le_of_gt a.isLt
  have he : x.G.n + e.val < x.G.n + x.G.edges.length := Nat.add_lt_add_left e.isLt _
  simp only [gm02FullPortForward, gm02FullPortOld, gm02FullPortEdge, a.isLt,
    Nat.le_add_right, he, hn, Nat.add_sub_cancel_left, e.isLt, ↓reduceDIte,
    true_and, false_and, or_false]

/-- Edge-to-terminal adjacency reads only active flags and the matching candidate digit. -/
theorem gm02FullPortGraph_edge_terminal (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    (code K : ℕ) (e : Fin x.G.edges.length) (p : Fin (2 * K)) :
    (gm02FullPortGraph x gflags hflags code K).Adj
      (gm02FullPortEdge x K e) (gm02FullPortTerminal x K p) ↔
      p.val / 2 < x.edges.length ∧ hflags[p.val / 2]? = some 1 ∧
        gflags[e.val]? = some 1 ∧ gm02SeparatorDigit x.G.edges.length code p.val = e.val := by
  rw [gm02FullPortGraph_adj_of_lt x gflags hflags code K _ _ (gm02FullPortEdge_lt_terminal x K e p)]
  have hn : ¬ x.G.n + e.val < x.G.n := by omega
  have he : x.G.n + e.val < x.G.n + x.G.edges.length := Nat.add_lt_add_left e.isLt _
  have hp : x.G.n + x.G.edges.length + p.val < gm02FullPortSize x K := by
    have := p.isLt
    unfold gm02FullPortSize
    omega
  simp only [gm02FullPortForward, gm02FullPortEdge, gm02FullPortTerminal, hn,
    Nat.le_add_right, he, hp, Nat.add_sub_cancel_left, true_and, false_and, false_or]

end GraphMinor.Compute
