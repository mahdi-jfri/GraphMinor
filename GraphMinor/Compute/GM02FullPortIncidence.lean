module

public import GraphMinor.Compute.GM02FullPortVertices
public import GraphMinor.Compute.GM02ActiveIncidence

/-!
# The incidence meaning of numeric split adjacency

For an old vertex and a host-edge vertex, the numeric adjacency test
means exactly active incidence outside the pattern vertex set. For a
pattern terminal slot, its half-index recovers the original pattern
edge, and its candidate digit recovers the chosen host edge position.
-/

public section
namespace GraphMinor.Compute

/-- A zero vertex-mask entry means the supplied vertex is outside the pattern. -/
theorem gm02PortMask_zero_iff (x : GM02TopologicalInput) (a : Fin x.G.n) :
    (bitSetList x.vertices)[a.val]? = some 0 ↔ a ∉ x.vertices := by
  have hi : a.val < (bitSetList x.vertices).length := by rw [length_bitSetList]; exact a.isLt
  rw [List.getElem?_eq_getElem hi, getElem_bitSetList x.vertices a.val a.isLt]
  by_cases ha : a ∈ x.vertices <;> simp [ha]

/-- An old-to-edge adjacency is precisely an active incidence at a non-branch vertex. -/
theorem gm02FullPortGraph_old_edge_inc (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    (code K : ℕ) (a : Fin x.G.n) (e : Fin x.G.edges.length) :
    (gm02FullPortGraph x gflags hflags code K).Adj
      (gm02FullPortOld x K a) (gm02FullPortEdge x K e) ↔
      a ∉ x.vertices ∧ (gm02ActiveGraph x.G.graph gflags).Inc e.val a.val := by
  rw [gm02FullPortGraph_old_edge, gm02PortMask_zero_iff, gm02ActiveGraph_inc_getElem_iff]

/-- Dividing a terminal slot by two recovers its original pattern-edge position. -/
theorem gm02PortSlotEquiv_div_two (m : ℕ) (p : Fin m × Bool) :
    (gm02PortSlotEquiv m p).val / 2 = p.1.val := by
  rw [gm02PortSlotEquiv_val]
  cases p.2 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- The numeric terminal slot for an original supplied pattern edge and side. -/
@[expose] def gm02FullPortPatternTerminal (x : GM02TopologicalInput) (K : ℕ)
    (hK : x.edges.length ≤ K) (p : Fin x.edges.length × Bool) : Fin (gm02FullPortSize x K) :=
  gm02FullPortTerminal x K ⟨(gm02PortSlotEquiv x.edges.length p).val, by
    have := (gm02PortSlotEquiv x.edges.length p).isLt
    omega⟩

/-- A numeric pattern terminal is adjacent exactly to its active chosen host-edge position. -/
theorem gm02FullPortGraph_edge_patternTerminal (x : GM02TopologicalInput)
    (gflags hflags : List ℕ) (code K : ℕ) (hK : x.edges.length ≤ K)
    (e : Fin x.G.edges.length) (p : Fin x.edges.length × Bool) :
    (gm02FullPortGraph x gflags hflags code K).Adj
      (gm02FullPortEdge x K e) (gm02FullPortPatternTerminal x K hK p) ↔
      hflags[p.1.val]? = some 1 ∧ gflags[e.val]? = some 1 ∧
        (gm02PortAssignmentOfCode x code p).val = e.val := by
  rw [gm02FullPortPatternTerminal, gm02FullPortGraph_edge_terminal]
  simp only [gm02PortSlotEquiv_div_two, p.1.isLt, true_and]
  rfl

end GraphMinor.Compute
