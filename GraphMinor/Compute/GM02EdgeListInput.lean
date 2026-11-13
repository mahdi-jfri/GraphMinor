module

public import GraphMinor.Compute.Parse
public import GraphMinor.GM02.TreeDecomposition

/-!
# Plain edge-list multigraph inputs for II (4.6)

The paper measures graph size by vertices plus edges on page 310. Store
the vertex count and one pair of endpoints per actual edge. Repeated
pairs represent parallel edges and equal endpoints represent loops.
Edge names are their positions in this supplied list. Nothing in the
encoding describes a reduction, a path, or an answer.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set Classical

/-- A finite multigraph supplied by its vertex count and explicit list of edge endpoints. -/
structure GM02EdgeListInput where
  /-- Vertices have their given names below this count. -/
  n : ℕ
  /-- One supplied endpoint pair per edge, retaining loops and repetitions. -/
  edges : List (Fin n × Fin n)

/-- The actual undirected multigraph represented by the endpoint list. -/
def GM02EdgeListInput.graph (x : GM02EdgeListInput) : Graph ℕ ℕ where
  vertexSet := Set.Iio x.n
  edgeSet := Set.Iio x.edges.length
  IsLink e a b := ∃ h : e < x.edges.length,
    s(a, b) = s((x.edges[e]'h).1.val, (x.edges[e]'h).2.val)
  isLink_symm := by
    intro e _
    refine ⟨?_⟩
    intro a b h
    obtain ⟨he, hab⟩ := h
    exact ⟨he, (Sym2.eq_swap ..).trans hab⟩
  eq_or_eq_of_isLink_of_isLink := by
    intro e a b c d h₁ h₂
    obtain ⟨he₁, h₁⟩ := h₁
    obtain ⟨he₂, h₂⟩ := h₂
    rcases Sym2.eq_iff.1 (h₁.trans h₂.symm) with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  edge_mem_iff_exists_isLink := by
    intro e
    constructor
    · intro he
      exact ⟨(x.edges[e]'he).1.val, (x.edges[e]'he).2.val, he, rfl⟩
    · rintro ⟨a, b, he, _⟩
      exact he
  left_mem_of_isLink := by
    intro e a b h
    obtain ⟨he, h⟩ := h
    rcases Sym2.eq_iff.1 h with ⟨ha, _⟩ | ⟨ha, _⟩
    · exact ha.symm ▸ (x.edges[e]'he).1.isLt
    · exact ha.symm ▸ (x.edges[e]'he).2.isLt

/-- Only the vertex count, edge count, and supplied endpoint words occur in the input. -/
def GM02EdgeListInput.enc (x : GM02EdgeListInput) : List ℕ :=
  [x.n, x.edges.length] ++ flatEdges x.edges

/-- The graph size printed on II, page 310. -/
def GM02EdgeListInput.size (x : GM02EdgeListInput) : ℕ := x.n + x.edges.length

/-- Every supplied vertex is an actual graph vertex. -/
theorem GM02EdgeListInput.graph_vertices (x : GM02EdgeListInput) : V(x.graph) = Set.Iio x.n := rfl

/-- Every edge name is exactly one position of the supplied endpoint list. -/
theorem GM02EdgeListInput.graph_edges (x : GM02EdgeListInput) : E(x.graph) = Set.Iio x.edges.length := rfl

/-- The represented multigraph has a finite vertex set. -/
theorem GM02EdgeListInput.finite_vertices (x : GM02EdgeListInput) : V(x.graph).Finite := Set.finite_Iio _

/-- The represented multigraph has a finite edge set, including repeated endpoint pairs. -/
theorem GM02EdgeListInput.finite_edges (x : GM02EdgeListInput) : E(x.graph).Finite := Set.finite_Iio _

/-- The endpoints at a supplied edge position are linked by that actual edge. -/
theorem GM02EdgeListInput.isLink_getElem (x : GM02EdgeListInput) (e : ℕ) (he : e < x.edges.length) :
    x.graph.IsLink e (x.edges[e]'he).1.val (x.edges[e]'he).2.val := ⟨he, rfl⟩

end GraphMinor.Compute
