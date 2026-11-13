module

public import GraphMinor.Compute.GM02EdgeListInput
public import GraphMinor.GM02.TopologicalContainment
public import Mathlib.Data.Finset.Sort

/-!
# The plain pair of graph inputs of II (4.6)

Supply the host edge list, the pattern's vertex names, and the pattern
edge list. Every pattern endpoint belongs to its supplied vertex set,
which is a subset of the host vertices. The input contains no incident
edge choices, suppression sequence, or path. The three answer flags
state exactly the alternatives printed on II, page 319.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set Classical GraphMinor.GM02

/-- A host graph and a pattern on a supplied subset of its vertices, as in II (4.6). -/
structure GM02TopologicalInput where
  /-- The host's plain explicit edge-list input. -/
  G : GM02EdgeListInput
  /-- The pattern's given vertex names, including isolated vertices. -/
  vertices : Finset (Fin G.n)
  /-- The pattern's actual edges, retaining repeated pairs and loops. -/
  edges : List (Fin G.n × Fin G.n)
  /-- Both ends of each pattern edge are supplied pattern vertices. -/
  ends_mem : ∀ p ∈ edges, p.1 ∈ vertices ∧ p.2 ∈ vertices

/-- The pattern edge list with the common ambient vertex numbering. -/
def GM02TopologicalInput.patternSource (x : GM02TopologicalInput) : GM02EdgeListInput :=
  ⟨x.G.n, x.edges⟩

/-- The supplied pattern graph has precisely its supplied vertex subset. -/
def GM02TopologicalInput.H (x : GM02TopologicalInput) : Graph ℕ ℕ :=
  x.patternSource.graph.induce (x.vertices.image Fin.val : Set ℕ)

/-- The supplied pattern vertices are host vertices. -/
theorem GM02TopologicalInput.pattern_vertices_subset (x : GM02TopologicalInput) : V(x.H) ⊆ V(x.G.graph) := by
  intro a ha
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 ha
  exact v.isLt

/-- The pattern's induced graph is a subgraph of its plain edge-list graph. -/
theorem GM02TopologicalInput.pattern_le_source (x : GM02TopologicalInput) : x.H ≤ x.patternSource.graph := by
  apply Graph.induce_le
  intro a ha
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 ha
  exact v.isLt

/-- The pattern is finite on its explicitly supplied vertices. -/
theorem GM02TopologicalInput.pattern_finite_vertices (x : GM02TopologicalInput) : V(x.H).Finite :=
  (x.vertices.image Fin.val).finite_toSet

/-- Every pattern edge retains its actual list position as an edge name. -/
theorem GM02TopologicalInput.pattern_edges (x : GM02TopologicalInput) : E(x.H) = Set.Iio x.edges.length := by
  apply Set.Subset.antisymm
  · exact (x.pattern_le_source).edgeSet_mono
  · intro e he
    have hm := x.ends_mem (x.edges[e]'he) (List.getElem_mem he)
    have hl : x.H.IsLink e (x.edges[e]'he).1.val (x.edges[e]'he).2.val :=
      ⟨⟨he, rfl⟩, Finset.mem_image.2 ⟨_, hm.1, rfl⟩, Finset.mem_image.2 ⟨_, hm.2, rfl⟩⟩
    exact hl.edge_mem

/-- The pattern has finitely many edges, including parallel copies. -/
theorem GM02TopologicalInput.pattern_finite_edges (x : GM02TopologicalInput) : E(x.H).Finite := by
  rw [x.pattern_edges]
  exact Set.finite_Iio _

/-- Plain input words consist only of the two supplied edge lists and pattern vertex names. -/
noncomputable def GM02TopologicalInput.enc (x : GM02TopologicalInput) : List ℕ :=
  x.G.enc ++ [x.vertices.card] ++ ((x.vertices.sort (· ≤ ·)).map Fin.val) ++
    [x.edges.length] ++ flatEdges x.edges

/-- The sum of the two graph sizes, using II's vertex-plus-edge measure. -/
def gm02TopologicalSize (x : GM02TopologicalInput) : ℕ :=
  x.G.size + x.vertices.card + x.edges.length

/-- The output flags are the three alternatives of II (4.6), page 319. -/
def GM02TopologicalInput.correct (x : GM02TopologicalInput) (w : ℤ) (s : State) : Prop :=
  (s.regs outReg = 1 ∧ TopologicallyContains x.G.graph x.H) ∨
  (s.regs outReg = 0 ∧ ¬TopologicallyContains x.G.graph x.H) ∨
  (s.regs outReg = 2 ∧ w < (treeWidth x.G.graph x.G.finite_vertices x.G.finite_edges : ℕ))

end GraphMinor.Compute
