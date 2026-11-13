module

public import GraphMinor.GM05.SimpleSubgraphLift
public import GraphMinor.GM05.PathTransfer
import GraphMinor.GM05.MinorTransfer
import GraphMinor.Minor.Basic

/-!
# Paths with their actual edges

Paths retain both an ordered vertex sequence and a graph with exactly those
steps, without loops or parallel copies. Thus different choices of a parallel
edge remain different paths. Taking shadows forgets only those edge choices.
-/

@[expose] public section
namespace GraphMinor.GM01.Full
open Graph Set SimpleGraph GM05
universe u v
variable {α : Type u} {β : Type v}

/-- A path with actual edges, as in Graph Minors I, Section 1, page 41.
The sequence has no repeated vertices. Its graph contains exactly one edge
for each step and no other edges. -/
structure Path (α : Type u) (β : Type v) where
  /-- Ordered vertices, including the initial and terminal vertices. -/
  toPath : GM01.Path α
  /-- The actual edges of the path. -/
  graph : Graph α β
  /-- The graph has exactly the steps of the sequence. -/
  shadow_eq : simpleShadow graph = toPath.toSubgraph
  /-- A path has no loop. -/
  no_loop : ∀ e x, ¬ graph.IsLink e x x
  /-- Each step uses one edge. -/
  no_parallel : ∀ e f x y, graph.IsLink e x y → graph.IsLink f x y → e = f

namespace Path
/-- Vertices of an actual-edge path. -/
def verts (P : Path α β) : Set α := P.toPath.verts

/-- A path is in the host when all its actual edges and vertices are. -/
def IsIn (P : Path α β) (G : Graph α β) : Prop := P.graph ≤ G

/-- The path graph has the vertices of the sequence. -/
theorem vertexSet_eq (P : Path α β) : V(P.graph) = P.verts :=
  congrArg SimpleGraph.Subgraph.verts P.shadow_eq

/-- A path in a general graph gives a path in its shadow. -/
theorem isIn_shadow {P : Path α β} {G : Graph α β} (h : P.IsIn G) :
    P.toPath.IsIn (simpleShadow G) := by
  rw [GM01.Path.IsIn, ← P.shadow_eq]
  exact simpleShadow_mono h

/-- Every path of the shadow can be realized using actual edges. -/
theorem exists_lift {G : Graph α β} {P : GM01.Path α}
    (h : P.IsIn (simpleShadow G)) :
    ∃ Q : Path α β, Q.IsIn G ∧ Q.toPath = P := by
  obtain ⟨K, hK, hs, hl, hp⟩ := GM05.Full.exists_simple_subgraph_lift h
  exact ⟨⟨P, K, hs, hl, hp⟩, hK, rfl⟩
end Path

/-- A finite grid-free graph has a grid-free shadow. -/
theorem shadow_mem_gridFree {θ : ℕ} {G : Graph α β}
    (hV : V(G).Finite) (hE : E(G).Finite)
    (hG : ¬ IsIsoMinor (gridGraph θ) G) : simpleShadow G ∈ 𝓕 θ := by
  intro hm
  exact hG (hm.trans (GM05.simpleShadow_isIsoMinor G hV hE))

end GraphMinor.GM01.Full
