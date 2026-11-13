module

public import GraphMinor.Surface.Defs
public import GraphMinor.Minor.Model
public import GraphMinor.GM09.Defs
import GraphMinor.Minor.Basic

/-!
# Topological containment of finite multigraphs

Graph Minors IV, Section 1, page 229 defines a subdivision by repeated replacement
of an edge by two edges in series. We express one replacement by its vertices,
edges, and incidence relation. In particular, replacing a loop gives two parallel
edges. Subdivisions are finite sequences of these replacements. Isomorphisms
before and after the sequence allow arbitrary names for vertices and edges.
-/

@[expose] public section

namespace GraphMinor.GM04

open Graph

/-- Replace one edge by two edges in series, as in Graph Minors IV, Section 1,
page 229. The new vertex and the two new edges are fresh. The ends of the
replaced edge may coincide, so the definition also applies to loops. -/
def IsEdgeSubdivision {α β : Type*} (G H : Graph α β) : Prop :=
  ∃ e u v a f g,
    G.IsLink e u v ∧ a ∉ V(G) ∧ f ∉ E(G) ∧ g ∉ E(G) ∧ f ≠ g ∧
    V(H) = insert a V(G) ∧ E(H) = insert f (insert g (E(G) \ {e})) ∧
    ∀ d x y, H.IsLink d x y ↔
      (d ≠ e ∧ G.IsLink d x y) ∨
      (d = f ∧ ((x = u ∧ y = a) ∨ (x = a ∧ y = u))) ∨
      (d = g ∧ ((x = a ∧ y = v) ∨ (x = v ∧ y = a)))

/-- Graph Minors IV, Section 1, page 229: a graph topologically contains another
when one of its subgraphs is isomorphic to a subdivision of the other.
The intermediate graphs use natural numbers as names. For finite graphs these
provide enough fresh names for every finite sequence of subdivisions. -/
def IsTopologicalMinor {α β α' β' : Type*} (H : Graph α β) (G : Graph α' β') : Prop :=
  ∃ H₀ S : Graph ℕ ℕ, Nonempty (Iso H H₀) ∧
    Relation.ReflTransGen IsEdgeSubdivision H₀ S ∧
    ∃ K ≤ G, Nonempty (Iso S K)

/-- An undirected tree is non-null, connected, and has no circuits (Graph Minors IV,
Section 2, page 230). Finiteness is required separately in sequence statements. -/
def IsUndirectedTree {α β : Type*} (G : Graph α β) : Prop :=
  GraphConnected G ∧ Surface.IsGraphForest G

/-- A family of `k` vertex-disjoint circuits, as in Graph Minors IV, (1.3),
page 229. Circuits include loops and pairs of parallel edges. -/
def HasDisjointCircuits {α β : Type*} (G : Graph α β) (k : ℕ) : Prop :=
  ∃ C : Fin k → Graph α β, (∀ i, GM09.IsGraphCircuit G (C i)) ∧
    Pairwise (fun i j ↦ Disjoint V(C i) V(C j))

/-- Every graph has an empty family of vertex-disjoint circuits. Consequently
there are no graphs satisfying the exclusion in IV (1.3) when `k = 0`. -/
theorem hasDisjointCircuits_zero {α β : Type*} (G : Graph α β) :
    HasDisjointCircuits G 0 :=
  ⟨Fin.elim0, fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i⟩

/-- A graph without edges cannot undergo an edge subdivision. -/
theorem not_isEdgeSubdivision_of_edgeSet_eq_empty {α β : Type*} {G H : Graph α β}
    (hG : E(G) = ∅) : ¬ IsEdgeSubdivision G H := by
  rintro ⟨e, u, v, a, f, g, he, _⟩
  have hm := he.edge_mem
  rw [hG] at hm
  exact hm

/-- A graph already using natural numbers as names is topologically contained
in itself, by a subdivision sequence of length zero. -/
theorem isTopologicalMinor_refl_nat (G : Graph ℕ ℕ) : IsTopologicalMinor G G :=
  ⟨G, G, ⟨Iso.refl G⟩, .refl, G, le_rfl, ⟨Iso.refl G⟩⟩

end GraphMinor.GM04
