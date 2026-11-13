module

public import GraphMinor.Kruskal.AddressIntervals

/-!
# Forests with a fixed set of added vertices

A graph with a chosen vertex set whose deletion leaves a forest can be
recorded by its forest components, edge counts from each forest vertex to
the chosen vertices, and edge counts within the chosen set. This file
constructs graphs from that data. Every edge has two specified ends, so
loops and parallel edges are retained.
-/

@[expose] public section

namespace GraphMinor.Mader

open Graph Kruskal

/-- A multigraph with every vertex and edge present and with the specified
ends for each edge. An edge may have equal ends. -/
def graphOfEnds {V E : Type*} (left right : E → V) : Graph V E where
  vertexSet := Set.univ
  edgeSet := Set.univ
  IsLink e x y := (x = left e ∧ y = right e) ∨ (x = right e ∧ y = left e)
  isLink_symm _ _ := ⟨by
    intro x y h
    exact h.elim (fun h ↦ Or.inr h.symm) (fun h ↦ Or.inl h.symm)⟩
  eq_or_eq_of_isLink_of_isLink := by
    intro e x y z w h h'
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  edge_mem_iff_exists_isLink e :=
    ⟨fun _ ↦ ⟨left e, right e, Or.inl ⟨rfl, rfl⟩⟩, fun _ ↦ Set.mem_univ _⟩
  left_mem_of_isLink _ := by intro x y _; exact Set.mem_univ x

/-- The vertices of the disjoint family of forest components. -/
abbrev ForestVertex {n : ℕ} (t : Fin n → OrderedTree) :=
  Σ i, V(rootedGraph (t i).toRootedTree)

/-- The edges of the disjoint family of forest components. -/
abbrev ForestEdge {n : ℕ} (t : Fin n → OrderedTree) :=
  Σ i, E(rootedGraph (t i).toRootedTree)

/-- An attachment edge is indexed by its forest end, its chosen end, and
its position among the parallel edges with those ends. -/
abbrev AttachmentEdge {k n : ℕ} (t : Fin n → OrderedTree)
    (f : Fin n → List ℕ → Fin k → ℕ) :=
  Σ v : ForestVertex t, Σ a : Fin k, Fin (f v.1 v.2.val a)

/-- An edge within the chosen set is indexed by its two ends and its
position among the edges with those ends. -/
abbrev CoreEdge {k : ℕ} (c : Fin k × Fin k → ℕ) :=
  Σ a : Fin k, Σ b : Fin k, Fin (c (a, b))

/-- The three kinds of edges in a forest with added vertices. -/
abbrev ApexForestEdge {k n : ℕ} (t : Fin n → OrderedTree)
    (f : Fin n → List ℕ → Fin k → ℕ) (c : Fin k × Fin k → ℕ) :=
  ForestEdge t ⊕ (AttachmentEdge t f ⊕ CoreEdge c)

/-- The first end of each edge. Forest edges point from parent to child. -/
def apexForestLeft {k n : ℕ} (t : Fin n → OrderedTree)
    (f : Fin n → List ℕ → Fin k → ℕ) (c : Fin k × Fin k → ℕ) :
    ApexForestEdge t f c → Fin k ⊕ ForestVertex t
  | .inl ⟨i, e⟩ => .inr ⟨i, (t i).addressParent e⟩
  | .inr (.inl ⟨v, _, _⟩) => .inr v
  | .inr (.inr ⟨a, _, _⟩) => .inl a

/-- The second end of each edge. -/
def apexForestRight {k n : ℕ} (t : Fin n → OrderedTree)
    (f : Fin n → List ℕ → Fin k → ℕ) (c : Fin k × Fin k → ℕ) :
    ApexForestEdge t f c → Fin k ⊕ ForestVertex t
  | .inl ⟨i, e⟩ => .inr ⟨i, (t i).addressChild e⟩
  | .inr (.inl ⟨_, a, _⟩) => .inl a
  | .inr (.inr ⟨_, b, _⟩) => .inl b

/-- Construct the multigraph from the forest and all attachment and core
edge multiplicities. No bound on these multiplicities is imposed. -/
def apexForest {k n : ℕ} (t : Fin n → OrderedTree)
    (f : Fin n → List ℕ → Fin k → ℕ) (c : Fin k × Fin k → ℕ) :=
  graphOfEnds (apexForestLeft t f c) (apexForestRight t f c)

end GraphMinor.Mader
