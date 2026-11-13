module

public import GraphMinor.GM02.PortTermination

/-!
# Vertices reserved for one projected split path

Reserve the copies of one route's inner vertices, its host-edge vertices,
and its own two terminals. Disjoint host interiors and edge sets make
these reserved sets disjoint for different pattern edges. They are
subsets of the corrected split graph's vertex set.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

/-- The vertices available to the split path for one edge-labelled host route. -/
def portRouteVertices {α : Type u} {β : Type v} {k : ℕ}
    (inner : List α) (edges : List β) (i : Fin k) : Set (PortVertex α β k) :=
  portOld '' {y | y ∈ inner} ∪ (portEdge '' {e | e ∈ edges} ∪
    {portTerminal (i, false), portTerminal (i, true)})

/-- Old vertices in a reserved set are exactly the route's interior vertices. -/
theorem portOld_mem_routeVertices {α : Type u} {β : Type v} {k : ℕ}
    (inner : List α) (edges : List β) (i : Fin k) (y : α) :
    portOld y ∈ portRouteVertices inner edges i ↔ y ∈ inner := by
  simp [portRouteVertices, portOld, portEdge, portTerminal]

/-- Edge vertices in a reserved set are exactly the route's traversed host edges. -/
theorem portEdge_mem_routeVertices {α : Type u} {β : Type v} {k : ℕ}
    (inner : List α) (edges : List β) (i : Fin k) (e : β) :
    portEdge e ∈ portRouteVertices inner edges i ↔ e ∈ edges := by
  simp [portRouteVertices, portOld, portEdge, portTerminal]

/-- A reserved set contains exactly its own indexed terminals. -/
theorem portTerminal_mem_routeVertices {α : Type u} {β : Type v} {k : ℕ}
    (inner : List α) (edges : List β) (i : Fin k) (p : Fin k × Bool) :
    portTerminal p ∈ portRouteVertices inner edges i ↔ p.1 = i := by
  rcases p with ⟨j, side⟩
  cases side <;> simp [portRouteVertices, portOld, portEdge, portTerminal]

/-- The reserved sets lie in the split graph when the route interiors avoid branch vertices. -/
theorem portRouteVertices_subset {α : Type u} {β : Type v} {k : ℕ} (G H : Graph α β)
    (inner : List α) (edges : List β) (i : Fin k)
    (hinner : ∀ y ∈ inner, y ∈ V(G) \ V(H)) (hedges : ∀ e ∈ edges, e ∈ E(G)) :
    portRouteVertices inner edges i ⊆ portVertexSet G H k := by
  rintro a (⟨y, hy, rfl⟩ | ⟨e, he, rfl⟩ | ha)
  · exact Or.inl ⟨y, hinner y hy, rfl⟩
  · exact Or.inr (Or.inl ⟨e, hedges e he, rfl⟩)
  · rcases ha with h | h
    · exact Or.inr (Or.inr ⟨(i, false), h.symm⟩)
    · exact Or.inr (Or.inr ⟨(i, true), (Set.mem_singleton_iff.1 h).symm⟩)

/-- Different route reservations are disjoint when the host interiors and host-edge sets are disjoint. -/
theorem portRouteVertices_disjoint {α : Type u} {β : Type v} {k : ℕ}
    (inner : Fin k → List α) (edges : Fin k → List β) (i j : Fin k) (hij : i ≠ j)
    (hdV : Disjoint {y | y ∈ inner i} {y | y ∈ inner j})
    (hdE : Disjoint {e | e ∈ edges i} {e | e ∈ edges j}) :
    Disjoint (portRouteVertices (inner i) (edges i) i) (portRouteVertices (inner j) (edges j) j) := by
  rw [Set.disjoint_left]
  intro a hai haj
  rcases a with (y | e) | p
  · exact Set.disjoint_left.1 hdV ((portOld_mem_routeVertices _ _ _ _).1 hai)
      ((portOld_mem_routeVertices _ _ _ _).1 haj)
  · exact Set.disjoint_left.1 hdE ((portEdge_mem_routeVertices _ _ _ _).1 hai)
      ((portEdge_mem_routeVertices _ _ _ _).1 haj)
  · exact hij (((portTerminal_mem_routeVertices _ _ _ _).1 hai).symm.trans
      ((portTerminal_mem_routeVertices _ _ _ _).1 haj))

end GraphMinor.GM02
