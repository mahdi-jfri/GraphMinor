module

public import GraphMinor.GM02.PortEdgeResources
import GraphMinor.GM02.FeasiblePathSupport

/-!
# Vertices on a feasible split path

A path of one prescribed pair cannot visit a terminal of another pair,
since that terminal lies on the other path. Its vertices are therefore
old non-branch vertices, original-edge vertices, or its own two ends.
These facts allow projection back to the original host graph without
introducing extra branch vertices on an edge route in (4.6).
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

/-- Each split terminal is an endpoint of its indexed prescribed pair. -/
theorem portTerminal_mem_pair {α : Type u} {β : Type v} {k : ℕ} (G H : Graph α β)
    {ends : Fin k → α × α} (choice : PortChoice G ends) (i : Fin k) (side : Bool) :
    portTerminal (i, side) ∈ (portPair G H choice i).val := by
  cases side <;> simp [portPair, Sym2.mem_iff]

/-- A terminal occurring in a disjoint path family belongs to that path's own indexed pair. -/
theorem portTerminal_index_eq_of_mem_family {α : Type u} {β : Type v} {k : ℕ} (G H : Graph α β)
    {ends : Fin k → α × α} (choice : PortChoice G ends)
    (P : ∀ p : {p // p ∈ (portTermination G H choice).pairs}, PairPath (pathGraph (portGraph G H choice)) p.val)
    (hP : ∀ p q, p ≠ q → Disjoint (P p).vertices (P q).vertices)
    (i : Fin k) (p : Fin k × Bool)
    (hmem : portTerminal p ∈ (P (portPair G H choice i)).vertices) : p.1 = i := by
  have hp := portTerminal_mem_pair G H choice p.1 p.2
  have he := endpoint_pair_eq_of_mem_family (portTermination G H choice) P hP hmem hp
  exact (portPair_injective G H choice he).symm

/-- Every vertex on an indexed feasible path is an allowed old vertex, an edge vertex, or one of its own ends. -/
theorem portPath_vertex_cases {α : Type u} {β : Type v} {k : ℕ} (G H : Graph α β)
    {ends : Fin k → α × α} (choice : PortChoice G ends)
    (P : ∀ p : {p // p ∈ (portTermination G H choice).pairs}, PairPath (pathGraph (portGraph G H choice)) p.val)
    (hP : ∀ p q, p ≠ q → Disjoint (P p).vertices (P q).vertices)
    (i : Fin k) (a : PortVertex α β k) (ha : a ∈ (P (portPair G H choice i)).vertices) :
    (∃ y ∈ V(G) \ V(H), a = portOld y) ∨ (∃ e ∈ E(G), a = portEdge e) ∨
      a = portTerminal (i, false) ∨ a = portTerminal (i, true) := by
  have hdiag := (portTermination G H choice).not_diag _ (portPair G H choice i).property
  have hv := (P (portPair G H choice i)).vertices_subset hdiag ha
  change a ∈ portVertexSet G H k at hv
  rcases hv with ⟨y, hy, rfl⟩ | ⟨e, he, rfl⟩ | ⟨p, rfl⟩
  · exact Or.inl ⟨y, hy, rfl⟩
  · exact Or.inr (Or.inl ⟨e, he, rfl⟩)
  · have hp := portTerminal_index_eq_of_mem_family G H choice P hP i p ha
    rcases p with ⟨j, side⟩
    dsimp only at hp
    subst j
    cases side with
    | false => exact Or.inr (Or.inr (Or.inl rfl))
    | true => exact Or.inr (Or.inr (Or.inr rfl))

end GraphMinor.GM02
