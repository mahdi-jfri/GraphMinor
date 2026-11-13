module

public import GraphMinor.GM02.PortLink

/-!
# Alternation of vertex labels and edge names

In the corrected split graph, every neighbor of a vertex with an
original vertex label is an edge vertex. Every neighbor of an edge
vertex has an original vertex label. Thus a split path can be read two
steps at a time, retaining the name of each host edge it uses.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

/-- The original edge name recorded by an edge vertex. -/
def portEdgeLabel {α : Type u} {β : Type v} {k : ℕ} : PortVertex α β k → Option β
  | Sum.inl (Sum.inr e) => some e
  | _ => none

/-- A neighbor of a vertex carrying an original vertex label is an edge vertex. -/
theorem portAdj_exists_edge {α : Type u} {β : Type v} {k : ℕ} (G H : Graph α β)
    {ends : Fin k → α × α} (choice : PortChoice G ends) (a b : PortVertex α β k) (x : α)
    (ha : portLabel ends a = some x) (hab : (portGraph G H choice).Adj a b) :
    ∃ e, b = portEdge e := by
  have hr := (portGraph_adj_iff G H choice a b).1 hab |>.2.2
  rcases a with (a | e) | p <;> rcases b with (b | f) | q
  · exact False.elim hr
  · exact ⟨f, rfl⟩
  · exact False.elim hr
  · cases ha
  · cases ha
  · cases ha
  · exact False.elim hr
  · exact ⟨f, rfl⟩
  · exact False.elim hr

/-- Every neighbor of an edge vertex has an original vertex label. -/
theorem portEdge_adj_exists_label {α : Type u} {β : Type v} {k : ℕ} (G H : Graph α β)
    {ends : Fin k → α × α} (choice : PortChoice G ends) (e : β) (a : PortVertex α β k)
    (ha : (portGraph G H choice).Adj (portEdge e) a) : ∃ x, portLabel ends a = some x := by
  have hr := (portGraph_adj_iff G H choice (portEdge e) a).1 ha |>.2.2
  rcases a with (a | f) | p
  · exact ⟨a, rfl⟩
  · exact False.elim hr
  · exact ⟨_, rfl⟩

/-- A retained labeled vertex projects to a host vertex when pattern endpoints do. -/
theorem portLabel_mem_host {α : Type u} {β : Type v} {k : ℕ} (G H : Graph α β)
    {ends : Fin k → α × α} (choice : PortChoice G ends)
    (hVH : V(H) ⊆ V(G)) (hends : ∀ i, (ends i).1 ∈ V(H) ∧ (ends i).2 ∈ V(H))
    (a : PortVertex α β k) (x : α) (ha : a ∈ V(portGraph G H choice))
    (hx : portLabel ends a = some x) : x ∈ V(G) := by
  rcases a with (a | e) | p
  · have hm := (portOld_mem_vertexSet_iff G H k a).1 ha
    exact (Option.some.inj hx) ▸ hm.1
  · cases hx
  · have hm : (if p.2 then (ends p.1).2 else (ends p.1).1) ∈ V(G) := by
      cases p.2 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
        first | exact hVH (hends p.1).1 | exact hVH (hends p.1).2
    exact (Option.some.inj hx) ▸ hm

end GraphMinor.GM02
