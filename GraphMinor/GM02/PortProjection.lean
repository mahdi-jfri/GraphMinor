module

public import GraphMinor.GM02.PortPathVertices
import GraphMinor.GM02.FeasiblePathSupport

/-!
# Projecting split incidences to original host edges

Old vertices keep their original names and terminals carry their pattern
endpoint names. An edge vertex has no vertex label. Two consecutive
incidences through an edge vertex therefore identify a particular host
edge. On a feasible path their two original vertex labels differ: a
branch endpoint cannot be an old non-branch vertex, and the two ends of
a pattern loop cannot choose the same incident edge. This prevents the
false repeated-edge walks from the printed (4.5).
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

/-- The original vertex label of an old vertex or a terminal; edge vertices are skipped. -/
def portLabel {α : Type u} {β : Type v} {k : ℕ} (ends : Fin k → α × α) :
    PortVertex α β k → Option α
  | Sum.inl (Sum.inl a) => some a
  | Sum.inl (Sum.inr _) => none
  | Sum.inr p => some (if p.2 then (ends p.1).2 else (ends p.1).1)

/-- An old split vertex is retained precisely when it is not a pattern branch vertex. -/
theorem portOld_mem_vertexSet_iff {α : Type u} {β : Type v} (G H : Graph α β) (k : ℕ) (a : α) :
    portOld a ∈ portVertexSet G H k ↔ a ∈ V(G) \ V(H) := by
  simp [portVertexSet, portOld, portEdge, portTerminal]

/-- A projected vertex next to an edge vertex is incident with that exact original edge. -/
theorem portLabel_inc_of_adj {α : Type u} {β : Type v} {k : ℕ} (G H : Graph α β)
    {ends : Fin k → α × α} (choice : PortChoice G ends) (a : PortVertex α β k) (e : β) (x : α)
    (hadj : (portGraph G H choice).Adj a (portEdge e)) (hlabel : portLabel ends a = some x) : G.Inc e x := by
  have hr := (portGraph_adj_iff G H choice a (portEdge e)).1 hadj |>.2.2
  rcases a with (a | f) | p
  · have heq : a = x := Option.some.inj hlabel
    exact heq ▸ hr
  · cases hlabel
  · have heq : (if p.2 then (ends p.1).2 else (ends p.1).1) = x := Option.some.inj hlabel
    have hi := choice.incident p
    change (choice.edge p).val = e at hr
    rw [hr, heq] at hi
    exact hi

private theorem isLink_of_inc_ne {α : Type u} {β : Type v} {G : Graph α β} {e : β} {a b : α}
    (ha : G.Inc e a) (hb : G.Inc e b) (hne : a ≠ b) : G.IsLink e a b := by
  obtain ⟨c, hac⟩ := ha
  have hbc : b = c := hb.eq_of_isLink_of_ne_left hac hne.symm
  exact hbc.symm ▸ hac

/-- Two incidences with different original vertex labels recover a genuine host link. -/
theorem port_two_step_isLink {α : Type u} {β : Type v} {k : ℕ} (G H : Graph α β)
    {ends : Fin k → α × α} (choice : PortChoice G ends) (a b : PortVertex α β k) (e : β) (x y : α)
    (ha : (portGraph G H choice).Adj a (portEdge e)) (hb : (portGraph G H choice).Adj (portEdge e) b)
    (hax : portLabel ends a = some x) (hby : portLabel ends b = some y) (hne : x ≠ y) : G.IsLink e x y :=
  isLink_of_inc_ne (portLabel_inc_of_adj G H choice a e x ha hax)
    (portLabel_inc_of_adj G H choice b e y hb.symm hby) hne

end GraphMinor.GM02
