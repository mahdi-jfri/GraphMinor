module

public import GraphMinor.GM01.PathWidthComponents
public import GraphMinor.Minor.Model

/-!
# Connectivity of a component on the ambient vertex type

Graph Minors I, page 57, applies the preceding width bound to each
component of a layer after choosing a root. The component vertex set
is reachability from a chosen vertex. Every path witnessing that
reachability remains in the component, so the induced component is
connected and contains the chosen vertex.
-/

public section

namespace GraphMinor.GM01

open Set Graph Relation

/-- A vertex belongs to its component, as used to root the components
in the reduction on page 57 of GM01. -/
theorem mem_componentVertices_self {α β : Type*} (G : Graph α β) (v : V(G)) :
    v.val ∈ componentVertices G v := ⟨v.property, .refl⟩

/-- The induced graph on a component is connected. All intermediate
vertices of its defining reachability paths remain in that component. -/
theorem componentVertices_connected {α β : Type*} (G : Graph α β) (v : V(G)) :
    GraphConnected (G.induce (componentVertices G v)) := by
  have hValid : ∀ x, ReflTransGen G.Adj v.val x → x ∈ V(G) := by
    intro x h
    induction h with
    | refl => exact v.property
    | tail _ h _ => obtain ⟨e, he⟩ := h; exact he.right_mem
  have hLift : ∀ x ∈ componentVertices G v,
      ReflTransGen (G.induce (componentVertices G v)).Adj v.val x := by
    intro x hx
    induction hx.2 with
    | refl => exact .refl
    | @tail b c hab hbc ih =>
      obtain ⟨e, he⟩ := hbc
      exact (ih ⟨hValid b hab, hab⟩).tail ⟨e, he, ⟨hValid b hab, hab⟩, ⟨he.right_mem, hab.tail ⟨e, he⟩⟩⟩
  refine ⟨⟨v.val, mem_componentVertices_self G v⟩, ?_⟩
  intro x hx y hy
  exact (Std.Symm.symm _ _ (hLift x hx)).trans (hLift y hy)

end GraphMinor.GM01
