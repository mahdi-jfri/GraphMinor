module

public import GraphMinor.GM04.Patchwork.Defs
public import GraphMinor.GM06.Section3Basic
public import GraphMinor.GM01.Basic

/-!
# Components of a realization viewed as a multigraph

The realization in IV (9.2) is first a simple subgraph. Its multigraph
has the same walks and the same vertex sets of components. These facts
let the spanning-forest and drawing constructions preserve the expansion's
vertex sets.
-/

public section

namespace GraphMinor.GM04

open Set Surface Graph

universe u

private theorem walk_of_reachable {α : Type u} (H : (⊤ : SimpleGraph α).Subgraph)
    {x y : H.verts} (h : H.coe.Reachable x y) :
    Nonempty (GraphWalk (GM01.toGraph H) x.val y.val) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact ⟨.nil x.property⟩
  | @tail z y _ hzy ih =>
    obtain ⟨W⟩ := ih
    have he : (GM01.toGraph H).IsLink s(z.val, y.val) z.val y.val := ⟨rfl, hzy⟩
    exact ⟨W.append (.cons he (.nil y.property))⟩

private theorem reachable_of_walk {α : Type u} (H : (⊤ : SimpleGraph α).Subgraph)
    {x y : α} (W : GraphWalk (GM01.toGraph H) x y)
    (hx : x ∈ H.verts) (hy : y ∈ H.verts) :
    H.coe.Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  induction W with
  | nil _ => exact SimpleGraph.Reachable.refl _
  | @cons x z y e he rest ih =>
    have hz : z ∈ H.verts := H.edge_vert he.2.symm
    have hadj : H.coe.Adj ⟨x, hx⟩ ⟨z, hz⟩ := he.2
    exact hadj.reachable.trans (ih hz hy)

/-- Reading a simple realization as a multigraph preserves its component
vertex sets, as needed in IV (9.2), page 254. -/
theorem reachSet_toGraph_eq_componentVerts {α : Type u}
    (H : (⊤ : SimpleGraph α).Subgraph) (x : H.verts) :
    GM06.reachSet (GM01.toGraph H) x = componentVerts H x := by
  ext y
  constructor
  · rintro ⟨hy, ⟨W⟩⟩
    exact ⟨hy, reachable_of_walk H W x.property hy⟩
  · rintro ⟨hy, hreach⟩
    exact ⟨hy, walk_of_reachable H hreach⟩

/-- Two graph constructions with the same vertices and the same walk
connections have the same component vertex sets. -/
theorem reachSet_eq_of_walk_iff {α β γ : Type*} {G : Graph α β} {H : Graph α γ}
    (hV : V(G) = V(H))
    (hwalk : ∀ x y, Nonempty (GraphWalk G x y) ↔ Nonempty (GraphWalk H x y)) (x : α) :
    GM06.reachSet G x = GM06.reachSet H x := by
  ext y
  change (y ∈ V(G) ∧ Nonempty (GraphWalk G x y)) ↔
    y ∈ V(H) ∧ Nonempty (GraphWalk H x y)
  rw [hV, hwalk x y]

end GraphMinor.GM04
