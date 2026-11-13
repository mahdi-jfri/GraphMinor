module

public import GraphMinor.GM08.Section17RootLeaves

/-!
# Connected branches containing a new root leaf

A new leaf has just its old root as a neighbour. If a connected
subgraph contains that leaf and any old vertex, its last walk step
into the leaf shows that it also contains the old root. Consequently,
collapsing the new leaves in such a branch gives exactly its old
vertices. This preserves disjoint branch images in VIII (17.2).
-/

public section

namespace GraphMinor.GM08

open Set Graph

universe u v

/-- Collapse each new root leaf to its old vertex. -/
@[expose] def rootLeafCollapse {α : Type u} : α ⊕ α → α := Sum.elim id id

/-- The only neighbour of a new leaf is its old root. -/
theorem eq_old_root_of_adj_new_leaf {α : Type u} {β : Type v}
    (X : Graft α β) {z : α ⊕ α} {x : α}
    (h : (rootLeafGraph X).Adj z (Sum.inr x)) : z = Sum.inl x := by
  obtain ⟨e, he⟩ := h
  cases e <;> cases z <;> simp only [rootLeafGraph, rootLeafLink] at he
  exact congrArg Sum.inl (he.2.1.trans he.2.2.symm)

/-- A connected subgraph containing an old vertex and a new leaf also
contains the old root adjacent to that leaf. -/
theorem old_root_mem_of_connected_with_leaf {α : Type u} {β : Type v}
    (X : Graft α β) {K : Graph (α ⊕ α) (β ⊕ α)} (hK : K ≤ rootLeafGraph X)
    (hconn : GraphConnected K) (hold : ∃ y : α, Sum.inl y ∈ V(K))
    {x : α} (hx : Sum.inr x ∈ V(K)) : Sum.inl x ∈ V(K) := by
  obtain ⟨y, hy⟩ := hold
  have hwalk := hconn.2 (Sum.inl y) hy (Sum.inr x) hx
  rcases hwalk.cases_tail with heq | ⟨z, _, hz⟩
  · cases heq
  · obtain ⟨e, he⟩ := hz
    have hzeq := eq_old_root_of_adj_new_leaf X ⟨e, hK.isLink_mono he⟩
    exact hzeq ▸ he.left_mem

/-- On a connected subgraph containing an old vertex, the image of
collapsing leaves is exactly its set of old vertices. Thus collapsing
leaves cannot identify two disjoint such branches. -/
theorem collapse_image_eq_old_vertices {α : Type u} {β : Type v}
    (X : Graft α β) {K : Graph (α ⊕ α) (β ⊕ α)} (hK : K ≤ rootLeafGraph X)
    (hconn : GraphConnected K) (hold : ∃ y : α, Sum.inl y ∈ V(K)) :
    rootLeafCollapse '' V(K) = Sum.inl ⁻¹' V(K) := by
  apply subset_antisymm
  · rintro x ⟨z, hz, rfl⟩
    cases z with
    | inl x => exact hz
    | inr x => exact old_root_mem_of_connected_with_leaf X hK hconn hold hz
  · intro x hx
    exact ⟨Sum.inl x, hx, rfl⟩

end GraphMinor.GM08
