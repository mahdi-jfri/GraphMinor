module

public import GraphMinor.GM13.Defs

/-!
# Models with maps on actual edges

The edge-indexed model is equivalent to the definition in Graph Minors XIII,
Section 2, page 68. In particular, the separate loop and non-loop conditions
imply that every model edge lies outside every branch subgraph.
-/

public section

namespace GraphMinor.GM13

open Graph Set Function GraphMinor.Surface

universe u v

/-- With a nonempty target edge type, extending and restricting edge maps
preserves existence of a model. -/
theorem hasGraphModel_iff_exists_isGraphModel {α : Type u} {β : Type v}
    {α' β' : Type*} [Nonempty β] (H : Graph α' β') (G : Graph α β) :
    HasGraphModel H G ↔
      ∃ (a : α' → Graph α β) (b : β' → β), IsGraphModel H G a b := by
  exact ⟨HasGraphModel.exists_isGraphModel, hasGraphModel_of_exists_isGraphModel⟩

/-- Clause (i) of the model definition in XIII, page 68: no model edge belongs
 to any branch subgraph. For a non-loop edge, its two ends lie in disjoint
branches, so they cannot both belong to a third branch. -/
theorem IsEdgeGraphModel.edge_not_mem {α : Type u} {β : Type v} {α' β' : Type*}
    {H : Graph α' β'} {G : Graph α β} {a : α' → Graph α β} {b : E(H) → β}
    (h : IsEdgeGraphModel H G a b) {w : α'} (hw : w ∈ V(H)) (e : E(H)) :
    b e ∉ E(a w) := by
  intro he
  obtain ⟨u, v, hl⟩ := exists_isLink_of_mem_edgeSet e.property
  by_cases huv : u = v
  · subst v
    by_cases huw : u = w
    · subst w
      exact (h.loop_ends hl).1 he
    · obtain ⟨x, hx, y, hy, hxy⟩ := (h.loop_ends hl).2
      have hxy' : (a w).IsLink (b e) x y :=
        ((h.sub_of_mem hw).isLink_iff he).mpr hxy
      exact Set.disjoint_left.mp (h.disjoint_of_ne hl.left_mem hw huw) hx hxy'.left_mem
  · obtain ⟨x, hx, y, hy, hxy⟩ := h.link_ends_of_ne hl huv
    have hxy' : (a w).IsLink (b e) x y :=
      ((h.sub_of_mem hw).isLink_iff he).mpr hxy
    by_cases huw : u = w
    · subst w
      exact Set.disjoint_left.mp (h.disjoint_of_ne hl.left_mem hl.right_mem huv)
        hxy'.right_mem hy
    · exact Set.disjoint_left.mp (h.disjoint_of_ne hl.left_mem hw huw) hx hxy'.left_mem

/-- The model conditions are exactly clauses (i) and (ii) of XIII, Section 2,
page 68. The maps are indexed by actual edges, so an edgeless source needs
no edge name in the target. -/
theorem isEdgeGraphModel_iff {α : Type u} {β : Type v} {α' β' : Type*}
    {H : Graph α' β'} {G : Graph α β} (a : α' → Graph α β) (b : E(H) → β) :
    IsEdgeGraphModel H G a b ↔
      (∀ v ∈ V(H), a v ≤ G) ∧
      (∀ v ∈ V(H), V(a v).Nonempty) ∧
      (∀ v ∈ V(H), ∀ x ∈ V(a v), ∀ y ∈ V(a v), Nonempty (GraphWalk (a v) x y)) ∧
      (∀ u ∈ V(H), ∀ v ∈ V(H), u ≠ v → Disjoint V(a u) V(a v)) ∧
      (∀ e : E(H), b e ∈ E(G)) ∧ Injective b ∧
      (∀ v ∈ V(H), ∀ e : E(H), b e ∉ E(a v)) ∧
      (∀ (e : E(H)) u v, H.IsLink e.val u v →
        ∃ x ∈ V(a u), ∃ y ∈ V(a v), G.IsLink (b e) x y) := by
  constructor
  · intro h
    refine ⟨fun _ hv => h.sub_of_mem hv, fun _ hv => h.nonempty_of_mem hv,
      fun _ hv => h.connected_of_mem hv, fun _ hu _ hv => h.disjoint_of_ne hu hv,
      fun e => h.edge_mem e.property, h.eMap_injOn,
      fun _ hv e => h.edge_not_mem hv e, ?_⟩
    intro e u v hl
    by_cases huv : u = v
    · subst v
      exact (h.loop_ends hl).2
    · exact h.link_ends_of_ne hl huv
  · rintro ⟨hs, hn, hc, hd, he, hi, ho, hl⟩
    refine ⟨fun {v} hv => hs v hv, fun {v} hv => hn v hv,
      fun {v} hv => hc v hv, fun {u v} hu hv => hd u hu v hv,
      fun {e} he' => he ⟨e, he'⟩, ?_, ?_, hi⟩
    · intro e u v hlink _
      exact hl ⟨e, hlink.edge_mem⟩ u v hlink
    · intro e u hlink
      exact ⟨ho u hlink.left_mem ⟨e, hlink.edge_mem⟩,
        hl ⟨e, hlink.edge_mem⟩ u u hlink⟩

end GraphMinor.GM13
