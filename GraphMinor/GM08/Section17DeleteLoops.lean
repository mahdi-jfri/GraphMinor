module

public import GraphMinor.GM08.Defs

/-!
# Removing unused loops from a simulation host

Deleting loops does not change connectivity. Thus host loops unused by
the selected target edges may be deleted from a simulation, with the
same branches and selected edges. After collapsing collar leaves in
VIII (17.2), all added edges are loops, and this removes them.
-/

public section

namespace GraphMinor.GM08

open Set Graph

universe u v u' v'

private theorem connected_delete_loops {α : Type u} {β : Type v}
    {K : Graph α β} (hconn : GraphConnected K) (S : Set β)
    (hloop : ∀ e ∈ S, ∀ x y, K.IsLink e x y → x = y) :
    GraphConnected (K.deleteEdges S) := by
  refine ⟨hconn.1, ?_⟩
  intro x hx y hy
  have hwalk := hconn.2 x hx y hy
  clear hx hy
  induction hwalk with
  | refl => exact .refl
  | @tail z w hwalk hadj ih =>
    obtain ⟨e, he⟩ := hadj
    by_cases heS : e ∈ S
    · exact hloop e heS z w he ▸ ih
    · exact ih.tail ⟨e, he, heS⟩

/-- Unused host edges whose ends coincide can be deleted without
changing a simulation. This removes the collapsed collar edges in
VIII (17.2), page 284. -/
theorem IsGraphSimulation.delete_host_loops
    {α : Type u} {β : Type v} {γ : Type u'} {δ : Type v'}
    {H : Graph γ δ} {G : Graph α β} {ηv : γ → Set α} {ηe : δ → β}
    (h : IsGraphSimulation H G ηv ηe) (S : Set β)
    (hunused : ∀ e ∈ E(H), ηe e ∉ S)
    (hloop : ∀ e ∈ S, ∀ x y, G.IsLink e x y → x = y) :
    IsGraphSimulation H (G.deleteEdges S) ηv ηe := by
  refine {
    vertex_nonempty := h.vertex_nonempty
    vertex_subset := h.vertex_subset
    edge_mem := fun e he => ⟨h.edge_mem e he, hunused e he⟩
    vertex_disjoint := h.vertex_disjoint
    edge_injOn := h.edge_injOn
    inc_iff := ?_
    isLoopAt_iff := ?_
    connected := ?_ }
  · intro a ha e he
    simpa only [Graph.deleteEdges_inc, hunused e he, not_false_eq_true, and_true] using h.inc_iff a ha e he
  · intro a ha e he
    simpa only [Graph.deleteEdges_inc, hunused e he, not_false_eq_true, and_true] using h.isLoopAt_iff a ha e he
  · intro a ha
    obtain ⟨K, hKG, hKV, hconn⟩ := h.connected a ha
    have hKG' := hKG.trans Graph.deleteEdges_le
    have hconn' := connected_delete_loops hconn S
      (fun e he x y hxy => hloop e he x y (hKG'.isLink_mono hxy))
    refine ⟨K.deleteEdges S, ?_, hKV, hconn'⟩
    have hm := Graph.deleteEdges_mono_left hKG S
    have heq : (G.deleteEdges (ηe '' E(H))).deleteEdges S =
        (G.deleteEdges S).deleteEdges (ηe '' E(H)) := by
      rw [Graph.deleteEdges_deleteEdges, Graph.deleteEdges_deleteEdges, union_comm]
    exact heq ▸ hm

end GraphMinor.GM08
