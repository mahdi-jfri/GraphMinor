module

public import GraphMinor.Minor.Model

/-!
# Attachment vertices of a minor model

The branch trees used in II (4.8) must keep both ends of each representing
edge. The incidence and loop conditions of a minor model ensure that every
such end lies in a branch. Distinct branches then identify which branch
contains it. This includes both ends of a representing edge for a loop.
-/

public section

namespace GraphMinor.GM02

open Graph Set

universe u v u' v'

/-- Every end of a representing edge is in a branch set. For a loop this
uses the loop condition of a minor model. For a non-loop, the two target
ends give two disjoint branch sets, exhausting the two ends of the original
edge. -/
theorem IsMinorModel.edge_ends_covered
    {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {G : Graph α β} {H : Graph α' β'} {ηv : α' → Set α} {ηe : β' → β}
    (hm : IsMinorModel H G ηv ηe) {e : β'} (he : e ∈ E(H)) {x : α}
    (hx : G.Inc (ηe e) x) : ∃ u ∈ V(H), x ∈ ηv u := by
  obtain ⟨u, v, huv⟩ := Graph.exists_isLink_of_mem_edgeSet he
  by_cases huv' : u = v
  · subst v
    have hloop : H.IsLoopAt e u := huv
    exact ⟨u, huv.left_mem, ((hm.isLoopAt_iff u huv.left_mem e he).1 hloop) x hx⟩
  · obtain ⟨a, ha, hae⟩ := (hm.inc_iff u huv.left_mem e he).1 huv.inc_left
    obtain ⟨b, hb, hbe⟩ := (hm.inc_iff v huv.right_mem e he).1 huv.inc_right
    have hab : a ≠ b := by
      intro h
      exact Set.disjoint_left.1 (hm.vertex_disjoint u huv.left_mem v huv.right_mem huv')
        ha (h ▸ hb)
    rcases hx.eq_or_eq_or_eq hae hbe with rfl | rfl | heq
    · exact ⟨u, huv.left_mem, ha⟩
    · exact ⟨v, huv.right_mem, hb⟩
    · exact (hab heq).elim

end GraphMinor.GM02
