module

public import GraphMinor.GM02.SuppressMinorModel

/-!
# Edges remain inside branches after suppression

If each non-representing edge lies within a branch, suppressing a vertex
whose two incident edges are non-representing preserves this condition.
The two edges meet at the removed vertex, so their branches agree by
disjointness. The new edge therefore has both ends in that same branch.
-/

public section
namespace GraphMinor.GM02
open Graph Set
universe u v u' v'

/-- Suppression of two internal branch edges leaves every non-representing
edge internal to a surviving branch. The branch sets lose only the removed
vertex. -/
theorem internal_edges_after_suppression
    {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {G : Graph α β} {H : Graph α' β'} {ηv : α' → Set α} {ηe : β' → β}
    (hm : IsMinorModel H G ηv ηe) (d : SuppressionData G)
    (hfirst : d.first ∉ ηe '' E(H)) (hsecond : d.second ∉ ηe '' E(H))
    (hinternal : ∀ e ∈ E(G), e ∉ ηe '' E(H) →
      ∃ u ∈ V(H), ∀ x, G.Inc e x → x ∈ ηv u) :
    ∀ e ∈ E(d.result), e ∉ ηe '' E(H) →
      ∃ u ∈ V(H), ∀ x, d.result.Inc e x → x ∈ ηv u \ {d.vertex} := by
  intro e he hnot
  rcases d.edge_cases he with rfl | ⟨heG, he1, he2⟩
  · obtain ⟨u, hu, hends⟩ := hinternal d.first d.first_link.edge_mem hfirst
    obtain ⟨w, hw, hends'⟩ := hinternal d.second d.second_link.edge_mem hsecond
    have huw : u = w := by
      by_contra hn
      exact Set.disjoint_left.1 (hm.vertex_disjoint u hu w hw hn)
        (hends d.vertex d.first_link.inc_left) (hends' d.vertex d.second_link.inc_left)
    have hnew : d.result.IsLink d.fresh d.left d.right := Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
    refine ⟨u, hu, ?_⟩
    intro x hx
    refine ⟨?_, hx.vertex_mem.2⟩
    rcases hx.eq_or_eq_of_isLink hnew with rfl | rfl
    · exact hends d.left d.first_link.inc_right
    · exact huw ▸ hends' d.right d.second_link.inc_right
  · obtain ⟨u, hu, hends⟩ := hinternal e heG hnot
    refine ⟨u, hu, ?_⟩
    intro x hx
    refine ⟨?_, hx.vertex_mem.2⟩
    rcases (d.inc_iff e x).1 hx with ⟨hf, _⟩ | ⟨hxG, _, _⟩
    · exact (d.retained_not_fresh heG he1 he2 hf).elim
    · exact hends x hxG

end GraphMinor.GM02
