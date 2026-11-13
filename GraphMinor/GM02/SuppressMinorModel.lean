module

public import GraphMinor.GM02.SuppressionMap

/-!
# Suppressing an unmarked vertex of a minor model

Inside a branch of a minor model, a degree-two vertex that is not an end
of a representing edge may be suppressed. Remove that vertex from the
branch sets and keep the representing edges. Their incidence is unchanged.
For branch connectedness, map walks through the suppression. The removed
vertex maps to its first other end, which lies in the same branch.
-/

public section

namespace GraphMinor.GM02

open Graph Set Classical

universe u v u' v'

/-- A suppression inside a branch preserves a minor model if neither
removed edge nor the replacement edge represents a target edge. The first
other end must belong to each branch containing the removed vertex. -/
theorem IsMinorModel.suppress_of_same_branch
    {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {G : Graph α β} {H : Graph α' β'} {ηv : α' → Set α} {ηe : β' → β}
    (hm : IsMinorModel H G ηv ηe) (d : SuppressionData G)
    (hfirst : d.first ∉ ηe '' E(H)) (hsecond : d.second ∉ ηe '' E(H))
    (hfresh : d.fresh ∉ ηe '' E(H))
    (hsame : ∀ u ∈ V(H), d.vertex ∈ ηv u → d.left ∈ ηv u) :
    IsMinorModel H d.result (fun u => ηv u \ {d.vertex}) ηe := by
  have hret : ∀ e ∈ E(H), ηe e ∈ E(G) ∧ ηe e ≠ d.first ∧
      ηe e ≠ d.second ∧ ηe e ≠ d.fresh := by
    intro e he
    have hmeme : ηe e ∈ ηe '' E(H) := ⟨e, he, rfl⟩
    exact ⟨hm.edge_mem e he, fun h => hfirst (h ▸ hmeme),
      fun h => hsecond (h ▸ hmeme), fun h => hfresh (h ▸ hmeme)⟩
  have hinc : ∀ e ∈ E(H), ∀ x, d.result.Inc (ηe e) x ↔ G.Inc (ηe e) x := by
    intro e he x
    obtain ⟨_, h1, h2, hf⟩ := hret e he
    rw [d.inc_iff]
    exact ⟨fun h => h.elim (fun h => (hf h.1).elim) And.left,
      fun h => Or.inr ⟨h, h1, h2⟩⟩
  have havoid : ∀ e ∈ E(H), ∀ x, G.Inc (ηe e) x → x ≠ d.vertex := by
    intro e he x hx h
    exact d.retained_not_inc (hret e he).2.1 (hret e he).2.2.1 (h ▸ hx)
  have himage : ∀ u ∈ V(H), suppressionVertexMap d '' ηv u = ηv u \ {d.vertex} := by
    intro u hu
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      by_cases hyv : y = d.vertex
      · simp only [suppressionVertexMap, hyv, ↓reduceIte]
        exact ⟨hsame u hu (hyv ▸ hy), d.vertex_ne_left.symm⟩
      · simp only [suppressionVertexMap, hyv, ↓reduceIte]
        exact ⟨hy, hyv⟩
    · intro hx
      have hxv : x ≠ d.vertex := hx.2
      exact ⟨x, hx.1, by simp only [suppressionVertexMap, hxv, ↓reduceIte]⟩
  refine ⟨?_, ?_, ?_, ?_, hm.edge_injOn, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨x, hx⟩ := hm.vertex_nonempty u hu
    by_cases hxv : x = d.vertex
    · exact ⟨d.left, hsame u hu (hxv ▸ hx), d.vertex_ne_left.symm⟩
    · exact ⟨x, hx, hxv⟩
  · intro u hu x hx
    exact ⟨hm.vertex_subset u hu hx.1, hx.2⟩
  · intro e he
    obtain ⟨x, y, hxy⟩ := Graph.exists_isLink_of_mem_edgeSet (hm.edge_mem e he)
    exact ((d.retained_isLink_iff (hret e he).2.2.2 x y).2
      ⟨hxy, (hret e he).2.1, (hret e he).2.2.1⟩).edge_mem
  · intro a ha b hb hab
    exact (hm.vertex_disjoint a ha b hb hab).mono sdiff_subset sdiff_subset
  · intro u hu e he
    rw [hm.inc_iff u hu e he]
    constructor
    · rintro ⟨x, hx, hxe⟩
      exact ⟨x, ⟨hx, havoid e he x hxe⟩, (hinc e he x).2 hxe⟩
    · rintro ⟨x, hx, hxe⟩
      exact ⟨x, hx.1, (hinc e he x).1 hxe⟩
  · intro u hu e he
    rw [hm.isLoopAt_iff u hu e he]
    constructor
    · intro hall x hx
      have hxG := (hinc e he x).1 hx
      exact ⟨hall x hxG, havoid e he x hxG⟩
    · intro hall x hx
      exact (hall x ((hinc e he x).2 hx)).1
  · intro u hu
    obtain ⟨K, hK, hKv, hconn⟩ := hm.connected u hu
    let L := (d.result.deleteEdges (ηe '' E(H))).induce (ηv u \ {d.vertex})
    have hsub : ηv u \ {d.vertex} ⊆ V(d.result.deleteEdges (ηe '' E(H))) :=
      fun x hx => ⟨hm.vertex_subset u hu hx.1, hx.2⟩
    refine ⟨L, Graph.induce_le hsub, rfl, ?_⟩
    have hc := d.connected_image hfresh hK hconn
    simpa only [hKv, himage u hu] using hc

end GraphMinor.GM02
