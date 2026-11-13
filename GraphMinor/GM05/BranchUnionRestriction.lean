module

public import GraphMinor.Minor.Model
import GraphMinor.GM05.CopyModels
import GraphMinor.Minor.Basic

/-!
# Restricting a minor model to its branch union

For GM V, (8.14), every chosen middle edge has both ends in the
star branches. The whole model therefore lies in the host induced
on their vertex union. This keeps the eventual expansion inside
the vertices belonging to its one geometric copy.
-/

public section
namespace GraphMinor.GM05
open Set Graph

/-- A model lies in the host induced on the union of its branches.
This is the vertex bound needed for the expansions in GM V, (8.14). -/
theorem minor_model_induce_branch_union {α β α' β' : Type*}
    {H : Graph α' β'} {G : Graph α β} {ηv : α' → Set α} {ηe : β' → β}
    (hm : IsMinorModel H G ηv ηe) :
    IsMinorModel H (G.induce (⋃ v ∈ V(H), ηv v)) ηv ηe := by
  let B := ⋃ v ∈ V(H), ηv v
  have hB : B ⊆ V(G) := by
    intro x hx
    obtain ⟨v,hv,hxv⟩ := mem_iUnion₂.mp hx
    exact hm.vertex_subset v hv hxv
  have ends : ∀ e ∈ E(H), ∀ x, G.Inc (ηe e) x → x ∈ B := by
    intro e he x hx
    obtain ⟨u,v,huv⟩ := H.exists_isLink_of_mem_edgeSet he
    obtain ⟨p,hp,q,hq,hpq⟩ := minor_model_link hm huv
    rcases hx.eq_or_eq_of_isLink hpq with rfl | rfl
    · exact mem_iUnion₂.mpr ⟨u,huv.left_mem,hp⟩
    · exact mem_iUnion₂.mpr ⟨v,huv.right_mem,hq⟩
  have hinc : ∀ e ∈ E(H), ∀ x, (G.induce B).Inc (ηe e) x ↔ G.Inc (ηe e) x := by
    intro e he x
    constructor
    · rintro ⟨y,hxy⟩
      exact ⟨y,hxy.1⟩
    · rintro ⟨y,hxy⟩
      exact ⟨y,hxy,ends e he x hxy.inc_left,ends e he y hxy.inc_right⟩
  refine ⟨hm.vertex_nonempty,?_,?_,hm.vertex_disjoint,hm.edge_injOn,?_,?_,?_⟩
  · intro v hv x hx
    exact mem_iUnion₂.mpr ⟨v,hv,hx⟩
  · intro e he
    obtain ⟨x,y,hxy⟩ := G.exists_isLink_of_mem_edgeSet (hm.edge_mem e he)
    exact ⟨x,y,hxy,ends e he x hxy.inc_left,ends e he y hxy.inc_right⟩
  · intro v hv e he
    change H.Inc e v ↔ ∃ x ∈ ηv v, (G.induce B).Inc (ηe e) x
    simpa only [hinc e he] using hm.inc_iff v hv e he
  · intro v hv e he
    change H.IsLoopAt e v ↔ ∀ x, (G.induce B).Inc (ηe e) x → x ∈ ηv v
    simpa only [hinc e he] using hm.isLoopAt_iff v hv e he
  · intro v hv
    obtain ⟨K,hK,hKV,hconn⟩ := hm.connected v hv
    have hKB : V(K) ⊆ B := fun x hx ↦ mem_iUnion₂.mpr ⟨v,hv,hKV ▸ hx⟩
    have hKG : K ≤ G := hK.trans Graph.deleteEdges_le
    refine ⟨K,⟨hKB,?_⟩,hKV,hconn⟩
    intro e x y he
    exact ⟨⟨hKG.isLink_mono he,hKB he.left_mem,hKB he.right_mem⟩,(hK.isLink_mono he).2⟩

end GraphMinor.GM05
