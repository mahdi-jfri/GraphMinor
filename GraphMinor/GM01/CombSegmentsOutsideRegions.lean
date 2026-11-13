module

public import GraphMinor.GM01.CombShiftRanges
public import GraphMinor.GM01.CombPathsOutside

/-!
# An early selected segment avoids a later region

The prefix retained in Graph Minors I, (4.10), page 58, uses only cells
before its boundary cut. Its centres lie outside the later region,
and every selected replacing path has both source ends before that
cut. The proved source-side closure gives avoidance for all of them.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function

/-- A selected segment entirely before a cut is disjoint from the
later avoidance region. This places the old comb model inside `B` in
GM01 (4.10), page 58. -/
theorem combSegmentSupport_disjoint_later_region {α β : Type*} {γ L m : ℕ}
    {N : Graph α β} {c : (pathComb γ L).verts → α} (hc : Injective c)
    (P : (pathComb γ L).coe.edgeSet → Graph α β) (hPN : ∀ e, P e ≤ N)
    (hE : E(N) = ⋃ e, E(P e))
    (hRanges : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ L).coe.edgeSet, e ≠ f → V(P e) ∩ V(P f) ⊆ range c)
    (offset : ℕ) (hbound : offset + m ≤ L) (q : Fin L) (hq : q.val < L - 1)
    (hupper : offset + m ≤ q.val + 1) :
    Disjoint (combSegmentSupport c P offset hbound)
      (vertexAvoidanceRegion N
        (c ⟨Sum.inl ⟨L - 1, by omega⟩, pathComb_spine_mem γ L _⟩)
        (c ⟨Sum.inl q, pathComb_spine_mem γ L q⟩)) := by
  let f := combShiftEmbedding (γ := γ) offset hbound
  let hf := fun {a b} (h : (pathComb γ m).coe.Adj a b) ↦ combShiftEmbedding_adj offset hbound h
  have hidx : ∀ v ∈ range f, (pathCombSpineIndex v.val).val ≤ q.val := by
    intro v hv
    have h := (mem_range_combShiftEmbedding_iff offset hbound v).mp hv
    omega
  apply Set.disjoint_left.mpr
  intro x hx hxRegion
  rcases hx with ⟨v, rfl⟩ | hxPath
  · exact comb_subdivision_centre_not_mem_later_region hc hPN hE hRanges hInter q hq (f v)
      (hidx _ (mem_range_self v)) hxRegion
  · obtain ⟨e, hxe⟩ := Set.mem_iUnion.mp hxPath
    have hEnds : ∀ v ∈ (subdivisionEmbeddingEdges f hf e).val,
        (pathCombSpineIndex v.val).val ≤ q.val := by
      intro v hv
      exact hidx v (subdivisionEmbeddingEdges_mem_range f hf e hv)
    exact Set.disjoint_left.mp
      (comb_subdivision_path_disjoint_later_region hc hPN hE hRanges hInter q hq
        (subdivisionEmbeddingEdges f hf e) hEnds) hxe hxRegion

end GraphMinor.GM01
