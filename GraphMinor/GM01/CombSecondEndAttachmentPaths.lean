module

public import GraphMinor.GM01.CombEndAttachmentPaths
public import GraphMinor.GM01.CombReflectionIntervals
import GraphMinor.GM01.SubdivisionReindex

/-!
# The path from the second end to the middle cells

Graph Minors I, (4.14), page 59, contracts both ends of the layer
subdivision. Reflect the proved first-end path construction to obtain
the path from the second attachment to the last centre of the middle
segment. Reflection preserves all subdivision conditions and sends
the first three cells to the last three cells. The path therefore
meets the middle only at its last centre and stays in the last three
cells.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- The clean second-end path to the retained middle in GM01 (4.14),
page 59, with its location in the final three cells. -/
theorem exists_path_from_second_end_to_middle {α β : Type*} {γ L : ℕ}
    (hL : 5 ≤ L) {D : Graph α β}
    (c : (pathComb γ L).verts → α) (hc : Injective c)
    (P : (pathComb γ L).coe.edgeSet → Graph α β)
    (hV : V(D) = range c ∪ ⋃ e, V(P e))
    (hPaths : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds D (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ L).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c ∧ Disjoint E(P e) E(P f))
    {x : α} (hx : x ∈ combSecondEndSupport (by omega) c P) :
    let t := c ⟨Sum.inl ⟨L - 3, by omega⟩, pathComb_spine_mem γ L _⟩
    ∃ Q : Graph α β, IsGraphPathWithEnds D Q x t ∧
      V(Q) ∩ combSegmentSupport c P 2 (by omega : 2 + (L - 4) ≤ L) = {t} ∧
      V(Q) ⊆ combSegmentSupport c P (L - 3) (by omega : L - 3 + 3 ≤ L) := by
  let r := combReflectionEmbedding (γ := γ) (L := L)
  let E := combReflectionEdges (γ := γ) (L := L)
  let c' := fun v ↦ c (r v)
  let P' := fun e ↦ P (E e)
  have hdata := subdivision_reindex r combReflectionEmbedding_adj combReflectionEmbedding_involutive
    c P hV hPaths hInter
  have hcentres : ∀ v, c' v ∈ V(D) := by
    intro v
    rw [hV]
    exact Or.inl (mem_range_self (r v))
  have hxFirst : x ∈ combFirstEndSupport (by omega) c' P' := by
    rw [combFirstEndSupport_reflect_eq_second]
    exact hx
  obtain ⟨Q, hQ, hMeet, hSupport⟩ := exists_path_from_first_end_to_tail_with_support
    (by omega : 0 < L - 4) (by omega : 2 + (L - 4) ≤ L) c' (hc.comp r.injective)
    hcentres P' hdata.2.1 hdata.2.2 hxFirst
  have hroot : (rootedCombSegment (by omega : 0 < L - 4) D c' P' 2
      (by omega : 2 + (L - 4) ≤ L)).root.val =
      c ⟨Sum.inl ⟨L - 3, by omega⟩, pathComb_spine_mem γ L _⟩ := by
    apply congrArg c
    apply Subtype.ext
    apply congrArg Sum.inl
    apply Fin.ext
    change L - 1 - (2 + 0) = L - 3
    omega
  have hMiddle : combSegmentSupport c' P' 2 (by omega : 2 + (L - 4) ≤ L) =
      combSegmentSupport c P 2 (by omega : 2 + (L - 4) ≤ L) := by
    rw [combSegmentSupport_reflect_eq]
    congr 1
    omega
  have hLast : combSegmentSupport c' P' 0 (by omega : 0 + 3 ≤ L) =
      combSegmentSupport c P (L - 3) (by omega : L - 3 + 3 ≤ L) := by
    rw [combSegmentSupport_reflect_eq]
  refine ⟨Q, hroot ▸ hQ, ?_, ?_⟩
  · change V(Q) ∩ combSegmentSupport c' P' 2 _ = _ at hMeet
    rw [hMiddle, hroot] at hMeet
    exact hMeet
  · exact hLast ▸ hSupport

end GraphMinor.GM01
