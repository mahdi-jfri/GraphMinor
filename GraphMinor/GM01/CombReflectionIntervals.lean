module

public import GraphMinor.GM01.CombReflectionSubdivision
import GraphMinor.GM01.CombInteriorForkReflection

/-!
# Reflection of a represented cell interval

The two joins in Graph Minors I, (4.14), page 59, use paths through
the first and second ends. Reflection sends each cell interval to
its reversed interval, including its centres and all replacing paths.
Thus the proved first-end path construction applies at the other end
with the same bounds on the cells it uses.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function

/-- Reflecting a cell interval reflects its entire subdivision support,
as needed for the second join in GM01 (4.14), page 59. -/
theorem combSegmentSupport_reflect_eq {α β : Type*} {γ L m : ℕ}
    (c : (pathComb γ L).verts → α) (P : (pathComb γ L).coe.edgeSet → Graph α β)
    (offset : ℕ) (hbound : offset + m ≤ L) :
    combSegmentSupport (fun v ↦ c (combReflectionEmbedding v))
      (fun e ↦ P (combReflectionEdges e)) offset hbound =
      combSegmentSupport c P (L - (offset + m)) (by omega : L - (offset + m) + m ≤ L) := by
  let r := combReflectionEmbedding (γ := γ) (L := L)
  let E := combReflectionEdges (γ := γ) (L := L)
  have hidx : ∀ v : (pathComb γ L).verts,
      (pathCombSpineIndex (r v).val).val = L - ((pathCombSpineIndex v.val).val + 1) :=
    fun v ↦ combReflectVertex_spineIndex v.val
  have hInv : Involutive r := combReflectionEmbedding_involutive
  have hEInv : Involutive E := combReflectionEdges_involutive
  ext x
  change x ∈ combSegmentSupport (fun v ↦ c (r v)) (fun e ↦ P (E e)) offset hbound ↔
    x ∈ combSegmentSupport c P (L - (offset + m)) (by omega : L - (offset + m) + m ≤ L)
  rw [mem_combSegmentSupport_iff, mem_combSegmentSupport_iff]
  constructor
  · rintro (⟨v, hlo, hhi, hv⟩ | ⟨e, hxe, hEnds⟩)
    · have hi := hidx v
      have hvL := (pathCombSpineIndex v.val).isLt
      exact Or.inl ⟨r v, by omega, by omega, hv⟩
    · refine Or.inr ⟨E e, hxe, ?_⟩
      intro u hu
      change u ∈ Sym2.map r e.val at hu
      obtain ⟨v, hv, hrv⟩ := Sym2.mem_map.mp hu
      have h := hEnds v hv
      have hi := hidx v
      have hvL := (pathCombSpineIndex v.val).isLt
      rw [← hrv]
      exact ⟨by omega, by omega⟩
  · rintro (⟨v, hlo, hhi, hv⟩ | ⟨e, hxe, hEnds⟩)
    · have hi := hidx v
      have hvL := (pathCombSpineIndex v.val).isLt
      refine Or.inl ⟨r v, by omega, by omega, ?_⟩
      rw [hInv v]
      exact hv
    · refine Or.inr ⟨E e, ?_, ?_⟩
      · rw [hEInv e]
        exact hxe
      · intro u hu
        change u ∈ Sym2.map r e.val at hu
        obtain ⟨v, hv, hrv⟩ := Sym2.mem_map.mp hu
        have h := hEnds v hv
        have hi := hidx v
        have hvL := (pathCombSpineIndex v.val).isLt
        rw [← hrv]
        exact ⟨by omega, by omega⟩

end GraphMinor.GM01
