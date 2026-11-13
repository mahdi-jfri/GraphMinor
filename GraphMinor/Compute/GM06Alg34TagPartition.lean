module

public import GraphMinor.Compute.GM06Alg34Tags
public import GraphMinor.Compute.GM06Alg34Words

/-!
# Block tags classify the supplied division

Equal positive tags point to one common supplied block. Conversely, for
a division, two labels in a common block have identical block-membership
patterns and hence equal tags. This connects the computed RAM table to
the paper's division, including repeated list representations of a block.
-/

@[expose] public section
namespace GraphMinor.Compute

open Set GM06

universe u

/-- The sets represented by the supplied lists of labels. -/
def gm06BlockSets {α : Type u} (D : List (List α)) : Set (Set α) :=
  (fun B => {a | a ∈ B}) '' {B | B ∈ D}

/-- Equal nonzero last-block tags identify a common supplied block. This
part needs no disjointness assumption on the block lists. -/
theorem gm06BlockTag_common_block {α : Type u} [DecidableEq α]
    (D : List (List α)) (a b : α) (heq : gm06BlockTag D a = gm06BlockTag D b)
    (hpos : gm06BlockTag D a ≠ 0) : ∃ B ∈ D, a ∈ B ∧ b ∈ B := by
  induction D with
  | nil => exact False.elim (hpos rfl)
  | cons B D ih =>
    have hleA := gm06BlockTag_le_length D a
    have hleB := gm06BlockTag_le_length D b
    by_cases ha0 : gm06BlockTag D a = 0
    · have haB : a ∈ B := by
        by_contra hn
        exact hpos (by simp only [gm06BlockTag, ha0, hn, ↓reduceIte])
      by_cases hb0 : gm06BlockTag D b = 0
      · by_cases hbB : b ∈ B
        · exact ⟨B, List.mem_cons_self, haB, hbB⟩
        · have hbzero : gm06BlockTag (B :: D) b = 0 := by
            simp only [gm06BlockTag, hb0, hbB, ↓reduceIte]
          exact False.elim (hpos (heq.trans hbzero))
      · have ht : D.length + 1 = gm06BlockTag D b := by
          simpa only [gm06BlockTag, ha0, hb0, haB, ↓reduceIte] using heq
        omega
    · by_cases hb0 : gm06BlockTag D b = 0
      · by_cases hbB : b ∈ B
        · have ht : gm06BlockTag D a = D.length + 1 := by
            simpa only [gm06BlockTag, ha0, hb0, hbB, ↓reduceIte] using heq
          omega
        · simp only [gm06BlockTag, ha0, hb0, hbB, ↓reduceIte] at heq
      · have ht : gm06BlockTag D a = gm06BlockTag D b := by
          simpa only [gm06BlockTag, ha0, hb0, ↓reduceIte] using heq
        obtain ⟨A, hA, haA, hbA⟩ := ih ht ha0
        exact ⟨A, List.mem_cons_of_mem B hA, haA, hbA⟩

/-- Two supplied members of a division that share a label represent the
same set, even when their lists have different orders. -/
theorem gm06BlockSets_eq_of_common {α : Type u} {D : List (List α)}
    (hD : IsDivision (gm06BlockSets D)) {A B : List α} (hA : A ∈ D) (hB : B ∈ D)
    {a : α} (haA : a ∈ A) (haB : a ∈ B) : ({v | v ∈ A} : Set α) = {v | v ∈ B} := by
  by_cases heq : ({v | v ∈ A} : Set α) = {v | v ∈ B}
  · exact heq
  · have hdis := hD.2.2 (show ({v | v ∈ A} : Set α) ∈ gm06BlockSets D from ⟨A, hA, rfl⟩)
      (show ({v | v ∈ B} : Set α) ∈ gm06BlockSets D from ⟨B, hB, rfl⟩) heq
    exact False.elim (Set.disjoint_left.mp hdis haA haB)

/-- Two labels of one division block have the same membership in every
supplied block, because distinct division members are disjoint. -/
theorem gm06BlockTag_eq_of_same_block {α : Type u} [DecidableEq α] {D : List (List α)}
    (hD : IsDivision (gm06BlockSets D)) {B : List α} (hB : B ∈ D)
    {a b : α} (ha : a ∈ B) (hb : b ∈ B) : gm06BlockTag D a = gm06BlockTag D b := by
  apply gm06BlockTag_eq_of_memberships
  intro A hA
  constructor
  · intro haA
    exact (gm06BlockSets_eq_of_common hD hA hB haA ha).symm.subset hb
  · intro hbA
    exact (gm06BlockSets_eq_of_common hD hA hB hbA hb).symm.subset ha

/-- For a division, equality of positive tags means exactly membership
in one common supplied block. -/
theorem gm06BlockTag_eq_pos_iff {α : Type u} [DecidableEq α] {D : List (List α)}
    (hD : IsDivision (gm06BlockSets D)) (a b : α) :
    (gm06BlockTag D a = gm06BlockTag D b ∧ gm06BlockTag D a ≠ 0) ↔
      ∃ B ∈ D, a ∈ B ∧ b ∈ B := by
  constructor
  · rintro ⟨heq, hpos⟩
    exact gm06BlockTag_common_block D a b heq hpos
  · rintro ⟨B, hB, ha, hb⟩
    refine ⟨gm06BlockTag_eq_of_same_block hD hB ha hb, ?_⟩
    intro hzero
    exact (gm06BlockTag_eq_zero_iff D a).mp hzero B hB ha

/-- The computed table entry at a finite vertex label is its supplied
block tag, without any dependence on geometric coordinates. -/
theorem gm06DivisionIds_fin_getD (x : GM06DrawingData) (a : Fin x.n) :
    (gm06DivisionIds x.raw.division (List.replicate x.n 0)).getD a.val 0 =
      gm06BlockTag x.division a := by
  rw [gm06DivisionIds_zero_getD _ _ _ a.isLt]
  exact gm06BlockTag_map Fin.val Fin.val_injective x.division a

end GraphMinor.Compute
