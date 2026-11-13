module

public import GraphMinor.Compute.GM06Alg34TagDivision

/-!
# Meaning of a vertex's tag after the division scan

A tag records the last supplied block containing the vertex, numbered
from the end of the block list. Zero means that no block contains it.
The verified table-update function has exactly these pointwise values.
The tag is bounded by the number of supplied blocks.
-/

@[expose] public section
namespace GraphMinor.Compute

universe u v

/-- The last containing block's index counted from the end, with zero
for a label occurring in no supplied block. -/
def gm06BlockTag {α : Type u} [DecidableEq α] : List (List α) → α → ℕ
  | [], _ => 0
  | B :: D, a =>
    if gm06BlockTag D a = 0 then (if a ∈ B then D.length + 1 else 0) else gm06BlockTag D a

/-- A tag always fits in the supplied block count. -/
theorem gm06BlockTag_le_length {α : Type u} [DecidableEq α] (D : List (List α)) (a : α) :
    gm06BlockTag D a ≤ D.length := by
  induction D with
  | nil => exact le_rfl
  | cons B D ih =>
    simp only [gm06BlockTag, List.length_cons]
    split_ifs
    · exact le_rfl
    · exact Nat.zero_le _
    · exact ih.trans (Nat.le_succ _)

/-- Exactly the labels absent from every supplied block have tag zero. -/
theorem gm06BlockTag_eq_zero_iff {α : Type u} [DecidableEq α] (D : List (List α)) (a : α) :
    gm06BlockTag D a = 0 ↔ ∀ B ∈ D, a ∉ B := by
  induction D with
  | nil => simp only [gm06BlockTag, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  | cons B D ih =>
    simp only [List.forall_mem_cons, ← ih]
    by_cases ht : gm06BlockTag D a = 0 <;> by_cases hb : a ∈ B <;>
      simp [gm06BlockTag, ht, hb]

/-- Labels with the same memberships in the supplied blocks get the same
last-block tag, even if blocks are repeated or reordered internally. -/
theorem gm06BlockTag_eq_of_memberships {α : Type u} [DecidableEq α]
    (D : List (List α)) (a b : α) (h : ∀ B ∈ D, a ∈ B ↔ b ∈ B) :
    gm06BlockTag D a = gm06BlockTag D b := by
  induction D with
  | nil => rfl
  | cons B D ih =>
    have ht := ih (fun A hA => h A (List.mem_cons_of_mem B hA))
    have hm := h B List.mem_cons_self
    simp only [gm06BlockTag, ht, hm]

/-- Injective changes of label names preserve the table's block tags. -/
theorem gm06BlockTag_map {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (D : List (List α)) (a : α) :
    gm06BlockTag (D.map (List.map f)) (f a) = gm06BlockTag D a := by
  induction D with
  | nil => rfl
  | cons B D ih =>
    have hm : f a ∈ B.map f ↔ a ∈ B := by simp only [List.mem_map, hf.eq_iff, exists_eq_right]
    simp only [List.map_cons, gm06BlockTag, ih, List.length_map, hm]

/-- One block update changes a valid table position exactly when its
label occurs in that block. -/
theorem gm06TagBlock_getD (tag : ℕ) (vs ids : List ℕ) (a : ℕ) (ha : a < ids.length) :
    (gm06TagBlock tag vs ids).getD a 0 = if a ∈ vs then tag else ids.getD a 0 := by
  induction vs generalizing ids with
  | nil => simp only [gm06TagBlock, List.not_mem_nil, ↓reduceIte]
  | cons v vs ih =>
    rw [gm06TagBlock, ih (ids.set v tag) (by simpa only [List.length_set] using ha),
      getD_set_of_lt ids tag 0 ha]
    by_cases hs : a ∈ vs
    · simp [hs]
    · by_cases hv : v = a
      · subst v
        simp [hs]
      · simp [hs, hv, Ne.symm hv]

/-- The division scan gives its last-block tag to every covered position
and leaves uncovered positions at their original values. -/
theorem gm06DivisionIds_getD (D : List (List ℕ)) (ids : List ℕ) (a : ℕ) (ha : a < ids.length) :
    (gm06DivisionIds D ids).getD a 0 =
      if gm06BlockTag D a = 0 then ids.getD a 0 else gm06BlockTag D a := by
  induction D generalizing ids with
  | nil => simp only [gm06DivisionIds, gm06BlockTag, ↓reduceIte]
  | cons B D ih =>
    rw [gm06DivisionIds, ih (gm06TagBlock (B :: D).length B ids)
      (by simpa only [gm06TagBlock_length] using ha), gm06TagBlock_getD _ _ _ _ ha]
    by_cases ht : gm06BlockTag D a = 0 <;> by_cases hb : a ∈ B <;>
      simp [gm06BlockTag, ht, hb]

/-- From a zero-initialized table the pointwise values are exactly the
last-block tags, including uncovered labels. -/
theorem gm06DivisionIds_zero_getD (D : List (List ℕ)) (n a : ℕ) (ha : a < n) :
    (gm06DivisionIds D (List.replicate n 0)).getD a 0 = gm06BlockTag D a := by
  rw [gm06DivisionIds_getD _ _ _ (by simpa only [List.length_replicate] using ha),
    getD_replicate_of_lt 0 0 ha]
  by_cases ht : gm06BlockTag D a = 0 <;> simp only [ht, ↓reduceIte]

end GraphMinor.Compute
