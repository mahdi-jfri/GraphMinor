module

public import Mathlib.Data.List.Nodup

/-!
# Recording one insertion in a path list

For the counting argument in II (2.8), a vertex in a path list is recorded
by its predecessor, or by a marker for the beginning of a path. A vertex
not on any path receives an unused marker instead. Erasing the vertex and
recording this slot retains enough information to recover a list with no
repeated vertices.
-/

@[expose] public section
namespace GraphMinor.GM02
open Classical
universe u
variable {α : Type u} [DecidableEq α]

/-- Insert `a` immediately after the first occurrence of `b`. -/
def insertAfter (a b : α) : List α → List α
  | [] => []
  | x :: xs => if x = b then x :: a :: xs else x :: insertAfter a b xs

/-- Inserting after an absent vertex leaves a list unchanged. -/
theorem insertAfter_eq_of_not_mem (a b : α) {l : List α} (hb : b ∉ l) :
    insertAfter a b l = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hbx : x ≠ b := fun h => hb (List.mem_cons.2 (Or.inl h.symm))
    have hbxs : b ∉ xs := fun h => hb (List.mem_cons_of_mem x h)
    simp [insertAfter, hbx, ih hbxs]

/-- The position of the first occurrence of `a`: absent, at the beginning,
or immediately after another vertex. -/
def listInsertionSlot (a : α) : List α → Option (Option α)
  | [] => none
  | x :: xs => if x = a then some none else
      match listInsertionSlot a xs with
      | some none => some (some x)
      | slot => slot

/-- The beginning slot occurs exactly when the list begins with `a`. -/
theorem listInsertionSlot_head_iff (a : α) (l : List α) :
    listInsertionSlot a l = some none ↔ l.head? = some a := by
  cases l with
  | nil => simp [listInsertionSlot]
  | cons x xs =>
    by_cases h : x = a
    · simp [listInsertionSlot, h]
    · simp only [listInsertionSlot, h, ↓reduceIte, List.head?_cons, Option.some.injEq]
      cases listInsertionSlot a xs with
      | none => simp
      | some slot => cases slot <;> simp

/-- A predecessor recorded by a slot belongs to the list. -/
theorem mem_of_listInsertionSlot {a b : α} {l : List α}
    (h : listInsertionSlot a l = some (some b)) : b ∈ l := by
  induction l with
  | nil => simp [listInsertionSlot] at h
  | cons x xs ih =>
    by_cases hx : x = a
    · simp [listInsertionSlot, hx] at h
    · simp only [listInsertionSlot, hx, ↓reduceIte] at h
      cases hs : listInsertionSlot a xs with
      | none => simp [hs] at h
      | some slot =>
        cases slot with
        | none => simp only [hs, Option.some.injEq] at h; exact List.mem_cons.2 (Or.inl h.symm)
        | some c =>
          simp only [hs, Option.some.injEq] at h
          exact List.mem_cons_of_mem x (ih (hs.trans (congrArg some (congrArg some h))))

/-- A vertex is absent exactly when it has no insertion slot. -/
theorem listInsertionSlot_none_iff (a : α) (l : List α) :
    listInsertionSlot a l = none ↔ a ∉ l := by
  induction l with
  | nil => simp [listInsertionSlot]
  | cons x xs ih =>
    by_cases hx : x = a
    · subst x; simp [listInsertionSlot]
    · cases hs : listInsertionSlot a xs with
      | none => simpa [listInsertionSlot, hx, Ne.symm hx, hs, List.mem_cons] using (ih.mp hs)
      | some slot =>
        have hm : a ∈ xs := by
          by_contra hn
          have heq := ih.mpr hn
          rw [hs] at heq
          contradiction
        cases slot <;> simp [listInsertionSlot, hx, hs, List.mem_cons, hm]

/-- A recorded predecessor remains in the list after erasing the vertex. -/
theorem mem_erase_of_listInsertionSlot {a b : α} {l : List α} (hl : l.Nodup)
    (h : listInsertionSlot a l = some (some b)) : b ∈ l.erase a := by
  induction l with
  | nil => simp [listInsertionSlot] at h
  | cons x xs ih =>
    have hxs := List.nodup_cons.1 hl
    by_cases hx : x = a
    · simp [listInsertionSlot, hx] at h
    · simp only [listInsertionSlot, hx, ↓reduceIte] at h
      cases hs : listInsertionSlot a xs with
      | none => simp [hs] at h
      | some slot =>
        cases slot with
        | none =>
          simp only [hs, Option.some.injEq] at h
          subst b
          simp [hx]
        | some c =>
          simp only [hs, Option.some.injEq] at h
          have hb := ih hxs.2 (hs.trans (congrArg some (congrArg some h)))
          simpa [List.erase_cons, hx] using List.mem_cons_of_mem x hb

/-- Erasing a vertex and recording its slot recovers a list with distinct
vertices. This is the injectivity step in the insertion count for II (2.8). -/
theorem reconstruct_list_of_slot (a : α) {l : List α} (hl : l.Nodup) :
    (match listInsertionSlot a l with
      | none => l.erase a
      | some none => a :: l.erase a
      | some (some b) => insertAfter a b (l.erase a)) = l := by
  induction l with
  | nil => simp [listInsertionSlot]
  | cons x xs ih =>
    have hnodup := List.nodup_cons.1 hl
    by_cases hx : x = a
    · subst x
      simp [listInsertionSlot]
    · have ih' := ih hnodup.2
      cases hs : listInsertionSlot a xs with
      | none =>
        simpa [listInsertionSlot, hx, hs, List.erase_cons, Ne.symm hx] using
          congrArg (List.cons x) (show xs.erase a = xs by simpa [hs] using ih')
      | some slot =>
        cases slot with
        | none =>
          have hhead := (listInsertionSlot_head_iff a xs).1 hs
          cases xs with
          | nil => simp at hhead
          | cons y ys =>
            have hy : y = a := Option.some.inj hhead
            subst y
            simp [listInsertionSlot, hx, insertAfter]
        | some b =>
          have hb : b ∈ xs := mem_of_listInsertionSlot hs
          have hxb : x ≠ b := fun heq => hnodup.1 (heq ▸ hb)
          simpa [listInsertionSlot, hx, hs, List.erase_cons, Ne.symm hx, insertAfter, hxb] using
            congrArg (List.cons x)
              (show insertAfter a b (xs.erase a) = xs by simpa [hs] using ih')

end GraphMinor.GM02
