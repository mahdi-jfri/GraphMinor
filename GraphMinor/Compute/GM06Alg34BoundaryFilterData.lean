module

public import GraphMinor.Compute.GM06Alg34BoundaryEntry

/-!
# Finite buffer updates for boundary-list selection

A boundary scan keeps selected old labels in their original order and
writes their new labels consecutively. The finite reference update
records those writes, including arbitrary old buffer contents. Its
live prefix is exactly the selected and relabelled boundary list.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Filter old labels by the boundary test and map them to their new labels. -/
def gm06BoundaryWords {α : Type*} (selected : α → Bool) (labels : α → ℕ)
    (L : List α) : List ℕ := (L.filter selected).map labels

/-- Exact consecutive writes made by a boundary-list selection pass. -/
def gm06BoundaryWrites {α : Type*} (selected : α → Bool) (labels : α → ℕ) :
    List α → ℕ → List ℕ → List ℕ
  | [], _, dst => dst
  | v :: L, k, dst => gm06BoundaryWrites selected labels L
      (k + (if selected v then 1 else 0))
      (if selected v then dst.set k (labels v) else dst)

/-- A selection pass preserves the allocated boundary buffer. -/
theorem gm06BoundaryWrites_length {α : Type*} (selected : α → Bool) (labels : α → ℕ)
    (L : List α) (k : ℕ) (dst : List ℕ) :
    (gm06BoundaryWrites selected labels L k dst).length = dst.length := by
  induction L generalizing k dst with
  | nil => rfl
  | cons v L ih => rw [gm06BoundaryWrites, ih]; cases selected v <;> simp

/-- The selected word list never exceeds the old-label list. -/
theorem gm06BoundaryWords_length_le {α : Type*} (selected : α → Bool) (labels : α → ℕ)
    (L : List α) : (gm06BoundaryWords selected labels L).length ≤ L.length := by
  simpa only [gm06BoundaryWords, List.length_map] using List.length_filter_le selected L

/-- Selection writes fill exactly the new live words after any existing
prefix and leave the unused reserved suffix unchanged. -/
theorem gm06BoundaryWrites_append {α : Type*} (selected : α → Bool) (labels : α → ℕ)
    (L : List α) (front suffix : List ℕ) (hcap : L.length ≤ suffix.length) :
    gm06BoundaryWrites selected labels L front.length (front ++ suffix) =
      front ++ gm06BoundaryWords selected labels L ++
        suffix.drop (gm06BoundaryWords selected labels L).length := by
  induction L generalizing front suffix with
  | nil => simp [gm06BoundaryWrites, gm06BoundaryWords]
  | cons v L ih =>
    rw [gm06BoundaryWrites]
    cases hv : selected v with
    | false =>
      simp only [hv, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      simpa only [gm06BoundaryWords, List.filter_cons, hv, Bool.false_eq_true, ↓reduceIte] using
        ih front suffix (by simp only [List.length_cons] at hcap; omega)
    | true =>
      simp only [hv, ↓reduceIte]
      cases suffix with
      | nil => simp at hcap
      | cons old suffix =>
        have hcap' : L.length ≤ suffix.length := by simp only [List.length_cons] at hcap; omega
        have hh := ih (front ++ [labels v]) suffix hcap'
        rw [List.set_append_right _ _ (by omega)]
        simp only [Nat.sub_self, List.set_cons_zero]
        simpa [gm06BoundaryWords, hv, List.length_append, List.append_assoc] using hh

/-- Starting at zero makes the live boundary prefix exactly its
selected relabelled list. -/
theorem gm06BoundaryWrites_take {α : Type*} (selected : α → Bool) (labels : α → ℕ)
    (L : List α) (dst : List ℕ) (hcap : L.length ≤ dst.length) :
    (gm06BoundaryWrites selected labels L 0 dst).take (gm06BoundaryWords selected labels L).length =
      gm06BoundaryWords selected labels L := by
  have hh := gm06BoundaryWrites_append selected labels L [] dst hcap
  simpa using congrArg (List.take (gm06BoundaryWords selected labels L).length) hh

end GraphMinor.Compute
