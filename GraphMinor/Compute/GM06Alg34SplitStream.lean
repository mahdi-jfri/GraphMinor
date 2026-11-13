module

public import GraphMinor.Compute.GM06Alg34ReadBlockTest

/-!
# The finite stream of division blocks

The component rejection scan consumes the supplied length-prefixed
block records. Their word count bounds both the number of records and
the total number of labels, so one weighted stream bound covers the
search and scan work of every block.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The length-prefixed label records of a supplied division. -/
def gm06BlockStream {n : ℕ} (D : List (List (Fin n))) : List ℕ :=
  D.flatMap (fun L => GM06DrawingData.listWords (L.map Fin.val))

/-- The empty division has an empty block stream. -/
theorem gm06BlockStream_nil {n : ℕ} : gm06BlockStream ([] : List (List (Fin n))) = [] := rfl

/-- The next record consists of its length, its labels, then the remaining records. -/
theorem gm06BlockStream_cons {n : ℕ} (L : List (Fin n)) (D : List (List (Fin n))) :
    gm06BlockStream (L :: D) =
      GM06DrawingData.listWords (L.map Fin.val) ++ gm06BlockStream D := rfl

/-- Each block contributes one count word and one word per supplied label. -/
theorem gm06BlockStream_cons_length {n : ℕ} (L : List (Fin n))
    (D : List (List (Fin n))) :
    (gm06BlockStream (L :: D)).length = 1 + L.length + (gm06BlockStream D).length := by
  simp only [gm06BlockStream_cons, List.length_append, GM06DrawingData.listWords,
    List.length_cons, List.length_map]
  omega

/-- There are at most as many supplied blocks as record words. -/
theorem gm06BlockStream_count_le {n : ℕ} (D : List (List (Fin n))) :
    D.length ≤ (gm06BlockStream D).length := by
  induction D with
  | nil => exact Nat.le_refl 0
  | cons L D ih => rw [List.length_cons, gm06BlockStream_cons_length]; omega

end GraphMinor.Compute
