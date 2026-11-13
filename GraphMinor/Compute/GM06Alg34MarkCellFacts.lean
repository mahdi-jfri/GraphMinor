module

public import GraphMinor.Compute.GM06Alg34MarkCellLoop

/-!
# Reading the matrix produced by closure-incidence marks

A sequence of marks sets an entry to one exactly when some supplied
label addresses it. Other entries retain their previous value. This
pointwise description connects the marking loop to the finite closure
relation, including repeated boundary labels.
-/

public section
namespace GraphMinor.Compute

/-- Closure marks leave the matrix allocation unchanged. -/
theorem gm06MarkCells_length (row shift : ℕ) (L dst : List ℕ) :
    (gm06MarkCells row shift L dst).length = dst.length := by
  induction L generalizing dst with
  | nil => rfl
  | cons v L ih => rw [gm06MarkCells, ih, List.length_set]

/-- A matrix entry is marked exactly when a supplied label addresses it,
and otherwise retains its old value. -/
theorem gm06MarkCells_getElem (row shift : ℕ) (L dst : List ℕ) (j : ℕ)
    (hj : j < dst.length) :
    (gm06MarkCells row shift L dst)[j]'(by rw [gm06MarkCells_length]; exact hj) =
      if L.any (fun v => decide (row + shift + v = j)) then 1 else dst[j] := by
  induction L generalizing dst with
  | nil => simp [gm06MarkCells]
  | cons v L ih =>
    have hh := ih (dst.set (row + shift + v) 1) (by simpa only [List.length_set] using hj)
    simp only [gm06MarkCells]
    rw [hh, List.getElem_set]
    by_cases he : row + shift + v = j <;> simp [he]

/-- Starting from zeros gives the exact zero-one row incidence test. -/
theorem gm06MarkCells_replicate_getElem (row shift : ℕ) (L : List ℕ) (N j : ℕ)
    (hj : j < N) :
    (gm06MarkCells row shift L (List.replicate N 0))[j]'(by
      rw [gm06MarkCells_length, List.length_replicate]; exact hj) =
      if L.any (fun v => decide (row + shift + v = j)) then 1 else 0 := by
  have hh := gm06MarkCells_getElem row shift L (List.replicate N 0) j (by simpa using hj)
  simpa only [List.getElem_replicate] using hh

end GraphMinor.Compute
