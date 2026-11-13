module

public import GraphMinor.Compute.GM06Alg34ComplementFlatEntry
public import GraphMinor.Compute.Graph

/-!
# The finite complement adjacency matrix

Enumerate the ordered pairs of packed cells in row-major order and
record their complement edge bits. The matrix is an ordinary adjacency
matrix for the finite complement graph, including when there are no
cells. The RAM scan fills exactly this list.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The exact row-major complement edge bits determined by supplied input. -/
def gm06ComplementMatrixData (x : GM06DrawingData) (vs : List (Fin x.n)) : List ℕ :=
  List.ofFn (fun i : Fin (x.cellCount * x.cellCount) =>
    if (x.complementGraph vs).Adj i.divNat i.modNat then 1 else 0)

/-- The complement matrix has one entry per packed cell pair. -/
theorem gm06ComplementMatrixData_length (x : GM06DrawingData) (vs : List (Fin x.n)) :
    (gm06ComplementMatrixData x vs).length = x.cellCount * x.cellCount := by
  simp only [gm06ComplementMatrixData, List.length_ofFn]

/-- Each flat complement matrix position is the edge bit for its quotient
and remainder labels. -/
theorem gm06ComplementMatrixData_get (x : GM06DrawingData) (vs : List (Fin x.n))
    (i : Fin (x.cellCount * x.cellCount)) :
    (gm06ComplementMatrixData x vs)[i.val]'(by
      rw [gm06ComplementMatrixData_length]; exact i.isLt) =
      if (x.complementGraph vs).Adj i.divNat i.modNat then 1 else 0 := by
  simp only [gm06ComplementMatrixData, List.getElem_ofFn]

/-- The row-major complement data represent precisely the finite graph
whose components are used to recompute regions after deletion. -/
theorem gm06ComplementMatrixData_isAdjMatrixList (x : GM06DrawingData)
    (vs : List (Fin x.n)) : IsAdjMatrixList (x.complementGraph vs) (gm06ComplementMatrixData x vs) := by
  refine ⟨gm06ComplementMatrixData_length x vs, ?_⟩
  intro a b
  let i : Fin (x.cellCount * x.cellCount) := ⟨a.val * x.cellCount + b.val,
    mul_add_lt_mul a.isLt b.isLt⟩
  have hN : 0 < x.cellCount := Nat.zero_lt_of_lt b.isLt
  have hrow : i.divNat = a := by
    apply Fin.ext
    change (a.val * x.cellCount + b.val) / x.cellCount = a.val
    rw [Nat.mul_comm a.val, Nat.mul_add_div hN, Nat.div_eq_of_lt b.isLt, Nat.add_zero]
  have hcol : i.modNat = b := by
    apply Fin.ext
    change (a.val * x.cellCount + b.val) % x.cellCount = b.val
    rw [Nat.mul_comm a.val, Nat.mul_add_mod, Nat.mod_eq_of_lt b.isLt]
  have hh := gm06ComplementMatrixData_get x vs i
  rw [hrow, hcol] at hh
  have hentry : (gm06ComplementMatrixData x vs)[a.val * x.cellCount + b.val]'(by
      rw [gm06ComplementMatrixData_length]; exact mul_add_lt_mul a.isLt b.isLt) =
      if (x.complementGraph vs).Adj a b then 1 else 0 := hh
  rw [hentry]
  constructor
  · simp
  · split <;> omega

end GraphMinor.Compute
