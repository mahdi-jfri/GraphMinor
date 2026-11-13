module

public import GraphMinor.Compute.GM06Alg34OwnCellRows
public import GraphMinor.Compute.GM06Alg34EdgeRowsData
public import GraphMinor.Compute.GM06Alg34RegionRowsData

/-!
# The closure matrix computed from supplied drawing data

Start with the square zero array. Mark the vertex rows, then the
supplied edge endpoint rows, then the supplied region boundary rows.
Every value comes from the finite input. The allocation remains the
square of the supplied cell count throughout these updates.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The exact finite matrix resulting from all three supplied-cell row passes. -/
def gm06ClosureMatrixData (x : GM06DrawingData) : List ℕ :=
  gm06RegionRows x.cellCount x.n (x.n + x.ends.length) x.raw.regions
    (gm06EdgeRows x.cellCount x.n x.raw.ends
      (gm06OwnCellRows x.cellCount 0 x.n (List.replicate (x.cellCount * x.cellCount) 0)))

/-- The computed closure matrix has exactly one slot per ordered cell pair. -/
theorem gm06ClosureMatrixData_length (x : GM06DrawingData) :
    (gm06ClosureMatrixData x).length = x.cellCount * x.cellCount := by
  simp only [gm06ClosureMatrixData, gm06RegionRows_length, gm06EdgeRows_length,
    gm06OwnCellRows_length, List.length_replicate]

/-- The own-cell mark of a vertex is exactly its numbered closure list. -/
theorem gm06VertexRow_marks_closure (x : GM06DrawingData) (v : Fin x.n) (dst : List ℕ) :
    gm06MarkCells (x.cellCount * v.val) 0
      ((x.cellClosure (.inl v)).map (fun c => (x.cellNumbering c).val)) dst =
      dst.set (x.cellCount * v.val + v.val) 1 := by
  rw [x.numbered_cellClosure_vertex]
  simp only [gm06MarkCells, Nat.add_zero]

end GraphMinor.Compute
