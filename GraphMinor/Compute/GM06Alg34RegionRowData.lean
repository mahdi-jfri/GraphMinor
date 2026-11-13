module

public import GraphMinor.Compute.GM06Alg34MarkCellFacts
public import GraphMinor.Compute.GM06Alg34PackedCells

/-!
# Region-row marks agree with the supplied closure relation

Marking concatenated incidence lists is the same as applying their
marks in succession. A kind offset can be moved into the supplied
labels. These identities identify the region row writer's three passes
with the numbered closure list used by the finite cell graph.
-/

public section
namespace GraphMinor.Compute

/-- Marking concatenated lists is exactly successive marking. -/
theorem gm06MarkCells_append (row shift : ℕ) (L M dst : List ℕ) :
    gm06MarkCells row shift (L ++ M) dst =
      gm06MarkCells row shift M (gm06MarkCells row shift L dst) := by
  induction L generalizing dst with
  | nil => rfl
  | cons v L ih => simp only [List.cons_append, gm06MarkCells, ih]

/-- A fixed cell-kind offset can equivalently be added to the supplied labels. -/
theorem gm06MarkCells_shift (row shift : ℕ) (L dst : List ℕ) :
    gm06MarkCells row shift L dst = gm06MarkCells row 0 (L.map (fun v => shift + v)) dst := by
  induction L generalizing dst with
  | nil => rfl
  | cons v L ih =>
    simp only [List.map_cons, gm06MarkCells, Nat.add_zero]
    rw [ih]
    simp only [Nat.add_assoc]

/-- The region row writer's own-cell, vertex, and edge marks are exactly
one marking pass over the numbered supplied region closure. -/
theorem gm06RegionRow_marks_closure (x : GM06DrawingData) (r : Fin x.regions.length)
    (row : ℕ) (dst : List ℕ) :
    gm06MarkCells row 0
      ((x.cellClosure (.inr (.inr r))).map (fun c => (x.cellNumbering c).val)) dst =
      gm06MarkCells row x.n (x.regions[r].edges.map Fin.val)
        (gm06MarkCells row 0 (x.regions[r].vertices.map Fin.val)
          (dst.set (row + (x.n + (x.ends.length + r.val))) 1)) := by
  rw [x.numbered_cellClosure_region]
  simp only [gm06MarkCells, Nat.add_zero]
  rw [gm06MarkCells_append]
  simpa only [List.map_map, Function.comp_def] using
    (gm06MarkCells_shift row x.n (x.regions[r].edges.map Fin.val)
      (gm06MarkCells row 0 (x.regions[r].vertices.map Fin.val)
        (dst.set (row + (x.n + (x.ends.length + r.val))) 1))).symm

end GraphMinor.Compute
