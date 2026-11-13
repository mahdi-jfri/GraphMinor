module

public import GraphMinor.Compute.GM06Alg34ClosureMatrixData
public import GraphMinor.Compute.GM06Alg34MatrixMarks

/-!
# Supplied row lists for the closure matrix

The vertex, edge, and region scans mark the same row lists as a single
fold. The lists use only the supplied counts, endpoints, and boundary
labels. This separates reading the matrix from the order in which its
three scans write it.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Vertex closure rows, followed by edge and region closure rows. -/
def gm06ClosureRowLists (x : GM06DrawingData) : List (ℕ × List ℕ) :=
  ((List.range' 0 x.n).map (fun v => (v, [v]))) ++
  ((x.raw.ends.zipIdx x.n).map (fun p => (p.2, [p.2, p.1.1, p.1.2]))) ++
  ((x.raw.regions.zipIdx (x.n + x.ends.length)).map
    (fun r => (r.2, r.2 :: (r.1.1 ++ r.1.2.map (fun e => x.n + e)))))

/-- Consecutive vertex updates are a fold of singleton closure rows. -/
theorem gm06OwnCellRows_eq_fold (N i k : ℕ) (dst : List ℕ) :
    gm06OwnCellRows N i k dst =
      ((List.range' i k).map (fun v => (v, [v]))).foldl (gm06MatrixMarkRow N) dst := by
  induction k generalizing i dst with
  | zero => rfl
  | succ k ih =>
    simp only [gm06OwnCellRows, List.range'_succ, List.map_cons, List.foldl_cons]
    exact ih (i + 1) (dst.set (N * i + i) 1)

/-- Consecutive edge updates are a fold of the own-cell and endpoint lists. -/
theorem gm06EdgeRows_eq_fold (N i : ℕ) (es : List (ℕ × ℕ)) (dst : List ℕ) :
    gm06EdgeRows N i es dst =
      ((es.zipIdx i).map (fun p => (p.2, [p.2, p.1.1, p.1.2]))).foldl
        (gm06MatrixMarkRow N) dst := by
  induction es generalizing i dst with
  | nil => rfl
  | cons p es ih =>
    simp only [gm06EdgeRows, List.zipIdx_cons, List.map_cons, List.foldl_cons]
    exact ih (i + 1) (gm06EdgeRowWrite N i p dst)

/-- Consecutive region updates are a fold of their supplied closure lists. -/
theorem gm06RegionRows_eq_fold (N n i : ℕ) (rs : List (List ℕ × List ℕ))
    (dst : List ℕ) :
    gm06RegionRows N n i rs dst =
      ((rs.zipIdx i).map (fun r => (r.2, r.2 :: (r.1.1 ++ r.1.2.map (fun e => n + e))))).foldl
        (gm06MatrixMarkRow N) dst := by
  induction rs generalizing i dst with
  | nil => rfl
  | cons r rs ih =>
    simp only [gm06RegionRows, List.zipIdx_cons, List.map_cons, List.foldl_cons]
    rw [ih]
    congr 1
    simp only [gm06MatrixMarkRow, gm06MarkCells, Nat.add_zero]
    rw [gm06MarkCells_append, ← gm06MarkCells_shift]
    rfl

/-- All three operational passes mark exactly the supplied row lists. -/
theorem gm06ClosureMatrixData_eq_fold (x : GM06DrawingData) :
    gm06ClosureMatrixData x =
      (gm06ClosureRowLists x).foldl (gm06MatrixMarkRow x.cellCount)
        (List.replicate (x.cellCount * x.cellCount) 0) := by
  simp only [gm06ClosureMatrixData, gm06ClosureRowLists, List.foldl_append,
    gm06OwnCellRows_eq_fold, gm06EdgeRows_eq_fold, gm06RegionRows_eq_fold]

end GraphMinor.Compute
