module

public import GraphMinor.Compute.GM06Alg34RegionRowData
public import GraphMinor.Compute.GM06Alg34Layout

/-!
# Finite closure-matrix updates for the supplied edge stream

Each edge marks its own packed cell and its two supplied ends. Apply
these updates at consecutive packed edge labels. The natural-word
stream is exactly the endpoint section already present in the input.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The two supplied endpoint words per old edge. -/
def gm06EdgeWords (es : List (ℕ × ℕ)) : List ℕ := es.flatMap (fun p => [p.1, p.2])

/-- The exact own-cell and two-endpoint update for one old edge. -/
def gm06EdgeRowWrite (N i : ℕ) (p : ℕ × ℕ) (dst : List ℕ) : List ℕ :=
  (((dst.set (N * i + i) 1).set (N * i + p.1) 1).set (N * i + p.2) 1)

/-- The exact closure-row updates for consecutive supplied old edges. -/
def gm06EdgeRows (N : ℕ) : ℕ → List (ℕ × ℕ) → List ℕ → List ℕ
  | _, [], dst => dst
  | i, p :: es, dst => gm06EdgeRows N (i + 1) es (gm06EdgeRowWrite N i p dst)

/-- There are exactly two endpoint words per supplied edge. -/
theorem gm06EdgeWords_length (es : List (ℕ × ℕ)) :
    (gm06EdgeWords es).length = 2 * es.length := by
  induction es with
  | nil => rfl
  | cons p es ih =>
    simp only [gm06EdgeWords, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at *
    omega

/-- One old-edge row update preserves matrix allocation. -/
theorem gm06EdgeRowWrite_length (N i : ℕ) (p : ℕ × ℕ) (dst : List ℕ) :
    (gm06EdgeRowWrite N i p dst).length = dst.length := by
  simp only [gm06EdgeRowWrite, List.length_set]

/-- All consecutive old-edge updates preserve matrix allocation. -/
theorem gm06EdgeRows_length (N i : ℕ) (es : List (ℕ × ℕ)) (dst : List ℕ) :
    (gm06EdgeRows N i es dst).length = dst.length := by
  induction es generalizing i dst with
  | nil => rfl
  | cons p es ih => rw [gm06EdgeRows, ih, gm06EdgeRowWrite_length]

/-- The raw endpoint stream is the supplied input's endpoint section. -/
theorem gm06EdgeWords_raw (x : GM06DrawingData) : gm06EdgeWords x.raw.ends = x.endpointWords := by
  simp only [gm06EdgeWords, GM06DrawingData.raw, GM06DrawingData.endpointWords, List.flatMap_map]

/-- The finite edge-row update is exactly its numbered closure-list marking. -/
theorem gm06EdgeRow_marks_closure (x : GM06DrawingData) (e : Fin x.ends.length) (dst : List ℕ) :
    gm06MarkCells (x.cellCount * (x.n + e.val)) 0
      ((x.cellClosure (.inr (.inl e))).map (fun c => (x.cellNumbering c).val)) dst =
      gm06EdgeRowWrite x.cellCount (x.n + e.val) (x.ends[e].1.val, x.ends[e].2.val) dst := by
  rw [x.numbered_cellClosure_edge]
  simp only [gm06MarkCells, Nat.add_zero, gm06EdgeRowWrite]

end GraphMinor.Compute
