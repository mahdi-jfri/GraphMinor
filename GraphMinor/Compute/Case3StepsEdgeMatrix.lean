module

public import GraphMinor.Compute.Case3StepsEdgeLabels

/-!
# The endpoint table for routing multigraph pairs

Each canonical simple edge writes its owner label at both directed endpoint
positions. The table has one word for each ordered pair of vertices. This
uses quadratic vertex work and one constant-size update per simple edge,
within the bound required by XIII (9.9), step 5, p. 105.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Row-major position for a directed endpoint pair. -/
def case3PairPosition {n : ℕ} (u v : Fin n) : ℕ := u.1 * n + v.1

/-- Every endpoint position lies in the square table. -/
theorem case3PairPosition_lt {n : ℕ} (u v : Fin n) : case3PairPosition u v < n * n := by
  have hu := u.2
  have hv := v.2
  unfold case3PairPosition
  nlinarith

/-- Store one undirected edge's owner at both directed endpoint positions. -/
def case3PutEdgeLabel {n : ℕ} (table : List ℕ) (u v : Fin n) (label : ℕ) : List ℕ :=
  (table.set (case3PairPosition u v) label).set (case3PairPosition v u) label

/-- Updating both directions preserves the table length. -/
theorem case3PutEdgeLabel_length {n : ℕ} (table : List ℕ) (u v : Fin n) (label : ℕ) :
    (case3PutEdgeLabel table u v label).length = table.length := by
  simp only [case3PutEdgeLabel, List.length_set]

/-- The table after visiting the first `k` canonical simple edges. -/
noncomputable def case3EdgeMatrixPrefix (x : Alg81Input) (Z : Finset (Fin x.n))
    (k : ℕ) : List ℕ :=
  ((List.finRange (case3InputEdges x).length).take k).foldl
    (fun table j => let e := (case3InputEdges x)[j.1]
      case3PutEdgeLabel table e.1 e.2 (case3EdgeLabel x Z j))
    (List.replicate (x.n * x.n) 0)

/-- Before the edge scan, every matrix entry is zero. -/
theorem case3EdgeMatrixPrefix_zero (x : Alg81Input) (Z : Finset (Fin x.n)) :
    case3EdgeMatrixPrefix x Z 0 = List.replicate (x.n * x.n) 0 := rfl

/-- Each canonical edge advances the matrix by its two endpoint writes. -/
theorem case3EdgeMatrixPrefix_succ (x : Alg81Input) (Z : Finset (Fin x.n))
    (k : ℕ) (hk : k < (case3InputEdges x).length) :
    case3EdgeMatrixPrefix x Z (k + 1) =
      case3PutEdgeLabel (case3EdgeMatrixPrefix x Z k)
        ((case3InputEdges x)[k]).1 ((case3InputEdges x)[k]).2
        (case3EdgeLabel x Z ⟨k, hk⟩) := by
  have hget : (List.finRange (case3InputEdges x).length)[k]'(by
      simpa only [List.length_finRange] using hk) = ⟨k, hk⟩ := by
    apply Fin.ext
    simp only [List.getElem_finRange, Fin.val_cast]
  unfold case3EdgeMatrixPrefix
  rw [take_add_one_eq_append_getElem _ k (by simpa only [List.length_finRange] using hk),
    List.foldl_append, hget]
  rfl

/-- Every partial endpoint table has the square vertex count as its length. -/
theorem case3EdgeMatrixPrefix_length (x : Alg81Input) (Z : Finset (Fin x.n)) (k : ℕ) :
    (case3EdgeMatrixPrefix x Z k).length = x.n * x.n := by
  have hfold (js : List (Fin (case3InputEdges x).length)) (table : List ℕ) :
      (js.foldl (fun table j => let e := (case3InputEdges x)[j.1]
        case3PutEdgeLabel table e.1 e.2 (case3EdgeLabel x Z j)) table).length = table.length := by
    induction js generalizing table with
    | nil => rfl
    | cons j js ih =>
      rw [List.foldl_cons, ih]
      exact case3PutEdgeLabel_length _ _ _ _
  exact (hfold _ _).trans (List.length_replicate ..)

end GraphMinor.Compute
