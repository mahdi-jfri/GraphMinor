module

public import GraphMinor.Compute.CrossingOpsEdgeStream

/-!
# Splitting the edge prefix at its last row

An edge prefix consists of every increasing edge in earlier vertex rows and a prefix
of one final row. This form supports a constant-time membership test using that row's
index and a mark array for the chosen neighbours in the final row.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- All increasing edges in vertex rows below `x`. -/
def edgeRowsBefore {N : ℕ} (lists : Fin N → List ℕ) (x : ℕ) : List (Fin N × Fin N) :=
  ((List.finRange N).take x).flatMap (edgeRow lists)

@[simp] theorem edgeRowsBefore_zero {N : ℕ} (lists : Fin N → List ℕ) :
    edgeRowsBefore lists 0 = [] := rfl

@[simp] theorem edgeRowsBefore_all {N : ℕ} (lists : Fin N → List ℕ) :
    edgeRowsBefore lists N = edgeStream lists := by
  have hlen : (List.finRange N).length = N := by simp
  have ht : (List.finRange N).take N = List.finRange N := by
    simpa only [hlen] using (show (List.finRange N).take (List.finRange N).length = List.finRange N from List.take_length)
  simp only [edgeRowsBefore, ht, edgeStream]

/-- The next row appends exactly its increasing edges. -/
theorem edgeRowsBefore_succ {N : ℕ} (lists : Fin N → List ℕ) {x : ℕ} (hx : x < N) :
    edgeRowsBefore lists (x + 1) = edgeRowsBefore lists x ++ edgeRow lists ⟨x, hx⟩ := by
  have hx' : x < (List.finRange N).length := by simpa using hx
  simp only [edgeRowsBefore, List.take_succ_eq_append_getElem hx', List.flatMap_append,
    List.flatMap_singleton, List.getElem_finRange, Fin.cast_mk]

/-- Membership in the earlier rows is membership in the stream with smaller first index. -/
theorem mem_edgeRowsBefore {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    (h : IsAdjListFamily G lists) (x : ℕ) (u v : Fin N) :
    (u, v) ∈ edgeRowsBefore lists x ↔ G.Adj u v ∧ u.val < v.val ∧ u.val < x := by
  have htake : ∀ a : Fin N, a ∈ (List.finRange N).take x ↔ a.val < x := by
    intro a
    simpa only [List.idxOf_finRange] using
      (List.mem_take_iff_idxOf_lt (show a ∈ List.finRange N by simp) :
        a ∈ (List.finRange N).take x ↔ (List.finRange N).idxOf a < x)
  simp only [edgeRowsBefore, List.mem_flatMap, htake, mem_edgeRow]
  constructor
  · rintro ⟨a, ha, rfl, hv, hlt⟩
    exact ⟨((h u).2.2.2 v).mp hv, hlt, ha⟩
  · rintro ⟨hadj, hlt, hrow⟩
    exact ⟨u, hrow, rfl, ((h u).2.2.2 v).mpr hadj, hlt⟩

/-- The row count computed from numerical neighbours equals the oriented row length. -/
theorem edgeRow_length {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    (h : IsAdjListFamily G lists) (u : Fin N) :
    (edgeRow lists u).length = ((lists u).filter (fun y => u.val < y)).length := by
  have hh := map_val_toFin (h u).1
  rw [← hh, List.filter_map]
  simp only [edgeRow, List.length_map, Function.comp_def]

/-- Earlier rows followed by a prefix of the current row form a prefix of the edge stream. -/
theorem edgeRowsBefore_prefix {N : ℕ} (lists : Fin N → List ℕ) (u : Fin N) (q : ℕ) :
    edgeRowsBefore lists u.val ++ (edgeRow lists u).take q <+: edgeStream lists := by
  have hu : u.val < (List.finRange N).length := by simpa using u.isLt
  have hrows : List.finRange N = (List.finRange N).take u.val ++ u :: (List.finRange N).drop (u.val + 1) := by
    calc
      List.finRange N = (List.finRange N).take u.val ++ (List.finRange N).drop u.val :=
        (List.take_append_drop _ _).symm
      _ = _ := by rw [List.drop_eq_getElem_cons hu]; simp only [List.getElem_finRange, Fin.cast_mk, Fin.eta]
  let rest := ((List.finRange N).drop (u.val + 1)).flatMap (edgeRow lists)
  have hs : edgeStream lists = edgeRowsBefore lists u.val ++ edgeRow lists u ++ rest := by
    rw [edgeStream, hrows, List.flatMap_append, List.flatMap_cons]
    simp only [edgeRowsBefore, rest, List.append_assoc]
  refine ⟨(edgeRow lists u).drop q ++ rest, ?_⟩
  calc
    (edgeRowsBefore lists u.val ++ (edgeRow lists u).take q) ++ ((edgeRow lists u).drop q ++ rest) =
        edgeRowsBefore lists u.val ++ edgeRow lists u ++ rest := by
      simpa only [List.append_assoc] using congrArg (fun l => edgeRowsBefore lists u.val ++ l ++ rest)
        (List.take_append_drop q (edgeRow lists u))
    _ = edgeStream lists := hs.symm

/-- If a prefix's row decomposition has length `k`, it is precisely the first `k` edges. -/
theorem edgeRowsBefore_take_eq {N : ℕ} (lists : Fin N → List ℕ) (u : Fin N) (q k : ℕ)
    (hq : q ≤ (edgeRow lists u).length)
    (hk : (edgeRowsBefore lists u.val).length + q = k) :
    edgeRowsBefore lists u.val ++ (edgeRow lists u).take q = (edgeStream lists).take k := by
  have hp := List.prefix_iff_eq_take.mp (edgeRowsBefore_prefix lists u q)
  simpa only [List.length_append, List.length_take, Nat.min_eq_left hq, hk] using hp

end GraphMinor.Compute.Crossing
