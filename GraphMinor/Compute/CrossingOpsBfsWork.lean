module

public import GraphMinor.Compute.CrossingOpsBfsStep
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Charging BFS scans to vertices

The work charged to a scanned vertex is a fixed overhead plus its list length.
A scan adds exactly one vertex's charge. Since the history has no repeated vertices,
its total charge is at most the sum over all vertices.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Work already charged to the scanned prefix of the queue history. -/
def bfsScannedWork {N : ℕ} (nbrs : Fin N → List (Fin N))
    (items : List (Fin N)) (head : ℕ) : ℕ :=
  ((items.take head).map (fun v => 19 + 27 * (nbrs v).length)).sum

/-- Advancing the head charges exactly the vertex just scanned, regardless of new discoveries. -/
theorem bfsScannedWork_scan {N : ℕ} (nbrs : Fin N → List (Fin N))
    (items fresh : List (Fin N)) {head : ℕ} (pending : head < items.length) :
    bfsScannedWork nbrs (items ++ fresh) (head + 1) =
      bfsScannedWork nbrs items head + 19 + 27 * (nbrs items[head]).length := by
  have hp : (items ++ fresh).take (head + 1) = items.take (head + 1) := by
    rw [List.take_append_of_le_length (by omega)]
  simp only [bfsScannedWork, hp, List.take_succ_eq_append_getElem pending,
    List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
  omega

/-- The work of a duplicate-free scanned prefix is bounded by the sum over all vertices. -/
theorem bfsScannedWork_le {N : ℕ} (nbrs : Fin N → List (Fin N))
    (items : List (Fin N)) (head : ℕ) (hnd : items.Nodup) :
    bfsScannedWork nbrs items head ≤ ∑ v : Fin N, (19 + 27 * (nbrs v).length) := by
  classical
  let l := items.take head
  have hl : l.Nodup := hnd.take
  change (l.map _).sum ≤ _
  rw [← List.sum_toFinset _ hl]
  exact Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)

end GraphMinor.Compute.Crossing
