module

public import GraphMinor.Compute.Algorithm99OrderRank
import Mathlib.Data.List.GetD
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Conv

/-!
# Reading a stable grouping at its bucket positions

The destination position used by the scattering program is the length of all
earlier buckets plus the number of earlier entries in the current bucket.
Splitting both the list of buckets and the source list at these positions
shows that the grouped list contains the original entry there.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Stable grouping of a list by a vertex-valued key. -/
def alg99StableGroup {α : Type*} {n : ℕ} (xs : List α) (key : α → Fin n) : List α :=
  (List.finRange n).flatMap (fun u => xs.filter (fun x => decide (key x = u)))

private theorem count_key_eq99 {α : Type*} {n : ℕ} (xs : List α)
    (key : α → Fin n) (u : Fin n) :
    (xs.map key).count u = (xs.filter (fun x => decide (key x = u))).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : key x = u
    · simp [h, ih]
    · simp [h, ih]

private theorem group_prefix_length99 {α : Type*} {n : ℕ} (xs : List α)
    (key : α → Fin n) (k : ℕ) (hk : k ≤ n) :
    (((List.finRange n).take k).flatMap (fun u =>
      xs.filter (fun x => decide (key x = u)))).length =
        ((xs.map key).filter (fun u => decide (u.1 < k))).length := by
  simp only [List.length_flatMap]
  simp_rw [← count_key_eq99 xs key]
  rw [List.map_take, ← List.ofFn_eq_map]
  exact alg99_prefix_counts (xs.map key) k hk

/-- Reading the stable grouping at a source entry's bucket position returns
that source entry. No distinctness assumption on the source list is needed. -/
theorem alg99StableGroup_getD_position {α : Type*} {n : ℕ} (xs : List α)
    (key : α → Fin n) (i : Fin xs.length) (d : α) :
    (alg99StableGroup xs key).getD
      (alg99BucketPosition (xs.map key) ⟨i.1, by simp⟩) d = xs[i.1] := by
  let u := key xs[i.1]
  let pre := ((List.finRange n).take u.1).flatMap
    (fun v => xs.filter (fun x => decide (key x = v)))
  let rowPre := (xs.take i.1).filter (fun x => decide (key x = u))
  let rowPost := (xs.drop (i.1 + 1)).filter (fun x => decide (key x = u))
  let post := ((List.finRange n).drop (u.1 + 1)).flatMap
    (fun v => xs.filter (fun x => decide (key x = v)))
  have hrow : xs.filter (fun x => decide (key x = u)) = rowPre ++ xs[i.1] :: rowPost := by
    have hsplit : xs = xs.take i.1 ++ xs[i.1] :: xs.drop (i.1 + 1) := by
      rw [← List.drop_eq_getElem_cons i.2, List.take_append_drop]
    conv_lhs => rw [hsplit]
    simp only [List.filter_append, List.filter_cons]
    simp only [u, decide_true, ↓reduceIte, rowPre, rowPost]
  have hsplit : alg99StableGroup xs key = pre ++ (rowPre ++ xs[i.1] :: rowPost) ++ post := by
    have hfin : List.finRange n = (List.finRange n).take u.1 ++
        u :: (List.finRange n).drop (u.1 + 1) := by
      have hu : u.1 < (List.finRange n).length := by simp
      have hsplit := List.take_append_drop u.1 (List.finRange n)
      rw [List.drop_eq_getElem_cons hu] at hsplit
      simpa using hsplit.symm
    unfold alg99StableGroup
    rw [hfin, List.flatMap_append, List.flatMap_cons, hrow]
    simp only [pre, post, List.append_assoc]
  have hpre : pre.length = alg99BucketStart (xs.map key) u := by
    exact group_prefix_length99 xs key u.1 (Nat.le_of_lt u.2)
  have hrowPre : rowPre.length = ((xs.map key).take i.1).count u := by
    rw [← List.map_take]
    exact (count_key_eq99 (xs.take i.1) key u).symm
  have hpos : alg99BucketPosition (xs.map key) ⟨i.1, by simp⟩ =
      pre.length + rowPre.length := by
    simp only [alg99BucketPosition, List.getElem_map, u, hpre, hrowPre]
  rw [hpos, hsplit, List.append_assoc, List.getD_append_right _ _ _ _ (by omega),
    Nat.add_sub_cancel_left, List.append_assoc,
    List.getD_append_right _ _ _ _ (by omega), Nat.sub_self]
  rfl

end GraphMinor.Compute
