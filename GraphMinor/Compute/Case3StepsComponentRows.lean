module

public import GraphMinor.Compute.Case3StepsComponents

/-!
# Storage for the outside components

The member computation in step (5) stores one row for each vertex. A core
vertex has a zero row. Any other vertex has the indicator row of its outside
component. Rows have the same length as the graph's vertex set, so searches
can be copied into a single flat array.
-/

@[expose] public section

namespace GraphMinor.Compute

open Classical

/-- The component row belonging to a seed. Core vertices have zero rows. -/
noncomputable def case3ComponentRow (x : Alg81Input) (Z : Finset (Fin x.n))
    (u : Fin x.n) : List ℕ :=
  if u ∈ Z then List.replicate x.n 0 else bitSetList (compOutside x Z u)

/-- All component rows in vertex order. -/
noncomputable def case3ComponentRows (x : Alg81Input) (Z : Finset (Fin x.n)) : List ℕ :=
  (List.finRange x.n).flatMap (case3ComponentRow x Z)

/-- Every component row has exactly one word per vertex. -/
theorem case3ComponentRow_length (x : Alg81Input) (Z : Finset (Fin x.n)) (u : Fin x.n) :
    (case3ComponentRow x Z u).length = x.n := by
  unfold case3ComponentRow
  split_ifs <;> simp only [List.length_replicate, length_bitSetList]

/-- The first `k` rows occupy `k n` words. -/
theorem case3ComponentRows_prefix_length (x : Alg81Input) (Z : Finset (Fin x.n))
    (k : ℕ) (hk : k ≤ x.n) :
    (((List.finRange x.n).take k).flatMap (case3ComponentRow x Z)).length = k * x.n := by
  have haux : ∀ L : List (Fin x.n), (L.flatMap (case3ComponentRow x Z)).length = L.length * x.n := by
    intro L
    induction L with
    | nil => simp
    | cons u L ih =>
      simp only [List.flatMap_cons, List.length_append, case3ComponentRow_length, ih,
        List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
  rw [haux, List.length_take, List.length_finRange, Nat.min_eq_left hk]

/-- The complete table contains `n²` words. -/
theorem case3ComponentRows_length (x : Alg81Input) (Z : Finset (Fin x.n)) :
    (case3ComponentRows x Z).length = x.n * x.n := by
  have h := case3ComponentRows_prefix_length x Z x.n le_rfl
  have ht : (List.finRange x.n).take x.n = List.finRange x.n :=
    List.take_of_length_le (by simp only [List.length_finRange]; exact le_rfl)
  rw [ht] at h
  exact h

/-- Advancing the row loop appends exactly the next component row. -/
theorem case3ComponentRows_prefix_succ (x : Alg81Input) (Z : Finset (Fin x.n))
    (k : ℕ) (hk : k < x.n) :
    (((List.finRange x.n).take (k + 1)).flatMap (case3ComponentRow x Z)) =
      (((List.finRange x.n).take k).flatMap (case3ComponentRow x Z)) ++
        case3ComponentRow x Z ⟨k, hk⟩ := by
  rw [take_add_one_eq_append_getElem (List.finRange x.n) k (by simpa only [List.length_finRange] using hk)]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.getElem_finRange]
  apply congrArg (fun u : Fin x.n =>
    (((List.finRange x.n).take k).flatMap (case3ComponentRow x Z)) ++ case3ComponentRow x Z u)
  exact Fin.ext rfl

/-- Before the next row is written, the remaining zero storage splits into
that row and the storage for the later rows. -/
theorem case3ComponentRows_storage_succ (x : Alg81Input) (Z : Finset (Fin x.n))
    (k : ℕ) (hk : k < x.n) :
    (((List.finRange x.n).take k).flatMap (case3ComponentRow x Z)) ++
        List.replicate ((x.n - k) * x.n) 0 =
      (((List.finRange x.n).take k).flatMap (case3ComponentRow x Z)) ++
        List.replicate x.n 0 ++ List.replicate ((x.n - (k + 1)) * x.n) 0 := by
  have hsub : x.n - k = 1 + (x.n - (k + 1)) := by omega
  rw [hsub, Nat.add_mul, Nat.one_mul, List.replicate_add, List.append_assoc]

/-- After the last row there is no unused storage. -/
theorem case3ComponentRows_storage_done (x : Alg81Input) (Z : Finset (Fin x.n)) :
    (((List.finRange x.n).take x.n).flatMap (case3ComponentRow x Z)) ++
        List.replicate ((x.n - x.n) * x.n) 0 = case3ComponentRows x Z := by
  simp only [Nat.sub_self, Nat.zero_mul, List.replicate_zero, List.append_nil]
  rw [List.take_of_length_le (by simp only [List.length_finRange]; exact le_rfl)]
  rfl

/-- All row entries fit in any word that contains zero and one. -/
theorem case3ComponentRow_words {w : ℕ} (x : Alg81Input) (Z : Finset (Fin x.n))
    (u : Fin x.n) (hw : 1 < 2 ^ w) :
    ∀ z ∈ case3ComponentRow x Z u, z < 2 ^ w := by
  intro z hz
  unfold case3ComponentRow at hz
  split_ifs at hz with hu
  · have heq := (List.mem_replicate.mp hz).2
    subst z
    omega
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
    exact (getElem_bitSetList_le_one _ i hi).trans_lt hw

end GraphMinor.Compute
