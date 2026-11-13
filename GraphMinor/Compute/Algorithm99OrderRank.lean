module

import GraphMinor.Compute.Algorithm99OrderCounts

/-!
# Positions in a stable sort by edge tail

A tail bucket starts after all edges with a smaller tail. Within its bucket,
an edge follows exactly the earlier edges with the same tail. These positions
are in bounds and distinct. Thus a scattering pass cannot overwrite an earlier
edge, including when several edges have the same endpoints.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Number of source entries whose key is smaller than `u`. -/
def alg99BucketStart {n : ℕ} (keys : List (Fin n)) (u : Fin n) : ℕ :=
  (keys.filter (fun v => decide (v < u))).length

/-- Position of an edge in a stable grouping by tail. -/
def alg99BucketPosition {n : ℕ} (keys : List (Fin n)) (i : Fin keys.length) : ℕ :=
  alg99BucketStart keys keys[i.1] + (keys.take i.1).count keys[i.1]

private theorem length_filter_lt_succ99 {n : ℕ} (keys : List (Fin n))
    (k : Fin n) :
    (keys.filter (fun v => decide (v.1 < k.1 + 1))).length =
      (keys.filter (fun v => decide (v.1 < k.1))).length + keys.count k := by
  induction keys with
  | nil => simp
  | cons v keys ih =>
    simp only [List.filter_cons, List.count_cons]
    by_cases hlt : v.1 < k.1
    · have hs : v.1 < k.1 + 1 := by omega
      have hne : v ≠ k := by intro h; subst v; omega
      simp only [hlt, hs, hne, beq_iff_eq, decide_true, ↓reduceIte, List.length_cons, Nat.add_zero]
      rw [ih]
      omega
    · by_cases heq : v = k
      · subst v
        simp only [Nat.lt_irrefl, Nat.lt_succ_self, decide_true, decide_false,
          Bool.false_eq_true, ↓reduceIte, List.length_cons, BEq.rfl]
        rw [ih]
        omega
      · have hs : ¬ v.1 < k.1 + 1 := by
          have hne : v.1 ≠ k.1 := fun h => heq (Fin.ext h)
          omega
        simp only [hlt, hs, heq, beq_iff_eq, decide_false,
          Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        exact ih

/-- The prefix sums of the occurrence counts give the bucket starts. This
connects the counting and prefix-sum programs to the stable destination ranks. -/
theorem alg99_prefix_counts {n : ℕ} (keys : List (Fin n)) (k : ℕ) (hk : k ≤ n) :
    ((List.ofFn (fun v : Fin n => keys.count v)).take k).sum =
      (keys.filter (fun v => decide (v.1 < k))).length := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hkn : k < n := by omega
    have hi := ih (by omega)
    rw [List.take_add_one,
      List.getElem?_eq_getElem (by simpa using hkn)]
    simp only [Option.toList_some, List.sum_append, List.sum_cons, List.sum_nil,
      Nat.add_zero, List.getElem_ofFn]
    rw [hi, length_filter_lt_succ99 keys ⟨k, hkn⟩]

/-- The counts sum to the length of the key stream. -/
theorem alg99_sum_counts {n : ℕ} (keys : List (Fin n)) :
    (List.ofFn (fun v : Fin n => keys.count v)).sum = keys.length := by
  have h := alg99_prefix_counts keys n (Nat.le_refl n)
  rw [List.take_of_length_le (by simp),
    List.filter_eq_self.mpr (fun (v : Fin n) _ => by simp)] at h
  exact h

/-- A bucket and all buckets before it fit in the source length. -/
theorem alg99BucketStart_add_count_le {n : ℕ} (keys : List (Fin n)) (u : Fin n) :
    alg99BucketStart keys u + keys.count u ≤ keys.length := by
  induction keys with
  | nil => simp [alg99BucketStart]
  | cons v keys ih =>
    simp only [alg99BucketStart, List.filter_cons, List.count_cons, List.length_cons] at *
    by_cases hlt : v < u
    · have hne : v ≠ u := ne_of_lt hlt
      simp [hlt, hne] at *
      omega
    · by_cases heq : v = u
      · simpa [hlt, heq, Nat.add_assoc] using Nat.succ_le_succ ih
      · simpa [hlt, heq] using ih.trans (Nat.le_succ _)

/-- The whole bucket of a smaller key ends before a larger key's bucket. -/
theorem alg99BucketStart_add_count_le_of_lt {n : ℕ} (keys : List (Fin n))
    {u v : Fin n} (huv : u < v) :
    alg99BucketStart keys u + keys.count u ≤ alg99BucketStart keys v := by
  induction keys with
  | nil => simp [alg99BucketStart]
  | cons x keys ih =>
    simp only [alg99BucketStart, List.filter_cons, List.count_cons] at *
    by_cases hxu : x < u
    · have hxv : x < v := hxu.trans huv
      have hne : x ≠ u := ne_of_lt hxu
      simp [hxu, hxv, hne] at *
      omega
    · by_cases heq : x = u
      · subst x
        simpa [huv, Nat.add_assoc] using Nat.succ_le_succ ih
      · by_cases hxv : x < v
        · simpa [hxu, heq, hxv] using ih.trans (Nat.le_succ _)
        · simpa [hxu, heq, hxv] using ih

/-- A prefix ending before an occurrence contains fewer copies of that key
than the whole list. -/
theorem alg99_count_take_lt {n : ℕ} (keys : List (Fin n)) (i : Fin keys.length) :
    (keys.take i.1).count keys[i.1] < keys.count keys[i.1] := by
  have hsplit := congrArg (List.count keys[i.1]) (List.take_append_drop i.1 keys)
  rw [List.count_append, List.drop_eq_getElem_cons i.2, List.count_cons] at hsplit
  simp only [BEq.rfl, ↓reduceIte] at hsplit
  omega

/-- Every stable bucket position is a valid destination index. -/
theorem alg99BucketPosition_lt {n : ℕ} (keys : List (Fin n)) (i : Fin keys.length) :
    alg99BucketPosition keys i < keys.length := by
  have hb := alg99BucketStart_add_count_le keys keys[i.1]
  have hp := alg99_count_take_lt keys i
  dsimp only [alg99BucketPosition]
  omega

/-- Earlier occurrences of a key have smaller positions within their bucket. -/
theorem alg99_count_take_lt_of_lt {n : ℕ} (keys : List (Fin n))
    (i j : Fin keys.length) (hij : i < j) :
    (keys.take i.1).count keys[i.1] < (keys.take j.1).count keys[i.1] := by
  have hle := List.Sublist.count_le keys[i.1]
    (List.take_sublist_take_left (l := keys) (show i.1 + 1 ≤ j.1 by omega))
  rw [List.take_add_one, List.getElem?_eq_getElem i.2, List.count_append] at hle
  simp only [Option.toList_some, List.count_singleton, BEq.rfl, ↓reduceIte] at hle
  omega

/-- A stable grouping assigns different destination positions to different
source indices. No assumption on distinct endpoints or positive degrees is used. -/
theorem alg99BucketPosition_injective {n : ℕ} (keys : List (Fin n)) :
    Function.Injective (alg99BucketPosition keys) := by
  have hkey : ∀ i j : Fin keys.length, keys[i.1] < keys[j.1] →
      alg99BucketPosition keys i < alg99BucketPosition keys j := by
    intro i j hij
    have hb := alg99BucketStart_add_count_le_of_lt keys hij
    have hp := alg99_count_take_lt keys i
    dsimp only [alg99BucketPosition]
    omega
  have hsame : ∀ i j : Fin keys.length, i < j → keys[i.1] = keys[j.1] →
      alg99BucketPosition keys i < alg99BucketPosition keys j := by
    intro i j hij heq
    have hp := alg99_count_take_lt_of_lt keys i j hij
    dsimp only [alg99BucketPosition]
    rw [← heq]
    omega
  intro i j heq
  have hk : keys[i.1] = keys[j.1] := by
    rcases lt_trichotomy keys[i.1] keys[j.1] with hlt | he | hgt
    · have := hkey i j hlt
      omega
    · exact he
    · have := hkey j i hgt
      omega
  rcases lt_trichotomy i j with hlt | he | hgt
  · have := hsame i j hlt hk
    omega
  · exact he
  · have := hsame j i hgt hk.symm
    omega

end GraphMinor.Compute
