module

public import GraphMinor.Compute.Case3StepsAttachmentBound

/-!
# Fixed-size keys for small boundaries

A boundary with at most three vertices is encoded by its size and its vertices
in increasing order, padded with zeroes. The size distinguishes padding from
a genuine vertex numbered zero. Equal keys therefore mean equal boundaries.
-/

@[expose] public section

namespace GraphMinor.Compute

open Classical

/-- Boundary vertices encountered before the scan reaches `k`. -/
noncomputable def case3BoundaryPrefix {n : ℕ} (S : Finset (Fin n)) (k : ℕ) : List (Fin n) :=
  ((List.finRange n).take k).filter (fun u => u ∈ S)

/-- The full increasing list of boundary vertices. -/
noncomputable def case3BoundaryVertices {n : ℕ} (S : Finset (Fin n)) : List (Fin n) :=
  (List.finRange n).filter (fun u => u ∈ S)

/-- A size word and three vertex slots. -/
noncomputable def case3BoundaryKey {n : ℕ} (S : Finset (Fin n)) : List ℕ :=
  S.card :: ((case3BoundaryVertices S).map Fin.val ++ List.replicate (3 - S.card) 0)

/-- The boundary list has one entry for each boundary vertex. -/
theorem case3BoundaryVertices_length {n : ℕ} (S : Finset (Fin n)) :
    (case3BoundaryVertices S).length = S.card := by
  have hnd : (case3BoundaryVertices S).Nodup := (List.nodup_finRange n).filter _
  have hfin : (case3BoundaryVertices S).toFinset = S := by
    ext u
    simp [case3BoundaryVertices]
  exact (List.toFinset_card_of_nodup hnd).symm.trans (congrArg Finset.card hfin)

/-- A boundary scan starts with no collected vertices. -/
theorem case3BoundaryPrefix_zero {n : ℕ} (S : Finset (Fin n)) :
    case3BoundaryPrefix S 0 = [] := by simp [case3BoundaryPrefix]

/-- Advancing the scan either appends the current boundary vertex or leaves
its collected list unchanged. -/
theorem case3BoundaryPrefix_succ {n : ℕ} (S : Finset (Fin n)) (k : ℕ) (hk : k < n) :
    case3BoundaryPrefix S (k + 1) = case3BoundaryPrefix S k ++
      (if (⟨k, hk⟩ : Fin n) ∈ S then [⟨k, hk⟩] else []) := by
  have hget : (List.finRange n)[k]'(by simpa only [List.length_finRange] using hk) = ⟨k, hk⟩ := by
    apply Fin.ext
    simp only [List.getElem_finRange, Fin.val_cast]
  unfold case3BoundaryPrefix
  rw [take_add_one_eq_append_getElem (List.finRange n) k (by simpa only [List.length_finRange] using hk),
    List.filter_append]
  simp only [hget, List.filter_cons, List.filter_nil, decide_eq_true_eq]

/-- Finishing the scan gives the full boundary list. -/
theorem case3BoundaryPrefix_done {n : ℕ} (S : Finset (Fin n)) :
    case3BoundaryPrefix S n = case3BoundaryVertices S := by
  unfold case3BoundaryPrefix case3BoundaryVertices
  rw [List.take_of_length_le (by simp only [List.length_finRange]; exact le_rfl)]

/-- The collected list never contains more vertices than the boundary. -/
theorem case3BoundaryPrefix_length_le {n : ℕ} (S : Finset (Fin n)) (k : ℕ) :
    (case3BoundaryPrefix S k).length ≤ S.card := by
  rw [← case3BoundaryVertices_length S]
  exact ((List.take_sublist k (List.finRange n)).filter _).length_le

/-- Small boundaries always occupy exactly four words. -/
theorem case3BoundaryKey_length {n : ℕ} (S : Finset (Fin n)) (hS : S.card ≤ 3) :
    (case3BoundaryKey S).length = 4 := by
  simp only [case3BoundaryKey, List.length_cons, List.length_append,
    List.length_map, case3BoundaryVertices_length, List.length_replicate]
  omega

/-- Every key word fits when the vertex numbers and size word fit. -/
theorem case3BoundaryKey_words {n w : ℕ} (S : Finset (Fin n)) (hS : S.card ≤ 3)
    (hw : 4 < 2 ^ w) (hn : n < 2 ^ w) :
    ∀ z ∈ case3BoundaryKey S, z < 2 ^ w := by
  intro z hz
  simp only [case3BoundaryKey, List.mem_cons, List.mem_append] at hz
  rcases hz with rfl | hz | hz
  · omega
  · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hz
    exact v.2.trans hn
  · have heq := (List.mem_replicate.mp hz).2
    subst z
    omega

/-- The first word records the size even when vertex zero is present. -/
theorem case3BoundaryKey_head {n : ℕ} (S : Finset (Fin n)) :
    (case3BoundaryKey S).headD 0 = S.card := rfl

/-- The partially written key has a zero header until the scan finishes. -/
noncomputable def case3BoundaryKeyPrefix {n : ℕ} (S : Finset (Fin n)) (k : ℕ) : List ℕ :=
  0 :: ((case3BoundaryPrefix S k).map Fin.val ++
    List.replicate (3 - (case3BoundaryPrefix S k).length) 0)

/-- A partial key still occupies four words. -/
theorem case3BoundaryKeyPrefix_length {n : ℕ} (S : Finset (Fin n)) (hS : S.card ≤ 3)
    (k : ℕ) : (case3BoundaryKeyPrefix S k).length = 4 := by
  have hle := (case3BoundaryPrefix_length_le S k).trans hS
  simp only [case3BoundaryKeyPrefix, List.length_cons, List.length_append,
    List.length_map, List.length_replicate]
  omega

private theorem paddedBoundary_set (pre : List ℕ) (v : ℕ) (hlen : pre.length < 3) :
    (0 :: (pre ++ List.replicate (3 - pre.length) 0)).set (pre.length + 1) v =
      0 :: ((pre ++ [v]) ++ List.replicate (3 - (pre.length + 1)) 0) := by
  rw [List.set_cons_succ, List.set_append_right _ _ (by omega)]
  simp only [Nat.sub_self]
  rw [show 3 - pre.length = (3 - (pre.length + 1)) + 1 by omega,
    List.replicate_succ, List.set_cons_zero]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- A present boundary vertex fills the next vacant slot. -/
theorem case3BoundaryKeyPrefix_set {n : ℕ} (S : Finset (Fin n)) (hS : S.card ≤ 3)
    (k : ℕ) (hk : k < n) (hmem : (⟨k, hk⟩ : Fin n) ∈ S) :
    (case3BoundaryKeyPrefix S k).set ((case3BoundaryPrefix S k).length + 1) k =
      case3BoundaryKeyPrefix S (k + 1) := by
  have hs := case3BoundaryPrefix_succ S k hk
  simp only [hmem, ↓reduceIte] at hs
  have hlen : (case3BoundaryPrefix S k).length < 3 := by
    have hle := (case3BoundaryPrefix_length_le S (k + 1)).trans hS
    rw [hs, List.length_append, List.length_singleton] at hle
    omega
  unfold case3BoundaryKeyPrefix
  rw [hs, List.map_append, List.map_cons, List.map_nil, List.length_append, List.length_singleton]
  have hp := paddedBoundary_set ((case3BoundaryPrefix S k).map Fin.val) k
    (by simpa only [List.length_map] using hlen)
  simpa only [List.length_map] using hp

/-- An absent vertex leaves the partial key unchanged. -/
theorem case3BoundaryKeyPrefix_skip {n : ℕ} (S : Finset (Fin n)) (k : ℕ)
    (hk : k < n) (hmem : (⟨k, hk⟩ : Fin n) ∉ S) :
    case3BoundaryKeyPrefix S (k + 1) = case3BoundaryKeyPrefix S k := by
  unfold case3BoundaryKeyPrefix
  rw [case3BoundaryPrefix_succ S k hk]
  simp only [hmem, ↓reduceIte, List.append_nil]

/-- Finishing the scan and writing the size gives the boundary key. -/
theorem case3BoundaryKeyPrefix_finish {n : ℕ} (S : Finset (Fin n)) :
    (case3BoundaryKeyPrefix S n).set 0 S.card = case3BoundaryKey S := by
  simp only [case3BoundaryKeyPrefix, case3BoundaryPrefix_done, List.set_cons_zero,
    case3BoundaryVertices_length, case3BoundaryKey]

/-- Equal boundary keys identify equal vertex sets. -/
theorem case3BoundaryKey_injective {n : ℕ} (S T : Finset (Fin n))
    (heq : case3BoundaryKey S = case3BoundaryKey T) : S = T := by
  have hcard : S.card = T.card := congrArg (fun L : List ℕ => L.headD 0) heq
  have htail := congrArg (fun L : List ℕ => L.tail.take S.card) heq
  have hlenS : ((case3BoundaryVertices S).map Fin.val).length = S.card := by
    rw [List.length_map, case3BoundaryVertices_length]
  have hlenT : ((case3BoundaryVertices T).map Fin.val).length = S.card := by
    rw [List.length_map, case3BoundaryVertices_length, hcard]
  simp only [case3BoundaryKey, List.tail_cons, ← hlenS, List.take_left] at htail
  rw [show ((case3BoundaryVertices S).map Fin.val).length =
    ((case3BoundaryVertices T).map Fin.val).length by omega, List.take_left] at htail
  ext u
  have hmem : u.1 ∈ (case3BoundaryVertices S).map Fin.val ↔
      u.1 ∈ (case3BoundaryVertices T).map Fin.val := by rw [htail]
  simpa [case3BoundaryVertices, List.mem_map, Fin.val_inj] using hmem

end GraphMinor.Compute
