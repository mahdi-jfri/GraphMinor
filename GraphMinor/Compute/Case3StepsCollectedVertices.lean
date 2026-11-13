module

public import GraphMinor.Compute.Case3StepsBoundaryKeys

/-!
# Buffers for ordered member vertices

The vertex scan keeps the vertices already found at the front of a buffer.
Unused entries are zero. The next present vertex fills the first unused entry.
This supplies the ordered vertex lists used in Graph Minors XIII, (9.9), step 5,
pp. 105–106.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- A vertex buffer after scanning the first `k` vertices. -/
noncomputable def case3CollectedVertices {n : ℕ} (S : Finset (Fin n)) (k : ℕ) : List ℕ :=
  (case3BoundaryPrefix S k).map Fin.val ++
    List.replicate (n - (case3BoundaryPrefix S k).length) 0

/-- The collected prefix fits in the vertex buffer. -/
theorem case3BoundaryPrefix_length_le_n {n : ℕ} (S : Finset (Fin n)) (k : ℕ) :
    (case3BoundaryPrefix S k).length ≤ n :=
  (case3BoundaryPrefix_length_le S k).trans (by simpa only [Fintype.card_fin] using Finset.card_le_univ S)

/-- A collected vertex buffer always has the original vertex count as its length. -/
theorem case3CollectedVertices_length {n : ℕ} (S : Finset (Fin n)) (k : ℕ) :
    (case3CollectedVertices S k).length = n := by
  have h := case3BoundaryPrefix_length_le_n S k
  simp only [case3CollectedVertices, List.length_append, List.length_map,
    List.length_replicate]
  omega

/-- Before scanning, all buffer entries are zero. -/
theorem case3CollectedVertices_zero {n : ℕ} (S : Finset (Fin n)) :
    case3CollectedVertices S 0 = List.replicate n 0 := by
  simp [case3CollectedVertices, case3BoundaryPrefix_zero]

private theorem paddedVertices_set (pre : List ℕ) (v n : ℕ) (hlen : pre.length < n) :
    (pre ++ List.replicate (n - pre.length) 0).set pre.length v =
      (pre ++ [v]) ++ List.replicate (n - (pre.length + 1)) 0 := by
  rw [List.set_append_right _ _ (by omega)]
  simp only [Nat.sub_self]
  rw [show n - pre.length = (n - (pre.length + 1)) + 1 by omega,
    List.replicate_succ, List.set_cons_zero]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- A present vertex occupies the next unused slot. -/
theorem case3CollectedVertices_set {n : ℕ} (S : Finset (Fin n)) (k : ℕ)
    (hk : k < n) (hmem : (⟨k, hk⟩ : Fin n) ∈ S) :
    (case3CollectedVertices S k).set (case3BoundaryPrefix S k).length k =
      case3CollectedVertices S (k + 1) := by
  have hs := case3BoundaryPrefix_succ S k hk
  simp only [hmem, ↓reduceIte] at hs
  have hlen : (case3BoundaryPrefix S k).length < n := by
    have hle := case3BoundaryPrefix_length_le_n S (k + 1)
    rw [hs, List.length_append, List.length_singleton] at hle
    omega
  unfold case3CollectedVertices
  rw [hs, List.map_append, List.map_cons, List.map_nil, List.length_append,
    List.length_singleton]
  simpa only [List.length_map] using
    paddedVertices_set ((case3BoundaryPrefix S k).map Fin.val) k n
      (by simpa only [List.length_map] using hlen)

/-- An absent vertex leaves the buffer unchanged. -/
theorem case3CollectedVertices_skip {n : ℕ} (S : Finset (Fin n)) (k : ℕ)
    (hk : k < n) (hmem : (⟨k, hk⟩ : Fin n) ∉ S) :
    case3CollectedVertices S (k + 1) = case3CollectedVertices S k := by
  unfold case3CollectedVertices
  rw [case3BoundaryPrefix_succ S k hk]
  simp only [hmem, ↓reduceIte, List.append_nil]

/-- At the end, the buffer starts with the full increasing vertex list. -/
theorem case3CollectedVertices_done {n : ℕ} (S : Finset (Fin n)) :
    case3CollectedVertices S n =
      (case3BoundaryVertices S).map Fin.val ++ List.replicate (n - S.card) 0 := by
  simp only [case3CollectedVertices, case3BoundaryPrefix_done, case3BoundaryVertices_length]

end GraphMinor.Compute
