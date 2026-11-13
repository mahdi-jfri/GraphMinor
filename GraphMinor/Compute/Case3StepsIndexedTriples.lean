module

public import GraphMinor.Compute.Case3StepsPairTriples

/-!
# Copying a list of stored pair records

Each pair index selects three adjacent input words. Concatenating these
slices describes the exact member record buffer. For valid indices the
slices have three words each and retain the full original multiplicities.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- The three input words at a stored pair index. -/
def case3EncodedPairTriple {n : ℕ} (D : MultiDigraph n) (j : ℕ) : List ℕ :=
  (D.enc.drop (2 + 3 * j)).take 3

/-- Concatenate the unchanged input records selected by an index list. -/
def case3IndexedTriples {n : ℕ} (D : MultiDigraph n) (indices : List ℕ) : List ℕ :=
  indices.flatMap (case3EncodedPairTriple D)

/-- At a valid index, the selected words are precisely the full pair record. -/
theorem case3EncodedPairTriple_eq {n : ℕ} (D : MultiDigraph n) (j : Fin D.numActivePairs) :
    case3EncodedPairTriple D j.1 = case3PairTriple D j := by
  unfold case3EncodedPairTriple
  rw [case3PairTriple_enc_split D j, List.append_assoc,
    ← case3PairTriple_prefix_length D j, List.drop_left,
    ← case3PairTriple_length D j, List.take_left]

/-- Copying a leading index prepends exactly its three input words. -/
theorem case3IndexedTriples_cons {n : ℕ} (D : MultiDigraph n) (j : ℕ) (indices : List ℕ) :
    case3IndexedTriples D (j :: indices) =
      case3EncodedPairTriple D j ++ case3IndexedTriples D indices := rfl

/-- Every valid selected record contributes exactly three words. -/
theorem case3IndexedTriples_length {n : ℕ} (D : MultiDigraph n) (indices : List ℕ)
    (hvalid : ∀ j ∈ indices, j < D.numActivePairs) :
    (case3IndexedTriples D indices).length = 3 * indices.length := by
  induction indices with
  | nil => rfl
  | cons j js ih =>
    rw [case3IndexedTriples_cons, List.length_append,
      case3EncodedPairTriple_eq D ⟨j, hvalid j List.mem_cons_self⟩,
      case3PairTriple_length, ih (fun k hk => hvalid k (List.mem_cons_of_mem _ hk))]
    simp only [List.length_cons]
    omega

end GraphMinor.Compute
