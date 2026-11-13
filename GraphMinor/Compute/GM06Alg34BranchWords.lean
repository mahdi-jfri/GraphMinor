module

public import GraphMinor.Compute.GM06Alg34ComponentInputs
public import GraphMinor.Compute.GM06Alg34PayloadBudget
public import GraphMinor.Compute.GM06Alg34WordBounds

/-!
# Serialized component branch records and their bounds

Write each canonical component payload as a length-prefixed word list.
The induced payload bound applies to every component. Multiplying it
by the supplied vertex count therefore bounds all queued branches,
including the empty graph. All fields remain plain finite input data.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- One complete component payload preceded by its word length. -/
def gm06ComponentRecordWords (x : GM06DrawingData) (a : Fin x.n) : List ℕ :=
  GM06DrawingData.listWords (x.componentData a).words

/-- Component records selected by canonical roots in a supplied source list. -/
def gm06ComponentQueueWords (x : GM06DrawingData) (V : List (Fin x.n)) : List ℕ :=
  (V.filter x.isComponentRoot).flatMap (gm06ComponentRecordWords x)

/-- Reserve one maximum-size record for each supplied vertex and one extra record. -/
def gm06BranchCapacity (x : GM06DrawingData) : ℕ :=
  (x.n + 1) * (gm06PayloadCapacity x + 1)

/-- Every component input obeys the existing cubic induced-payload bound. -/
theorem gm06ComponentData_size_le_capacity (x : GM06DrawingData) (a : Fin x.n) :
    (x.componentData a).size ≤ gm06PayloadCapacity x :=
  gm06Induced_size_le_capacity x (x.componentVertices a)

/-- A component record has at most one length word beyond the payload bound. -/
theorem gm06ComponentRecordWords_length_le (x : GM06DrawingData) (a : Fin x.n) :
    (gm06ComponentRecordWords x a).length ≤ gm06PayloadCapacity x + 1 := by
  have hh := (x.componentData a).words_length_le_size.trans (gm06ComponentData_size_le_capacity x a)
  simp only [gm06ComponentRecordWords, GM06DrawingData.listWords, List.length_cons]
  omega

/-- Every word in a component record is bounded by the parent payload capacity. -/
theorem gm06ComponentRecordWords_word_le (x : GM06DrawingData) (a : Fin x.n)
    {v : ℕ} (hv : v ∈ gm06ComponentRecordWords x a) : v ≤ gm06PayloadCapacity x := by
  rcases List.mem_cons.mp hv with rfl | hv
  · exact (x.componentData a).words_length_le_size.trans (gm06ComponentData_size_le_capacity x a)
  · exact (gm06Words_le_size (x.componentData a) v hv).trans (gm06ComponentData_size_le_capacity x a)

/-- The record stream is bounded by one maximum-size record per scanned source. -/
theorem gm06ComponentQueueWords_length_le (x : GM06DrawingData) (V : List (Fin x.n)) :
    (gm06ComponentQueueWords x V).length ≤ V.length * (gm06PayloadCapacity x + 1) := by
  induction V with
  | nil => simp only [gm06ComponentQueueWords, List.filter_nil, List.flatMap_nil, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons a V ih =>
    have hh := gm06ComponentRecordWords_length_le x a
    cases ht : x.isComponentRoot a <;>
      simp only [gm06ComponentQueueWords, List.filter_cons, ht, Bool.false_eq_true,
        ↓reduceIte, List.flatMap_cons, List.length_append, List.length_cons] at *
    · exact ih.trans (Nat.mul_le_mul_right _ (Nat.le_succ _))
    · rw [Nat.add_mul, Nat.one_mul]
      omega

/-- All canonical component records fit the branch queue reservation. -/
theorem gm06ComponentQueueWords_length_lt_capacity (x : GM06DrawingData) :
    (gm06ComponentQueueWords x (List.finRange x.n)).length < gm06BranchCapacity x := by
  have hh := gm06ComponentQueueWords_length_le x (List.finRange x.n)
  simp only [List.length_finRange] at hh
  unfold gm06BranchCapacity
  rw [Nat.add_mul, Nat.one_mul]
  omega

end GraphMinor.Compute
