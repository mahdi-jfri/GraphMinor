module

public import GraphMinor.Compute.GM06Alg34PayloadSpace
import Mathlib.Tactic.Ring

/-!
# Polynomial bounds for complete payload construction

The number of supplied cells, the sum of the vertex and edge counts,
and the input suffix length are bounded by the original size. These
bounds turn the sum of serialization scans into a single cubic bound.
The new payload size also fits the same cubic word reservation.
-/

public section
namespace GraphMinor.Compute

private theorem size_capacity (n : ℕ) : 2 * n + n * (n + 2) ≤ (n + 2) ^ 3 := by
  ring_nf
  omega

/-- The size of the induced drawing fits the original cubic reservation. -/
theorem gm06Induced_size_le_capacity (x : GM06DrawingData) (vs : List (Fin x.n)) :
    (x.inducedData vs).size ≤ gm06PayloadCapacity x :=
  (gm06Induced_size_le x vs).trans (size_capacity x.size)

private theorem writer_budget (n : ℕ) :
    34 * n + (26 * (n * n) + 23 * n + (18 * n + 72) * n + 99) * n +
      60 * n + 74 ≤ 200 * (n + 2) ^ 3 := by
  ring_nf
  omega

/-- The exact sum of section-writer bounds is cubic in the old input size. -/
theorem gm06PayloadWriteTime_le (x : GM06DrawingData) (vs : List (Fin x.n)) :
    17 * (x.inducedData vs).endpointWords.length +
      (26 * (x.cellCount * x.cellCount) + 23 * x.cellCount +
        (18 * x.cellCount + 72) * (x.n + x.ends.length) + 99) * x.cellCount +
      60 * (x.cuffWords.length + x.divisionWords.length) + 74 ≤
      200 * (x.size + 2) ^ 3 := by
  have hN := x.cellCount_le_size
  have hnm : x.n + x.ends.length ≤ x.size := by
    simp only [GM06DrawingData.cellCount] at hN
    omega
  have he : (x.inducedData vs).ends.length ≤ x.ends.length := by
    rw [x.inducedData_ends_length, ← gm06EdgeMask_sum]
    exact gm06EdgeMask_sum_le x vs
  have hep : 17 * (x.inducedData vs).endpointWords.length ≤ 34 * x.size := by
    rw [(x.inducedData vs).endpointWords_length]
    have hm := x.counts_le_size.2.1
    omega
  have hsuf : x.cuffWords.length + x.divisionWords.length ≤ x.size := by
    have hw := x.words_length
    have hh := x.words_length_le_size
    omega
  have hsq := Nat.mul_le_mul hN hN
  have hinner := Nat.mul_le_mul (show 18 * x.cellCount + 72 ≤ 18 * x.size + 72 by omega) hnm
  have hscan := Nat.mul_le_mul (show
      26 * (x.cellCount * x.cellCount) + 23 * x.cellCount +
        (18 * x.cellCount + 72) * (x.n + x.ends.length) + 99 ≤
      26 * (x.size * x.size) + 23 * x.size + (18 * x.size + 72) * x.size + 99 by omega) hN
  exact (show _ ≤ 34 * x.size +
      (26 * (x.size * x.size) + 23 * x.size + (18 * x.size + 72) * x.size + 99) * x.size +
      60 * x.size + 74 by omega).trans (writer_budget x.size)

end GraphMinor.Compute
