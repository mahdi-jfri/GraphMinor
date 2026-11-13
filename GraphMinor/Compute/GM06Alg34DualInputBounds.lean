module

public import GraphMinor.Compute.GM06Alg34DualSourcePrepare

/-!
# Supplied count bounds for dual preparation

The encoded division includes a length word per block, so its block
count is bounded by the input size. Together with the cuff-length
bound and the header counts, this provides the logarithmic-word
limits needed by the class and incidence preparation passes.
-/

public section
namespace GraphMinor.Compute

/-- The supplied number of division blocks is at most the drawing input size. -/
theorem gm06Dual_division_length_le_size (x : GM06DrawingData) : x.division.length ≤ x.size := by
  have hwords := x.words_length
  have hsize := x.words_length_le_size
  have hblocks := gm06BlockSection_count_le_length x.raw.division
  have hdivwords : x.divisionWords.length = 1 +
      (x.raw.division.flatMap GM06DrawingData.listWords).length := by
    rw [x.divisionWords_eq]
    simp only [List.length_cons]
    omega
  have hraw : x.raw.division.length = x.division.length := by simp [GM06DrawingData.raw]
  omega

/-- A header or cuff count bounded by the input size has two spare word values. -/
theorem gm06Dual_count_span_lt_wordSize (x : GM06DrawingData) {c k : ℕ}
    (hc : 2 ≤ c) (hk : k ≤ x.size) : k + 2 < 2 ^ wordSize c x.size := by
  have hh := two_mul_lt_two_pow_wordSize (n := x.size) hc
  omega

/-- Doubled cuff positions and their following gaps fit logarithmic constructor words. -/
theorem gm06Dual_double_cuff_lt_wordSize (x : GM06DrawingData) {c k : ℕ}
    (hc : 2 ≤ c) (hk : k ≤ x.size) : 2 * k + 1 < 2 ^ wordSize c x.size := by
  have hh := two_mul_lt_two_pow_wordSize (n := x.size) hc
  omega

end GraphMinor.Compute
