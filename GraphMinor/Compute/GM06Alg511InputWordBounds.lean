module

public import GraphMinor.Compute.GM06Alg511WindingInput
public import GraphMinor.Compute.GM06Alg511TurnWords
import GraphMinor.Compute.GM06Alg511SelectField
import GraphMinor.Compute.GM06Alg511TurnLayout
import GraphMinor.Compute.GM06Alg511Numerator
import Mathlib.Tactic

/-!
# Word bounds when composing initialization with orientation

The orientation phase of VI (5.11), page 134, reuses integer turn
words already present in the supplied input. Their count and values
are bounded by the input code. Products of computed words fit after
a fixed enlargement of the word size, so no hypothesis about an
unknown computed answer is needed for the composition.
-/

public section
namespace GraphMinor.Compute

/-- Every magnitude word in the flattened turn row occurs in the
original supplied winding input. -/
theorem gm06Alg511TurnWords_mem_input (x : GM06Alg511WindingInput) (v : ℕ)
    (hv : v ∈ gm06Alg511TurnWords x.edgeTurns) : v ∈ gm06Alg511WindingWords x := by
  obtain ⟨z, hz, hvz⟩ := List.mem_flatMap.mp hv
  apply gm06Alg511_mem_encoded_row
    (rows := [gm06Alg511Words x.drawing, gm06EncodeRows (x.edgeTurns.map gm06Alg511IntegerWords)])
    (row := gm06EncodeRows (x.edgeTurns.map gm06Alg511IntegerWords)) (by simp)
  exact gm06Alg511_mem_encoded_row (List.mem_map.mpr ⟨z, hz, rfl⟩) hvz

/-- The count of flattened turn words is bounded by the length of
the original supplied winding input. -/
theorem gm06Alg511TurnWordCount_le_input (x : GM06Alg511WindingInput) :
    2 * x.edgeTurns.length ≤ (gm06Alg511WindingWords x).length := by
  have hrow : gm06EncodeRows (x.edgeTurns.map gm06Alg511IntegerWords) ∈
      [gm06Alg511Words x.drawing, gm06EncodeRows (x.edgeTurns.map gm06Alg511IntegerWords)] := by simp
  have hlen := gm06Alg511_encoded_row_length_le hrow
  rw [gm06Alg511TurnCode_length] at hlen
  exact (by omega : 2 * x.edgeTurns.length ≤ 1 + 3 * x.edgeTurns.length).trans hlen

/-- Two products of word-sized values fit in three times that word
size. This covers both unsigned cross-multiplication sums. -/
theorem gm06Alg511SumProducts_lt_triple {w a b c d : ℕ} (hw : 0 < w)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) (hc : c < 2 ^ w) (hd : d < 2 ^ w) :
    a * b + c * d < 2 ^ (3 * w) := by
  have hfirst := gm06Alg511ProductAdd_lt_double ha hb (Nat.two_pow_pos w)
  have hsecond := gm06Alg511ProductAdd_lt_double hc hd (Nat.two_pow_pos w)
  simp only [Nat.add_zero] at hfirst hsecond
  calc
    a * b + c * d < 2 ^ (2 * w) + 2 ^ (2 * w) := Nat.add_lt_add hfirst hsecond
    _ = 2 ^ (2 * w + 1) := by rw [Nat.pow_succ]; ring
    _ ≤ 2 ^ (3 * w) := Nat.pow_le_pow_right (by decide) (by omega)

end GraphMinor.Compute
