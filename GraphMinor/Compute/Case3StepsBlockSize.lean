module

public import GraphMinor.Compute.Case3StepsBranchRecordBounds

/-!
# Linear block size and its word bound

A valid wall encoding has linear vertex size. The compass vertex and edge
sections add one and three words per item. Both member scans share a buffer
of capacity 24 times the ambient vertex and edge sum. These bounds give a
fixed linear size for the completed block and for its tagged output.
-/

public section

namespace GraphMinor.Compute

/-- The computed sections and reserved member capacity bound the block by
a fixed constant times the ambient vertex and full-edge count. -/
theorem case3Block_length_le {h N M : ℕ} {D : MultiDigraph N}
    (W : WallOfHeight h D) (hW : W.IsValid) (Kv : List ℕ)
    (Ke : List (ℕ × ℕ × ℕ)) (corners : List ℕ) (members : List Case3MemberRecord)
    (hv : Kv.length ≤ N) (he : Ke.length ≤ M) (hc : corners.length = 4)
    (hr : (members.flatMap Case3MemberRecord.enc).length ≤ 24 * (N + M + 1)) :
    (encCase3Block W Kv Ke corners members).length ≤ 40 * (N + M + 1) := by
  have hwall := WallOfHeight.length_encList_le hW
  simp only [encCase3Block, List.length_append, List.length_cons,
    case3Length_encEdgeTriples, hc]
  omega

private theorem forty_one_mul_le_pow_four (t : ℕ) : 41 * t ≤ (t + 2) ^ 4 := by
  have ht : t ≤ t * t := Nat.le_mul_self t
  nlinarith only [ht, Nat.zero_le (t ^ 4), Nat.zero_le (t ^ 3)]

/-- The fourth-power word size also covers the block and the bitset/tag
prefix, using the same ambient product as the member scans. -/
theorem case3Block_tagged_length_lt_two_pow {w N E : ℕ} (block : List ℕ)
    (hlen : block.length ≤ 40 * (N + E + 1))
    (hw : wordSize 4 ((N + 1) * (E + N + 1)) ≤ w) :
    1 + N + block.length < 2 ^ w := by
  let V := (N + 1) * (E + N + 1)
  have hv : N + E + 1 ≤ V := by
    dsimp only [V]
    nlinarith only [Nat.zero_le (N * (E + N + 1))]
  have hsum : 1 + N + block.length ≤ 41 * V := by omega
  have hpow : (V + 2) ^ 4 < 2 ^ w :=
    (pow_lt_two_pow_wordSize (c := 4) (by decide) V).trans_le (Nat.pow_le_pow_right (by decide) hw)
  exact hsum.trans_lt ((forty_one_mul_le_pow_four V).trans_lt hpow)

/-- The exponent itself fits in the word bound, so a fixed wall-header
constant can be included by increasing that exponent. -/
theorem case3WordSize_exponent_lt {c V w : ℕ} (hc : 1 ≤ c) (hw : wordSize c V ≤ w) :
    c < 2 ^ w := by
  have hp : (V + 2) ^ c < 2 ^ w :=
    (pow_lt_two_pow_wordSize hc V).trans_le (Nat.pow_le_pow_right (by decide) hw)
  exact (Nat.lt_two_pow_self (n := c)).trans_le
    ((Nat.pow_le_pow_left (by omega : 2 ≤ V + 2) c).trans (Nat.le_of_lt hp))

end GraphMinor.Compute
