module

public import GraphMinor.Compute.Case3StepsCandidateSizeBound

/-!
# One word-size bound for the member scan

The member calls use at most twice the ambient product as their size
argument. The stored counts, candidate labels, encodings, and record buffer
are linear in the ambient vertex and edge counts. A fourth power of the
ambient size bounds all of these words and lengths together.
-/

public section

namespace GraphMinor.Compute

/-- A fourth power bounds the constant factor used by the record buffer. -/
theorem case3TwentyFour_mul_le_pow_four (t : ℕ) : 24 * t ≤ (t + 2) ^ 4 := by
  nlinarith [Nat.zero_le (t ^ 4), Nat.zero_le (t ^ 3), Nat.zero_le (t ^ 2)]

/-- The numeric word bounds needed by member construction, compacting,
mask scanning, and the preallocated record buffer. -/
theorem case3Scan_word_bounds {k N E A m w : ℕ} (hk : k ≤ N) (hA : A ≤ E) (hm : m ≤ E)
    (hpow : (((N + 1) * (E + N + 1)) + 2) ^ 4 < 2 ^ w) :
    6 < 2 ^ w ∧ k + 1 < 2 ^ w ∧ N < 2 ^ w ∧ k * 4 < 2 ^ w ∧
      2 + 2 * m < 2 ^ w ∧ k + m < 2 ^ w ∧ E < 2 ^ w ∧
      2 + 3 * A < 2 ^ w ∧ 24 * (N + E + 1) < 2 ^ w ∧ k + m + 1 < 2 ^ w := by
  have hbase : N + E + 1 ≤ (N + 1) * (E + N + 1) := by
    have hmul := Nat.mul_le_mul_right (E + N + 1) (show 1 ≤ N + 1 by omega)
    simpa only [Nat.one_mul, Nat.add_comm E N] using hmul
  have hcap : 24 * (N + E + 1) < 2 ^ w :=
    ((Nat.mul_le_mul_left 24 hbase).trans (case3TwentyFour_mul_le_pow_four _)).trans_lt hpow
  omega

/-- An individual call can use the ambient word size after doubling only
the constant supplied by its (7.2) specification. -/
theorem case3MemberCall_wordSize_le (x : Alg81Input) (D : MultiDigraph x.n)
    (hG : D.toSimpleGraph = x.G) (Z : Finset (Fin x.n))
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x Z))
    (i : Case3SelectedGroup x Z) (c N : ℕ) (hn : x.n ≤ N) :
    wordSize c (algorithm72Size (case3MemberAlgorithm72Input x D Z i)) ≤
      wordSize (2 * c) ((N + 1) * (D.numEdges + N + 1)) := by
  apply case3WordSize_le_of_le_two_mul c
  exact (case3MemberAlgorithm72Size_le_ambient x D hG Z hdiv i).trans
    (Nat.mul_le_mul_left 2 (Nat.mul_le_mul (Nat.add_le_add_right hn 1)
      (Nat.add_le_add_right (Nat.add_le_add_left hn D.numEdges) 1)))

/-- All routed and compact member encodings fit the same edge-count word
bounds. This supplies the per-member inequalities used in each iteration. -/
theorem case3SelectedMember_word_bounds {w : ℕ} (x : Alg81Input) (D : MultiDigraph x.n)
    (hG : D.toSimpleGraph = x.G) (Z : Finset (Fin x.n))
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x Z))
    (i : Case3SelectedGroup x Z) (he : D.numEdges < 2 ^ w)
    (henc : 2 + 3 * D.numEdges < 2 ^ w) :
    2 + 3 * (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).numActivePairs < 2 ^ w ∧
      (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).numEdges < 2 ^ w ∧
      2 + 3 * (case3CompactMember x D Z i).numActivePairs < 2 ^ w ∧
      (case3CompactMember x D Z i).numEdges < 2 ^ w := by
  have hR := MultiDigraph.numEdges_mono (case3RoutedMember_le x D Z (case3RawIndexLabel x i.1))
  have hRA := (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).numActivePairs_le_numEdges
  have hCA := (case3CompactMember x D Z i).numActivePairs_le_numEdges
  have hCE := case3CompactMember_numEdges x D hG Z hdiv i
  omega

end GraphMinor.Compute
