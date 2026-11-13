module

public import GraphMinor.Compute.GM06Alg34ClosureRowsProg
public import GraphMinor.Compute.GM06Alg34Header

/-!
# A quadratic RAM program for the supplied-cell closure matrix

Read the actual input header, allocate the cell matrix, and run all
three supplied-cell row passes. The program starts with arbitrary
scratch contents. Its exact finite output and quadratic time bound use
only the serialized input size, with logarithmic RAM words.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Construct the supplied-cell closure matrix directly from input array 0. -/
def gm06ClosureMatrixProg : Cmd := .seq gm06ReadHeaderProg gm06ClosureRowsProg

private theorem alg34_closure_time_bound (n : ℕ) :
    n * n + 107 * n + 60 ≤ 120 * (n + 1) ^ 2 := by
  simp only [Nat.pow_two, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
  omega

/-- The original supplied array yields exactly its finite closure matrix
in quadratic time, with logarithmic words and arbitrary scratch contents. -/
theorem gm06ClosureMatrixProg_exec (x : GM06DrawingData) {c : ℕ} (hc : 2 ≤ c)
    {s : State} (hinput : s.arrs 0 = x.words) :
    ∃ s' t, Exec (wordSize c x.size) gm06ClosureMatrixProg s s' t ∧
      t ≤ 120 * (x.size + 1) ^ 2 ∧ s'.arrs 12 = gm06ClosureMatrixData x ∧
      s'.regs 170 = x.cellCount ∧ s'.regs 103 = x.cuffOffset ∧
      AtStream 0 x.cuffOffset (x.cuffWords ++ x.divisionWords) s' ∧
      s'.regs 100 = x.n ∧ s'.regs 101 = x.ends.length ∧ s'.regs 102 = x.regions.length ∧
      (∀ A : ℕ, A ≠ 12 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, q < 100 → s'.regs q = s.regs q) := by
  have hc1 : 1 ≤ c := by omega
  have hsize : x.size < 2 ^ wordSize c x.size := lt_two_pow_wordSize_of_le hc1 (Nat.le_succ _)
  have hlength := x.words_length_lt_wordSize hc1
  have hcounts := x.counts_le_size
  have hN := x.cellCount_le_size.trans_lt hsize
  have hNsize : x.cellCount ≤ x.size + 2 := x.cellCount_le_size.trans (by omega)
  have hsquare : x.cellCount * x.cellCount < 2 ^ wordSize c x.size :=
    (Nat.mul_le_mul hNsize hNsize).trans_lt (sq_lt_two_pow_wordSize hc)
  have hw3 : 3 < 2 ^ wordSize c x.size := by have hh := x.five_le_words_length; omega
  have hw1 : 1 < 2 ^ wordSize c x.size := by omega
  have hend : 3 + x.endpointWords.length < 2 ^ wordSize c x.size := by
    rw [x.endpointWords_length]
    exact x.regionOffset_lt_length.trans hlength
  have hsource : s.arrs 0 = [x.n, x.ends.length, x.regions.length] ++ x.endpointWords ++
      (x.regionWords ++ (x.cuffWords ++ x.divisionWords)) := by
    rw [hinput, x.words_layout]
    simp only [List.append_assoc]
  have hstream : AtStream 0 3
      (x.endpointWords ++ (x.regionWords ++ (x.cuffWords ++ x.divisionWords))) s :=
    ⟨[x.n, x.ends.length, x.regions.length], rfl, by simpa only [List.append_assoc] using hsource⟩
  obtain ⟨s₁, t₁, he₁, ht₁, hn₁, hm₁, hr₁, _, _, ha₁, hregs₁⟩ :=
    gm06ReadHeaderProg_exec x.endpointWords (x.regionWords ++ (x.cuffWords ++ x.divisionWords))
      x.endpointWords_length hw3 (hcounts.1.trans_lt hsize) (hcounts.2.1.trans_lt hsize)
      (hcounts.2.2.trans_lt hsize) hend hsource
  obtain ⟨s₂, t₂, he₂, ht₂, hbuf₂, hN₂, hp₂, hs₂, hn₂, hm₂, hr₂, ha₂, hregs₂⟩ :=
    gm06ClosureRowsProg_exec x (x.cuffWords ++ x.divisionWords) hw1 hN hsquare
      (x.cuffOffset_lt_length.trans hlength) (hstream.of_arr_eq (ha₁ 0)) hn₁ hm₁ hr₁
  have hsquare_size : x.cellCount * x.cellCount ≤ x.size * x.size :=
    Nat.mul_le_mul x.cellCount_le_size x.cellCount_le_size
  have hregion_size : x.regionWords.length ≤ x.size := by
    have hh := x.words_length
    have hls := x.words_length_le_size
    omega
  have htime : t₁ + t₂ ≤ x.size * x.size + 107 * x.size + 60 := by omega
  refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, htime.trans (alg34_closure_time_bound _),
    hbuf₂, hN₂, hp₂, hs₂, hn₂, hm₂, hr₂, ?_, ?_⟩
  · intro A hA
    exact (ha₂ A hA).trans (ha₁ A)
  · intro q hq
    exact (hregs₂ q hq).trans (hregs₁ q (by omega) (by omega) (by omega) (by omega))

end GraphMinor.Compute
