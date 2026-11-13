module

public import GraphMinor.Compute.GM06Alg34Header
public import GraphMinor.Compute.GM06Alg34Layout

/-!
# Linear-time access to the supplied cuff and division sections

Read the header from input array 0, skip the endpoint pairs, and run the
counted region loop. The actual serialized lengths discharge every word
bound. The parser uses logarithmic words and a linear number of steps.
It preserves the input array and every other array.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Locate the supplied cuff section from the start of the input array. -/
def gm06LocateCuffsProg : Cmd :=
  .seq gm06ReadHeaderProg (gm06SkipRegionsProg 0 103 104 102)

/-- For every supplied finite input, the parser reaches its cuff section
in at most `33 * (size + 1)` steps, using logarithmic words. The initial
registers are arbitrary, and all arrays are preserved. -/
theorem gm06LocateCuffsProg_exec (x : GM06DrawingData) {c : ℕ} (hc : 1 ≤ c)
    {s : State} (harr : s.arrs 0 = x.words) :
    ∃ s' t, Exec (wordSize c x.size) gm06LocateCuffsProg s s' t ∧
      t ≤ 33 * (x.size + 1) ∧
      s'.regs 100 = x.n ∧ s'.regs 101 = x.ends.length ∧ s'.regs 102 = 0 ∧
      s'.regs 103 = x.cuffOffset ∧ AtStream 0 x.cuffOffset (x.cuffWords ++ x.divisionWords) s' ∧
      (∀ a, s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q < 100 ∨ 105 ≤ q → s'.regs q = s.regs q) := by
  have hsize : x.size < 2 ^ wordSize c x.size := lt_two_pow_wordSize_of_le hc (Nat.le_succ _)
  have hlength := x.words_length_lt_wordSize hc
  have hcounts := x.counts_le_size
  have hfive := x.five_le_words_length
  have hlen_size := x.words_length_le_size
  have hw : 3 < 2 ^ wordSize c x.size := by omega
  have h1 : 1 < 2 ^ wordSize c x.size := by omega
  have hstart : 3 + x.endpointWords.length < 2 ^ wordSize c x.size := by
    rw [x.endpointWords_length]
    exact x.regionOffset_lt_length.trans hlength
  have hsource : s.arrs 0 = [x.n, x.ends.length, x.regions.length] ++ x.endpointWords ++
      (x.regionWords ++ (x.cuffWords ++ x.divisionWords)) := by
    rw [harr, x.words_layout]
    simp only [List.append_assoc]
  obtain ⟨s₁, t₁, hex₁, ht₁, hn₁, hm₁, hr₁, hpos₁, hstream₁, harr₁, hreg₁⟩ :=
    gm06ReadHeaderProg_exec x.endpointWords (x.regionWords ++ (x.cuffWords ++ x.divisionWords))
      x.endpointWords_length hw (hcounts.1.trans_lt hsize) (hcounts.2.1.trans_lt hsize)
      (hcounts.2.2.trans_lt hsize) hstart hsource
  have hrlen : x.raw.regions.length = x.regions.length := by
    simp only [GM06DrawingData.raw, List.length_map]
  have hcountw : x.raw.regions.length < 2 ^ wordSize c x.size := by
    rw [hrlen]
    exact hcounts.2.2.trans_lt hsize
  have hregion_end : 3 + 2 * x.ends.length + (gm06RegionWords x.raw.regions).length <
      2 ^ wordSize c x.size := x.cuffOffset_lt_length.trans hlength
  have hr₁' : s₁.regs 102 = x.raw.regions.length := hr₁.trans hrlen.symm
  obtain ⟨s₂, t₂, hex₂, ht₂, hpos₂, hzero₂, hstream₂, harr₂, hreg₂⟩ :=
    gm06SkipRegionsProg_exec 103 104 102 (by decide) (by decide) (by decide)
      x.raw.regions (x.cuffWords ++ x.divisionWords) h1 hcountw hregion_end hstream₁ hpos₁ hr₁'
  have htime : t₁ + t₂ ≤ 33 * (x.size + 1) := by
    rw [hrlen] at ht₂
    omega
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, htime, ?_, ?_, hzero₂, hpos₂, hstream₂, ?_, ?_⟩
  · exact (hreg₂ 100 (by decide) (by decide) (by decide)).trans hn₁
  · exact (hreg₂ 101 (by decide) (by decide) (by decide)).trans hm₁
  · intro a
    exact (harr₂ a).trans (harr₁ a)
  · intro q hq
    rw [hreg₂ q (by omega) (by omega) (by omega)]
    exact hreg₁ q (by omega) (by omega) (by omega) (by omega)

/-- The initial parsing phase of VI (3.4) is a single Word RAM program
with a proved linear time bound on the supplied plain finite array. -/
theorem gm06LocateCuffsProg_computes :
    ComputesRelInTime GM06DrawingData.size (fun x s => s.arrs 0 = x.words)
      (fun x s => s.regs 100 = x.n ∧ s.regs 101 = x.ends.length ∧ s.regs 102 = 0 ∧
        s.regs 103 = x.cuffOffset ∧ AtStream 0 x.cuffOffset (x.cuffWords ++ x.divisionWords) s ∧
        s.arrs 0 = x.words)
      gm06LocateCuffsProg (fun n => n + 1) := by
  refine ⟨33, 1, by decide, by decide, ?_⟩
  intro x s hs
  obtain ⟨s', t, hex, ht, hn, hm, hr, hpos, hstream, harr, _⟩ :=
    gm06LocateCuffsProg_exec x (c := 1) (by decide) hs
  exact ⟨s', t, hex, ht, hn, hm, hr, hpos, hstream, (harr 0).trans hs⟩

end GraphMinor.Compute
