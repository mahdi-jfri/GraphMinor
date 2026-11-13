module

public import GraphMinor.Compute.GM06Alg34Prepare
public import GraphMinor.Compute.GM06Alg34CrossScanRun

/-!
# The initial cross-free check of Graph Minors VI (3.4)

Read the supplied cuff and division, build the block table, and run the
four-position crossing scan. The composite program takes the original
array with arbitrary scratch contents. Its answer is the finite
cross-free predicate and its time is quartic in the input size.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The initial cross-free check: preparation followed by the crossing scan. -/
def gm06CheckCrossFreeProg : Cmd := .seq gm06PrepareCrossingProg gm06CrossScanProg

/-- The initial check in VI (3.4), page 121, computes cross-freeness from
the supplied one-cuff drawing data in polynomial time. -/
theorem gm06CheckCrossFreeProg_exec (x : GM06DrawingData) {L : List (Fin x.n)}
    (hL : x.cuffs = [L]) (hnd : L.Nodup) (hD : GM06.IsDivision x.divisionSet)
    {c : ℕ} (hc : 1 ≤ c) {s : State} (harr : s.arrs 0 = x.words) :
    ∃ s' t, Exec (wordSize c x.size) gm06CheckCrossFreeProg s s' t ∧
      t ≤ 452 * (x.size + 1) ^ 4 ∧
      s'.regs 0 = (if x.crossFree then 1 else 0) ∧ s'.arrs 0 = x.words := by
  have hsize : x.size < 2 ^ wordSize c x.size :=
    lt_two_pow_wordSize_of_le hc (Nat.le_succ _)
  have hwords := x.words_length
  have hcw := x.cuffWords_singleton_length hL
  have hwl := x.words_length_le_size
  have hfive := x.five_le_words_length
  have hlen : L.length ≤ x.size := by omega
  have hn := x.counts_le_size.1
  have hblocks := gm06BlockSection_count_le_length x.raw.division
  have hdivwords : x.divisionWords.length = 1 +
      (x.raw.division.flatMap GM06DrawingData.listWords).length := by
    rw [x.divisionWords_eq]
    simp only [List.length_cons]
    omega
  have hraw : x.raw.division.length = x.division.length := by
    simp [GM06DrawingData.raw]
  have hd : x.division.length ≤ x.size := by omega
  obtain ⟨s₁, t₁, hex₁, ht₁, hL₁, hD₁, _, _, _, hbound, _, _, _, harr₁, _⟩ :=
    gm06PrepareCrossingProg_exec x hL hc harr
  obtain ⟨s₂, t₂, hex₂, ht₂, hans, harr₂, _⟩ := gm06CrossScanProg_exec x L
    (by omega) (hlen.trans_lt hsize) (hn.trans_lt hsize) (hd.trans_lt hsize) hL₁ hD₁ hbound
  have hpow : (L.length + 1) ^ 4 ≤ (x.size + 1) ^ 4 :=
    Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) 4
  have hlinear : x.size + 1 ≤ (x.size + 1) ^ 4 := by ring_nf; omega
  have ht₁' := ht₁.trans (Nat.mul_le_mul_left 200 hlinear)
  have ht₂' := ht₂.trans (Nat.mul_le_mul_left 252 hpow)
  have heq : gm06CrossScan x.division L = x.crossFree := by
    have hiff := gm06CrossScan_iff_crossFree x hL hnd hD
    cases hs : gm06CrossScan x.division L <;> cases hx : x.crossFree <;> simp_all
  exact ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, by omega, heq ▸ hans,
    (harr₂ 0).trans ((harr₁ 0 (by decide) (by decide)).trans harr)⟩

/-- The first phase of (3.4) is a single RAM program with quartic time
and logarithmic words on every supplied valid one-cuff division. -/
theorem gm06CheckCrossFreeProg_computes :
    ComputesRelInTime GM06DrawingData.size
      (fun x s => (∃ L, x.cuffs = [L] ∧ L.Nodup) ∧
        GM06.IsDivision x.divisionSet ∧ s.arrs 0 = x.words)
      (fun x s => s.regs 0 = (if x.crossFree then 1 else 0) ∧ s.arrs 0 = x.words)
      gm06CheckCrossFreeProg (fun n => (n + 1) ^ 4) := by
  refine ⟨452, 1, by decide, by decide, ?_⟩
  rintro x s ⟨⟨L, hL, hnd⟩, hD, harr⟩
  obtain ⟨s', t, hex, ht, hans, harr'⟩ :=
    gm06CheckCrossFreeProg_exec x hL hnd hD (c := 1) (by decide) harr
  exact ⟨s', t, hex, ht, hans, harr'⟩

end GraphMinor.Compute
