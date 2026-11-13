module

public import GraphMinor.Compute.GM06Alg34CuffParse
public import GraphMinor.Compute.GM06Alg34TagInit

/-!
# Preparing the finite crossing test from the supplied array

The program reads the cuff order, allocates the vertex table, and scans
the supplied division blocks into it. It produces exactly the finite
list-update table already verified for the division loop. Every bound
comes from the actual input size, so the preparation phase has linear
time and logarithmic words.
-/

@[expose] public section
namespace GraphMinor.Compute

namespace GM06DrawingData

theorem divisionWords_eq (x : GM06DrawingData) :
    x.divisionWords = x.raw.division.length :: x.raw.division.flatMap listWords := by rfl

theorem divisionOffset_add_length (x : GM06DrawingData) :
    x.divisionOffset + x.divisionWords.length = x.words.length := x.words_length.symm

end GM06DrawingData

/-- Read the supplied cyclic order and build the division table, before
performing any crossing comparisons. -/
def gm06PrepareCrossingProg : Cmd := .seq gm06ReadDiscCuffProg gm06TagDivisionProg

/-- Preparation uses at most `200 * (size + 1)` RAM steps with logarithmic
words. The initial table and scratch registers are arbitrary. -/
theorem gm06PrepareCrossingProg_exec (x : GM06DrawingData) {L : List (Fin x.n)}
    (hL : x.cuffs = [L]) {c : ℕ} (hc : 1 ≤ c) {s : State} (harr : s.arrs 0 = x.words) :
    ∃ s' t, Exec (wordSize c x.size) gm06PrepareCrossingProg s s' t ∧
      t ≤ 200 * (x.size + 1) ∧ s'.arrs 2 = L.map Fin.val ∧
      s'.arrs 3 = gm06DivisionIds x.raw.division (List.replicate x.n 0) ∧
      s'.regs 100 = x.n ∧ s'.regs 101 = x.ends.length ∧ s'.regs 102 = 0 ∧
      s'.regs 105 = L.length ∧ s'.regs 103 = x.words.length ∧ s'.regs 107 = 0 ∧
      AtStream 0 x.words.length [] s' ∧
      (∀ a : ℕ, a ≠ 2 → a ≠ 3 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q < 100 → s'.regs q = s.regs q) := by
  have hsize : x.size < 2 ^ wordSize c x.size := lt_two_pow_wordSize_of_le hc (Nat.le_succ _)
  have hn := x.counts_le_size.1
  have hwordlen := x.words_length_lt_wordSize hc
  have hfive := x.five_le_words_length
  have hw : 1 < 2 ^ wordSize c x.size := by omega
  have hbytes : x.divisionWords.length = 1 +
      (x.raw.division.flatMap GM06DrawingData.listWords).length := by
    rw [x.divisionWords_eq]
    simp only [List.length_cons]
    omega
  have hoff : x.divisionOffset + 1 + (x.raw.division.flatMap GM06DrawingData.listWords).length =
      x.words.length := by
    have heq := x.divisionOffset_add_length
    rw [hbytes] at heq
    omega
  have hcount := gm06BlockSection_count_le_length x.raw.division
  have hcountw : x.raw.division.length < 2 ^ wordSize c x.size := by omega
  have hvalid : ∀ B ∈ x.raw.division, ∀ v ∈ B, v < x.n := by
    intro B hB v hv
    change B ∈ x.division.map (List.map Fin.val) at hB
    obtain ⟨A, _, rfl⟩ := List.mem_map.mp hB
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hv
    exact a.isLt
  have hbound : x.n + (x.raw.division.flatMap GM06DrawingData.listWords).length ≤ x.size := by
    have heq : x.size = x.n + x.words.length := rfl
    omega
  obtain ⟨s₁, t₁, hex₁, ht₁, hL₁, hn₁, hm₁, hr₁, hlen₁, hpos₁, hstream₁, harr₁, hreg₁⟩ :=
    gm06ReadDiscCuffProg_exec x hL hc harr
  rw [x.divisionWords_eq] at hstream₁
  have hstream₁' : AtStream 0 x.divisionOffset
      (x.raw.division.length :: (x.raw.division.flatMap GM06DrawingData.listWords ++ [])) s₁ := by
    simpa only [List.append_nil] using hstream₁
  obtain ⟨s₂, t₂, hex₂, ht₂, hids₂, hpos₂, hzero₂, hstream₂, harr₂, hreg₂⟩ :=
    gm06TagDivisionProg_exec x.raw.division [] hw (hn.trans_lt hsize) hcountw hvalid
      (hoff.symm ▸ hwordlen) hstream₁' hpos₁ hn₁
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, by omega, ?_, hids₂, ?_, ?_, ?_, ?_,
    hpos₂.trans hoff, hzero₂, hoff ▸ hstream₂, ?_, ?_⟩
  · exact (harr₂ 2 (by decide)).trans hL₁
  · exact (hreg₂ 100 (by decide) (by decide) (by decide) (by decide)).trans hn₁
  · exact (hreg₂ 101 (by decide) (by decide) (by decide) (by decide)).trans hm₁
  · exact (hreg₂ 102 (by decide) (by decide) (by decide) (by decide)).trans hr₁
  · exact (hreg₂ 105 (by decide) (by decide) (by decide) (by decide)).trans hlen₁
  · intro a ha2 ha3
    exact (harr₂ a ha3).trans (harr₁ a ha2)
  · intro q hq
    rw [hreg₂ q (by omega) (by omega) (by omega) (by omega)]
    exact hreg₁ q hq

/-- The preparation phase is one concrete RAM program with a proved
linear bound for every supplied array having one cuff list. -/
theorem gm06PrepareCrossingProg_computes :
    ComputesRelInTime GM06DrawingData.size
      (fun x s => x.cuffs.length = 1 ∧ s.arrs 0 = x.words)
      (fun x s => ∃ L : List (Fin x.n), x.cuffs = [L] ∧ s.arrs 2 = L.map Fin.val ∧
        s.arrs 3 = gm06DivisionIds x.raw.division (List.replicate x.n 0) ∧
        s.regs 100 = x.n ∧ s.regs 105 = L.length ∧ s.regs 103 = x.words.length ∧
        s.regs 107 = 0 ∧ s.arrs 0 = x.words)
      gm06PrepareCrossingProg (fun n => n + 1) := by
  refine ⟨200, 1, by decide, by decide, ?_⟩
  intro x s hs
  obtain ⟨L, hL⟩ : ∃ L : List (Fin x.n), x.cuffs = [L] := by
    cases hx : x.cuffs with
    | nil =>
      have heq := hs.1
      simp only [hx, List.length_nil] at heq
      cases heq
    | cons L Ls =>
      have heq := hs.1
      rw [hx, List.length_cons] at heq
      have hLs : Ls = [] := List.length_eq_zero_iff.mp (by omega)
      exact ⟨L, congrArg (List.cons L) hLs⟩
  obtain ⟨s', t, hex, ht, hL', hids, hn, _, _, hlen, hpos, hzero, _, harr, _⟩ :=
    gm06PrepareCrossingProg_exec x hL (c := 1) (by decide) hs.2
  exact ⟨s', t, hex, ht, L, hL, hL', hids, hn, hlen, hpos, hzero,
    (harr 0 (by decide) (by decide)).trans hs.2⟩

end GraphMinor.Compute
