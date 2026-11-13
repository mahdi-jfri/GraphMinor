module

public import GraphMinor.Compute.GM06Alg34CuffRead

/-!
# Linear-time parsing through the disc cuff

Run the header/region parser and read the single supplied cyclic list.
The source array itself bounds every word and copied label. The composed
program leaves the cursor at the division blocks and the cuff order in
array 2. No geometric data or initial scratch-register values are read.
-/

@[expose] public section
namespace GraphMinor.Compute

namespace GM06DrawingData

/-- Cursor position at the supplied division-block count. -/
def divisionOffset (x : GM06DrawingData) : ℕ := x.cuffOffset + x.cuffWords.length

theorem divisionOffset_lt_length (x : GM06DrawingData) : x.divisionOffset < x.words.length := by
  have hl := x.words_length
  have hd := x.divisionWords_pos
  unfold divisionOffset cuffOffset
  omega

theorem cuffWords_singleton {x : GM06DrawingData} {L : List (Fin x.n)}
    (hL : x.cuffs = [L]) : x.cuffWords = 1 :: listWords (L.map Fin.val) := by
  simp only [cuffWords, listsWords, hL, List.map_cons, List.map_nil, List.length_cons,
    List.length_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem cuffWords_singleton_length {x : GM06DrawingData} {L : List (Fin x.n)}
    (hL : x.cuffs = [L]) : x.cuffWords.length = 2 + L.length := by
  rw [cuffWords_singleton hL]
  simp only [List.length_cons, listWords, List.length_map]
  omega

end GM06DrawingData

/-- Parse from the beginning of the supplied array through its disc cuff. -/
def gm06ReadDiscCuffProg : Cmd := .seq gm06LocateCuffsProg gm06ReadCuffProg

/-- The composed parser copies exactly the one supplied cuff and reaches
the division section in at most `100 * (size + 1)` steps with logarithmic
words. Every initial scratch register may be arbitrary. -/
theorem gm06ReadDiscCuffProg_exec (x : GM06DrawingData) {L : List (Fin x.n)}
    (hL : x.cuffs = [L]) {c : ℕ} (hc : 1 ≤ c) {s : State}
    (harr : s.arrs 0 = x.words) :
    ∃ s' t, Exec (wordSize c x.size) gm06ReadDiscCuffProg s s' t ∧
      t ≤ 100 * (x.size + 1) ∧ s'.arrs 2 = L.map Fin.val ∧
      s'.regs 100 = x.n ∧ s'.regs 101 = x.ends.length ∧ s'.regs 102 = 0 ∧
      s'.regs 105 = L.length ∧ s'.regs 103 = x.divisionOffset ∧
      AtStream 0 x.divisionOffset x.divisionWords s' ∧
      (∀ a : ℕ, a ≠ 2 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q < 100 → s'.regs q = s.regs q) := by
  have hsize : x.size < 2 ^ wordSize c x.size := lt_two_pow_wordSize_of_le hc (Nat.le_succ _)
  have hn := x.counts_le_size.1
  have hlength := x.words_length_lt_wordSize hc
  have hfive := x.five_le_words_length
  have hw : 1 < 2 ^ wordSize c x.size := by omega
  have hclen := x.cuffWords_singleton_length hL
  have hoff : x.cuffOffset + 2 + (L.map Fin.val).length = x.divisionOffset := by
    rw [GM06DrawingData.divisionOffset, hclen, List.length_map]
    omega
  have hend : x.cuffOffset + 2 + (L.map Fin.val).length < 2 ^ wordSize c x.size := by
    rw [hoff]
    exact x.divisionOffset_lt_length.trans hlength
  have hword : ∀ z ∈ L.map Fin.val, z < 2 ^ wordSize c x.size := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hz
    exact i.isLt.trans (hn.trans_lt hsize)
  have hLsize : L.length ≤ x.size := by
    have hpos := x.divisionOffset_lt_length
    have hws := x.words_length_le_size
    unfold GM06DrawingData.divisionOffset at hpos
    omega
  obtain ⟨s₁, t₁, hex₁, ht₁, hn₁, hm₁, hr₁, hpos₁, hstream₁, harr₁, hreg₁⟩ :=
    gm06LocateCuffsProg_exec x hc harr
  rw [x.cuffWords_singleton hL] at hstream₁
  obtain ⟨s₂, t₂, hex₂, ht₂, hcopy₂, hlen₂, _, hpos₂, hstream₂, harr₂, hreg₂⟩ :=
    gm06ReadCuffProg_exec (L.map Fin.val) x.divisionWords hw hword hend hstream₁ hpos₁
  simp only [List.length_map] at ht₂ hlen₂
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, by omega, hcopy₂, ?_, ?_, ?_, hlen₂,
    hpos₂.trans hoff, hoff ▸ hstream₂, ?_, ?_⟩
  · exact (hreg₂ 100 (by decide) (by decide) (by decide) (by decide)).trans hn₁
  · exact (hreg₂ 101 (by decide) (by decide) (by decide) (by decide)).trans hm₁
  · exact (hreg₂ 102 (by decide) (by decide) (by decide) (by decide)).trans hr₁
  · intro a ha
    exact (harr₂ a ha).trans (harr₁ a)
  · intro q hq
    rw [hreg₂ q (by omega) (by omega) (by omega) (by omega)]
    exact hreg₁ q (Or.inl hq)

/-- Reading the disc cuff is a single RAM program with linear time and
logarithmic words, for every supplied array with one cuff list. -/
theorem gm06ReadDiscCuffProg_computes :
    ComputesRelInTime GM06DrawingData.size
      (fun x s => x.cuffs.length = 1 ∧ s.arrs 0 = x.words)
      (fun x s => ∃ L : List (Fin x.n), x.cuffs = [L] ∧ s.arrs 2 = L.map Fin.val ∧
        s.regs 100 = x.n ∧ s.regs 101 = x.ends.length ∧ s.regs 102 = 0 ∧
        s.regs 105 = L.length ∧ s.regs 103 = x.divisionOffset ∧
        AtStream 0 x.divisionOffset x.divisionWords s ∧ s.arrs 0 = x.words)
      gm06ReadDiscCuffProg (fun n => n + 1) := by
  refine ⟨100, 1, by decide, by decide, ?_⟩
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
  obtain ⟨s', t, hex, ht, hcopy, hn, hm, hr, hlen, hpos, hstream, harr, _⟩ :=
    gm06ReadDiscCuffProg_exec x hL (c := 1) (by decide) hs.2
  exact ⟨s', t, hex, ht, L, hL, hcopy, hn, hm, hr, hlen, hpos, hstream,
    (harr 0 (by decide)).trans hs.2⟩

end GraphMinor.Compute
