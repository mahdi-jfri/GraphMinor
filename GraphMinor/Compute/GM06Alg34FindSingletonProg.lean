module

public import GraphMinor.Compute.GM06Alg34SingletonLoop
public import GraphMinor.Compute.GM06Alg34Prepare

/-!
# Finding a singleton directly from the drawing array

Locate the division section by reading the supplied disc cuff. Initialize
the found flag, read the supplied block count, and run the verified
whole-division loop. The program returns the exact finite singleton
search with natural-number vertex labels. All word bounds follow from
the original array size, and the time is linear in that size.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Read the supplied division and find its first singleton block. -/
def gm06FindSingletonProg : Cmd :=
  .seq gm06ReadDiscCuffProg
    (.seq (.assign 113 (.const 0))
      (.seq (readStreamWordProg 0 103 107) gm06SingletonLoopProg))

/-- The input-array singleton search has a linear time bound with
logarithmic words and arbitrary initial scratch contents. -/
theorem gm06FindSingletonProg_exec (x : GM06DrawingData) {L : List (Fin x.n)}
    (hL : x.cuffs = [L]) {c : ℕ} (hc : 1 ≤ c) {s : State} (harr : s.arrs 0 = x.words) :
    ∃ s' t, Exec (wordSize c x.size) gm06FindSingletonProg s s' t ∧
      t ≤ 200 * (x.size + 1) ∧
      gm06SingletonRegs ((gm06FindSingleton x.division).map Fin.val) s' ∧
      s'.regs 103 = x.words.length ∧ s'.regs 107 = 0 ∧ s'.arrs 0 = x.words ∧
      (∀ q : ℕ, q < 100 → s'.regs q = s.regs q) := by
  have hwordlen := x.words_length_lt_wordSize hc
  have hsize := x.words_length_le_size
  have hfive := x.five_le_words_length
  have hw : 1 < 2 ^ wordSize c x.size := by omega
  have hbytes : x.divisionWords.length = 1 +
      (x.raw.division.flatMap GM06DrawingData.listWords).length := by
    rw [x.divisionWords_eq]
    simp only [List.length_cons]
    omega
  have hoff : x.divisionOffset + 1 + (x.raw.division.flatMap GM06DrawingData.listWords).length =
      x.words.length := by
    have h := x.divisionOffset_add_length
    rw [hbytes] at h
    omega
  have hcount := gm06BlockSection_count_le_length x.raw.division
  have hcountw : x.raw.division.length < 2 ^ wordSize c x.size := by omega
  have hvalid : ∀ B ∈ x.raw.division, ∀ v ∈ B, v < 2 ^ wordSize c x.size := by
    intro B hB v hv
    change B ∈ x.division.map (List.map Fin.val) at hB
    obtain ⟨A, _, rfl⟩ := List.mem_map.mp hB
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hv
    exact lt_trans (lt_of_lt_of_le a.isLt x.counts_le_size.1)
      (lt_two_pow_wordSize_of_le hc (Nat.le_succ _))
  obtain ⟨s₁, t₁, hex₁, ht₁, _, _, _, _, _, hpos₁, hstream₁, harr₁, hreg₁⟩ :=
    gm06ReadDiscCuffProg_exec x hL hc harr
  let s₂ := s₁.setReg 113 0
  have hex₂ : Exec (wordSize c x.size) (.assign 113 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  have hfound₂ : gm06SingletonRegs none s₂ := by
    simp [gm06SingletonRegs, s₂]
  rw [x.divisionWords_eq] at hstream₁
  have hstream₂ : AtStream 0 x.divisionOffset
      (x.raw.division.length :: (x.raw.division.flatMap GM06DrawingData.listWords ++ [])) s₂ := by
    simpa only [List.append_nil] using hstream₁.of_arr_eq (s' := s₂) rfl
  have hpos₂ : s₂.regs 103 = x.divisionOffset := by simpa [s₂] using hpos₁
  obtain ⟨s₃, t₃, hex₃, ht₃, hcount₃, hpos₃, hstream₃, harr₃, hreg₃⟩ :=
    readStreamWordProg_exec 103 107 (by decide) hw (by omega) hcountw hstream₂ hpos₂
  have hfound₃ : gm06SingletonRegs none s₃ :=
    ⟨(hreg₃ 113 (by decide) (by decide)).trans hfound₂.1,
      fun v hv => (hreg₃ 114 (by decide) (by decide)).trans (hfound₂.2 v hv)⟩
  obtain ⟨s₄, t₄, hex₄, ht₄, hfound₄, hpos₄, hzero₄, _, harr₄, hreg₄⟩ :=
    gm06SingletonLoopProg_exec x.raw.division [] none hw hvalid (hoff.symm ▸ hwordlen)
      hstream₃ hpos₃ hcount₃ hfound₃
  have hmap : gm06FindSingleton x.raw.division = (gm06FindSingleton x.division).map Fin.val :=
    gm06FindSingleton_map Fin.val Fin.val_injective x.division
  refine ⟨s₄, t₁ + (2 + (t₃ + t₄)), .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by omega, hmap ▸ hfound₄, hpos₄.trans hoff, hzero₄,
    (harr₄ 0).trans ((harr₃ 0).trans ((harr₁ 0 (by decide)).trans harr)), ?_⟩
  intro q hq
  rw [hreg₄ q (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega), hreg₃ q (by omega) (by omega)]
  exact (State.setReg_regs_ne _ _ (by omega : q ≠ 113)).trans (hreg₁ q hq)

end GraphMinor.Compute
