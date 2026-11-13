module

public import GraphMinor.Compute.GM06Alg34PayloadFront
public import GraphMinor.Compute.GM06Alg34PayloadSuffix
public import GraphMinor.Compute.GM06Alg34RegionOutputProg

/-!
# Serializing every section of an induced drawing

Write the computed header and endpoints, scan the canonical new region
roots, then restore the saved cuff cursor and restrict the two final
list sections. Every pass reads the supplied data or tables computed
from it. Their concatenation is the complete induced drawing encoding.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Write all five sections using the prepared deletion tables. -/
def gm06PayloadWriteProg : Cmd :=
  .seq gm06PayloadFrontProg (.seq gm06RegionOutputProg
    (.seq (.assign 103 (.reg 176)) gm06PayloadSuffixProg))

/-- All prepared tables suffice to write the exact full induced encoding.
The bound is the sum of the finite scans used by its three section passes. -/
theorem gm06PayloadWriteProg_exec {w cap : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (hw : 3 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hN : x.cellCount < 2 ^ w) (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    (hinputSize : x.words.length < 2 ^ w)
    (hbudget : gm06SerializationBudget x < 2 ^ w) {s : State}
    (hinput : s.arrs 0 = x.words)
    (hvertexMask : s.arrs 4 = gm06VertexMask vs) (hvertexRanks : s.arrs 5 = gm06VertexRanks vs)
    (hedgeMask : s.arrs 6 = gm06EdgeMask x vs) (hedgeRanks : s.arrs 7 = gm06EdgeRanks x vs)
    (hends : s.arrs 8 = (x.inducedData vs).endpointWords)
    (hmat : s.arrs 12 = gm06ClosureMatrixData x) (hrootMask : s.arrs 36 = gm06RootMask x vs)
    (hsize : s.regs 4 = x.cellCount) (hc : s.regs 170 = x.cellCount)
    (hvn : s.regs 100 = x.n) (hem : s.regs 101 = x.ends.length)
    (hnewN : s.regs 131 = (x.activeVertices vs).length)
    (hnewE : s.regs 137 = (x.activeEdges vs).length)
    (hnewR : s.regs 203 = (x.regionRoots vs).length) (hsaved : s.regs 176 = x.cuffOffset)
    (hlists : IsAdjList (x.complementGraph vs) 30 31 32 (adjListOf (x.complementGraph vs)) s)
    (hlen : (s.arrs 32).length = x.cellCount * x.cellCount)
    (hbuf : IsPrefixBuffer 10 [] ((x.inducedData vs).words.length + cap) s)
    (hcursor : s.regs 143 = 0) :
    ∃ s' t, Exec w gm06PayloadWriteProg s s' t ∧
      t ≤ 17 * (x.inducedData vs).endpointWords.length +
        (26 * (x.cellCount * x.cellCount) + 23 * x.cellCount +
          (18 * x.cellCount + 72) * (x.n + x.ends.length) + 99) * x.cellCount +
        60 * (x.cuffWords.length + x.divisionWords.length) + 74 ∧
      IsPrefixBuffer 10 (x.inducedData vs).words cap s' ∧
      s'.regs 143 = (x.inducedData vs).words.length ∧
      (∀ j : ℕ, j ≠ 9 → j ≠ 10 → j ≠ 11 → j ≠ 33 → j ≠ 34 → s'.arrs j = s.arrs j) := by
  let y := x.inducedData vs
  let pfx := [y.n, y.ends.length, y.regions.length] ++ y.endpointWords
  have hn' : y.n ≤ x.n :=
    (List.length_filter_le _ _).trans_eq List.length_finRange
  have he : y.ends.length ≤ x.ends.length := by
    rw [x.inducedData_ends_length, ← gm06EdgeMask_sum]
    exact gm06EdgeMask_sum_le x vs
  have hr : y.regions.length ≤ x.cellCount := by
    rw [x.inducedData_regions_length, ← gm06RootMask_sum]
    exact gm06RootMask_sum_le x vs
  have hm : x.ends.length ≤ x.cellCount := by
    simp only [GM06DrawingData.cellCount]; omega
  have hep : y.endpointWords.length ≤ 2 * x.ends.length := by
    rw [y.endpointWords_length]; omega
  have hpfx : pfx.length = 3 + y.endpointWords.length := by
    simp only [pfx, List.length_append, List.length_cons, List.length_nil] <;> omega
  have hrlen := gm06Induced_regionWords_length_le x vs
  have hclen := gm06Induced_cuffWords_length_le x vs
  change y.regionWords.length ≤ x.cellCount * (2 + x.n + x.ends.length) at hrlen
  have hprod := Nat.mul_le_mul_right (2 + x.n + x.ends.length) (Nat.le_succ x.cellCount)
  change x.cellCount * (2 + x.n + x.ends.length) ≤
    (x.cellCount + 1) * (2 + x.n + x.ends.length) at hprod
  have hbudget' := hbudget
  unfold gm06SerializationBudget at hbudget'
  change IsPrefixBuffer 10 [] (y.words.length + cap) s at hbuf
  obtain ⟨s₁, t₁, hex₁, ht₁, hb₁, hp₁, ha₁, hg₁⟩ :=
    gm06PayloadFrontProg_exec y
      (cap := y.regionWords.length + y.cuffWords.length + y.divisionWords.length + cap) hw (hn'.trans_lt hn) (he.trans_lt (hm.trans_lt hN))
      (hr.trans_lt hN) (by omega) hends
      (by simpa only [y.words_length, y.endpointWords_length, Nat.add_assoc] using hbuf)
      hcursor hnewN (by simpa only [y, x.inducedData_ends_length] using hnewE)
      (by simpa only [y, x.inducedData_regions_length] using hnewR)
  have hkeep₁ : ∀ q : ℕ, q = 4 ∨ q = 100 ∨ q = 101 ∨ q = 170 ∨ q = 176 →
      s₁.regs q = s.regs q := by
    intro q hq
    apply hg₁ q <;> rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨s₂, t₂, hex₂, ht₂, hb₂, hp₂, ha₂, hg₂⟩ :=
    gm06RegionOutputProg_exec (cap := y.cuffWords.length + y.divisionWords.length + cap)
      x vs pfx (by omega) hN hsquare
      (by rw [hpfx]; omega)
      ((ha₁ 36 (by decide)).trans hrootMask) ((ha₁ 12 (by decide)).trans hmat)
      ((hkeep₁ _ (by decide)).trans hc)
      ((ha₁ 4 (by decide)).trans hvertexMask) ((ha₁ 5 (by decide)).trans hvertexRanks)
      ((ha₁ 6 (by decide)).trans hedgeMask) ((ha₁ 7 (by decide)).trans hedgeRanks)
      ((hkeep₁ _ (by decide)).trans hsize) ((hkeep₁ _ (by decide)).trans hvn)
      ((hkeep₁ _ (by decide)).trans hem)
      (hlists.of_arrs_eq (ha₁ 30 (by decide)) (ha₁ 31 (by decide)) (ha₁ 32 (by decide)))
      (by rw [ha₁ 32 (by decide)]; exact hlen) (by simpa only [Nat.add_assoc] using hb₁) (by rw [hpfx]; exact hp₁)
  have hsaved₂ : s₂.regs 176 = x.cuffOffset :=
    (hg₂ 176 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hkeep₁ _ (by decide)).trans hsaved)
  let s₃ := s₂.setReg 103 x.cuffOffset
  have hrestore : Exec w (.assign 103 (.reg 176)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, hsaved₂, x.cuffOffset_lt_length.trans hinputSize])
  have hstream : AtStream 0 x.cuffOffset ((x.cuffWords ++ x.divisionWords) ++ []) s₃ := by
    refine ⟨[x.n, x.ends.length, x.regions.length] ++ x.endpointWords ++ x.regionWords, ?_, ?_⟩
    · simp only [List.length_append, List.length_cons, List.length_nil, x.endpointWords_length,
        GM06DrawingData.cuffOffset] <;> omega
    · change s₂.arrs 0 = _
      rw [ha₂ 0 (by decide) (by decide) (by decide) (by decide) (by decide), ha₁ 0 (by decide), hinput,
        x.words_layout]
      simp only [List.append_nil, List.append_assoc]
  have hmask₃ : s₃.arrs 4 = gm06VertexMask vs :=
    (ha₂ 4 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((ha₁ 4 (by decide)).trans hvertexMask)
  have hrank₃ : s₃.arrs 5 = gm06VertexRanks vs :=
    (ha₂ 5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((ha₁ 5 (by decide)).trans hvertexRanks)
  have hinputLen := x.words_length
  obtain ⟨s₄, t₄, hex₄, ht₄, hb₄, hp₄, _, _, ha₄, _⟩ :=
    gm06PayloadSuffixProg_exec (cap := cap) x vs [] (pfx ++ y.regionWords) (by omega) hn
      (by unfold GM06DrawingData.cuffOffset; omega)
      (by simp only [List.length_append]; rw [hpfx]; omega)
      hstream (by simp [s₃]) hmask₃ hrank₃ hb₂
      (by simpa [s₃, State.setReg] using hp₂)
  dsimp only [y] at ht₁
  refine ⟨s₄, t₁ + (t₂ + (2 + t₄)), .seq hex₁ (.seq hex₂ (.seq hrestore hex₄)),
    by omega, ?_, ?_, ?_⟩
  · change IsPrefixBuffer 10 y.words cap s₄
    rw [y.words_layout]
    exact hb₄
  · change s₄.regs 143 = y.words.length
    rw [y.words_layout]
    exact hp₄
  · intro j h9 h10 h11 h33 h34
    exact (ha₄ j h9 h10 h11).trans
      ((ha₂ j h9 h10 h11 h33 h34).trans (ha₁ j h10))

end GraphMinor.Compute
