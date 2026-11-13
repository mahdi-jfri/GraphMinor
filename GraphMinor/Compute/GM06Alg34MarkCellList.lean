module

public import GraphMinor.Compute.GM06Alg34MarkCellLoop

/-!
# Reading and marking a length-prefixed closure list

Read a supplied boundary-list length and mark all of its labels in the
current closure row. The same pass handles vertex and edge lists by
the fixed kind offset. Its output is the exact finite sequence of marks.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Read one supplied boundary-list length and mark all its entries. -/
def gm06MarkCellListProg : Cmd :=
  .seq (readStreamWordProg 0 103 172) gm06MarkCellLoopProg

/-- The length-prefixed closure-list pass consumes exactly its supplied
words and performs their exact matrix marks with linear RAM work. -/
theorem gm06MarkCellListProg_exec {w off row shift : ℕ} (L tail : List ℕ)
    (hw : 1 < 2 ^ w) (hoff : off + 1 + L.length < 2 ^ w) {s : State}
    (hs : AtStream 0 off (GM06DrawingData.listWords L ++ tail) s) (hp : s.regs 103 = off)
    (hr : s.regs 173 = row) (hshift : s.regs 174 = shift)
    (hlen : (s.arrs 12).length < 2 ^ w)
    (hvalid : ∀ v ∈ L, row + shift + v < (s.arrs 12).length) :
    ∃ s' t, Exec w gm06MarkCellListProg s s' t ∧ t ≤ 20 * L.length + 9 ∧
      s'.arrs 12 = gm06MarkCells row shift L (s.arrs 12) ∧
      s'.regs 103 = off + 1 + L.length ∧ s'.regs 172 = 0 ∧
      AtStream 0 (off + 1 + L.length) tail s' ∧
      (∀ a : ℕ, a ≠ 12 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 103 → q ≠ 109 → q ≠ 172 → s'.regs q = s.regs q) := by
  have hLw : L.length < 2 ^ w := by omega
  obtain ⟨s₁, t₁, he₁, ht₁, hc₁, hp₁, hs₁, ha₁, hr₁⟩ :=
    readStreamWordProg_exec 103 172 (by decide) hw (by omega) hLw hs hp
  obtain ⟨s₂, t₂, he₂, ht₂, hbuf₂, hp₂, hc₂, hs₂, ha₂, hr₂⟩ :=
    gm06MarkCellLoopProg_exec L tail hw hoff hs₁ hp₁ hc₁
      ((hr₁ 173 (by decide) (by decide)).trans hr)
      ((hr₁ 174 (by decide) (by decide)).trans hshift)
      (by rw [ha₁ 12]; exact hlen) (by rw [ha₁ 12]; exact hvalid)
  refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, by omega, ?_, hp₂, hc₂, hs₂, ?_, ?_⟩
  · rw [hbuf₂, ha₁ 12]
  · intro a ha
    exact (ha₂ a ha).trans (ha₁ a)
  · intro q hqp hqv hqc
    exact (hr₂ q hqp hqv hqc).trans (hr₁ q hqp hqc)

end GraphMinor.Compute
