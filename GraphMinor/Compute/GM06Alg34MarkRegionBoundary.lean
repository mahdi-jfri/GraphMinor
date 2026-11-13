module

public import GraphMinor.Compute.GM06Alg34MarkCellList
import GraphMinor.Compute.GM06Alg34MarkCellFacts

/-!
# Marking the two supplied boundary lists of a region

Vertices use their old numeric labels, while edges follow the vertex
range in the packed cell numbering. Mark the vertex list with offset
zero, then the edge list with the supplied vertex count as offset.
The input cursor passes exactly the two length-prefixed lists.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Mark one region's vertex and edge boundary lists at the current row offset. -/
def gm06MarkRegionBoundaryProg : Cmd :=
  .seq (.assign 174 (.const 0))
    (.seq gm06MarkCellListProg
      (.seq (.assign 174 (.reg 100)) gm06MarkCellListProg))

/-- The two supplied boundary lists produce exactly their packed closure
incidences, with linear work and preservation of other matrix rows. -/
theorem gm06MarkRegionBoundaryProg_exec {w off row n : ℕ} (V E tail : List ℕ)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w)
    (hoff : off + 2 + V.length + E.length < 2 ^ w) {s : State}
    (hs : AtStream 0 off (GM06DrawingData.listWords V ++ GM06DrawingData.listWords E ++ tail) s)
    (hp : s.regs 103 = off) (hr : s.regs 173 = row) (hnreg : s.regs 100 = n)
    (hlen : (s.arrs 12).length < 2 ^ w)
    (hV : ∀ v ∈ V, row + 0 + v < (s.arrs 12).length)
    (hE : ∀ e ∈ E, row + n + e < (s.arrs 12).length) :
    ∃ s' t, Exec w gm06MarkRegionBoundaryProg s s' t ∧ t ≤ 20 * (V.length + E.length) + 22 ∧
      s'.arrs 12 = gm06MarkCells row n E (gm06MarkCells row 0 V (s.arrs 12)) ∧
      s'.regs 103 = off + 2 + V.length + E.length ∧
      AtStream 0 (off + 2 + V.length + E.length) tail s' ∧
      s'.regs 174 = n ∧
      (∀ a : ℕ, a ≠ 12 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 103 → q ≠ 109 → q ≠ 172 → q ≠ 174 → s'.regs q = s.regs q) := by
  let s₀ := s.setReg 174 0
  have he₀ : Exec w (.assign 174 (.const 0)) s s₀ 2 :=
    .assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  have hs₀ : AtStream 0 off
      (GM06DrawingData.listWords V ++ (GM06DrawingData.listWords E ++ tail)) s₀ := by
    simpa only [List.append_assoc] using hs.of_arr_eq (s' := s₀) rfl
  obtain ⟨s₁, t₁, he₁, ht₁, hbuf₁, hp₁, _, hs₁, ha₁, hr₁⟩ :=
    gm06MarkCellListProg_exec V (GM06DrawingData.listWords E ++ tail) hw (by omega) hs₀
      (by simp [s₀, hp]) (by simp [s₀, hr]) (by simp [s₀]) hlen hV
  have hn₁ : s₁.regs 100 = n :=
    (hr₁ 100 (by decide) (by decide) (by decide)).trans hnreg
  let s₂ := s₁.setReg 174 n
  have he₂ : Exec w (.assign 174 (.reg 100)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, hn₁, hn])
  have hlen₂ : (s₂.arrs 12).length = (s.arrs 12).length := by
    change (s₁.arrs 12).length = _
    rw [hbuf₁, gm06MarkCells_length]
    rfl
  have hp₂ : s₂.regs 103 = off + 1 + V.length := by simp [s₂, hp₁]
  have hr₂ : s₂.regs 173 = row := by
    rw [State.setReg_regs_ne _ _ (by decide : 173 ≠ 174),
      hr₁ 173 (by decide) (by decide) (by decide)]
    simpa [s₀] using hr
  obtain ⟨s₃, t₃, he₃, ht₃, hbuf₃, hp₃, _, hs₃, _, hr₃⟩ :=
    gm06MarkCellListProg_exec (s := s₂) (row := row) (shift := n) E tail hw (by omega) (hs₁.of_arr_eq (s' := s₂) rfl) hp₂ hr₂
      (by simp [s₂]) (hlen₂ ▸ hlen) (fun e he => by rw [hlen₂]; exact hE e he)
  have hex : Exec w gm06MarkRegionBoundaryProg s s₃ (2 + (t₁ + (2 + t₃))) :=
    .seq he₀ (.seq he₁ (.seq he₂ he₃))
  refine ⟨s₃, _, hex, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbuf₃]
    change gm06MarkCells row n E (s₁.arrs 12) = _
    rw [hbuf₁]
    rfl
  · omega
  · convert hs₃ using 1 <;> omega
  · rw [hr₃ 174 (by decide) (by decide) (by decide)]
    simp [s₂]
  · intro a ha
    exact hex.arrs_eq_of_not_mem_writtenArrs (by
      simp [gm06MarkRegionBoundaryProg, gm06MarkCellListProg, gm06MarkCellLoopProg,
        gm06MarkCellProg, readStreamWordProg, Cmd.writtenArrs, ha])
  · intro q hqp hqv hqc hqs
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simp [gm06MarkRegionBoundaryProg, gm06MarkCellListProg, gm06MarkCellLoopProg,
        gm06MarkCellProg, readStreamWordProg, Cmd.writtenRegs, hqp, hqv, hqc, hqs])

end GraphMinor.Compute
