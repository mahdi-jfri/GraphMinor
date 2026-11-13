module

public import GraphMinor.Compute.GM06Alg34EndsFold
public import GraphMinor.Compute.GM06Alg34EdgeMaskProg

/-!
# Building the induced endpoint section on the RAM

Allocate twice the computed surviving-edge count, then scan the old
endpoint section using the masks and rank tables. The resulting array
is exactly the new finite payload's endpoint section. All other arrays
are preserved, and the work is linear in the old and new edge counts.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Allocate the new endpoint section and emit surviving old edges. -/
def gm06EndsProg : Cmd :=
  .seq (.alloc 8 (.op .mul (.const 2) (.reg 137)))
    (.seq (.assign 134 (.reg 101))
      (.seq (.assign 135 (.const 0))
        (.seq (.assign 103 (.const 3)) gm06EndsLoopProg)))

/-- The supplied endpoint section and computed finite tables produce
exactly the new endpoint words, with a linear RAM time bound. -/
theorem gm06EndsProg_exec {w : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (tail : List ℕ)
    (hw : 3 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hoff : 3 + 2 * x.ends.length < 2 ^ w)
    (hout : 2 * (x.activeEdges vs).length < 2 ^ w) {s : State}
    (hstream : AtStream 0 3 (x.endpointWords ++ tail) s)
    (hcount : s.regs 101 = x.ends.length)
    (hnewcount : s.regs 137 = (x.activeEdges vs).length)
    (hV : s.arrs 5 = gm06VertexRanks vs) (hE : s.arrs 7 = gm06EdgeRanks x vs)
    (hmask : s.arrs 6 = gm06EdgeMask x vs) :
    ∃ s' t, Exec w gm06EndsProg s s' t ∧
      t ≤ 45 * x.ends.length + 2 * (x.activeEdges vs).length + 10 ∧
      s'.arrs 8 = (x.inducedData vs).endpointWords ∧
      s'.regs 103 = 3 + 2 * x.ends.length ∧
      AtStream 0 (3 + 2 * x.ends.length) tail s' ∧
      (∀ a : ℕ, a ≠ 8 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 103 → q ≠ 132 → q ≠ 133 → q ≠ 134 → q ≠ 135 →
        s'.regs q = s.regs q) := by
  have hm : x.ends.length < 2 ^ w := by omega
  have hnew : (x.activeEdges vs).length < 2 ^ w := by omega
  have h2 : 2 < 2 ^ w := by omega
  let s₀ := s.setArr 8 (List.replicate (2 * (x.activeEdges vs).length) 0)
  let s₁ := s₀.setReg 134 x.ends.length
  let s₂ := s₁.setReg 135 0
  let s₃ := s₂.setReg 103 3
  have he₀ : Exec w (.alloc 8 (.op .mul (.const 2) (.reg 137))) s s₀
      (3 + 2 * (x.activeEdges vs).length) :=
    .alloc (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hnewcount, h2, hnew, hout])
  have he₁ : Exec w (.assign 134 (.reg 101)) s₀ s₁ 2 :=
    .assign (by simp [s₀, Expr.eval, checkWord, hcount, hm])
  have he₂ : Exec w (.assign 135 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  have he₃ : Exec w (.assign 103 (.const 3)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  have hs₃ : AtStream 0 3 (gm06EdgeStream x (List.finRange x.ends.length) ++ tail) s₃ := by
    rw [gm06EdgeStream_all]
    exact hstream.of_arr_eq (by simp [s₃, s₂, s₁, s₀])
  have hlabels : (List.finRange x.ends.length).map Fin.val =
      List.range' 0 (List.finRange x.ends.length).length := by
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simp
  obtain ⟨s₄, t₄, he₄, ht₄, hout₄, hp₄, _, _, hs₄, _, _⟩ :=
    gm06EndsLoopProg_exec (off := 3) (k := 0) (s := s₃) x vs
      (List.finRange x.ends.length) tail (by omega) hn hm
      (by simpa only [List.length_finRange] using hoff)
      (by simpa only [List.length_finRange, Nat.zero_add] using hm) hout hlabels
      hs₃ (by simp [s₃]) (by simp [s₃, s₂]) (by simp [s₃, s₂, s₁])
      (by simpa [s₃, s₂, s₁, s₀] using hV) (by simpa [s₃, s₂, s₁, s₀] using hE)
      (by simpa [s₃, s₂, s₁, s₀] using hmask) (by simp [s₃, s₂, s₁, s₀])
  have hex : Exec w gm06EndsProg s s₄
      ((3 + 2 * (x.activeEdges vs).length) + (2 + (2 + (2 + t₄)))) :=
    .seq he₀ (.seq he₁ (.seq he₂ (.seq he₃ he₄)))
  refine ⟨s₄, _, hex, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_finRange] at ht₄
    omega
  · rw [hout₄]
    exact gm06RelabelEndsWrite_fold_all x vs _ (by simp [s₃, s₂, s₁, s₀])
  · simpa only [List.length_finRange] using hp₄
  · simpa only [List.length_finRange] using hs₄
  · intro a ha
    exact hex.arrs_eq_of_not_mem_writtenArrs (by
      simp [gm06EndsProg, gm06EndsLoopProg, gm06EndsStepProg, gm06WriteEndsProg,
        gm06ReadEndsProg, readStreamWordProg, Cmd.writtenArrs, ha])
  · intro q hq hqA hqB hqc hqi
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simp [gm06EndsProg, gm06EndsLoopProg, gm06EndsStepProg, gm06WriteEndsProg,
        gm06ReadEndsProg, readStreamWordProg, Cmd.writtenRegs, hq, hqA, hqB, hqc, hqi])

end GraphMinor.Compute
