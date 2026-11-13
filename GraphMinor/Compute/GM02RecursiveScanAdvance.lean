module

public import GraphMinor.Compute.GM02RecursiveScanProgram

/-!
# Advancing the crossing-scheme scan

An absent catalogue code causes no recursive call. Its branch increments
only the scan index, and the fixed dispatch adds a bounded constant cost.
At the end of the code range, copy the accumulated feasibility bit into
the answer register and switch to the return state.
-/

public section
namespace GraphMinor.Compute
open Classical

/-- A missing fixed catalogue code advances exactly one position. -/
theorem gm02RecursiveScanCodeProg_absent_exec {w : ℕ} (q : ℕ)
    (B : GM02BoundaryInput) (i : Fin (gm02RecursiveCodeBound q)) (s : State)
    (hcat : s.regs 330 = gm02BoundarySchemeSetCode (gm02RecursiveBoundaryBound q) B)
    (hi : ¬∃ C : B.schemes, gm02BoundarySchemeCode B C = i.val)
    (hcode : s.regs (gm02RecursiveControlBase q + 4) = i.val)
    (hcodes : 2 ^ gm02RecursiveCodeBound q ≤ 2 ^ w) (hw : 2 < 2 ^ w)
    (hnext : i.val + 1 < 2 ^ w) :
    Exec w (gm02RecursiveScanCodeProg q i.val) s
      (s.setReg (gm02RecursiveControlBase q + 4) (i.val + 1)) 9 := by
  have hg := gm02CatalogueBitExpr_invalid B i s hcat hcodes hw hi
  have he : Exec w (.assign (gm02RecursiveControlBase q + 4)
      (.op .add (.reg (gm02RecursiveControlBase q + 4)) (.const 1))) s
      (s.setReg (gm02RecursiveControlBase q + 4) (i.val + 1)) 4 := by
    apply Exec.assign
    simp [Expr.eval, BinOp.eval, BinOp.raw, hcode,
      checkWord_of_lt (by omega : i.val < 2 ^ w),
      checkWord_of_lt (by omega : 1 < 2 ^ w), checkWord_of_lt hnext]
  exact Exec.ite_false hg he

/-- The full scan command dispatches an absent code and changes no other data. -/
theorem gm02RecursiveScanProg_absent_exec {w : ℕ} (q : ℕ)
    (B : GM02BoundaryInput) (i : Fin (gm02RecursiveCodeBound q)) (s : State)
    (hcat : s.regs 330 = gm02BoundarySchemeSetCode (gm02RecursiveBoundaryBound q) B)
    (hi : ¬∃ C : B.schemes, gm02BoundarySchemeCode B C = i.val)
    (hcode : s.regs (gm02RecursiveControlBase q + 4) = i.val)
    (hcodes : 2 ^ gm02RecursiveCodeBound q ≤ 2 ^ w) (hw : 2 < 2 ^ w)
    (hK : gm02RecursiveCodeBound q < 2 ^ w) :
    ∃ t, Exec w (gm02RecursiveScanProg q) s
        (s.setReg (gm02RecursiveControlBase q + 4) (i.val + 1)) t ∧
      t ≤ 12 + 4 * gm02RecursiveCodeBound q := by
  let K := gm02RecursiveCodeBound q
  have hpos : 0 < K := gm02BoundarySchemeCodeBound_pos _
  have he := gm02RecursiveScanCodeProg_absent_exec q B i s hcat hi hcode hcodes hw
    (by have := i.isLt; omega)
  have he' : Exec w (gm02RecursiveScanCodeProg q (s.regs (gm02RecursiveControlBase q + 4))) s
      (s.setReg (gm02RecursiveControlBase q + 4) (i.val + 1)) 9 := by
    simpa only [hcode] using he
  obtain ⟨t, ht, htime⟩ := branchValProg_exec (gm02RecursiveControlBase q + 4)
    (gm02RecursiveScanCodeProg q) (K - 1) (by have := i.isLt; omega) (by omega) he'
  have hg : (.op .lt (.reg (gm02RecursiveControlBase q + 4)) (.const K) : Expr).eval w s = some 1 := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, hcode, i.isLt,
      checkWord_of_lt (i.isLt.trans hK), checkWord_of_lt hK,
      checkWord_of_lt (by omega : 1 < 2 ^ w), K]
  exact ⟨3 + t, Exec.ite_true (v := 1) hg (by decide) ht, by omega⟩

/-- Once the code range is exhausted, the accumulated answer is returned verbatim. -/
theorem gm02RecursiveScanProg_done_exec {w : ℕ} (q : ℕ) (s : State) (answer : ℕ)
    (hcode : s.regs (gm02RecursiveControlBase q + 4) = gm02RecursiveCodeBound q)
    (hanswer : s.regs (gm02RecursiveControlBase q + 5) = answer)
    (hK : gm02RecursiveCodeBound q < 2 ^ w) (ha : answer < 2 ^ w) (hw : 3 < 2 ^ w) :
    Exec w (gm02RecursiveScanProg q) s
      ((s.setReg outReg answer).setReg (gm02RecursiveControlBase q + 18) 3) 7 := by
  have hg : (.op .lt (.reg (gm02RecursiveControlBase q + 4))
      (.const (gm02RecursiveCodeBound q)) : Expr).eval w s = some 0 := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, hcode, checkWord_of_lt hK,
      checkWord_of_lt (by omega : 0 < 2 ^ w)]
  have he₁ : Exec w (.assign outReg (.reg (gm02RecursiveControlBase q + 5))) s
      (s.setReg outReg answer) 2 := Exec.assign (by simp [Expr.eval, hanswer, checkWord_of_lt ha])
  have he₂ : Exec w (.assign (gm02RecursiveControlBase q + 18) (.const 3))
      (s.setReg outReg answer) ((s.setReg outReg answer).setReg (gm02RecursiveControlBase q + 18) 3) 2 :=
    Exec.assign (checkWord_of_lt hw)
  exact Exec.ite_false hg (Exec.seq he₁ he₂)

end GraphMinor.Compute
