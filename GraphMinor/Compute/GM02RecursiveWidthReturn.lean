module

public import GraphMinor.Compute.GM02RecursiveReturnProgram
public import GraphMinor.Compute.GM02RecursiveFrameWrites

/-!
# Propagating a returned width report through a saved frame

A child width report bypasses the parent's remaining scheme scan. Pop
the exact parent frame and retain answer flag two, then remain in the
return state. The parent's graph and sides are restored, its older
stack prefix is retained, and root size and capacity do not change.
-/

public section
namespace GraphMinor.Compute

/-- Returning a width report restores the parent and immediately propagates its flag. -/
theorem gm02RecursiveReturnProg_width_exec {w cap : ℕ} (q : ℕ)
    (P L R pref : List ℕ) (mode code aggregate leftAnswer catalogue : ℕ) (s : State)
    (hw : 3 < 2 ^ w) (hlen : pref.length + 9 + P.length + L.length + R.length < 2 ^ w)
    (hPw : ∀ v ∈ P, v < 2 ^ w) (hLw : ∀ v ∈ L, v < 2 ^ w) (hRw : ∀ v ∈ R, v < 2 ^ w)
    (hheader : ∀ v ∈ gm02SavedFrameHeader P L R mode code aggregate leftAnswer catalogue, v < 2 ^ w)
    (hstack : s.arrs (gm02RecursiveStackArr q) = pref ++
      gm02SavedFrameWords P L R mode code aggregate leftAnswer catalogue pref.length ++ List.replicate cap 0)
    (hpos : s.regs (gm02RecursiveControlBase q + 10) = pref.length + 9 + P.length + L.length + R.length)
    (hflag : s.regs outReg = 2) :
    let b := gm02RecursiveControlBase q
    ∃ s' t, Exec w (gm02RecursiveReturnProg q) s s' t ∧
      t ≤ 34 * (P.length + L.length + R.length) + 301 ∧
      s'.arrs (gm02RecursiveParentArr q) = P ∧ s'.arrs 1 = L ∧ s'.arrs 2 = R ∧
      s'.regs outReg = 2 ∧ s'.regs (b + 18) = 3 ∧ s'.regs (b + 10) = pref.length ∧
      IsPrefixBuffer (gm02RecursiveStackArr q) pref (9 + P.length + L.length + R.length + cap) s' ∧
      (∀ offset : ℕ, 18 < offset → s'.regs (b + offset) = s.regs (b + offset)) := by
  let p := gm02RecursiveParentArr q
  let b := gm02RecursiveControlBase q
  let stack := gm02RecursiveStackArr q
  let scratch := gm02RecursiveZeroArr q
  have hpg := gm02RecursiveParentArr_ge q
  have hbg := gm02RecursiveControlBase_ge q
  have hgeom : stack ≠ p ∧ stack ≠ 1 ∧ stack ≠ 2 ∧ scratch ≠ stack ∧
      p ≠ 1 ∧ p ≠ 2 ∧ (1 : Arr) ≠ 2 ∧ p ≠ scratch ∧ (1 : Arr) ≠ scratch ∧ (2 : Arr) ≠ scratch := by
    dsimp only [p, stack, scratch, gm02RecursiveStackArr, gm02RecursiveZeroArr, Arr] at *
    omega
  obtain ⟨s₁, t₁, he₁, ht₁, hP₁, hL₁, hR₁, _, _, _, _, _, hpos₁, hstack₁, hr₁⟩ :=
    gm02RestoreFrameProg_exec stack scratch p 1 2 b
      hgeom.1 hgeom.2.1 hgeom.2.2.1 hgeom.2.2.2.1 hgeom.2.2.2.2.1
      hgeom.2.2.2.2.2.1 hgeom.2.2.2.2.2.2.1 hgeom.2.2.2.2.2.2.2.1
      hgeom.2.2.2.2.2.2.2.2.1 hgeom.2.2.2.2.2.2.2.2.2
      P L R pref mode code aggregate leftAnswer catalogue s (by omega) hlen hPw hLw hRw hheader hstack hpos
  have hflag₁ : s₁.regs outReg = 2 :=
    (hr₁ _ (by dsimp only [b, outReg, Reg] at *; omega)).trans hflag
  have hg : (.op .eq (.reg (b + 10)) (.const 0) : Expr).eval w s = some 0 := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, b, hpos,
      checkWord_of_lt hlen, checkWord_of_lt (by omega : 0 < 2 ^ w)]
  have hi : (.op .eq (.reg outReg) (.const 2) : Expr).eval w s₁ = some 1 := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, hflag₁,
      checkWord_of_lt (by omega : 2 < 2 ^ w), checkWord_of_lt (by omega : 1 < 2 ^ w)]
  let s₂ := s₁.setReg (b + 18) 3
  have he₂ : Exec w (.assign (b + 18) (.const 3)) s₁ s₂ 2 := Exec.assign (checkWord_of_lt hw)
  have he : Exec w (gm02RecursiveReturnProg q) s s₂ (3 + (t₁ + (3 + 2))) :=
    Exec.ite_false hg (Exec.seq he₁ (Exec.ite_true (v := 1) hi (by decide) he₂))
  refine ⟨s₂, _, he, by omega, hP₁, hL₁, hR₁, ?_, by simp [s₂, b], ?_, hstack₁, ?_⟩
  · exact (State.setReg_regs_ne _ _ (by dsimp only [b, outReg, Reg] at *; omega)).trans hflag₁
  · exact (State.setReg_regs_ne _ _ (by dsimp only [Reg]; omega)).trans hpos₁
  · intro offset hoff
    exact (State.setReg_regs_ne _ _ (by dsimp only [Reg] at *; omega)).trans
      (he₁.regs_eq_of_not_mem_writtenRegs (gm02RecursiveRestoreFrame_high_not_written q offset hoff))

end GraphMinor.Compute
