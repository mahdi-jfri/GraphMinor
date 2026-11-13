module

public import GraphMinor.Compute.GM02RecursiveCallProgram
public import GraphMinor.Compute.GM02RecursiveFrameWrites
import GraphMinor.Compute.GM02RecursiveWorkFrames
import GraphMinor.Compute.CrossingOpsCycleTest

/-!
# Saving a parent and entering its constructed child

The child already occupies its plain-input work array. Save the exact
parent arrays and continuation metadata, copy that child into the
current input, and enter the opposite phase. The proof records the
actual saved frame and preserves the root-size and capacity words.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Pushing an already constructed child saves its exact parent continuation. -/
theorem gm02RecursivePushChildProg_exec {w cap : ℕ} (right : Bool) (q : ℕ)
    (P L R child pref : List ℕ) (phase code aggregate leftAnswer catalogue : ℕ) (s : State)
    (hP : s.arrs (gm02RecursiveParentArr q) = P) (hL : s.arrs 1 = L) (hR : s.arrs 2 = R)
    (hchild : s.arrs (gm02RecursiveTemplateArr q + 14) = child)
    (hphase : s.regs (gm02RecursiveControlBase q + 3) = phase)
    (hcode : s.regs (gm02RecursiveControlBase q + 4) = code)
    (hagg : s.regs (gm02RecursiveControlBase q + 5) = aggregate)
    (hleft : s.regs (gm02RecursiveControlBase q + 6) = leftAnswer)
    (hcat : s.regs 330 = catalogue) (hph : phase ≤ 1)
    (hw : 3 < 2 ^ w) (hframe : pref.length + 9 + P.length + L.length + R.length < 2 ^ w)
    (hclen : child.length < 2 ^ w)
    (hPw : ∀ v ∈ P, v < 2 ^ w) (hLw : ∀ v ∈ L, v < 2 ^ w)
    (hRw : ∀ v ∈ R, v < 2 ^ w) (hchildw : ∀ v ∈ child, v < 2 ^ w)
    (hc : code < 2 ^ w) (ha : aggregate < 2 ^ w) (hl : leftAnswer < 2 ^ w) (hcatw : catalogue < 2 ^ w)
    (hstack : IsPrefixBuffer (gm02RecursiveStackArr q) pref
      (9 + P.length + L.length + R.length + cap) s)
    (hpos : s.regs (gm02RecursiveControlBase q + 10) = pref.length) :
    let tag := phase + if right then 2 else 0
    let b := gm02RecursiveControlBase q
    ∃ s' t, Exec w (gm02RecursivePushChildProg right q) s s' t ∧
      t ≤ 17 * (P.length + L.length + R.length) + 16 * child.length + 110 ∧
      IsPrefixBuffer (gm02RecursiveStackArr q)
        (pref ++ gm02SavedFrameWords P L R tag code aggregate leftAnswer catalogue pref.length) cap s' ∧
      s'.arrs (gm02RecursiveParentArr q) = child ∧ s'.arrs 1 = L ∧ s'.arrs 2 = R ∧
      s'.regs (b + 10) = pref.length + 9 + P.length + L.length + R.length ∧
      s'.regs (b + 3) = 1 - phase ∧ s'.regs (b + 18) = 1 ∧
      (∀ offset : ℕ, 18 < offset → s'.regs (b + offset) = s.regs (b + offset)) := by
  let p := gm02RecursiveParentArr q
  let a := gm02RecursiveTemplateArr q
  let b := gm02RecursiveControlBase q
  let stack := gm02RecursiveStackArr q
  let tag := phase + if right then 2 else 0
  have hpg := gm02RecursiveParentArr_ge q
  have hbg := gm02RecursiveControlBase_ge q
  have htag : tag ≤ 3 := by cases right <;> simp only [tag, Bool.false_eq_true, ↓reduceIte] <;> omega
  have htagMod : tag % 2 = phase := by cases right <;> simp only [tag, Bool.false_eq_true, ↓reduceIte] <;> omega
  let s₁ := s.setReg (b + 3) tag
  have he₁ : Exec w (.assign (b + 3) (.op .add (.reg (b + 3)) (.const (if right then 2 else 0)))) s s₁ 4 := by
    apply Exec.assign
    exact eval_add (eval_reg hphase (by dsimp only [b, Reg] at *; omega)) (eval_const (by cases right <;> simp; omega)) (htag.trans_lt hw)
  have hs₁ (r : Reg) (hr : r ≠ b + 3) : s₁.regs r = s.regs r := State.setReg_regs_ne _ _ hr
  obtain ⟨s₂, t₂, he₂, ht₂, hstack₂, hpos₂, ha₂, hr₂⟩ :=
    gm02SaveFrameProg_exec p 1 2 stack (b + 10) (b + 8) (b + 12) (b + 13)
      (b + 3) (b + 4) (b + 5) (b + 6) 330
      (by dsimp only [p, stack, gm02RecursiveStackArr, Arr]; omega)
      (by dsimp only [p, stack, gm02RecursiveStackArr, Arr] at *; omega)
      (by dsimp only [p, stack, gm02RecursiveStackArr, Arr] at *; omega)
      (by dsimp only [b, Reg] at *; omega) (by dsimp only [b, Reg] at *; omega) (by dsimp only [b, Reg] at *; omega) (by dsimp only [b, Reg] at *; omega)
      (by intro r hr; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
          dsimp only [b, Reg] at *; omega)
      (by intro r hr; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
          dsimp only [b, Reg] at *; omega)
      P L R pref tag code aggregate leftAnswer catalogue s₁ (by dsimp only [b, Reg] at *; omega) hframe hP hL hR hPw hLw hRw
      (by simp [s₁])
      ((hs₁ _ (by dsimp only [b, Reg] at *; omega)).trans hcode) ((hs₁ _ (by dsimp only [b, Reg] at *; omega)).trans hagg)
      ((hs₁ _ (by dsimp only [b, Reg] at *; omega)).trans hleft)
      ((hs₁ _ (by dsimp only [b, Reg] at *; omega)).trans hcat)
      (htag.trans_lt hw) hc ha hl hcatw hstack
      ((hs₁ _ (by dsimp only [b, Reg] at *; omega)).trans hpos)
  have hchild₂ : s₂.arrs (a + 14) = child := (ha₂ _
    (by dsimp only [a, stack, gm02RecursiveTemplateArr, gm02RecursiveStackArr, Arr]; omega)).trans hchild
  obtain ⟨s₃, t₃, he₃, ht₃, hchild₃, ha₃, _⟩ := copyArray72Prog_exec (a + 14) p 350 351
    (by dsimp only [a, p, gm02RecursiveTemplateArr, Arr]; omega) (by decide)
    child s₂ (by dsimp only [b, Reg] at *; omega) hclen hchildw hchild₂
  have hhigh₃ (offset : ℕ) : s₃.regs (b + offset) = s₂.regs (b + offset) :=
    gm02_regs_eq_of_low_writes he₃ (gm02CopyWorkArray_writtenRegs_subset _ _) _
      (by dsimp only [b, Reg] at *; omega)
  have hmode₃ : s₃.regs (b + 3) = tag := (hhigh₃ 3).trans
    ((hr₂ _ (by dsimp only [b, Reg] at *; omega) (by dsimp only [b, Reg] at *; omega) (by dsimp only [b, Reg] at *; omega)).trans (by simp [s₁]))
  let s₄ := s₃.setReg (b + 3) (1 - phase)
  have he₄ : Exec w (.assign (b + 3)
      (.op .sub (.const 1) (.op .mod (.reg (b + 3)) (.const 2)))) s₃ s₄ 6 := by
    apply Exec.assign
    simpa only [htagMod] using eval_sub (eval_const (by omega : 1 < 2 ^ w))
      (eval_mod (eval_reg hmode₃ (htag.trans_lt hw)) (eval_const (by omega : 2 < 2 ^ w)) (by decide))
  let s₅ := s₄.setReg (b + 18) 1
  have he₅ : Exec w (.assign (b + 18) (.const 1)) s₄ s₅ 2 := Exec.assign (eval_const (by dsimp only [b, Reg] at *; omega))
  refine ⟨s₅, 4 + (t₂ + (t₃ + (6 + 2))), Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅))),
    by omega, ?_, hchild₃, ?_, ?_, ?_, ?_, by simp [s₅, b], ?_⟩
  · exact hstack₂.of_arr_eq (ha₃ stack (by dsimp only [stack, p, gm02RecursiveStackArr, Arr]; omega))
  · exact (ha₃ 1 (by dsimp only [p, Arr] at *; omega)).trans
      ((ha₂ 1 (by dsimp only [stack, gm02RecursiveStackArr, Arr] at *; omega)).trans hL)
  · exact (ha₃ 2 (by dsimp only [p, Arr] at *; omega)).trans
      ((ha₂ 2 (by dsimp only [stack, gm02RecursiveStackArr, Arr] at *; omega)).trans hR)
  · exact (State.setReg_regs_ne _ _ (by dsimp only [b, Reg] at *; omega)).trans
      ((State.setReg_regs_ne _ _ (by dsimp only [b, Reg] at *; omega)).trans ((hhigh₃ 10).trans hpos₂))
  · simp [s₅, s₄, b]
  · intro offset hoff
    have hsav : s₂.regs (b + offset) = s₁.regs (b + offset) :=
      he₂.regs_eq_of_not_mem_writtenRegs (gm02RecursiveSaveFrame_not_written q _
        (by dsimp only [b, Reg] at *; omega) (by dsimp only [b, Reg] at *; omega) (by dsimp only [b, Reg] at *; omega) (by dsimp only [b, Reg] at *; omega) (by dsimp only [b, Reg] at *; omega))
    exact (State.setReg_regs_ne _ _ (by dsimp only [Reg] at *; omega)).trans
      ((State.setReg_regs_ne _ _ (by dsimp only [Reg] at *; omega)).trans
        ((hhigh₃ offset).trans (hsav.trans (hs₁ _ (by dsimp only [Reg] at *; omega)))))

end GraphMinor.Compute
