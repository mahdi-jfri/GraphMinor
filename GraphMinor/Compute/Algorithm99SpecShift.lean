module

public import GraphMinor.Compute.Algorithm99SpecInner
public import GraphMinor.Compute.Algorithm33Multigraph

/-!
# Shifting Algorithm (9.9) into the caller's memory

The inner program runs above the caller's arrays and above register 52. Its
tag and tree size are then copied into registers 51 and 52. The finishing
commands preserve every array and every register below 50.
-/

@[expose] public section
namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Copy the shifted tag and, in case (i), the shifted tree size. -/
def alg99SpecFinishProg : Cmd :=
  .seq (.assign 51 (.reg 80))
    (.ite (.op .eq (.reg 51) (.const 0)) (.assign 52 (.reg 83)) .skip)

/-- Run the inner program above the caller memory, then write its output registers. -/
def alg99SpecProg (P72 P97 P : Cmd) (pp h : ℕ) (h2 : 2 ≤ h)
    (h' : ℕ) (h2' : 2 ≤ h') (B Q : ℕ) : Cmd :=
  .seq ((alg99SpecInnerProg P72 P97 P pp h h2 h' h2' B Q).shift (alg105ArrBase pp) 53)
    alg99SpecFinishProg

/-- The final two register writes take at most seven steps and leave arrays
unchanged. The conditional tree-size bound is needed only in case (i). -/
theorem alg99SpecFinishProg_exec {w : ℕ} (b : ℕ) (s sub : State)
    (hw : 3 < 2 ^ w) (htag : sub.regs 27 ≤ 2)
    (htree : sub.regs 27 = 0 → sub.regs 30 < 2 ^ w) :
    ∃ s' time, Exec w alg99SpecFinishProg (s.applyShifted b 53 sub) s' time ∧
      time ≤ 7 ∧ s'.regs 51 = sub.regs 27 ∧
      (sub.regs 27 = 0 → s'.regs 52 = sub.regs 30) ∧
      (∀ a, s'.arrs a = (s.applyShifted b 53 sub).arrs a) ∧
      (∀ r < 50, s'.regs r = s.regs r) := by
  let mid := s.applyShifted b 53 sub
  let s₁ := mid.setReg 51 (sub.regs 27)
  have htagw : sub.regs 27 < 2 ^ w := by omega
  have he₁ : Exec w (.assign 51 (.reg 80)) mid s₁ 2 :=
    .assign (by simp [mid, State.applyShifted, Expr.eval, checkWord, htagw])
  by_cases hz : sub.regs 27 = 0
  · let s₂ := s₁.setReg 52 (sub.regs 30)
    have he₂ : Exec w (.assign 52 (.reg 83)) s₁ s₂ 2 :=
      .assign (by simp [s₁, mid, State.applyShifted, Expr.eval, checkWord, htree hz])
    refine ⟨s₂, 7, .seq he₁ (.ite_true (v := 1) ?_ one_ne_zero he₂), by decide,
      by simp [s₂, s₁], (fun _ => by simp [s₂]), (fun _ => rfl), ?_⟩
    · simp [s₁, hz, Expr.eval, BinOp.eval, BinOp.raw, checkWord, show 1 < 2 ^ w by omega]
    · intro r hr
      simp only [s₂, s₁, State.setReg_regs_ne _ _ (show r ≠ 52 by romega),
        State.setReg_regs_ne _ _ (show r ≠ 51 by romega)]
      exact State.applyShifted_regs_lt b 53 s sub (by romega)
  · refine ⟨s₁, 6, .seq he₁ (.ite_false ?_ (.skip _)), by decide,
      by simp [s₁], (fun h => (hz h).elim), (fun _ => rfl), ?_⟩
    · simp [s₁, hz, Expr.eval, BinOp.eval, BinOp.raw, checkWord, htagw]
    · intro r hr
      simp only [s₁, State.setReg_regs_ne _ _ (show r ≠ 51 by romega)]
      exact State.applyShifted_regs_lt b 53 s sub (by romega)

end GraphMinor.Compute
