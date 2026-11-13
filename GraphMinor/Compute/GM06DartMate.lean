module

public import GraphMinor.Compute.CrossingOpsBasic

/-!
# Opposite directed ends in the cylinder input

Consecutive endpoint positions describe the two directed ends of one
edge. Swapping these positions preserves the edge and distinguishes
the two ends even for a loop. This is the local operation used when
following a boundary walk through an edge. Its RAM implementation
uses parity and one addition or subtraction.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- The opposite directed end of an edge, for consecutive endpoint labels. -/
def gm06DartMate (j : ℕ) : ℕ := if j % 2 = 0 then j + 1 else j - 1

/-- The opposite end is still a directed end of the same finite edge list. -/
theorem gm06DartMate_lt {j m : ℕ} (h : j < 2 * m) : gm06DartMate j < 2 * m := by
  unfold gm06DartMate
  split <;> omega

/-- Swapping ends twice returns to the original directed end. -/
theorem gm06DartMate_involutive : Function.Involutive gm06DartMate := by
  intro j
  unfold gm06DartMate
  split <;> split <;> omega

/-- The two directed ends remain distinct, including at a loop. -/
theorem gm06DartMate_ne (j : ℕ) : gm06DartMate j ≠ j := by
  unfold gm06DartMate
  split <;> omega

/-- Swapping ends preserves the undirected edge index. -/
theorem gm06DartMate_edge (j : ℕ) : gm06DartMate j / 2 = j / 2 := by
  unfold gm06DartMate
  split <;> omega

/-- Read a directed-end index in register 23 and put its opposite in register 24. -/
def gm06DartMateProg : Cmd :=
  .ite (.op .eq (.op .mod (.reg 23) (.const 2)) (.const 0))
    (.assign 24 (.op .add (.reg 23) (.const 1)))
    (.assign 24 (.op .sub (.reg 23) (.const 1)))

/-- The opposite-end operation takes exactly nine RAM steps. -/
theorem gm06DartMateProg_exec {w j m : ℕ} (s : State)
    (hw : 2 < 2 ^ w) (hn : 2 * m < 2 ^ w) (hj : j < 2 * m)
    (hr : s.regs 23 = j) :
    Exec w gm06DartMateProg s (s.setReg 24 (gm06DartMate j)) 9 := by
  have hjw : j < 2 ^ w := hj.trans hn
  have hmod : (Expr.op .mod (.reg 23) (.const 2)).eval w s = some (j % 2) := by
    simp [Expr.eval, hr, BinOp.eval, BinOp.raw, checkWord, hjw, hw,
      (Nat.mod_lt j (by decide : 0 < 2)).trans hw]
  have he := eval_eq hmod (eval_const (Nat.two_pow_pos w)) (by omega : 1 < 2 ^ w)
  by_cases hp : j % 2 = 0
  · have hfit : j + 1 < 2 ^ w := by
      have hh := (gm06DartMate_lt hj).trans hn
      simpa only [gm06DartMate, hp, ite_true] using hh
    have hb := Exec.assign (r := 24)
      (eval_add (eval_reg hr hjw) (eval_const (by omega : 1 < 2 ^ w)) hfit)
    simpa only [gm06DartMateProg, gm06DartMate, hp, ite_true, Expr.cost] using
      (Exec.ite_true (cond := .op .eq (.op .mod (.reg 23) (.const 2)) (.const 0)) (by simpa only [hp, ite_true] using he) (by decide : 1 ≠ 0) hb)
  · have hb := Exec.assign (r := 24)
      (eval_sub (eval_reg hr hjw) (eval_const (by omega : 1 < 2 ^ w)))
    simpa only [gm06DartMateProg, gm06DartMate, hp, ite_false, Expr.cost] using
      (Exec.ite_false (cond := .op .eq (.op .mod (.reg 23) (.const 2)) (.const 0)) (by simpa only [hp, ite_false] using he) hb)

end GraphMinor.Compute
