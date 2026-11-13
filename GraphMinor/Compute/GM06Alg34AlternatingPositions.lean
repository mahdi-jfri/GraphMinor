module

public import GraphMinor.Compute.GM06Alg34BetweenExpressions

/-!
# Evaluating alternating boundary positions on the RAM

A primal cuff position is doubled. Its following gap gets the next
odd position. These expressions require only the original position
register and have constant cost. The doubled cuff bound ensures that
both expressions fit a word.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The even slot occupied by a primal boundary vertex. -/
def gm06EvenPosition (r : ℕ) : Expr := .op .mul (.const 2) (.reg r)

/-- The odd slot of the gap following a primal boundary vertex. -/
def gm06OddPosition (r : ℕ) : Expr := .op .add (gm06EvenPosition r) (.const 1)

/-- Doubling a supplied position computes its exact even slot. -/
theorem gm06EvenPosition_eval {w r k : ℕ} {s : State}
    (hw : 2 < 2 ^ w) (hr : s.regs r = k) (hk : 2 * k + 1 < 2 ^ w) :
    (gm06EvenPosition r).eval w s = some (2 * k) := by
  have hkw : k < 2 ^ w := by omega
  have htw : 2 * k < 2 ^ w := by omega
  simp [gm06EvenPosition, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr, hkw, htw, hw]

/-- The gap expression computes the exact following odd slot. -/
theorem gm06OddPosition_eval {w r k : ℕ} {s : State}
    (hw : 2 < 2 ^ w) (hr : s.regs r = k) (hk : 2 * k + 1 < 2 ^ w) :
    (gm06OddPosition r).eval w s = some (2 * k + 1) := by
  have he := gm06EvenPosition_eval hw hr hk
  have hw1 : 1 < 2 ^ w := by omega
  unfold gm06OddPosition
  simp only [Expr.eval, he]
  simp [BinOp.eval, BinOp.raw, checkWord, hw1, hk]

end GraphMinor.Compute
