module

public import GraphMinor.Compute.Basic

/-!
# Emitting an updated gap region number

Write the computed region number at the live end of the gap buffer,
then advance its count. The step preserves every other register and
array and takes seven RAM operations.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Append region register 6401 to buffer 48 with live count 6404. -/
def gm06GapUpdateEmitProg : Cmd :=
  .seq (.write 48 (.reg 6404) (.reg 6401))
    (.assign 6404 (.op .add (.reg 6404) (.const 1)))

/-- The gap emission step performs exactly one consecutive buffer write. -/
theorem gm06GapUpdateEmitProg_exec {w k v : ℕ} (hw : 1 < 2 ^ w)
    (hk : k + 1 < 2 ^ w) (hv : v < 2 ^ w) {s : State}
    (hcount : s.regs 6404 = k) (hvalue : s.regs 6401 = v)
    (hcap : k < (s.arrs 48).length) :
    Exec w gm06GapUpdateEmitProg s ((s.writeArr 48 k v).setReg 6404 (k + 1)) 7 := by
  have hkw : k < 2 ^ w := by omega
  refine .seq (.write ?_ ?_ hcap) (.assign ?_)
  · simp [Expr.eval, checkWord, hcount, hkw]
  · simp [Expr.eval, checkWord, hvalue, hv]
  · simp [Expr.eval, checkWord, BinOp.eval, BinOp.raw, hcount, hkw, hk, hw]

end GraphMinor.Compute
