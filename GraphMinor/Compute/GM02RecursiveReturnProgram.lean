module

public import GraphMinor.Compute.GM02RecursiveScanProgram
public import GraphMinor.Compute.GM02RestoreFrame
public import GraphMinor.Compute.GM02PrepareBoundaryNumbering

/-!
# Returning from the two recursive side calls

A left answer is saved before the right call. A right answer contributes
to the parent's feasibility bit exactly when both sides are feasible.
Every width report immediately propagates to the parent. Restoring a
parent also restores its catalogue and recomputes the inverse boundary
names needed by the next selected child construction.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Record the left answer and dispatch its matching right recursive call. -/
noncomputable def gm02RecursiveAfterLeftProg (q : ℕ) : Cmd :=
  let b := gm02RecursiveControlBase q
  .seq (.assign (b + 6) (.reg outReg))
    (branchValProg (b + 4) (gm02RecursiveCallProg true q) (gm02RecursiveCodeBound q - 1))

/-- Add a pair of feasible side answers to the parent accumulator, then continue scanning. -/
def gm02RecursiveAfterRightProg (q : ℕ) : Cmd :=
  let b := gm02RecursiveControlBase q
  .seq (.assign (b + 3) (.op .mod (.reg (b + 3)) (.const 2)))
    (.seq (.assign (b + 5) (.op .sub (.const 1)
        (.op .mul (.op .sub (.const 1) (.reg (b + 5)))
          (.op .sub (.const 1) (.op .mul (.reg (b + 6)) (.reg outReg))))))
      (.seq (.assign (b + 4) (.op .add (.reg (b + 4)) (.const 1)))
        (.assign (b + 18) (.const 2))))

/-- Restore the saved catalogue and recompute its compact boundary names. -/
def gm02RecursiveRestoreBoundaryProg (q : ℕ) : Cmd :=
  .seq (.assign 330 (.reg (gm02RecursiveControlBase q + 7)))
    (gm02PrepareBoundaryNumberingProg (gm02RecursiveParentArr q))

/-- Return to a saved parent, propagate width, or finish at the root. -/
noncomputable def gm02RecursiveReturnProg (q : ℕ) : Cmd :=
  let p := gm02RecursiveParentArr q
  let b := gm02RecursiveControlBase q
  .ite (.op .eq (.reg (b + 10)) (.const 0)) (.assign (b + 18) (.const 0))
    (.seq (gm02RestoreFrameProg (gm02RecursiveStackArr q) (gm02RecursiveZeroArr q) p 1 2 b)
      (.ite (.op .eq (.reg outReg) (.const 2)) (.assign (b + 18) (.const 3))
        (.seq (gm02RecursiveRestoreBoundaryProg q)
          (.ite (.op .lt (.reg (b + 3)) (.const 2))
            (gm02RecursiveAfterLeftProg q) (gm02RecursiveAfterRightProg q)))))

end GraphMinor.Compute
