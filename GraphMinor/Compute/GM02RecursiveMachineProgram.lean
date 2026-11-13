module

public import GraphMinor.Compute.GM02RecursiveEnterProgram
public import GraphMinor.Compute.GM02RecursiveReturnProgram
public import GraphMinor.Compute.GM02SavedFrameBounds

/-!
# The alternating A1/A2 Word RAM machine

One loop dispatches three states: enter the current instance, scan its
crossing schemes, or return its answer through the saved parent stack.
The root starts in A2. Initialization copies the plain input into its
retained parent array and allocates the polynomial saved-frame buffer
from the supplied vertex-count header.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The saved-stack capacity as an expression in the root vertex-count register. -/
def gm02RecursiveCapacityExpr (q : ℕ) : Expr :=
  let r := gm02RecursiveControlBase q + 20
  .op .mul (.op .add (.op .mul (.const 2) (.reg r)) (.const 2))
    (.op .add (.op .add (.const 12) (.op .mul (.op .mul (.const 2) (.reg r)) (.reg r)))
      (.op .mul (.const 3) (.reg r)))

/-- The single-step dispatch for enter, scan, and return states. -/
noncomputable def gm02RecursiveMachineStepProg (q : ℕ) : Cmd :=
  let b := gm02RecursiveControlBase q
  .ite (.op .eq (.reg (b + 18)) (.const 1)) (gm02RecursiveEnterProg q)
    (.ite (.op .eq (.reg (b + 18)) (.const 2)) (gm02RecursiveScanProg q)
      (gm02RecursiveReturnProg q))

/-- Initialize the root A2 call and its polynomial saved-frame buffer from plain array 0. -/
def gm02RecursiveMachineInitProg (q : ℕ) : Cmd :=
  let p := gm02RecursiveParentArr q
  let b := gm02RecursiveControlBase q
  .seq (copyArray72Prog inArr p 350 351)
    (.seq (.assign (b + 20) (.read p (.const 0)))
      (.seq (.assign (b + 21) (gm02RecursiveCapacityExpr q))
        (.seq (.alloc (gm02RecursiveStackArr q) (.reg (b + 21)))
          (.seq (.assign (b + 10) (.const 0))
            (.seq (.assign (b + 3) (.const 1)) (.assign (b + 18) (.const 1)))))))

/-- The complete saved-frame alternating-recursion program on a plain terminated input. -/
noncomputable def gm02RecursiveMachineProg (q : ℕ) : Cmd :=
  .seq (gm02RecursiveMachineInitProg q)
    (.while (.reg (gm02RecursiveControlBase q + 18)) (gm02RecursiveMachineStepProg q))

end GraphMinor.Compute
