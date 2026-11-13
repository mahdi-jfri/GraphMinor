module

public import GraphMinor.Compute.GM02RecursiveCallProgram

/-!
# Scanning the fixed crossing-scheme catalogue

The scan index selects one fixed code branch. Skip a zero catalogue bit
and advance the index. A present code starts its left recursive call.
After all codes have been considered, return the accumulated feasibility
bit. The subsequent right call and accumulation are handled on return.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Process one fixed code in the catalogue scan. -/
noncomputable def gm02RecursiveScanCodeProg (q code : ℕ) : Cmd :=
  let b := gm02RecursiveControlBase q
  .ite (gm02CatalogueBitExpr code) (gm02RecursiveCallProg false q code)
    (.assign (b + 4) (.op .add (.reg (b + 4)) (.const 1)))

/-- Dispatch the scan index, or return the accumulated result at the range end. -/
noncomputable def gm02RecursiveScanProg (q : ℕ) : Cmd :=
  let b := gm02RecursiveControlBase q
  let K := gm02RecursiveCodeBound q
  .ite (.op .lt (.reg (b + 4)) (.const K))
    (branchValProg (b + 4) (gm02RecursiveScanCodeProg q) (K - 1))
    (.seq (.assign outReg (.reg (b + 5))) (.assign (b + 18) (.const 3)))

end GraphMinor.Compute
