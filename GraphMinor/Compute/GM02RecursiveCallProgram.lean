module

public import GraphMinor.Compute.GM02RecursiveMemory
public import GraphMinor.Compute.GM02SelectedRightChild
public import GraphMinor.Compute.GM02SaveFrame

/-!
# The saved-frame recursive call command

Construct the chosen canonical child while retaining the parent arrays.
Tag the parent phase with the side whose answer will return, save its
frame, copy the child's plain input into the current-parent array, and
enter the opposite A1/A2 phase. The saved mode is the parent phase plus
two for a right-child continuation.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Save the current parent and enter the already constructed child. -/
def gm02RecursivePushChildProg (right : Bool) (q : ℕ) : Cmd :=
  let p := gm02RecursiveParentArr q
  let a := gm02RecursiveTemplateArr q
  let b := gm02RecursiveControlBase q
  .seq (.assign (b + 3) (.op .add (.reg (b + 3)) (.const (if right then 2 else 0))))
    (.seq (gm02SaveFrameProg p 1 2 (gm02RecursiveStackArr q)
        (b + 10) (b + 8) (b + 12) (b + 13) (b + 3) (b + 4) (b + 5) (b + 6) 330)
      (.seq (copyArray72Prog (a + 14) p 350 351)
        (.seq (.assign (b + 3) (.op .sub (.const 1) (.op .mod (.reg (b + 3)) (.const 2))))
          (.assign (b + 18) (.const 1)))))

/-- Construct a child, save its parent continuation, and enter the opposite phase. -/
noncomputable def gm02RecursiveCallProg (right : Bool) (q code : ℕ) : Cmd :=
  .seq (gm02SelectedChildProg right (gm02RecursiveBoundaryBound q)
      (gm02RecursiveParentArr q) (gm02RecursiveTemplateArr q) code)
    (gm02RecursivePushChildProg right q)

end GraphMinor.Compute
