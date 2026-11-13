module

public import GraphMinor.Compute.GM02RecursiveMemory
public import GraphMinor.Compute.GM02BaseExhaustion
public import GraphMinor.Compute.GM02BoundaryCatalogueFromParent

/-!
# Entering an A1 or A2 recursive instance

For a graph on at most four times the fixed width, run the bounded
exhaustive program. Otherwise balance all vertices in A1 or the terminal
support in A2. A separator rejection returns the width flag. A found
separator is followed by complete boundary-catalogue generation and
initialization of the scheme scan.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Select the paper's all-vertex or terminal-support separator query by phase. -/
def gm02RecursiveSeparatorSelectProg (q : ℕ) : Cmd :=
  let p := gm02RecursiveParentArr q
  let b := gm02RecursiveControlBase q
  .ite (.op .eq (.reg (b + 3)) (.const 0))
    (gm02RecursiveStepOneProg true q p (p + 50) (p + 51))
    (gm02RecursiveStepOneProg false q p (p + 50) (p + 51))

/-- Initialize the scheme index, feasibility accumulator, and scan control state. -/
def gm02RecursiveScanInitProg (q : ℕ) : Cmd :=
  let b := gm02RecursiveControlBase q
  .seq (.assign (b + 4) (.const 0))
    (.seq (.assign (b + 5) (.const 0))
      (.seq (.assign (b + 6) (.const 0)) (.assign (b + 18) (.const 2))))

/-- Enter a recursive instance by exhaustion or the paper's separator step. -/
noncomputable def gm02RecursiveEnterProg (q : ℕ) : Cmd :=
  let p := gm02RecursiveParentArr q
  let b := gm02RecursiveControlBase q
  .ite (.op .le (.read p (.const 0)) (.const (4 * q)))
    (.seq (gm02BaseExhaustionProg (4 * q) p outReg (b + 22))
      (.assign (b + 18) (.const 3)))
    (.seq (gm02RecursiveSeparatorSelectProg q)
      (.ite (.op .eq (.reg outReg) (.const 2)) (.assign (b + 18) (.const 3))
        (.seq (gm02BoundaryCatalogueFromParentProg (gm02RecursiveBoundaryBound q) p)
          (gm02RecursiveScanInitProg q))))

end GraphMinor.Compute
