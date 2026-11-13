module

public import GraphMinor.Compute.GM06Alg34CrossFree
public import GraphMinor.Compute.GM06Alg34GapSingletonExhaust
public import GraphMinor.Compute.GM06Alg34GapInteriorStep
public import GraphMinor.Compute.GM06Alg34SplitProg
public import GraphMinor.Compute.GM06Alg34GapBranchProg
public import GraphMinor.Compute.GM06Alg34DualBuild
public import GraphMinor.Compute.GM06Alg34GapTaskMaterialize

/-!
# The reduction driver for the disc feasibility algorithm

Check cross-freeness, exhaust singleton deletions, and delete an interior
component when one is found. A split block rejects the instance.
Otherwise branch into components or construct the dual and resume
singleton deletions. Completed components are replaced by pending
parent/root records until the queue is empty.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Save the answer and stop the reduction loop. -/
def gm06DriverStop (b : Bool) : Cmd :=
  .seq (.assign 9001 (.const (if b then 1 else 0))) (.assign 9000 (.const 0))

/-- Materialize the next pending task, or accept when no task remains. -/
def gm06DriverNext : Cmd :=
  .ite (.op .lt (.reg 7000) (.reg 7001)) gm06GapTaskMaterializeProg (gm06DriverStop true)

/-- On a connected stuck input construct the dual and immediately resume
singleton reductions. Otherwise append all component tasks and start the next task. -/
def gm06DriverComponents : Cmd :=
  .seq gm06BranchRootsProg
    (.ite (.op .lt (.const 1) (.reg 203))
      (.seq gm06GapTaskEnqueueProg gm06DriverNext)
      (.seq gm06DualBuildProg gm06GapSingletonExhaustProg))

/-- The non-null reduction cases of VI (3.3), followed when needed by duality. -/
def gm06DriverNonNull : Cmd :=
  .seq gm06GapInteriorStepProg
    (.ite (.reg 6600) .skip
      (.seq gm06SplitProg (.ite (.reg 263) gm06DriverComponents (gm06DriverStop false))))

/-- One pass through the work queue, exhausting singleton deletions first. -/
def gm06DriverBody : Cmd :=
  .seq gm06GapSingletonExhaustProg
    (.ite (.read 0 (.const 0)) gm06DriverNonNull gm06DriverNext)

/-- Reserve a polynomial task queue from the supplied array lengths and vertex count.
Four squarings give the sixteenth power of the augmented input size bound. -/
def gm06DriverQueueInit : Cmd :=
  .seq (.assign 9004 (.op .add (.read 0 (.const 0))
    (.op .add (.len 0) (.op .add (.len 47) (.const 2)))))
    (.seq (.assign 9004 (.op .mul (.reg 9004) (.reg 9004)))
      (.seq (.assign 9004 (.op .mul (.reg 9004) (.reg 9004)))
        (.seq (.assign 9004 (.op .mul (.reg 9004) (.reg 9004)))
          (.seq (.assign 9004 (.op .mul (.reg 9004) (.reg 9004)))
            (.seq (.alloc 42 (.reg 9004))
              (.seq (.assign 7000 (.const 0)) (.assign 7001 (.const 0))))))))

/-- The complete finite command implementing the procedure of VI (3.4), page 121.
It reads the supplied drawing and gap arrays 0 and 47, and returns its Boolean in register 0. -/
def gm06Alg34Prog : Cmd :=
  .seq gm06CheckCrossFreeProg
    (.seq (.assign 9001 (.reg 0))
      (.seq (.ite (.reg 9001)
        (.seq gm06DriverQueueInit
          (.seq (.assign 9000 (.const 1)) (.while (.reg 9000) gm06DriverBody))) .skip)
        (.assign 0 (.reg 9001))))

end GraphMinor.Compute
