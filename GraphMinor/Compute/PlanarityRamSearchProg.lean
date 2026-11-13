module

public import GraphMinor.Compute.PlanarityRamPrepare
public import GraphMinor.Compute.PlanarityRamFrameRead
public import GraphMinor.Compute.PlanarityRamDiscover
public import GraphMinor.Compute.PlanarityRamPostorder

/-!
# The explicit-frame DFS command

This assembles the fixed commands for lines 166–220 of `docs/planarity/planarity_linear.py`. A
root scan starts one frame stack for each undiscovered component. Each frame step
completes a vertex or advances one adjacency index. Tree-child discovery
and back-edge completion use the record programs proved separately.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

/-- Remove the optional-edge tag and finish that incoming edge. -/
def finishIncomingProg : Cmd :=
  .seq (.assign 45 (.read Field.parentEdge.array (.reg 41)))
    (.ite (.reg 45)
      (.seq (.assign 45 (.op .sub (.reg 45) (.const 1))) finishEdgeProg) .skip)

/-- Complete the loaded vertex and finish its incoming edge, when present. -/
def completeFrameProg : Cmd :=
  .seq popFrameProg (.seq appendPostorderProg finishIncomingProg)

/-- Discover a tree child after reading it into register 43. -/
def treeChildProg : Cmd :=
  .seq (addEdgeProg true) (.seq discoverChildProg pushFrameProg)

/-- Create and finish a back-edge record from the loaded endpoints. -/
def backEdgeProg : Cmd :=
  .seq (addEdgeProg false)
    (.seq (.assign 45 (.op .sub (.reg 37) (.const 1))) finishEdgeProg)

/-- An already discovered neighbor contributes a back edge exactly when it
is not the current parent and has smaller depth. Tagged depths have the
same order as their decoded values for discovered vertices. -/
def visitedNeighborProg : Cmd :=
  .ite (.op .eq (.read Field.parent.array (.reg 41))
      (.op .add (.reg 43) (.const 1))) .skip
    (.ite (.op .lt (.read Field.depth.array (.reg 43))
      (.read Field.depth.array (.reg 41))) backEdgeProg .skip)

/-- Read and consume one adjacency entry of the loaded vertex. -/
def scanNeighborProg : Cmd :=
  .seq (.assign 43 (.read 32 (.op .add (.read 30 (.reg 41)) (.reg 42))))
    (.seq advanceFrameProg
      (.ite (.read Field.depth.array (.reg 43)) visitedNeighborProg treeChildProg))

/-- One frame step follows the exhausted-list test in `searchFrames`. -/
def searchFrameStepProg : Cmd :=
  .seq loadFrameProg
    (.ite (.op .le (.op .sub (.read 31 (.reg 41)) (.read 30 (.reg 41))) (.reg 42))
      completeFrameProg scanNeighborProg)

/-- Run the current component until its frame stack is empty. -/
def searchComponentProg : Cmd := .while (.reg 38) searchFrameStepProg

/-- A fresh root receives depth zero, encoded by one, and one initial frame. -/
def startRootProg : Cmd :=
  .seq (.assign 43 (.reg 40))
    (.seq (.write Field.depth.array (.reg 40) (.const 1)) pushFrameProg)

/-- Skip a discovered root, or search its whole component. -/
def searchRootProg : Cmd :=
  .ite (.read Field.depth.array (.reg 40)) .skip
    (.seq startRootProg searchComponentProg)

/-- The full search command, including counting and fixed arena allocation. -/
def depthFirstSearchProg : Cmd :=
  .seq prepareSearchProg
    (.seq (.assign 40 (.const 0)) (forUp 40 (.reg 30) searchRootProg))

end GraphMinor.Compute.PlanarityRam
