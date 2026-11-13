module

public import GraphMinor.Compute.PlanarityRamSearch
public import GraphMinor.Compute.PlanarityRamArenas

/-!
# Protected input fields of the search and bucket programs

Every instruction writes only scratch registers and work arrays. The
written-field sets of the two fixed commands prove preservation for all
executions, independently of the graph and the correctness invariants.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

private theorem depthFirstSearch_reg_not_written (r : ℕ) (hr : r < 30) :
    r ∉ depthFirstSearchProg.writtenRegs := by
  dsimp only [depthFirstSearchProg, prepareSearchProg, initializeSearchProg, countEntriesProg, searchRootProg, startRootProg, searchComponentProg, searchFrameStepProg, loadFrameProg, completeFrameProg, popFrameProg, appendPostorderProg, finishIncomingProg, finishEdgeProg, finishKeyProg, parentPairProg, insertPairProg, insertLowProg, scanNeighborProg, advanceFrameProg, visitedNeighborProg, backEdgeProg, treeChildProg, addEdgeProg, storeEdgeProg, discoverChildProg, pushFrameProg, allocateFields, searchFields, forUp, Cmd.writtenRegs, Field.array]
  simp only [Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty, not_or]
  try dsimp only [Reg, Arr] at *
  simp only [not_false_eq_true, true_and, and_true]
  omega

private theorem depthFirstSearch_arr_not_written (a : ℕ) (ha : a < 33) :
    a ∉ depthFirstSearchProg.writtenArrs := by
  dsimp only [depthFirstSearchProg, prepareSearchProg, initializeSearchProg, countEntriesProg, searchRootProg, startRootProg, searchComponentProg, searchFrameStepProg, loadFrameProg, completeFrameProg, popFrameProg, appendPostorderProg, finishIncomingProg, finishEdgeProg, finishKeyProg, parentPairProg, insertPairProg, insertLowProg, scanNeighborProg, advanceFrameProg, visitedNeighborProg, backEdgeProg, treeChildProg, addEdgeProg, storeEdgeProg, discoverChildProg, pushFrameProg, allocateFields, searchFields, forUp, Cmd.writtenArrs, Field.array]
  simp only [Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty, not_or]
  try dsimp only [Reg, Arr] at *
  simp only [not_false_eq_true, true_and, and_true]
  omega

/-- Every depthFirstSearch execution preserves the calling convention's protected fields. -/
theorem depthFirstSearchProg_preserves {w t : ℕ} {s s' : State}
    (h : Exec w depthFirstSearchProg s s' t) :
    (∀ r < 30, s'.regs r = s.regs r) ∧ (∀ a < 33, s'.arrs a = s.arrs a) :=
  ⟨fun r hr => h.regs_eq_of_not_mem_writtenRegs (depthFirstSearch_reg_not_written r hr),
    fun a ha => h.arrs_eq_of_not_mem_writtenArrs (depthFirstSearch_arr_not_written a ha)⟩

private theorem bucketSort_reg_not_written (r : ℕ) (hr : r < 30) :
    r ∉ bucketSortProg.writtenRegs := by
  dsimp only [bucketSortProg, allocateFields, bucketFields, pushBucketProg, scanBucketsProg, scanBucketProg, outgoingBucketProg, outgoingBucketStepProg, appendOutgoingProg, appendOutgoingLinksProg, forUp, Cmd.writtenRegs, Field.array]
  simp only [Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty, not_or]
  try dsimp only [Reg, Arr] at *
  simp only [not_false_eq_true, true_and, and_true]
  omega

private theorem bucketSort_arr_not_written (a : ℕ) (ha : a < 33) :
    a ∉ bucketSortProg.writtenArrs := by
  dsimp only [bucketSortProg, allocateFields, bucketFields, pushBucketProg, scanBucketsProg, scanBucketProg, outgoingBucketProg, outgoingBucketStepProg, appendOutgoingProg, appendOutgoingLinksProg, forUp, Cmd.writtenArrs, Field.array]
  simp only [Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty, not_or]
  try dsimp only [Reg, Arr] at *
  simp only [not_false_eq_true, true_and, and_true]
  omega

/-- Every bucketSort execution preserves the calling convention's protected fields. -/
theorem bucketSortProg_preserves {w t : ℕ} {s s' : State}
    (h : Exec w bucketSortProg s s' t) :
    (∀ r < 30, s'.regs r = s.regs r) ∧ (∀ a < 33, s'.arrs a = s.arrs a) :=
  ⟨fun r hr => h.regs_eq_of_not_mem_writtenRegs (bucketSort_reg_not_written r hr),
    fun a ha => h.arrs_eq_of_not_mem_writtenArrs (bucketSort_arr_not_written a ha)⟩

/-- Bucket sorting does not change the N and M header registers. -/
theorem bucketSortProg_headers {w t : ℕ} {s s' : State}
    (h : Exec w bucketSortProg s s' t) : s'.regs 30 = s.regs 30 ∧ s'.regs 36 = s.regs 36 := by
  constructor <;> apply h.regs_eq_of_not_mem_writtenRegs <;>
    simp [bucketSortProg, allocateFields, bucketFields, pushBucketProg, scanBucketsProg, scanBucketProg, outgoingBucketProg, outgoingBucketStepProg, appendOutgoingProg, appendOutgoingLinksProg, forUp, Cmd.writtenRegs]

end GraphMinor.Compute.PlanarityRam
