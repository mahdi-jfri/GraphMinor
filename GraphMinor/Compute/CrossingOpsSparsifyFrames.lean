module

public import GraphMinor.Compute.CrossingOpsSparsifyRetain
public import GraphMinor.Compute.CrossingOpsInstall
public import GraphMinor.Compute.CrossingOpsDeleteRecord

/-!
# Register preservation for sparsification

The forest, retention, and installation programs use registers at or above their
supplied base. These syntactic facts let the final composition preserve the caller's
registers without expanding the loops in a large execution proof.
-/

public section

namespace GraphMinor.Compute.Crossing

private theorem forestPass_not_written (A R r : ℕ) (hr : r < R) :
    r ∉ (forestPassProg A R).writtenRegs := by
  have hn : ∀ i, r ≠ R + i := by intro i; omega
  have hz : r ≠ R := by omega
  simp [forestPassProg, bfsForestProg, bfsForestInit, bfsRootsLoop, bfsChooseRoot,
    bfsRootRun, bfsRootPush, bfsForestLoop, bfsForestStep, bfsScanProg, tryPushReg, fillLengthProg, fillArr, queueInit, queuePush, queuePop,
    residualPassProg, residualRebuildProg, residualVertexLoop, vertexLoopProg,
    filterListProg, forList, emitWhenProg, emitProg, copyMinNProg, copyMinProg,
    forUp, Cmd.writtenRegs, hn, hz]

private theorem forestSequence_not_written (n A R r : ℕ) (hr : r < R) :
    r ∉ (forestSequenceProg n A R).writtenRegs := by
  induction n generalizing A with
  | zero => simp [forestSequenceProg, Cmd.writtenRegs]
  | succ n ih =>
    simpa only [forestSequenceProg, Cmd.writtenRegs, Finset.mem_union, not_or]
      using And.intro (forestPass_not_written A R r hr) (ih (A + 10))

/-- The forest preparation preserves registers below its register base. -/
theorem sparsifyForestsProg_regs {w : ℕ} {a : InstArrs} {A R : ℕ} {s s' : State} {t : ℕ}
    (hex : Exec w (sparsifyForestsProg a A R) s s' t) {r : ℕ} (hr : r < R) :
    s'.regs r = s.regs r := by
  have hn : ∀ i, r ≠ R + i := by intro i; omega
  have hz : r ≠ R := by omega
  apply hex.regs_eq_of_not_mem_writtenRegs
  have hf := forestSequence_not_written 4 (A + 10) R r hr
  simp only [sparsifyForestsProg, apexFourForestProg, Cmd.writtenRegs,
    Finset.mem_union, not_or]
  refine ⟨?_, ?_, hf⟩
  · simp [copyInstanceProg, copyMinProg, forUp, Cmd.writtenRegs, hn, hz]
  · simp [apexPrepareProg, markArrayProg, writeAllProg, forArrProg,
      apexRebuildProg, apexVertexLoop, apexBody, appendMarkProg,
      filterListProg, forList, emitWhenProg, emitProg, copyMinNProg,
      concatProg, copyAtProg, vertexLoopProg, emitArrayProg, forUp, Cmd.writtenRegs, hn, hz]

/-- The retention command preserves registers below its register base. -/
theorem sparsifyRetainProg_regs {w : ℕ} {a : InstArrs} {A R : ℕ} {s s' : State} {t : ℕ}
    (hex : Exec w (sparsifyRetainProg a A R) s s' t) {r : ℕ} (hr : r < R) :
    s'.regs r = s.regs r := by
  have hn : ∀ i, r ≠ R + i := by intro i; omega
  have hz : r ≠ R := by omega
  apply hex.regs_eq_of_not_mem_writtenRegs
  simp [sparsifyRetainProg, sparsifyCountProg, cardBitSetProg, sparsifyQuotaProg,
    selectEdgesProg, locateEdgeRowLoop, locateEdgeRowBody, countGreaterProg,
    boundaryMarksProg, cyclePositionsProg, retainRebuildProg, subgraphRebuildProg,
    subgraphVertexLoop, vertexLoopProg, markArrayProg, writeAllProg, forArrProg,
    filterListProg, forList, emitWhenProg, emitProg, copyMinNProg,
    forUp, Cmd.writtenRegs, hn, hz]

end GraphMinor.Compute.Crossing
