module

public import GraphMinor.Compute.GM06PhaseCut
public import GraphMinor.Compute.GM06PhaseRecords
public import GraphMinor.Compute.GM06PhaseComponentFaces
public import GraphMinor.Compute.GM06PhaseBoundaries
public import GraphMinor.Compute.GM06PhaseApply4

/-!
# The current-core Reduction 4 command and its memory frame

Sections 9, 10, 12 and 13 of our proof of VI (5.7) (outlined in
`GraphMinor/GM06/Alg57Algorithm.lean`) cut the current drawing and scan its components in cuff
order. This command saves the computed rotation records and common origins,
prepares each component's face and boundary rows, searches it, and
installs a successful rerouting in the current linkage. Its syntactic
write frame preserves every other core field and loop counter.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Save computed component records and origins, and retain the
original linkage while component searches reuse the low scratch block. -/
def gm06Reduction4PhaseSaveProg : Cmd :=
  .seq (gm06PhaseCopyProg 601 640)
    (.seq (gm06PhaseCopyProg 626 641)
      (.seq (gm06PhaseCopyProg 8 642)
        (.seq (.assign 682 (.op .mul (.const 2) (.reg 100)))
          (.seq (.assign 683 (.op .mul (.const 2)
            (.op .add (.len 12) (.op .add (.len 6) (.len 7)))))
            (.seq (.assign 684 (.len 12))
              (.seq (.assign 685 (.len 6))
                (.seq (.assign 693 (.const 1))
                  (.seq (.assign 681 (.const 0)) (.assign 646 (.const 0))))))))))

/-- Read the left path and next right path from the saved original
linkage, computing their copied vertices and the left edge labels. -/
def gm06PhaseLoadBoundariesProg : Cmd :=
  .seq (.assign 688 (.reg 681))
    (.seq (gm06PhaseSelectRowProg 642 645)
      (.seq (.assign 695 (.read 6 (.reg 688)))
        (.seq (gm06PhaseBoundaryRowProg 645 609 0)
          (.seq (gm06PhaseLeftEdgesProg 645)
            (.seq (.assign 688 (.op .mod (.op .add (.reg 681) (.const 1)) (.reg 685)))
              (.seq (gm06PhaseSelectRowProg 642 646)
                (.seq (.assign 695 (.read 6 (.reg 688))) (gm06PhaseBoundaryRowProg 646 608 1))))))))

/-- Restore finite-space counts after each component consumes scratch. -/
def gm06PhaseComponentCountsProg : Cmd :=
  .seq (.assign 668 (.const 0))
    (.seq (.assign 647 (.op .mul (.const 2) (.reg 683)))
      (.seq (.assign 648 (.reg 682))
        (.seq (.assign 649 (.reg 683))
          (.seq (.assign 672 (.reg 684)) (.assign 673 (.reg 681))))))

/-- Search the currently selected face, deriving ordinary flags from
the original edge count. Install the rerouting only on success. -/
def gm06Reduction4PhaseSearchProg : Cmd :=
  .seq gm06PhaseLoadBoundariesProg
    (.seq (.assign 670 (.reg 684))
      (.seq (.assign 620 (.reg 682))
        (.seq gm06CandidateOrdinaryProg
          (.seq gm06Find4DartsProg (.ite (.reg 646) gm06PhaseApply4Prog .skip)))))

/-- One component consumes its next physical rotation record. The
saved record cursor survives every face, search and splice subroutine. -/
def gm06Reduction4PhaseBody : Cmd :=
  .seq (.assign 661 (.reg 693))
    (.seq (gm06PhaseReadRecordProg 640 625)
      (.seq (.assign 693 (.reg 661))
        (.seq gm06PhaseComponentCountsProg
          (.seq gm06PhaseComponentFacesProg
            (.seq (.ite (.reg 668) gm06Reduction4PhaseSearchProg .skip)
              (.assign 681 (.op .add (.reg 681) (.const 1))))))))

/-- Continue while a cuff component remains and no search has succeeded. -/
def gm06Reduction4PhaseCond : Expr :=
  exprAnd (exprLt (.reg 681) (.reg 685)) (exprNot (.reg 646))

/-- The complete current-core Reduction 4 phase command. -/
def gm06Reduction4PhaseProg : Cmd :=
  .seq gm06PhaseCutProg
    (.seq gm06Reduction4PhaseSaveProg (.while gm06Reduction4PhaseCond gm06Reduction4PhaseBody))

/-- Reserved registers plus the persistent bit that a rerouting clears. -/
def gm06Reduction4PhaseRegs : List ℕ := 329 :: List.range' 600 100

/-- Reserved arrays plus the linkage that a rerouting replaces. -/
def gm06Reduction4PhaseArrs : List ℕ := 8 :: List.range' 600 60

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem phase_written_regs :
    gm06Reduction4PhaseProg.writtenRegs ⊆ gm06Reduction4PhaseRegs.toFinset := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem phase_written_arrs :
    gm06Reduction4PhaseProg.writtenArrs ⊆ gm06Reduction4PhaseArrs.toFinset := by decide

/-- Every execution preserves all memory outside the reserved phase
block and its explicit linkage/bit outputs. This includes the input,
active masks, rotation rows, cuffs, contraction history and outer counters. -/
theorem gm06Reduction4PhaseProg_frame {w t : ℕ} {s sf : State}
    (he : Exec w gm06Reduction4PhaseProg s sf t) :
    Keeps gm06Reduction4PhaseRegs gm06Reduction4PhaseArrs s sf := by
  constructor
  · intro r hr
    apply he.regs_eq_of_not_mem_writtenRegs
    intro hm
    exact hr (by simpa only [List.mem_toFinset] using phase_written_regs hm)
  · intro a ha
    apply he.arrs_eq_of_not_mem_writtenArrs
    intro hm
    exact ha (by simpa only [List.mem_toFinset] using phase_written_arrs hm)

end GraphMinor.Compute
