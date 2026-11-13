module

public import GraphMinor.Compute.GM02RecursiveMemory
public import GraphMinor.Compute.GM02SaveFrame
public import GraphMinor.Compute.GM02RestoreFrame

/-!
# Control words preserved by saving a parent frame

The frame writer changes its cursor, saved-start word, source length,
and two copying scratch words. State that finite write set explicitly
so that root size and capacity remain available across every child call.
-/

public section
namespace GraphMinor.Compute

/-- Saving a frame touches only its five designated cursor and scratch words. -/
theorem gm02RecursiveSaveFrame_not_written (q : ℕ) (r : Reg)
    (h8 : r ≠ gm02RecursiveControlBase q + 8)
    (h10 : r ≠ gm02RecursiveControlBase q + 10)
    (h12 : r ≠ gm02RecursiveControlBase q + 12)
    (h13 : r ≠ gm02RecursiveControlBase q + 13)
    (h14 : r ≠ gm02RecursiveControlBase q + 14) :
    r ∉ (gm02SaveFrameProg (gm02RecursiveParentArr q) 1 2 (gm02RecursiveStackArr q)
      (gm02RecursiveControlBase q + 10) (gm02RecursiveControlBase q + 8)
      (gm02RecursiveControlBase q + 12) (gm02RecursiveControlBase q + 13)
      (gm02RecursiveControlBase q + 3) (gm02RecursiveControlBase q + 4)
      (gm02RecursiveControlBase q + 5) (gm02RecursiveControlBase q + 6) 330).writtenRegs := by
  simp [gm02SaveFrameProg, gm02SaveFrameHeaderProg, gm02SavedFrameHeaderExprs,
    gm02AppendSavedWordsProg, gm02SaveFrameArraysProg, gm02AppendSavedArrayProg,
    appendBufSliceProg, appendBufSliceBody, appendWordProg, forUp, Cmd.writtenRegs,
    h8, h10, h12, h13, show r ≠ gm02RecursiveControlBase q + 13 + 1 by
      simpa only [Nat.add_assoc] using h14]

/-- Popping a frame preserves control words beyond the complete restore scratch range. -/
theorem gm02RecursiveRestoreFrame_high_not_written (q offset : ℕ) (hoff : 18 < offset) :
    gm02RecursiveControlBase q + offset ∉
      (gm02RestoreFrameProg (gm02RecursiveStackArr q) (gm02RecursiveZeroArr q)
        (gm02RecursiveParentArr q) 1 2 (gm02RecursiveControlBase q)).writtenRegs := by
  simp only [gm02RestoreFrameProg, gm02FindSavedFrameProg, gm02RestoreFrameHeaderProg,
    gm02ReadSavedHeaderProg, readStreamWordProg, gm02RestoreFrameArraysProg,
    gm02RestoreSavedArrayProg, readSliceProg, readSliceBody, gm02ClearSavedSliceProg,
    writeSliceProg, writeSliceBody, forUp, Cmd.writtenRegs, Finset.mem_union,
    Finset.mem_singleton, Finset.notMem_empty, or_false, not_or, Nat.add_assoc]
  dsimp only [Reg] at *
  repeat' apply And.intro
  all_goals first | trivial | omega

end GraphMinor.Compute
