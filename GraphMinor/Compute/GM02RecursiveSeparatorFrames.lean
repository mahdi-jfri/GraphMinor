module

public import GraphMinor.Compute.GM02RecursiveMemory
public import GraphMinor.Compute.GM02RecursiveWorkFrames
public import GraphMinor.Compute.GM02RecursiveEnterProgram

/-!
# Preserving the recursive control block across separator search

The input-construction and reporting commands use low registers. The
remaining separator search has a finite syntactic write set, below the
chosen control block. Both A1 and A2 separator branches therefore leave
every recursive control register unchanged.
-/

public section
namespace GraphMinor.Compute

/-- Step 1 of either phase leaves the fixed recursive control block untouched. -/
theorem gm02RecursiveStepOneProg_control_not_written (allVertices : Bool) (q offset : ℕ)
    (src graph bits : Arr) :
    gm02RecursiveControlBase q + offset ∉
      (gm02RecursiveStepOneProg allVertices q src graph bits).writtenRegs := by
  have hge := gm02RecursiveControlBase_ge q
  have hr : 1000 ≤ gm02RecursiveControlBase q + offset := by dsimp only [Reg] at *; omega
  have hbuild : gm02RecursiveControlBase q + offset ∉
      (gm02BuildSeparatorInputProg allVertices src graph bits inArr).writtenRegs := by
    intro h
    have hh := Finset.mem_range.mp (gm02BuildSeparatorInputProg_writtenRegs_subset
      allVertices src graph bits inArr h)
    exact (Nat.not_lt_of_ge hr) hh
  have hreport : gm02RecursiveControlBase q + offset ∉ gm02SeparatorReportProg.writtenRegs := by
    intro h
    have hh := Finset.mem_range.mp (gm02SeparatorReportProg_writtenRegs_subset h)
    exact (Nat.not_lt_of_ge hr) hh
  change gm02RecursiveControlBase q + offset ∉
    (((gm02BuildSeparatorInputProg allVertices src graph bits inArr).writtenRegs ∪
      (gm02BalancedSeparationProg q).writtenRegs) ∪ gm02SeparatorReportProg.writtenRegs)
  simp only [Finset.mem_union, not_or]
  exact ⟨⟨hbuild, gm02RecursiveControlBase_not_written q offset⟩, hreport⟩

/-- Selecting the A1/A2 separator query also preserves the entire control block. -/
theorem gm02RecursiveSeparatorSelectProg_control_not_written (q offset : ℕ) :
    gm02RecursiveControlBase q + offset ∉ (gm02RecursiveSeparatorSelectProg q).writtenRegs := by
  change gm02RecursiveControlBase q + offset ∉
    ((gm02RecursiveStepOneProg true q (gm02RecursiveParentArr q)
      (gm02RecursiveParentArr q + 50) (gm02RecursiveParentArr q + 51)).writtenRegs ∪
    (gm02RecursiveStepOneProg false q (gm02RecursiveParentArr q)
      (gm02RecursiveParentArr q + 50) (gm02RecursiveParentArr q + 51)).writtenRegs)
  simp only [Finset.mem_union, not_or]
  exact ⟨gm02RecursiveStepOneProg_control_not_written true q offset _ _ _,
    gm02RecursiveStepOneProg_control_not_written false q offset _ _ _⟩

end GraphMinor.Compute
