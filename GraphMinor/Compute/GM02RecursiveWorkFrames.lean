module

public import GraphMinor.Compute.GM02BuildChildFromTemplate
public import GraphMinor.Compute.GM02PrepareBoundaryData
public import GraphMinor.Compute.GM02PackBoundaryInput
public import GraphMinor.Compute.GM02RecursiveStepOne

/-!
# Register frames for the recursive work routines

The graph, boundary, and child-building routines use fixed low scratch
registers. Their syntactic write sets therefore lie below 1000. These
bounds preserve the separate recursive control block while the same
work routines are reused for successive parents and children.
-/

public section
set_option maxRecDepth 4096
namespace GraphMinor.Compute

/-- The whole-array copy used to enter a child touches only low scratch registers. -/
theorem gm02CopyWorkArray_writtenRegs_subset (src dst : Arr) :
    (copyArray72Prog src dst 350 351).writtenRegs ⊆ Finset.range 1000 := by
  change (copyArray72Prog 0 0 350 351).writtenRegs ⊆ Finset.range 1000
  decide

/-- The complete chosen-child builder touches only low scratch registers. -/
theorem gm02BuildChildFromTemplateProg_writtenRegs_subset (right : Bool)
    (parent support reserved fresh rawPairs a : Arr) :
    (gm02BuildChildFromTemplateProg right parent support reserved fresh rawPairs a).writtenRegs ⊆
      Finset.range 1000 := by
  cases right with
  | false =>
    change (gm02BuildChildFromTemplateProg false 0 0 0 0 0 0).writtenRegs ⊆ Finset.range 1000
    decide
  | true =>
    change (gm02BuildChildFromTemplateProg true 0 0 0 0 0 0).writtenRegs ⊆ Finset.range 1000
    decide

/-- Computing the inverse boundary numbering leaves high control registers intact. -/
theorem gm02PrepareBoundaryNumberingProg_writtenRegs_subset (a : Arr) :
    (gm02PrepareBoundaryNumberingProg a).writtenRegs ⊆ Finset.range 1000 := by
  change (gm02PrepareBoundaryNumberingProg 0).writtenRegs ⊆ Finset.range 1000
  decide

/-- Preparing all boundary arrays leaves high control registers intact. -/
theorem gm02PrepareBoundaryDataProg_writtenRegs_subset (a : Arr) :
    (gm02PrepareBoundaryDataProg a).writtenRegs ⊆ Finset.range 1000 := by
  change (gm02PrepareBoundaryDataProg 0).writtenRegs ⊆ Finset.range 1000
  decide

/-- Packing the boundary input leaves high control registers intact. -/
theorem gm02PackBoundaryInputProg_writtenRegs_subset (a : Arr) :
    (gm02PackBoundaryInputProg a).writtenRegs ⊆ Finset.range 1000 := by
  change (gm02PackBoundaryInputProg 0).writtenRegs ⊆ Finset.range 1000
  decide

/-- Constructing either separator input leaves high control registers intact. -/
theorem gm02BuildSeparatorInputProg_writtenRegs_subset (allVertices : Bool)
    (src graph bits dst : Arr) :
    (gm02BuildSeparatorInputProg allVertices src graph bits dst).writtenRegs ⊆ Finset.range 1000 := by
  cases allVertices with
  | false =>
    change (gm02BuildSeparatorInputProg false 0 0 0 0).writtenRegs ⊆ Finset.range 1000
    decide
  | true =>
    change (gm02BuildSeparatorInputProg true 0 0 0 0).writtenRegs ⊆ Finset.range 1000
    decide

/-- Converting separator rejection to a width report touches only the output register. -/
theorem gm02SeparatorReportProg_writtenRegs_subset :
    gm02SeparatorReportProg.writtenRegs ⊆ Finset.range 1000 := by decide

/-- A low-register routine preserves every recursive control register above its range. -/
theorem gm02_regs_eq_of_low_writes {w : ℕ} {c : Cmd} {s s' : State} {t : ℕ}
    (he : Exec w c s s' t) (hc : c.writtenRegs ⊆ Finset.range 1000)
    (r : Reg) (hr : 1000 ≤ r) : s'.regs r = s.regs r := by
  apply he.regs_eq_of_not_mem_writtenRegs
  intro hm
  have hl := Finset.mem_range.mp (hc hm)
  exact (Nat.not_lt_of_ge hr) hl

end GraphMinor.Compute
