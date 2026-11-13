module

public import GraphMinor.Compute.GM02RecursiveStepOne
public import GraphMinor.Compute.GM02BoundarySchemeCode

/-!
# Fixed memory ranges for the alternating-recursion machine

Place the retained parent input and saved stack above every array used
by the separator search. Place the control-register block above every
separator register and the fixed copying scratch registers. These
choices depend only on the fixed width parameter, so recursive calls
reuse one fixed collection of arrays and registers.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Retained parent input, above the separator's entire array range. -/
def gm02RecursiveParentArr (q : ℕ) : Arr :=
  100 + (gm02BalancedSeparationProg q).writtenArrs.sup id

/-- Fixed template work-array base after the parent boundary work arrays. -/
def gm02RecursiveTemplateArr (q : ℕ) : Arr := gm02RecursiveParentArr q + 20

/-- The saved-parent frame buffer. -/
def gm02RecursiveStackArr (q : ℕ) : Arr := gm02RecursiveParentArr q + 40

/-- Zero-buffer scratch used when popping a saved parent frame. -/
def gm02RecursiveZeroArr (q : ℕ) : Arr := gm02RecursiveParentArr q + 35

/-- A control-register block disjoint from all separator and fixed scratch registers. -/
def gm02RecursiveControlBase (q : ℕ) : Reg :=
  1000 + (gm02BalancedSeparationProg q).writtenRegs.sup id

/-- All crossing-scheme boundaries are bounded by seven times the fixed width. -/
def gm02RecursiveBoundaryBound (q : ℕ) : ℕ := 7 * q

/-- Fixed scheme-data scan range used by the recursive machine. -/
noncomputable def gm02RecursiveCodeBound (q : ℕ) : ℕ :=
  gm02BoundarySchemeCodeBound (gm02RecursiveBoundaryBound q)

/-- The parent and later work arrays are outside the separator's written arrays. -/
theorem gm02RecursiveParentArr_not_written (q offset : ℕ) :
    gm02RecursiveParentArr q + offset ∉ (gm02BalancedSeparationProg q).writtenArrs := by
  intro h
  have hl := Finset.le_sup (f := id) h
  dsimp only [gm02RecursiveParentArr, Arr, id] at hl ⊢
  omega

/-- The recursive control block is outside the separator's written registers. -/
theorem gm02RecursiveControlBase_not_written (q offset : ℕ) :
    gm02RecursiveControlBase q + offset ∉ (gm02BalancedSeparationProg q).writtenRegs := by
  intro h
  have hl := Finset.le_sup (f := id) h
  dsimp only [gm02RecursiveControlBase, Reg, id] at hl ⊢
  omega

/-- The retained parent range is above every fixed low work array. -/
theorem gm02RecursiveParentArr_ge (q : ℕ) : 100 ≤ gm02RecursiveParentArr q := by
  dsimp only [gm02RecursiveParentArr, Arr]
  omega

/-- Every control register is above all fixed low scratch registers. -/
theorem gm02RecursiveControlBase_ge (q : ℕ) : 1000 ≤ gm02RecursiveControlBase q := by
  dsimp only [gm02RecursiveControlBase, Reg]
  omega

end GraphMinor.Compute
