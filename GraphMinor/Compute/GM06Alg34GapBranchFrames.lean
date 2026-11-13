module

public import GraphMinor.Compute.GM06Alg34BranchRoots

/-!
# Memory retained by canonical component preparation

The root preparation uses the graph work arrays through array 40 and
registers below 5103. Thus the supplied gap list and the pending queue,
including both queue cursors, survive preparation unchanged.
-/

public section
namespace GraphMinor.Compute

private theorem root_arrays : gm06BranchRootsProg.writtenArrs ⊆ Finset.range 41 := by decide

set_option maxRecDepth 4096 in
private theorem root_registers : gm06BranchRootsProg.writtenRegs ⊆ Finset.range 300 ∪ {5100, 5101, 5102} := by decide

/-- Root preparation preserves the gap and pending queue arrays. -/
theorem gm06GapBranchRoots_array_frame {w t : ℕ} {s s' : State}
    (he : Exec w gm06BranchRootsProg s s' t) (A : ℕ) (hA : 41 ≤ A) :
    s'.arrs A = s.arrs A := by
  apply he.arrs_eq_of_not_mem_writtenArrs
  intro hm
  have hh := Finset.mem_range.mp (root_arrays hm)
  omega

/-- Root preparation preserves both queue cursors and all other outer registers. -/
theorem gm06GapBranchRoots_register_frame {w t : ℕ} {s s' : State}
    (he : Exec w gm06BranchRootsProg s s' t) (q : ℕ) (hq : 5103 ≤ q) :
    s'.regs q = s.regs q := by
  apply he.regs_eq_of_not_mem_writtenRegs
  intro hm
  have hh := root_registers hm
  simp only [Finset.mem_union, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton] at hh
  rcases hh with hh | hh | hh | hh
  · omega
  · subst q; omega
  · subst q; omega
  · subst q; omega

end GraphMinor.Compute
