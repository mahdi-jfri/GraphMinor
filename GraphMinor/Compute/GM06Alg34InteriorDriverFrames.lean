module

public import GraphMinor.Compute.GM06Alg34GapInteriorStep
public import GraphMinor.Compute.GM06Alg34SplitProg

/-!
# Queue memory preserved by interior deletion and split testing

Both commands use the current input and their own finite scratch.
Their syntactic write sets retain the pending queue, its cursors and
the outer control registers. The split scan also retains the supplied
gap array, which it does not read or write.
-/

public section
namespace GraphMinor.Compute

private theorem interior_arrays : 42 ∉ gm06GapInteriorStepProg.writtenArrs := by decide
private theorem split_arrays : Disjoint gm06SplitProg.writtenArrs ({42, 47} : Finset ℕ) := by decide

set_option maxRecDepth 8192 in
private theorem interior_registers :
    Disjoint gm06GapInteriorStepProg.writtenRegs ({7000, 7001, 9000, 9001, 9004} : Finset ℕ) := by decide

set_option maxRecDepth 8192 in
private theorem split_registers :
    Disjoint gm06SplitProg.writtenRegs ({7000, 7001, 9000, 9001, 9004} : Finset ℕ) := by decide

/-- The augmented interior deletion phase retains the pending queue. -/
theorem gm06GapInteriorStep_queue_frame {w t : ℕ} {s s' : State}
    (he : Exec w gm06GapInteriorStepProg s s' t) : s'.arrs 42 = s.arrs 42 :=
  he.arrs_eq_of_not_mem_writtenArrs interior_arrays

/-- Interior deletion retains both queue cursors and the driver controls. -/
theorem gm06GapInteriorStep_driver_frame {w t : ℕ} {s s' : State}
    (he : Exec w gm06GapInteriorStepProg s s' t) (q : ℕ)
    (hq : q ∈ ({7000, 7001, 9000, 9001, 9004} : Finset ℕ)) : s'.regs q = s.regs q := by
  apply he.regs_eq_of_not_mem_writtenRegs
  intro hm
  exact Finset.disjoint_left.mp interior_registers hm hq

/-- The split scan retains the pending queue and supplied gap array. -/
theorem gm06Split_queue_gap_frame {w t : ℕ} {s s' : State}
    (he : Exec w gm06SplitProg s s' t) (A : ℕ) (hA : A ∈ ({42, 47} : Finset ℕ)) :
    s'.arrs A = s.arrs A := by
  apply he.arrs_eq_of_not_mem_writtenArrs
  intro hm
  exact Finset.disjoint_left.mp split_arrays hm hA

/-- The split scan retains both queue cursors and the driver controls. -/
theorem gm06Split_driver_frame {w t : ℕ} {s s' : State}
    (he : Exec w gm06SplitProg s s' t) (q : ℕ)
    (hq : q ∈ ({7000, 7001, 9000, 9001, 9004} : Finset ℕ)) : s'.regs q = s.regs q := by
  apply he.regs_eq_of_not_mem_writtenRegs
  intro hm
  exact Finset.disjoint_left.mp split_registers hm hq

end GraphMinor.Compute
