module

public import GraphMinor.Compute.GM06Alg34Driver

/-!
# Outer controls retained by dual and queue operations

Dual construction, task decoding and component enqueueing use their
own scratch registers. Their write sets exclude the running flag,
saved answer and queue capacity. The initial cross-free scan also
retains the supplied gap words. These frames let the driver compose
the independently verified phase programs.
-/

public section
namespace GraphMinor.Compute

private theorem cross_gap : 47 ∉ gm06CheckCrossFreeProg.writtenArrs := by decide

set_option maxRecDepth 8192 in
private theorem dual_controls :
    Disjoint gm06DualBuildProg.writtenRegs ({9000, 9001, 9004} : Finset ℕ) := by decide

set_option maxRecDepth 8192 in
private theorem task_controls :
    Disjoint gm06GapTaskMaterializeProg.writtenRegs ({9000, 9001, 9004} : Finset ℕ) := by decide

set_option maxRecDepth 8192 in
private theorem enqueue_controls :
    Disjoint gm06GapTaskEnqueueProg.writtenRegs ({9000, 9001, 9004} : Finset ℕ) := by decide

/-- The initial crossing scan retains the supplied gap array. -/
theorem gm06CheckCrossFree_gap_frame {w t : ℕ} {s s' : State}
    (he : Exec w gm06CheckCrossFreeProg s s' t) : s'.arrs 47 = s.arrs 47 :=
  he.arrs_eq_of_not_mem_writtenArrs cross_gap

/-- Dual construction retains the outer driver controls. -/
theorem gm06DualBuild_driver_frame {w t : ℕ} {s s' : State}
    (he : Exec w gm06DualBuildProg s s' t) (q : ℕ)
    (hq : q ∈ ({9000, 9001, 9004} : Finset ℕ)) : s'.regs q = s.regs q := by
  apply he.regs_eq_of_not_mem_writtenRegs
  intro hm
  exact Finset.disjoint_left.mp dual_controls hm hq

/-- Task decoding and materialization retain the outer driver controls. -/
theorem gm06GapTaskMaterialize_driver_frame {w t : ℕ} {s s' : State}
    (he : Exec w gm06GapTaskMaterializeProg s s' t) (q : ℕ)
    (hq : q ∈ ({9000, 9001, 9004} : Finset ℕ)) : s'.regs q = s.regs q := by
  apply he.regs_eq_of_not_mem_writtenRegs
  intro hm
  exact Finset.disjoint_left.mp task_controls hm hq

/-- Appending component records retains the outer driver controls. -/
theorem gm06GapTaskEnqueue_driver_frame {w t : ℕ} {s s' : State}
    (he : Exec w gm06GapTaskEnqueueProg s s' t) (q : ℕ)
    (hq : q ∈ ({9000, 9001, 9004} : Finset ℕ)) : s'.regs q = s.regs q := by
  apply he.regs_eq_of_not_mem_writtenRegs
  intro hm
  exact Finset.disjoint_left.mp enqueue_controls hm hq

end GraphMinor.Compute
