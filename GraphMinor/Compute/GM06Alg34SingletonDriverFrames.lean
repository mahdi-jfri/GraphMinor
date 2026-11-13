module

public import GraphMinor.Compute.GM06Alg34GapSingletonExhaust

/-!
# Queue memory preserved by singleton exhaustion

The singleton phase only writes its deletion scratch arrays and the
current drawing and gap arrays. Its write sets exclude the task queue,
both queue cursors, and the driver's control registers. Syntactic frame
lemmas make these facts available for any terminating execution.
-/

public section
namespace GraphMinor.Compute

private theorem queue_not_written : 42 ∉ gm06GapSingletonExhaustProg.writtenArrs := by decide

set_option maxRecDepth 8192 in
private theorem cursors_not_written :
    Disjoint gm06GapSingletonExhaustProg.writtenRegs ({7000, 7001, 9000, 9001, 9004} : Finset ℕ) := by decide

/-- Singleton exhaustion retains the pending queue array. -/
theorem gm06GapSingletonExhaust_queue_frame {w t : ℕ} {s s' : State}
    (he : Exec w gm06GapSingletonExhaustProg s s' t) : s'.arrs 42 = s.arrs 42 :=
  he.arrs_eq_of_not_mem_writtenArrs queue_not_written

/-- Singleton exhaustion retains both queue cursors and the driver control registers. -/
theorem gm06GapSingletonExhaust_driver_frame {w t : ℕ} {s s' : State}
    (he : Exec w gm06GapSingletonExhaustProg s s' t) (q : ℕ)
    (hq : q ∈ ({7000, 7001, 9000, 9001, 9004} : Finset ℕ)) : s'.regs q = s.regs q := by
  apply he.regs_eq_of_not_mem_writtenRegs
  intro hm
  exact Finset.disjoint_left.mp cursors_not_written hm hq

end GraphMinor.Compute
