module

public import GraphMinor.Compute.Algorithm33Multigraph

/-!
# Reading back a shifted member computation

Splicing a local execution above the caller's bases preserves the caller
frame. Reading the shifted part back gives exactly the local final state,
so the retained record and wall data can be used without re-encoding them.
-/

public section

namespace GraphMinor.Compute

/-- Reading a spliced private state recovers that state exactly. -/
theorem case3State_unshift_applyShifted (a_base r_base : ℕ) (s localState : State) :
    (s.applyShifted a_base r_base localState).unshift a_base r_base = localState := by
  apply State.ext
  · funext r
    rw [State.unshift_regs, State.applyShifted_regs_add]
  · funext a
    rw [State.unshift_arrs, State.applyShifted_arrs_add]

/-- Replacing the private part twice keeps only its last value. -/
theorem case3State_applyShifted_overwrite (a_base r_base : ℕ) (s u v : State) :
    (s.applyShifted a_base r_base u).applyShifted a_base r_base v =
      s.applyShifted a_base r_base v := by
  apply State.ext
  · funext r
    simp only [State.applyShifted]
    split_ifs <;> rfl
  · funext a
    simp only [State.applyShifted]
    split_ifs <;> rfl

end GraphMinor.Compute
