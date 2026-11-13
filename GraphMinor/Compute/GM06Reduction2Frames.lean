module

public import GraphMinor.Compute.GM06Reduction2AtVertex

/-!
# Outer-loop registers for the Reduction 2 scan

The local component and loop programs use their own scratch
registers. The scan over the supplied initial-vertex row keeps
its counter in register 290. The local program preserves that
counter, so its verified execution can be used inside a counted loop.
-/

public section
namespace GraphMinor.Compute

set_option maxRecDepth 4096 in
/-- The local Reduction 2 program leaves its caller's row counter unchanged. -/
theorem gm06Reduction2AtVertexProg_reg290 {w t : ℕ} {s s' : State}
    (he : Exec w gm06Reduction2AtVertexProg s s' t) : s'.regs 290 = s.regs 290 := by
  apply he.regs_eq_of_not_mem_writtenRegs
  decide

end GraphMinor.Compute
