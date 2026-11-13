module

public import GraphMinor.Compute.GM06Alg34InteriorFind

/-!
# External metadata preserved by interior-component search

The component search uses its finite graph scratch arrays and a fixed
range of scalar registers. Its syntactic write sets preserve the gap
input, saved parent payloads, and outer driver counters in every run.
-/

public section
namespace GraphMinor.Compute

private theorem find_arrays : gm06InteriorFindProg.writtenArrs ⊆ Finset.range 40 := by decide

set_option maxRecDepth 2048 in
private theorem find_registers : gm06InteriorFindProg.writtenRegs ⊆ Finset.range 300 := by decide

/-- Interior-component search preserves every external metadata array. -/
theorem gm06GapInteriorFind_array_frame {w t : ℕ} {s s' : State}
    (he : Exec w gm06InteriorFindProg s s' t) {A : ℕ} (hA : 40 ≤ A) :
    s'.arrs A = s.arrs A := by
  apply he.arrs_eq_of_not_mem_writtenArrs
  intro hm
  have hh := Finset.mem_range.mp (find_arrays hm)
  omega

/-- Interior-component search preserves every outer driver counter. -/
theorem gm06GapInteriorFind_register_frame {w t : ℕ} {s s' : State}
    (he : Exec w gm06InteriorFindProg s s' t) {q : ℕ} (hq : 300 ≤ q) :
    s'.regs q = s.regs q := by
  apply he.regs_eq_of_not_mem_writtenRegs
  intro hm
  have hh := Finset.mem_range.mp (find_registers hm)
  omega

end GraphMinor.Compute
