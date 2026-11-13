module

public import GraphMinor.Compute.GM06Alg34ComponentBuild
public import GraphMinor.Compute.GM06Alg34VertexRootRanks

/-!
# Memory preserved while building component branches

The concrete component builder uses only its fixed scratch arrays and
registers. Its syntactic write sets therefore leave the saved parent
input, branch queue, and outer-loop counters available. These frame
facts follow from the command itself and apply to every execution.
-/

public section
namespace GraphMinor.Compute

private theorem componentBuild_arrays :
    gm06ComponentBuildProg.writtenArrs ⊆ Finset.range 40 := by decide

set_option maxRecDepth 2048 in
private theorem componentBuild_registers :
    gm06ComponentBuildProg.writtenRegs ⊆ Finset.range 300 := by decide

/-- Constructing a component input preserves every array numbered at least 40. -/
theorem gm06ComponentBuildProg_array_frame {w t : ℕ} {s s' : State}
    (hex : Exec w gm06ComponentBuildProg s s' t) {A : ℕ} (hA : 40 ≤ A) :
    s'.arrs A = s.arrs A := by
  apply hex.arrs_eq_of_not_mem_writtenArrs
  intro hm
  have hh := Finset.mem_range.mp (componentBuild_arrays hm)
  omega

/-- Constructing a component input preserves the outer branch counters. -/
theorem gm06ComponentBuildProg_register_frame {w t : ℕ} {s s' : State}
    (hex : Exec w gm06ComponentBuildProg s s' t) {q : ℕ} (hq : 5000 ≤ q) :
    s'.regs q = s.regs q := by
  apply hex.regs_eq_of_not_mem_writtenRegs
  intro hm
  have hh := Finset.mem_range.mp (componentBuild_registers hm)
  omega

end GraphMinor.Compute
