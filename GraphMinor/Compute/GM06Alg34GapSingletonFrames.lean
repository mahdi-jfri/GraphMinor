module

public import GraphMinor.Compute.GM06Alg34FindSingletonProg

/-!
# Gap arrays preserved by singleton search

The singleton search copies only the supplied cuff and uses a fixed
range of scalar scratch. Its syntactic write sets preserve the external
gap incidence and all outer reduction counters in every execution.
-/

public section
namespace GraphMinor.Compute

private theorem search_arrays : gm06FindSingletonProg.writtenArrs ⊆ {2} := by decide

set_option maxRecDepth 2048 in
private theorem search_registers : gm06FindSingletonProg.writtenRegs ⊆ Finset.range 200 := by decide

/-- Searching for a singleton preserves every array except the cuff copy. -/
theorem gm06GapFindSingleton_array_frame {w t : ℕ} {s s' : State}
    (he : Exec w gm06FindSingletonProg s s' t) {A : ℕ} (hA : A ≠ 2) :
    s'.arrs A = s.arrs A := by
  apply he.arrs_eq_of_not_mem_writtenArrs
  intro hm
  exact hA (Finset.mem_singleton.mp (search_arrays hm))

/-- Searching for a singleton preserves all outer reduction counters. -/
theorem gm06GapFindSingleton_register_frame {w t : ℕ} {s s' : State}
    (he : Exec w gm06FindSingletonProg s s' t) {q : ℕ} (hq : 200 ≤ q) :
    s'.regs q = s.regs q := by
  apply he.regs_eq_of_not_mem_writtenRegs
  intro hm
  have hh := Finset.mem_range.mp (search_registers hm)
  omega

end GraphMinor.Compute
