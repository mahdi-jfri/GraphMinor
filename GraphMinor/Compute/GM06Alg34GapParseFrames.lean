module

public import GraphMinor.Compute.GM06Alg34GapParse

/-!
# Memory reserved outside the augmented input parser

The parser writes only its three arrays and a fixed finite set of
scratch registers. Its syntactic write sets therefore preserve outer
queue storage and counters on every execution, independently of the
input representation or the parser's correctness proof.
-/

public section
namespace GraphMinor.Compute

private theorem gapParse_arrays : gm06GapParseProg.writtenArrs ⊆ ({0, 47, 49} : Finset ℕ) := by decide

private theorem gapParse_registers : gm06GapParseProg.writtenRegs ⊆
    ({6000, 6001, 6002, 6003, 6100, 6101, 6102, 6200, 6201, 6202, 6300, 6301, 6302} : Finset ℕ) := by decide

/-- Parsing augmented input preserves every array outside its three output and copy arrays. -/
theorem gm06GapParseProg_array_frame {w t : ℕ} {s s' : State}
    (he : Exec w gm06GapParseProg s s' t) {A : ℕ}
    (h0 : A ≠ 0) (h47 : A ≠ 47) (h49 : A ≠ 49) : s'.arrs A = s.arrs A := by
  apply he.arrs_eq_of_not_mem_writtenArrs
  intro hm
  have hh := gapParse_arrays hm
  simp only [Finset.mem_insert, Finset.mem_singleton, h0, h47, h49, or_false] at hh

/-- Parsing augmented input preserves registers below or above its reserved scratch range. -/
theorem gm06GapParseProg_register_frame {w t : ℕ} {s s' : State}
    (he : Exec w gm06GapParseProg s s' t) {q : ℕ}
    (hq : q < 6000 ∨ 6303 ≤ q) : s'.regs q = s.regs q := by
  apply he.regs_eq_of_not_mem_writtenRegs
  intro hm
  have hh := gapParse_registers hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

end GraphMinor.Compute
