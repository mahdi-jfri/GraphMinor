module

public import GraphMinor.Compute.GM06FindLabel
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Testing whether the computed neighbour is off the outer cuff

Reduction 3 in VI (5.7), page 133, contracts an initial leaf edge
only when its other vertex is not on the outer cuff. Search the
supplied outer-cuff row for the computed neighbour label. The
sentinel equal to the row length distinguishes absence from any valid position.
The test preserves all arrays and takes linear time in the cuff size.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Test the neighbour label in 301 against the outer-cuff array 7.
Register 305 is one precisely for absence from that supplied row. -/
def gm06OuterCuffAbsentProg : Cmd :=
  .seq (gm06FindLabelProg 7 301 303 304)
    (.assign 305 (.op .eq (.reg 304) (.len 7)))

/-- The outer-cuff test computes nonmembership of the actual input
row, with an explicit linear bound and no change to instance arrays. -/
theorem gm06OuterCuffAbsentProg_exec {w : ℕ} (cs : List ℕ) (v : ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hn : cs.length < 2 ^ w) (hx : ∀ x ∈ cs, x < 2 ^ w)
    (hv : v < 2 ^ w) (h7 : s.arrs 7 = cs) (h301 : s.regs 301 = v) :
    ∃ s' t, Exec w gm06OuterCuffAbsentProg s s' t ∧
      t ≤ 11 + 13 * cs.length ∧ Keeps [303, 304, 305] [] s s' ∧
      (s'.regs 305 = 1 ↔ v ∉ cs) ∧ (s'.regs 305 = 0 ∨ s'.regs 305 = 1) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hout⟩ := gm06FindLabelProg_exec
    7 301 303 304 (by decide) (by decide) (by decide) cs v s hw hn hx hv h7 h301
  have hbound : s₁.regs 304 ≤ cs.length := by
    rcases hout with ⟨hh, _⟩ | ⟨j, hj, hh, _⟩ <;> omega
  have htest : s₁.regs 304 = cs.length ↔ v ∉ cs := by
    rcases hout with ⟨hh, hnone⟩ | ⟨j, hj, hh, hjv⟩
    · refine ⟨?_, fun _ => hh⟩
      rintro _ hv
      obtain ⟨j, hj, hjv⟩ := List.mem_iff_getElem.mp hv
      exact hnone j hj hjv
    · have hmem : v ∈ cs := hjv ▸ List.getElem_mem hj
      constructor
      · intro heq
        omega
      · intro hnmem
        exact False.elim (hnmem hmem)
  have harr : s₁.arrs 7 = cs := (hk₁.2 7 (by simp)).trans h7
  let value := if s₁.regs 304 = cs.length then 1 else 0
  let s₂ := s₁.setReg 305 value
  have he₂ : Exec w (.assign 305 (.op .eq (.reg 304) (.len 7))) s₁ s₂ 4 :=
    .assign (GraphMinor.Compute.Crossing.eval_eq
      (GraphMinor.Compute.Crossing.eval_reg (s := s₁) (r := 304) rfl (hbound.trans_lt hn))
      (GraphMinor.Compute.Crossing.eval_len harr hn) hw)
  have hk₁' : Keeps [303, 304, 305] [] s s₁ := hk₁.mono (by simp) (by simp)
  refine ⟨s₂, t₁ + 4, .seq he₁ he₂, by omega, hk₁'.setReg (by simp) _, ?_, ?_⟩
  · change value = 1 ↔ v ∉ cs
    have hh : value = 1 ↔ s₁.regs 304 = cs.length := by simp [value]
    exact hh.trans htest
  · change value = 0 ∨ value = 1
    dsimp only [value]
    split <;> simp

end GraphMinor.Compute
