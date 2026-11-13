module

public import GraphMinor.Compute.GM06OptionalRotationSector

/-!
# Testing both directed ends of a supplied edge

An edge is numbered in register 53. Its two directed labels are twice
that number and the next integer. Test each label in the rotation row
and combine the sector flags. This includes loops, whose two directed
ends may both occur at the same vertex, while preserving their labels.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Return whether either directed end of the edge in 53 lies in the chosen sector. -/
def gm06EitherEndSectorProg (rot : Arr) : Cmd :=
  .seq (.assign 38 (.op .mul (.reg 53) (.const 2)))
    (.seq (gm06OptionalRotationSectorProg rot)
      (.seq (.assign 54 (.reg 43))
        (.seq (.assign 38 (.op .add (.reg 38) (.const 1)))
          (.seq (gm06OptionalRotationSectorProg rot)
            (.assign 43 (.op .lt (.const 0) (.op .add (.reg 54) (.reg 43))))))))

/-- The edge-sector query tests both actual directed labels in linear time. -/
theorem gm06EitherEndSectorProg_exec {w : ℕ} (rot : ℕ) (xs : List ℕ)
    (p q e m : ℕ) (s : State) (hw : 2 < 2 ^ w)
    (hn : xs.length < 2 ^ w) (hx : ∀ x ∈ xs, x < 2 ^ w) (hnd : xs.Nodup)
    (hp : p ∈ xs) (hq : q ∈ xs) (he : e < m) (hm : 2 * m < 2 ^ w)
    (ha : s.arrs rot = xs) (h36 : s.regs 36 = p) (h37 : s.regs 37 = q) (h53 : s.regs 53 = e) :
    ∃ s' t, Exec w (gm06EitherEndSectorProg rot) s s' t ∧
      t ≤ 104 + 104 * xs.length ∧ Keeps [38, 50, 40, 41, 42, 43, 54] [] s s' ∧
      (s'.regs 43 = 1 ↔ gm06RotationSectorFlag xs p q (2 * e) = 1 ∨
        gm06RotationSectorFlag xs p q (2 * e + 1) = 1) ∧
      (s'.regs 43 = 0 ∨ s'.regs 43 = 1) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hew : e < 2 ^ w := by omega
  have h0w : 2 * e < 2 ^ w := by omega
  have h1w : 2 * e + 1 < 2 ^ w := by omega
  let f₀ := gm06RotationSectorFlag xs p q (2 * e)
  let f₁ := gm06RotationSectorFlag xs p q (2 * e + 1)
  have hf₀ : f₀ ≤ 1 := gm06RotationSectorFlag_le_one xs p q (2 * e)
  have hf₁ : f₁ ≤ 1 := gm06RotationSectorFlag_le_one xs p q (2 * e + 1)
  let s₀ := s.setReg 38 (2 * e)
  have he₀ : Exec w (.assign 38 (.op .mul (.reg 53) (.const 2))) s s₀ 4 := by
    apply Exec.assign
    simpa only [Nat.mul_comm] using GraphMinor.Compute.Crossing.eval_mul
      (GraphMinor.Compute.Crossing.eval_reg h53 hew)
      (GraphMinor.Compute.Crossing.eval_const hw) (by omega : e * 2 < 2 ^ w)
  have ha₀ : s₀.arrs rot = xs := by simpa [s₀] using ha
  have hp₀ : s₀.regs 36 = p := by simp [s₀, h36]
  have hq₀ : s₀.regs 37 = q := by simp [s₀, h37]
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hr₀⟩ := gm06OptionalRotationSectorProg_exec rot xs p q (2 * e)
    s₀ hw hn hx hnd hp hq h0w ha₀ hp₀ hq₀ (by simp [s₀])
  change s₁.regs 43 = f₀ at hr₀
  let s₂ := s₁.setReg 54 f₀
  have he₂ : Exec w (.assign 54 (.reg 43)) s₁ s₂ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_reg hr₀ (hf₀.trans_lt hw1))
  have h38 : s₁.regs 38 = 2 * e := by
    simpa only [s₀, State.setReg_regs_self] using hk₁.1 38 (by decide)
  let s₃ := s₂.setReg 38 (2 * e + 1)
  have he₃ : Exec w (.assign 38 (.op .add (.reg 38) (.const 1))) s₂ s₃ 4 :=
    .assign (GraphMinor.Compute.Crossing.eval_add
      (GraphMinor.Compute.Crossing.eval_reg (by simpa [s₂] using h38) h0w)
      (GraphMinor.Compute.Crossing.eval_const hw1) h1w)
  have ha₃ : s₃.arrs rot = xs := by
    simpa only [s₃, s₂, State.setReg_arrs] using (hk₁.2 rot (by simp)).trans ha₀
  have hp₃ : s₃.regs 36 = p := by
    simpa [s₃, s₂] using (hk₁.1 36 (by decide)).trans hp₀
  have hq₃ : s₃.regs 37 = q := by
    simpa [s₃, s₂] using (hk₁.1 37 (by decide)).trans hq₀
  obtain ⟨s₄, t₄, he₄, ht₄, hk₄, hr₁⟩ := gm06OptionalRotationSectorProg_exec rot xs p q (2 * e + 1)
    s₃ hw hn hx hnd hp hq h1w ha₃ hp₃ hq₃ (by simp [s₃])
  change s₄.regs 43 = f₁ at hr₁
  have h54 : s₄.regs 54 = f₀ := by
    simpa [s₃, s₂] using hk₄.1 54 (by decide)
  have hsum : f₀ + f₁ < 2 ^ w := by omega
  have hval := GraphMinor.Compute.Crossing.eval_lt
    (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
    (GraphMinor.Compute.Crossing.eval_add
      (GraphMinor.Compute.Crossing.eval_reg h54 (hf₀.trans_lt hw1))
      (GraphMinor.Compute.Crossing.eval_reg hr₁ (hf₁.trans_lt hw1)) hsum) hw1
  let s₅ := s₄.setReg 43 (if 0 < f₀ + f₁ then 1 else 0)
  have he₅ : Exec w (.assign 43 (.op .lt (.const 0) (.op .add (.reg 54) (.reg 43)))) s₄ s₅ 6 :=
    .assign hval
  have hex : Exec w (gm06EitherEndSectorProg rot) s s₅ (4 + (t₁ + (2 + (4 + (t₄ + 6))))) :=
    .seq he₀ (.seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ he₅))))
  refine ⟨s₅, _, hex, by omega, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro j hj
    apply hex.regs_eq_of_not_mem_writtenRegs
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    simp only [gm06EitherEndSectorProg, gm06OptionalRotationSectorProg,
      gm06RotationSectorProg, gm06FindLabelProg, gm06BetweenProg, forUp, Cmd.writtenRegs,
      Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty, not_or, or_false]
    tauto
  · intro a _
    apply hex.arrs_eq_of_not_mem_writtenArrs
    simp [gm06EitherEndSectorProg, gm06OptionalRotationSectorProg, gm06RotationSectorProg,
      gm06FindLabelProg, gm06BetweenProg, forUp, Cmd.writtenArrs]
  · have hh : 0 < f₀ + f₁ ↔ f₀ = 1 ∨ f₁ = 1 := by omega
    have hresult : s₅.regs 43 = 1 ↔ 0 < f₀ + f₁ := by
      simp only [s₅, State.setReg_regs_self]
      by_cases hp : 0 < f₀ + f₁ <;> simp [hp]
    exact hresult.trans hh
  · simp only [s₅, State.setReg_regs_self]
    by_cases hp : 0 < f₀ + f₁ <;> simp [hp]

end GraphMinor.Compute
