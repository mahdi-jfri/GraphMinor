module

public import GraphMinor.Compute.Basic
public import GraphMinor.Compute.TwoPathsCyc
import GraphMinor.Compute.CrossingOpsBasic
import Mathlib.Tactic

/-!
# Forming the integer numerator of a path winding

For VI (5.11), page 134, multiply the signed edge-turn sum by the
path count and add the difference of cuff indices. Keep the two
nonnegative parts in separate words. Their difference is the exact
integer numerator of the winding over denominator `k`.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- From positive/negative turn sums 21/22, path count 52, target
index 46 and source index 53, write the scaled winding parts 54/55. -/
def gm06Alg511ScaledWindingProg : Cmd :=
  .seq (.assign 54 (.op .add (.op .mul (.reg 52) (.reg 21)) (.reg 46)))
    (.assign 55 (.op .add (.op .mul (.reg 52) (.reg 22)) (.reg 53)))

/-- The constant-time scaled-winding calculation gives exactly the
integer from the proved normalized path winding formula. -/
theorem gm06Alg511ScaledWindingProg_exec {w : ℕ} (k p q i j : ℕ) (s : State)
    (hk : k < 2 ^ w) (hp : p < 2 ^ w) (hq : q < 2 ^ w)
    (hi : i < 2 ^ w) (hj : j < 2 ^ w)
    (hpos : k * p + j < 2 ^ w) (hneg : k * q + i < 2 ^ w)
    (hrk : s.regs 52 = k) (hrp : s.regs 21 = p) (hrq : s.regs 22 = q)
    (hri : s.regs 53 = i) (hrj : s.regs 46 = j) :
    ∃ s', Exec w gm06Alg511ScaledWindingProg s s' 12 ∧
      s'.regs 54 = k * p + j ∧ s'.regs 55 = k * q + i ∧
      (s'.regs 54 : ℤ) - (s'.regs 55 : ℤ) = (k : ℤ) * ((p : ℤ) - (q : ℤ)) + j - i ∧
      Keeps [54, 55] [] s s' := by
  let s₁ := s.setReg 54 (k * p + j)
  let s₂ := s₁.setReg 55 (k * q + i)
  have he₁ : Exec w (.assign 54 (.op .add (.op .mul (.reg 52) (.reg 21)) (.reg 46))) s s₁ 6 :=
    .assign (Crossing.eval_add
      (Crossing.eval_mul (Crossing.eval_reg hrk hk) (Crossing.eval_reg hrp hp)
        (lt_of_le_of_lt (Nat.le_add_right _ _) hpos)) (Crossing.eval_reg hrj hj) hpos)
  have he₂ : Exec w (.assign 55 (.op .add (.op .mul (.reg 52) (.reg 22)) (.reg 53))) s₁ s₂ 6 :=
    .assign (Crossing.eval_add
      (Crossing.eval_mul (Crossing.eval_reg (by simpa [s₁] using hrk) hk)
        (Crossing.eval_reg (by simpa [s₁] using hrq) hq)
        (lt_of_le_of_lt (Nat.le_add_right _ _) hneg))
      (Crossing.eval_reg (by simpa [s₁] using hri) hi) hneg)
  refine ⟨s₂, .seq he₁ he₂, by simp [s₂, s₁], by simp [s₂], ?_,
    ((Keeps.refl _ _ s).setReg (by simp) _).setReg (by simp) _⟩
  simp [s₂, s₁]; ring

end GraphMinor.Compute
