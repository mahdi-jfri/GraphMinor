module

public import GraphMinor.Compute.Basic
public import GraphMinor.Compute.TwoPathsCyc
import GraphMinor.Compute.CrossingOpsBasic
import Mathlib.Tactic

/-!
# Comparing the initial winding with the rational target

For VI (5.11), page 134, reverse orientation exactly when the
initial winding exceeds the target. Both are signed numerator pairs
with positive denominators. Cross multiplication compares two sums
of natural products, so no signed RAM arithmetic or division is
needed. The output is the bit used by the orientation branch.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Cross multiplication of two signed numerator pairs is exactly
the strict comparison of their rational values. -/
theorem gm06Alg511Above_iff {p q a b k d : ℕ} (hk : 0 < k) (hd : 0 < d) :
    ((a : ℝ) - b) / d < ((p : ℝ) - q) / k ↔ q * d + a * k < p * d + b * k := by
  rw [div_lt_div_iff₀ (Nat.cast_pos.mpr hd) (Nat.cast_pos.mpr hk)]
  constructor
  · intro h
    have hc : ((q * d + a * k : ℕ) : ℝ) < ((p * d + b * k : ℕ) : ℝ) := by
      push_cast
      nlinarith only [h]
    exact_mod_cast hc
  · intro h
    have hc : ((q * d + a * k : ℕ) : ℝ) < ((p * d + b * k : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    nlinarith only [hc]

/-- Compare current winding `(54-55)/52` with target `(62-63)/64`.
Write one in 56 exactly when the current winding is greater. -/
def gm06Alg511CompareWindingProg : Cmd :=
  .assign 56 (.op .lt
    (.op .add (.op .mul (.reg 55) (.reg 64)) (.op .mul (.reg 62) (.reg 52)))
    (.op .add (.op .mul (.reg 54) (.reg 64)) (.op .mul (.reg 63) (.reg 52))))

/-- The orientation comparison takes sixteen steps, returns the
exact strict-comparison bit and preserves every supplied array. -/
theorem gm06Alg511CompareWindingProg_exec {w : ℕ} (p q a b k d : ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hk : 0 < k) (hd : 0 < d)
    (hpfit : p < 2 ^ w) (hqfit : q < 2 ^ w)
    (hafit : a < 2 ^ w) (hbfit : b < 2 ^ w)
    (hkfit : k < 2 ^ w) (hdfit : d < 2 ^ w)
    (hleft : q * d + a * k < 2 ^ w) (hright : p * d + b * k < 2 ^ w)
    (hrp : s.regs 54 = p) (hrq : s.regs 55 = q)
    (hra : s.regs 62 = a) (hrb : s.regs 63 = b)
    (hrk : s.regs 52 = k) (hrd : s.regs 64 = d) :
    ∃ s', Exec w gm06Alg511CompareWindingProg s s' 16 ∧
      (s'.regs 56 = 0 ∨ s'.regs 56 = 1) ∧
      (s'.regs 56 = 1 ↔ ((a : ℝ) - b) / d < ((p : ℝ) - q) / k) ∧
      Keeps [56] [] s s' := by
  have hL := Crossing.eval_add
    (Crossing.eval_mul (Crossing.eval_reg hrq hqfit) (Crossing.eval_reg hrd hdfit)
      (lt_of_le_of_lt (Nat.le_add_right _ _) hleft))
    (Crossing.eval_mul (Crossing.eval_reg hra hafit) (Crossing.eval_reg hrk hkfit)
      (lt_of_le_of_lt (Nat.le_add_left _ _) hleft)) hleft
  have hR := Crossing.eval_add
    (Crossing.eval_mul (Crossing.eval_reg hrp hpfit) (Crossing.eval_reg hrd hdfit)
      (lt_of_le_of_lt (Nat.le_add_right _ _) hright))
    (Crossing.eval_mul (Crossing.eval_reg hrb hbfit) (Crossing.eval_reg hrk hkfit)
      (lt_of_le_of_lt (Nat.le_add_left _ _) hright)) hright
  let bit := if q * d + a * k < p * d + b * k then 1 else 0
  refine ⟨s.setReg 56 bit, .assign (Crossing.eval_lt hL hR hw), ?_, ?_,
    (Keeps.refl _ _ s).setReg (by simp) _⟩
  · dsimp only [bit]
    split <;> simp
  · simp only [State.setReg_regs_self]
    rw [gm06Alg511Above_iff hk hd]
    simp [bit]

end GraphMinor.Compute
