module

public import GraphMinor.Compute.Case3StepsMemberScanBody
public import GraphMinor.Compute.Case3StepsInitMemberScan

/-!
# The stopping condition of the member scan

The scan continues while candidate labels remain and no wall has been
returned. Its body skips nonselected and noninterior candidates, storing
only the interior branch results. The record buffer is allocated once.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Continue precisely while a candidate remains and the wall flag is zero. -/
def case3MemberScanCond : Expr :=
  .op .mul (.op .lt (.reg 54) (.reg 52)) (.op .eq (.reg 0) (.const 0))

/-- Initialize and scan candidate labels until exhaustion or a wall result. -/
def case3MemberScanProg (h : ℕ) (P72 : Cmd) : Cmd :=
  .seq case3InitMemberScanProg (.while case3MemberScanCond (case3MemberScanBody h P72))

/-- The checked continuation test has exactly the intended Boolean value. -/
theorem case3MemberScanCond_eval {w k L b : ℕ} (hw : 1 < 2 ^ w)
    (hk : k < 2 ^ w) (hL : L < 2 ^ w) (hb : b ≤ 1) {s : State}
    (hindex : s.regs 54 = k) (hlimit : s.regs 52 = L) (hflag : s.regs 0 = b) :
    case3MemberScanCond.eval w s = some (if k < L ∧ b = 0 then 1 else 0) := by
  have hbw : b < 2 ^ w := lt_of_le_of_lt hb hw
  have h0 := Nat.two_pow_pos w
  by_cases hkl : k < L <;> by_cases hb0 : b = 0 <;>
    simp only [case3MemberScanCond, Expr.eval, checkWord, hindex, hlimit, hflag,
      hk, hL, hbw, h0, hw, BinOp.eval, BinOp.raw, hkl, hb0,
      ↓reduceIte, Nat.one_mul, Nat.zero_mul, and_self, false_and, and_false]

end GraphMinor.Compute
