module

public import GraphMinor.Compute.GM06Alg511Target
public import GraphMinor.Compute.Basic
import GraphMinor.Compute.CrossingOpsBasic
import Mathlib.Tactic

/-!
# The RAM integrality test for VI (5.11)

Once the path count and the two signed target words have been loaded,
the first test of page 134 takes constant time. Signs do not affect
integrality. Add each integer's two nonnegative parts, multiply the
numerator magnitude by the path count, and test the remainder modulo
the denominator magnitude. The execution theorem allows arbitrary
scratch contents and preserves every input array.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Test (5.10)(i), with the path count in register 1 and the positive
and negative target parts in registers 2 through 5. Return the bit in 0. -/
def gm06Alg511IntegralProg : Cmd :=
  .assign 0 (.op .eq
    (.op .mod (.op .mul (.reg 1) (.op .add (.reg 2) (.reg 3)))
      (.op .add (.reg 4) (.reg 5))) (.const 0))

private theorem parts_eq_natAbs (z : ℤ) : z.toNat + (-z).toNat = z.natAbs := by
  cases z <;> simp

/-- The RAM test returns one exactly when the supplied rational target
satisfies (5.10)(i). Its execution takes twelve steps. -/
theorem gm06Alg511IntegralProg_exec (x : GM06Alg511Input) (s : State) (w : ℕ)
    (hb : x.denominator ≠ 0) (hw : 1 < 2 ^ w)
    (hk : s.regs 1 = x.pathCount)
    (ha : s.regs 2 = x.numerator.toNat) (ha' : s.regs 3 = (-x.numerator).toNat)
    (hd : s.regs 4 = x.denominator.toNat) (hd' : s.regs 5 = (-x.denominator).toNat)
    (hkfit : x.pathCount < 2 ^ w) (hafit : x.numerator.natAbs < 2 ^ w)
    (hdfit : x.denominator.natAbs < 2 ^ w)
    (hprod : x.pathCount * x.numerator.natAbs < 2 ^ w) :
    ∃ s', Exec w gm06Alg511IntegralProg s s' 12 ∧ s'.arrs = s.arrs ∧
      (s'.regs 0 = 1 ↔ ∃ m : ℤ, (x.pathCount : ℝ) * x.target = m) ∧
      (s'.regs 0 = 0 ∨ s'.regs 0 = 1) ∧
      ∀ r ≠ 0, s'.regs r = s.regs r := by
  have haparts := parts_eq_natAbs x.numerator
  have hdparts := parts_eq_natAbs x.denominator
  have heA : (Expr.op .add (.reg 2) (.reg 3)).eval w s =
      some x.numerator.natAbs := by
    have h := Crossing.eval_add
      (Crossing.eval_reg ha (by omega)) (Crossing.eval_reg ha' (by omega))
      (show x.numerator.toNat + (-x.numerator).toNat < 2 ^ w by omega)
    simpa only [haparts] using h
  have heD : (Expr.op .add (.reg 4) (.reg 5)).eval w s =
      some x.denominator.natAbs := by
    have h := Crossing.eval_add
      (Crossing.eval_reg hd (by omega)) (Crossing.eval_reg hd' (by omega))
      (show x.denominator.toNat + (-x.denominator).toNat < 2 ^ w by omega)
    simpa only [hdparts] using h
  have heP := Crossing.eval_mul (Crossing.eval_reg hk hkfit) heA hprod
  have hdpos : 0 < x.denominator.natAbs := Int.natAbs_pos.mpr hb
  have hrem : x.pathCount * x.numerator.natAbs % x.denominator.natAbs < 2 ^ w :=
    lt_trans (Nat.mod_lt _ hdpos) hdfit
  have heR : (Expr.op .mod (.op .mul (.reg 1) (.op .add (.reg 2) (.reg 3)))
      (.op .add (.reg 4) (.reg 5))).eval w s =
      some (x.pathCount * x.numerator.natAbs % x.denominator.natAbs) := by
    rw [Expr.eval, heP, heD]
    simpa only [BinOp.eval, BinOp.raw,
      show x.denominator.natAbs ≠ 0 by omega, ↓reduceIte] using checkWord_of_lt hrem
  let bit := if x.pathCount * x.numerator.natAbs % x.denominator.natAbs = 0 then 1 else 0
  have he := Crossing.eval_eq heR (Crossing.eval_const (Nat.two_pow_pos w)) hw
  have hdiv : x.pathCount * x.numerator.natAbs % x.denominator.natAbs = 0 ↔
      x.denominator ∣ (x.pathCount : ℤ) * x.numerator := by
    rw [← Nat.dvd_iff_mod_eq_zero, ← Int.natAbs_dvd_natAbs,
      Int.natAbs_mul, Int.natAbs_natCast]
  refine ⟨s.setReg 0 bit, ?_, rfl, ?_, ?_, ?_⟩
  · exact Exec.assign he
  · simp only [State.setReg_regs_self]
    have hbit : bit = 1 ↔ x.pathCount * x.numerator.natAbs % x.denominator.natAbs = 0 := by
      simp [bit]
    exact hbit.trans (hdiv.trans
      (gm06Alg511_integral_iff x.pathCount x.numerator x.denominator hb).symm)
  · simp only [State.setReg_regs_self]
    dsimp only [bit]
    split <;> simp
  · intro r hr
    exact State.setReg_regs_ne s bit hr

end GraphMinor.Compute
