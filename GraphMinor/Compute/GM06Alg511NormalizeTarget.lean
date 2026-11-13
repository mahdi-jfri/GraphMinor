module

public import GraphMinor.Compute.GM06Alg511Target
public import GraphMinor.Compute.Basic
public import GraphMinor.Compute.TwoPathsCyc
import GraphMinor.Compute.CrossingOpsBasic
import Mathlib.Tactic

/-!
# Giving the supplied target a positive denominator

For the orientation comparison of VI (5.11), page 134, normalize the
supplied signed denominator. Its magnitude is positive. When the
denominator is negative, swap the numerator's two magnitude words.
The represented rational is unchanged, so unsigned cross multiplication
can compare it with the computed initial winding.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Numerator after moving the sign of the denominator to the numerator. -/
def gm06Alg511NormalTargetNumerator (a b : ℤ) : ℤ := if b < 0 then -a else a

private theorem signed_parts_real (a : ℤ) : (a.toNat : ℝ) - ((-a).toNat : ℝ) = a := by
  have h : (a.toNat : ℤ) - ((-a).toNat : ℤ) = a := by omega
  exact_mod_cast h

/-- Moving a denominator's sign to the numerator preserves the
supplied rational target, for either sign of nonzero denominator. -/
theorem gm06Alg511NormalTarget_value (a b : ℤ) :
    (gm06Alg511NormalTargetNumerator a b : ℝ) / b.natAbs = (a : ℝ) / b := by
  cases b with
  | ofNat n => simp [gm06Alg511NormalTargetNumerator, show ¬ ((n : ℤ) < 0) from by omega]
  | negSucc n =>
    simp [gm06Alg511NormalTargetNumerator]
    rw [show (-1 + -(n : ℝ)) = -((n : ℝ) + 1) by ring, div_neg, neg_div]

/-- Read signed target rows 1009/1010. Return normalized numerator
parts in 62/63 and the positive denominator magnitude in 64 and 66. -/
def gm06Alg511NormalizeTargetProg : Cmd :=
  .seq (.assign 66 (.op .add (.read 1010 (.const 0)) (.read 1010 (.const 1))))
    (.seq (.ite (.read 1010 (.const 1))
      (.seq (.assign 62 (.read 1009 (.const 1))) (.assign 63 (.read 1009 (.const 0))))
      (.seq (.assign 62 (.read 1009 (.const 0))) (.assign 63 (.read 1009 (.const 1)))))
      (.assign 64 (.reg 66)))

/-- The constant-time target normalization computes the exact
positive-denominator rational representation and preserves all arrays. -/
theorem gm06Alg511NormalizeTargetProg_exec {w : ℕ} (a b : ℤ) (s : State)
    (hb : b ≠ 0) (hw : 1 < 2 ^ w) (hafit : a.natAbs < 2 ^ w) (hbfit : b.natAbs < 2 ^ w)
    (hnum : s.arrs 1009 = gm06Alg511IntegerWords a)
    (hden : s.arrs 1010 = gm06Alg511IntegerWords b) :
    ∃ s', Exec w gm06Alg511NormalizeTargetProg s s' 16 ∧
      s'.regs 62 = (gm06Alg511NormalTargetNumerator a b).toNat ∧
      s'.regs 63 = (-(gm06Alg511NormalTargetNumerator a b)).toNat ∧
      s'.regs 64 = b.natAbs ∧ s'.regs 66 = b.natAbs ∧ 0 < s'.regs 64 ∧
      ((s'.regs 62 : ℝ) - (s'.regs 63 : ℝ)) / s'.regs 64 = (a : ℝ) / b ∧
      Keeps [66, 62, 63, 64] [] s s' := by
  have hA : a.toNat + (-a).toNat = a.natAbs := by cases a <;> simp
  have hB : b.toNat + (-b).toNat = b.natAbs := by cases b <;> simp
  have ha0 : a.toNat < 2 ^ w := by omega
  have ha1 : (-a).toNat < 2 ^ w := by omega
  have hb0 : b.toNat < 2 ^ w := by omega
  have hb1 : (-b).toNat < 2 ^ w := by omega
  have readA0 (st : State) (ha : st.arrs 1009 = gm06Alg511IntegerWords a) :
      (Expr.read 1009 (.const 0)).eval w st = some a.toNat := by
    simp [Expr.eval, ha, gm06Alg511IntegerWords, checkWord, ha0]
  have readA1 (st : State) (ha : st.arrs 1009 = gm06Alg511IntegerWords a) :
      (Expr.read 1009 (.const 1)).eval w st = some (-a).toNat := by
    simp [Expr.eval, ha, gm06Alg511IntegerWords, checkWord, ha1, hw]
  have readB0 : (Expr.read 1010 (.const 0)).eval w s = some b.toNat := by
    simp [Expr.eval, hden, gm06Alg511IntegerWords, checkWord, hb0]
  have readB1 (st : State) (ha : st.arrs 1010 = gm06Alg511IntegerWords b) :
      (Expr.read 1010 (.const 1)).eval w st = some (-b).toNat := by
    simp [Expr.eval, ha, gm06Alg511IntegerWords, checkWord, hb1, hw]
  let s₁ := s.setReg 66 b.natAbs
  let s₂ := (s₁.setReg 62 (gm06Alg511NormalTargetNumerator a b).toNat).setReg 63
    (-(gm06Alg511NormalTargetNumerator a b)).toNat
  let s₃ := s₂.setReg 64 b.natAbs
  have hsum := Crossing.eval_add readB0 (readB1 s hden) (by omega : b.toNat + (-b).toNat < 2 ^ w)
  have he₁ : Exec w (.assign 66 (.op .add (.read 1010 (.const 0)) (.read 1010 (.const 1)))) s s₁ 6 :=
    .assign (by simpa only [hB] using hsum)
  have he₂ : Exec w
      (.ite (.read 1010 (.const 1))
        (.seq (.assign 62 (.read 1009 (.const 1))) (.assign 63 (.read 1009 (.const 0))))
        (.seq (.assign 62 (.read 1009 (.const 0))) (.assign 63 (.read 1009 (.const 1))))) s₁ s₂ 8 := by
    by_cases hneg : b < 0
    · have hnonzero : (-b).toNat ≠ 0 := by omega
      have hbranch := Exec.seq (Exec.assign (r := 62) (readA1 s₁ hnum))
        (Exec.assign (r := 63) (readA0 (s₁.setReg 62 (-a).toNat) hnum))
      simpa only [s₂, gm06Alg511NormalTargetNumerator, hneg, ite_true, neg_neg, Expr.cost] using
        Exec.ite_true (cond := .read 1010 (.const 1)) (readB1 s₁ hden) hnonzero hbranch
    · have hzero : (-b).toNat = 0 := by omega
      have hbranch := Exec.seq (Exec.assign (r := 62) (readA0 s₁ hnum))
        (Exec.assign (r := 63) (readA1 (s₁.setReg 62 a.toNat) hnum))
      simpa only [s₂, gm06Alg511NormalTargetNumerator, hneg, ite_false, Expr.cost] using
        Exec.ite_false (cond := .read 1010 (.const 1)) (by simpa only [hzero] using readB1 s₁ hden) hbranch
  have he₃ : Exec w (.assign 64 (.reg 66)) s₂ s₃ 2 :=
    .assign (Crossing.eval_reg (by simp [s₂, s₁]) hbfit)
  have hp : s₃.regs 62 = (gm06Alg511NormalTargetNumerator a b).toNat := by simp [s₃, s₂]
  have hq : s₃.regs 63 = (-(gm06Alg511NormalTargetNumerator a b)).toNat := by simp [s₃, s₂]
  have hd : s₃.regs 64 = b.natAbs := by simp [s₃]
  refine ⟨s₃, .seq he₁ (.seq he₂ he₃), hp, hq, hd, by simp [s₃, s₂, s₁],
    by rw [hd]; exact Int.natAbs_pos.mpr hb, ?_, ?_⟩
  · rw [hp, hq, hd, signed_parts_real, gm06Alg511NormalTarget_value]
  · exact ((((Keeps.refl _ _ s).setReg (by simp) _).setReg (by simp) _).setReg
      (by simp) _).setReg (by simp) _

end GraphMinor.Compute
