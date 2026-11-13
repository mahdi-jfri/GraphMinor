module

public import GraphMinor.Compute.GM06Alg511Unpack
public import GraphMinor.Compute.GM06Alg511Target
import GraphMinor.Compute.CrossingOpsBasic
import Mathlib.Tactic

/-!
# Reading and testing the target of VI (5.11)

Load the supplied fields and test (5.10)(i) using the path count and
integer parts in the loaded arrays. This is the first phase of the
procedure on page 134. Its execution starts from the plain input
array with arbitrary scratch contents and takes linear time.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The remainder test on the loaded path count and signed target rows. -/
def gm06Alg511LoadedTest : Cmd :=
  .assign 0 (.op .eq
    (.op .mod
      (.op .mul (.read 8 (.const 0))
        (.op .add (.read 9 (.const 0)) (.read 9 (.const 1))))
      (.op .add (.read 10 (.const 0)) (.read 10 (.const 1)))) (.const 0))

/-- Load the input rows and perform the first rejection test. -/
def gm06Alg511InitialTestProg : Cmd :=
  .seq gm06Alg511UnpackProg gm06Alg511LoadedTest

private theorem parts_eq_natAbs (z : ℤ) : z.toNat + (-z).toNat = z.natAbs := by
  cases z <;> simp

/-- The loaded test evaluates the first condition of (5.10) in seventeen steps. -/
theorem gm06Alg511LoadedTest_exec (x : GM06Alg511Input) (s : State) (w : ℕ)
    (hb : x.denominator ≠ 0) (hw : 1 < 2 ^ w)
    (hk : s.arrs 8 = [x.pathCount])
    (ha : s.arrs 9 = gm06Alg511IntegerWords x.numerator)
    (hd : s.arrs 10 = gm06Alg511IntegerWords x.denominator)
    (hkfit : x.pathCount < 2 ^ w) (hafit : x.numerator.natAbs < 2 ^ w)
    (hdfit : x.denominator.natAbs < 2 ^ w)
    (hprod : x.pathCount * x.numerator.natAbs < 2 ^ w) :
    ∃ s', Exec w gm06Alg511LoadedTest s s' 17 ∧ s'.arrs = s.arrs ∧
      (s'.regs 0 = 1 ↔ ∃ m : ℤ, (x.pathCount : ℝ) * x.target = m) ∧
      (s'.regs 0 = 0 ∨ s'.regs 0 = 1) := by
  have hap := parts_eq_natAbs x.numerator
  have hdp := parts_eq_natAbs x.denominator
  have hK : (Expr.read 8 (.const 0)).eval w s = some x.pathCount := by
    simp [Expr.eval, checkWord, hk, hkfit]
  have hA : (Expr.op .add (.read 9 (.const 0)) (.read 9 (.const 1))).eval w s =
      some x.numerator.natAbs := by
    have h0 : (Expr.read 9 (.const 0)).eval w s = some x.numerator.toNat := by
      simp [Expr.eval, checkWord, ha, gm06Alg511IntegerWords,
        show x.numerator.toNat < 2 ^ w by omega]
    have h1 : (Expr.read 9 (.const 1)).eval w s = some (-x.numerator).toNat := by
      simp [Expr.eval, checkWord, ha, gm06Alg511IntegerWords,
        show (-x.numerator).toNat < 2 ^ w by omega, hw]
    simpa only [hap] using Crossing.eval_add h0 h1 (by omega)
  have hD : (Expr.op .add (.read 10 (.const 0)) (.read 10 (.const 1))).eval w s =
      some x.denominator.natAbs := by
    have h0 : (Expr.read 10 (.const 0)).eval w s = some x.denominator.toNat := by
      simp [Expr.eval, checkWord, hd, gm06Alg511IntegerWords,
        show x.denominator.toNat < 2 ^ w by omega]
    have h1 : (Expr.read 10 (.const 1)).eval w s = some (-x.denominator).toNat := by
      simp [Expr.eval, checkWord, hd, gm06Alg511IntegerWords,
        show (-x.denominator).toNat < 2 ^ w by omega, hw]
    simpa only [hdp] using Crossing.eval_add h0 h1 (by omega)
  have hP := Crossing.eval_mul hK hA hprod
  have hdpos : 0 < x.denominator.natAbs := Int.natAbs_pos.mpr hb
  have hrem : x.pathCount * x.numerator.natAbs % x.denominator.natAbs < 2 ^ w :=
    lt_trans (Nat.mod_lt _ hdpos) hdfit
  have hR : (Expr.op .mod
      (.op .mul (.read 8 (.const 0))
        (.op .add (.read 9 (.const 0)) (.read 9 (.const 1))))
      (.op .add (.read 10 (.const 0)) (.read 10 (.const 1)))).eval w s =
      some (x.pathCount * x.numerator.natAbs % x.denominator.natAbs) := by
    rw [Expr.eval, hP, hD]
    simpa only [BinOp.eval, BinOp.raw,
      show x.denominator.natAbs ≠ 0 by omega, ↓reduceIte] using checkWord_of_lt hrem
  let bit := if x.pathCount * x.numerator.natAbs % x.denominator.natAbs = 0 then 1 else 0
  have hE := Crossing.eval_eq hR (Crossing.eval_const (Nat.two_pow_pos w)) hw
  have hdiv : x.pathCount * x.numerator.natAbs % x.denominator.natAbs = 0 ↔
      x.denominator ∣ (x.pathCount : ℤ) * x.numerator := by
    rw [← Nat.dvd_iff_mod_eq_zero, ← Int.natAbs_dvd_natAbs,
      Int.natAbs_mul, Int.natAbs_natCast]
  refine ⟨s.setReg 0 bit, Exec.assign hE, rfl, ?_, ?_⟩
  · simp only [State.setReg_regs_self]
    have hbit : bit = 1 ↔ x.pathCount * x.numerator.natAbs % x.denominator.natAbs = 0 := by
      simp [bit]
    exact hbit.trans (hdiv.trans
      (gm06Alg511_integral_iff x.pathCount x.numerator x.denominator hb).symm)
  · simp only [State.setReg_regs_self]
    dsimp only [bit]
    split <;> simp

/-- From the supplied word array, the initial phase returns the exact
(5.10)(i) bit in linear time and preserves the original input. -/
theorem gm06Alg511InitialTestProg_exec (x : GM06Alg511Input) (s : State) (w : ℕ)
    (hb : x.denominator ≠ 0) (hw : 1 < 2 ^ w)
    (ha : s.arrs 0 = gm06Alg511Words x)
    (hn : (gm06Alg511Words x).length < 2 ^ w)
    (hwords : ∀ v ∈ gm06Alg511Words x, v < 2 ^ w)
    (hkfit : x.pathCount < 2 ^ w) (hafit : x.numerator.natAbs < 2 ^ w)
    (hdfit : x.denominator.natAbs < 2 ^ w)
    (hprod : x.pathCount * x.numerator.natAbs < 2 ^ w) :
    ∃ s' t, Exec w gm06Alg511InitialTestProg s s' t ∧
      t ≤ 20 + 22 * (gm06Alg511Words x).length ∧ s'.arrs 0 = s.arrs 0 ∧
      (s'.regs 0 = 1 ↔ ∃ m : ℤ, (x.pathCount : ℝ) * x.target = m) ∧
      (s'.regs 0 = 0 ∨ s'.regs 0 = 1) := by
  obtain ⟨s₁, t, he, ht, hf, _, hs⟩ := gm06Alg511UnpackProg_exec x s hw ha hn hwords
  have hK : s₁.arrs 8 = [x.pathCount] := hf ⟨6, by decide⟩
  have hA : s₁.arrs 9 = gm06Alg511IntegerWords x.numerator := hf ⟨7, by decide⟩
  have hD : s₁.arrs 10 = gm06Alg511IntegerWords x.denominator := hf ⟨8, by decide⟩
  obtain ⟨s₂, he₂, harr, hbit, hbool⟩ :=
    gm06Alg511LoadedTest_exec x s₁ w hb hw hK hA hD hkfit hafit hdfit hprod
  exact ⟨s₂, t + 17, .seq he he₂, by omega, by rw [harr, hs], hbit, hbool⟩

end GraphMinor.Compute
