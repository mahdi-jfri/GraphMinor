module

public import GraphMinor.Compute.GM02SeparatorCodes
public import GraphMinor.Compute.CrossingOpsBasic

/-!
# RAM expressions decoding separator codes

For the code enumeration of II (3.1), build fixed powers of one plus
the vertex count by multiplication. Division by such a power followed
by remainder recovers a candidate slot. Since the separator bound is
fixed, these are fixed expressions. Their intermediate words fit whenever
the largest required power and the code fit.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- A fixed power of a word expression, expanded into multiplications. -/
def gm02PowerExpr (base : Expr) : ℕ → Expr
  | 0 => .const 1
  | k + 1 => .op .mul (gm02PowerExpr base k) base

/-- The expanded power has size linear in the fixed exponent. -/
theorem gm02PowerExpr_cost (base : Expr) (k : ℕ) :
    (gm02PowerExpr base k).cost = 1 + k * (base.cost + 1) := by
  induction k with
  | zero => simp only [gm02PowerExpr, Expr.cost, Nat.zero_mul, Nat.add_zero]
  | succ k ih => simp only [gm02PowerExpr, Expr.cost, ih, Nat.add_mul, Nat.one_mul]; omega

/-- The power expression evaluates without exceeding its final power. -/
theorem gm02PowerExpr_eval {w b : ℕ} (base : Expr) (k : ℕ) (s : State)
    (hb : 1 ≤ b) (he : base.eval w s = some b) (hpow : b ^ k < 2 ^ w) :
    (gm02PowerExpr base k).eval w s = some (b ^ k) := by
  induction k with
  | zero => exact eval_const hpow
  | succ k ih =>
    have hprev : b ^ k < 2 ^ w :=
      (Nat.pow_le_pow_right hb (Nat.le_succ k)).trans_lt hpow
    simpa only [gm02PowerExpr, pow_succ] using eval_mul (ih hprev) he (by simpa [pow_succ] using hpow)

/-- The base of separator codes is one plus the vertex count in register 40. -/
def gm02CodeBaseExpr : Expr := .op .add (.reg 40) (.const 1)

/-- Decode a fixed slot of the code in register 190. -/
def gm02CodeDigitExpr (i : ℕ) : Expr :=
  .op .mod (.op .div (.reg 190) (gm02PowerExpr gm02CodeBaseExpr i)) gm02CodeBaseExpr

/-- Each digit expression has size linear in its fixed slot index. -/
theorem gm02CodeDigitExpr_cost (i : ℕ) : (gm02CodeDigitExpr i).cost = 7 + 4 * i := by
  simp only [gm02CodeDigitExpr, Expr.cost, gm02PowerExpr_cost, gm02CodeBaseExpr]
  omega

/-- Division and remainder expressions recover the candidate slot exactly. -/
theorem gm02CodeDigitExpr_eval {w n code : ℕ} (i : ℕ) (s : State)
    (hrn : s.regs 40 = n) (hcode : s.regs 190 = code)
    (hb : n + 1 < 2 ^ w) (hc : code < 2 ^ w) (hp : (n + 1) ^ i < 2 ^ w) :
    (gm02CodeDigitExpr i).eval w s = some (gm02SeparatorDigit n code i) := by
  have h1 : 1 < 2 ^ w := (show 1 ≤ n + 1 by omega).trans_lt hb
  have hn : n < 2 ^ w := (Nat.lt_succ_self n).trans hb
  have hebase : gm02CodeBaseExpr.eval w s = some (n + 1) :=
    eval_add (eval_reg hrn hn) (eval_const h1) hb
  have hepow := gm02PowerExpr_eval gm02CodeBaseExpr i s (Nat.succ_le_succ (Nat.zero_le n)) hebase hp
  have hecode := eval_reg hcode hc
  have hdiv : code / (n + 1) ^ i < 2 ^ w := (Nat.div_le_self _ _).trans_lt hc
  have hmod : code / (n + 1) ^ i % (n + 1) < 2 ^ w :=
    (Nat.mod_lt _ (Nat.succ_pos n)).trans hb
  have hpowne : (n + 1) ^ i ≠ 0 := Nat.ne_of_gt (Nat.pow_pos (Nat.succ_pos n))
  have hediv : (.op .div (.reg 190) (gm02PowerExpr gm02CodeBaseExpr i) : Expr).eval w s =
      some (code / (n + 1) ^ i) := by
    change (match (Expr.reg 190).eval w s, (gm02PowerExpr gm02CodeBaseExpr i).eval w s with
      | some x, some y => BinOp.div.eval w x y
      | _, _ => none) = _
    rw [hecode, hepow]
    simp only [BinOp.eval, BinOp.raw, ite_eq_right hpowne, checkWord, ite_eq_left hdiv]
  change (match (.op .div (.reg 190) (gm02PowerExpr gm02CodeBaseExpr i) : Expr).eval w s,
      gm02CodeBaseExpr.eval w s with
    | some x, some y => BinOp.mod.eval w x y
    | _, _ => none) = _
  rw [hediv, hebase]
  simp only [BinOp.eval, BinOp.raw, ite_eq_right (Nat.succ_ne_zero n), checkWord, ite_eq_left hmod]
  rfl

end GraphMinor.Compute
