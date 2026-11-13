module

public import GraphMinor.Compute.GM02BoundarySchemeSet
public import GraphMinor.Compute.Basic
import GraphMinor.Compute.CrossingOpsReplLists
import GraphMinor.Compute.CrossingOpsCycleTest

/-!
# Reading one valid-scheme catalogue bit

Each branch in the fixed scheme scan has a constant code. Division by
its fixed power of two and remainder modulo two read exactly the
catalogue bit computed from the parent boundary. The digit is one
precisely when an actual boundary scheme has that code.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical GraphMinor.Compute.Crossing

/-- Read the bit for a fixed data code from catalogue register 330. -/
def gm02CatalogueBitExpr (i : ℕ) : Expr :=
  .op .mod (.op .div (.reg 330) (.const (2 ^ i))) (.const 2)

/-- The catalogue-bit expression has constant evaluation cost. -/
theorem gm02CatalogueBitExpr_cost (i : ℕ) : (gm02CatalogueBitExpr i).cost = 5 := rfl

/-- Word-sized division and remainder read the required binary digit. -/
theorem gm02CatalogueBitExpr_eval {w code : ℕ} (i : ℕ) (s : State)
    (hcode : s.regs 330 = code) (hc : code < 2 ^ w)
    (hp : 2 ^ i < 2 ^ w) (hw : 2 < 2 ^ w) :
    (gm02CatalogueBitExpr i).eval w s = some (gm02SeparatorDigit 1 code i) := by
  have hd := eval_div (eval_reg hcode hc) (eval_const hp) (by positivity : 2 ^ i ≠ 0)
    ((Nat.div_le_self code (2 ^ i)).trans_lt hc)
  have hm := eval_mod hd (eval_const hw) (by decide : 0 < 2)
  exact hm

/-- On a computed catalogue, a selected bit is one exactly for a genuine scheme code. -/
theorem gm02CatalogueBitExpr_valid {w N : ℕ} (B : GM02BoundaryInput)
    (i : Fin (gm02BoundarySchemeCodeBound N)) (s : State)
    (hcat : s.regs 330 = gm02BoundarySchemeSetCode N B)
    (hcodes : 2 ^ gm02BoundarySchemeCodeBound N ≤ 2 ^ w) (hw : 2 < 2 ^ w) :
    (gm02CatalogueBitExpr i.val).eval w s = some 1 ↔
      ∃ C : B.schemes, gm02BoundarySchemeCode B C = i.val := by
  have hc := (gm02BoundarySchemeSetCode_lt N B).trans_le hcodes
  have hp : 2 ^ i.val < 2 ^ w := by
    exact (Nat.pow_lt_pow_right (by decide : 1 < 2) i.isLt).trans_le hcodes
  rw [gm02CatalogueBitExpr_eval i.val s hcat hc hp hw, Option.some.injEq]
  exact gm02BoundarySchemeSetCode_digit N B i

/-- A code absent from the computed catalogue evaluates to zero. -/
theorem gm02CatalogueBitExpr_invalid {w N : ℕ} (B : GM02BoundaryInput)
    (i : Fin (gm02BoundarySchemeCodeBound N)) (s : State)
    (hcat : s.regs 330 = gm02BoundarySchemeSetCode N B)
    (hcodes : 2 ^ gm02BoundarySchemeCodeBound N ≤ 2 ^ w) (hw : 2 < 2 ^ w)
    (hi : ¬∃ C : B.schemes, gm02BoundarySchemeCode B C = i.val) :
    (gm02CatalogueBitExpr i.val).eval w s = some 0 := by
  have hc := (gm02BoundarySchemeSetCode_lt N B).trans_le hcodes
  have hp := (Nat.pow_lt_pow_right (by decide : 1 < 2) i.isLt).trans_le hcodes
  rw [gm02CatalogueBitExpr_eval i.val s hcat hc hp hw]
  have hne : gm02SeparatorDigit 1 (gm02BoundarySchemeSetCode N B) i.val ≠ 1 :=
    fun h => hi ((gm02BoundarySchemeSetCode_digit N B i).mp h)
  have hle := gm02SeparatorDigit_le 1 (gm02BoundarySchemeSetCode N B) i.val
  congr 1
  omega

end GraphMinor.Compute
