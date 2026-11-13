module

public import GraphMinor.Compute.Logic

/-!
# Boolean RAM expressions for member tests

Normalized zero-or-one indicators can be combined by multiplication for
conjunction and a positive sum for disjunction. These expression rules keep
all intermediate values within a word containing zero, one, and two.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Conjunction of two normalized indicators. -/
def case3AndExpr (e f : Expr) : Expr := .op .mul e f

/-- Disjunction of two normalized indicators. -/
def case3OrExpr (e f : Expr) : Expr := .op .lt (.const 0) (.op .add e f)

/-- Multiplication computes conjunction for normalized indicators. -/
theorem case3AndExpr_eval {w : ℕ} {s : State} (e f : Expr)
    (P Q : Prop) [Decidable P] [Decidable Q] (hw : 1 < 2 ^ w)
    (he : e.eval w s = some (if P then 1 else 0))
    (hf : f.eval w s = some (if Q then 1 else 0)) :
    (case3AndExpr e f).eval w s = some (if P ∧ Q then 1 else 0) := by
  have h0 : 0 < 2 ^ w := by omega
  by_cases hP : P <;> by_cases hQ : Q <;>
    simp [case3AndExpr, Expr.eval, he, hf, BinOp.eval, BinOp.raw, checkWord, hP, hQ, hw, h0]

/-- A positive sum computes disjunction for normalized indicators. -/
theorem case3OrExpr_eval {w : ℕ} {s : State} (e f : Expr)
    (P Q : Prop) [Decidable P] [Decidable Q] (hw : 2 < 2 ^ w)
    (he : e.eval w s = some (if P then 1 else 0))
    (hf : f.eval w s = some (if Q then 1 else 0)) :
    (case3OrExpr e f).eval w s = some (if P ∨ Q then 1 else 0) := by
  have h0 : 0 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  by_cases hP : P <;> by_cases hQ : Q <;>
    simp [case3OrExpr, Expr.eval, he, hf, BinOp.eval, BinOp.raw, checkWord, hP, hQ, hw, h0, h1]

/-- Comparing two represented words returns their equality indicator. -/
theorem case3EqExpr_eval {w a b : ℕ} {s : State} (e f : Expr)
    (hw : 1 < 2 ^ w)
    (he : e.eval w s = some a) (hf : f.eval w s = some b) :
    (Expr.op .eq e f).eval w s = some (if a = b then 1 else 0) := by
  have h0 : 0 < 2 ^ w := by omega
  by_cases hab : a = b <;>
    simp [Expr.eval, he, hf, BinOp.eval, BinOp.raw, checkWord, hab, hw, h0]

/-- Comparing two represented words returns their strict-order indicator. -/
theorem case3LtExpr_eval {w a b : ℕ} {s : State} (e f : Expr)
    (hw : 1 < 2 ^ w)
    (he : e.eval w s = some a) (hf : f.eval w s = some b) :
    (Expr.op .lt e f).eval w s = some (if a < b then 1 else 0) := by
  have h0 : 0 < 2 ^ w := by omega
  by_cases hab : a < b <;>
    simp [Expr.eval, he, hf, BinOp.eval, BinOp.raw, checkWord, hab, hw, h0]

end GraphMinor.Compute
