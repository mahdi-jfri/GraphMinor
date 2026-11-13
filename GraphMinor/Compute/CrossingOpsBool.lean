module

public import GraphMinor.Compute.CrossingOpsBasic

/-!
# Boolean combinations of word tests

The combinations below keep intermediate values within zero and one. They let the
retention program combine parent, cycle, and extra-edge tests without overflow.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Negation of a zero-one word test. -/
def boolNot (E : Expr) : Expr := .op .sub (.const 1) E

/-- Conjunction of zero-one word tests. -/
def boolAnd (E F : Expr) : Expr := .op .mul E F

/-- Disjunction of zero-one word tests. -/
def boolOr (E F : Expr) : Expr := boolNot (boolAnd (boolNot E) (boolNot F))

/-- Negation has the expected zero-one value. -/
theorem eval_boolNot {w : ℕ} {s : State} {E : Expr} {P : Prop} [Decidable P]
    (hE : E.eval w s = some (if P then 1 else 0)) (hw : 1 < 2 ^ w) :
    (boolNot E).eval w s = some (if ¬ P then 1 else 0) := by
  have hh := eval_sub (eval_const (w := w) (s := s) hw) hE
  by_cases hp : P <;> simpa [boolNot, hp] using hh

/-- Conjunction has the expected zero-one value. -/
theorem eval_boolAnd {w : ℕ} {s : State} {E F : Expr} {P Q : Prop} [Decidable P] [Decidable Q]
    (hE : E.eval w s = some (if P then 1 else 0))
    (hF : F.eval w s = some (if Q then 1 else 0)) (hw : 1 < 2 ^ w) :
    (boolAnd E F).eval w s = some (if P ∧ Q then 1 else 0) := by
  have hbound : (if P then 1 else 0) * (if Q then 1 else 0) < 2 ^ w := by
    by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq, hw, show 0 < 2 ^ w by omega]
  have hh := eval_mul hE hF hbound
  by_cases hp : P <;> by_cases hq : Q <;> simpa [boolAnd, hp, hq] using hh

/-- Disjunction has the expected zero-one value. -/
theorem eval_boolOr {w : ℕ} {s : State} {E F : Expr} {P Q : Prop} [Decidable P] [Decidable Q]
    (hE : E.eval w s = some (if P then 1 else 0))
    (hF : F.eval w s = some (if Q then 1 else 0)) (hw : 1 < 2 ^ w) :
    (boolOr E F).eval w s = some (if P ∨ Q then 1 else 0) := by
  have hh := eval_boolNot (eval_boolAnd (eval_boolNot hE hw) (eval_boolNot hF hw) hw) hw
  simpa only [boolOr, not_and_or, not_not] using hh

end GraphMinor.Compute.Crossing
