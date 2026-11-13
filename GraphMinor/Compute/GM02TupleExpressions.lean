module

public import GraphMinor.Compute.CrossingOpsBasic
public import GraphMinor.GM02.SeparatorCandidates

/-!
# Testing membership in a candidate separator

The search in II (3.1) represents a small separator by a fixed number of
vertex slots. A slot equal to the vertex count is empty. Multiplying the
inequality bits tests that a vertex is absent from every slot. The
expression has size linear in the fixed number of slots and evaluates
using only zero and one as intermediate products.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing Classical

/-- A zero/one expression testing that a vertex differs from every slot. -/
def gm02TupleFreeExpr (base : Reg) (vertex : Expr) : ℕ → Expr
  | 0 => .const 1
  | k + 1 => .op .mul (gm02TupleFreeExpr base vertex k)
      (.op .sub (.const 1) (.op .eq vertex (.reg (base + k))))

/-- The expression size is linear in the number of slots. -/
theorem gm02TupleFreeExpr_cost (base : Reg) (vertex : Expr) (k : ℕ) :
    (gm02TupleFreeExpr base vertex k).cost = 1 + k * (vertex.cost + 5) := by
  induction k with
  | zero => simp only [gm02TupleFreeExpr, Expr.cost, Nat.zero_mul, Nat.add_zero]
  | succ k ih => simp only [gm02TupleFreeExpr, Expr.cost, ih, Nat.add_mul, Nat.one_mul]; omega

/-- Slot comparison computes the exact absence indicator. -/
theorem gm02TupleFreeExpr_eval {w : ℕ} (base : Reg) (vertex : Expr) (k v : ℕ)
    (s : State) (hw : 1 < 2 ^ w) (hv : vertex.eval w s = some v)
    (hslots : ∀ i < k, s.regs (base + i) < 2 ^ w) :
    (gm02TupleFreeExpr base vertex k).eval w s =
      some (if ∀ i < k, v ≠ s.regs (base + i) then 1 else 0) := by
  induction k with
  | zero => simpa only [gm02TupleFreeExpr, Nat.not_lt_zero, IsEmpty.forall_iff, implies_true,
      ↓reduceIte] using eval_const hw
  | succ k ih =>
    have hprev := ih (fun i hi => hslots i (Nat.lt_succ_of_lt hi))
    have hcmp := eval_eq hv (eval_reg rfl (hslots k (Nat.lt_succ_self k))) hw
    have hsub := eval_sub (eval_const hw) hcmp
    have hprod : (if ∀ i < k, v ≠ s.regs (base + i) then 1 else 0) *
        (1 - (if v = s.regs (base + k) then 1 else 0)) < 2 ^ w := by
      split_ifs <;> omega
    have he := eval_mul hprev hsub hprod
    have heq : (if ∀ i < k, v ≠ s.regs (base + i) then 1 else 0) *
        (1 - (if v = s.regs (base + k) then 1 else 0)) =
        (if ∀ i < k + 1, v ≠ s.regs (base + i) then 1 else 0) := by
      by_cases hp : ∀ i < k, v ≠ s.regs (base + i)
      · by_cases hk : v = s.regs (base + k)
        · have hn : ¬∀ i < k + 1, v ≠ s.regs (base + i) :=
            fun h => h k (Nat.lt_succ_self k) hk
          simp only [ite_eq_left hp, ite_eq_left hk, ite_eq_right hn]
        · have hall : ∀ i < k + 1, v ≠ s.regs (base + i) := by
            intro i hi
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hil | rfl
            · exact hp i hil
            · exact hk
          simp only [ite_eq_left hp, ite_eq_right hk, ite_eq_left hall]
      · have hn : ¬∀ i < k + 1, v ≠ s.regs (base + i) :=
          fun h => hp (fun i hi => h i (Nat.lt_succ_of_lt hi))
        simp only [ite_eq_right hp, ite_eq_right hn, Nat.zero_mul]
    simpa only [gm02TupleFreeExpr, heq] using he

end GraphMinor.Compute
