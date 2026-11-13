module

public import GraphMinor.Compute.GM02ComponentLabelsProg
public import GraphMinor.Compute.GM02GroupingUpdates

/-!
# Testing whether to add a component

Before the grouping threshold is reached, a vertex needs a component
search only when it is outside both the separator and the selected side.
Multiply the slot-absence bit by the complement of the side-membership
bit. This is exactly the guard of the grouping step in II (3.1).
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing Classical

/-- A vertex is eligible when it is absent from the separator and current side. -/
def gm02GroupingGuardExpr (k : ℕ) : Expr :=
  .op .mul (gm02TupleFreeExpr 200 (.reg 181) k) (.op .sub (.const 1) (.read 70 (.reg 181)))

/-- The eligibility expression has size depending only on the fixed slot count. -/
theorem gm02GroupingGuardExpr_cost (k : ℕ) : (gm02GroupingGuardExpr k).cost = 6 * k + 6 := by
  simp only [gm02GroupingGuardExpr, Expr.cost, gm02TupleFreeExpr_cost]
  omega

/-- The guard is one exactly for a vertex outside both represented sets. -/
theorem gm02GroupingGuardExpr_eval {n k w : ℕ} (f : Fin k → ℕ) (hf : ∀ i, f i ≤ n)
    (Y : Finset (Fin n)) (a : Fin n) (s : State) (hw : 2 < 2 ^ w) (hn : n < 2 ^ w)
    (hra : s.regs 181 = a.val) (hY : s.arrs 70 = gm02VertexBits Y)
    (hslots : ∀ i, s.regs (200 + i.val) = f i) :
    (gm02GroupingGuardExpr k).eval w s =
      some (if a ∉ gm02SlotVertices f ∧ a ∉ Y then 1 else 0) := by
  have hefree := gm02TupleFreeExpr_eval_slots 200 181 f a s (by omega) hra hn hf hslots
  have heread : (.read 70 (.reg 181) : Expr).eval w s = some (if a ∈ Y then 1 else 0) := by
    have he := eval_read (a := 70) (eval_reg hra (a.isLt.trans hn))
      (by simpa only [hY, gm02VertexBits, List.length_ofFn] using a.isLt)
      (by simp only [hY, gm02VertexBits, List.getElem_ofFn]; split_ifs <;> omega)
    simpa only [hY, gm02VertexBits, List.getElem_ofFn, Fin.eta] using he
  have hesub := eval_sub (eval_const (show 1 < 2 ^ w by omega)) heread
  have hfit : (if a ∉ gm02SlotVertices f then 1 else 0) *
      (1 - (if a ∈ Y then 1 else 0)) < 2 ^ w := by split_ifs <;> omega
  have he := eval_mul hefree hesub hfit
  by_cases hx : a ∈ gm02SlotVertices (n := n) f <;> by_cases hy : a ∈ Y <;>
    simpa [gm02GroupingGuardExpr, hx, hy] using he

end GraphMinor.Compute
