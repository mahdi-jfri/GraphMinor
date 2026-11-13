module

public import GraphMinor.Compute.GM02FullPortIncidence
public import GraphMinor.Compute.GM02CheckChoice
import GraphMinor.Compute.CrossingOpsBasic

/-!
# The old-to-edge adjacency expression for the split builder

The checked incidence command supplies the active-incidence bit. Read
the old vertex's branch mask and require zero. Multiplication then gives
exactly the old-to-edge adjacency of the numeric split graph. This read
occurs only in the old-vertex range.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing Classical

/-- Combine the checked incidence bit with the old vertex's zero branch mask. -/
@[expose] def gm02OldPortAdjExpr : Expr :=
  .op .mul (.reg 46) (.op .eq (.read 22 (.reg 60)) (.const 0))

/-- The old-to-edge adjacency expression has fixed cost. -/
theorem gm02OldPortAdjExpr_cost : gm02OldPortAdjExpr.cost = 6 := rfl

/-- The saved incidence bit and branch mask compute exactly the numeric old-to-edge adjacency. -/
theorem gm02OldPortAdjExpr_eval {w : ℕ} (x : GM02TopologicalInput) (s : State)
    (gflags hflags : List ℕ) (code K : ℕ) (a : Fin x.G.n) (e : Fin x.G.edges.length)
    (hmask : s.arrs 22 = bitSetList x.vertices) (ha : s.regs 60 = a.val)
    (hinc : s.regs 46 = if (gm02ActiveGraph x.G.graph gflags).Inc e.val a.val then 1 else 0)
    (hw : 1 < 2 ^ w) (hn : x.G.n < 2 ^ w) :
    gm02OldPortAdjExpr.eval w s = some (if (gm02FullPortGraph x gflags hflags code K).Adj
      (gm02FullPortOld x K a) (gm02FullPortEdge x K e) then 1 else 0) := by
  let bit : ℕ := if a ∈ x.vertices then 1 else 0
  have hbit : bit ≤ 1 := by dsimp only [bit]; split <;> omega
  have hget : (s.arrs 22)[a.val]? = some bit := by
    rw [hmask]
    exact List.getElem?_eq_some_iff.2
      ⟨by rw [length_bitSetList]; exact a.isLt, getElem_bitSetList x.vertices a.val a.isLt⟩
  obtain ⟨hi, heq⟩ := List.getElem?_eq_some_iff.1 hget
  have hread := (eval_read (eval_reg ha (a.isLt.trans hn)) hi (heq ▸ hbit.trans_lt hw)).trans
    (congrArg some heq)
  have hmaskbit := eval_eq hread (eval_const (by omega : 0 < 2 ^ w)) hw
  have hincword : (if (gm02ActiveGraph x.G.graph gflags).Inc e.val a.val then 1 else 0) < 2 ^ w := by
    split <;> omega
  have hprod : (if (gm02ActiveGraph x.G.graph gflags).Inc e.val a.val then 1 else 0) *
      (if bit = 0 then 1 else 0) < 2 ^ w := by
    split_ifs <;> simp only [Nat.one_mul, Nat.zero_mul, Nat.mul_zero] <;> omega
  have hout := eval_mul (eval_reg hinc hincword) hmaskbit hprod
  simp only [gm02FullPortGraph_old_edge_inc]
  by_cases hm : a ∈ x.vertices <;>
    by_cases hi : (gm02ActiveGraph x.G.graph gflags).Inc e.val a.val <;>
    simpa [gm02OldPortAdjExpr, bit, hm, hi] using hout

end GraphMinor.Compute
