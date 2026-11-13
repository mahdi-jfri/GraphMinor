module

public import GraphMinor.Compute.GM02HostLoopFlags
public import GraphMinor.Compute.BitSet
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Testing a host branch loop on the Word RAM

After reading the host endpoints, compare them and inspect the pattern
vertex bit at the first endpoint. Multiplying these two equality bits
computes precisely whether the supplied host edge is a loop at a pattern
vertex. All reads are within the supplied host vertex count.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Compare saved host endpoints and test membership in the pattern vertex mask. -/
def gm02HostBranchLoopExpr : Expr :=
  .op .mul (.op .eq (.reg 42) (.reg 44)) (.op .eq (.read 22 (.reg 42)) (.const 1))

/-- The host loop test has constant cost. -/
theorem gm02HostBranchLoopExpr_cost : gm02HostBranchLoopExpr.cost = 8 := rfl

/-- The expression computes exactly the supplied host branch-loop predicate. -/
theorem gm02HostBranchLoopExpr_eval {w : ℕ} (x : GM02TopologicalInput) (s : State)
    (e : Fin x.G.edges.length) (hmask : s.arrs 22 = bitSetList x.vertices)
    (hleft : s.regs 42 = (x.G.edges[e.val]'e.isLt).1.val)
    (hright : s.regs 44 = (x.G.edges[e.val]'e.isLt).2.val)
    (hw : 1 < 2 ^ w) (hn : x.G.n < 2 ^ w) :
    gm02HostBranchLoopExpr.eval w s = some (if gm02HostBranchLoopTest x e then 1 else 0) := by
  let a := (x.G.edges[e.val]'e.isLt).1
  let b := (x.G.edges[e.val]'e.isLt).2
  let bit : ℕ := if a ∈ x.vertices then 1 else 0
  have hbit : bit ≤ 1 := by dsimp only [bit]; split <;> omega
  have hget : (s.arrs 22)[a.val]? = some bit := by
    rw [hmask]
    apply List.getElem?_eq_some_iff.2
    refine ⟨by rw [length_bitSetList]; exact a.isLt, ?_⟩
    exact getElem_bitSetList x.vertices a.val a.isLt
  obtain ⟨hi, heq⟩ := List.getElem?_eq_some_iff.1 hget
  have hread : (Expr.read 22 (.reg 42)).eval w s = some bit := by
    exact (eval_read (eval_reg hleft (a.isLt.trans hn)) hi (heq ▸ hbit.trans_lt hw)).trans (congrArg some heq)
  let p₁ := if a.val = b.val then 1 else 0
  let p₂ := if bit = 1 then 1 else 0
  have hp₁ : p₁ ≤ 1 := by dsimp only [p₁]; split <;> omega
  have hp₂ : p₂ ≤ 1 := by dsimp only [p₂]; split <;> omega
  have hp : p₁ * p₂ ≤ 1 := Nat.mul_le_mul hp₁ hp₂
  have heval : gm02HostBranchLoopExpr.eval w s = some (p₁ * p₂) :=
    eval_mul (eval_eq (eval_reg hleft (a.isLt.trans hn)) (eval_reg hright (b.isLt.trans hn)) hw)
      (eval_eq hread (eval_const hw) hw) (hp.trans_lt hw)
  have hvalue : p₁ * p₂ = if gm02HostBranchLoopTest x e then 1 else 0 := by
    change p₁ * p₂ = if decide (a = b ∧ a ∈ x.vertices) then 1 else 0
    by_cases hab : a = b
    · simp [p₁, p₂, bit, hab]
    · have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
      by_cases ha : a ∈ x.vertices <;> simp [p₁, p₂, bit, hab, hab', ha]
  exact heval.trans (congrArg some hvalue)

end GraphMinor.Compute
