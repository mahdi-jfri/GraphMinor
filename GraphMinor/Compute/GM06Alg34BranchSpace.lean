module

public import GraphMinor.Compute.GM06Alg34BranchWords
import Mathlib.Tactic.Ring

/-!
# Polynomial space reservation for component branches

The parent reserves one cubic payload record per supplied vertex.
A fifth power of the original input size bounds this reservation.
The RAM capacity expression uses only the saved vertex count and the
already verified payload-capacity expression.
-/

@[expose] public section
namespace GraphMinor.Compute

private theorem branch_power (n : ℕ) :
    (n + 1) * ((n + 2) ^ 3 + 1) ≤ (n + 2) ^ 5 := by
  ring_nf
  omega

/-- The branch reservation is polynomial in the original input size. -/
theorem gm06BranchCapacity_le_power (x : GM06DrawingData) :
    gm06BranchCapacity x ≤ (x.size + 2) ^ 5 := by
  exact (Nat.mul_le_mul_right (gm06PayloadCapacity x + 1)
    (Nat.add_le_add_right x.counts_le_size.1 1)).trans (branch_power x.size)

/-- The queue reservation fits logarithmic words in the original input size. -/
theorem gm06BranchCapacity_lt_wordSize (x : GM06DrawingData) {c : ℕ} (hc : 5 ≤ c) :
    gm06BranchCapacity x < 2 ^ wordSize c x.size := by
  apply lt_two_pow_wordSize_of_lt_pow (by omega)
  exact (gm06BranchCapacity_le_power x).trans (Nat.pow_le_pow_right (by omega) hc)

/-- Compute the complete branch reservation from the saved parent count
and the capacity expression evaluated on the original input. -/
def gm06BranchCapacityExpr : Expr :=
  .op .mul (.op .add (.reg 5000) (.const 1))
    (.op .add gm06PayloadCapacityExpr (.const 1))

/-- The branch reservation and its intermediate sums fit any word which
holds the reservation itself, and the capacity expression is exact. -/
theorem gm06BranchCapacityExpr_eval (x : GM06DrawingData) {w : ℕ}
    (hw : 1 < 2 ^ w) (hcap : gm06BranchCapacity x < 2 ^ w) {s : State}
    (hn : s.regs 5000 = x.n)
    (hp : gm06PayloadCapacityExpr.eval w s = some (gm06PayloadCapacity x)) :
    gm06BranchCapacityExpr.eval w s = some (gm06BranchCapacity x) := by
  have hsum : gm06PayloadCapacity x + 1 ≤ gm06BranchCapacity x := by
    unfold gm06BranchCapacity
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hcount : x.n + 1 ≤ gm06BranchCapacity x := by
    unfold gm06BranchCapacity
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hnw : x.n < 2 ^ w := by omega
  have hncw : x.n + 1 < 2 ^ w := hcount.trans_lt hcap
  have hpcw : gm06PayloadCapacity x + 1 < 2 ^ w := hsum.trans_lt hcap
  have hw0 : w ≠ 0 := by intro heq; subst w; norm_num at hw
  change (x.n + 1) * (gm06PayloadCapacity x + 1) < 2 ^ w at hcap
  unfold gm06BranchCapacityExpr
  simp only [Expr.eval, hp]
  simp [BinOp.eval, BinOp.raw, checkWord, hn, hnw, hw0, hncw, hpcw, hcap, gm06BranchCapacity]

end GraphMinor.Compute
