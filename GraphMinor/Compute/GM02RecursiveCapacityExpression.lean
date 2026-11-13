module

public import GraphMinor.Compute.GM02RecursiveMachineProgram
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Evaluating the polynomial stack-capacity expression

Every intermediate product and sum in the capacity formula is bounded
by the final reserved capacity. Hence a word bound for that capacity
also validates all arithmetic in the initialization command.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- A word-sized capacity validates the entire root-size capacity expression. -/
theorem gm02RecursiveCapacityExpr_eval {n w : ℕ} (q : ℕ) (s : State)
    (hn : s.regs (gm02RecursiveControlBase q + 20) = n)
    (hcap : gm02SavedFrameCapacity n < 2 ^ w) :
    (gm02RecursiveCapacityExpr q).eval w s = some (gm02SavedFrameCapacity n) := by
  have hspos : 0 < gm02SavedFrameSizeBound n := by unfold gm02SavedFrameSizeBound; omega
  have hs : gm02SavedFrameSizeBound n ≤ gm02SavedFrameCapacity n := by
    unfold gm02SavedFrameCapacity
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hf : 2 * n + 2 ≤ gm02SavedFrameCapacity n := by
    unfold gm02SavedFrameCapacity
    exact Nat.le_mul_of_pos_right _ hspos
  have hncap : n ≤ gm02SavedFrameCapacity n := by omega
  have h2cap : 2 ≤ gm02SavedFrameCapacity n := by omega
  have h12cap : 12 ≤ gm02SavedFrameCapacity n := by
    have hh : 12 ≤ gm02SavedFrameSizeBound n := by unfold gm02SavedFrameSizeBound; omega
    exact hh.trans hs
  have hnn : 2 * n * n ≤ gm02SavedFrameCapacity n := by
    have hh : 2 * n * n ≤ gm02SavedFrameSizeBound n := by unfold gm02SavedFrameSizeBound; omega
    exact hh.trans hs
  have hsum : 12 + 2 * n * n ≤ gm02SavedFrameCapacity n := by
    have hh : 12 + 2 * n * n ≤ gm02SavedFrameSizeBound n := by unfold gm02SavedFrameSizeBound; omega
    exact hh.trans hs
  have h3n : 3 * n ≤ gm02SavedFrameCapacity n := by
    have hh : 3 * n ≤ gm02SavedFrameSizeBound n := by unfold gm02SavedFrameSizeBound; omega
    exact hh.trans hs
  have heN := eval_reg hn (hncap.trans_lt hcap)
  have he2 := eval_const (s := s) (h2cap.trans_lt hcap)
  have he12 := eval_const (s := s) (h12cap.trans_lt hcap)
  have he3 := eval_const (s := s) ((show 3 ≤ gm02SavedFrameCapacity n by omega).trans_lt hcap)
  have he2n := eval_mul he2 heN ((show 2 * n ≤ gm02SavedFrameCapacity n by omega).trans_lt hcap)
  have heF := eval_add he2n he2 (hf.trans_lt hcap)
  have heNN := eval_mul he2n heN (hnn.trans_lt hcap)
  have heSum := eval_add he12 heNN (hsum.trans_lt hcap)
  have he3N := eval_mul he3 heN (h3n.trans_lt hcap)
  have heSize := eval_add heSum he3N (hs.trans_lt hcap)
  exact eval_mul heF heSize hcap

end GraphMinor.Compute
