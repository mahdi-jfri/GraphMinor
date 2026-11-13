module

public import GraphMinor.Compute.GM02PortAssignmentCodes
public import GraphMinor.Compute.GM02DecodeDigitsArray
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Reading the candidate slot for a pattern endpoint

The fixed candidate array has two slots for each possible pattern edge.
Read position `2f` or `2f + 1` for the supplied pattern edge `f`. The
pattern bound proves the read is in range, and the decoded digit bound
proves the selected host position fits a word, including its sentinel.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Read the candidate edge choice for one side of pattern position 43. -/
@[expose] def gm02ChoiceSlotExpr (side : Bool) : Expr :=
  .read 23 (.op .add (.op .mul (.const 2) (.reg 43)) (.const (if side then 1 else 0)))

/-- The slot read has fixed cost. -/
theorem gm02ChoiceSlotExpr_cost (side : Bool) : (gm02ChoiceSlotExpr side).cost = 6 := rfl

/-- The read agrees exactly with the raw assignment decoded from the candidate code. -/
theorem gm02ChoiceSlotExpr_eval {w K code : ℕ} (x : GM02TopologicalInput) (s : State)
    (f : Fin x.edges.length) (side : Bool) (hK : x.edges.length ≤ K)
    (harr : s.arrs 23 = List.ofFn (fun i : Fin (2 * K) =>
      gm02SeparatorDigit x.G.edges.length code i.val))
    (hf : s.regs 43 = f.val) (hw : 2 < 2 ^ w) (hKw : 2 * K < 2 ^ w)
    (hmw : x.G.edges.length + 1 < 2 ^ w) :
    (gm02ChoiceSlotExpr side).eval w s = some (gm02PortAssignmentOfCode x code (f, side)).val := by
  let d : ℕ := if side then 1 else 0
  have hd : d ≤ 1 := by cases side <;> decide
  have hi : 2 * f.val + d < 2 * K := by have := f.isLt; omega
  have hfw : f.val < 2 ^ w := by omega
  have hmul : 2 * f.val < 2 ^ w := by omega
  have hsum : 2 * f.val + d < 2 ^ w := hi.trans hKw
  have hidx := eval_add (eval_mul (eval_const hw) (eval_reg hf hfw) hmul)
    (eval_const (by omega : d < 2 ^ w)) hsum
  have hget : (s.arrs 23)[2 * f.val + d]? =
      some (gm02SeparatorDigit x.G.edges.length code (2 * f.val + d)) := by
    rw [harr]
    simp only [List.getElem?_ofFn, hi, ↓reduceDIte]
  have hval : gm02SeparatorDigit x.G.edges.length code (2 * f.val + d) < 2 ^ w :=
    (gm02SeparatorDigit_le ..).trans_lt (by omega)
  obtain ⟨hbound, heq⟩ := List.getElem?_eq_some_iff.1 hget
  have hread := (eval_read hidx hbound (heq ▸ hval)).trans (congrArg some heq)
  rw [gm02PortAssignmentOfCode_val]
  exact hread

end GraphMinor.Compute
