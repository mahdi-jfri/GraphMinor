module

public import GraphMinor.Compute.Case3StepsMemberEncodingProg
public import GraphMinor.Compute.Case3StepsInteriorProg
public import GraphMinor.Compute.Case3StepsPrepareMember72
public import GraphMinor.Compute.Case3StepsMemberResultStore
public import GraphMinor.Compute.Case3StepsStoreMemberRecord
public import GraphMinor.Compute.Case3StepsGroupMask

/-!
# The body of the member scan

A set mask bit selects one merged member. Test it against the full wall
perimeter and invoke (7.2) only for an interior member. A branch record is
stored in the shared buffer, while a wall sets the stopping flag. Every
iteration then advances the candidate index.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Process a selected interior member and store a branch result. -/
def case3InteriorMemberProg (h : ℕ) (P72 : Cmd) : Cmd :=
  .seq (case3PrepareMember72Prog P72) (case3MemberResultStoreProg h)

/-- Process one candidate and advance its numeric index. -/
def case3MemberScanBody (h : ℕ) (P72 : Cmd) : Cmd :=
  .seq (.ite (.read 29 (.reg 54))
    (.seq case3MemberEncodingProg
      (.seq case3InteriorProg (.ite (.reg 100) (case3InteriorMemberProg h P72) .skip))) .skip)
    (.assign 54 (.op .add (.reg 54) (.const 1)))

/-- The mask read tests precisely membership in the selected label set. -/
theorem case3MemberMask_eval {w L : ℕ} (S : Finset (Fin L)) (j : Fin L)
    (hw : 1 < 2 ^ w) (hL : L < 2 ^ w) {s : State}
    (hmask : s.arrs 29 = bitSetList S) (hindex : s.regs 54 = j.1) :
    (Expr.read 29 (.reg 54)).eval w s = some (if j ∈ S then 1 else 0) := by
  have hjw : j.1 < 2 ^ w := j.2.trans hL
  have hjlen : j.1 < (s.arrs 29).length := by rw [hmask, length_bitSetList]; exact j.2
  have hread : (s.arrs 29)[j.1] = if j ∈ S then 1 else 0 := by
    rw [← List.getD_eq_getElem _ 0 hjlen, hmask,
      List.getD_eq_getElem _ 0 (by rw [length_bitSetList]; exact j.2), getElem_bitSetList]
  simp only [Expr.eval, checkWord, hindex, hjw, hjlen, hread, ↓reduceIte, ↓reduceDIte]
  split
  · rfl
  · simp only [Nat.two_pow_pos, ↓reduceIte]

/-- An unset candidate bit takes seven steps and changes only the scan
index. No member graph is constructed or passed to (7.2). -/
theorem case3MemberScanBody_inactive_exec {w h : ℕ} (P72 : Cmd) (x : Alg81Input)
    (Z : Finset (Fin x.n)) (j : Fin (x.n + (case3InputEdges x).length))
    (hj : j ∉ case3GroupLabelSet x Z) (hw : 1 < 2 ^ w)
    (hL : x.n + (case3InputEdges x).length < 2 ^ w)
    {s : State} (hmask : s.arrs 29 = bitSetList (case3GroupLabelSet x Z))
    (hindex : s.regs 54 = j.1) :
    Exec w (case3MemberScanBody h P72) s (s.setReg 54 (j.1 + 1)) 7 := by
  have hjw : j.1 < 2 ^ w := j.2.trans hL
  have hj1 : j.1 + 1 < 2 ^ w := lt_of_le_of_lt j.2 hL
  have htest := case3MemberMask_eval (case3GroupLabelSet x Z) j hw hL hmask hindex
  rw [ite_eq_right hj] at htest
  exact .seq (.ite_false htest (.skip s)) (.assign (by
    simp only [Expr.eval, checkWord, hindex, hjw, hw, BinOp.eval, BinOp.raw, hj1, ↓reduceIte]))

end GraphMinor.Compute
