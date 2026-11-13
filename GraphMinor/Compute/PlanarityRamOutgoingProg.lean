module

public import GraphMinor.Compute.PlanarityRamOutgoingAppend
public import GraphMinor.Compute.PlanarityRamBucketPush

/-!
# The fixed outgoing-append command

Registers 51–54 hold the new edge, its source, and the old head and tail
words. The append command changes only the three outgoing arrays. The
new link is explicitly cleared, so unused link words need no invariant
beyond allocation. At most sixteen RAM steps perform all pointer writes.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

/-- Append through the current first and last words. -/
def appendOutgoingLinksProg : Cmd :=
  .seq (.write Field.outgoingNext.array (.reg 51) (.const 0))
    (.seq (.ite (.reg 53)
      (.write Field.outgoingNext.array (.op .sub (.reg 54) (.const 1))
        (.op .add (.reg 51) (.const 1)))
      (.write Field.outgoingFirst.array (.reg 52) (.op .add (.reg 51) (.const 1))))
      (.write Field.outgoingLast.array (.reg 52) (.op .add (.reg 51) (.const 1))))

/-- The pointer writes execute within sixteen steps from their explicit
register values, allocated slots, and word bounds. -/
theorem appendOutgoingLinksProg_exec {N M w : ℕ} (s : State) (i v p q : ℕ)
    (hi : i < M) (hv : v < N) (hp : p ≤ M) (hq : q ≤ M)
    (hlast : p ≠ 0 → 0 < q)
    (hr51 : s.regs 51 = i) (hr52 : s.regs 52 = v)
    (hr53 : s.regs 53 = p) (hr54 : s.regs 54 = q)
    (hfirst : (s.arrs Field.outgoingFirst.array).length = N)
    (htail : (s.arrs Field.outgoingLast.array).length = N)
    (hnext : (s.arrs Field.outgoingNext.array).length = M)
    (hw : 2 * (N + M + 1) < 2 ^ w) :
    ∃ t, Exec w appendOutgoingLinksProg s (appendOutgoingState s v i p q) t ∧ t ≤ 16 := by
  have hiw : i < 2 ^ w := by omega
  have hipw : i + 1 < 2 ^ w := by omega
  have hvw : v < 2 ^ w := by omega
  have hpw : p < 2 ^ w := by omega
  have hqw : q < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  have hzero : 0 < 2 ^ w := by omega
  let s1 := s.writeArr Field.outgoingNext.array i 0
  have hx1 : Exec w (.write Field.outgoingNext.array (.reg 51) (.const 0)) s s1 3 :=
    Exec.write (by simp [Expr.eval, hr51, checkWord_of_lt hiw])
      (checkWord_of_lt hzero) (hnext.symm ▸ hi)
  have hcond : (Expr.reg 53).eval w s1 = some p := by
    simp [Expr.eval, s1, hr53, checkWord_of_lt hpw]
  have hval (s' : State) (hr : s'.regs 51 = i) :
      (Expr.op .add (.reg 51) (.const 1)).eval w s' = some (i + 1) := by
    simp [Expr.eval, hr, BinOp.eval, BinOp.raw, checkWord_of_lt hiw,
      checkWord_of_lt hone, checkWord_of_lt hipw]
  by_cases hpzero : p = 0
  · let s2 := s1.writeArr Field.outgoingFirst.array v (i + 1)
    have hx2 : Exec w (.write Field.outgoingFirst.array (.reg 52)
        (.op .add (.reg 51) (.const 1))) s1 s2 5 :=
      Exec.write (by simp [Expr.eval, s1, hr52, checkWord_of_lt hvw])
        (hval s1 hr51) (by change v < (s.arrs Field.outgoingFirst.array).length; rw [hfirst]; exact hv)
    have hx3 : Exec w (.write Field.outgoingLast.array (.reg 52)
        (.op .add (.reg 51) (.const 1))) s2
        (s2.writeArr Field.outgoingLast.array v (i + 1)) 5 :=
      Exec.write (by simp [Expr.eval, s2, s1, hr52, checkWord_of_lt hvw])
        (hval s2 hr51) (by change v < (s.arrs Field.outgoingLast.array).length; rw [htail]; exact hv)
    refine ⟨14, ?_, by decide⟩
    simpa only [appendOutgoingLinksProg, appendOutgoingState, hpzero, ↓reduceIte, Expr.cost, s2, s1] using
      Exec.seq hx1 (Exec.seq (Exec.ite_false (cond := .reg 53) (by simpa only [hpzero] using hcond) hx2) hx3)
  · have hqpos := hlast hpzero
    have hqw' : q - 1 < 2 ^ w := by omega
    let s2 := s1.writeArr Field.outgoingNext.array (q - 1) (i + 1)
    have hx2 : Exec w (.write Field.outgoingNext.array (.op .sub (.reg 54) (.const 1))
        (.op .add (.reg 51) (.const 1))) s1 s2 7 :=
      Exec.write (by simp [Expr.eval, s1, hr54, BinOp.eval, BinOp.raw,
        checkWord_of_lt hqw, checkWord_of_lt hone, checkWord_of_lt hqw'])
        (hval s1 hr51) (by simp only [s1, State.writeArr_arrs_self, List.length_set, hnext]; omega)
    have hx3 : Exec w (.write Field.outgoingLast.array (.reg 52)
        (.op .add (.reg 51) (.const 1))) s2
        (s2.writeArr Field.outgoingLast.array v (i + 1)) 5 :=
      Exec.write (by simp [Expr.eval, s2, s1, hr52, checkWord_of_lt hvw])
        (hval s2 hr51) (by change v < (s.arrs Field.outgoingLast.array).length; rw [htail]; exact hv)
    refine ⟨16, ?_, by decide⟩
    simpa only [appendOutgoingLinksProg, appendOutgoingState, hpzero, ↓reduceIte, Expr.cost, s2, s1] using
      Exec.seq hx1 (Exec.seq (Exec.ite_true hcond hpzero hx2) hx3)

end GraphMinor.Compute.PlanarityRam
