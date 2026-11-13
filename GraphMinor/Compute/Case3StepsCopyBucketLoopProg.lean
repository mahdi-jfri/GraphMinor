module

public import GraphMinor.Compute.Case3StepsCopyPairTripleProg
public import GraphMinor.Compute.Case3StepsIndexedTriples
public import GraphMinor.Compute.Case3StepsBucketFollow
import Mathlib.Data.List.GetD

/-!
# Copying a counted bucket into a member edge buffer

The loop follows exactly the bucket count. It copies each full input triple,
advances the next pointer and output record index, and decreases the remaining
count. Its output is the concatenation of precisely the followed records.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Copy the remaining records counted by register 70, following head register 71. -/
def case3CopyBucketLoopProg : Cmd :=
  .while (.reg 70)
    (.seq case3CopyPairTripleProg
      (.seq (.assign 71 (.read 36 (.reg 71)))
        (.seq (.assign 72 (.op .add (.reg 72) (.const 1)))
          (.assign 70 (.op .sub (.reg 70) (.const 1))))))

/-- Following a valid counted bucket copies exactly its full pair records.
Only the member buffer and the traversal and scratch registers change. -/
theorem case3CopyBucketLoopProg_exec {w n : ℕ} (D : MultiDigraph n)
    (next : List ℕ) (hnextlen : next.length = D.numActivePairs)
    (hnextwords : ∀ z ∈ next, z < 2 ^ w)
    (rem q head : ℕ) (pre suf : List ℕ) (hpre : pre.length = 2 + 3 * q)
    (hvalid : ∀ j ∈ case3FollowBucket next head rem, j < D.numActivePairs)
    (hw : 3 < 2 ^ w) (hn : n < 2 ^ w) (he : D.numEdges < 2 ^ w)
    (hA : 2 + 3 * D.numActivePairs < 2 ^ w)
    (hQ : 2 + 3 * (q + rem) < 2 ^ w) {s : State}
    (hD : s.arrs 3 = D.enc) (hnext : s.arrs 36 = next)
    (hbuf : s.arrs 39 = pre ++ List.replicate (3 * rem) 0 ++ suf)
    (hrr : s.regs 70 = rem) (hrhead : s.regs 71 = head)
    (hrq : s.regs 72 = q) (hr3 : s.regs 73 = 3) :
    ∃ s' t, Exec w case3CopyBucketLoopProg s s' t ∧ t ≤ 80 * rem + 1 ∧
      s'.arrs 39 = pre ++ case3IndexedTriples D (case3FollowBucket next head rem) ++ suf ∧
      (∀ a, a ≠ 39 → s'.arrs a = s.arrs a) ∧
      (∀ r, r < 70 ∨ r = 73 ∨ 78 ≤ r → s'.regs r = s.regs r) := by
  have h0 : 0 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  induction rem generalizing q head pre s with
  | zero =>
    have hc : (Expr.reg 70).eval w s = some 0 := by
      simp only [Expr.eval, checkWord, hrr, h0, ↓reduceIte]
    refine ⟨s, 1, .while_false hc, by omega, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
    simpa only [Nat.mul_zero, List.replicate_zero, case3FollowBucket,
      case3IndexedTriples, List.flatMap_nil] using hbuf
  | succ rem ih =>
    have hhead : head < D.numActivePairs :=
      hvalid head (by exact List.mem_cons_self)
    have htail : ∀ j ∈ case3FollowBucket next (next.getD head 0) rem, j < D.numActivePairs := by
      intro j hj
      exact hvalid j (List.mem_cons_of_mem _ hj)
    have hremw : rem + 1 < 2 ^ w := by omega
    have hrem0w : rem < 2 ^ w := by omega
    have hqw : q < 2 ^ w := by omega
    have hqpw : q + 1 < 2 ^ w := by omega
    have hc : (Expr.reg 70).eval w s = some (rem + 1) := by
      simp only [Expr.eval, checkWord, hrr, hremw, ↓reduceIte]
    have hzeros : List.replicate (3 * (rem + 1)) (0 : ℕ) =
        List.replicate 3 0 ++ List.replicate (3 * rem) 0 := by
      rw [show 3 * (rem + 1) = 3 + 3 * rem by omega, List.replicate_add]
    obtain ⟨sB, tB, hexB, htB, hbufB, harrB, hregB⟩ :=
      case3CopyPairTripleProg_exec D ⟨head, hhead⟩ q pre (List.replicate (3 * rem) 0 ++ suf)
        hpre hw hn he hA (by omega) hD
        (by rw [hbuf, hzeros]; simp only [List.append_assoc]) hrhead hrq hr3
    have hi : head < (sB.arrs 36).length := by rw [harrB 36 (by decide), hnext, hnextlen]; exact hhead
    have hg : (sB.arrs 36)[head]'hi = next.getD head 0 := by
      rw [← List.getD_eq_getElem _ 0 hi, harrB 36 (by decide), hnext]
    have hnextw : next.getD head 0 < 2 ^ w := by
      rw [List.getD_eq_getElem _ 0 (by omega)]
      exact hnextwords _ (List.getElem_mem (by omega))
    have hnextw' : next[head]?.getD 0 < 2 ^ w := by
      simpa only [List.getD_eq_getElem?_getD] using hnextw
    have hheadw : head < 2 ^ w := by omega
    let sC := sB.setReg 71 (next.getD head 0)
    let sE := sC.setReg 72 (q + 1)
    let sF := sE.setReg 70 rem
    have hexC : Exec w (.assign 71 (.read 36 (.reg 71))) sB sC 3 :=
      .assign (by simp [Expr.eval, checkWord, hregB 71 (by decide), hrhead, hheadw, hi, hg, hnextw'])
    have hexE : Exec w (.assign 72 (.op .add (.reg 72) (.const 1))) sC sE 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, sC,
        State.setReg_regs_ne, hregB 72 (by decide), hrq, hqw, h1, hqpw])
    have hexF : Exec w (.assign 70 (.op .sub (.reg 70) (.const 1))) sE sF 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, sE, sC,
        State.setReg_regs_ne, hregB 70 (by decide), hrr, hremw, h1, hrem0w])
    have hpre' : (pre ++ case3PairTriple D ⟨head, hhead⟩).length = 2 + 3 * (q + 1) := by
      rw [List.length_append, hpre, case3PairTriple_length]
      omega
    have hbufF : sF.arrs 39 = (pre ++ case3PairTriple D ⟨head, hhead⟩) ++
        List.replicate (3 * rem) 0 ++ suf := by
      simpa only [sF, sE, sC, State.setReg_arrs, List.append_assoc] using hbufB
    obtain ⟨s', t, hex, ht, hdst, harr, hreg⟩ := ih (q + 1) (next.getD head 0)
      (pre ++ case3PairTriple D ⟨head, hhead⟩) hpre' htail (by omega) (s := sF)
      ((harrB 3 (by decide)).trans hD) ((harrB 36 (by decide)).trans hnext) hbufF
      (State.setReg_regs_self ..)
      (by simp only [sF, sE, sC, State.setReg_regs_ne _ _ (show (71 : ℕ) ≠ 70 by decide),
        State.setReg_regs_ne _ _ (show (71 : ℕ) ≠ 72 by decide), State.setReg_regs_self])
      (by simp only [sF, sE, State.setReg_regs_ne _ _ (show (72 : ℕ) ≠ 70 by decide), State.setReg_regs_self])
      (by simp only [sF, sE, sC,
        State.setReg_regs_ne _ _ (show (73 : ℕ) ≠ 70 by decide),
        State.setReg_regs_ne _ _ (show (73 : ℕ) ≠ 72 by decide),
        State.setReg_regs_ne _ _ (show (73 : ℕ) ≠ 71 by decide), hregB 73 (by decide), hr3])
    refine ⟨s', 1 + (tB + (3 + (4 + 4))) + t,
      .while_true hc (by omega) (.seq hexB (.seq hexC (.seq hexE hexF))) hex,
      by omega, ?_, ?_, ?_⟩
    · simpa only [case3FollowBucket, case3IndexedTriples_cons,
        case3EncodedPairTriple_eq D ⟨head, hhead⟩, List.append_assoc] using hdst
    · intro a ha
      exact (harr a ha).trans (harrB a ha)
    · intro r hr
      rw [hreg r hr, State.setReg_regs_ne _ _ (by romega),
        State.setReg_regs_ne _ _ (by romega), State.setReg_regs_ne _ _ (by romega)]
      exact hregB r (by romega)

end GraphMinor.Compute
