module

public import GraphMinor.Compute.CrossingLiftHistoryLoop
public import GraphMinor.Compute.CrossingTopLift
import GraphMinor.Compute.Specs4

/-!
# The history-aware lift program

The program copies the used record length to a scratch cursor and lifts the records from
last to first. Replacements use the reverse search of Lemma 1 and contractions use the
three cases of Section 11. Section 12's vertex accounting bounds the number of those
operations by the original vertex count. The resulting time is linear in the used record
words plus quadratic in the vertex count, as required by the corrected lift interface.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing

/-- Start the backward lift at the used end of the record buffer. -/
def liftRecHistProg (a_rec r_rec Q P a_base r_base : ℕ) : Cmd :=
  .seq (.assign r_base (.reg r_rec)) (liftHistoryLoopProg a_rec Q P a_base r_base)

/-- The word-size convention of the corrected interface covers the cursor and all
single-record lifting bounds. No active length or ambient count register is assumed. -/
private theorem lift_word_bound {w N capacity : ℕ}
    (hw : wordSize 65536 (capacity + (N + 1) * (N + 1)) ≤ w) :
    65536 * (N + capacity + 1) < 2 ^ w := by
  have hh := mul_lt_two_pow_of_wordSize_le (by decide : 1 ≤ 65536) hw
  have hn : N + 1 ≤ (N + 1) * (N + 1) := by nlinarith
  omega

/-- The complete history-aware lift claim, with no hypotheses. The program follows the
reverse record order, uses at most one component search per replacement, and charges
vertex-count work only to replacements and contractions, of which there are at most `N`. -/
theorem liftRecHistProgClaim_proved : LiftRecHistProgClaim := by
  intro a_rec r_rec Q P a_base r_base harr hrbase
  refine ⟨liftRecHistProg a_rec r_rec Q P a_base r_base, 100003, 65536, ?_⟩
  intro w N inst
  have hinst : inst = instDecidableEqFin N := Subsingleton.elim _ _
  cases hinst
  intro G G' S S' D D' rs k L₁ L₂ s hw hhistory _ hcross hbuf hQ hP _ _
  obtain ⟨ls, hls, hrec, hused⟩ := hbuf
  have hcap : ls.flatten.length ≤ (s.arrs a_rec).length := by
    rw [hrec, List.length_append]
    omega
  have hw' := lift_word_bound hw
  let s0 := s.setReg r_base ls.flatten.length
  have hinit : Exec w (.assign r_base (.reg r_rec)) s s0 2 :=
    .assign (eval_reg hused (by omega))
  obtain ⟨s1, t1, W, he1, ht1, _, hi1, _, hoQ, hoP, ha1, hr1⟩ := liftHistoryLoopProg_exec
    G G' (S : Set (Fin N)) (S' : Set (Fin N)) D D' L₁ L₂ a_rec Q P a_base r_base harr.1
    (harr.2 _ (by simp)) (harr.2 _ (by simp)) (harr.2 _ (by simp))
    rs ls (List.replicate k 0) s0 hls hhistory hcross hrec (by simp [s0]) hQ hP hw'
  have hwork : (N + 1) * liftWorkCount rs ≤ (N + 1) * (N + 1) := by
    simpa only [Nat.mul_comm] using liftWorkCount_mul_le hhistory
  have hpos : 1 ≤ (N + 1) * (N + 1) := Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
  refine ⟨s1, 2 + t1, .seq hinit he1, ?_, ?_, W, hi1, hoQ, hoP⟩
  · rw [hused]
    omega
  · constructor
    · intro q hq _
      exact (hr1 q hq).trans (by simp [s0, show q ≠ r_base by omega])
    · intro a ha hnot
      have haq : a ≠ Q := fun h => hnot (by simp [h])
      have hap : a ≠ P := fun h => hnot (by simp [h])
      exact ha1 a ha haq hap

end GraphMinor.Compute.Crossing
