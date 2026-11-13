module

public import GraphMinor.Compute.CrossingLiftHistoryBody
public import GraphMinor.Compute.CrossingLiftHistoryData
import Mathlib.Data.List.Induction

/-!
# Lifting the whole history backwards

The cursor starts just after the active record prefix. Each iteration reads and lifts its
last record, preserving a crossing pair for the remaining prefix. Induction by the last
record proves termination and the lift relation. Encoded words pay for reading iterations,
and only replacements and contractions contribute vertex-count work.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing

/-- Read and lift records backwards until the active prefix is empty. -/
def liftHistoryLoopProg (a_rec Q P a_base R : ℕ) : Cmd :=
  .while (.reg R) (liftHistoryBodyProg a_rec Q P a_base R)

private theorem loop_cost_step (B L N K J tb tr : ℕ) (hL : 2 ≤ L)
    (hb : tb ≤ 14 + 50000 * ((N + 1) * K + L))
    (hr : tr ≤ 100000 * (B + (N + 1) * J) + 1) :
    1 + tb + tr ≤ 100000 * ((B + L) + (N + 1) * (J + K)) + 1 := by
  simp only [Nat.mul_add] at *
  omega

private theorem record_not_path (a Q P : ℕ) (h : [a, Q, P].Nodup) : a ≠ Q ∧ a ≠ P := by
  simpa only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or,
    not_false_eq_true, List.nodup_nil, and_true] using (List.nodup_cons.mp h).1

/-- The backward loop terminates with a lift and an old crossing pair. The hypotheses are
an encoded history, its final crossing pair and stored cursor/paths, caller layout and
word bounds. Trailing buffer words are arbitrary and are never scanned. -/
theorem liftHistoryLoopProg_exec {w N : ℕ} (G G' : SimpleGraph (Fin N))
    (S S' : Set (Fin N)) (D D' L₁ L₂ : List (Fin N))
    (a_rec Q P a_base R : ℕ) (harr : [a_rec, Q, P].Nodup)
    (hrA : a_rec < a_base) (hQA : Q < a_base) (hPA : P < a_base)
    (rs : List (CrossRecord (Fin N))) (ls : List (List ℕ)) (spare : List ℕ) (s : State)
    (hls : List.Forall₂ IsRecordEnc rs ls) (hhistory : IsHistory (G, S, D) rs (G', S', D'))
    (hcross : IsCrossingPair G' D' L₁ L₂)
    (hrec : s.arrs a_rec = ls.flatten ++ spare) (hcursor : s.regs R = ls.flatten.length)
    (hQ : s.arrs Q = L₁.map Fin.val) (hP : s.arrs P = L₂.map Fin.val)
    (hw : 65536 * (N + (s.arrs a_rec).length + 1) < 2 ^ w) :
    ∃ (s' : State) (t : ℕ) (W : List (Fin N) × List (Fin N)),
      Exec w (liftHistoryLoopProg a_rec Q P a_base R) s s' t ∧
      t ≤ 100000 * (ls.flatten.length + (N + 1) * liftWorkCount rs) + 1 ∧
      s'.regs R = 0 ∧ IsLift rs (L₁, L₂) W ∧ IsCrossingPair G D W.1 W.2 ∧
      s'.arrs Q = W.1.map Fin.val ∧ s'.arrs P = W.2.map Fin.val ∧
      (∀ a < a_base, a ≠ Q → a ≠ P → s'.arrs a = s.arrs a) ∧
      (∀ k < R, s'.regs k = s.regs k) := by
  induction rs using List.reverseRecOn generalizing G' S' D' L₁ L₂ ls spare s with
  | nil =>
    cases hls
    cases hhistory
    have hc : s.regs R = 0 := by simpa using hcursor
    exact ⟨s, 1, (L₁, L₂), .while_false (eval_reg hc (by omega)),
      by simp [liftWorkCount], hc, rfl, hcross, hQ, hP, fun _ _ _ _ => rfl, fun _ _ => rfl⟩
  | append_singleton rs r ih =>
    obtain ⟨encs, words, rfl, hencs, hword⟩ := liftRecordEncoding_snoc hls
    obtain ⟨⟨H, T, E⟩, hpre, hstep⟩ := liftHistory_snoc hhistory
    have hfull : s.arrs a_rec = encs.flatten ++ words ++ spare := by
      simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil,
        List.append_nil, List.append_assoc] using hrec
    have hcap := congrArg List.length hfull
    simp only [List.length_append] at hcap
    have hstop : s.regs R = encs.flatten.length + words.length := by
      simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil,
        List.append_nil, List.length_append] using hcursor
    obtain ⟨s1, t1, M, he1, ht1, hc1, hi1, hcross1, hQ1, hP1, ha1, hr1⟩ :=
      liftHistoryBodyProg_exec (w := w) H G' T S' E D' L₁ L₂ r hstep hcross
        a_rec Q P a_base R harr hrA hQA hPA encs.flatten words spare hword s hfull hstop hQ hP (by omega)
    obtain ⟨hrQ, hrP⟩ := record_not_path a_rec Q P harr
    have hrec1 : s1.arrs a_rec = s.arrs a_rec := ha1 a_rec hrA hrQ hrP
    have hbuf1 : s1.arrs a_rec = encs.flatten ++ (words ++ spare) := by
      rw [hrec1, hfull, List.append_assoc]
    obtain ⟨s2, t2, W, he2, ht2, hc2, hi2, hcross2, hQ2, hP2, ha2, hr2⟩ :=
      ih H T E M.1 M.2 encs (words ++ spare) s1 hencs hpre hcross1 hbuf1 hc1 hQ1 hP1
        (by rw [hrec1]; exact hw)
    have hL := hword.two_le_length
    have hc : (Expr.reg R).eval w s = some (encs.flatten.length + words.length) :=
      eval_reg hstop (by omega)
    have hlast : IsLift [r] (L₁, L₂) M := ⟨(L₁, L₂), rfl, hi1⟩
    refine ⟨s2, 1 + t1 + t2, W, .while_true hc (by omega) he1 he2, ?_, hc2,
      liftHistory_lift_append hlast hi2, hcross2, hQ2, hP2, ?_, ?_⟩
    · have htime := loop_cost_step encs.flatten.length words.length N (liftWorkCount [r])
        (liftWorkCount rs) t1 t2 hL ht1 ht2
      simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil,
        List.append_nil, List.length_append, liftWorkCount_append] using htime
    · intro a ha haq hap
      exact (ha2 a ha haq hap).trans (ha1 a ha haq hap)
    · intro k hk
      exact (hr2 k hk).trans (hr1 k hk)

end GraphMinor.Compute.Crossing
