module

public import GraphMinor.Compute.CrossingLiftStep

/-!
# One iteration of the backward record scan

An iteration reads the trailing length, moves the cursor to the record start, copies that
start to the dispatcher's scratch register and lifts the record. Keeping the cursor below
the dispatcher's registers preserves the position needed for the next iteration.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing

/-- Read the preceding record and lift it, leaving the cursor at its start. -/
def liftHistoryBodyProg (a_rec Q P a_base R : ℕ) : Cmd :=
  .seq (readLiftRecordProg a_rec R (R + 1))
    (.seq (.assign (R + 10) (.reg R)) (liftEncodedStepProg a_rec Q P a_base (R + 10)))

/-- A reverse iteration reads and lifts exactly the last record of the active prefix.
The hypotheses specify a single-step history and its new crossing, the last encoded
record and cursor in memory, caller layout and word bounds. -/
theorem liftHistoryBodyProg_exec {w N : ℕ} (G G' : SimpleGraph (Fin N))
    (S S' : Set (Fin N)) (D D' L₁ L₂ : List (Fin N)) (r : CrossRecord (Fin N))
    (hstep : IsHistory (G, S, D) [r] (G', S', D'))
    (hcross : IsCrossingPair G' D' L₁ L₂)
    (a_rec Q P a_base R : ℕ) (harr : [a_rec, Q, P].Nodup)
    (hrA : a_rec < a_base) (hQA : Q < a_base) (hPA : P < a_base)
    (pre words spare : List ℕ) (henc : IsRecordEnc r words) (s : State)
    (hrec : s.arrs a_rec = pre ++ words ++ spare)
    (hstop : s.regs R = pre.length + words.length)
    (hQ : s.arrs Q = L₁.map Fin.val) (hP : s.arrs P = L₂.map Fin.val)
    (hw : 65536 * (N + pre.length + words.length + 1) < 2 ^ w) :
    ∃ (s' : State) (t : ℕ) (W : List (Fin N) × List (Fin N)),
      Exec w (liftHistoryBodyProg a_rec Q P a_base R) s s' t ∧
      t ≤ 14 + 50000 * ((N + 1) * liftWorkCount [r] + words.length) ∧
      s'.regs R = pre.length ∧ IsLiftOne r (L₁, L₂) W ∧ IsCrossingPair G D W.1 W.2 ∧
      s'.arrs Q = W.1.map Fin.val ∧ s'.arrs P = W.2.map Fin.val ∧
      (∀ a < a_base, a ≠ Q → a ≠ P → s'.arrs a = s.arrs a) ∧
      (∀ k < R, s'.regs k = s.regs k) := by
  obtain ⟨body, _, hbody⟩ := henc.exists_body
  obtain ⟨s1, t1, he1, ht1, hc1, _, ha1, hr1⟩ := readLiftRecordProg_exec (w := w)
    a_rec R (R + 1) (by omega) pre body spare s (by simpa only [← hbody] using hrec)
    (by simpa only [List.length_append, ← hbody] using hstop) (by rw [List.length_append, ← hbody]; omega)
  let s2 := s1.setReg (R + 10) pre.length
  have he2 : Exec w (.assign (R + 10) (.reg R)) s1 s2 2 :=
    .assign (eval_reg hc1 (by omega))
  obtain ⟨s3, t3, W, he3, ht3, hi3, hc3, hQ3, hP3, ha3, hr3⟩ := liftEncodedStepProg_exec
    G G' S S' D D' L₁ L₂ r hstep hcross a_rec Q P a_base (R + 10) harr hrA hQA hPA
    pre words spare henc s2 ((ha1 _).trans hrec) (by simp [s2])
    ((ha1 _).trans hQ) ((ha1 _).trans hP) hw
  refine ⟨s3, t1 + (2 + t3), W, .seq he1 (.seq he2 he3), by omega,
    ?_, hi3, hc3, hQ3, hP3, ?_, ?_⟩
  · exact (hr3 R (by omega)).trans ((show s2.regs R = s1.regs R by
      simp [s2]).trans hc1)
  · intro a ha haq hap
    exact (ha3 a ha haq hap).trans (ha1 a)
  · intro k hk
    have hh := hr3 k (by omega)
    rw [show s2.regs k = s1.regs k by simp [s2, show k ≠ R + 10 by omega]] at hh
    exact hh.trans (hr1 k (by omega) (by omega))

end GraphMinor.Compute.Crossing
