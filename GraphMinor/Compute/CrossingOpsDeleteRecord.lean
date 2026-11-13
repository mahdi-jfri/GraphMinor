module

public import GraphMinor.Compute.CrossingOpsContract
import GraphMinor.Compute.CrossingOpsReplFrames

/-!
# The deletion record for sparsification

Section 7.2 of `docs/crossing/crossing_extractor.tex` deletes the edges outside the retained graph.
The deletion record needs only its tag and length. This program writes those two
words in scratch memory and appends them to the existing record buffer.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing

/-- Store the two-word encoding of a deletion record. -/
def deletionEncodeProg (A : ℕ) : Cmd :=
  .seq (.alloc (A + 7) (.const 2))
    (.seq (.write (A + 7) (.const 0) (.const 2))
      (.write (A + 7) (.const 1) (.const 1)))

/-- The encoding command writes `[2,1]`, preserves other arrays, and changes no registers. -/
theorem deletionEncodeProg_exec {w : ℕ} (A : ℕ) (s : State) (hw : 2 < 2 ^ w) :
    ∃ s', Exec w (deletionEncodeProg A) s s' 9 ∧ s'.arrs (A + 7) = [2, 1] ∧
      (∀ a, a ≠ A + 7 → s'.arrs a = s.arrs a) ∧ s'.regs = s.regs := by
  let s0 := s.setArr (A + 7) [0, 0]
  let s1 := s0.writeArr (A + 7) 0 2
  let s2 := s1.writeArr (A + 7) 1 1
  have he0 : Exec w (.alloc (A + 7) (.const 2)) s s0 3 :=
    .alloc (eval_const hw)
  have he1 : Exec w (.write (A + 7) (.const 0) (.const 2)) s0 s1 3 :=
    .write (eval_const (by omega)) (eval_const hw) (by simp [s0])
  have he2 : Exec w (.write (A + 7) (.const 1) (.const 1)) s1 s2 3 :=
    .write (eval_const (by omega)) (eval_const (by omega)) (by simp [s1, s0])
  refine ⟨s2, .seq he0 (.seq he1 he2), ?_, ?_, rfl⟩
  · simp [s2, s1, s0, State.writeArr, State.setArr]
  · intro a ha
    simp [s2, s1, s0, State.writeArr_arrs_ne, State.setArr_arrs_ne, ha]

/-- Encode and append a deletion record without growing the record array. -/
def deletionAppendProg (a_rec r_rec A R : ℕ) : Cmd :=
  .seq (deletionEncodeProg A) (contrAppBuf a_rec r_rec A R)

/-- The deletion append takes at most 60 steps and consumes two free buffer entries.
The old graph and vertex set are the data recorded by the deletion constructor. -/
theorem deletionAppendProg_exec {w N : ℕ} (a_rec r_rec A R : ℕ)
    (hA : a_rec < A) (hrr : r_rec < R)
    {G : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {recs : List (CrossRecord (Fin N))} {k : ℕ} {s : State}
    (hbuf : IsRecBufAt a_rec r_rec recs k s) (h8 : s.regs (R + 8) = N)
    (hk : 2 ≤ k) (hw : (s.arrs a_rec).length + N + 4 < 2 ^ w) :
    ∃ s' t, Exec w (deletionAppendProg a_rec r_rec A R) s s' t ∧ t ≤ 60 ∧
      IsRecBufAt a_rec r_rec (recs ++ [CrossRecord.del G S]) (k - 2) s' ∧
      (s'.arrs a_rec).length = (s.arrs a_rec).length ∧
      (∀ a, a ≠ a_rec → a ≠ A + 7 → s'.arrs a = s.arrs a) ∧
      (∀ r, r < R → r ≠ r_rec → s'.regs r = s.regs r) := by
  obtain ⟨s0, he0, henc, ha0, hr0⟩ := deletionEncodeProg_exec (w := w) A s (by omega)
  have hrec : s0.arrs a_rec = s.arrs a_rec := ha0 _ (by omega)
  have hb0 : IsRecBufAt a_rec r_rec recs k s0 := by
    simpa only [IsRecBufAt, hrec, hr0] using hbuf
  obtain ⟨s1, t1, he1, ht1, hb1, hl1⟩ := contrAppBuf_exec (w := w) a_rec r_rec A R hA hrr hb0
    (rec := CrossRecord.del G S) (by simpa [IsRecordEnc, withLength, henc])
    (by rw [hr0]; exact h8) (by simpa [henc] using hk)
    (by rw [hrec, henc]; simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨s1, 9 + t1, .seq he0 he1, ?_, ?_, hl1.trans (congrArg List.length hrec), ?_, ?_⟩
  · rw [henc] at ht1; simp only [List.length_cons, List.length_nil] at ht1; omega
  · simpa only [henc, List.length_cons, List.length_nil] using hb1
  · intro a ha hb
    exact (he1.arrs_eq_of_not_mem_writtenArrs (by simp [ha])).trans (ha0 a hb)
  · intro r hr hne
    exact (he1.regs_eq_of_not_mem_writtenRegs (by simp; omega)).trans (congrFun hr0 r)

end GraphMinor.Compute.Crossing
