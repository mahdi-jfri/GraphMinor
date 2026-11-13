module

public import GraphMinor.Compute.CrossingOpsBfsRoots
public import GraphMinor.Compute.CrossingOpsBfsFill

/-!
# Initializing the BFS forest search

The number of vertices is read from the active array. The program allocates marks,
parent words, and queue storage, fills parent words with the dynamic sentinel, and
starts both queue indices and the possible-root index at zero.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Initialize the BFS search, reading the number of vertices from the active array. -/
def bfsForestInit (A R : ℕ) : Cmd :=
  .seq (.assign (R + 1) (.len (A + 6)))
    (.seq (.alloc (A + 3) (.reg (R + 1)))
      (.seq (.alloc (A + 4) (.reg (R + 1)))
        (.seq (fillLengthProg (A + 4) R)
          (.seq (queueInit (A + 5) (R + 2) (R + 3) (.reg (R + 1)))
            (.assign R (.const 0))))))

/-- Initialization produces empty marks, no parents, and an empty queue in linear time. -/
theorem bfsForestInit_exec {w N : ℕ} (A R : ℕ) {s : State}
    (hlen : (s.arrs (A + 6)).length = N) (hN : N < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ s' t, Exec w (bfsForestInit A R) s s' t ∧ t ≤ 20 + 13 * N ∧
      s'.regs R = 0 ∧ s'.regs (R + 1) = N ∧
      IsQueueHistory (A + 5) (R + 2) (R + 3) N [] 0 s' ∧
      s'.arrs (A + 3) = bfsMarks ([] : List (Fin N)) ∧
      IsBfsParentsAt (A + 4) ([] : List (Fin N × Fin N)) s' ∧
      (∀ a, a ≠ A + 3 → a ≠ A + 4 → a ≠ A + 5 → s'.arrs a = s.arrs a) ∧
      (∀ r, r < R ∨ R + 4 ≤ r → s'.regs r = s.regs r) := by
  let s1 := s.setReg (R + 1) N
  let s2 := s1.setArr (A + 3) (List.replicate N 0)
  let s3 := s2.setArr (A + 4) (List.replicate N 0)
  have he1 : Exec w (.assign (R + 1) (.len (A + 6))) s s1 2 :=
    .assign (by simp [Expr.eval, checkWord, hlen, hN])
  have he2 : Exec w (.alloc (A + 3) (.reg (R + 1))) s1 s2 (1 + N) :=
    .alloc (eval_reg (by simp [s1]) hN)
  have he3 : Exec w (.alloc (A + 4) (.reg (R + 1))) s2 s3 (1 + N) :=
    .alloc (eval_reg (by simp [s2, s1]) hN)
  obtain ⟨s4, t4, he4, ht4, ha4, haf4, hr4⟩ :=
    fillLengthProg_exec (A + 4) R (s := s3) (by simp [s3]) hN hw
  have hr4N : s4.regs (R + 1) = N := (hr4 _ (by omega)).trans (by simp [s3, s2, s1])
  let s5 := s4.setArr (A + 5) (List.replicate N 0)
  let s6 := s5.setReg (R + 2) 0
  let s7 := s6.setReg (R + 3) 0
  let s8 := s7.setReg R 0
  have he5 : Exec w (.alloc (A + 5) (.reg (R + 1))) s4 s5 (1 + N) :=
    .alloc (eval_reg hr4N hN)
  have he6 : Exec w (.assign (R + 2) (.const 0)) s5 s6 2 := .assign (eval_const (by omega))
  have he7 : Exec w (.assign (R + 3) (.const 0)) s6 s7 2 := .assign (eval_const (by omega))
  have he8 : Exec w (.assign R (.const 0)) s7 s8 2 := .assign (eval_const (by omega))
  have hex : Exec w (bfsForestInit A R) s s8
      (2 + ((1 + N) + ((1 + N) + (t4 + (((1 + N) + (2 + 2)) + 2))))) :=
    .seq he1 (.seq he2 (.seq he3 (.seq he4 (.seq (.seq he5 (.seq he6 he7)) he8))))
  refine ⟨s8, _, hex, by omega, by simp [s8], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [s8, s7, s6, s5, hr4N]
  · refine ⟨by simp [s8, s7, s6, s5], by simp, ?_, ?_, by simp, ?_⟩
    · simp [s8, s7, s6]
    · simp [s8, s7]
    · intro i hi; simp at hi
  · have hh := haf4 (A + 3) (by omega)
    simp only [s3, s2, State.setArr_arrs_ne _ _ (show A + 3 ≠ A + 4 by omega),
      State.setArr_arrs_self] at hh
    simpa [s8, s7, s6, s5, bfsMarks, List.ofFn_const] using hh
  · apply isBfsParentsAt_empty
    simpa [s8, s7, s6, s5] using ha4
  · intro a h3 h4 h5
    exact hex.arrs_eq_of_not_mem_writtenArrs (by
      simp [bfsForestInit, fillLengthProg, fillArr, forUp, queueInit, Cmd.writtenArrs, h3, h4, h5])
  · intro r hh
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      have h0 : r ≠ R := by omega
      have h1 : r ≠ R + 1 := by omega
      have h2 : r ≠ R + 2 := by omega
      have h3 : r ≠ R + 3 := by omega
      simp [bfsForestInit, fillLengthProg, fillArr, forUp, queueInit, Cmd.writtenRegs, h0, h1, h2, h3])

end GraphMinor.Compute.Crossing
