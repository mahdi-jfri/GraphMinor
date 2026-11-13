module

public import GraphMinor.Compute.CrossingOpsBasic

/-!
# Appending an oriented edge to the parser buffer

The replacement search keeps one orientation of each recorded edge. Its buffer begins with
two header words and has room for all recorded pairs. A cursor marks the next unused pair.
This file writes a pair at the cursor and advances it by two, preserving the remaining buffer.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Write the endpoints at the cursor and advance it past the pair. -/
def liftEmitPairProg (dst r_pos r_a r_b : ℕ) : Cmd :=
  .seq (.write dst (.reg r_pos) (.reg r_a))
    (.seq (.write dst (.op .add (.reg r_pos) (.const 1)) (.reg r_b))
      (.assign r_pos (.op .add (.reg r_pos) (.const 2))))

/-- Appending one pair costs twelve steps. The assumptions give its buffer position,
endpoints and word bounds. All other arrays and all other registers are preserved. -/
theorem liftEmitPairProg_exec {w : ℕ} (dst r_pos r_a r_b : ℕ)
    (A C : List ℕ) (a b : ℕ) (s : State)
    (hd : s.arrs dst = A ++ [0, 0] ++ C) (hp : s.regs r_pos = A.length)
    (ha : s.regs r_a = a) (hb : s.regs r_b = b)
    (hw : A.length + 3 < 2 ^ w) (haw : a < 2 ^ w) (hbw : b < 2 ^ w) :
    ∃ s', Exec w (liftEmitPairProg dst r_pos r_a r_b) s s' 12 ∧
      s'.arrs dst = A ++ [a, b] ++ C ∧ s'.regs r_pos = A.length + 2 ∧
      (∀ c, c ≠ dst → s'.arrs c = s.arrs c) ∧
      (∀ q, q ≠ r_pos → s'.regs q = s.regs q) := by
  let s1 := s.writeArr dst A.length a
  let s2 := s1.writeArr dst (A.length + 1) b
  have h1 : s1.arrs dst = A ++ [a, 0] ++ C := by
    simp only [s1, State.writeArr_arrs_self, hd, List.append_assoc,
      List.cons_append, List.nil_append]
    rw [List.set_append_right _ _ (by omega)]
    simp
  have h2 : s2.arrs dst = A ++ [a, b] ++ C := by
    simp only [s2, State.writeArr_arrs_self, h1, List.append_assoc,
      List.cons_append, List.nil_append]
    rw [List.set_append_right _ _ (by omega)]
    simp
  have he1 : Exec w (.write dst (.reg r_pos) (.reg r_a)) s s1 3 :=
    .write (eval_reg hp (by omega)) (eval_reg ha haw)
      (by rw [hd]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have he2 : Exec w (.write dst (.op .add (.reg r_pos) (.const 1)) (.reg r_b)) s1 s2 5 :=
    .write (eval_add (eval_reg hp (by omega)) (eval_const (by omega)) (by omega))
      (eval_reg hb hbw)
      (by rw [h1]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  refine ⟨s2.setReg r_pos (A.length + 2), .seq he1 (.seq he2
    (.assign (eval_add (eval_reg hp (by omega)) (eval_const (by omega)) (by omega)))),
    h2, by simp, ?_, ?_⟩
  · intro c hc
    simp only [State.setReg_arrs, s2, s1, State.writeArr_arrs_ne _ _ _ hc]
  · intro q hq
    simp [hq, s2, s1]

end GraphMinor.Compute.Crossing
