module

public import GraphMinor.Compute.F92Segments
public import GraphMinor.Compute.F92Labels

/-!
# Scanning a path to its first intersection

Read vertices in order. On the first vertex that belongs to the current segment set but
not the wall, save the prefix length including that vertex and finish the loop. If no such
vertex is found, retain the full path. The arrays are read only.
-/

@[expose] public section

namespace GraphMinor.Compute.Alg92

/-- One step of the first-intersection scan. Registers hold total length, cursor,
retained length and current vertex, in that order. -/
def f92CutStepProg (a_path a_H a_F r_base : ℕ) : Cmd :=
  .seq (.assign (r_base + 3) (.read a_path (.reg (r_base + 1))))
    (.ite (.read a_F (.reg (r_base + 3)))
      (.ite (.read a_H (.reg (r_base + 3)))
        (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1)))
        (.seq (.assign (r_base + 2) (.op .add (.reg (r_base + 1)) (.const 1)))
          (.assign (r_base + 1) (.reg r_base))))
      (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1))))

/-- The state after reading one vertex. -/
def f92CutStepState (s : State) (r_base i N y : ℕ) (hit : Bool) : State :=
  let s₁ := s.setReg (r_base + 3) y
  if hit then (s₁.setReg (r_base + 2) (i + 1)).setReg (r_base + 1) N
  else s₁.setReg (r_base + 1) (i + 1)

/-- One scan step tests the two bitsets and either advances or records the first hit. -/
theorem f92CutStepProg_exec {w n h : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (F : Finset (Fin n))
    (a_path a_H a_F r_base i N : ℕ) (y : Fin n) (s : State)
    (hH : IsBitSet W.vertexFinset a_H s) (hF : IsBitSet F a_F s)
    (hri : s.regs (r_base + 1) = i) (hrN : s.regs r_base = N)
    (hi : i < (s.arrs a_path).length) (hval : (s.arrs a_path)[i]'hi = y.val)
    (hiN : i < N) (hN : N < 2 ^ w) (hn : n < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ t, Exec w (f92CutStepProg a_path a_H a_F r_base) s
      (f92CutStepState s r_base i N y.val (f92Meets W F y)) t ∧ t ≤ 13 := by
  have hiw : i < 2 ^ w := hiN.trans hN
  have hincw : i + 1 < 2 ^ w := (Nat.succ_le_of_lt hiN).trans_lt hN
  have hyw := y.isLt.trans hn
  let s₁ := s.setReg (r_base + 3) y.val
  have hex₁ : Exec w (.assign (r_base + 3) (.read a_path (.reg (r_base + 1)))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, hri, hiw, hi, hval, hyw])
  have hread (X : Finset (Fin n)) (a : ℕ) (hx : IsBitSet X a s) :
      (Expr.read a (.reg (r_base + 3))).eval w s₁ = some (if y ∈ X then 1 else 0) := by
    have hlen := hx.1
    have hv := hx.getElem_eq_ite y
    simp only [Expr.eval, s₁, State.setReg_regs_self, State.setReg_arrs, checkWord,
      hyw, hlen, y.isLt, hv, ↓reduceIte]
    split_ifs <;> simp_all
  have hreadF := hread F a_F hF
  have hreadH := hread W.vertexFinset a_H hH
  have hinc : Exec w (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1)))
      s₁ (s₁.setReg (r_base + 1) (i + 1)) 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁,
      hri, hiw, hw, hincw])
  have hstop : Exec w
      (.seq (.assign (r_base + 2) (.op .add (.reg (r_base + 1)) (.const 1)))
        (.assign (r_base + 1) (.reg r_base))) s₁
      ((s₁.setReg (r_base + 2) (i + 1)).setReg (r_base + 1) N) 6 :=
    .seq (.assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁,
      hri, hiw, hw, hincw]))
      (.assign (by simp [Expr.eval, checkWord, s₁, hrN, hN]))
  unfold f92CutStepProg f92CutStepState f92Meets
  by_cases hyF : y ∈ F
  · simp only [hyF, ↓reduceIte] at hreadF
    by_cases hyH : y ∈ W.vertexFinset
    · simp only [hyH, ↓reduceIte] at hreadH
      simp only [hyF, hyH, not_true_eq_false, and_false, decide_false, Bool.false_eq_true,
        ↓reduceIte]
      exact ⟨11, .seq hex₁ (.ite_true hreadF (by omega) (.ite_true hreadH (by omega) hinc)), by omega⟩
    · simp only [hyH, ↓reduceIte] at hreadH
      simp only [hyF, hyH, not_false_eq_true, and_self, decide_true, ↓reduceIte]
      exact ⟨13, .seq hex₁ (.ite_true hreadF (by omega) (.ite_false hreadH hstop)), by omega⟩
  · simp only [hyF, ↓reduceIte] at hreadF
    simp only [hyF, false_and, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact ⟨9, .seq hex₁ (.ite_false hreadF hinc), by omega⟩

/-- Scan until the cursor reaches the total path length. -/
def f92CutLoopProg (a_path a_H a_F r_base : ℕ) : Cmd :=
  .while (.op .lt (.reg (r_base + 1)) (.reg r_base))
    (f92CutStepProg a_path a_H a_F r_base)

/-- Starting at a path suffix, the loop retains exactly the prefix through its first hit.
The retained length is initialized to the full path length, so a search with no hit keeps it. -/
theorem f92CutLoopProg_exec {w n h : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (F : Finset (Fin n)) (a_path a_H a_F r_base N : ℕ)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hN : N < 2 ^ w) :
    ∀ (L pre : List (Fin n)) (s : State), N = pre.length + L.length →
      s.arrs a_path = (pre ++ L).map Fin.val →
      IsBitSet W.vertexFinset a_H s → IsBitSet F a_F s →
      s.regs r_base = N → s.regs (r_base + 1) = pre.length →
      s.regs (r_base + 2) = N →
      ∃ s' t, Exec w (f92CutLoopProg a_path a_H a_F r_base) s s' t ∧
        t ≤ 3 + 30 * L.length ∧ s'.regs (r_base + 1) = N ∧
        s'.regs (r_base + 2) = pre.length + (f92Prefix W F L).length
  | [], pre, s, hsize, _, _, _, hrN, hri, hcut => by
    have hcond : (Expr.op .lt (.reg (r_base + 1)) (.reg r_base)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrN,
        show pre.length = N by simpa using hsize.symm, hN, Nat.zero_lt_of_lt hw]
    have hsize' : N = pre.length := by simpa using hsize
    exact ⟨s, 3, .while_false hcond, by simp, hri.trans hsize'.symm,
      by simpa [f92Prefix] using hcut.trans hsize'⟩
  | y :: ys, pre, s, hsize, hsrc, hH, hF, hrN, hri, hcut => by
    have hip : pre.length < N := by simp only [List.length_cons] at hsize; omega
    have hipw := hip.trans hN
    have hcond : (Expr.op .lt (.reg (r_base + 1)) (.reg r_base)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrN, hipw, hN, hip, hw]
    have hiarr : pre.length < (s.arrs a_path).length := by
      rw [hsrc, List.length_map, List.length_append, List.length_cons]; omega
    have hyval : (s.arrs a_path)[pre.length]'hiarr = y.val := by
      simp [hsrc, List.getElem_append_right]
    obtain ⟨t₁, hex₁, ht₁⟩ := f92CutStepProg_exec W F a_path a_H a_F r_base
      pre.length N y s hH hF hri hrN hiarr hyval hip hN hn hw
    let st := f92CutStepState s r_base pre.length N y.val (f92Meets W F y)
    by_cases hhit : f92Meets W F y = true
    · have hri' : st.regs (r_base + 1) = N := by simp [st, f92CutStepState, hhit]
      have hcut' : st.regs (r_base + 2) = pre.length + 1 := by simp [st, f92CutStepState, hhit]
      have hrN' : st.regs r_base = N := by simp [st, f92CutStepState, hhit, hrN]
      have hstop : Exec w (f92CutLoopProg a_path a_H a_F r_base) st st 3 :=
        .while_false (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri', hrN', hN,
          Nat.zero_lt_of_lt hw])
      exact ⟨st, 3 + t₁ + 3, .while_true hcond (by omega) hex₁ hstop,
        by simp only [List.length_cons]; omega, hri', by simpa [f92Prefix, hhit] using hcut'⟩
    · have hfalse : f92Meets W F y = false := Bool.eq_false_iff.mpr hhit
      have hsrc' : st.arrs a_path = ((pre ++ [y]) ++ ys).map Fin.val := by
        simpa [st, f92CutStepState, hfalse, List.append_assoc] using hsrc
      obtain ⟨s', t', hex', ht', hri', hcut'⟩ :=
        f92CutLoopProg_exec W F a_path a_H a_F r_base N hw hn hN ys (pre ++ [y]) st
          (by simp only [List.length_append, List.length_cons, List.length_nil] at hsize ⊢; omega)
          hsrc' (hH.of_arr_eq (by simp [st, f92CutStepState, hfalse]))
          (hF.of_arr_eq (by simp [st, f92CutStepState, hfalse]))
          (by simp [st, f92CutStepState, hfalse, hrN])
          (by simp [st, f92CutStepState, hfalse])
          (by simp [st, f92CutStepState, hfalse, hcut])
      refine ⟨s', 3 + t₁ + t', .while_true hcond (by omega) hex₁ hex',
        by simp only [List.length_cons]; omega, hri', ?_⟩
      simpa [f92Prefix, hfalse, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcut'

/-- Initialize the retained length and scan the whole path. -/
def f92CutProg (a_path a_H a_F r_base : ℕ) : Cmd :=
  .seq (.assign r_base (.len a_path))
    (.seq (.assign (r_base + 1) (.const 0))
      (.seq (.assign (r_base + 2) (.reg r_base)) (f92CutLoopProg a_path a_H a_F r_base)))

/-- The scan computes the exact length of `f92Prefix` in linear time, without changing
any array or any register outside its four scratch registers. -/
theorem f92CutProg_exec {w n h : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (F : Finset (Fin n)) (P : List (Fin n))
    (a_path a_H a_F r_base : ℕ) (hw : 1 < 2 ^ w) (hn : n < 2 ^ w)
    (hP : P.length < 2 ^ w) {s : State}
    (hsrc : s.arrs a_path = P.map Fin.val)
    (hH : IsBitSet W.vertexFinset a_H s) (hF : IsBitSet F a_F s) :
    ∃ s' t, Exec w (f92CutProg a_path a_H a_F r_base) s s' t ∧
      t ≤ 9 + 30 * P.length ∧ s'.regs (r_base + 2) = (f92Prefix W F P).length ∧
      (∀ a, s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q < r_base ∨ r_base + 3 < q → s'.regs q = s.regs q) := by
  let s₁ := s.setReg r_base P.length
  have hex₁ : Exec w (.assign r_base (.len a_path)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hsrc, hP])
  let s₂ := s₁.setReg (r_base + 1) 0
  have hex₂ : Exec w (.assign (r_base + 1) (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  let s₃ := s₂.setReg (r_base + 2) P.length
  have hex₃ : Exec w (.assign (r_base + 2) (.reg r_base)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, s₂, s₁, hP])
  obtain ⟨s₄, t₄, hex₄, ht₄, _, hcut₄⟩ :=
    f92CutLoopProg_exec W F a_path a_H a_F r_base P.length hw hn hP P [] s₃ (by simp) hsrc
      (hH.of_arr_eq rfl) (hF.of_arr_eq rfl) (by simp [s₃, s₂, s₁]) (by simp [s₃, s₂]) (by simp [s₃])
  have hex : Exec w (f92CutProg a_path a_H a_F r_base) s s₄ (2 + (2 + (2 + t₄))) :=
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄))
  refine ⟨s₄, _, hex, by omega, by simpa using hcut₄, ?_, ?_⟩
  · intro a
    exact hex.arrs_eq_of_not_mem_writtenArrs (by
      simp [f92CutProg, f92CutLoopProg, f92CutStepProg, Cmd.writtenArrs])
  · intro q hq
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simp [f92CutProg, f92CutLoopProg, f92CutStepProg, Cmd.writtenRegs,
        show q ≠ r_base by omega, show q ≠ r_base + 1 by omega,
        show q ≠ r_base + 2 by omega, show q ≠ r_base + 3 by omega])

end GraphMinor.Compute.Alg92
