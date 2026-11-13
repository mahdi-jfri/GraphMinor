module

public import GraphMinor.Compute.CrossingOpsReplLists
public import GraphMinor.Compute.BitSet

/-!
# Reading the sparsification size and edge quota

The threshold in Section 7.2 uses the active vertex count. The command reads the
ambient size from the mark array, counts its set bits, and computes the quota
of three times the active count minus five. No graph size is built into the command.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Count active vertices, saving the ambient size in `R+8` and the count in `R+17`. -/
def sparsifyCountProg (a_alive R : ℕ) : Cmd :=
  .seq (.assign (R + 8) (.len a_alive))
    (cardBitSetProg a_alive (.reg (R + 8)) (R + 17) (R + 18))

/-- Reading and counting the active marks takes linear time and preserves all arrays. -/
theorem sparsifyCountProg_exec {w N : ℕ} (a_alive R : ℕ)
    (S : Finset (Fin N)) {s : State}
    (hal : s.arrs a_alive = List.ofFn (fun u : Fin N => if u ∈ S then 1 else 0))
    (hw : N + 2 < 2 ^ w) :
    ∃ s' t, Exec w (sparsifyCountProg a_alive R) s s' t ∧ t ≤ 12 * N + 9 ∧
      s'.regs (R + 8) = N ∧ s'.regs (R + 17) = S.card ∧
      s'.arrs = s.arrs ∧
      (∀ r, r ≠ R + 8 → r ≠ R + 17 → r ≠ R + 18 → s'.regs r = s.regs r) := by
  have hlen : (s.arrs a_alive).length = N := by rw [hal]; simp
  let s0 := s.setReg (R + 8) N
  have he0 : Exec w (.assign (R + 8) (.len a_alive)) s s0 2 := by
    apply Exec.assign
    simpa only [hlen] using eval_len (w := w) (s := s) (a := a_alive) rfl (by omega)
  obtain ⟨s1, t1, he1, ht1, hc1, ha1, hr1⟩ := cardBitSetProg_exec (w := w)
    S a_alive (R + 8) (R + 17) (R + 18) (by omega) (by omega) (by omega)
    (by omega) (by omega) (s := s0)
    (IsBitSet.of_bitSetList S a_alive s0 (by simpa [s0, bitSetList] using hal))
    (by simp [s0])
  refine ⟨s1, 2 + t1, .seq he0 he1, by omega, ?_, hc1, funext ha1, ?_⟩
  · rw [hr1 _ (by omega) (by omega)]; simp [s0]
  · intro r h8 h17 h18
    rw [hr1 _ h17 h18]; simp [s0, h8]

/-- Store the extra-edge quota from the active count. -/
def sparsifyQuotaProg (R : ℕ) : Cmd :=
  .assign (R + 5) (.op .sub (.op .mul (.const 3) (.reg (R + 17))) (.const 5))

/-- The quota is computed by word operations whenever the active count fits the bound. -/
theorem sparsifyQuotaProg_exec {w : ℕ} (R n : ℕ) {s : State}
    (hn : s.regs (R + 17) = n) (hw : 16 * n + 6 < 2 ^ w) :
    Exec w (sparsifyQuotaProg R) s (s.setReg (R + 5) (3 * n - 5)) 6 := by
  apply Exec.assign
  exact eval_sub (eval_mul (eval_const (by omega)) (eval_reg hn (by omega)) (by omega))
    (eval_const (by omega))

/-- Test whether the old graph exceeds sixteen times the active vertex count. -/
def sparsifyDenseTest (a_ent R : ℕ) : Expr :=
  .op .lt (.op .mul (.const 16) (.reg (R + 17)))
    (.op .div (.len a_ent) (.const 2))

/-- The numerical density test is exactly the threshold of Section 7.2. -/
theorem eval_sparsifyDenseTest {w : ℕ} (a_ent R n e : ℕ) {s : State}
    (hn : s.regs (R + 17) = n) (he : (s.arrs a_ent).length = 2 * e)
    (hw : 16 * n + 2 * e + 17 < 2 ^ w) :
    (sparsifyDenseTest a_ent R).eval w s = some (if 16 * n < e then 1 else 0) := by
  have hdiv : (Expr.op .div (.len a_ent) (.const 2)).eval w s = some e := by
    have h := eval_div (w := w) (s := s) (eval_len (a := a_ent) rfl (by omega))
      (eval_const (c := 2) (by omega)) (by decide) (by omega)
    simpa only [he, show 2 * e / 2 = e by omega] using h
  exact eval_lt (eval_mul (eval_const (by omega)) (eval_reg hn (by omega)) (by omega)) hdiv (by omega)

end GraphMinor.Compute.Crossing
