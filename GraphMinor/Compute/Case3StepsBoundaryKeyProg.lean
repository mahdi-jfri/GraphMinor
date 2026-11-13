module

public import GraphMinor.Compute.Case3StepsBoundaryKeyBody

/-!
# Writing a boundary key

The scan records boundary vertices in increasing order and finishes by
writing the size header. This computes a four-word key in linear time from
a bitset of a boundary with at most three vertices.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Scan the boundary bitset and write its size and vertex slots. -/
def case3BoundaryKeyProg (a_set a_key r_n r_i r_cnt : ℕ) : Cmd :=
  .seq (.alloc a_key (.const 4))
    (.seq (.assign r_i (.const 0))
      (.seq (.assign r_cnt (.const 0))
        (.seq (forUp r_i (.reg r_n) (case3BoundaryKeyBody a_set a_key r_i r_cnt))
          (.write a_key (.const 0) (.reg r_cnt)))))

private theorem boundaryKeyLoop_exec {w n : ℕ} (S : Finset (Fin n)) (hS : S.card ≤ 3)
    (a_set a_key r_n r_i r_cnt : ℕ) (ha : a_set ≠ a_key)
    (hni : r_n ≠ r_i) (hnc : r_n ≠ r_cnt) (hic : r_i ≠ r_cnt)
    (hw : 4 < 2 ^ w) (hn : n + 1 < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = n) {s : State}
    (hset : IsBitSet S a_set s) (hkey : s.arrs a_key = case3BoundaryKeyPrefix S k)
    (hrn : s.regs r_n = n) (hri : s.regs r_i = k)
    (hrcnt : s.regs r_cnt = (case3BoundaryPrefix S k).length) :
    ∃ s' t, Exec w (forUp r_i (.reg r_n) (case3BoundaryKeyBody a_set a_key r_i r_cnt)) s s' t ∧
      t ≤ 3 + 19 * rem ∧ s'.arrs a_key = case3BoundaryKeyPrefix S n ∧
      s'.regs r_cnt = S.card := by
  have h0 : 0 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have hnw : n < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk : k = n := by omega
    have hc : (Expr.op .lt (.reg r_i) (.reg r_n)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrn, hk, hnw, h0]
    refine ⟨s, 3, .while_false hc, by omega, hk ▸ hkey, ?_⟩
    simpa only [hk, case3BoundaryPrefix_done, case3BoundaryVertices_length] using hrcnt
  | succ rem ih =>
    have hk : k < n := by omega
    have hkw : k < 2 ^ w := by omega
    have hkpw : k + 1 < 2 ^ w := by omega
    have hc : (Expr.op .lt (.reg r_i) (.reg r_n)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrn, hk, hkw, hnw, h1]
    obtain ⟨sB, tB, hexB, htB, hkeyB, hcntB, harrB, hregB⟩ :=
      case3BoundaryKeyBody_exec S hS a_set a_key r_i r_cnt hw hnw k hk hset hkey hri hrcnt
    let sC := sB.setReg r_i (k + 1)
    have hriB : sB.regs r_i = k := (hregB r_i hic).trans hri
    have hexC : Exec w (.assign r_i (.op .add (.reg r_i) (.const 1))) sB sC 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hriB, hkw, h1, hkpw])
    obtain ⟨s', t, hex, ht, hdst, hcnt⟩ := ih (k + 1) (by omega) (s := sC)
      (hset.of_arr_eq (harrB a_set ha)) hkeyB
      (by rw [State.setReg_regs_ne _ _ hni, hregB r_n hnc, hrn])
      (State.setReg_regs_self ..)
      (by rw [State.setReg_regs_ne _ _ hic.symm]; exact hcntB)
    exact ⟨s', 3 + (tB + 4) + t, .while_true hc (by decide) (.seq hexB hexC) hex,
      by omega, hdst, hcnt⟩

/-- A small boundary key is written in at most `19 n + 15` steps. Only its
array and the two scan registers change. -/
theorem case3BoundaryKeyProg_exec {w n : ℕ} (S : Finset (Fin n)) (hS : S.card ≤ 3)
    (a_set a_key r_n r_i r_cnt : ℕ) (ha : a_set ≠ a_key)
    (hni : r_n ≠ r_i) (hnc : r_n ≠ r_cnt) (hic : r_i ≠ r_cnt)
    (hw : 4 < 2 ^ w) (hn : n + 1 < 2 ^ w)
    {s : State} (hset : IsBitSet S a_set s) (hrn : s.regs r_n = n) :
    ∃ s' t, Exec w (case3BoundaryKeyProg a_set a_key r_n r_i r_cnt) s s' t ∧
      t ≤ 19 * n + 15 ∧ s'.arrs a_key = case3BoundaryKey S ∧
      (∀ a, a ≠ a_key → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ r_i → r ≠ r_cnt → s'.regs r = s.regs r) := by
  have h0 : 0 < 2 ^ w := by omega
  let s₁ := s.setArr a_key (List.replicate 4 0)
  let s₂ := s₁.setReg r_i 0
  let s₃ := s₂.setReg r_cnt 0
  have hex₁ : Exec w (.alloc a_key (.const 4)) s s₁ 5 :=
    .alloc (by simp only [Expr.eval, checkWord, hw, ↓reduceIte])
  have hex₂ : Exec w (.assign r_i (.const 0)) s₁ s₂ 2 :=
    .assign (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
  have hex₃ : Exec w (.assign r_cnt (.const 0)) s₂ s₃ 2 :=
    .assign (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
  obtain ⟨s₄, t₄, hex₄, ht₄, hkey₄, hcnt₄⟩ := boundaryKeyLoop_exec S hS a_set a_key r_n r_i r_cnt
    ha hni hnc hic hw hn n 0 (by omega) (s := s₃)
    (hset.of_arr_eq (State.setArr_arrs_ne _ _ ha))
    (by simp only [s₃, s₂, s₁, State.setReg_arrs, State.setArr_arrs_self,
      case3BoundaryKeyPrefix, case3BoundaryPrefix_zero, List.map_nil, List.length_nil,
      List.nil_append, Nat.sub_zero]; rfl)
    (by simp only [s₃, s₂, s₁, State.setReg_regs_ne _ _ hnc, State.setReg_regs_ne _ _ hni,
      State.setArr_regs, hrn])
    (by simp only [s₃, s₂, State.setReg_regs_ne _ _ hic, State.setReg_regs_self])
    (by simp only [s₃, State.setReg_regs_self, case3BoundaryPrefix_zero, List.length_nil])
  let s₅ := s₄.writeArr a_key 0 S.card
  have hcw : S.card < 2 ^ w := by omega
  have hex₅ : Exec w (.write a_key (.const 0) (.reg r_cnt)) s₄ s₅ 3 :=
    .write (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
      (by simp only [Expr.eval, checkWord, hcnt₄, hcw, ↓reduceIte])
      (by rw [hkey₄, case3BoundaryKeyPrefix_length S hS n]; omega)
  have hex : Exec w (case3BoundaryKeyProg a_set a_key r_n r_i r_cnt) s s₅ (5 + (2 + (2 + (t₄ + 3)))) :=
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅)))
  refine ⟨s₅, 5 + (2 + (2 + (t₄ + 3))), hex, by omega, ?_, ?_, ?_⟩
  · simp only [s₅, State.writeArr_arrs_self, hkey₄, case3BoundaryKeyPrefix_finish]
  · intro a ha'
    exact hex.arrs_eq_of_not_mem_writtenArrs (by
      simp [case3BoundaryKeyProg, case3BoundaryKeyBody, forUp, Cmd.writtenArrs, ha'])
  · intro r hi hc
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simp [case3BoundaryKeyProg, case3BoundaryKeyBody, forUp, Cmd.writtenRegs, hi, hc])

end GraphMinor.Compute
