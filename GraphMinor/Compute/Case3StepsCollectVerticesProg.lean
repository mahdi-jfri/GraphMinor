module

public import GraphMinor.Compute.Case3StepsCollectVerticesBody

/-!
# Collecting ordered member vertices

The scan records member vertices in increasing order in a buffer of the original
vertex count. The final count marks the end of the list. This is the vertex-list
part of Graph Minors XIII, (9.9), step 5, pp. 105–106.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Scan a vertex bitset into an ordered list and record its length. -/
def case3CollectVerticesProg (a_set a_key r_n r_i r_cnt : ℕ) : Cmd :=
  .seq (.alloc a_key (.reg r_n))
    (.seq (.assign r_i (.const 0))
      (.seq (.assign r_cnt (.const 0))
        (forUp r_i (.reg r_n) (case3CollectVerticesBody a_set a_key r_i r_cnt))))

private theorem collectVerticesLoop_exec {w n : ℕ} (S : Finset (Fin n)) 
    (a_set a_key r_n r_i r_cnt : ℕ) (ha : a_set ≠ a_key)
    (hni : r_n ≠ r_i) (hnc : r_n ≠ r_cnt) (hic : r_i ≠ r_cnt)
    (hw : 4 < 2 ^ w) (hn : n + 1 < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = n) {s : State}
    (hset : IsBitSet S a_set s) (hkey : s.arrs a_key = case3CollectedVertices S k)
    (hrn : s.regs r_n = n) (hri : s.regs r_i = k)
    (hrcnt : s.regs r_cnt = (case3BoundaryPrefix S k).length) :
    ∃ s' t, Exec w (forUp r_i (.reg r_n) (case3CollectVerticesBody a_set a_key r_i r_cnt)) s s' t ∧
      t ≤ 3 + 19 * rem ∧ s'.arrs a_key = case3CollectedVertices S n ∧
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
      case3CollectVerticesBody_exec S a_set a_key r_i r_cnt hw hnw k hk hset hkey hri hrcnt
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

/-- The ordered list and its length are computed in linear time. Only the
output array and the two scan registers change. -/
theorem case3CollectVerticesProg_exec {w n : ℕ} (S : Finset (Fin n)) 
    (a_set a_key r_n r_i r_cnt : ℕ) (ha : a_set ≠ a_key)
    (hni : r_n ≠ r_i) (hnc : r_n ≠ r_cnt) (hic : r_i ≠ r_cnt)
    (hw : 4 < 2 ^ w) (hn : n + 1 < 2 ^ w)
    {s : State} (hset : IsBitSet S a_set s) (hrn : s.regs r_n = n) :
    ∃ s' t, Exec w (case3CollectVerticesProg a_set a_key r_n r_i r_cnt) s s' t ∧
      t ≤ 20 * n + 8 ∧ s'.arrs a_key = (case3BoundaryVertices S).map Fin.val ++
        List.replicate (n - S.card) 0 ∧ s'.regs r_cnt = S.card ∧
      (∀ a, a ≠ a_key → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ r_i → r ≠ r_cnt → s'.regs r = s.regs r) := by
  have h0 : 0 < 2 ^ w := by omega
  let s₁ := s.setArr a_key (List.replicate n 0)
  let s₂ := s₁.setReg r_i 0
  let s₃ := s₂.setReg r_cnt 0
  have hex₁ : Exec w (.alloc a_key (.reg r_n)) s s₁ (1 + n) :=
    .alloc (by simp only [Expr.eval, checkWord, hrn, show n < 2 ^ w by omega, ↓reduceIte])
  have hex₂ : Exec w (.assign r_i (.const 0)) s₁ s₂ 2 :=
    .assign (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
  have hex₃ : Exec w (.assign r_cnt (.const 0)) s₂ s₃ 2 :=
    .assign (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
  obtain ⟨s₄, t₄, hex₄, ht₄, hkey₄, hcnt₄⟩ := collectVerticesLoop_exec S a_set a_key r_n r_i r_cnt
    ha hni hnc hic hw hn n 0 (by omega) (s := s₃)
    (hset.of_arr_eq (State.setArr_arrs_ne _ _ ha))
    (by simp only [s₃, s₂, s₁, State.setReg_arrs, State.setArr_arrs_self,
      case3CollectedVertices_zero])
    (by simp only [s₃, s₂, s₁, State.setReg_regs_ne _ _ hnc, State.setReg_regs_ne _ _ hni,
      State.setArr_regs, hrn])
    (by simp only [s₃, s₂, State.setReg_regs_ne _ _ hic, State.setReg_regs_self])
    (by simp only [s₃, State.setReg_regs_self, case3BoundaryPrefix_zero, List.length_nil])
  have hex : Exec w (case3CollectVerticesProg a_set a_key r_n r_i r_cnt) s s₄
      ((1 + n) + (2 + (2 + t₄))) := .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄))
  refine ⟨s₄, (1 + n) + (2 + (2 + t₄)), hex, by omega, ?_, hcnt₄, ?_, ?_⟩
  · exact hkey₄.trans (case3CollectedVertices_done S)
  · intro a ha'
    exact hex.arrs_eq_of_not_mem_writtenArrs (by
      simp [case3CollectVerticesProg, case3CollectVerticesBody, forUp, Cmd.writtenArrs, ha'])
  · intro r hi hc
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simp [case3CollectVerticesProg, case3CollectVerticesBody, forUp, Cmd.writtenRegs, hi, hc])

end GraphMinor.Compute
