module

public import GraphMinor.Compute.CrossingOpsEmit

/-!
# Array emission with a sum of body costs

The replacement record scans adjacency lists of different lengths. This loop rule sums
those lengths by allowing a separate body cost for each index. It uses the counting-loop
rule from `Compute.Logic` and tracks the emitted prefix and remaining buffer capacity.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- An array loop emitting a list for each entry, with a cost bound for each index. -/
theorem forArrEmitSum_exec {w : ℕ} (a r_i r_n r_y a_buf r_cnt : ℕ) (body : Cmd)
    (g : ℕ → List ℕ) (Q : ℕ → State → Prop) (B : ℕ → ℕ)
    (hin : r_i ≠ r_n) (hic : r_i ≠ r_cnt) (hnc : r_n ≠ r_cnt) (hyc : r_y ≠ r_cnt)
    (hyi : r_y ≠ r_i) (hyn : r_y ≠ r_n) (hw : 1 < 2 ^ w) {s : State} {pre : List ℕ} {k : ℕ}
    (hlen : (s.arrs a).length < 2 ^ w) (hl_w : ∀ x ∈ s.arrs a, x < 2 ^ w)
    (hQ0 : Q 0 s) (hb0 : IsBuf a_buf r_cnt pre k s)
    (hk : ((s.arrs a).flatMap g).length ≤ k)
    (hQ : ∀ j s s', Q j s → s'.arrs = s.arrs →
      (∀ r, r ≠ r_i → r ≠ r_n → r ≠ r_y → s'.regs r = s.regs r) → Q j s')
    (hent : ∀ j s', Q j s' → s'.arrs a = s.arrs a)
    (hbody : ∀ j (hj : j < (s.arrs a).length), ∀ s' pre' k', Q j s' → s'.regs r_i = j →
      s'.regs r_n = (s.arrs a).length → s'.regs r_y = (s.arrs a)[j] →
      IsBuf a_buf r_cnt pre' k' s' → (g (s.arrs a)[j]).length ≤ k' →
      pre'.length + k' = pre.length + k →
      ∃ s'' t, Exec w body s' s'' t ∧ t ≤ B j ∧ Q (j + 1) s'' ∧ s''.regs r_i = j ∧
        s''.regs r_n = (s.arrs a).length ∧
        IsBuf a_buf r_cnt (pre' ++ g (s.arrs a)[j]) (k' - (g (s.arrs a)[j]).length) s'') :
    ∃ s' t, Exec w (forArrProg a r_i r_n r_y body) s s' t ∧
      t ≤ 7 + ∑ j ∈ Finset.range (s.arrs a).length, (10 + B j) ∧ Q (s.arrs a).length s' ∧
      IsBuf a_buf r_cnt (pre ++ (s.arrs a).flatMap g) (k - ((s.arrs a).flatMap g).length) s' := by
  obtain ⟨l, hl⟩ : ∃ l, s.arrs a = l := ⟨_, rfl⟩
  rw [hl] at hlen hl_w hk hbody ⊢
  have hflat : ∀ j, (l.take j).flatMap g ++ (l.drop j).flatMap g = l.flatMap g := fun j => by
    rw [← List.flatMap_append, List.take_append_drop]
  have h0 : 0 < 2 ^ w := by omega
  have hex₁ : Exec w (.assign r_n (.len a)) s (s.setReg r_n l.length) 2 :=
    .assign (eval_len hl hlen)
  have hex₂ : Exec w (.assign r_i (.const 0)) (s.setReg r_n l.length)
      ((s.setReg r_n l.length).setReg r_i 0) 2 := .assign (eval_const h0)
  let I : ℕ → State → Prop := fun j st' =>
    st'.regs r_i = j ∧ st'.regs r_n = l.length ∧ Q j st' ∧
    IsBuf a_buf r_cnt (pre ++ (l.take j).flatMap g) (k - ((l.take j).flatMap g).length) st'
  have hI0 : I 0 ((s.setReg r_n l.length).setReg r_i 0) := by
    refine ⟨by simp, by simp [State.setReg_regs, hin.symm], ?_, ?_, ?_⟩
    · exact hQ 0 s _ hQ0 rfl (fun r h1 h2 _ => by simp [State.setReg_regs, h1, h2])
    · simpa using hb0.1
    · simp [State.setReg_regs, hic.symm, hnc.symm, hb0.2]
  obtain ⟨s', t, hex, ht, hI⟩ := Triple.forUp_sum I l.length (fun j => 3 + B j) (r_i := r_i) (hi := .reg r_n)
    (body := .seq (.assign r_y (.read a (.reg r_i))) body) hw hlen
    (fun j _ st' h => ⟨h.1, eval_reg h.2.1 hlen⟩)
    (fun j hj st' h => by
      obtain ⟨hri, hrn, hQj, hbj⟩ := h
      have hal : st'.arrs a = l := by rw [hent j st' hQj, hl]
      have hrd := eval_read (a := a) (eval_reg (w := w) hri (by omega)) (by rw [hal]; exact hj)
        (by simp only [hal]; exact hl_w _ (List.getElem_mem hj))
      simp only [hal] at hrd
      have hkj : (g l[j]).length ≤ k - ((l.take j).flatMap g).length := by
        have h1 := congrArg List.length (hflat j)
        rw [List.drop_eq_getElem_cons hj, List.flatMap_cons, List.length_append,
          List.length_append] at h1
        omega
      obtain ⟨s'', t', hex', ht', hQ', hri', hrn', hb'⟩ := hbody j hj (st'.setReg r_y l[j]) _ _
        (hQ j st' _ hQj rfl (fun r _ _ h3 => by simp [State.setReg_regs, h3]))
        (by simp [State.setReg_regs, hyi.symm, hri])
        (by simp [State.setReg_regs, hyn.symm, hrn])
        (by simp)
        ⟨hbj.1, by simp [State.setReg_regs, hyc.symm, hbj.2]⟩ hkj (by
          have h1 := congrArg List.length (hflat j)
          simp only [List.length_append] at h1 ⊢
          omega)
      refine ⟨s'', 3 + t', .seq (.assign hrd) hex', by simp [Expr.cost]; omega, ⟨by simp,
        by simp [State.setReg_regs, hin.symm, hrn'], hQ (j + 1) s'' _ hQ' rfl
          (fun r h1 _ _ => by simp [State.setReg_regs, h1]), ?_, ?_⟩, hri'⟩
      · rw [List.take_succ_eq_append_getElem hj, List.flatMap_append]
        simp only [State.setReg_arrs, hb'.1, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.append_assoc, List.length_append, Nat.sub_sub]
      · simp only [State.setReg_regs, hic.symm, ite_false, hb'.2]
        rw [List.take_succ_eq_append_getElem hj, List.flatMap_append]
        simp)
    _ hI0
  refine ⟨s', _, .seq hex₁ (.seq hex₂ hex), ?_, hI.2.2.1, by simpa using hI.2.2.2⟩
  simp only [Expr.cost] at ht ⊢
  have hsum : (∑ j ∈ Finset.range l.length, (1 + 6 + (3 + B j))) =
      ∑ j ∈ Finset.range l.length, (10 + B j) := by
    apply Finset.sum_congr rfl
    intro j _
    omega
  rw [hsum] at ht
  omega

end GraphMinor.Compute.Crossing
