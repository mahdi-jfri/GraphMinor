module

public import GraphMinor.Compute.CrossingOpsBasic

/-!
# Loops that emit entries into a buffer

Most loops of the programs of the crossing extractor walk over a list (an adjacency list, or a
whole array) and, for each entry `y`, append some entries `g y` to a buffer (`IsBuf`). This file
proves this pattern once, for a loop over an adjacency list (`forListEmit_exec`) and for a loop
over an array (`forArrProg`, `forArrEmit_exec`). The property `Q j` describes the rest of the
state after `j` entries; it must not depend on the counting registers of the loop.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- **A loop over an adjacency list that emits `g y` for each entry `y`.** -/
theorem forListEmit_exec {w : ℕ} (a_s a_e a_ent r_u r_k r_hi r_v a_buf r_cnt : ℕ) (body : Cmd)
    (u st en : ℕ) (l : List ℕ) (g : ℕ → List ℕ) (Q : ℕ → State → Prop) (B : ℕ)
    (hku : r_u ≠ r_k) (hkh : r_k ≠ r_hi) (hkc : r_k ≠ r_cnt) (hhc : r_hi ≠ r_cnt)
    (hvc : r_v ≠ r_cnt) (hvk : r_v ≠ r_k) (hvh : r_v ≠ r_hi)
    (hw : 1 < 2 ^ w) (hen : en < 2 ^ w) (hu : u < 2 ^ w) {s : State} {pre : List ℕ} {k : ℕ}
    (hlist : IsListAt a_s a_e a_ent u st en l s) (hru : s.regs r_u = u)
    (hl_w : ∀ x ∈ l, x < 2 ^ w) (hQ0 : Q 0 s) (hb0 : IsBuf a_buf r_cnt pre k s)
    (hk : (l.flatMap g).length ≤ k)
    (hQ : ∀ j s s', Q j s → s'.arrs = s.arrs →
      (∀ r, r ≠ r_k → r ≠ r_hi → r ≠ r_v → s'.regs r = s.regs r) → Q j s')
    (hent : ∀ j s', Q j s' → s'.arrs a_ent = s.arrs a_ent)
    (hbody : ∀ j (hj : j < l.length), ∀ s' pre' k', Q j s' → s'.regs r_k = st + j →
      s'.regs r_hi = en → s'.regs r_v = l[j] → IsBuf a_buf r_cnt pre' k' s' →
      (g l[j]).length ≤ k' → pre'.length + k' = pre.length + k →
      ∃ s'' t, Exec w body s' s'' t ∧ t ≤ B ∧ Q (j + 1) s'' ∧ s''.regs r_k = st + j ∧
        s''.regs r_hi = en ∧ IsBuf a_buf r_cnt (pre' ++ g l[j]) (k' - (g l[j]).length) s'') :
    ∃ s' t, Exec w (forList a_s a_e a_ent r_u r_k r_hi r_v body) s s' t ∧
      t ≤ 9 + l.length * (10 + B) ∧ Q l.length s' ∧
      IsBuf a_buf r_cnt (pre ++ l.flatMap g) (k - (l.flatMap g).length) s' := by
  have hflat : ∀ j, (l.take j).flatMap g ++ (l.drop j).flatMap g = l.flatMap g := fun j => by
    rw [← List.flatMap_append, List.take_append_drop]
  let I : ℕ → State → Prop := fun j st' =>
    Q j st' ∧ IsBuf a_buf r_cnt (pre ++ (l.take j).flatMap g)
      (k - ((l.take j).flatMap g).length) st'
  have hI0 : I 0 ((s.setReg r_k st).setReg r_hi en) := by
    refine ⟨hQ 0 s _ hQ0 rfl (fun r h1 h2 _ => by simp [State.setReg_regs, h1, h2]), ?_, ?_⟩
    · simpa using hb0.1
    · simp [State.setReg_regs, hkc.symm, hhc.symm, hb0.2]
  obtain ⟨s', t, hex, ht, hI⟩ := forList_exec a_s a_e a_ent r_u r_k r_hi r_v body u st en l I B
    hku hkh hw hen hu hlist hru hI0
    (fun j hj st' h => by
      have := hent j st' h.1
      obtain ⟨hu_st, hu_en, hen_ent, hdiff, hst, hen', hle, helem⟩ := hlist
      rw [this]
      exact ⟨by omega, helem j hj⟩)
    hl_w
    (fun j hj st' h hrk hrh => by
      obtain ⟨hQj, hbj⟩ := h
      have hkj : (g l[j]).length ≤ k - ((l.take j).flatMap g).length := by
        have h1 := congrArg List.length (hflat j)
        rw [List.drop_eq_getElem_cons hj, List.flatMap_cons, List.length_append,
          List.length_append] at h1
        omega
      obtain ⟨s'', t', hex', ht', hQ', hrk', hrh', hb'⟩ := hbody j hj (st'.setReg r_v l[j]) _ _
        (hQ j st' _ hQj rfl (fun r _ _ h3 => by simp [State.setReg_regs, h3]))
        (by simp [State.setReg_regs, hvk.symm, hrk])
        (by simp [State.setReg_regs, hvh.symm, hrh])
        (by simp)
        ⟨hbj.1, by simp [State.setReg_regs, hvc.symm, hbj.2]⟩ hkj (by
          have h1 := congrArg List.length (hflat j)
          simp only [List.length_append] at h1 ⊢
          omega)
      refine ⟨s'', t', hex', ht', hrk', hrh', ⟨hQ (j + 1) s'' _ hQ' rfl
        (fun r h1 _ _ => by simp [State.setReg_regs, h1]), ?_, ?_⟩⟩
      · rw [List.take_succ_eq_append_getElem hj, List.flatMap_append]
        simp only [State.setReg_arrs, hb'.1, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.append_assoc, List.length_append, Nat.sub_sub]
      · simp only [State.setReg_regs, hkc.symm, if_false, hb'.2]
        rw [List.take_succ_eq_append_getElem hj, List.flatMap_append]
        simp)
  refine ⟨s', t, hex, ht, hI.1, ?_⟩
  simpa using hI.2

/-! ### A loop over an array -/

/-- Run `body` for each entry `a[i]` of the array `a`, with `i` in register `r_i`, the length in
`r_n` and the entry in `r_y`. -/
def forArrProg (a : Arr) (r_i r_n r_y : Reg) (body : Cmd) : Cmd :=
  .seq (.assign r_n (.len a))
    (.seq (.assign r_i (.const 0))
      (forUp r_i (.reg r_n) (.seq (.assign r_y (.read a (.reg r_i))) body)))

/-- **A loop over an array that emits `g y` for each entry `y`.** -/
theorem forArrEmit_exec {w : ℕ} (a r_i r_n r_y a_buf r_cnt : ℕ) (body : Cmd)
    (g : ℕ → List ℕ) (Q : ℕ → State → Prop) (B : ℕ)
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
      ∃ s'' t, Exec w body s' s'' t ∧ t ≤ B ∧ Q (j + 1) s'' ∧ s''.regs r_i = j ∧
        s''.regs r_n = (s.arrs a).length ∧
        IsBuf a_buf r_cnt (pre' ++ g (s.arrs a)[j]) (k' - (g (s.arrs a)[j]).length) s'') :
    ∃ s' t, Exec w (forArrProg a r_i r_n r_y body) s s' t ∧
      t ≤ 7 + (s.arrs a).length * (10 + B) ∧ Q (s.arrs a).length s' ∧
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
  obtain ⟨s', t, hex, ht, hI⟩ := forUp_exec' I l.length (3 + B) (r_i := r_i) (hi := .reg r_n)
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
      · simp only [State.setReg_regs, hic.symm, if_false, hb'.2]
        rw [List.take_succ_eq_append_getElem hj, List.flatMap_append]
        simp)
    _ hI0
  refine ⟨s', _, .seq hex₁ (.seq hex₂ hex), ?_, hI.2.2.1, by simpa using hI.2.2.2⟩
  simp only [Expr.cost] at ht ⊢
  nlinarith

/-! ### Tests of equality -/

theorem exec_ite_eq_true {w : ℕ} {r₁ r₂ : Reg} {c₁ c₂ : Cmd} {s s' : State} {t a : ℕ}
    (h₁ : s.regs r₁ = a) (h₂ : s.regs r₂ = a) (ha : a < 2 ^ w) (hw : 1 < 2 ^ w)
    (hc : Exec w c₁ s s' t) : Exec w (.ite (.op .eq (.reg r₁) (.reg r₂)) c₁ c₂) s s' (3 + t) :=
  .ite_true (eval_eq (eval_reg h₁ ha) (eval_reg h₂ ha) hw) (by simp) hc

theorem exec_ite_eq_false {w : ℕ} {r₁ r₂ : Reg} {c₁ c₂ : Cmd} {s s' : State} {t a b : ℕ}
    (h₁ : s.regs r₁ = a) (h₂ : s.regs r₂ = b) (hab : a ≠ b) (ha : a < 2 ^ w) (hb : b < 2 ^ w)
    (hw : 1 < 2 ^ w) (hc : Exec w c₂ s s' t) :
    Exec w (.ite (.op .eq (.reg r₁) (.reg r₂)) c₁ c₂) s s' (3 + t) := by
  have := eval_eq (w := w) (s := s) (eval_reg h₁ ha) (eval_reg h₂ hb) hw
  rw [if_neg hab] at this
  exact .ite_false this hc

/-- Emitting the value of a register. -/
theorem emitReg_exec {w : ℕ} (a_buf r_cnt r : ℕ) {pre : List ℕ} {k v : ℕ} {s : State}
    (hb : IsBuf a_buf r_cnt pre (k + 1) s) (hv : s.regs r = v) (hvw : v < 2 ^ w)
    (hw : pre.length + 1 < 2 ^ w) :
    ∃ s', Exec w (emitProg a_buf r_cnt (.reg r)) s s' 7 ∧ IsBuf a_buf r_cnt (pre ++ [v]) k s' ∧
      (∀ a, a ≠ a_buf → s'.arrs a = s.arrs a) ∧ (∀ r', r' ≠ r_cnt → s'.regs r' = s.regs r') := by
  obtain ⟨hex, hb'⟩ := emitProg_exec a_buf r_cnt (.reg r) hb (eval_reg hv hvw) hw
  refine ⟨_, hex, hb', fun a ha => by simp [State.writeArr_arrs_ne _ _ _ ha],
    fun r' hr => by simp [State.setReg_regs, hr]⟩

end GraphMinor.Compute.Crossing
