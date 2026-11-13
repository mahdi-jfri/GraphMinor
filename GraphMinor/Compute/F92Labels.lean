module

public import GraphMinor.Compute.F92Search
public import GraphMinor.Compute.F92Unpack

/-!
# Preparing the labels for a subwall search

Each vertex is labeled by reading the main-wall, subwall and inside bitsets. Inside vertices
are sources, wall vertices outside the subwall are targets, the remaining wall vertices
are forbidden, and vertices outside the wall are free. One scan writes all labels.
-/

@[expose] public section

namespace GraphMinor.Compute.Alg92

/-- Label one vertex using the three bitsets. -/
def f92LabelStepProg (a_H a_S a_I a_lab r_i : ℕ) : Cmd :=
  .ite (.read a_I (.reg r_i)) (.write a_lab (.reg r_i) (.const 0))
    (.ite (.read a_H (.reg r_i))
      (.ite (.read a_S (.reg r_i)) (.write a_lab (.reg r_i) (.const 2))
        (.write a_lab (.reg r_i) (.const 3)))
      (.write a_lab (.reg r_i) (.const 0)))

private theorem bitset_read_eval {w n : ℕ} {X : Finset (Fin n)} {a r : ℕ}
    {s : State} (hX : IsBitSet X a s) (i : Fin n) (hr : s.regs r = i.val)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) :
    (Expr.read a (.reg r)).eval w s = some (if i ∈ X then 1 else 0) := by
  have hiw := i.isLt.trans hn
  have hlen := hX.1
  have hv := hX.getElem_eq_ite i
  simp only [Expr.eval, hr, checkWord, hiw, hlen, i.isLt, hv, ↓reduceIte]
  split_ifs <;> simp_all

/-- The label for one vertex is written in at most nine steps. -/
theorem f92LabelStepProg_exec {w n h hs : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (S : WallOfHeight hs G)
    (a_H a_S a_I a_lab r_i : ℕ) (s : State) (i : Fin n)
    (hH : IsBitSet W.vertexFinset a_H s) (hS : IsBitSet S.vertexFinset a_S s)
    (hI : IsBitSet S.insideFinset a_I s) (hr : s.regs r_i = i.val)
    (hlab : (s.arrs a_lab).length = n) (hw : 3 < 2 ^ w) (hn : n < 2 ^ w) :
    ∃ t, Exec w (f92LabelStepProg a_H a_S a_I a_lab r_i) s
      (s.writeArr a_lab i.val (f92SearchLabel W S i)) t ∧ t ≤ 9 := by
  have hw1 : 1 < 2 ^ w := by omega
  have hiw := i.isLt.trans hn
  have hreadH := bitset_read_eval hH i hr hw1 hn
  have hreadS := bitset_read_eval hS i hr hw1 hn
  have hreadI := bitset_read_eval hI i hr hw1 hn
  have hwrite (v : ℕ) (hv : v < 2 ^ w) :
      Exec w (.write a_lab (.reg r_i) (.const v)) s (s.writeArr a_lab i.val v) 3 :=
    .write (by simp [Expr.eval, checkWord, hr, hiw])
      (by simp [Expr.eval, checkWord, hv]) (by rw [hlab]; exact i.isLt)
  unfold f92LabelStepProg f92SearchLabel
  by_cases hinside : i ∈ S.insideFinset
  · simp only [hinside, ↓reduceIte] at hreadI ⊢
    exact ⟨5, .ite_true hreadI (by omega) (hwrite 0 (by omega)), by omega⟩
  · simp only [hinside, ↓reduceIte] at hreadI ⊢
    by_cases hwall : i ∈ W.vertexFinset
    · simp only [hwall, ↓reduceIte] at hreadH ⊢
      by_cases hsub : i ∈ S.vertexFinset
      · simp only [hsub, ↓reduceIte] at hreadS ⊢
        exact ⟨9, .ite_false hreadI (.ite_true hreadH (by omega)
          (.ite_true hreadS (by omega) (hwrite 2 (by omega)))), by omega⟩
      · simp only [hsub, ↓reduceIte] at hreadS ⊢
        exact ⟨9, .ite_false hreadI (.ite_true hreadH (by omega)
          (.ite_false hreadS (hwrite 3 hw))), by omega⟩
    · simp only [hwall, ↓reduceIte] at hreadH ⊢
      exact ⟨7, .ite_false hreadI (.ite_false hreadH (hwrite 0 (by omega))), by omega⟩

/-- Allocate the label array and fill it in vertex order. -/
def f92LabelsProg (a_H a_S a_I a_lab r_n r_i : ℕ) : Cmd :=
  .seq (.alloc a_lab (.reg r_n)) (.seq (.assign r_i (.const 0))
    (forUp r_i (.reg r_n) (f92LabelStepProg a_H a_S a_I a_lab r_i)))

/-- Label preparation takes linear time and preserves the input bitsets and all registers
except the cursor. No geometric or path-existence result is needed to prepare labels. -/
theorem f92LabelsProg_exec {w n h hs : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (S : WallOfHeight hs G)
    (a_H a_S a_I a_lab r_n r_i : ℕ)
    (hHL : a_H ≠ a_lab) (hSL : a_S ≠ a_lab) (hIL : a_I ≠ a_lab) (hni : r_n ≠ r_i)
    (hw : 3 < 2 ^ w) (hn : n < 2 ^ w) {s : State}
    (hH : IsBitSet W.vertexFinset a_H s) (hS : IsBitSet S.vertexFinset a_S s)
    (hI : IsBitSet S.insideFinset a_I s) (hrn : s.regs r_n = n) :
    ∃ s' t, Exec w (f92LabelsProg a_H a_S a_I a_lab r_n r_i) s s' t ∧
      t ≤ 6 + 17 * n ∧ s'.arrs a_lab = List.ofFn (f92SearchLabel W S) ∧
      (∀ a : ℕ, a ≠ a_lab → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ r_i → s'.regs q = s.regs q) := by
  let s₁ := s.setArr a_lab (List.replicate n 0)
  have hex₁ : Exec w (.alloc a_lab (.reg r_n)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hrn, hn])
  let s₂ := s₁.setReg r_i 0
  have hex₂ : Exec w (.assign r_i (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  let Inv (i : ℕ) (st : State) : Prop :=
    st.regs r_n = n ∧ st.regs r_i = i ∧
    IsBitSet W.vertexFinset a_H st ∧ IsBitSet S.vertexFinset a_S st ∧
    IsBitSet S.insideFinset a_I st ∧
    ∃ (hlen : (st.arrs a_lab).length = n), ∀ u : Fin n, u.val < i →
      (st.arrs a_lab)[u.val]'(by rw [hlen]; exact u.isLt) = f92SearchLabel W S u
  have hloop : ⦃Inv 0⦄[w] forUp r_i (.reg r_n) (f92LabelStepProg a_H a_S a_I a_lab r_i)
      ⦃Inv n⦄ ≤ fun _ => 3 + n * 16 := by
    apply Triple.forUp_const Inv n 9 (by omega) hn
    · intro i _ st hinv
      exact ⟨hinv.2.1, by simp [Expr.eval, checkWord, hinv.1, hn]⟩
    · intro i hi st ⟨hrn', hri, hH', hS', hI', hlen, hprev⟩
      obtain ⟨t, hex, ht⟩ := f92LabelStepProg_exec W S a_H a_S a_I a_lab r_i st
        ⟨i, hi⟩ hH' hS' hI' hri hlen hw hn
      let st' := st.writeArr a_lab i (f92SearchLabel W S ⟨i, hi⟩)
      refine ⟨st', t, hex, ht, ?_, hri⟩
      refine ⟨by simp [st', State.setReg_regs_ne _ _ hni, hrn'], by simp,
        hH'.of_arr_eq (by simp [st', hHL]), hS'.of_arr_eq (by simp [st', hSL]),
        hI'.of_arr_eq (by simp [st', hIL]), by simp [st', hlen], ?_⟩
      intro u hu
      simp only [State.setReg_arrs, st', State.writeArr_arrs_self]
      by_cases hui : u.val = i
      · have heq : u = ⟨i, hi⟩ := Fin.ext hui
        subst u
        rw [List.getElem_set_self]
      · rw [List.getElem_set_ne (by omega)]
        exact hprev u (by omega)
  have hinit : Inv 0 s₂ := by
    exact ⟨by simp [s₂, s₁, hni, hrn], by simp [s₂],
      hH.of_arr_eq (by simp [s₂, s₁, hHL]), hS.of_arr_eq (by simp [s₂, s₁, hSL]),
      hI.of_arr_eq (by simp [s₂, s₁, hIL]), by simp [s₂, s₁], fun _ hi => by omega⟩
  obtain ⟨s₃, t₃, hex₃, ht₃, _, _, _, _, _, hlen, hvals⟩ := hloop s₂ hinit
  dsimp only at ht₃
  have hex : Exec w (f92LabelsProg a_H a_S a_I a_lab r_n r_i) s s₃
      ((1 + n) + (2 + t₃)) := .seq hex₁ (.seq hex₂ hex₃)
  refine ⟨s₃, _, hex, by omega, ?_, ?_, ?_⟩
  · apply List.ext_getElem
    · simpa using hlen
    · intro i hi hj
      rw [List.getElem_ofFn]
      exact hvals ⟨i, by simpa using hj⟩ (by simpa using hj)
  · intro a ha
    exact hex.arrs_eq_of_not_mem_writtenArrs (by
      simp [f92LabelsProg, f92LabelStepProg, forUp, Cmd.writtenArrs, ha])
  · intro q hq
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simp [f92LabelsProg, f92LabelStepProg, forUp, Cmd.writtenRegs, hq])

end GraphMinor.Compute.Alg92
