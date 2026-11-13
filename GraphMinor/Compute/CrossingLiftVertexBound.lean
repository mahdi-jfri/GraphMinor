module

public import GraphMinor.Compute.CrossingOpsBasic

/-!
# Reading the search vertex bound from recorded vertex lists

The lift interface does not supply the ambient vertex count in a register. For the reverse
replacement search, all recorded vertices lie in the boundary and recorded-component lists.
Scanning their labels and taking one more than their maximum gives a sufficient array size,
no larger than the ambient count. This file computes that bound from memory.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Extend a numerical vertex bound by all labels in a recorded list. -/
def liftVertexBound {N : ℕ} (L : List (Fin N)) (M : ℕ) : ℕ :=
  L.foldl (fun m x => max m (x.val + 1)) M

/-- A list scan never decreases the current vertex bound. -/
theorem liftVertexBound_start_le {N : ℕ} (L : List (Fin N)) (M : ℕ) : M ≤ liftVertexBound L M := by
  induction L generalizing M with
  | nil => exact Nat.le_refl _
  | cons x L ih => exact (Nat.le_max_left _ _).trans (ih (max M (x.val + 1)))

/-- A bound built from labels of `Fin N` remains at most `N` when it starts at most `N`. -/
theorem liftVertexBound_le {N : ℕ} (L : List (Fin N)) {M : ℕ} (hM : M ≤ N) :
    liftVertexBound L M ≤ N := by
  induction L generalizing M with
  | nil => exact hM
  | cons x L ih => exact ih (max_le hM (Nat.succ_le_of_lt x.isLt))

/-- Every recorded vertex has label strictly below the bound computed from its list. -/
theorem liftVertexBound_mem {N : ℕ} {L : List (Fin N)} {x : Fin N} (hx : x ∈ L) (M : ℕ) :
    x.val < liftVertexBound L M := by
  induction L generalizing M with
  | nil => simp at hx
  | cons y L ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · have h := liftVertexBound_start_le L (max M (x.val + 1))
      exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)) h
    · exact ih hx (max M (y.val + 1))

/-- Scan one recorded list and increase `r_bound` when a label does not yet fit below it. -/
def liftGrowVertexBoundProg (src r_bound R : ℕ) : Cmd :=
  .seq (.assign R (.const 0))
    (forUp R (.len src)
      (.seq (.assign (R + 1) (.read src (.reg R)))
        (.ite (.op .le (.reg r_bound) (.reg (R + 1)))
          (.assign r_bound (.op .add (.reg (R + 1)) (.const 1))) .skip)))

private theorem eval_bound_le {w : ℕ} {s : State} {r q : ℕ} {a b : ℕ}
    (hr : s.regs r = a) (hq : s.regs q = b) (ha : a < 2 ^ w) (hb : b < 2 ^ w)
    (hw : 1 < 2 ^ w) :
    (Expr.op .le (.reg r) (.reg q)).eval w s = some (if a ≤ b then 1 else 0) := by
  by_cases h : a ≤ b <;>
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr, hq, ha, hb, h, hw,
      show 0 < 2 ^ w by omega]

/-- Growing the bound from a stored list is linear and changes no array. The hypotheses
supply the initial bound in a lower register, the stored list and the word bound. -/
theorem liftGrowVertexBoundProg_exec {w N : ℕ} (src r_bound R : ℕ) (hbR : r_bound < R)
    (L : List (Fin N)) (M : ℕ) (hM : M ≤ N) (s : State)
    (hsrc : s.arrs src = L.map Fin.val) (hbound : s.regs r_bound = M)
    (hw : N + L.length + 2 < 2 ^ w) :
    ∃ s' t, Exec w (liftGrowVertexBoundProg src r_bound R) s s' t ∧
      t ≤ 20 * (L.length + 1) ∧ s'.regs r_bound = liftVertexBound L M ∧
      (∀ a, s'.arrs a = s.arrs a) ∧
      (∀ q < R, q ≠ r_bound → s'.regs q = s.regs q) := by
  have hw0 : 0 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  let F := fun j => liftVertexBound (L.take j) M
  let I : ℕ → State → Prop := fun j st =>
    st.regs R = j ∧ st.regs r_bound = F j ∧ (∀ a, st.arrs a = s.arrs a) ∧
    (∀ q < R, q ≠ r_bound → st.regs q = s.regs q)
  have hinit : I 0 (s.setReg R 0) := by
    refine ⟨by simp, ?_, fun _ => rfl, ?_⟩
    · simpa [F, liftVertexBound, show r_bound ≠ R by omega] using hbound
    · intro q hq hqb; simp [show q ≠ R by omega]
  obtain ⟨s1, t1, he1, ht1, hI⟩ := forUp_exec' I L.length 10 hw1 (by omega)
    (r_i := R) (hi := .len src)
    (body := .seq (.assign (R + 1) (.read src (.reg R)))
      (.ite (.op .le (.reg r_bound) (.reg (R + 1)))
        (.assign r_bound (.op .add (.reg (R + 1)) (.const 1))) .skip))
    (fun j _ st hI => ⟨hI.1, by
      have he := eval_len (w := w) ((hI.2.2.1 src).trans hsrc) (by simp only [List.length_map]; omega)
      simpa only [List.length_map] using he⟩)
    (fun j hj st hI => by
      obtain ⟨hi, hb, harr, hr⟩ := hI
      have hs : st.arrs src = L.map Fin.val := (harr src).trans hsrc
      have hidx : j < (st.arrs src).length := by rw [hs, List.length_map]; exact hj
      have hval : (st.arrs src)[j]'hidx = L[j].val := by simp only [hs, List.getElem_map]
      have hyw : L[j].val < 2 ^ w := L[j].isLt.trans (by omega)
      have hread : (Expr.read src (.reg R)).eval w st = some L[j].val := by
        rw [← hval]
        exact eval_read (eval_reg hi (by omega)) hidx (by rw [hval]; exact hyw)
      have hFn : F j ≤ N := liftVertexBound_le _ hM
      have hstep : F (j + 1) = max (F j) (L[j].val + 1) := by
        simp only [F, liftVertexBound, List.take_succ_eq_append_getElem hj, List.foldl_append,
          List.foldl_cons, List.foldl_nil]
      let st1 := st.setReg (R + 1) L[j].val
      have hb1 : st1.regs r_bound = F j := by simp [st1, show r_bound ≠ R + 1 by omega, hb]
      have hc := eval_bound_le hb1 (show st1.regs (R + 1) = L[j].val by simp [st1])
        (by omega) hyw hw1
      by_cases hle : F j ≤ L[j].val
      · have hc1 : (Expr.op .le (.reg r_bound) (.reg (R + 1))).eval w st1 = some 1 := by
          simpa only [hle, ↓reduceIte] using hc
        refine ⟨st1.setReg r_bound (L[j].val + 1), 10,
          .seq (.assign hread) (.ite_true hc1 (by omega)
            (.assign (eval_add (eval_reg (by simp) hyw) (eval_const hw1) (by omega)))),
          by omega, ?_, ?_⟩
        · refine ⟨by simp, ?_, harr, ?_⟩
          · rw [State.setReg_regs_ne _ _ (show r_bound ≠ R by omega), State.setReg_regs_self, hstep,
              max_eq_right (by omega)]
          · intro q hq hqb
            simp [show q ≠ R by omega, hqb, st1, show q ≠ R + 1 by omega, hr q hq hqb]
        · simp [show R ≠ r_bound by omega, st1, hi]
      · have hc0 : (Expr.op .le (.reg r_bound) (.reg (R + 1))).eval w st1 = some 0 := by
          simpa only [hle, ↓reduceIte] using hc
        refine ⟨st1, 7, .seq (.assign hread) (.ite_false hc0 (.skip st1)), by omega, ?_, ?_⟩
        · refine ⟨by simp, ?_, harr, ?_⟩
          · rw [State.setReg_regs_ne _ _ (show r_bound ≠ R by omega), hb1, hstep, max_eq_left (by omega)]
          · intro q hq hqb
            simp [show q ≠ R by omega, st1, show q ≠ R + 1 by omega, hr q hq hqb]
        · simp [st1, hi])
    (s.setReg R 0) hinit
  refine ⟨s1, 2 + t1, .seq (.assign (eval_const hw0)) he1, ?_, ?_, hI.2.2.1, hI.2.2.2⟩
  · simp only [Expr.cost, Nat.reduceAdd] at ht1; omega
  · simpa only [F, List.take_length] using hI.2.1

/-- Compute the search bound from the boundary and recorded component, starting at zero. -/
def liftVertexBoundProg (boundary component r_bound R : ℕ) : Cmd :=
  .seq (.assign r_bound (.const 0))
    (.seq (liftGrowVertexBoundProg boundary r_bound R) (liftGrowVertexBoundProg component r_bound R))

/-- The search vertex bound is computed from the two recorded lists and is at most `N`.
All assumptions describe their storage, a lower output register and a word bound. -/
theorem liftVertexBoundProg_exec {w N : ℕ} (boundary component r_bound R : ℕ) (hbR : r_bound < R)
    (B C : List (Fin N)) (s : State)
    (hB : s.arrs boundary = B.map Fin.val) (hC : s.arrs component = C.map Fin.val)
    (hw : N + B.length + C.length + 2 < 2 ^ w) :
    ∃ s' t, Exec w (liftVertexBoundProg boundary component r_bound R) s s' t ∧
      t ≤ 40 * (B.length + C.length + 2) ∧
      s'.regs r_bound = liftVertexBound (B ++ C) 0 ∧
      (∀ a, s'.arrs a = s.arrs a) ∧
      (∀ q < R, q ≠ r_bound → s'.regs q = s.regs q) := by
  let s0 := s.setReg r_bound 0
  obtain ⟨s1, t1, he1, ht1, ho1, ha1, hr1⟩ := liftGrowVertexBoundProg_exec (w := w)
    boundary r_bound R hbR B 0 (Nat.zero_le _) s0 hB (by simp [s0]) (by omega)
  obtain ⟨s2, t2, he2, ht2, ho2, ha2, hr2⟩ := liftGrowVertexBoundProg_exec (w := w)
    component r_bound R hbR C (liftVertexBound B 0) (liftVertexBound_le B (Nat.zero_le _))
    s1 ((ha1 component).trans hC) ho1 (by omega)
  refine ⟨s2, 2 + (t1 + t2), .seq (.assign (eval_const (by omega))) (.seq he1 he2),
    by omega, ?_, fun a => (ha2 a).trans (ha1 a), ?_⟩
  · simpa only [liftVertexBound, List.foldl_append] using ho2
  · intro q hq hqb
    rw [hr2 q hq hqb, hr1 q hq hqb]
    simp [s0, hqb]

end GraphMinor.Compute.Crossing
