module

public import GraphMinor.Compute.CrossingLiftEdges
public import GraphMinor.Compute.CrossingLiftEdgeBuffer
import GraphMinor.Compute.TwoPathsFrameEdges

/-!
# Filtering the recorded edges into a parser buffer

The record lists both orientations. A single scan retains increasing pairs and writes them
into a buffer large enough for all pairs. Unused words remain zero and are passed to the
existing parser as its permitted trailing data.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- The two endpoint reads and conditional append for one recorded pair. -/
def liftEdgeFilterBody (src dst R : ℕ) : Cmd :=
  .seq (.assign (R + 3) (.read src (.op .mul (.const 2) (.reg R))))
    (.seq (.assign (R + 4) (.read src (.op .add (.op .mul (.const 2) (.reg R)) (.const 1))))
      (.ite (.op .lt (.reg (R + 3)) (.reg (R + 4)))
        (liftEmitPairProg dst (R + 1) (R + 3) (R + 4)) .skip))

/-- Allocate an upper bound for the retained pairs and scan the flat record once. -/
def liftEdgeFilterScanProg (src dst R : ℕ) : Cmd :=
  .seq (.alloc dst (.op .add (.const 2) (.len src)))
    (.seq (.assign (R + 2) (.op .div (.len src) (.const 2)))
      (.seq (.assign (R + 1) (.const 2))
        (.seq (.assign R (.const 0))
          (forUp R (.reg (R + 2)) (liftEdgeFilterBody src dst R)))))

private theorem flat_length {N : ℕ} (E : List (Fin N × Fin N)) :
    (E.flatMap encPair).length = 2 * E.length := TwoPaths.length_pairsList E

private theorem kept_step {N : ℕ} (E : List (Fin N × Fin N)) (j : ℕ) (hj : j < E.length) :
    liftSearchEdges (E.take (j + 1)) =
      if E[j].1.val < E[j].2.val then liftSearchEdges (E.take j) ++ [E[j]]
      else liftSearchEdges (E.take j) := by
  simp only [liftSearchEdges, List.take_succ_eq_append_getElem hj, List.filter_append,
    List.filter_cons, List.filter_nil, decide_eq_true_eq]
  split <;> simp_all

/-- The edge scan writes exactly the retained pairs followed by unused zero words.
It assumes a flat recorded list, distinct source and buffer arrays, and a word bound.
The cursor is returned just past the retained pairs, for writing the parser header. -/
theorem liftEdgeFilterScanProg_exec {w N : ℕ} (src dst R : ℕ) (hsd : src ≠ dst)
    (E : List (Fin N × Fin N)) (s : State)
    (hsrc : s.arrs src = E.flatMap encPair)
    (hw : N + 8 * E.length + 16 < 2 ^ w) :
    ∃ s' t, Exec w (liftEdgeFilterScanProg src dst R) s s' t ∧
      t ≤ 100 * E.length + 30 ∧
      s'.arrs dst = [0, 0] ++ (liftSearchEdges E).flatMap encPair ++
        List.replicate (2 * (E.length - (liftSearchEdges E).length)) 0 ∧
      s'.regs (R + 1) = 2 + 2 * (liftSearchEdges E).length ∧
      (∀ a, a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ q < R, s'.regs q = s.regs q) := by
  have hw0 : 0 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  let s0 := s.setArr dst (List.replicate (2 + 2 * E.length) 0)
  let s1 := s0.setReg (R + 2) E.length
  let s2 := s1.setReg (R + 1) 2
  let s3 := s2.setReg R 0
  have hs0 : s0.arrs src = E.flatMap encPair := by simp [s0, hsd, hsrc]
  have hecount : (Expr.op .div (.len src) (.const 2)).eval w s0 = some E.length := by
    have he := eval_len (w := w) hs0 (by rw [flat_length]; omega)
    rw [Expr.eval, he, eval_const hw2, flat_length]
    simp [BinOp.eval, BinOp.raw, checkWord, show E.length < 2 ^ w by omega]
  let F := fun j => liftSearchEdges (E.take j)
  let I : ℕ → State → Prop := fun j st =>
    st.regs R = j ∧ st.regs (R + 2) = E.length ∧
    st.regs (R + 1) = 2 + 2 * (F j).length ∧
    st.arrs src = E.flatMap encPair ∧
    st.arrs dst = [0, 0] ++ (F j).flatMap encPair ++
      List.replicate (2 * (E.length - (F j).length)) 0
  have hf0 : F 0 = [] := by simp [F, liftSearchEdges]
  have hinit : I 0 s3 := by
    refine ⟨by simp [s3], by simp [s3, s2, s1], ?_, hs0, ?_⟩
    · simp [s3, s2, F, liftSearchEdges]
    · simp only [hf0, List.flatMap_nil, List.append_nil, List.length_nil, Nat.sub_zero]
      simp only [s3, s2, s1, State.setReg_arrs, s0, State.setArr_arrs_self]
      rw [List.replicate_add]
      rfl
  obtain ⟨s4, t4, he4, ht4, hI⟩ := forUp_exec' I E.length 40 hw1 (by omega)
    (r_i := R) (hi := .reg (R + 2)) (body := liftEdgeFilterBody src dst R)
    (fun j _ st hi => ⟨hi.1, eval_reg hi.2.1 (by omega)⟩)
    (fun j hj st hi => by
      obtain ⟨hr, hn, hp, hs, hd⟩ := hi
      have hf : (F j).length ≤ j := (liftSearchEdges_length _).trans (by simp)
      have hfields := TwoPaths.pairsList_getElem? E j
      change (E.flatMap encPair)[2 * j]? = (E[j]?).map (fun p => p.1.val) ∧
        (E.flatMap encPair)[2 * j + 1]? = (E[j]?).map (fun p => p.2.val) at hfields
      have hfa : (st.arrs src)[2 * j]? = some E[j].1.val := by
        simpa only [hs, TwoPaths.pairsList, List.getElem?_eq_getElem hj, Option.map_some] using hfields.1
      have hfb : (st.arrs src)[2 * j + 1]? = some E[j].2.val := by
        simpa only [hs, TwoPaths.pairsList, List.getElem?_eq_getElem hj, Option.map_some] using hfields.2
      have hreadA : (Expr.read src (.op .mul (.const 2) (.reg R))).eval w st = some E[j].1.val := by
        obtain ⟨hb, hv⟩ := List.getElem?_eq_some_iff.mp hfa
        rw [← hv]
        exact eval_read (eval_mul (eval_const hw2) (eval_reg hr (by omega)) (by omega)) hb
          (by rw [hv]; exact E[j].1.isLt.trans (by omega))
      let st1 := st.setReg (R + 3) E[j].1.val
      have hreadB : (Expr.read src (.op .add (.op .mul (.const 2) (.reg R)) (.const 1))).eval w st1 =
          some E[j].2.val := by
        obtain ⟨hb, hv⟩ := List.getElem?_eq_some_iff.mp hfb
        rw [← hv]
        exact eval_read (s := st1) (eval_add (eval_mul (eval_const hw2)
          (eval_reg (by simpa [st1] using hr) (by omega)) (by omega))
          (eval_const hw1) (by omega)) hb
          (by simpa only [st1, State.setReg_arrs, hv] using E[j].2.isLt.trans (by omega : N < 2 ^ w))
      let st2 := st1.setReg (R + 4) E[j].2.val
      have hp2 : st2.regs (R + 1) = 2 + 2 * (F j).length := by simp [st2, st1, hp]
      have ha2 : st2.regs (R + 3) = E[j].1.val := by simp [st2, st1]
      have hb2 : st2.regs (R + 4) = E[j].2.val := by simp [st2]
      have hcond : (Expr.op .lt (.reg (R + 3)) (.reg (R + 4))).eval w st2 =
          some (if E[j].1.val < E[j].2.val then 1 else 0) := by
        by_cases hh : E[j].1.val < E[j].2.val <;>
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, ha2, hb2, hh,
            E[j].1.isLt.trans (by omega : N < 2 ^ w),
            E[j].2.isLt.trans (by omega : N < 2 ^ w), hw0, hw1]
      have hstep := kept_step E j hj
      by_cases hkeep : E[j].1.val < E[j].2.val
      · let A := [0, 0] ++ (F j).flatMap encPair
        let C := List.replicate (2 * (E.length - ((F j).length + 1))) 0
        have hpad : st2.arrs dst = A ++ [0, 0] ++ C := by
          change st.arrs dst = _
          rw [hd]
          have hz : 2 * (E.length - (F j).length) = 2 + 2 * (E.length - ((F j).length + 1)) := by omega
          rw [hz, List.replicate_add]
          simp only [A, C, List.append_assoc]; rfl
        obtain ⟨st3, he3, ho3, hp3, ha3, hr3⟩ := liftEmitPairProg_exec (w := w) dst (R + 1) (R + 3) (R + 4)
          A C E[j].1.val E[j].2.val st2 hpad
          (by simpa only [A, List.length_append, List.length_cons, List.length_nil, flat_length] using hp2)
          ha2 hb2 (by simp only [A, List.length_append, List.length_cons, List.length_nil, flat_length]; omega)
          (E[j].1.isLt.trans (by omega)) (E[j].2.isLt.trans (by omega))
        refine ⟨st3, 27, .seq (.assign hreadA) (.seq (.assign hreadB)
          (.ite_true (by simpa only [hkeep, ↓reduceIte] using hcond) (by omega) he3)), by omega, ?_, ?_⟩
        · refine ⟨by simp, ?_, ?_, ?_, ?_⟩
          · simp [hr3 (R + 2) (by omega), st2, st1, hn]
          · simpa only [State.setReg_regs_ne _ _ (show R + 1 ≠ R by omega), F, hstep, hkeep, ↓reduceIte, List.length_append, List.length_cons,
              List.length_nil, Nat.zero_add, Nat.reduceAdd, A, flat_length, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using hp3
          · exact (ha3 _ hsd).trans hs
          · simpa only [State.setReg_arrs, F, hstep, hkeep, ↓reduceIte, List.flatMap_append, List.flatMap_cons,
              List.flatMap_nil, encPair, List.length_append, List.length_cons, List.length_nil,
              List.append_nil, Nat.reduceAdd, A, C, List.append_assoc] using ho3
        · simp [hr3 R (by omega), st2, st1, hr]
      · refine ⟨st2, 16, .seq (.assign hreadA) (.seq (.assign hreadB)
          (.ite_false (by simpa only [hkeep, ↓reduceIte] using hcond) (.skip st2))), by omega, ?_, ?_⟩
        · refine ⟨by simp, by simp [st2, st1, hn], ?_, hs, ?_⟩
          · simpa only [State.setReg_regs_ne _ _ (show R + 1 ≠ R by omega), F, hstep, hkeep, ↓reduceIte] using hp2
          · simpa only [State.setReg_arrs, st2, st1, F, hstep, hkeep, ↓reduceIte] using hd
        · simp [st2, st1, hr])
    s3 hinit
  have healloc : Exec w (.alloc dst (.op .add (.const 2) (.len src))) s s0 (3 + (2 + 2 * E.length)) :=
    .alloc (by
      have he := eval_add (eval_const hw2) (eval_len (w := w) hsrc (by rw [flat_length]; omega)) (by rw [flat_length]; omega)
      simpa only [flat_length] using he)
  have heall : Exec w (liftEdgeFilterScanProg src dst R) s s4
      ((3 + (2 + 2 * E.length)) + (4 + (2 + (2 + t4)))) :=
    .seq healloc (.seq (.assign hecount) (.seq (.assign (eval_const hw2)) (.seq (.assign (eval_const hw0)) he4)))
  refine ⟨s4, _, heall, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Expr.cost] at ht4; omega
  · simpa only [F, List.take_length] using hI.2.2.2.2
  · simpa only [F, List.take_length] using hI.2.2.1
  · intro a ha
    exact heall.arrs_eq_of_not_mem_writtenArrs
      (by simp [liftEdgeFilterScanProg, liftEdgeFilterBody, liftEmitPairProg, forUp, Cmd.writtenArrs, ha])
  · intro q hq
    exact heall.regs_eq_of_not_mem_writtenRegs
      (by simp [liftEdgeFilterScanProg, liftEdgeFilterBody, liftEmitPairProg, forUp, Cmd.writtenRegs,
        show q ≠ R by omega, show q ≠ R + 1 by omega, show q ≠ R + 2 by omega,
        show q ≠ R + 3 by omega, show q ≠ R + 4 by omega])

end GraphMinor.Compute.Crossing
