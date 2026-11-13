module

public import GraphMinor.Compute.CrossingLiftCuts
public import GraphMinor.Compute.CrossingLiftCutVisit
public import GraphMinor.Compute.CrossingLiftFind
import GraphMinor.Compute.CrossingLoopCand

/-!
# Scanning the first and last boundary visits on the RAM

Lemma 1 replaces the entire path segment between the first and last visits to the separator.
The program scans path vertices and tests each against the recorded boundary list. The first
index is saved once, and the index after the last visit is updated on every visit. Since the
boundary has at most three vertices, all membership scans together take linear time.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Compute the two replacement splice cuts, using scratch registers starting at `R`. -/
def liftCutScanProg (src boundary r_first r_after R : ℕ) : Cmd :=
  .seq (.assign r_first (.len src))
    (.seq (.assign r_after (.const 0))
      (.seq (.assign R (.const 0))
        (forUp R (.len src)
          (.seq (.assign (R + 1) (.read src (.reg R)))
            (.seq (liftFindVertexProg boundary (R + 1) (R + 2) (R + 3))
              (.ite (.op .lt (.reg (R + 2)) (.len boundary))
                (liftCutVisitProg src r_first r_after R) .skip))))))

/-- The cut scan computes exactly the first boundary index and the index after the last visit.
Its only assumptions are the stored lists, a duplicate-free boundary of size at most three,
distinct lower output registers and a word bound. It changes no array. -/
theorem liftCutScanProg_exec {w N : ℕ} (src boundary r_first r_after R : ℕ)
    (hfR : r_first < R) (haR : r_after < R) (hfa : r_first ≠ r_after)
    (L B : List (Fin N)) (hB : B.Nodup) (hsmall : B.length ≤ 3) (s : State)
    (hsrc : s.arrs src = L.map Fin.val) (hbd : s.arrs boundary = B.map Fin.val)
    (hw : 16 * (N + L.length + B.length + 5) < 2 ^ w) :
    ∃ s' t, Exec w (liftCutScanProg src boundary r_first r_after R) s s' t ∧
      t ≤ 100 * (L.length + 1) ∧
      s'.regs r_first = liftFirstBoundaryIndex B L ∧
      s'.regs r_after = liftAfterLastBoundaryIndex B L ∧
      (∀ c, s'.arrs c = s.arrs c) ∧
      (∀ q < R, q ≠ r_first → q ≠ r_after → s'.regs q = s.regs q) := by
  have hw0 : 0 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hnw : N < 2 ^ w := by omega
  let f := liftFirstBoundaryIndex B L
  have hflen : f ≤ L.length := (liftBoundaryIndices_le_length B L).1
  let budget := 16 * (B.length + 1) + 15
  let s0 := s.setReg r_first L.length
  let s1 := s0.setReg r_after 0
  let s2 := s1.setReg R 0
  let I : ℕ → State → Prop := fun j st =>
    st.regs R = j ∧ st.regs r_first = (if f < j then f else L.length) ∧
    st.regs r_after = liftAfterLastBoundaryIndex B (L.take j) ∧
    (∀ c, st.arrs c = s.arrs c) ∧
    (∀ q < R, q ≠ r_first → q ≠ r_after → st.regs q = s.regs q)
  have hinit : I 0 s2 := by
    refine ⟨by simp [s2], ?_, ?_, fun _ => rfl, ?_⟩
    · simp [s2, s1, s0, show r_first ≠ R by omega, hfa]
    · simp [s2, s1, show r_after ≠ R by omega, liftAfterLastBoundaryIndex]
    · intro q hq hqf hqa; simp [s2, s1, s0, show q ≠ R by omega, hqf, hqa]
  obtain ⟨s3, t3, he3, ht3, hI⟩ := forUp_exec' I L.length budget hw1 (by omega)
    (r_i := R) (hi := .len src)
    (body := .seq (.assign (R + 1) (.read src (.reg R)))
      (.seq (liftFindVertexProg boundary (R + 1) (R + 2) (R + 3))
        (.ite (.op .lt (.reg (R + 2)) (.len boundary)) (liftCutVisitProg src r_first r_after R) .skip)))
    (fun j _ st hI => ⟨hI.1, by
      have he := eval_len (w := w) ((hI.2.2.2.1 src).trans hsrc) (by simp only [List.length_map]; omega)
      simpa only [List.length_map] using he⟩)
    (fun j hj st hI => by
      obtain ⟨hi, hf, haf, harr, hr⟩ := hI
      have hs : st.arrs src = L.map Fin.val := (harr src).trans hsrc
      have hbound : j < (st.arrs src).length := by rw [hs, List.length_map]; exact hj
      have hval : (st.arrs src)[j]'hbound = L[j].val := by simp only [hs, List.getElem_map]
      have hread : (Expr.read src (.reg R)).eval w st = some L[j].val := by
        rw [← hval]
        exact eval_read (eval_reg hi (by omega)) hbound (by rw [hval]; exact L[j].isLt.trans hnw)
      let st1 := st.setReg (R + 1) L[j].val
      obtain ⟨st2, t2, he2, ht2, hp2, ha2, hr2⟩ := liftFindVertexProg_exec
        boundary (R + 1) (R + 2) (R + 3) (by omega) (by omega) (by omega)
        (B.map Fin.val) L[j].val st1 ((harr boundary).trans hbd) (by simp [st1])
        (hB.map Fin.val_injective)
        (by intro x hx; obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx; exact y.isLt.trans hnw)
        (L[j].isLt.trans hnw) (by simp only [List.length_map]; omega)
      have hcounter : st2.regs R = j := by
        rw [hr2 R (by omega) (by omega)]; simp [st1, hi]
      have hfirst : st2.regs r_first = (if f < j then f else L.length) := by
        rw [hr2 r_first (by omega) (by omega)]
        simp [st1, show r_first ≠ R + 1 by omega, hf]
      have hafter : st2.regs r_after = liftAfterLastBoundaryIndex B (L.take j) := by
        rw [hr2 r_after (by omega) (by omega)]
        simp [st1, show r_after ≠ R + 1 by omega, haf]
      have hpos : st2.regs (R + 2) = B.idxOf L[j] := by simpa only [idxOf_map_val] using hp2
      have hcond := eval_lt (eval_reg hpos (Nat.lt_of_le_of_lt List.idxOf_le_length (by omega)))
        (eval_len ((ha2 boundary).trans ((harr boundary).trans hbd)) (by simp only [List.length_map]; omega)) hw1
      have hstep := liftAfterLastBoundaryIndex_take_step B L hj
      by_cases hm : L[j] ∈ B
      · have hlt : B.idxOf L[j] < B.length := List.idxOf_lt_length_iff.mpr hm
        have hc : (Expr.op .lt (.reg (R + 2)) (.len boundary)).eval w st2 = some 1 := by
          simpa only [List.length_map, hlt, ↓reduceIte] using hcond
        have hfj : f ≤ j := liftFirstBoundaryIndex_le_of_mem B L hj hm
        obtain ⟨st3, tvisit, hevisit, htvisit, hf3, ha3, havisit, hrvisit⟩ := liftCutVisitProg_exec (w := w)
          src r_first r_after R (by omega) hfa f j L.length st2 hfj hj
          (by rw [ha2 src]; change (st.arrs src).length = L.length; rw [hs, List.length_map]) hcounter hfirst (by omega)
        refine ⟨st3, 3 + (t2 + (3 + tvisit)),
          .seq (.assign hread) (.seq he2 (.ite_true hc (by omega) hevisit)),
          by simp only [List.length_map] at ht2; dsimp [budget]; omega, ?_, ?_⟩
        · refine ⟨by simp, ?_, ?_, ?_, ?_⟩
          · simpa only [State.setReg_regs_ne _ _ (show r_first ≠ R by omega),
              show f < j + 1 by omega, ↓reduceIte] using hf3
          · simpa only [State.setReg_regs_ne _ _ (show r_after ≠ R by omega), hstep, hm, ↓reduceIte] using ha3
          · intro c; exact (havisit c).trans ((ha2 c).trans (harr c))
          · intro q hq hqf hqa
            rw [State.setReg_regs_ne _ _ (show q ≠ R by omega), hrvisit q hqf hqa,
              hr2 q (by omega) (by omega)]
            simp only [st1, State.setReg_regs_ne _ _ (show q ≠ R + 1 by omega)]
            exact hr q hq hqf hqa
        · exact (hrvisit R (by omega) (by omega)).trans hcounter
      · have hlt : ¬ B.idxOf L[j] < B.length := by rw [List.idxOf_eq_length hm]; omega
        have hc : (Expr.op .lt (.reg (R + 2)) (.len boundary)).eval w st2 = some 0 := by
          simpa only [List.length_map, hlt, ↓reduceIte] using hcond
        have hfj : f ≠ j := liftFirstBoundaryIndex_ne_of_not_mem B L hj hm
        refine ⟨st2, 3 + (t2 + 4), .seq (.assign hread) (.seq he2 (.ite_false hc (.skip st2))),
          by simp only [List.length_map] at ht2; dsimp [budget]; omega, ?_, hcounter⟩
        refine ⟨by simp, ?_, ?_, ?_, ?_⟩
        · rw [State.setReg_regs_ne _ _ (show r_first ≠ R by omega), hfirst]
          split_ifs <;> omega
        · simpa only [State.setReg_regs_ne _ _ (show r_after ≠ R by omega), hstep, hm, ↓reduceIte] using hafter
        · intro c; exact (ha2 c).trans (harr c)
        · intro q hq hqf hqa
          rw [State.setReg_regs_ne _ _ (show q ≠ R by omega), hr2 q (by omega) (by omega)]
          simp only [st1, State.setReg_regs_ne _ _ (show q ≠ R + 1 by omega)]
          exact hr q hq hqf hqa)
    s2 hinit
  refine ⟨s3, 2 + (2 + (2 + t3)),
    .seq (.assign (by
      have he := eval_len (w := w) hsrc (by simp only [List.length_map]; omega)
      simpa only [List.length_map] using he))
      (.seq (.assign (eval_const hw0)) (.seq (.assign (eval_const hw0)) he3)),
    ?_, ?_, ?_, hI.2.2.2.1, hI.2.2.2.2⟩
  · simp only [Expr.cost, Nat.reduceAdd] at ht3
    have hb : budget ≤ 79 := by dsimp [budget]; omega
    have hm := Nat.mul_le_mul_left L.length (show 7 + budget ≤ 86 by omega)
    omega
  · rw [hI.2.1]; split_ifs <;> omega
  · simpa only [List.take_length] using hI.2.2.1

end GraphMinor.Compute.Crossing
