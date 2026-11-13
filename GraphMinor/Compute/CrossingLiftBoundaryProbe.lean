module

public import GraphMinor.Compute.CrossingLiftPairTest
public import GraphMinor.Compute.CrossingLiftFind
import GraphMinor.Compute.CrossingLoopCand

/-!
# Testing the path edge after one boundary vertex

A replacement can add only boundary-to-boundary edges. This routine locates one boundary
vertex on a returned path. If it has a following vertex on the boundary, it tests their
ordered pair in the recorded old edges. A missing pair is precisely a new clique edge.
The caller repeats this routine for the at most three boundary vertices.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- The new-edge flag for the edge following boundary vertex `a` on the path. -/
def liftBoundaryAfterFlag {N : ℕ} (B : List (Fin N)) (E : List (Fin N × Fin N))
    (L : List (Fin N)) (a : Fin N) : ℕ :=
  if h : L.idxOf a + 1 < L.length then
    if L[L.idxOf a + 1] ∈ B ∧ (a, L[L.idxOf a + 1]) ∉ E then 1 else 0
  else 0

/-- Probe one boundary vertex in `r_a`, returning a new-edge flag in `r_bad`.
Its path position is left in `R+2`. Registers starting at `R` are scratch. -/
def liftBoundaryProbeProg (src boundary edges r_a r_bad R : ℕ) : Cmd :=
  .seq (.assign r_bad (.const 0))
    (.seq (liftFindVertexProg src r_a (R + 2) (R + 1))
      (.ite (.op .lt (.op .add (.reg (R + 2)) (.const 1)) (.len src))
        (.seq (.assign (R + 3) (.read src (.op .add (.reg (R + 2)) (.const 1))))
          (.seq (liftFindVertexProg boundary (R + 3) (R + 4) (R + 1))
            (.ite (.op .lt (.reg (R + 4)) (.len boundary))
              (.seq (liftPairTestProg edges r_a (R + 3) (R + 5) (R + 8))
                (.ite (.reg (R + 5)) .skip (.assign r_bad (.const 1)))) .skip))) .skip))

/-- The boundary probe costs linear time in the path and the recorded lists. Its hypotheses
are duplicate-free path/boundary lists, stored arrays and target, register separation, and
word bounds. It changes no array and preserves all other lower registers. -/
theorem liftBoundaryProbeProg_exec {w N : ℕ}
    (src boundary edges r_a r_bad R : ℕ) (haR : r_a < R) (hbR : r_bad < R) (hab : r_a ≠ r_bad)
    (L B : List (Fin N)) (E : List (Fin N × Fin N)) (a : Fin N)
    (hL : L.Nodup) (hB : B.Nodup) (s : State)
    (hsrc : s.arrs src = L.map Fin.val) (hbd : s.arrs boundary = B.map Fin.val)
    (hedges : s.arrs edges = E.flatMap encPair) (ha : s.regs r_a = a.val)
    (hw : 16 * (N + L.length + B.length + E.length + 5) < 2 ^ w) :
    ∃ s' t, Exec w (liftBoundaryProbeProg src boundary edges r_a r_bad R) s s' t ∧
      t ≤ 100 * (L.length + B.length + E.length + 1) + 100 ∧
      s'.regs r_bad = liftBoundaryAfterFlag B E L a ∧ s'.regs (R + 2) = L.idxOf a ∧
      (∀ c, s'.arrs c = s.arrs c) ∧
      (∀ q < R, q ≠ r_bad → s'.regs q = s.regs q) := by
  have hw0 : 0 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hnw : N < 2 ^ w := by omega
  have hmapw : ∀ xs : List (Fin N), ∀ x ∈ xs.map Fin.val, x < 2 ^ w := by
    intro xs x hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    exact y.isLt.trans hnw
  let s0 := s.setReg r_bad 0
  obtain ⟨s1, t1, he1, ht1, hp1, ha1, hr1⟩ := liftFindVertexProg_exec
    src r_a (R + 2) (R + 1) (by omega) (by omega) (by omega)
    (L.map Fin.val) a.val s0 hsrc (by simp [s0, hab, ha])
    (hL.map Fin.val_injective) (hmapw L) (a.isLt.trans hnw)
    (by simp only [List.length_map]; omega)
  have hpos1 : s1.regs (R + 2) = L.idxOf a := by simpa only [idxOf_map_val] using hp1
  have hbad1 : s1.regs r_bad = 0 := by
    rw [hr1 r_bad (by omega) (by omega)]; simp [s0]
  have ha1val : s1.regs r_a = a.val := by
    rw [hr1 r_a (by omega) (by omega)]; simp [s0, hab, ha]
  have hsrc1 : s1.arrs src = L.map Fin.val := (ha1 src).trans hsrc
  have hcond := eval_lt (eval_add (eval_reg hpos1
    (Nat.lt_of_le_of_lt List.idxOf_le_length (by omega))) (eval_const hw1) (by
      have hh : L.idxOf a ≤ L.length := List.idxOf_le_length; omega))
    (eval_len hsrc1 (by simp only [List.length_map]; omega)) hw1
  by_cases hnext : L.idxOf a + 1 < L.length
  · have hc1 : (Expr.op .lt (.op .add (.reg (R + 2)) (.const 1)) (.len src)).eval w s1 = some 1 := by
      simpa only [List.length_map, hnext, ↓reduceIte] using hcond
    let b := L[L.idxOf a + 1]
    have hbw : b.val < 2 ^ w := b.isLt.trans hnw
    have hread : (Expr.read src (.op .add (.reg (R + 2)) (.const 1))).eval w s1 = some b.val := by
      have hbound : L.idxOf a + 1 < (s1.arrs src).length := by rw [hsrc1, List.length_map]; exact hnext
      have hv : (s1.arrs src)[L.idxOf a + 1]'hbound = b.val := by simp only [hsrc1, List.getElem_map]; rfl
      rw [← hv]
      exact eval_read (eval_add (eval_reg hpos1 (by omega)) (eval_const hw1) (by omega)) hbound
        (by rw [hv]; exact hbw)
    let s2 := s1.setReg (R + 3) b.val
    obtain ⟨s3, t3, he3, ht3, hp3, ha3, hr3⟩ := liftFindVertexProg_exec
      boundary (R + 3) (R + 4) (R + 1) (by omega) (by omega) (by omega)
      (B.map Fin.val) b.val s2 ((ha1 boundary).trans hbd) (by simp [s2])
      (hB.map Fin.val_injective) (hmapw B) hbw (by simp only [List.length_map]; omega)
    have hpos3 : s3.regs (R + 2) = L.idxOf a := by
      rw [hr3 (R + 2) (by omega) (by omega)]; simp [s2, hpos1]
    have hbad3 : s3.regs r_bad = 0 := by
      rw [hr3 r_bad (by omega) (by omega)]; simp [s2, show r_bad ≠ R + 3 by omega, hbad1]
    have ha3val : s3.regs r_a = a.val := by
      rw [hr3 r_a (by omega) (by omega)]; simp [s2, show r_a ≠ R + 3 by omega, ha1val]
    have hb3val : s3.regs (R + 3) = b.val := by
      rw [hr3 (R + 3) (by omega) (by omega)]; simp [s2]
    have hp3fin : s3.regs (R + 4) = B.idxOf b := by simpa only [idxOf_map_val] using hp3
    have hcb := eval_lt (eval_reg hp3fin (Nat.lt_of_le_of_lt List.idxOf_le_length (by omega)))
      (eval_len ((ha3 boundary).trans ((ha1 boundary).trans hbd)) (by simp only [List.length_map]; omega)) hw1
    by_cases hbm : b ∈ B
    · have hlt : B.idxOf b < B.length := List.idxOf_lt_length_iff.mpr hbm
      have hcb1 : (Expr.op .lt (.reg (R + 4)) (.len boundary)).eval w s3 = some 1 := by
        simpa only [List.length_map, hlt, ↓reduceIte] using hcb
      obtain ⟨s4, t4, he4, ht4, ho4, ha4, hr4⟩ := liftPairTestProg_exec (w := w)
        edges r_a (R + 3) (R + 5) (R + 8) (by omega) (by omega) (by omega) (by omega) (by omega)
        E a b s3 ((ha3 edges).trans ((ha1 edges).trans hedges)) ha3val hb3val (by omega)
      have hpos4 : s4.regs (R + 2) = L.idxOf a := (hr4 _ (by omega) (by omega)).trans hpos3
      have hbad4 : s4.regs r_bad = 0 := (hr4 _ (by omega) (by omega)).trans hbad3
      by_cases hem : (a, b) ∈ E
      · have hf1 : (Expr.reg (R + 5)).eval w s4 = some 1 :=
          eval_reg (by simpa only [hem, ↓reduceIte] using ho4) hw1
        refine ⟨s4, 2 + (t1 + (5 + (5 + (t3 + (3 + (t4 + 2)))))),
          .seq (.assign (eval_const hw0)) (.seq he1 (.ite_true hc1 (by omega)
            (.seq (.assign hread) (.seq he3 (.ite_true hcb1 (by omega)
              (.seq he4 (.ite_true hf1 (by omega) (.skip s4)))))))), ?_, ?_, hpos4, ?_, ?_⟩
        · simp only [List.length_map] at ht1 ht3; omega
        · simp only [liftBoundaryAfterFlag, hnext, ↓reduceDIte]
          change s4.regs r_bad = (if b ∈ B ∧ (a, b) ∉ E then 1 else 0)
          simpa only [hem, not_true_eq_false, and_false, ↓reduceIte] using hbad4
        · intro c; exact (ha4 c).trans ((ha3 c).trans (ha1 c))
        · intro q hq hqb
          rw [hr4 q (by omega) (by omega), hr3 q (by omega) (by omega)]
          simp only [s2, State.setReg_regs_ne _ _ (show q ≠ R + 3 by omega)]
          rw [hr1 q (by omega) (by omega)]; simp [s0, hqb]
      · have hf0 : (Expr.reg (R + 5)).eval w s4 = some 0 :=
          eval_reg (by simpa only [hem, ↓reduceIte] using ho4) hw0
        refine ⟨s4.setReg r_bad 1, 2 + (t1 + (5 + (5 + (t3 + (3 + (t4 + 3)))))),
          .seq (.assign (eval_const hw0)) (.seq he1 (.ite_true hc1 (by omega)
            (.seq (.assign hread) (.seq he3 (.ite_true hcb1 (by omega)
              (.seq he4 (.ite_false hf0 (.assign (eval_const hw1))))))))), ?_, ?_, ?_, ?_, ?_⟩
        · simp only [List.length_map] at ht1 ht3; omega
        · simp only [State.setReg_regs_self, liftBoundaryAfterFlag, hnext, ↓reduceDIte]
          change 1 = (if b ∈ B ∧ (a, b) ∉ E then 1 else 0)
          simp [hbm, hem]
        · simp [show R + 2 ≠ r_bad by omega, hpos4]
        · intro c; exact (ha4 c).trans ((ha3 c).trans (ha1 c))
        · intro q hq hqb
          rw [State.setReg_regs_ne _ _ hqb, hr4 q (by omega) (by omega), hr3 q (by omega) (by omega)]
          simp only [s2, State.setReg_regs_ne _ _ (show q ≠ R + 3 by omega)]
          rw [hr1 q (by omega) (by omega)]; simp [s0, hqb]
    · have hlt : ¬ B.idxOf b < B.length := by rw [List.idxOf_eq_length hbm]; omega
      have hcb0 : (Expr.op .lt (.reg (R + 4)) (.len boundary)).eval w s3 = some 0 := by
        simpa only [List.length_map, hlt, ↓reduceIte] using hcb
      refine ⟨s3, 2 + (t1 + (5 + (5 + (t3 + 4)))),
        .seq (.assign (eval_const hw0)) (.seq he1 (.ite_true hc1 (by omega)
          (.seq (.assign hread) (.seq he3 (.ite_false hcb0 (.skip s3)))))), ?_, ?_, hpos3, ?_, ?_⟩
      · simp only [List.length_map] at ht1 ht3; omega
      · simp only [liftBoundaryAfterFlag, hnext, ↓reduceDIte]
        change s3.regs r_bad = (if b ∈ B ∧ (a, b) ∉ E then 1 else 0)
        simpa only [hbm, false_and, ↓reduceIte] using hbad3
      · intro c; exact (ha3 c).trans (ha1 c)
      · intro q hq hqb
        rw [hr3 q (by omega) (by omega)]
        simp only [s2, State.setReg_regs_ne _ _ (show q ≠ R + 3 by omega)]
        rw [hr1 q (by omega) (by omega)]; simp [s0, hqb]
  · have hc0 : (Expr.op .lt (.op .add (.reg (R + 2)) (.const 1)) (.len src)).eval w s1 = some 0 := by
      simpa only [List.length_map, hnext, ↓reduceIte] using hcond
    refine ⟨s1, 2 + (t1 + 6), .seq (.assign (eval_const hw0)) (.seq he1 (.ite_false hc0 (.skip s1))),
      ?_, ?_, hpos1, ha1, ?_⟩
    · simp only [List.length_map] at ht1; omega
    · simpa only [liftBoundaryAfterFlag, hnext, ↓reduceDIte] using hbad1
    · intro q hq hqb; rw [hr1 q (by omega) (by omega)]; simp [s0, hqb]

end GraphMinor.Compute.Crossing
