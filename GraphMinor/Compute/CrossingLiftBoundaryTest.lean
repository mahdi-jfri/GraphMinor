module

public import GraphMinor.Compute.CrossingLiftBoundaryProbe

/-!
# Testing all boundary vertices of a replacement

Lemma 1's reverse rule needs to know whether a returned path uses a new clique edge. Every
such edge starts at one of the at most three recorded boundary vertices. The program here
probes those vertices and combines their flags. Thus the repeated path and edge scans still
cost only linear time in the path and recorded edge-list lengths.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Probe every boundary vertex, returning whether any following boundary pair is a new edge. -/
def liftBoundaryTestProg (src boundary edges r_bad R : ℕ) : Cmd :=
  .seq (.assign r_bad (.const 0))
    (.seq (.assign R (.const 0))
      (forUp R (.len boundary)
        (.seq (.assign (R + 1) (.read boundary (.reg R)))
          (.seq (liftBoundaryProbeProg src boundary edges (R + 1) (R + 2) (R + 16))
            (.ite (.reg (R + 2)) (.assign r_bad (.const 1)) .skip)))))

private theorem afterFlag_zero_or_one {N : ℕ} (B : List (Fin N))
    (E : List (Fin N × Fin N)) (L : List (Fin N)) (a : Fin N) :
    liftBoundaryAfterFlag B E L a = 0 ∨ liftBoundaryAfterFlag B E L a = 1 := by
  unfold liftBoundaryAfterFlag
  split_ifs <;> simp

private theorem boundary_prefix_step {N : ℕ} (B L : List (Fin N))
    (E : List (Fin N × Fin N)) {j : ℕ} (hj : j < B.length) :
    (∃ a ∈ B.take (j + 1), liftBoundaryAfterFlag B E L a = 1) ↔
      (∃ a ∈ B.take j, liftBoundaryAfterFlag B E L a = 1) ∨
        liftBoundaryAfterFlag B E L B[j] = 1 := by
  rw [List.take_succ_eq_append_getElem hj]
  simp only [List.mem_append, List.mem_singleton, or_and_right, exists_or, exists_eq_left]

/-- Testing all recorded boundary vertices takes linear time because their number is at most
three. The assumptions are stored lists, duplicate-free path and boundary, the boundary-size
bound, a result register below scratch, and a word bound. -/
theorem liftBoundaryTestProg_exec {w N : ℕ} (src boundary edges r_bad R : ℕ) (hbR : r_bad < R)
    (L B : List (Fin N)) (E : List (Fin N × Fin N))
    (hL : L.Nodup) (hB : B.Nodup) (hsmall : B.length ≤ 3) (s : State)
    (hsrc : s.arrs src = L.map Fin.val) (hbd : s.arrs boundary = B.map Fin.val)
    (hedges : s.arrs edges = E.flatMap encPair)
    (hw : 16 * (N + L.length + B.length + E.length + 5) < 2 ^ w) :
    ∃ s' t, Exec w (liftBoundaryTestProg src boundary edges r_bad R) s s' t ∧
      t ≤ 500 * (L.length + E.length + 1) + 1500 ∧
      s'.regs r_bad = (if ∃ a ∈ B, liftBoundaryAfterFlag B E L a = 1 then 1 else 0) ∧
      (∀ c, s'.arrs c = s.arrs c) ∧
      (∀ q < R, q ≠ r_bad → s'.regs q = s.regs q) := by
  have hw0 : 0 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  let budget := 100 * (L.length + B.length + E.length + 1) + 106
  let s0 := s.setReg r_bad 0
  let s1 := s0.setReg R 0
  let I : ℕ → State → Prop := fun j st =>
    st.regs R = j ∧
    st.regs r_bad = (if ∃ a ∈ B.take j, liftBoundaryAfterFlag B E L a = 1 then 1 else 0) ∧
    (∀ c, st.arrs c = s.arrs c) ∧
    (∀ q < R, q ≠ r_bad → st.regs q = s.regs q)
  have hinit : I 0 s1 := by
    refine ⟨by simp [s1], ?_, fun _ => rfl, ?_⟩
    · simp [s1, s0, show r_bad ≠ R by omega]
    · intro q hq hqb; simp [s1, s0, show q ≠ R by omega, hqb]
  obtain ⟨s2, t2, he2, ht2, hI⟩ := forUp_exec' I B.length budget hw1 (by omega)
    (r_i := R) (hi := .len boundary)
    (body := .seq (.assign (R + 1) (.read boundary (.reg R)))
      (.seq (liftBoundaryProbeProg src boundary edges (R + 1) (R + 2) (R + 16))
        (.ite (.reg (R + 2)) (.assign r_bad (.const 1)) .skip)))
    (fun j _ st hI => ⟨hI.1, by
      have he := eval_len (w := w) ((hI.2.2.1 boundary).trans hbd) (by simp only [List.length_map]; omega)
      simpa only [List.length_map] using he⟩)
    (fun j hj st hI => by
      obtain ⟨hi, ho, harr, hr⟩ := hI
      have hbdst : st.arrs boundary = B.map Fin.val := (harr boundary).trans hbd
      have hbound : j < (st.arrs boundary).length := by rw [hbdst, List.length_map]; exact hj
      have hval : (st.arrs boundary)[j]'hbound = B[j].val := by simp only [hbdst, List.getElem_map]
      have hread : (Expr.read boundary (.reg R)).eval w st = some B[j].val := by
        rw [← hval]
        exact eval_read (eval_reg hi (by omega)) hbound (by rw [hval]; exact B[j].isLt.trans (by omega))
      let st1 := st.setReg (R + 1) B[j].val
      obtain ⟨st2, tprobe, heprobe, htprobe, hflag, hpos, haprobe, hrprobe⟩ :=
        liftBoundaryProbeProg_exec (w := w) src boundary edges (R + 1) (R + 2) (R + 16)
          (by omega) (by omega) (by omega) L B E B[j] hL hB st1
          ((harr src).trans hsrc) ((harr boundary).trans hbd) ((harr edges).trans hedges)
          (by simp [st1]) hw
      have hR2 : st2.regs R = j := by
        rw [hrprobe R (by omega) (by omega)]; simp [st1, hi]
      have hbad2 : st2.regs r_bad = st.regs r_bad := by
        rw [hrprobe r_bad (by omega) (by omega)]; simp [st1, show r_bad ≠ R + 1 by omega]
      have hstep := boundary_prefix_step B L E hj
      by_cases hf : liftBoundaryAfterFlag B E L B[j] = 1
      · have hc : (Expr.reg (R + 2)).eval w st2 = some 1 := eval_reg (hflag.trans hf) hw1
        refine ⟨st2.setReg r_bad 1, 3 + (tprobe + 3),
          .seq (.assign hread) (.seq heprobe (.ite_true hc (by omega) (.assign (eval_const hw1)))),
          by dsimp [budget]; omega, ?_, ?_⟩
        · refine ⟨by simp, ?_, ?_, ?_⟩
          · simp [show r_bad ≠ R by omega, hstep, hf]
          · intro c; exact (haprobe c).trans (harr c)
          · intro q hq hqb
            simp only [State.setReg_regs_ne _ _ (show q ≠ R by omega), State.setReg_regs_ne _ _ hqb]
            rw [hrprobe q (by omega) (by omega)]
            simp only [st1, State.setReg_regs_ne _ _ (show q ≠ R + 1 by omega)]
            exact hr q hq hqb
        · simp [show R ≠ r_bad by omega, hR2]
      · have hf0 : liftBoundaryAfterFlag B E L B[j] = 0 :=
          (afterFlag_zero_or_one B E L B[j]).resolve_right hf
        have hc : (Expr.reg (R + 2)).eval w st2 = some 0 := eval_reg (hflag.trans hf0) hw0
        refine ⟨st2, 3 + (tprobe + 2), .seq (.assign hread) (.seq heprobe (.ite_false hc (.skip st2))),
          by dsimp [budget]; omega, ?_, hR2⟩
        refine ⟨by simp, ?_, ?_, ?_⟩
        · simpa only [State.setReg_regs_ne _ _ (show r_bad ≠ R by omega), hstep, hf, or_false] using hbad2.trans ho
        · intro c; exact (haprobe c).trans (harr c)
        · intro q hq hqb
          rw [State.setReg_regs_ne _ _ (show q ≠ R by omega), hrprobe q (by omega) (by omega)]
          simp only [st1, State.setReg_regs_ne _ _ (show q ≠ R + 1 by omega)]
          exact hr q hq hqb)
    s1 hinit
  refine ⟨s2, 2 + (2 + t2), .seq (.assign (eval_const hw0)) (.seq (.assign (eval_const hw0)) he2),
    ?_, ?_, hI.2.2.1, hI.2.2.2⟩
  · simp only [Expr.cost] at ht2
    have hm := Nat.mul_le_mul_right (7 + budget) hsmall
    dsimp [budget] at hm ht2
    omega
  · simpa only [List.take_length] using hI.2.1

end GraphMinor.Compute.Crossing
