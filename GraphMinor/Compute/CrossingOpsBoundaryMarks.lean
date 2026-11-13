module

public import GraphMinor.Compute.CrossingOpsFilter
public import GraphMinor.Compute.CrossingOpsReplMark

/-!
# Marking the chosen prefix of the final edge row

The program copies the increasing neighbours of the final row into a bounded buffer,
copies the requested prefix, and uses the existing marking loop on that prefix. This
marks exactly the boundary-row edges chosen for the extra retained edge set.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Mark the first `R+6` increasing neighbours of the vertex in `R`. `R+8` holds `N`. -/
def boundaryMarksProg (a_s a_e a_ent B R : ℕ) : Cmd :=
  .seq (.alloc B (.reg (R + 8)))
    (.seq (.assign (R + 4) (.const 0))
      (.seq (filterListProg a_s a_e a_ent B R (.op .lt (.reg R) (.reg (R + 3))))
        (.seq (.assign (R + 14) (.reg (R + 6)))
          (.seq (.assign (R + 11) (.reg (R + 8)))
            (.seq (copyMinNProg B (B + 1) (R + 11) (R + 12) (R + 14))
              (markArrayProg (B + 1) (B + 2) R))))))

/-- The boundary marks represent exactly the chosen prefix, with a linear cost bound. -/
theorem boundaryMarksProg_exec {w N : ℕ} (a_s a_e a_ent B R : ℕ)
    {s : State} {l : List ℕ} {x st en q : ℕ}
    (hs : a_s < B) (he : a_e < B) (hent : a_ent < B)
    (hl : IsListAt a_s a_e a_ent x st en l s) (hx : s.regs R = x)
    (hxN : x < N) (hN : s.regs (R + 8) = N) (hq : s.regs (R + 6) = q)
    (hqlen : q ≤ (l.filter (fun y => x < y)).length)
    (hlen : l.length ≤ N) (hlt : ∀ y ∈ l, y < N)
    (hw : N + (s.arrs a_ent).length + 2 < 2 ^ w) :
    ∃ s' t, Exec w (boundaryMarksProg a_s a_e a_ent B R) s s' t ∧ t ≤ 60 * (N + 1) ∧
      s'.arrs (B + 2) = setAt (List.replicate N 0) ((l.filter (fun y => x < y)).take q) 1 ∧
      s'.regs R = x ∧ (∀ a, a < B → s'.arrs a = s.arrs a) := by
  let up := l.filter (fun y => x < y)
  have hqN : q ≤ N := hqlen.trans ((List.length_filter_le _ _).trans hlen)
  have hup : up.length ≤ N := (List.length_filter_le _ _).trans hlen
  have huplt : ∀ y ∈ up, y < N := fun y hy => hlt y (List.mem_of_mem_filter hy)
  let s1 := s.setArr B (List.replicate N 0)
  let s2 := s1.setReg (R + 4) 0
  have he1 : Exec w (.alloc B (.reg (R + 8))) s s1 (1 + N) := .alloc (eval_reg hN (by omega))
  have he2 : Exec w (.assign (R + 4) (.const 0)) s1 s2 2 := .assign (eval_const (by omega))
  have ha2 : ∀ a, a < B → s2.arrs a = s.arrs a := by
    intro a ha; simp [s2, s1, State.setArr_arrs_ne, show a ≠ B by omega]
  obtain ⟨s3, t3, he3, ht3, hb3, ha3, hr3⟩ := filterListProg_exec (w := w) (pre := []) (k := N)
    a_s a_e a_ent B R (.op .lt (.reg R) (.reg (R + 3))) (fun y => x < y)
    (by omega) (hl.of_arrs_eq (ha2 _ hs) (ha2 _ he) (ha2 _ hent))
    (by simpa [s2, s1] using hx) (by simp [IsBuf, s2, s1])
    hup (fun y hy => (hlt y hy).trans (show N < 2 ^ w by omega)) (by omega)
    (by have hh := hl.2.2.1; omega) (by omega)
    (by simp only [List.length_nil, Nat.zero_add]; omega)
    (fun z y hy _ hx' hy' => by
      simpa only [decide_eq_true_eq] using eval_lt (eval_reg hx' (show x < 2 ^ w by omega))
        (eval_reg hy' ((hlt y hy).trans (show N < 2 ^ w by omega))) (show 1 < 2 ^ w by omega))
  have hr6 : s3.regs (R + 6) = q :=
    (hr3 _ (by omega) (by omega) (by omega) (by omega)).trans (by simpa [s2, s1] using hq)
  have hr8 : s3.regs (R + 8) = N :=
    (hr3 _ (by omega) (by omega) (by omega) (by omega)).trans (by simpa [s2, s1] using hN)
  have hr0 : s3.regs R = x :=
    (hr3 _ (by omega) (by omega) (by omega) (by omega)).trans (by simpa [s2, s1] using hx)
  let s4 := s3.setReg (R + 14) q
  let s5 := s4.setReg (R + 11) N
  have he4 : Exec w (.assign (R + 14) (.reg (R + 6))) s3 s4 2 := .assign (eval_reg hr6 (by omega))
  have he5 : Exec w (.assign (R + 11) (.reg (R + 8))) s4 s5 2 :=
    .assign (eval_reg (by simpa [s4] using hr8) (by omega))
  obtain ⟨s6, t6, he6, ht6, harr6, ha6, hr6'⟩ := copyMinNProg_exec (w := w)
    B (B + 1) (R + 11) (R + 12) (R + 14) (by omega) (by omega) (by omega) (by omega)
    (s := s5) (B := N) (n := q) (by simp [s5]) (by omega) (by omega)
    (by simp [s5, s4]) (by omega) (by simp [s5, s4, hb3.1]; omega)
  have hsel : s6.arrs (B + 1) = up.take q := by
    rw [harr6]
    simp only [s5, s4, State.setReg_arrs, hb3.1, List.nil_append]
    rw [List.take_append_of_le_length hqlen]
    exact map_min_of_le (fun y hy => (huplt y (List.mem_of_mem_take hy)).le)
  have hr8' : s6.regs (R + 8) = N :=
    (hr6' _ (by omega)).trans (by simp [s5, s4, hr8])
  obtain ⟨s7, t7, he7, ht7, hm7, ha7, hr7⟩ := markArrayProg_exec (w := w) (N := N)
    (B + 1) (B + 2) R (s := s6) (l := up.take q) (by omega) hsel hr8'
    (fun y hy => huplt y (List.mem_of_mem_take hy))
    (by have hh := List.length_take_le q up; omega) (by omega) (by omega)
  have hex := Exec.seq he1 (.seq he2 (.seq he3 (.seq he4 (.seq he5 (.seq he6 he7)))))
  refine ⟨s7, _, hex, ?_, hm7, ?_, ?_⟩
  · simp only [Expr.cost] at ht3
    have htake : (up.take q).length ≤ q := List.length_take_le q up
    omega
  · exact (hr7 R (by omega) (by omega) (by omega)).trans
      ((hr6' R (by omega)).trans (by simp [s5, s4, hr0]))
  · intro a hh
    exact hex.arrs_eq_of_not_mem_writtenArrs (by
      simp [boundaryMarksProg, filterListProg, forList, forUp, emitWhenProg, emitProg,
        copyMinNProg, markArrayProg, writeAllProg, forArrProg, Cmd.writtenArrs,
        show a ≠ B by omega, show a ≠ B + 1 by omega, show a ≠ B + 2 by omega])

end GraphMinor.Compute.Crossing
