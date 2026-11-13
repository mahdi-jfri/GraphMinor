module

public import GraphMinor.Compute.CrossingOpsCountGreater

/-!
# Locating the final selected edge row

A row search counts its increasing neighbours. If the remaining edge quota fits in
this row, it records the quota and stops. Otherwise it subtracts the row count and
advances to the next vertex. The program reads the quota and all sizes from registers.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Compare two word expressions using non-strict order. -/
theorem eval_le {w : ℕ} {s : State} {E F : Expr} {a b : ℕ}
    (hE : E.eval w s = some a) (hF : F.eval w s = some b) (hw : 1 < 2 ^ w) :
    (Expr.op .le E F).eval w s = some (if a ≤ b then 1 else 0) := by
  by_cases hh : a ≤ b <;> simp [Expr.eval, hE, hF, BinOp.eval, BinOp.raw, checkWord,
    hh, hw, show 0 < 2 ^ w by omega]

/-- Locate the final selected row, with quota in `R+5` and final-row count in `R+6`. -/
def locateEdgeRowBody (a_s a_e a_ent R : ℕ) : Cmd :=
  .seq (countGreaterProg a_s a_e a_ent R)
    (.ite (.op .le (.reg (R + 5)) (.reg (R + 4)))
      (.seq (.assign (R + 6) (.reg (R + 5))) (.assign (R + 5) (.const 0)))
      (.seq (.assign (R + 5) (.op .sub (.reg (R + 5)) (.reg (R + 4))))
        (.assign R (.op .add (.reg R) (.const 1)))))

/-- One row search stops with its remaining quota, or advances after paying for the
entire row. It takes linear time in the adjacency-list length and changes no array. -/
theorem locateEdgeRowBody_exec {w : ℕ} (a_s a_e a_ent R : ℕ)
    {s : State} {x st en quota : ℕ} {l : List ℕ}
    (hl : IsListAt a_s a_e a_ent x st en l s) (hx : s.regs R = x)
    (hq : s.regs (R + 5) = quota)
    (hxword : x + 1 < 2 ^ w) (hqword : quota < 2 ^ w)
    (hen : en < 2 ^ w) (hlen : l.length < 2 ^ w)
    (hlword : ∀ y ∈ l, y < 2 ^ w) (hw : 1 < 2 ^ w) :
    let count := (l.filter (fun y => x < y)).length
    ∃ s' t, Exec w (locateEdgeRowBody a_s a_e a_ent R) s s' t ∧ t ≤ 25 + 17 * l.length ∧
      s'.regs R = (if quota ≤ count then x else x + 1) ∧
      s'.regs (R + 5) = (if quota ≤ count then 0 else quota - count) ∧
      s'.regs (R + 6) = (if quota ≤ count then quota else s.regs (R + 6)) ∧
      (∀ a, s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ R → r ≠ R + 1 → r ≠ R + 2 → r ≠ R + 3 → r ≠ R + 4 →
        r ≠ R + 5 → r ≠ R + 6 → s'.regs r = s.regs r) := by
  let count := (l.filter (fun y => x < y)).length
  obtain ⟨s1, t1, he1, ht1, hc1, ha1, hr1⟩ := countGreaterProg_exec a_s a_e a_ent R
    hl hx (by omega) hen hlen hlword hw
  have hx1 : s1.regs R = x := (hr1 R (by omega) (by omega) (by omega) (by omega)).trans hx
  have hq1 : s1.regs (R + 5) = quota :=
    (hr1 (R + 5) (by omega) (by omega) (by omega) (by omega)).trans hq
  have h6 : s1.regs (R + 6) = s.regs (R + 6) := hr1 _ (by omega) (by omega) (by omega) (by omega)
  have hcount : count < 2 ^ w := (List.length_filter_le _ _).trans_lt hlen
  have htest : (Expr.op .le (.reg (R + 5)) (.reg (R + 4))).eval w s1 =
      some (if quota ≤ count then 1 else 0) :=
    eval_le (eval_reg hq1 hqword) (eval_reg hc1 hcount) hw
  have hrun : ∃ s' t, Exec w (locateEdgeRowBody a_s a_e a_ent R) s s' t ∧ t ≤ 25 + 17 * l.length ∧
      s'.regs R = (if quota ≤ count then x else x + 1) ∧
      s'.regs (R + 5) = (if quota ≤ count then 0 else quota - count) ∧
      s'.regs (R + 6) = (if quota ≤ count then quota else s.regs (R + 6)) := by
    by_cases hdone : quota ≤ count
    · let s2 := s1.setReg (R + 6) quota
      let s3 := s2.setReg (R + 5) 0
      have he2 : Exec w (.assign (R + 6) (.reg (R + 5))) s1 s2 2 := .assign (eval_reg hq1 hqword)
      have he3 : Exec w (.assign (R + 5) (.const 0)) s2 s3 2 := .assign (eval_const (by omega))
      refine ⟨s3, t1 + (3 + (2 + 2)), .seq he1
        (.ite_true (by simpa [hdone] using htest) (by decide) (.seq he2 he3)), by omega, ?_, ?_, ?_⟩
      · simp [s3, s2, hdone, hx1]
      · simp [s3, hdone]
      · simp [s3, s2, hdone]
    · let s2 := s1.setReg (R + 5) (quota - count)
      let s3 := s2.setReg R (x + 1)
      have he2 : Exec w (.assign (R + 5) (.op .sub (.reg (R + 5)) (.reg (R + 4)))) s1 s2 4 :=
        .assign (eval_sub (eval_reg hq1 hqword) (eval_reg hc1 hcount))
      have he3 : Exec w (.assign R (.op .add (.reg R) (.const 1))) s2 s3 4 :=
        .assign (eval_add (eval_reg (by simpa [s2] using hx1) (by omega)) (eval_const hw) hxword)
      refine ⟨s3, t1 + (3 + (4 + 4)), .seq he1
        (.ite_false (by simpa [hdone] using htest) (.seq he2 he3)), by omega, ?_, ?_, ?_⟩
      · simp [s3, hdone]
      · simp [s3, s2, hdone]
      · simp [s3, s2, hdone, h6]
  obtain ⟨s', t, he, ht, hx', hq', h6'⟩ := hrun
  refine ⟨s', t, he, ht, hx', hq', h6', ?_, ?_⟩
  · intro a
    exact he.arrs_eq_of_not_mem_writtenArrs (by
      simp [locateEdgeRowBody, countGreaterProg, forList, forUp, Cmd.writtenArrs])
  · intro r h0 h1 h2 h3 h4 h5 h6
    exact he.regs_eq_of_not_mem_writtenRegs (by
      simp [locateEdgeRowBody, countGreaterProg, forList, forUp, Cmd.writtenRegs, h0, h1, h2, h3, h4, h5, h6])

end GraphMinor.Compute.Crossing
