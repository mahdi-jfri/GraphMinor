module

public import GraphMinor.Compute.Case3StepsWriteCopyProg

/-!
# Expanding all copies of one directed pair

The copy counter runs from zero to the stored multiplicity. Each iteration
writes one triple and leaves its number unchanged. The completed triple
prefix advances by that multiplicity, so the outer pair scan can continue
with the next directed pair in the multigraph's order.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Expand the pair in 106/107 with multiplicity 108 after prefix 109. -/
def case3ExpandCopiesProg : Cmd :=
  .seq (.assign 110 (.const 0))
    (.seq (forUp 110 (.reg 108) case3WriteCopyProg)
      (.assign 109 (.op .add (.reg 109) (.reg 108))))

private theorem copiesLoop_exec {w : ℕ} (pre suf : List ℕ) (u v q m : ℕ)
    (hpre : pre.length = 3 * q) (hw : 3 < 2 ^ w)
    (hlen : pre.length + 3 * m + 1 < 2 ^ w) (hu : u < 2 ^ w) (hv : v < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = m) {s : State}
    (hdst : s.arrs 50 = pre ++ case3ParallelCopies u v k ++ List.replicate (3 * (m - k)) 0 ++ suf)
    (hru : s.regs 106 = u) (hrv : s.regs 107 = v) (hrm : s.regs 108 = m)
    (hrq : s.regs 109 = q) (hrk : s.regs 110 = k) :
    ∃ s' t, Exec w (forUp 110 (.reg 108) case3WriteCopyProg) s s' t ∧
      t ≤ 3 + 26 * rem ∧ s'.arrs 50 = pre ++ case3ParallelCopies u v m ++ suf := by
  have h0 : 0 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have hmw : m < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk : k = m := by omega
    have hc : (Expr.op .lt (.reg 110) (.reg 108)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrm, hk, hmw, h0]
    refine ⟨s, 3, .while_false hc, by omega, ?_⟩
    simpa only [hk, Nat.sub_self, Nat.mul_zero, List.replicate_zero, List.append_nil] using hdst
  | succ rem ih =>
    have hk : k < m := by omega
    have hkw : k < 2 ^ w := by omega
    have hkp : k + 1 < 2 ^ w := by omega
    have hc : (Expr.op .lt (.reg 110) (.reg 108)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrm, hk, hkw, hmw, h1]
    have hrep : List.replicate (3 * (m - k)) 0 =
        [0, 0, 0] ++ List.replicate (3 * (m - (k + 1))) 0 := by
      rw [show 3 * (m - k) = 3 + 3 * (m - (k + 1)) by omega, List.replicate_add]
      rfl
    obtain ⟨sB, hexB, hdstB, harrB, hregB⟩ := case3WriteCopyProg_exec
      (pre ++ case3ParallelCopies u v k) (List.replicate (3 * (m - (k + 1))) 0 ++ suf) u v q k
      (by rw [List.length_append, case3ParallelCopies_length, hpre]; omega) hw
      (by rw [List.length_append, case3ParallelCopies_length]; omega) hu hv
      (s := s) (by simpa only [List.append_assoc, hrep] using hdst) hru hrv hrq hrk
    let sC := sB.setReg 110 (k + 1)
    have hexC : Exec w (.assign 110 (.op .add (.reg 110) (.const 1))) sB sC 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hregB 110 (by decide), hrk, hkw, h1, hkp])
    have hbufC : sC.arrs 50 = pre ++ case3ParallelCopies u v (k + 1) ++
        List.replicate (3 * (m - (k + 1))) 0 ++ suf := by
      rw [State.setReg_arrs, hdstB, case3ParallelCopies_succ]
      simp only [List.append_assoc]
    have hregC (r : ℕ) (h110 : r ≠ 110) (h116 : r ≠ 116) : sC.regs r = s.regs r := by
      rw [State.setReg_regs_ne _ _ h110, hregB r h116]
    obtain ⟨s', t, hex, ht, hdst'⟩ := ih (k + 1) (by omega) (s := sC) hbufC
      (by rw [hregC 106 (by decide) (by decide)]; exact hru)
      (by rw [hregC 107 (by decide) (by decide)]; exact hrv)
      (by rw [hregC 108 (by decide) (by decide)]; exact hrm)
      (by rw [hregC 109 (by decide) (by decide)]; exact hrq)
      (State.setReg_regs_self ..)
    exact ⟨s', 3 + (19 + 4) + t, .while_true hc (by decide) (.seq hexB hexC) hex, by omega, hdst'⟩

/-- Expanding a parallel class costs at most `26 m + 9` and writes exactly
its numbered copies, retaining all surrounding record words. -/
theorem case3ExpandCopiesProg_exec {w : ℕ} (pre suf : List ℕ) (u v q m : ℕ)
    (hpre : pre.length = 3 * q) (hw : 3 < 2 ^ w)
    (hlen : pre.length + 3 * m + 1 < 2 ^ w) (hu : u < 2 ^ w) (hv : v < 2 ^ w)
    {s : State} (hdst : s.arrs 50 = pre ++ List.replicate (3 * m) 0 ++ suf)
    (hru : s.regs 106 = u) (hrv : s.regs 107 = v)
    (hrm : s.regs 108 = m) (hrq : s.regs 109 = q) :
    ∃ s' t, Exec w case3ExpandCopiesProg s s' t ∧ t ≤ 26 * m + 9 ∧
      s'.arrs 50 = pre ++ case3ParallelCopies u v m ++ suf ∧ s'.regs 109 = q + m ∧
      (∀ a, a ≠ 50 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 109 → r ≠ 110 → r ≠ 116 → s'.regs r = s.regs r) := by
  have h0 : 0 < 2 ^ w := by omega
  have hq : q < 2 ^ w := by omega
  have hm : m < 2 ^ w := by omega
  have hqm : q + m < 2 ^ w := by omega
  let s₁ := s.setReg 110 0
  have hex₁ : Exec w (.assign 110 (.const 0)) s s₁ 2 :=
    .assign (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
  obtain ⟨s₂, t₂, hex₂, ht₂, hdst₂⟩ := copiesLoop_exec pre suf u v q m hpre hw hlen hu hv m 0 (by omega)
    (s := s₁) (by simpa only [s₁, State.setReg_arrs, case3ParallelCopies, List.range_zero,
      List.map_nil, encEdgeTriples, List.append_nil, Nat.sub_zero] using hdst)
    (by simp only [s₁, State.setReg_regs_ne _ _ (show (106 : ℕ) ≠ 110 by decide), hru])
    (by simp only [s₁, State.setReg_regs_ne _ _ (show (107 : ℕ) ≠ 110 by decide), hrv])
    (by simp only [s₁, State.setReg_regs_ne _ _ (show (108 : ℕ) ≠ 110 by decide), hrm])
    (by simp only [s₁, State.setReg_regs_ne _ _ (show (109 : ℕ) ≠ 110 by decide), hrq])
    (State.setReg_regs_self ..)
  have hregs₂ (r : ℕ) (h110 : r ≠ 110) (h116 : r ≠ 116) : s₂.regs r = s.regs r := by
    rw [hex₂.regs_eq_of_not_mem_writtenRegs (by simp [forUp, case3WriteCopyProg, Cmd.writtenRegs, h110, h116]),
      State.setReg_regs_ne _ _ h110]
  let s₃ := s₂.setReg 109 (q + m)
  have hex₃ : Exec w (.assign 109 (.op .add (.reg 109) (.reg 108))) s₂ s₃ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hregs₂ 109 (by decide) (by decide), hregs₂ 108 (by decide) (by decide), hrq, hrm, hq, hm, hqm])
  have hex : Exec w case3ExpandCopiesProg s s₃ (2 + (t₂ + 4)) := .seq hex₁ (.seq hex₂ hex₃)
  refine ⟨s₃, 2 + (t₂ + 4), hex, by omega, hdst₂, State.setReg_regs_self .., ?_, ?_⟩
  · intro a ha
    exact hex.arrs_eq_of_not_mem_writtenArrs (by simp [case3ExpandCopiesProg, forUp, case3WriteCopyProg, Cmd.writtenArrs, ha])
  · intro r h109 h110 h116
    exact hex.regs_eq_of_not_mem_writtenRegs (by simp [case3ExpandCopiesProg, forUp, case3WriteCopyProg, Cmd.writtenRegs, h109, h110, h116])

end GraphMinor.Compute
