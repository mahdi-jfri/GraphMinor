module

public import GraphMinor.Compute.TwoPathsCyc
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Computing the signed cuff labels

The rotation representation for VI (5.7), page 133, numbers the
inner cuff gaps after the original edges, in their supplied cuff
order. Gap i has forward end 2(m+i). The negative end at vertex i
is the reverse end of its preceding gap. The two labels differ
even with one gap. They are computed from the array lengths and
the cuff index, rather than supplied as a side certificate.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing TwoPaths

/-- The index of the preceding gap in a positive-length cuff. -/
def gm06PreviousCuffIndex (k i : ℕ) : ℕ := if i = 0 then k - 1 else i - 1

/-- Compute the negative and positive inner cuff end labels in 36
and 39, using cuff index 295, activity length 12 and cuff length 6. -/
def gm06ClockwiseCuffMarkersProg : Cmd :=
  .seq (.ite (.reg 295)
      (.assign 296 (.op .sub (.reg 295) (.const 1)))
      (.assign 296 (.op .sub (.len 6) (.const 1))))
    (.seq (.assign 36 (.op .add
        (.op .mul (.const 2) (.op .add (.len 12) (.reg 296))) (.const 1)))
      (.assign 39 (.op .mul (.const 2) (.op .add (.len 12) (.reg 295)))))

private theorem cuffMarkers_eval_length {w n a : ℕ} {s : State}
    (h : (s.arrs a).length = n) (hn : n < 2 ^ w) :
    (Expr.len a).eval w s = some n := by
  simp [Expr.eval, checkWord, h, hn]

/-- The predecessor gap index is in the supplied cuff. -/
theorem gm06PreviousCuffIndex_lt {k i : ℕ} (hi : i < k) : gm06PreviousCuffIndex k i < k := by
  unfold gm06PreviousCuffIndex
  split <;> omega

/-- The two cuff markers are computed in at most nineteen RAM
steps. All instance arrays and the supplied cuff index are preserved. -/
theorem gm06ClockwiseCuffMarkersProg_exec {w k i m : ℕ} (s : State)
    (hi : i < k) (hw : 2 < 2 ^ w) (hsize : 2 * (m + k) + 1 < 2 ^ w)
    (h6 : (s.arrs 6).length = k) (h12 : (s.arrs 12).length = m) (h295 : s.regs 295 = i) :
    ∃ s' t, Exec w gm06ClockwiseCuffMarkersProg s s' t ∧ t ≤ 19 ∧
      Keeps [296, 36, 39] [] s s' ∧
      s'.regs 296 = gm06PreviousCuffIndex k i ∧
      s'.regs 36 = 2 * (m + gm06PreviousCuffIndex k i) + 1 ∧
      s'.regs 39 = 2 * (m + i) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hkw : k < 2 ^ w := by omega
  have hmw : m < 2 ^ w := by omega
  have hiw : i < 2 ^ w := hi.trans hkw
  have hprev := gm06PreviousCuffIndex_lt hi
  let s₀ := s.setReg 296 (gm06PreviousCuffIndex k i)
  have hbranch : ∃ t, Exec w (.ite (.reg 295)
      (.assign 296 (.op .sub (.reg 295) (.const 1)))
      (.assign 296 (.op .sub (.len 6) (.const 1)))) s s₀ t ∧ t ≤ 5 := by
    by_cases hz : i = 0
    · refine ⟨5, ?_, by decide⟩
      have he : Exec w (.assign 296 (.op .sub (.len 6) (.const 1))) s
          (s.setReg 296 (k - 1)) 4 :=
        .assign (eval_sub (cuffMarkers_eval_length h6 hkw) (eval_const hw1))
      simpa only [s₀, gm06PreviousCuffIndex, hz, ite_true, Expr.cost, Nat.reduceAdd] using
        (Exec.ite_false (cond := .reg 295)
          (by simpa only [hz] using eval_reg h295 hiw) he)
    · refine ⟨5, ?_, by decide⟩
      have he : Exec w (.assign 296 (.op .sub (.reg 295) (.const 1))) s
          (s.setReg 296 (i - 1)) 4 :=
        .assign (eval_sub (eval_reg h295 hiw) (eval_const hw1))
      simpa only [s₀, gm06PreviousCuffIndex, hz, ite_false, Expr.cost, Nat.reduceAdd] using
        (Exec.ite_true (cond := .reg 295) (eval_reg h295 hiw) hz he)
  obtain ⟨t₀, he₀, ht₀⟩ := hbranch
  have hprevReg : s₀.regs 296 = gm06PreviousCuffIndex k i := by simp [s₀]
  have hsum : m + gm06PreviousCuffIndex k i < 2 ^ w := by omega
  have htwice : 2 * (m + gm06PreviousCuffIndex k i) < 2 ^ w := by omega
  have hmarker : 2 * (m + gm06PreviousCuffIndex k i) + 1 < 2 ^ w := by omega
  let s₁ := s₀.setReg 36 (2 * (m + gm06PreviousCuffIndex k i) + 1)
  have he₁ : Exec w (.assign 36 (.op .add
      (.op .mul (.const 2) (.op .add (.len 12) (.reg 296))) (.const 1))) s₀ s₁ 8 :=
    .assign (eval_add (eval_mul (eval_const hw)
      (eval_add (cuffMarkers_eval_length (by simpa [s₀] using h12) hmw)
        (eval_reg hprevReg (hprev.trans hkw)) hsum) htwice) (eval_const hw1) hmarker)
  let s₂ := s₁.setReg 39 (2 * (m + i))
  have he₂ : Exec w (.assign 39 (.op .mul (.const 2) (.op .add (.len 12) (.reg 295))))
      s₁ s₂ 6 :=
    .assign (eval_mul (eval_const hw)
      (eval_add (cuffMarkers_eval_length (by simpa [s₁, s₀] using h12) hmw)
        (eval_reg (by simpa [s₁, s₀] using h295) hiw) (by omega)) (by omega))
  have hex : Exec w gm06ClockwiseCuffMarkersProg s s₂ (t₀ + (8 + 6)) :=
    .seq he₀ (.seq he₁ he₂)
  refine ⟨s₂, _, hex, by omega, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro r hr
    apply hex.regs_eq_of_not_mem_writtenRegs
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gm06ClockwiseCuffMarkersProg, Cmd.writtenRegs]
    tauto
  · intro a _
    apply hex.arrs_eq_of_not_mem_writtenArrs
    simp [gm06ClockwiseCuffMarkersProg, Cmd.writtenArrs]
  · simp [s₂, s₁, s₀]
  · simp [s₂, s₁]
  · simp [s₂]

end GraphMinor.Compute
