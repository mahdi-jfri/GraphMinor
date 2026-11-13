module

public import GraphMinor.Compute.GM06Alg34DriverStop
public import GraphMinor.Compute.GM06Alg34DriverControlFrames
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Selecting the next task or accepting the finished queue

When the two queue cursors agree, the driver saves acceptance and stops.
Otherwise it decodes the next parent/root packet and installs its exact
component input. The remaining queue and live end are retained, and the
outer running flag, saved answer and capacity stay fixed.
-/

public section
namespace GraphMinor.Compute

/-- An exhausted task queue stops with acceptance in seven steps. -/
theorem gm06DriverNext_done_exec {w : ℕ} {s : State} (hw : 1 < 2 ^ w)
    (hpos : s.regs 7000 = s.regs 7001) (hend : s.regs 7001 < 2 ^ w) :
    ∃ s', Exec w gm06DriverNext s s' 7 ∧ s'.regs 9000 = 0 ∧ s'.regs 9001 = 1 ∧
      (∀ A : ℕ, s'.arrs A = s.arrs A) := by
  have hcond : (Expr.op .lt (.reg 7000) (.reg 7001)).eval w s = some 0 := by
    simpa only [lt_self_iff_false, ite_false] using Crossing.eval_lt
      (Crossing.eval_reg hpos hend) (Crossing.eval_reg rfl hend) hw
  obtain ⟨s', he, hrun, hans, ha, _⟩ := gm06DriverStop_exec hw true s
  exact ⟨s', .ite_false hcond he, hrun, hans, ha⟩

/-- A pending task is decoded and materialized exactly, with cubic time
and with all outer driver controls retained. -/
theorem gm06DriverNext_task_exec {w off : ℕ} (T : GM06GapComponentTask) (tail : List ℕ)
    (L : List (Fin T.drawing.n)) (hL : T.drawing.cuffs = [L]) (hlen : T.gaps.length = L.length)
    (hw : wordSize 3 T.drawing.size ≤ w) (hsize : T.size < 2 ^ w)
    (hend : off + T.words.length < 2 ^ w) {s : State}
    (hstream : AtStream 42 off (T.words ++ tail) s) (hpos : s.regs 7000 = off)
    (hactive : off < s.regs 7001) (hbound : s.regs 7001 < 2 ^ w) :
    ∃ s' t, Exec w gm06DriverNext s s' t ∧ t ≤ 1700 * (T.size + 2) ^ 3 + 3 ∧
      s'.arrs 0 = T.target.drawing.words ∧ s'.arrs 47 = T.target.discGapWords ∧
      s'.regs 7000 = off + T.words.length ∧ AtStream 42 (off + T.words.length) tail s' ∧
      s'.regs 7001 = s.regs 7001 ∧ s'.regs 9000 = s.regs 9000 ∧
      s'.regs 9001 = s.regs 9001 ∧ s'.regs 9004 = s.regs 9004 := by
  have hw1 : 1 < 2 ^ w := by
    have hh := T.drawing.five_le_words_length
    have hs := T.drawing.words_length_le_size.trans T.drawing_size_le
    omega
  have hcond : (Expr.op .lt (.reg 7000) (.reg 7001)).eval w s = some 1 := by
    simpa only [ite_eq_left hactive] using Crossing.eval_lt
      (Crossing.eval_reg hpos (hactive.trans hbound)) (Crossing.eval_reg rfl hbound) hw1
  obtain ⟨s', t, he, ht, hin, hgap, hp, hs, hend', _⟩ :=
    gm06GapTaskMaterializeProg_exec T tail L hL hlen hw hsize hend hstream hpos
  refine ⟨s', 3 + t, .ite_true hcond (by decide) he, by omega, hin, hgap, hp, hs, hend', ?_, ?_, ?_⟩
  · exact gm06GapTaskMaterialize_driver_frame he 9000 (by decide)
  · exact gm06GapTaskMaterialize_driver_frame he 9001 (by decide)
  · exact gm06GapTaskMaterialize_driver_frame he 9004 (by decide)

end GraphMinor.Compute
