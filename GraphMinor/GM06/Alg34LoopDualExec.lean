module

public import GraphMinor.GM06.Alg34LoopState
public import GraphMinor.Compute.GM06Alg34DualExhaustExec

/-!
# The complete dual branch preserves the driver invariant

At a connected stuck state, the established geometric progress proof
and the exact RAM dual/singleton execution give the same finite output.
Its work charge is strictly smaller, its answer is unchanged, and all
pending task words and cursors stay fixed. Thus the storage inequality
and the complete driver invariant hold at the next loop entry.
-/

public section
namespace GraphMinor.Compute

open GM06
universe u

/-- The full dual branch retains the loop invariant and strictly lowers
its total work charge, with a uniform polynomial execution bound. -/
theorem gm06Driver_dual {M E Q : ℕ} {answer : Prop}
    {X : GM06GapInput} {past : List ℕ} {tasks : List GM06GapComponentTask} {s : State}
    (hInv : gm06DriverInvariant.{u} M E Q answer (.running X past tasks) s)
    (hn : 0 < X.drawing.n) (hI : X.drawing.findInteriorComponent = none)
    (hSing : gm06FindSingleton X.drawing.division = none) (hk : X.drawing.componentRoots.length ≤ 1) :
    ∃ s' t, Exec (wordSize 256 Q) (.seq gm06DualBuildProg gm06GapSingletonExhaustProg) s s' t ∧
      t ≤ 8000 * (gm06RoundBase Q) ^ 22 ∧
      gm06DriverInvariant.{u} M E Q answer (.running (gm06GapReduceSingletons X.discDualData) past tasks) s' ∧
      (GM06DriverConfig.running (gm06GapReduceSingletons X.discDualData) past tasks).work (M + 1) <
        (GM06DriverConfig.running X past tasks).work (M + 1) := by
  obtain ⟨hX, hB, hTasks, hin, hgap, hbuf, hpos, hend, hrun, hcap, hbudget, hans⟩ := hInv
  obtain ⟨s', t, he, ht, hin', hgap', hq, hp, hend', hrun', _, hcap'⟩ :=
    gm06DualExhaust_exec Q X hB.2.2.1 hB.2.2.2.1 hB.2.2.2.2.1 hB.2.2.2.2.2
      (gm06LoopInstance_layout hX) (gm06LoopInstance_regions_pos hX hn)
      (gm06LoopInstance_division hX) hin hgap
  obtain ⟨hY, hBY, hf, hwork⟩ := gm06LoopInstance_dual hX hB hn hI hSing hk
  have hpw := gm06Round_power_le Q (40 * (Q + 2) ^ 2 + 2) 22 (gm06RoundBase_bounds Q).2.1 le_rfl
  have htime := ht.trans (Nat.mul_le_mul_left 8000 hpw)
  have hmul := Nat.mul_le_mul_left (2 * gm06TaskRecordBound Q)
    (Nat.add_le_add_right hwork.le (gm06TaskWork (M + 1) tasks))
  refine ⟨s', t, he, htime, ?_, ?_⟩
  · exact ⟨hY, hBY, hTasks, hin', hgap', hbuf.of_arr_eq hq, hp.trans hpos, hend'.trans hend,
      hrun'.trans hrun, hcap'.trans hcap, by omega, hans.trans (and_congr hf Iff.rfl)⟩
  · change _ + gm06TaskWork (M + 1) tasks < _ + gm06TaskWork (M + 1) tasks
    omega

end GraphMinor.Compute
