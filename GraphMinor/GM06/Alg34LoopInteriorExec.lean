module

public import GraphMinor.GM06.Alg34LoopState
public import GraphMinor.Compute.GM06Alg34Driver
public import GraphMinor.Compute.GM06Alg34InteriorDriverFrames
import GraphMinor.Compute.CrossingOpsBasic
import GraphMinor.Compute.GM06Alg34InteriorReduce

/-!
# A successful interior deletion preserves the driver invariant

The finite search identifies the deleted component and the exact RAM
payload matches the proved geometric restriction. Its answer and all
fixed bounds are retained, while its work charge strictly decreases.
The success flag takes the driver's skip branch and leaves the queue
and outer controls unchanged.
-/

public section
namespace GraphMinor.Compute

open GM06
universe u

/-- When interior search succeeds, the complete non-null driver command
returns the exact deletion with the full invariant and smaller work. -/
theorem gm06Driver_interior {M E Q : ℕ} {answer : Prop}
    {X : GM06GapInput} {past : List ℕ} {tasks : List GM06GapComponentTask} {s : State}
    (hInv : gm06DriverInvariant.{u} M E Q answer (.running X past tasks) s)
    (a : Fin X.drawing.n) (hfind : X.drawing.findInteriorComponent = some a) :
    ∃ s' t, Exec (wordSize 256 Q) gm06DriverNonNull s s' t ∧
      t ≤ 2002 * (gm06RoundBase Q) ^ 22 ∧
      gm06DriverInvariant.{u} M E Q answer (.running (X.interiorGapData a) past tasks) s' ∧
      (GM06DriverConfig.running (X.interiorGapData a) past tasks).work (M + 1) <
        (GM06DriverConfig.running X past tasks).work (M + 1) := by
  obtain ⟨hX, hB, hTasks, hin, hgap, hbuf, hpos, hend, hrun, hcap, hbudget, hans⟩ := hInv
  have hsize := gm06LoopBounds_size hB
  have hshape : ∃ L R, X.drawing.cuffs = [L] ∧ X.gapRegions = [R] ∧ R.length = L.length := by
    obtain ⟨L, R, hL, hR, hlen, _⟩ := gm06LoopInstance_layout hX
    exact ⟨L, R, hL, hR, hlen⟩
  obtain ⟨s', t, he, ht, hin', hgap', hflag, _⟩ :=
    gm06GapInteriorStepProg_exec X hshape (c := 21) (by decide) hin hgap
  have he' := he.mono_wordSize (gm06Uniform_wordSize Q _ hsize)
  simp only [GM06GapInput.interiorStepData, hfind, Option.isSome_some, ↓reduceIte] at hin' hgap' hflag
  have ha := gm06FindInteriorComponent_sound X.drawing a hfind
  obtain ⟨hY, hBY, hf, hwork⟩ := gm06LoopInstance_interior hX hB a ha
  have hw : 1 < 2 ^ wordSize 256 Q := lt_two_pow_wordSize_of_le (by decide) (by omega)
  have hbranch : Exec (wordSize 256 Q)
      (.ite (.reg 6600) .skip (.seq gm06SplitProg (.ite (.reg 263) gm06DriverComponents (gm06DriverStop false))))
      s' s' 2 := .ite_true (Crossing.eval_reg hflag hw) (by decide) (.skip s')
  have hpw := gm06Round_power_le Q (X.drawing.size + 2) 3
    ((Nat.add_le_add_right hsize 2).trans (gm06RoundBase_bounds Q).2.1) (by decide)
  have ht' := ht.trans (Nat.mul_le_mul_left 2000 hpw)
  have hpower : 1 ≤ (gm06RoundBase Q) ^ 22 := Nat.one_le_pow _ _ (gm06RoundBase_bounds Q).1
  have hmul := Nat.mul_le_mul_left (2 * gm06TaskRecordBound Q)
    (Nat.add_le_add_right hwork.le (gm06TaskWork (M + 1) tasks))
  refine ⟨s', t + 2, .seq he' hbranch, by omega, ?_, ?_⟩
  · exact ⟨hY, hBY, hTasks, hin', hgap', hbuf.of_arr_eq (gm06GapInteriorStep_queue_frame he'),
      (gm06GapInteriorStep_driver_frame he' 7000 (by decide)).trans hpos,
      (gm06GapInteriorStep_driver_frame he' 7001 (by decide)).trans hend,
      (gm06GapInteriorStep_driver_frame he' 9000 (by decide)).trans hrun,
      (gm06GapInteriorStep_driver_frame he' 9004 (by decide)).trans hcap,
      by omega, hans.trans (and_congr hf Iff.rfl)⟩
  · change _ + gm06TaskWork (M + 1) tasks < _ + gm06TaskWork (M + 1) tasks
    omega

end GraphMinor.Compute
