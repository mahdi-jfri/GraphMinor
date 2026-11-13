module

public import GraphMinor.GM06.Alg34LoopState
public import GraphMinor.Compute.GM06Alg34GapSingletonComplexity
public import GraphMinor.Compute.GM06Alg34SingletonDriverFrames

/-!
# The singleton phase preserves the complete driver invariant

Run the existing exact RAM singleton phase at the common word size.
The geometric and numerical phase proofs supply the new current
instance. Its answer is unchanged and its charge cannot increase, so
the cumulative queue storage inequality and all pending tasks remain
valid. Syntactic frames preserve the queue and outer controls.
-/

public section
namespace GraphMinor.Compute

open GM06
universe u

/-- Singleton exhaustion retains the full queue invariant at uniform word
size and installs its exact finite current problem. -/
theorem gm06Driver_singletons {M E Q : ℕ} {answer : Prop}
    {X : GM06GapInput} {past : List ℕ} {tasks : List GM06GapComponentTask} {s : State}
    (hInv : gm06DriverInvariant.{u} M E Q answer (.running X past tasks) s) :
    ∃ s' t, Exec (wordSize 256 Q) gm06GapSingletonExhaustProg s s' t ∧
      t ≤ 4000 * (gm06RoundBase Q) ^ 22 ∧
      gm06DriverInvariant.{u} M E Q answer (.running (gm06GapReduceSingletons X) past tasks) s' ∧
      (GM06DriverConfig.running (gm06GapReduceSingletons X) past tasks).work (M + 1) ≤
        (GM06DriverConfig.running X past tasks).work (M + 1) := by
  obtain ⟨hX, hB, hTasks, hin, hgap, hbuf, hpos, hend, hrun, hcap, hbudget, hans⟩ := hInv
  have hsize := gm06LoopBounds_size hB
  have hshape : ∃ L R, X.drawing.cuffs = [L] ∧ X.gapRegions = [R] ∧ R.length = L.length := by
    obtain ⟨L, R, hL, hR, hlen, _⟩ := gm06LoopInstance_layout hX
    exact ⟨L, R, hL, hR, hlen⟩
  obtain ⟨s', t, he, ht, hin', hgap', _, _⟩ := gm06GapSingletonExhaustProg_exec_poly X hshape hin hgap
  have he' := he.mono_wordSize (gm06Uniform_wordSize Q _ hsize)
  obtain ⟨hY, hBY, hf, hwork⟩ := gm06LoopInstance_singletons hX hB
  have hp := gm06Round_power_le Q (X.drawing.size + 2) 22
    ((Nat.add_le_add_right hsize 2).trans (gm06RoundBase_bounds Q).2.1) le_rfl
  have htime := ht.trans (Nat.mul_le_mul_left 4000 hp)
  have hq := gm06GapSingletonExhaust_queue_frame he'
  have hmul := Nat.mul_le_mul_left (2 * gm06TaskRecordBound Q)
    (Nat.add_le_add_right hwork (gm06TaskWork (M + 1) tasks))
  refine ⟨s', t, he', htime, ?_, ?_⟩
  · refine ⟨hY, hBY, hTasks, hin', hgap', hbuf.of_arr_eq hq,
      (gm06GapSingletonExhaust_driver_frame he' 7000 (by decide)).trans hpos,
      (gm06GapSingletonExhaust_driver_frame he' 7001 (by decide)).trans hend,
      (gm06GapSingletonExhaust_driver_frame he' 9000 (by decide)).trans hrun,
      (gm06GapSingletonExhaust_driver_frame he' 9004 (by decide)).trans hcap, ?_, ?_⟩
    · omega
    · exact hans.trans (and_congr hf Iff.rfl)
  · change _ + gm06TaskWork (M + 1) tasks ≤ _ + gm06TaskWork (M + 1) tasks
    omega

end GraphMinor.Compute
