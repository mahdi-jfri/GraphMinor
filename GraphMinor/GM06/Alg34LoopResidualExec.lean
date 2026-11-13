module

public import GraphMinor.GM06.Alg34LoopComponentsExec
import GraphMinor.Compute.GM06Alg34InteriorDriverFrames
import GraphMinor.Compute.CrossingOpsBasic

/-!
# The residual non-null case

When neither an interior component nor a split block is found, both
searches leave the current drawing intact. Their memory frames retain
the pending queue. The component count then chooses the proved branch.
-/

public section
namespace GraphMinor.Compute
open GM06
universe u

/-- A stuck split-free input proceeds to the component or dual branch. -/
theorem gm06Driver_residual {M E Q : ℕ} {answer : Prop}
    {X : GM06GapInput} {past : List ℕ} {tasks : List GM06GapComponentTask} {s : State}
    (hInv : gm06DriverInvariant.{u} M E Q answer (.running X past tasks) s)
    (hn : 0 < X.drawing.n) (hI : X.drawing.findInteriorComponent = none)
    (hSing : gm06FindSingleton X.drawing.division = none)
    (hs : X.drawing.hasSplitBlock = false) :
    ∃ cfg' s' t, Exec (wordSize 256 Q) gm06DriverNonNull s s' t ∧
      t ≤ 11000 * (gm06RoundBase Q) ^ 22 ∧ gm06DriverInvariant.{u} M E Q answer cfg' s' ∧
      cfg'.work (M + 1) < (GM06DriverConfig.running X past tasks).work (M + 1) := by
  obtain ⟨hX, hB, hTasks, hin, hgap, hbuf, hpos, hend, hrun, hcap, hbudget, hans⟩ := hInv
  have hsize := gm06LoopBounds_size hB
  obtain ⟨L, R, hL, hR, hlen, _⟩ := gm06LoopInstance_layout hX
  have hw : 1 < 2 ^ wordSize 256 Q := lt_two_pow_wordSize_of_le (by decide) (by omega)
  obtain ⟨s₁, t₁, he₁, ht₁, hi₁, hg₁, hflag₁, _⟩ :=
    gm06GapInteriorStepProg_exec X ⟨L, R, hL, hR, hlen⟩ (c := 21) (by decide) hin hgap
  have he₁' := he₁.mono_wordSize (gm06Uniform_wordSize Q _ hsize)
  simp only [GM06GapInput.interiorStepData, hI, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hi₁ hg₁ hflag₁
  obtain ⟨s₂, t₂, he₂, ht₂, hflag₂, hi₂, _, _, _⟩ :=
    gm06SplitProg_exec X.drawing hL (c := 21) (by decide) hi₁
  have he₂' := he₂.mono_wordSize (gm06Uniform_wordSize Q _ hsize)
  have hone : s₂.regs 263 = 1 := by
    simpa only [hs, Bool.not_false, ↓reduceIte] using hflag₂
  have hInv₂ : gm06DriverInvariant.{u} M E Q answer (.running X past tasks) s₂ :=
    ⟨hX, hB, hTasks, hi₂, (gm06Split_queue_gap_frame he₂ 47 (by decide)).trans hg₁,
      hbuf.of_arr_eq ((gm06Split_queue_gap_frame he₂ 42 (by decide)).trans
        (gm06GapInteriorStep_queue_frame he₁)),
      ((gm06Split_driver_frame he₂ 7000 (by decide)).trans
        (gm06GapInteriorStep_driver_frame he₁ 7000 (by decide))).trans hpos,
      ((gm06Split_driver_frame he₂ 7001 (by decide)).trans
        (gm06GapInteriorStep_driver_frame he₁ 7001 (by decide))).trans hend,
      ((gm06Split_driver_frame he₂ 9000 (by decide)).trans
        (gm06GapInteriorStep_driver_frame he₁ 9000 (by decide))).trans hrun,
      ((gm06Split_driver_frame he₂ 9004 (by decide)).trans
        (gm06GapInteriorStep_driver_frame he₁ 9004 (by decide))).trans hcap,
      hbudget, hans⟩
  obtain ⟨cfg', s', t₃, he₃, ht₃, hInv', hwork⟩ := gm06Driver_components hInv₂ hn hI hSing hs
  have hi : Exec (wordSize 256 Q)
      (.ite (.reg 263) gm06DriverComponents (gm06DriverStop false)) s₂ s' (1 + t₃) :=
    .ite_true (Crossing.eval_reg hone hw) (by decide) he₃
  have ho : Exec (wordSize 256 Q)
      (.ite (.reg 6600) .skip (.seq gm06SplitProg
        (.ite (.reg 263) gm06DriverComponents (gm06DriverStop false)))) s₁ s' (1 + (t₂ + (1 + t₃))) :=
    .ite_false (Crossing.eval_reg hflag₁ (Nat.two_pow_pos _)) (.seq he₂' hi)
  have hp₁ := gm06Round_power_le Q (X.drawing.size + 2) 3
    ((Nat.add_le_add_right hsize 2).trans (gm06RoundBase_bounds Q).2.1) (by decide)
  have hp₂ := gm06Round_power_le Q (X.drawing.size + 1) 3
    (by have hh := (gm06RoundBase_bounds Q).2.1; omega) (by decide)
  have ht₁' := ht₁.trans (Nat.mul_le_mul_left 2000 hp₁)
  have ht₂' := ht₂.trans (Nat.mul_le_mul_left 500 hp₂)
  have hpower : 1 ≤ (gm06RoundBase Q) ^ 22 := Nat.one_le_pow _ _ (gm06RoundBase_bounds Q).1
  exact ⟨cfg', s', _, .seq he₁' ho, by omega, hInv', hwork⟩

end GraphMinor.Compute
