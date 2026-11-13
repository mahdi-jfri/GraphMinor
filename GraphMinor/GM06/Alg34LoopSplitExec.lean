module

public import GraphMinor.GM06.Alg34LoopState
public import GraphMinor.Compute.GM06Alg34DriverStop
public import GraphMinor.Compute.GM06Alg34GapInteriorStep
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Split-block rejection in the complete non-null command

When interior search fails, the current input is retained. The split
scan returns zero exactly for a split block. VI (3.3)(iii), already
proved for the finite input, excludes feasibility. The driver therefore
saves rejection and stops, closing all remaining task work at once.
-/

public section
namespace GraphMinor.Compute

open GM06
universe u

/-- An exhausted interior search followed by a split block causes correct
rejection, with uniform polynomial time and strictly smaller work. -/
theorem gm06Driver_split_reject {M E Q : ℕ} {answer : Prop}
    {X : GM06GapInput} {past : List ℕ} {tasks : List GM06GapComponentTask} {s : State}
    (hInv : gm06DriverInvariant.{u} M E Q answer (.running X past tasks) s)
    (hI : X.drawing.findInteriorComponent = none) (hSplit : X.drawing.hasSplitBlock = true) :
    ∃ s' t, Exec (wordSize 256 Q) gm06DriverNonNull s s' t ∧
      t ≤ 2600 * (gm06RoundBase Q) ^ 22 ∧
      gm06DriverInvariant.{u} M E Q answer (.halted false) s' ∧
      (GM06DriverConfig.halted false).work (M + 1) <
        (GM06DriverConfig.running X past tasks).work (M + 1) := by
  obtain ⟨hX, hB, _, hin, hgap, _, _, _, _, _, _, hans⟩ := hInv
  have hsize := gm06LoopBounds_size hB
  obtain ⟨L, R, hL, hR, hlen, _⟩ := gm06LoopInstance_layout hX
  have hw : 1 < 2 ^ wordSize 256 Q := lt_two_pow_wordSize_of_le (by decide) (by omega)
  obtain ⟨s₁, t₁, he₁, ht₁, hi₁, _, hflag₁, _⟩ :=
    gm06GapInteriorStepProg_exec X ⟨L, R, hL, hR, hlen⟩ (c := 21) (by decide) hin hgap
  have he₁' := he₁.mono_wordSize (gm06Uniform_wordSize Q _ hsize)
  simp only [GM06GapInput.interiorStepData, hI, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hi₁ hflag₁
  obtain ⟨s₂, t₂, he₂, ht₂, hflag₂, _, _, _, _⟩ := gm06SplitProg_exec X.drawing hL (c := 21) (by decide) hi₁
  have he₂' := he₂.mono_wordSize (gm06Uniform_wordSize Q _ hsize)
  have hzero : s₂.regs 263 = 0 := by
    simpa only [hSplit, Bool.not_true, Bool.false_eq_true, ↓reduceIte] using hflag₂
  obtain ⟨s', he₃, hstop, hans', _, _⟩ := gm06DriverStop_exec hw false s₂
  have hinner : Exec (wordSize 256 Q)
      (.ite (.reg 263) gm06DriverComponents (gm06DriverStop false)) s₂ s' 5 :=
    .ite_false (Crossing.eval_reg hzero (Nat.two_pow_pos _)) he₃
  have houter : Exec (wordSize 256 Q)
      (.ite (.reg 6600) .skip (.seq gm06SplitProg (.ite (.reg 263) gm06DriverComponents (gm06DriverStop false))))
      s₁ s' (1 + (t₂ + 5)) :=
    .ite_false (Crossing.eval_reg hflag₁ (Nat.two_pow_pos _)) (.seq he₂' hinner)
  have hp₁ := gm06Round_power_le Q (X.drawing.size + 2) 3
    ((Nat.add_le_add_right hsize 2).trans (gm06RoundBase_bounds Q).2.1) (by decide)
  have hp₂ := gm06Round_power_le Q (X.drawing.size + 1) 3
    (by have hh := (gm06RoundBase_bounds Q).2.1; omega) (by decide)
  have ht₁' := ht₁.trans (Nat.mul_le_mul_left 2000 hp₁)
  have ht₂' := ht₂.trans (Nat.mul_le_mul_left 500 hp₂)
  have hpower : 1 ≤ (gm06RoundBase Q) ^ 22 := Nat.one_le_pow _ _ (gm06RoundBase_bounds Q).1
  refine ⟨s', t₁ + (1 + (t₂ + 5)), .seq he₁' houter, by omega, ⟨hstop, hans', ?_⟩,
    GM06DriverConfig.work_pos (M + 1) X past tasks⟩
  constructor
  · intro ha
    exact False.elim (X.drawing.not_feasible_of_hasSplitBlock hSplit (hans.mp ha).1)
  · intro hf
    cases hf

end GraphMinor.Compute
