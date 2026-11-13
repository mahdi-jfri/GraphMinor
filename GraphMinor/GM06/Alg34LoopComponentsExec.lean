module

public import GraphMinor.GM06.Alg34LoopBranchExec
public import GraphMinor.GM06.Alg34LoopDualExec
import GraphMinor.Compute.GM06Alg34GapBranchFrames
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Selecting the component or dual branch

Canonical root preparation retains the queue and the current input.
Its exact root count selects component branching when there are at
least two components. Otherwise the established dual execution applies.
Both branches preserve the answer and strictly reduce remaining work.
-/

public section
namespace GraphMinor.Compute
open GM06
universe u

/-- Component preparation followed by its actual count test preserves
 the driver invariant and strictly decreases its work. -/
theorem gm06Driver_components {M E Q : ℕ} {answer : Prop}
    {X : GM06GapInput} {past : List ℕ} {tasks : List GM06GapComponentTask} {s : State}
    (hInv : gm06DriverInvariant.{u} M E Q answer (.running X past tasks) s)
    (hn : 0 < X.drawing.n) (hI : X.drawing.findInteriorComponent = none)
    (hSing : gm06FindSingleton X.drawing.division = none)
    (hs : X.drawing.hasSplitBlock = false) :
    ∃ cfg' s' t, Exec (wordSize 256 Q) gm06DriverComponents s s' t ∧
      t ≤ 8400 * (gm06RoundBase Q) ^ 22 ∧ gm06DriverInvariant.{u} M E Q answer cfg' s' ∧
      cfg'.work (M + 1) < (GM06DriverConfig.running X past tasks).work (M + 1) := by
  obtain ⟨hX, hB, hTasks, hin, hgap, hbuf, hpos, hend, hrun, hcap, hbudget, hans⟩ := hInv
  have hsize := gm06LoopBounds_size hB
  obtain ⟨s₁, t₁, he₁, ht₁, hin₁, hmask, _, _, hcount⟩ :=
    gm06BranchRootsProg_exec X.drawing (c := 21) (by decide) hin
  have he₁' := he₁.mono_wordSize (gm06Uniform_wordSize Q _ hsize)
  have hInv₁ : gm06DriverInvariant.{u} M E Q answer (.running X past tasks) s₁ :=
    ⟨hX, hB, hTasks, hin₁, (gm06GapBranchRoots_array_frame he₁ 47 (by decide)).trans hgap,
      hbuf.of_arr_eq (gm06GapBranchRoots_array_frame he₁ 42 (by decide)),
      (gm06GapBranchRoots_register_frame he₁ 7000 (by decide)).trans hpos,
      (gm06GapBranchRoots_register_frame he₁ 7001 (by decide)).trans hend,
      (gm06GapBranchRoots_register_frame he₁ 9000 (by decide)).trans hrun,
      (gm06GapBranchRoots_register_frame he₁ 9004 (by decide)).trans hcap, hbudget, hans⟩
  have hw : 1 < 2 ^ wordSize 256 Q := lt_two_pow_wordSize_of_le (by decide) (by omega)
  have hkfit : X.drawing.componentRoots.length < 2 ^ wordSize 256 Q := by
    have hh := gm06VertexRootMask_sum_le X.drawing
    rw [gm06VertexRootMask_sum] at hh
    have hnQ := hB.2.2.1
    unfold GM06DrawingData.cellCount at hnQ
    exact (show X.drawing.componentRoots.length ≤ Q by omega).trans_lt
      (lt_two_pow_wordSize_of_le (by decide) (by omega))
  have htest := Crossing.eval_lt (Crossing.eval_const hw)
    (Crossing.eval_reg hcount hkfit) hw
  have hp := gm06Round_power_le Q (X.drawing.size + 1) 3
    (by have hh := (gm06RoundBase_bounds Q).2.1; omega) (by decide)
  have ht₁' := ht₁.trans (Nat.mul_le_mul_left 300 hp)
  have hpower : 1 ≤ (gm06RoundBase Q) ^ 22 := Nat.one_le_pow _ _ (gm06RoundBase_bounds Q).1
  by_cases hk : 2 ≤ X.drawing.componentRoots.length
  · obtain ⟨L, R, _, hR, _, _⟩ := gm06LoopInstance_layout hX
    obtain ⟨cfg', s', t₂, he₂, ht₂, hInv', hwork⟩ := gm06Driver_branch hInv₁ R hR hn hk hs hmask
    have hc : 1 < X.drawing.componentRoots.length := by omega
    simp only [hc, ↓reduceIte] at htest
    refine ⟨cfg', s', t₁ + (3 + t₂), .seq he₁' (.ite_true htest (by decide) he₂),
      by omega, hInv', hwork⟩
  · obtain ⟨s', t₂, he₂, ht₂, hInv', hwork⟩ := gm06Driver_dual hInv₁ hn hI hSing (by omega)
    have hc : ¬1 < X.drawing.componentRoots.length := by omega
    simp only [hc, ↓reduceIte] at htest
    refine ⟨_, s', t₁ + (3 + t₂), .seq he₁' (.ite_false htest he₂), by omega, hInv', hwork⟩

end GraphMinor.Compute
