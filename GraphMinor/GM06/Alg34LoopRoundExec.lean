module

public import GraphMinor.GM06.Alg34LoopNonNullExec
public import GraphMinor.GM06.Alg34LoopSingletonExec
public import GraphMinor.GM06.Alg34LoopNextExec
import GraphMinor.Compute.GM06Alg34DriverHeader

/-!
# One full round of the disc algorithm

Exhaust singleton deletions first. The resulting vertex header selects
completion or the non-null cases. Singleton exhaustion cannot increase
work, and the selected case strictly decreases it. The sum of their
costs fits the common round bound.
-/

public section
namespace GraphMinor.Compute
open GM06
universe u

/-- Every running round preserves the answer invariant and strictly
lowers the total work, within the uniform round time bound. -/
theorem gm06Driver_round {M E Q : ℕ} {answer : Prop}
    {X : GM06GapInput} {past : List ℕ} {tasks : List GM06GapComponentTask} {s : State}
    (hInv : gm06DriverInvariant.{u} M E Q answer (.running X past tasks) s) :
    ∃ cfg' s' t, Exec (wordSize 256 Q) gm06DriverBody s s' t ∧
      t ≤ gm06RoundBound Q ∧ gm06DriverInvariant.{u} M E Q answer cfg' s' ∧
      cfg'.work (M + 1) < (GM06DriverConfig.running X past tasks).work (M + 1) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hInv₁, hw₁⟩ := gm06Driver_singletons hInv
  let Y := gm06GapReduceSingletons X
  have hSing := gm06GapReduceSingletons_find_none X
  have hB := hInv₁.2.1
  have hnQ : Y.drawing.n ≤ Q := by
    have hh := hB.2.2.1
    change Y.drawing.cellCount ≤ Q at hh
    unfold GM06DrawingData.cellCount at hh
    omega
  have hfit : Y.drawing.n < 2 ^ wordSize 256 Q := hnQ.trans_lt
    (lt_two_pow_wordSize_of_le (by decide) (by omega))
  have htest := gm06Driver_vertex_eval Y.drawing hInv₁.2.2.2.1 hfit
  have hpower : 1 ≤ (gm06RoundBase Q) ^ 22 := Nat.one_le_pow _ _ (gm06RoundBase_bounds Q).1
  by_cases hn : Y.drawing.n = 0
  · obtain ⟨cfg', s', t₂, he₂, ht₂, hi, hw⟩ := gm06Driver_next_null hInv₁ hn
    rw [hn] at htest
    refine ⟨cfg', s', t₁ + (2 + t₂), .seq he₁ (.ite_false htest he₂), ?_, hi,
      hw.trans_le hw₁⟩
    unfold gm06RoundBound
    omega
  · obtain ⟨cfg', s', t₂, he₂, ht₂, hi, hw⟩ := gm06Driver_nonNull hInv₁ (show 0 < Y.drawing.n by omega) hSing
    refine ⟨cfg', s', t₁ + (2 + t₂), .seq he₁ (.ite_true htest hn he₂), ?_, hi,
      hw.trans_le hw₁⟩
    unfold gm06RoundBound
    omega

end GraphMinor.Compute
