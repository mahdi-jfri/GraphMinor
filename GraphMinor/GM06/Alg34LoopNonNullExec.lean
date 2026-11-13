module

public import GraphMinor.GM06.Alg34LoopResidualExec
public import GraphMinor.GM06.Alg34LoopInteriorExec
public import GraphMinor.GM06.Alg34LoopSplitExec

/-!
# All non-null reduction cases

The finite interior search and split test exhaust the cases of the
non-null command. Each successful execution retains the full invariant
and strictly lowers its remaining work, with one common time bound.
-/

public section
namespace GraphMinor.Compute
open GM06
universe u

/-- The non-null command always makes strict progress after singleton exhaustion. -/
theorem gm06Driver_nonNull {M E Q : ℕ} {answer : Prop}
    {X : GM06GapInput} {past : List ℕ} {tasks : List GM06GapComponentTask} {s : State}
    (hInv : gm06DriverInvariant.{u} M E Q answer (.running X past tasks) s)
    (hn : 0 < X.drawing.n) (hSing : gm06FindSingleton X.drawing.division = none) :
    ∃ cfg' s' t, Exec (wordSize 256 Q) gm06DriverNonNull s s' t ∧
      t ≤ 11000 * (gm06RoundBase Q) ^ 22 ∧ gm06DriverInvariant.{u} M E Q answer cfg' s' ∧
      cfg'.work (M + 1) < (GM06DriverConfig.running X past tasks).work (M + 1) := by
  cases hI : X.drawing.findInteriorComponent with
  | some a =>
    obtain ⟨s', t, he, ht, hi, hw⟩ := gm06Driver_interior hInv a hI
    exact ⟨_, s', t, he, ht.trans (Nat.mul_le_mul_right _ (by decide)), hi, hw⟩
  | none =>
    cases hs : X.drawing.hasSplitBlock with
    | false => exact gm06Driver_residual hInv hn hI hSing hs
    | true =>
      obtain ⟨s', t, he, ht, hi, hw⟩ := gm06Driver_split_reject hInv hI hs
      exact ⟨_, s', t, he, ht.trans (Nat.mul_le_mul_right _ (by decide)), hi, hw⟩

end GraphMinor.Compute
