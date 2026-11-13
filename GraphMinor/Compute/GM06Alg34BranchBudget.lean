module

public import GraphMinor.Compute.GM06Alg34RoundBound

/-!
# Cumulative queue budget after appending a branch

The exact component charge decrease pays for the new records. Add the
unchanged pending work to both sides of that payment inequality. This
retains the cumulative storage bound after appending all children. A
small arithmetic bound also pays for the enqueue scan in one round.
-/

public section
namespace GraphMinor.Compute

/-- Appending a component branch retains the cumulative queue storage inequality. -/
theorem gm06Branch_queue_budget (M Q used cap : ℕ) (x : GM06DrawingData)
    (R : List (Fin x.regions.length)) (tasks : List GM06GapComponentTask)
    (hk : 2 ≤ x.componentRoots.length) (hs : x.size ≤ 40 * (Q + 2) ^ 2) (hR : R.length ≤ Q)
    (hbudget : used + 2 * gm06TaskRecordBound Q * (x.workWeight (M + 1) + gm06TaskWork (M + 1) tasks) ≤ cap) :
    used + ((gm06GapComponentTasks x R).flatMap GM06GapComponentTask.words).length +
      2 * gm06TaskRecordBound Q *
        gm06TaskWork (M + 1) (tasks ++ gm06GapComponentTasks x R) ≤ cap := by
  have hpay := gm06ComponentTasks_storage_payment (M + 1) (gm06TaskRecordBound Q) x R hk
    (gm06ComponentTasks_words_le Q x R hs hR)
  rw [gm06TaskWork_append, Nat.mul_add]
  rw [Nat.mul_add] at hbudget
  omega

/-- The round base bounds the original count bound itself. -/
theorem gm06RoundBase_ge_count (Q : ℕ) : Q ≤ gm06RoundBase Q := by
  have h := (gm06RoundBase_bounds Q).2.1
  have hq : Q ≤ 40 * (Q + 2) ^ 2 + 2 := by
    ring_nf
    omega
  exact hq.trans h

/-- The enqueue scan fits a fixed multiple of the common round power. -/
theorem gm06Enqueue_time_le_round (Q S K N t : ℕ)
    (hS : S + K + 4 ≤ gm06RoundBase Q) (hN : N ≤ gm06RoundBase Q)
    (ht : t ≤ (20 * (S + K + 4) + 11) * N + 5) :
    t ≤ 36 * (gm06RoundBase Q) ^ 22 := by
  have hbase := (gm06RoundBase_bounds Q).1
  have h₁ : gm06RoundBase Q ≤ (gm06RoundBase Q) ^ 22 := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right hbase (by decide : 1 ≤ 22)
  have h₂ : (gm06RoundBase Q) ^ 2 ≤ (gm06RoundBase Q) ^ 22 :=
    Nat.pow_le_pow_right hbase (by decide : 2 ≤ 22)
  have hp : 1 ≤ (gm06RoundBase Q) ^ 22 := Nat.one_le_pow _ _ hbase
  have hprod := Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 20 hS) 11) hN
  ring_nf at hprod ht
  omega

end GraphMinor.Compute
