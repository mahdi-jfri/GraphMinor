module

public import GraphMinor.Compute.GM06Alg34TaskWork
public import GraphMinor.Compute.GM06Alg34UniformSize
import Mathlib.Tactic.Ring

/-!
# Uniform bounds for task records and the reserved queue

Each record stores a bounded parent drawing, one cuff's gap labels and
its root. The initial work charge is quadratic. Twice their product
fits the sixteenth-power queue reservation. Combined with storage
payment at every branch, this bounds all appended words, including
records already consumed from the queue.
-/

public section
namespace GraphMinor.Compute

/-- A uniform upper bound on one saved parent/root record. -/
def gm06TaskRecordBound (Q : ℕ) : ℕ := 44 * (Q + 2) ^ 2

/-- The record budget is a fixed quadratic polynomial in the supplied size. -/
theorem gm06TaskRecordBound_value (Q : ℕ) : gm06TaskRecordBound Q = 44 * (Q + 2) ^ 2 := by
  unfold gm06TaskRecordBound
  rfl

private theorem record_budget (Q : ℕ) :
    40 * (Q + 2) ^ 2 + Q + 3 ≤ gm06TaskRecordBound Q := by
  unfold gm06TaskRecordBound
  ring_nf
  omega

/-- A task with a uniformly bounded parent and gap list fits one record budget. -/
theorem gm06Task_size_le_recordBound (Q : ℕ) (x : GM06DrawingData)
    (R : List (Fin x.regions.length)) (a : Fin x.n)
    (hs : x.size ≤ 40 * (Q + 2) ^ 2) (hR : R.length ≤ Q) :
    (⟨x, R, a⟩ : GM06GapComponentTask).size ≤ gm06TaskRecordBound Q := by
  rw [gm06GapTask_size]
  exact (show x.size + R.length + 3 ≤ 40 * (Q + 2) ^ 2 + Q + 3 by omega).trans (record_budget Q)

/-- The complete branch appends at most one record budget per canonical root. -/
theorem gm06ComponentTasks_words_le (Q : ℕ) (x : GM06DrawingData)
    (R : List (Fin x.regions.length))
    (hs : x.size ≤ 40 * (Q + 2) ^ 2) (hR : R.length ≤ Q) :
    ((gm06GapComponentTasks x R).flatMap GM06GapComponentTask.words).length ≤
      x.componentRoots.length * gm06TaskRecordBound Q := by
  rw [← gm06GapTaskQueueWords_eq_tasks, gm06GapTaskQueueWords_length]
  have hwords : x.words.length + R.length + 3 ≤ gm06TaskRecordBound Q :=
    (show x.words.length + R.length + 3 ≤ 40 * (Q + 2) ^ 2 + Q + 3 from
      by have hw := x.words_length_le_size; omega).trans (record_budget Q)
  exact Nat.mul_le_mul_left x.componentRoots.length hwords

/-- Count bounds on an initial problem give a quadratic work charge. -/
theorem gm06WorkWeight_le_quadratic (Q C : ℕ) (x : GM06DrawingData)
    (hn : x.n ≤ Q) (he : x.ends.length ≤ Q) (hC : C ≤ Q + 1) :
    x.workWeight C ≤ 3 * (Q + 2) ^ 2 := by
  have hm := Nat.mul_le_mul hC he
  have hmass : x.workMass C ≤ Q + (Q + 1) * Q := by
    unfold GM06DrawingData.workMass
    omega
  have hbudget : Q + (Q + 1) * Q ≤ (Q + 2) ^ 2 := by ring_nf; omega
  have hsq : 1 ≤ (Q + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  unfold GM06DrawingData.workWeight
  split <;> omega

/-- The queue reservation contains twice the record budget times the initial work charge. -/
theorem gm06Queue_capacity_bound (Q W : ℕ) (hW : W ≤ 3 * (Q + 2) ^ 2) :
    2 * gm06TaskRecordBound Q * W ≤ (Q + 2) ^ 16 := by
  have h264 : 264 ≤ (Q + 2) ^ 12 :=
    (by decide : 264 ≤ 2 ^ 12).trans (Nat.pow_le_pow_left (by omega : 2 ≤ Q + 2) 12)
  have hp := Nat.mul_le_mul_left ((Q + 2) ^ 4) h264
  rw [← Nat.pow_add] at hp
  have hp' : 264 * (Q + 2) ^ 4 ≤ (Q + 2) ^ 16 := by
    simpa only [Nat.mul_comm] using hp
  calc
    2 * gm06TaskRecordBound Q * W ≤
        2 * gm06TaskRecordBound Q * (3 * (Q + 2) ^ 2) := Nat.mul_le_mul_left _ hW
    _ = 264 * (Q + 2) ^ 4 := by unfold gm06TaskRecordBound; ring
    _ ≤ (Q + 2) ^ 16 := hp'

end GraphMinor.Compute
