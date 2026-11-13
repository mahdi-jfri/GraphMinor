module

public import GraphMinor.Compute.GM06Alg34GapTaskQueueData
public import GraphMinor.Compute.GM06Alg34WorkWeight
import Mathlib.Tactic.Ring

/-!
# Work and storage charged to component tasks

Materialized task targets are exactly the canonical component inputs.
Their additive charge is therefore the component charge already proved.
Each appended record has a fixed parent-dependent length. A branch with
at least two children can pay for all of these words from twice its
charge decrease, since the number of children is at most twice one
less than that number.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The total future work charge of queued component records. -/
def gm06TaskWork (C : ℕ) (tasks : List GM06GapComponentTask) : ℕ :=
  (tasks.map (fun T => T.target.drawing.workWeight C)).sum

/-- Queue charge is additive under task concatenation. -/
theorem gm06TaskWork_append (C : ℕ) (A B : List GM06GapComponentTask) :
    gm06TaskWork C (A ++ B) = gm06TaskWork C A + gm06TaskWork C B := by
  simp only [gm06TaskWork, List.map_append, List.sum_append]

/-- Popping a task moves its charge to the current problem. -/
theorem gm06TaskWork_cons (C : ℕ) (T : GM06GapComponentTask) (tasks : List GM06GapComponentTask) :
    gm06TaskWork C (T :: tasks) = T.target.drawing.workWeight C + gm06TaskWork C tasks := rfl

/-- Branch task targets have the exact previously proved component charge. -/
theorem gm06ComponentTasks_work (C : ℕ) (x : GM06DrawingData)
    (R : List (Fin x.regions.length)) :
    gm06TaskWork C (gm06GapComponentTasks x R) + x.componentRoots.length = 3 * x.workMass C := by
  simp only [gm06TaskWork, gm06GapComponentTasks, List.map_map]
  change (x.componentRoots.map (fun a => (x.componentData a).workWeight C)).sum +
    x.componentRoots.length = _
  exact x.componentData_sum_workWeight C

/-- At least two component tasks strictly lower the remaining work. -/
theorem gm06ComponentTasks_work_lt (C : ℕ) (x : GM06DrawingData)
    (R : List (Fin x.regions.length)) (hk : 2 ≤ x.componentRoots.length) :
    gm06TaskWork C (gm06GapComponentTasks x R) < x.workWeight C := by
  simp only [gm06TaskWork, gm06GapComponentTasks, List.map_map]
  change (x.componentRoots.map (fun a => (x.componentData a).workWeight C)).sum < _
  exact x.componentData_workWeight_lt C hk

private theorem branch_payment (R k old next : ℕ) (hk : 2 ≤ k)
    (hwork : next + k = old + 1) : k * R + 2 * R * next ≤ 2 * R * old := by
  have hle : k + 2 * next ≤ 2 * old := by omega
  calc
    k * R + 2 * R * next = R * (k + 2 * next) := by ring
    _ ≤ R * (2 * old) := Nat.mul_le_mul_left R hle
    _ = 2 * R * old := by ring

/-- Twice the component charge decrease pays for one bounded record per child. -/
theorem gm06ComponentTasks_storage_payment (C B : ℕ) (x : GM06DrawingData)
    (R : List (Fin x.regions.length)) (hk : 2 ≤ x.componentRoots.length)
    (hwords : ((gm06GapComponentTasks x R).flatMap GM06GapComponentTask.words).length ≤
      x.componentRoots.length * B) :
    ((gm06GapComponentTasks x R).flatMap GM06GapComponentTask.words).length +
      2 * B * gm06TaskWork C (gm06GapComponentTasks x R) ≤ 2 * B * x.workWeight C := by
  have hn : x.n ≠ 0 := by
    cases hh : x.componentRoots with
    | nil => simp only [hh, List.length_nil] at hk; omega
    | cons a L => have ha := a.isLt; omega
  have hh := gm06ComponentTasks_work C x R
  have hw : x.workWeight C + 1 = 3 * x.workMass C := by
    have hp : 0 < x.workMass C := by unfold GM06DrawingData.workMass; omega
    change (if x.n = 0 then 1 else 3 * x.workMass C - 1) + 1 = _
    rw [ite_eq_right hn]
    omega
  have hh' : gm06TaskWork C (gm06GapComponentTasks x R) + x.componentRoots.length =
      x.workWeight C + 1 := hh.trans hw.symm
  have hpay := branch_payment B x.componentRoots.length (x.workWeight C)
    (gm06TaskWork C (gm06GapComponentTasks x R)) hk hh'
  omega

end GraphMinor.Compute
