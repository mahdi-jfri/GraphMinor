module

public import GraphMinor.Compute.GM06Alg34TaskWork

/-!
# Finite configurations of the reduction queue

A running configuration records the current finite input, consumed
queue words and pending component records. A stopped configuration
records its Boolean answer. These are finite data only. The sum of
current and pending work charges is the potential used to bound the
number of driver passes.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The finite current problem and work queue, or a saved final answer. -/
inductive GM06DriverConfig where
  | running (input : GM06GapInput) (past : List ℕ) (tasks : List GM06GapComponentTask)
  | halted (answer : Bool)

/-- Sum of the current and pending problem charges, with zero charge after stopping. -/
def GM06DriverConfig.work (C : ℕ) : GM06DriverConfig → ℕ
  | .running X _ tasks => X.drawing.workWeight C + gm06TaskWork C tasks
  | .halted _ => 0

/-- Every running configuration has positive work. -/
theorem GM06DriverConfig.work_pos (C : ℕ) (X : GM06GapInput)
    (past : List ℕ) (tasks : List GM06GapComponentTask) :
    0 < (GM06DriverConfig.running X past tasks).work C := by
  have hp := X.drawing.workWeight_pos C
  change 0 < X.drawing.workWeight C + gm06TaskWork C tasks
  omega

end GraphMinor.Compute
