module

public import GraphMinor.GM06.Alg34LoopTasks
public import GraphMinor.Compute.GM06Alg34DriverConfig
public import GraphMinor.Compute.GM06Alg34RoundBound
public import GraphMinor.Compute.Algorithm101Stream

/-!
# State invariant of the reduction driver

The current and pending finite problems retain the paper's geometric
conditions and the fixed numerical bounds. Queue words contain the
consumed prefix followed by the pending records and unused capacity.
Twice the remaining work pays for future appended records. Feasibility
of the original problem is the conjunction of the current and pending
answers, or the saved Boolean once the driver has stopped.
-/

@[expose] public section
namespace GraphMinor.Compute

open GM06
universe u

/-- Exact concatenation of pending parent/root packets. -/
def gm06TaskWords (tasks : List GM06GapComponentTask) : List ℕ :=
  tasks.flatMap GM06GapComponentTask.words

/-- Decoder conditions and intended bounded targets of all pending records. -/
def gm06PendingConditions (M E Q : ℕ) (tasks : List GM06GapComponentTask) : Prop :=
  ∀ T ∈ tasks, gm06TaskLayout Q T ∧ gm06LoopInstance.{u} T.target ∧ gm06LoopBounds M E Q T.target

/-- The conjunction of the current and pending finite feasibility answers. -/
def GM06DriverConfig.Feasible : GM06DriverConfig → Prop
  | .running X _ tasks => IsFeasible X.drawing.graph X.drawing.divisionSet ∧
      ∀ T ∈ tasks, IsFeasible T.target.drawing.graph T.target.drawing.divisionSet
  | .halted b => b = true

/-- The proof invariant of states reached by the reduction loop. Every
transition establishes these conditions from its preceding state. -/
def gm06DriverInvariant (M E Q : ℕ) (answer : Prop) : GM06DriverConfig → State → Prop
  | .running X past tasks, s =>
    gm06LoopInstance.{u} X ∧ gm06LoopBounds M E Q X ∧ gm06PendingConditions.{u} M E Q tasks ∧
    s.arrs 0 = X.drawing.words ∧ s.arrs 47 = X.discGapWords ∧
    IsPrefixBuffer 42 (past ++ gm06TaskWords tasks)
      ((Q + 2) ^ 16 - (past ++ gm06TaskWords tasks).length) s ∧
    s.regs 7000 = past.length ∧ s.regs 7001 = (past ++ gm06TaskWords tasks).length ∧
    s.regs 9000 = 1 ∧ s.regs 9004 = (Q + 2) ^ 16 ∧
    (past ++ gm06TaskWords tasks).length +
      2 * gm06TaskRecordBound Q * (X.drawing.workWeight (M + 1) + gm06TaskWork (M + 1) tasks) ≤
      (Q + 2) ^ 16 ∧
    (answer ↔ (GM06DriverConfig.running X past tasks).Feasible)
  | .halted b, s => s.regs 9000 = 0 ∧ s.regs 9001 = (if b then 1 else 0) ∧
    (answer ↔ (GM06DriverConfig.halted b).Feasible)

/-- Every running state invariant provides the unchanged running flag. -/
theorem gm06DriverInvariant_running_flag {M E Q : ℕ} {answer : Prop}
    {X : GM06GapInput} {past : List ℕ} {tasks : List GM06GapComponentTask} {s : State}
    (h : gm06DriverInvariant.{u} M E Q answer (.running X past tasks) s) : s.regs 9000 = 1 :=
  h.2.2.2.2.2.2.2.2.1

end GraphMinor.Compute
