module

public import GraphMinor.GM06.Alg34LoopSelectExec
public import GraphMinor.Compute.GM06Alg34BranchBudget
public import GraphMinor.Compute.GM06Alg34GapTaskEnqueue
public import GraphMinor.Compute.GM06Alg34DriverControlFrames

/-!
# Appending component tasks and selecting the next problem

The split-free parent answer is the conjunction of its component
answers. Append the exact canonical parent/root records to the pending
queue. Their charge loss pays for all new words. Selecting the next
record then preserves the conjunction and cannot increase the remaining
charge, so the full branch strictly lowers the driver's work potential.
-/

public section
namespace GraphMinor.Compute

open GM06
universe u

/-- With the canonical mask prepared, component enqueue and selection
preserve the full invariant and strictly lower the total remaining work. -/
theorem gm06Driver_branch {M E Q : ℕ} {answer : Prop}
    {X : GM06GapInput} {past : List ℕ} {tasks : List GM06GapComponentTask} {s : State}
    (hInv : gm06DriverInvariant.{u} M E Q answer (.running X past tasks) s)
    (R : List (Fin X.drawing.regions.length)) (hgroups : X.gapRegions = [R])
    (hn : 0 < X.drawing.n) (hk : 2 ≤ X.drawing.componentRoots.length)
    (hs : X.drawing.hasSplitBlock = false) (hmask : s.arrs 40 = gm06VertexRootMask X.drawing) :
    ∃ cfg' s' t, Exec (wordSize 256 Q) (.seq gm06GapTaskEnqueueProg gm06DriverNext) s s' t ∧
      t ≤ 1800 * (gm06RoundBase Q) ^ 22 ∧ gm06DriverInvariant.{u} M E Q answer cfg' s' ∧
      cfg'.work (M + 1) < (GM06DriverConfig.running X past tasks).work (M + 1) := by
  obtain ⟨hX, hB, hTasks, hin, hgap, hbuf, hpos, hend, hrun, hcap, hbudget, hans⟩ := hInv
  let children := gm06GapComponentTasks X.drawing R
  let pfx := past ++ gm06TaskWords tasks
  let free := (Q + 2) ^ 16 - (pfx.length + (gm06TaskWords children).length)
  have hsize := gm06LoopBounds_size hB
  have hnQ : X.drawing.n ≤ Q := by
    have hc := hB.2.2.1
    unfold GM06DrawingData.cellCount at hc
    omega
  have hRlen : R.length ≤ Q := by
    have hh := gm06LoopInstance_gap_length hX
    rw [X.discGapWords_singleton R hgroups, List.length_map] at hh
    exact hh.trans hnQ
  have hRecord := gm06Task_size_le_recordBound Q X.drawing R ⟨0, hn⟩ hsize hRlen
  rw [gm06GapTask_size] at hRecord
  have hwrite : pfx.length + (gm06TaskWords children).length +
      2 * gm06TaskRecordBound Q * gm06TaskWork (M + 1) (tasks ++ children) ≤ (Q + 2) ^ 16 :=
    gm06Branch_queue_budget M Q pfx.length _ X.drawing R tasks hk hsize hRlen hbudget
  have hused : pfx.length ≤ (Q + 2) ^ 16 := by omega
  have hnewused : pfx.length + (gm06TaskWords children).length ≤ (Q + 2) ^ 16 := by omega
  have hfree : (Q + 2) ^ 16 - pfx.length = (gm06TaskWords children).length + free := by
    dsimp only [free]
    omega
  have hbuf' : IsPrefixBuffer 42 pfx ((gm06TaskWords children).length + free) s := by
    rw [← hfree]
    exact hbuf
  have hw : 1 < 2 ^ wordSize 256 Q := lt_two_pow_wordSize_of_le (by decide) (by omega)
  obtain ⟨s₁, t₁, he₁, ht₁, hb₁, hend₁, _, _, _, hg₁⟩ :=
    gm06GapTaskEnqueueProg_exec X.drawing R hw
      (hRecord.trans_lt (gm06TaskRecordBound_lt Q)) hin
      (hgap.trans (X.discGapWords_singleton R hgroups)) hmask
      (hnewused.trans_lt (gm06Loop_capacity_lt Q)) hbuf' hend
  have hWordEq : past ++ gm06TaskWords (tasks ++ children) = pfx ++ gm06TaskWords children := by
    simp only [gm06TaskWords, List.flatMap_append, List.append_assoc, pfx]
  have hTasks' : gm06PendingConditions.{u} M E Q (tasks ++ children) := by
    intro T hT
    rcases List.mem_append.mp hT with hT | hT
    · exact hTasks T hT
    · exact gm06LoopInstance_tasks hX hB R hgroups T hT
  have hbuf₁ : IsPrefixBuffer 42 (past ++ gm06TaskWords (tasks ++ children))
      ((Q + 2) ^ 16 - (past ++ gm06TaskWords (tasks ++ children)).length) s₁ := by
    rw [hWordEq]
    simpa only [free, List.length_append, gm06TaskWords, children] using hb₁
  have hpos₁ : s₁.regs 7000 = past.length :=
    (hg₁ 7000 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hpos
  have hend₁' : s₁.regs 7001 = (past ++ gm06TaskWords (tasks ++ children)).length := by
    rw [hWordEq]
    exact hend₁
  have hbudget₁ : (past ++ gm06TaskWords (tasks ++ children)).length +
      2 * gm06TaskRecordBound Q * gm06TaskWork (M + 1) (tasks ++ children) ≤ (Q + 2) ^ 16 := by
    rw [hWordEq, List.length_append]
    exact hwrite
  have hf := gm06LoopInstance_tasks_feasible_iff hX R hgroups hs hk
  have hans₁ : answer ↔ ∀ T ∈ tasks ++ children,
      IsFeasible T.target.drawing.graph T.target.drawing.divisionSet := by
    constructor
    · intro ha T hT
      have hh := hans.mp ha
      rcases List.mem_append.mp hT with hT | hT
      · exact hh.2 T hT
      · exact hf.mp hh.1 T hT
    · intro hh
      apply hans.mpr
      exact ⟨hf.mpr (fun T hT => hh T (List.mem_append_right tasks hT)),
        fun T hT => hh T (List.mem_append_left children hT)⟩
  obtain ⟨cfg', s', t₂, he₂, ht₂, hInv', hwork⟩ := gm06Driver_select_tasks hTasks' hbuf₁ hpos₁ hend₁'
    ((gm06GapTaskEnqueue_driver_frame he₁ 9000 (by decide)).trans hrun)
    ((gm06GapTaskEnqueue_driver_frame he₁ 9004 (by decide)).trans hcap) hbudget₁ hans₁
  have hsmall : gm06TaskWork (M + 1) (tasks ++ children) <
      (GM06DriverConfig.running X past tasks).work (M + 1) := by
    have hc := gm06ComponentTasks_work_lt (M + 1) X.drawing R hk
    rw [gm06TaskWork_append]
    change gm06TaskWork (M + 1) tasks + gm06TaskWork (M + 1) children <
      X.drawing.workWeight (M + 1) + gm06TaskWork (M + 1) tasks
    exact Nat.add_lt_add_left hc _ |>.trans_eq (Nat.add_comm _ _)
  have hb := (gm06RoundBase_bounds Q).2.2
  have htime₁ := gm06Enqueue_time_le_round Q X.drawing.size R.length X.drawing.n t₁
    (by omega) (hnQ.trans (gm06RoundBase_ge_count Q)) ht₁
  refine ⟨cfg', s', t₁ + t₂, .seq he₁ he₂, by omega, hInv', hwork.trans_lt hsmall⟩

end GraphMinor.Compute
