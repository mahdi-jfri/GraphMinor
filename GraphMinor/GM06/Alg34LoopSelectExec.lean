module

public import GraphMinor.GM06.Alg34LoopState
public import GraphMinor.Compute.GM06Alg34DriverNext

/-!
# Selecting a pending problem after completing the current one

The queue stores all remaining independent problems. Its conjunction
of answers is the original answer. Decode the next record, or accept
if none remains. Selection moves a pending charge into the current
position, so the total remaining charge does not increase.
-/

public section
namespace GraphMinor.Compute

open GM06
universe u

/-- Selecting from a queue of remaining problems retains the full loop
invariant and does not increase its pending work charge. -/
theorem gm06Driver_select_tasks {M E Q : ℕ} {answer : Prop}
    {past : List ℕ} {tasks : List GM06GapComponentTask} {s : State}
    (hTasks : gm06PendingConditions.{u} M E Q tasks)
    (hbuf : IsPrefixBuffer 42 (past ++ gm06TaskWords tasks)
      ((Q + 2) ^ 16 - (past ++ gm06TaskWords tasks).length) s)
    (hpos : s.regs 7000 = past.length) (hend : s.regs 7001 = (past ++ gm06TaskWords tasks).length)
    (hrun : s.regs 9000 = 1) (hcap : s.regs 9004 = (Q + 2) ^ 16)
    (hbudget : (past ++ gm06TaskWords tasks).length +
      2 * gm06TaskRecordBound Q * gm06TaskWork (M + 1) tasks ≤ (Q + 2) ^ 16)
    (hans : answer ↔ ∀ T ∈ tasks, IsFeasible T.target.drawing.graph T.target.drawing.divisionSet) :
    ∃ cfg' s' t, Exec (wordSize 256 Q) gm06DriverNext s s' t ∧
      t ≤ 1703 * (gm06RoundBase Q) ^ 22 ∧ gm06DriverInvariant.{u} M E Q answer cfg' s' ∧
      cfg'.work (M + 1) ≤ gm06TaskWork (M + 1) tasks := by
  have hword := gm06Loop_capacity_lt Q
  have hused : (past ++ gm06TaskWords tasks).length ≤ (Q + 2) ^ 16 := by omega
  have hendw : s.regs 7001 < 2 ^ wordSize 256 Q := by rw [hend]; exact hused.trans_lt hword
  have hw1 : 1 < 2 ^ wordSize 256 Q := lt_two_pow_wordSize_of_le (by decide) (by omega)
  have hpower : 1 ≤ (gm06RoundBase Q) ^ 22 := Nat.one_le_pow _ _ (gm06RoundBase_bounds Q).1
  cases tasks with
  | nil =>
    have hend' : s.regs 7001 = past.length := by
      simpa only [gm06TaskWords, List.flatMap_nil, List.append_nil] using hend
    have heq : s.regs 7000 = s.regs 7001 := hpos.trans hend'.symm
    obtain ⟨s', he, hstop, hyes, _⟩ := gm06DriverNext_done_exec hw1 heq hendw
    refine ⟨.halted true, s', 7, he, by omega, ⟨hstop, hyes, ?_⟩, ?_⟩
    · constructor
      · intro _; rfl
      · intro _
        exact hans.mpr (by intro T hT; cases hT)
    · exact le_rfl
  | cons T rest =>
    obtain ⟨hLayout, hTGood, hTBounds⟩ := hTasks T List.mem_cons_self
    obtain ⟨L, hL, hlen, hparent, hTsize⟩ := hLayout
    have hWidth : wordSize 3 T.drawing.size ≤ wordSize 256 Q :=
      (wordSize_mono_left (by decide : 3 ≤ 21) _).trans (gm06Uniform_wordSize Q _ hparent)
    have hTword := hTsize.trans_lt (gm06TaskRecordBound_lt Q)
    have hTpos : 0 < T.words.length := by rw [T.words_length]; omega
    have hprefix : past.length + T.words.length ≤ (past ++ gm06TaskWords (T :: rest)).length := by
      simp only [gm06TaskWords, List.flatMap_cons, List.length_append]
      omega
    have hstream : AtStream 42 past.length
        (T.words ++ (gm06TaskWords rest ++ List.replicate
          ((Q + 2) ^ 16 - (past ++ gm06TaskWords (T :: rest)).length) 0)) s := by
      refine ⟨past, rfl, ?_⟩
      simpa only [IsPrefixBuffer, gm06TaskWords, List.flatMap_cons, List.append_assoc] using hbuf
    have hactive : past.length < s.regs 7001 := by rw [hend]; omega
    obtain ⟨s', t, he, ht, hin', hgap', hpos', _, hend', hrun', _, hcap'⟩ :=
      gm06DriverNext_task_exec T _ L hL hlen hWidth hTword
        (hprefix.trans hused |>.trans_lt hword) hstream hpos hactive hendw
    have hqueue : s'.arrs 42 = s.arrs 42 := he.arrs_eq_of_not_mem_writtenArrs (by decide)
    have hPending : gm06PendingConditions.{u} M E Q rest :=
      fun U hU => hTasks U (List.mem_cons_of_mem T hU)
    have hwork : (GM06DriverConfig.running T.target (past ++ T.words) rest).work (M + 1) =
        gm06TaskWork (M + 1) (T :: rest) := rfl
    have hp := gm06Round_power_le Q (T.size + 2) 3
      ((Nat.add_le_add_right hTsize 2).trans (gm06RoundBase_bounds Q).2.2) (by decide)
    have htime := ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 1700 hp) 3)
    refine ⟨.running T.target (past ++ T.words) rest, s', t, he, by omega, ?_, hwork.le⟩
    refine ⟨hTGood, hTBounds, hPending, hin', hgap', ?_, ?_, ?_, hrun'.trans hrun, hcap'.trans hcap, ?_, ?_⟩
    · simpa only [IsPrefixBuffer, gm06TaskWords, List.flatMap_cons, List.append_assoc] using hbuf.of_arr_eq hqueue
    · simpa only [List.length_append] using hpos'
    · simpa only [gm06TaskWords, List.flatMap_cons, List.append_assoc] using hend'.trans hend
    · simp only [gm06TaskWords, List.flatMap_cons, List.length_append, gm06TaskWork_cons] at hbudget ⊢
      omega
    · constructor
      · intro ha
        have hh := hans.mp ha
        exact ⟨hh T List.mem_cons_self, fun U hU => hh U (List.mem_cons_of_mem T hU)⟩
      · rintro ⟨hTf, hrest⟩
        apply hans.mpr
        intro U hU
        rcases List.mem_cons.mp hU with rfl | hU
        · exact hTf
        · exact hrest U hU

end GraphMinor.Compute
