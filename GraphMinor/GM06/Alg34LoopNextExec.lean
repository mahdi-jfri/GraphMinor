module

public import GraphMinor.GM06.Alg34LoopState
public import GraphMinor.Compute.GM06Alg34DriverNext

/-!
# Completing a null current problem and selecting the next task

A valid null current instance is feasible. If no record remains, the
saved answer is acceptance. Otherwise the next record's exact target
becomes current and its words join the consumed prefix. The conjunction
of answers is unchanged, and removing the completed problem strictly
lowers the total work charge while retaining the storage budget.
-/

public section
namespace GraphMinor.Compute

open GM06
universe u

/-- Completing a null problem preserves the queue invariant and strictly
lowers work, either by stopping or by selecting the next pending task. -/
theorem gm06Driver_next_null {M E Q : ℕ} {answer : Prop}
    {X : GM06GapInput} {past : List ℕ} {tasks : List GM06GapComponentTask} {s : State}
    (hInv : gm06DriverInvariant.{u} M E Q answer (.running X past tasks) s)
    (hn : X.drawing.n = 0) :
    ∃ cfg' s' t, Exec (wordSize 256 Q) gm06DriverNext s s' t ∧
      t ≤ 1703 * (gm06RoundBase Q) ^ 22 ∧ gm06DriverInvariant.{u} M E Q answer cfg' s' ∧
      cfg'.work (M + 1) < (GM06DriverConfig.running X past tasks).work (M + 1) := by
  obtain ⟨hX, hB, hTasks, hin, hgap, hbuf, hpos, hend, hrun, hcap, hbudget, hans⟩ := hInv
  have hf := gm06LoopInstance_null_feasible hX hn
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
        exact hans.mpr ⟨hf, by intro T hT; cases hT⟩
    · exact GM06DriverConfig.work_pos (M + 1) X past []
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
    have hwork : (GM06DriverConfig.running T.target (past ++ T.words) rest).work (M + 1) <
        (GM06DriverConfig.running X past (T :: rest)).work (M + 1) := by
      have hp := X.drawing.workWeight_pos (M + 1)
      simp only [GM06DriverConfig.work, gm06TaskWork_cons]
      omega
    have hmul := Nat.mul_le_mul_left (2 * gm06TaskRecordBound Q) hwork.le
    have hp := gm06Round_power_le Q (T.size + 2) 3
      ((Nat.add_le_add_right hTsize 2).trans (gm06RoundBase_bounds Q).2.2) (by decide)
    have htime := ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 1700 hp) 3)
    refine ⟨.running T.target (past ++ T.words) rest, s', t, he, by omega, ?_, hwork⟩
    refine ⟨hTGood, hTBounds, hPending, hin', hgap', ?_, ?_, ?_, hrun'.trans hrun, hcap'.trans hcap, ?_, ?_⟩
    · simpa only [IsPrefixBuffer, gm06TaskWords, List.flatMap_cons, List.append_assoc] using hbuf.of_arr_eq hqueue
    · simpa only [List.length_append] using hpos'
    · simpa only [gm06TaskWords, List.flatMap_cons, List.append_assoc] using hend'.trans hend
    · simp only [GM06DriverConfig.work, gm06TaskWork_cons] at hmul
      simp only [gm06TaskWords, List.flatMap_cons, List.length_append, gm06TaskWork_cons] at hbudget ⊢
      omega
    · constructor
      · intro ha
        have hh := hans.mp ha
        exact ⟨hh.2 T List.mem_cons_self, fun U hU => hh.2 U (List.mem_cons_of_mem T hU)⟩
      · rintro ⟨hTf, hrest⟩
        apply hans.mpr
        refine ⟨hf, ?_⟩
        intro U hU
        rcases List.mem_cons.mp hU with rfl | hU
        · exact hTf
        · exact hrest U hU

end GraphMinor.Compute
