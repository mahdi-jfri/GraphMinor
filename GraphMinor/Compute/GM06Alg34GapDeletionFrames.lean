module

public import GraphMinor.Compute.GM06Alg34DeletionPrepare

/-!
# Gap metadata preserved by deletion preparation

The existing deletion preparation writes neither the supplied cuff
copy nor the external gap array. Its last command computes root ranks.
Recover that exact rank-table postcondition from the command's final
root-mask postcondition and determinism of RAM execution.
-/

public section
namespace GraphMinor.Compute

private theorem preparation_arrays : gm06DeletionPrepareProg.writtenArrs ⊆ Finset.range 38 := by decide
private theorem preparation_not_cuff : 2 ∉ gm06DeletionPrepareProg.writtenArrs := by decide

set_option maxRecDepth 2048 in
private theorem preparation_registers : gm06DeletionPrepareProg.writtenRegs ⊆ Finset.range 300 := by decide

/-- Deletion preparation preserves the cuff copy and every external metadata array. -/
theorem gm06GapDeletionPrepare_array_frame {w t : ℕ} {s s' : State}
    (he : Exec w gm06DeletionPrepareProg s s' t) {A : ℕ} (hA : A = 2 ∨ 38 ≤ A) :
    s'.arrs A = s.arrs A := by
  apply he.arrs_eq_of_not_mem_writtenArrs
  intro hm
  rcases hA with rfl | hA
  · exact preparation_not_cuff hm
  · have hh := Finset.mem_range.mp (preparation_arrays hm)
    omega

/-- Deletion preparation preserves all counters outside its fixed scratch range. -/
theorem gm06GapDeletionPrepare_register_frame {w t : ℕ} {s s' : State}
    (he : Exec w gm06DeletionPrepareProg s s' t) {q : ℕ} (hq : 300 ≤ q) :
    s'.regs q = s.regs q := by
  apply he.regs_eq_of_not_mem_writtenRegs
  intro hm
  have hh := Finset.mem_range.mp (preparation_registers hm)
  omega

private theorem ranks_output {w t : ℕ} (x : GM06DrawingData) (vs : List (Fin x.n))
    (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w) {s s' : State}
    (he : Exec w gm06RootRanksProg s s' t) (hm : s'.arrs 36 = gm06RootMask x vs) :
    s'.arrs 37 = List.ofFn (fun a : Fin x.cellCount => ((gm06RootMask x vs).take a.val).sum) := by
  have hmask : s.arrs 36 = gm06RootMask x vs :=
    (he.arrs_eq_of_not_mem_writtenArrs (by decide : 36 ∉ gm06RootRanksProg.writtenArrs)).symm.trans hm
  obtain ⟨s₂, _, he₂, _, htable, _, _, _⟩ := gm06RootRanksProg_exec x vs hw hN hmask
  rw [(Exec.deterministic he he₂).1]
  exact htable

/-- The prepared root ranks are the exclusive prefixes of the computed
root mask. This follows from the existing preparation command itself. -/
theorem gm06GapDeletionPrepare_rootRanks {w t : ℕ} (x : GM06DrawingData) (vs : List (Fin x.n))
    (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w) {s s' : State}
    (he : Exec w gm06DeletionPrepareProg s s' t) (hm : s'.arrs 36 = gm06RootMask x vs) :
    s'.arrs 37 = List.ofFn (fun a : Fin x.cellCount => ((gm06RootMask x vs).take a.val).sum) := by
  cases he with
  | seq _ htail =>
    cases htail with
    | seq _ hregions =>
      cases hregions with
      | seq _ hroots =>
        cases hroots with
        | seq _ hranks => exact ranks_output x vs hw hN hranks hm

end GraphMinor.Compute
