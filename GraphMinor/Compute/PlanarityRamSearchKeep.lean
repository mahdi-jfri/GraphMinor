module

public import GraphMinor.Compute.PlanarityRamStepRefine

/-!
# Input fields kept by a frame iteration

Every write in a DFS iteration targets a work array. The root counter and
vertex-count register are only read or untouched. The written-field rules
of `Exec` give the preservation facts needed between while-loop iterations.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

private theorem step_arr_not_written (a : ℕ) (ha : a < 33) :
    a ∉ searchFrameStepProg.writtenArrs := by
  simp only [searchFrameStepProg, loadFrameProg, completeFrameProg, popFrameProg,
    appendPostorderProg, finishIncomingProg, finishEdgeProg, finishKeyProg, parentPairProg,
    insertPairProg, insertLowProg, scanNeighborProg, advanceFrameProg, visitedNeighborProg,
    backEdgeProg, treeChildProg, addEdgeProg, storeEdgeProg, discoverChildProg, pushFrameProg,
    Cmd.writtenArrs, Field.array, Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty,
    not_or]
  try dsimp only [Arr] at *
  simp only [not_false_eq_true, true_and, and_true]
  omega

/-- Each iteration preserves every input array. -/
theorem searchFrameStepProg_input_eq {w t : ℕ} {s s' : State}
    (hex : Exec w searchFrameStepProg s s' t) (a : ℕ) (ha : a < 33) :
    s'.arrs a = s.arrs a := hex.arrs_eq_of_not_mem_writtenArrs (step_arr_not_written a ha)

private theorem step_root_not_written (r : ℕ) (hr : r = 30 ∨ r = 40) :
    r ∉ searchFrameStepProg.writtenRegs := by
  rcases hr with rfl | rfl <;>
    simp [searchFrameStepProg, loadFrameProg, completeFrameProg, popFrameProg,
      appendPostorderProg, finishIncomingProg, finishEdgeProg, finishKeyProg, parentPairProg,
      insertPairProg, insertLowProg, scanNeighborProg, advanceFrameProg, visitedNeighborProg,
      backEdgeProg, treeChildProg, addEdgeProg, storeEdgeProg, discoverChildProg, pushFrameProg,
      Cmd.writtenRegs]


/-- Each iteration preserves the vertex-count register and outer root counter. -/
theorem searchFrameStepProg_root_regs {w t : ℕ} {s s' : State}
    (hex : Exec w searchFrameStepProg s s' t) : s'.regs 30 = s.regs 30 ∧ s'.regs 40 = s.regs 40 :=
  ⟨hex.regs_eq_of_not_mem_writtenRegs (step_root_not_written 30 (Or.inl rfl)),
    hex.regs_eq_of_not_mem_writtenRegs (step_root_not_written 40 (Or.inr rfl))⟩

/-- The same adjacency-list encoding is available after one iteration. -/
theorem searchFrameStepProg_adj {N w t : ℕ} {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} {s s' : State}
    (h : IsAdjList G 30 31 32 lists s) (hex : Exec w searchFrameStepProg s s' t) :
    IsAdjList G 30 31 32 lists s' :=
  h.of_arrs_eq (searchFrameStepProg_input_eq hex 30 (by decide))
    (searchFrameStepProg_input_eq hex 31 (by decide))
    (searchFrameStepProg_input_eq hex 32 (by decide))

/-- Valid adjacency labels in the input encoding are valid in its functional array. -/
theorem adjacency_labels_valid {N : ℕ} {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} (h : IsAdjListFamily G lists) :
    ∀ v : Fin (List.ofFn lists).toArray.size,
      ∀ u ∈ (List.ofFn lists).toArray[v.val]!, u < (List.ofFn lists).toArray.size := by
  intro v u hu
  have hv : v.val < N := by simpa using v.isLt
  have hlist : (List.ofFn lists).toArray[v.val]! = lists ⟨v.val, hv⟩ := by
    rw [getElem!_pos (List.ofFn lists).toArray v.val v.isLt]
    simp
  have hh := (h ⟨v.val, hv⟩).1 u (by simpa only [hlist] using hu)
  simpa using hh

/-- The whole component loop preserves all input arrays. -/
theorem searchComponentProg_input_eq {w t : ℕ} {s s' : State}
    (hex : Exec w searchComponentProg s s' t) (a : ℕ) (ha : a < 33) :
    s'.arrs a = s.arrs a := by
  apply hex.arrs_eq_of_not_mem_writtenArrs
  exact step_arr_not_written a ha

/-- The whole component loop preserves the count and root registers. -/
theorem searchComponentProg_root_regs {w t : ℕ} {s s' : State}
    (hex : Exec w searchComponentProg s s' t) : s'.regs 30 = s.regs 30 ∧ s'.regs 40 = s.regs 40 :=
  ⟨hex.regs_eq_of_not_mem_writtenRegs (step_root_not_written 30 (Or.inl rfl)),
    hex.regs_eq_of_not_mem_writtenRegs (step_root_not_written 40 (Or.inr rfl))⟩

/-- A whole root action preserves the input arrays. -/
theorem searchRootProg_input_eq {w t : ℕ} {s s' : State}
    (hex : Exec w searchRootProg s s' t) (a : ℕ) (ha : a < 33) :
    s'.arrs a = s.arrs a := by
  apply hex.arrs_eq_of_not_mem_writtenArrs
  have h33 : a ≠ 33 := Nat.ne_of_lt ha
  have h42 : a ≠ 42 := Nat.ne_of_lt (Nat.lt_trans ha (by decide : 33 < 42))
  have h43 : a ≠ 43 := Nat.ne_of_lt (Nat.lt_trans ha (by decide : 33 < 43))
  simp [searchRootProg, startRootProg, pushFrameProg, searchComponentProg,
    Cmd.writtenArrs, Field.array, h33, h42, h43, step_arr_not_written a ha]

/-- A root action does not advance its caller's root counter. -/
theorem searchRootProg_root_regs {w t : ℕ} {s s' : State}
    (hex : Exec w searchRootProg s s' t) : s'.regs 30 = s.regs 30 ∧ s'.regs 40 = s.regs 40 := by
  constructor <;> apply hex.regs_eq_of_not_mem_writtenRegs <;>
    simp [searchRootProg, startRootProg, pushFrameProg, searchComponentProg,
      Cmd.writtenRegs, step_root_not_written 30 (Or.inl rfl), step_root_not_written 40 (Or.inr rfl)]

end GraphMinor.Compute.PlanarityRam
