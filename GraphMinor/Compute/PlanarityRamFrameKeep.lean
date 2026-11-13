module

public import GraphMinor.Compute.PlanarityRamFrameRead
public import GraphMinor.Compute.PlanarityRamSearchProg
public import GraphMinor.Compute.Logic

/-!
# Keeping the live frames during record operations

The record and vertex programs write different arrays from the frame
stack. The operational semantics' written-field rules therefore preserve
its representation. This keeps the frame and search arguments separate
when assembling one DFS step.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

/-- An execution that does not write frame fields preserves their representation. -/
theorem FramesAt.of_exec {N w t : ℕ} {s s' : State} {stack : List LRPlanarity.Frame}
    {prog : Cmd} (h : FramesAt N s stack) (hex : Exec w prog s s' t)
    (hr : 38 ∉ prog.writtenRegs) (hv : Field.frameVertex.array ∉ prog.writtenArrs)
    (hn : Field.frameNext.array ∉ prog.writtenArrs) : FramesAt N s' stack := by
  refine ⟨(hex.regs_eq_of_not_mem_writtenRegs hr).trans h.1,
    h.2.1.of_arr_eq (hex.arrs_eq_of_not_mem_writtenArrs hv),
    h.2.2.of_arr_eq (hex.arrs_eq_of_not_mem_writtenArrs hn)⟩

/-- Creating a record does not alter the live frame stack. -/
theorem FramesAt.addEdge_exec {N w t : ℕ} {s s' : State} {stack : List LRPlanarity.Frame}
    (h : FramesAt N s stack) (tree : Bool) (hex : Exec w (addEdgeProg tree) s s' t) :
    FramesAt N s' stack := by
  apply h.of_exec hex <;>
    simp [addEdgeProg, storeEdgeProg, Cmd.writtenRegs, Cmd.writtenArrs, Field.array]

/-- Finishing a record does not alter the live frame stack. -/
theorem FramesAt.finishEdge_exec {N w t : ℕ} {s s' : State} {stack : List LRPlanarity.Frame}
    (h : FramesAt N s stack) (hex : Exec w finishEdgeProg s s' t) :
    FramesAt N s' stack := by
  apply h.of_exec hex <;>
    simp [finishEdgeProg, finishKeyProg, parentPairProg, insertPairProg, insertLowProg,
      Cmd.writtenRegs, Cmd.writtenArrs, Field.array]

/-- Filling a child's vertex data does not alter the live frame stack. -/
theorem FramesAt.discoverChild_exec {N w t : ℕ} {s s' : State} {stack : List LRPlanarity.Frame}
    (h : FramesAt N s stack) (hex : Exec w discoverChildProg s s' t) :
    FramesAt N s' stack := by
  apply h.of_exec hex <;>
    simp [discoverChildProg, Cmd.writtenRegs, Cmd.writtenArrs, Field.array]

/-- Appending a vertex completion does not alter the live frame stack. -/
theorem FramesAt.appendPostorder_exec {N w t : ℕ} {s s' : State} {stack : List LRPlanarity.Frame}
    (h : FramesAt N s stack) (hex : Exec w appendPostorderProg s s' t) :
    FramesAt N s' stack := by
  apply h.of_exec hex <;>
    simp [appendPostorderProg, Cmd.writtenRegs, Cmd.writtenArrs, Field.array]

/-- The endpoint registers remain available after edge creation. -/
theorem addEdgeProg_endpoints {w t : ℕ} {s s' : State} (tree : Bool)
    (hex : Exec w (addEdgeProg tree) s s' t) : s'.regs 41 = s.regs 41 ∧ s'.regs 43 = s.regs 43 := by
  constructor <;> apply hex.regs_eq_of_not_mem_writtenRegs <;>
    simp [addEdgeProg, storeEdgeProg, Cmd.writtenRegs]

/-- Child discovery leaves the endpoint registers fixed. -/
theorem discoverChildProg_endpoints {w t : ℕ} {s s' : State}
    (hex : Exec w discoverChildProg s s' t) : s'.regs 41 = s.regs 41 ∧ s'.regs 43 = s.regs 43 := by
  constructor <;> apply hex.regs_eq_of_not_mem_writtenRegs <;>
    simp [discoverChildProg, Cmd.writtenRegs]

end GraphMinor.Compute.PlanarityRam
