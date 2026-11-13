module

public import GraphMinor.Compute.Case3StepsCoreEdgeRepresentatives

/-!
# Reading canonical simple-edge endpoints

The existing edge parser is shifted to read the retained simple graph in
array 16. It reads one edge in constant time and keeps every array, including
the component key and representative tables.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Read edge register 18 into endpoint registers 42 and 43, using 44 as scratch. -/
def case3ReadCoreEdgeProg : Cmd := (readEdgeEndpoints 2 26 27 28).shift 16 16

/-- Every canonical edge has ordered endpoints and is an edge of the input. -/
theorem case3InputEdges_get_spec (x : Alg81Input) (j : Fin (case3InputEdges x).length) :
    ((case3InputEdges x)[j.1]).1 < ((case3InputEdges x)[j.1]).2 ∧
      x.G.Adj ((case3InputEdges x)[j.1]).1 ((case3InputEdges x)[j.1]).2 :=
  (mem_edgeListOf x.G _).mp (List.getElem_mem j.2)

/-- Reading one edge takes at most fourteen steps and changes only its
endpoint and scratch registers. -/
theorem case3ReadCoreEdgeProg_exec {w : ℕ} (x : Alg81Input)
    (j : Fin (case3InputEdges x).length) (hw : 2 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hm : 2 + 2 * (case3InputEdges x).length < 2 ^ w)
    {s : State} (hin : s.arrs 16 = encGraph x.G) (hrj : s.regs 18 = j.1) :
    ∃ s' t, Exec w case3ReadCoreEdgeProg s s' t ∧ t ≤ 14 ∧
      s'.regs 42 = ((case3InputEdges x)[j.1]).1.1 ∧
      s'.regs 43 = ((case3InputEdges x)[j.1]).2.1 ∧
      (∀ a, s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 42 → r ≠ 43 → r ≠ 44 → s'.regs r = s.regs r) := by
  have hinSub : (s.unshift 16 16).arrs inArr =
      [x.n, (case3InputEdges x).length] ++ flatEdges (case3InputEdges x) ++ [] := by
    simpa only [State.unshift_arrs, inArr, Nat.zero_add, case3InputEdges, encGraph, List.append_nil] using hin
  obtain ⟨s_sub, t, hex, ht, hru, hrv, harr, hreg⟩ :=
    readEdgeEndpoints_exec (case3InputEdges x) [] 2 26 27 28 j.1 (s.unshift 16 16)
      (by decide) (by decide) hw hn hm j.2 hinSub hrj
  refine ⟨s.applyShifted 16 16 s_sub, t, Exec.shift_from 16 16 hex, ht, ?_, ?_, ?_, ?_⟩
  · change (s.applyShifted 16 16 s_sub).regs (26 + 16) = _
    rw [State.applyShifted_regs_add, hru]
  · change (s.applyShifted 16 16 s_sub).regs (27 + 16) = _
    rw [State.applyShifted_regs_add, hrv]
  · intro a
    by_cases ha : 16 ≤ a
    · change (if 16 ≤ a then s_sub.arrs (a - 16) else s.arrs a) = _
      simp only [ha, ↓reduceIte]
      rw [harr, State.unshift_arrs, Nat.sub_add_cancel ha]
    · exact State.applyShifted_arrs_lt 16 16 s s_sub (by romega)
  · intro r h42 h43 h44
    by_cases hr : 16 ≤ r
    · change (if 16 ≤ r then s_sub.regs (r - 16) else s.regs r) = _
      simp only [hr, ↓reduceIte]
      rw [hreg (r - 16) (by romega) (by romega) (by romega), State.unshift_regs,
        Nat.sub_add_cancel hr]
    · exact State.applyShifted_regs_lt 16 16 s s_sub (by romega)

end GraphMinor.Compute
