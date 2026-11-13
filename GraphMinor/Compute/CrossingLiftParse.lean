module

public import GraphMinor.Compute.Parse
public import GraphMinor.Compute.Algorithm101Defs
import GraphMinor.Compute.Algorithm101Menger

/-!
# Building the recorded search graph in scratch memory

The existing linear graph parser builds adjacency lists from the oriented record edges.
Its arrays and vertex count are placed at the offsets read by the existing path search.
Shifting the program keeps the caller's lower registers and arrays intact.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Parse a graph in scratch memory, using the layout of the existing path search. -/
def liftParseSearchProg (R A : ℕ) : Cmd := (parseGraphProg 39 40 41 42 40).shiftMem R A

/-- The existing parser prepares the graph and vertex count for the search. The hypotheses
are its ordinary simple edge-list input, word bounds and stored input buffer. -/
theorem liftParseSearchProg_exec {w N : ℕ} (G : SimpleGraph (Fin N))
    (E : List (Fin N × Fin N)) (spare : List ℕ) (R A : ℕ) (s : State)
    (hE : IsSimpleEdgeList G E)
    (hs : s.arrs A = [N, E.length] ++ flatEdges E ++ spare)
    (hw : N + 2 * E.length + 4 < 2 ^ w) :
    ∃ s' t, Exec w (liftParseSearchProg R A) s s' t ∧
      t ≤ 23 * N + 88 * E.length + 27 ∧
      s'.regs (R + 40) = N ∧
      IsAdjList G (A + 40) (A + 41) (A + 42) (edgeNeighbors E) s' ∧
      (s'.arrs (A + 42)).length = 2 * E.length ∧
      s'.arrs A = s.arrs A ∧
      s'.regs (R + 74) = s.regs (R + 74) ∧ s'.regs (R + 75) = s.regs (R + 75) ∧
      (∀ a < A, s'.arrs a = s.arrs a) ∧ (∀ q < R, s'.regs q = s.regs q) := by
  have hin : (s.shiftDown R A).arrs inArr = [N, E.length] ++ flatEdges E ++ spare := hs
  obtain ⟨s0, t, he, ht, hi, hn, _, ha, hl, _⟩ := Triple.parseGraphProg_spec
    (w := w) G E spare 39 40 41 42 40 hE
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by omega) (by omega) (by omega) (s.shiftDown R A) hin
  refine ⟨s.shiftUp R A s0, t, he.shiftMem, ht, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [State.regs_shiftUp_add] using hn
  · exact ha.of_arrs_eq_shift (by simp) (by simp) (by simp)
  · simpa only [State.arrs_shiftUp_add] using hl
  · have hh := State.arrs_shiftUp_add R A s s0 0
    simpa only [Nat.add_zero] using hh.trans (hi.trans hs.symm)
  · simpa only [State.regs_shiftUp_add, State.regs_shiftDown] using he.regs_eq_of_not_mem_writtenRegs (r := 74)
      (by decide)
  · simpa only [State.regs_shiftUp_add, State.regs_shiftDown] using he.regs_eq_of_not_mem_writtenRegs (r := 75)
      (by decide)
  · intro a ha; simp [State.shiftUp, ha]
  · intro q hq; simp [State.shiftUp, hq]

end GraphMinor.Compute.Crossing
