module

public import GraphMinor.Compute.Case3StepsAllComponentsProg

/-!
# Parsing the simple compass encoding

The graph parser runs above the core and component-table arrays. Its shifted
adjacency arrays are the input to the outside restriction and component
searches in step (5) of XIII (9.9), page 104.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- The canonical simple edge list, using the input's adjacency decision procedure. -/
def case3InputEdges (x : Alg81Input) : List (Fin x.n × Fin x.n) :=
  @edgeListOf x.n x.G x.decAdj

/-- Parse array 16, using arrays 18 through 21 and registers starting at 32. -/
def case3ParseProg : Cmd := (parseGraphProg 2 3 4 5 0).shift 16 32

/-- Parsing preserves every array below 18, including the core bitset. -/
theorem case3ParseProg_exec {w : ℕ} (x : Alg81Input)
    (hw : 2 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hm : 2 + 2 * (edgeListOf x.G).length < 2 ^ w)
    {s : State} (hinput : s.arrs 16 = encGraph x.G) :
    ∃ s' t, Exec w case3ParseProg s s' t ∧
      t ≤ 23 * x.n + 88 * (edgeListOf x.G).length + 27 ∧
      IsAdjList x.G 19 20 21 (edgeNeighbors (edgeListOf x.G)) s' ∧
      (s'.arrs 21).length = 2 * (edgeListOf x.G).length ∧
      s'.regs 32 = x.n ∧ s'.regs 33 = (edgeListOf x.G).length ∧
      (∀ a < 18, s'.arrs a = s.arrs a) ∧
      (∀ r < 32, s'.regs r = s.regs r) := by
  have hs : (s.unshift 16 32).arrs inArr =
      [x.n, (edgeListOf x.G).length] ++ flatEdges (edgeListOf x.G) ++ [] := by
    simpa only [State.unshift_arrs, inArr, Nat.zero_add, encGraph, List.append_nil] using hinput
  obtain ⟨s_sub, t, hex, ht, _, hrn, hrm, hadj, hlen, _⟩ :=
    Triple.parseGraphProg_spec x.G (edgeListOf x.G) [] 2 3 4 5 0
      (isSimpleEdgeList_edgeListOf x.G)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hw hn hm (s.unshift 16 32) hs
  let s' := s.applyShifted 16 32 s_sub
  have hex' : Exec w case3ParseProg s s' t := Exec.shift_from 16 32 hex
  refine ⟨s', t, hex', ht, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply hadj.of_arrs_eq <;> rfl
  · change (s'.arrs (5 + 16)).length = _
    rw [show s'.arrs (5 + 16) = s_sub.arrs 5 from State.applyShifted_arrs_add ..]
    exact hlen
  · change s'.regs (0 + 32) = _
    rw [show s'.regs (0 + 32) = s_sub.regs 0 from State.applyShifted_regs_add ..]
    exact hrn
  · change s'.regs (1 + 32) = _
    rw [show s'.regs (1 + 32) = s_sub.regs 1 from State.applyShifted_regs_add ..]
    exact hrm
  · intro a ha
    exact hex'.arrs_eq_of_not_mem_writtenArrs (by
      simp [case3ParseProg, parseGraphProg, parsePass1Body, parsePrefixBody, parsePass2Body, readEdgeEndpoints, incArrAt, csrAppend, listAppend, Cmd.shift, forUp, Cmd.writtenArrs]
      dsimp only [Arr] at *
      omega)
  · intro r hr
    exact State.applyShifted_regs_lt 16 32 s s_sub hr

end GraphMinor.Compute
