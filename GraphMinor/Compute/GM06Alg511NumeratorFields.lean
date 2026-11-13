module

public import GraphMinor.Compute.GM06Alg511Numerator
import Mathlib.Tactic

/-!
# Original drawing tables retained by the initial numerator program

The orientation step of VI (5.11), page 134, reuses the original
endpoint, signed-turn and cuff tables. The initial numerator program
loads these tables during preparation. Its remaining commands change
only path buffers and scalar scratch. Determinism identifies the
preparation state with the verified loader's result, and the execution
frame rules carry the original tables to the actual final state.
-/

public section
namespace GraphMinor.Compute

/-- Every actual numerator execution retains the ordinary drawing
tables and vertex count needed for the subsequent orientation phase. -/
theorem gm06Alg511NumeratorProg_fields {w : ℕ} (x : GM06Alg511WindingInput)
    {α β : Type*} {G : Graph α β}
    (rep : GM06SuccessorGraphRep (x.drawing.withLinkage []) G)
    (s s' : State) (t : ℕ) (he : Exec w gm06Alg511NumeratorProg s s' t)
    (hw : 3 < 2 ^ w) (hinner : x.drawing.innerCuff ≠ [])
    (ha : s.arrs 1000 = gm06Alg511WindingWords x)
    (hn : (gm06Alg511WindingWords x).length < 2 ^ w)
    (hwords : ∀ v ∈ gm06Alg511WindingWords x, v < 2 ^ w)
    (hnfit : x.drawing.vertexCount < 2 ^ w)
    (hsquare : x.drawing.vertexCount * x.drawing.vertexCount < 2 ^ w) :
    s'.arrs 3 = x.drawing.endpoints ∧ s'.arrs 11 = gm06Alg511TurnWords x.edgeTurns ∧
      s'.arrs 1004 = x.drawing.innerCuff ∧ s'.arrs 1006 = x.drawing.outerCuff ∧
      s'.regs 41 = x.drawing.vertexCount := by
  obtain ⟨st, tt, hverified, _, _, hturns, houter, hinnerRow, hends, hN, _⟩ :=
    gm06Alg511WindingSetupProg_exec x rep s hw hinner ha hn hwords hnfit hsquare
  cases he with
  | seq hwind hscaled =>
    cases hwind with
    | seq hsetup hindex =>
      have hstate := (hsetup.deterministic hverified).1
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact (hscaled.arrs_eq_of_not_mem_writtenArrs (by decide)).trans
          ((hindex.arrs_eq_of_not_mem_writtenArrs (by decide)).trans
            ((congrArg (fun st : State => st.arrs 3) hstate).trans hends))
      · exact (hscaled.arrs_eq_of_not_mem_writtenArrs (by decide)).trans
          ((hindex.arrs_eq_of_not_mem_writtenArrs (by decide)).trans
            ((congrArg (fun st : State => st.arrs 11) hstate).trans hturns))
      · exact (hscaled.arrs_eq_of_not_mem_writtenArrs (by decide)).trans
          ((hindex.arrs_eq_of_not_mem_writtenArrs (by decide)).trans
            ((congrArg (fun st : State => st.arrs 1004) hstate).trans hinnerRow))
      · exact (hscaled.arrs_eq_of_not_mem_writtenArrs (by decide)).trans
          ((hindex.arrs_eq_of_not_mem_writtenArrs (by decide)).trans
            ((congrArg (fun st : State => st.arrs 1006) hstate).trans houter))
      · exact (hscaled.regs_eq_of_not_mem_writtenRegs (by decide)).trans
          ((hindex.regs_eq_of_not_mem_writtenRegs (by decide)).trans
            ((congrArg (fun st : State => st.regs 41) hstate).trans hN))

end GraphMinor.Compute
