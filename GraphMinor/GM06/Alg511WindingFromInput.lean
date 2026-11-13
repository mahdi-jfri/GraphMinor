module

public import GraphMinor.Compute.GM06Alg511WindingSetup
public import GraphMinor.GM06.Alg511WindingIndex
import Mathlib.Tactic

/-!
# Initial winding directly from retained input and flow output

For VI (5.11), page 134, prepare every winding scratch table from
the retained drawing words and start at prescribed source zero.
The program constructs its path trace, selects edges, sums their
turns and reads its final cuff index. No path buffers, selected edges
or winding values are required in the initial scratch state.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface

/-- After successful maximum flow, the entire initial-winding phase
runs from the retained supplied drawing and raw flow result. Its
computed signed turn and cuff index give an actual feasible value. -/
theorem alg511_initialWinding_from_input {w : ℕ} (x : GM06Alg511WindingInput)
    {G : Drawing ClosedCylinder} (rep : GM06Alg511GraphTurnRep x G)
    (hk : 0 < x.drawing.pathCount) (out : List ℕ)
    (hsys : IsValidPathSystem x.drawing.flowGraph x.drawing.flowInput.A x.drawing.flowInput.B
      (decUsed x.drawing.vertexCount out) (decPred x.drawing.vertexCount out)
      (decSucc x.drawing.vertexCount out))
    (hcount : (pathStarts (decUsed x.drawing.vertexCount out)
      (decPred x.drawing.vertexCount out)).card = x.drawing.pathCount)
    (s : State) (hw : 3 < 2 ^ w) (hword : 1 + 3 * x.drawing.vertexCount < 2 ^ w)
    (hsquare : x.drawing.vertexCount * x.drawing.vertexCount < 2 ^ w)
    (hproduct : x.drawing.vertexCount * (gm06Alg511TurnWords x.edgeTurns).sum < 2 ^ w)
    (hlen : out.length = 1 + 3 * x.drawing.vertexCount) (hout : s.arrs outArr = out)
    (ha : s.arrs 1000 = gm06Alg511WindingWords x)
    (hn : (gm06Alg511WindingWords x).length < 2 ^ w)
    (hwords : ∀ v ∈ gm06Alg511WindingWords x, v < 2 ^ w) :
    ∃ s' t, Exec w gm06Alg511InitialWindingProg s s' t ∧
      t ≤ 657 + 88 * (gm06Alg511Words x.drawing).length +
        25 * x.drawing.endpoints.length + 116 * x.edgeTurns.length +
        x.drawing.vertexCount * (122 + 13 * x.drawing.endpoints.length) ∧
      s'.regs 52 = x.drawing.pathCount ∧ s'.regs 53 = 0 ∧ s'.regs 46 < x.drawing.pathCount ∧
      IsThetaFeasible x.drawing.pathCount G
        ((((x.drawing.pathCount : ℤ) * ((s'.regs 21 : ℤ) - (s'.regs 22 : ℤ)) +
          (s'.regs 46 : ℤ) : ℤ) : ℝ) / x.drawing.pathCount) ∧
      ∀ a, a ∉ [1002, 1007, 1004, 1006, 1008, 3, 1100, 1005, 11, 12, 13] →
        s'.arrs a = s.arrs a := by
  have hinner : x.drawing.innerCuff ≠ [] := by
    intro he
    have hh := congrArg List.length rep.inner
    rw [he, List.length_nil, List.length_ofFn] at hh
    omega
  have hfirst : x.drawing.innerCuff.getD 0 0 = (rep.source ⟨0, hk⟩).val := by
    simp [rep.inner, List.getD_eq_getElem?_getD, hk]
  have hnfit : x.drawing.vertexCount < 2 ^ w := by omega
  obtain ⟨s₁, t₁, he₁, ht₁, hkeys, hturns, houter, _, _, hN, hsource, hK, hI, harr₁⟩ :=
    gm06Alg511WindingSetupProg_exec x rep.graph s hw hinner ha hn hwords hnfit hsquare
  have hendslen : x.drawing.endpoints.length ≤ (gm06Alg511Words x.drawing).length :=
    gm06Alg511_encoded_row_length_le (rows := gm06Alg511Rows x.drawing) (by simp [gm06Alg511Rows])
  have hbaselen : (gm06Alg511Words x.drawing).length ≤ (gm06Alg511WindingWords x).length :=
    gm06Alg511_encoded_row_length_le (by simp)
  obtain ⟨s₂, t₂, he₂, ht₂, harr₂, hindex, hfeasible⟩ :=
    alg511_windingIndex_exec x rep hk ⟨0, hk⟩ out hsys hcount s₁ (by omega) hword hsquare
      ((hendslen.trans hbaselen).trans_lt hn) hproduct hlen
      ((harr₁ outArr (by decide)).trans hout) hkeys hturns houter
      (hsource.trans hfirst) hN
  refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, by omega, ?_, ?_, hindex, ?_, ?_⟩
  · exact (he₂.regs_eq_of_not_mem_writtenRegs (by decide)).trans hK
  · exact (he₂.regs_eq_of_not_mem_writtenRegs (by decide)).trans hI
  · simpa using hfeasible
  · intro a ha'
    have ha12 : a ≠ 12 := fun he => ha' (by simp [he])
    have ha13 : a ≠ 13 := fun he => ha' (by simp [he])
    rw [harr₂ a ha12 ha13]
    apply harr₁ a
    intro hm
    apply ha'
    change a ∈ [1002, 1007, 1004, 1006, 1008, 3, 1100, 1005, 11] ++ [12, 13]
    exact List.mem_append_left _ hm

end GraphMinor.GM06
