module

public import GraphMinor.GM06.Alg511StoredWinding
import Mathlib.Tactic

/-!
# The fully stored initial linkage from retained input words

The initial winding phase of VI (5.11), page 134, starts with only
the retained drawing and raw maximum-flow output. It loads the
ordinary fields, computes every linkage edge choice, and calculates
the winding of that same full linkage. No prepared scratch arrays,
selected edges, or initial winding are part of the input relation.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface GraphMinor.GM11

/-- The complete initial linkage and its winding are computed from
retained input and raw successful flow, with arbitrary scratch data. -/
theorem alg511_storedWinding_from_input {w : ℕ} (x : GM06Alg511WindingInput)
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
    ∃ (s' : State) (t : ℕ)
      (W : ∀ i : Fin x.drawing.pathCount,
        GraphWalk (gm06Alg511LabelGraph rep.graph.pairs) (rep.source i)
          (traceWalk hsys x.drawing.vertexCount (rep.source i)).1)
      (actual : ∀ i : Fin x.drawing.pathCount,
        GraphWalk G.toGraph (rep.graph.vertex (rep.source i)).val
          (rep.graph.vertex (traceWalk hsys x.drawing.vertexCount (rep.source i)).1).val)
      (L : CylinderLinkage x.drawing.pathCount G),
      Exec w gm06Alg511StoredInitialWindingProg s s' t ∧
      t ≤ 659 + 88 * (gm06Alg511Words x.drawing).length +
        25 * x.drawing.endpoints.length + 116 * x.edgeTurns.length +
        x.drawing.vertexCount * (127 + 13 * x.drawing.endpoints.length) ∧
      (∀ arr, arr ∉ [1002, 1007, 1004, 1006, 1008, 3, 1100, 1005, 11, 1300, 12, 13] →
        s'.arrs arr = s.arrs arr) ∧
      s'.regs 52 = x.drawing.pathCount ∧ s'.regs 53 = 0 ∧
      (s'.arrs 1300).length = x.drawing.vertexCount ∧ s'.regs 46 < x.drawing.pathCount ∧
      L.HasTheta ((((x.drawing.pathCount : ℤ) * ((s'.regs 21 : ℤ) - (s'.regs 22 : ℤ)) +
        (s'.regs 46 : ℤ) : ℤ) : ℝ) / x.drawing.pathCount) ∧
      (∀ i, (W i).support = (traceWalk hsys x.drawing.vertexCount (rep.source i)).2.support ∧
        gm06Alg511LabelWalkDarts rep.graph.pairs (W i) =
          gm06Alg511ChosenDarts x.drawing (s'.arrs 1300) (W i).support) ∧
      (∀ i, (actual i).support = (W i).support.map (fun v => (rep.graph.vertex v).val) ∧
        alg511InterpretedWalkTurn rep.graph x.edgeTurns (actual i) =
          gm06Alg511LabelWalkTurn rep.graph.pairs x.edgeTurns (W i) ∧
        (actual i).edges = (W i).edges.map (fun e => (rep.graph.edge e).val) ∧
        L.pathDrawing i = walkDrawing G (actual i) ∧
        ParametrizesSet (L.curve i) (walkDrawing G (actual i)).U
          (rep.graph.vertex (rep.source i)).val
          (rep.graph.vertex (traceWalk hsys x.drawing.vertexCount (rep.source i)).1).val) := by
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
  obtain ⟨s₂, t₂, W, actual, L, he₂, ht₂, harr₂, hchoiceLen, hindex, htheta, hW, hactual⟩ :=
    alg511_storedWinding_exec x rep hk ⟨0, hk⟩ out hsys hcount s₁ (by omega) hword hsquare
      ((hendslen.trans hbaselen).trans_lt hn) hproduct hlen
      ((harr₁ outArr (by decide)).trans hout) hkeys hturns houter
      (hsource.trans hfirst) hN
  refine ⟨s₂, t₁ + t₂, W, actual, L, .seq he₁ he₂, by omega, ?_, ?_, ?_,
    hchoiceLen, hindex, ?_, hW, hactual⟩
  · intro arr hnot
    have hne₀ : arr ≠ 1300 := fun h => hnot (by simp [h])
    have hne₁ : arr ≠ 12 := fun h => hnot (by simp [h])
    have hne₂ : arr ≠ 13 := fun h => hnot (by simp [h])
    rw [harr₂ arr hne₀ hne₁ hne₂]
    apply harr₁ arr
    intro hm
    exact hnot (List.mem_append_left [1300, 12, 13] hm)
  · exact (he₂.regs_eq_of_not_mem_writtenRegs (by decide)).trans hK
  · exact (he₂.regs_eq_of_not_mem_writtenRegs (by decide)).trans hI
  · simpa only [Nat.cast_zero, sub_zero] using htheta

end GraphMinor.GM06
