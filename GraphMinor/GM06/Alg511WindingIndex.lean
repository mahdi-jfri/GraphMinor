module

public import GraphMinor.GM06.Alg511InitialWinding
import Mathlib.Tactic

/-!
# The initial winding with its computed cuff index

For VI (5.11), page 134, append the verified outer-cuff lookup to
the raw-flow turn computation. Its final register 46 holds the actual
endpoint index. Therefore the winding formula uses only values
computed by the program and the prescribed source index.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface

/-- The winding phase computes both the signed edge sum and the
outer cuff index, and their exact winding value is feasible. -/
theorem alg511_windingIndex_exec {w : ℕ} (x : GM06Alg511WindingInput)
    {G : Drawing ClosedCylinder} (rep : GM06Alg511GraphTurnRep x G)
    (hk : 0 < x.drawing.pathCount) (c : Fin x.drawing.pathCount) (out : List ℕ)
    (hsys : IsValidPathSystem x.drawing.flowGraph x.drawing.flowInput.A x.drawing.flowInput.B
      (decUsed x.drawing.vertexCount out) (decPred x.drawing.vertexCount out)
      (decSucc x.drawing.vertexCount out))
    (hcount : (pathStarts (decUsed x.drawing.vertexCount out)
      (decPred x.drawing.vertexCount out)).card = x.drawing.pathCount)
    (s : State) (hw : 2 < 2 ^ w) (hword : 1 + 3 * x.drawing.vertexCount < 2 ^ w)
    (hsquare : x.drawing.vertexCount * x.drawing.vertexCount < 2 ^ w)
    (hends : x.drawing.endpoints.length < 2 ^ w)
    (hproduct : x.drawing.vertexCount * (gm06Alg511TurnWords x.edgeTurns).sum < 2 ^ w)
    (hlen : out.length = 1 + 3 * x.drawing.vertexCount) (hout : s.arrs outArr = out)
    (hkeys : s.arrs 1100 = gm06Alg511DartKeys x.drawing)
    (hwords : s.arrs 11 = gm06Alg511TurnWords x.edgeTurns)
    (hcuff : s.arrs 1006 = x.drawing.outerCuff)
    (hcur : s.regs 40 = (rep.source c).val) (hN : s.regs 41 = x.drawing.vertexCount) :
    ∃ s' t, Exec w gm06Alg511WindingIndexProg s s' t ∧
      t ≤ 47 + x.drawing.vertexCount * (122 + 13 * x.drawing.endpoints.length) ∧
      (∀ arr, arr ≠ 12 → arr ≠ 13 → s'.arrs arr = s.arrs arr) ∧
      s'.regs 46 < x.drawing.pathCount ∧
      IsThetaFeasible x.drawing.pathCount G
        ((((x.drawing.pathCount : ℤ) * ((s'.regs 21 : ℤ) - (s'.regs 22 : ℤ)) +
          (s'.regs 46 : ℤ) - (c.val : ℤ) : ℤ) : ℝ) / x.drawing.pathCount) := by
  obtain ⟨s₁, t₁, he₁, ht₁, harr₁, j, hfinish, hfeasible⟩ :=
    alg511_initialWinding_exec x rep hk c out hsys hcount s hw hword hsquare
      hends hproduct hlen hout hkeys hwords hcur hN
  have hn : x.drawing.vertexCount < 2 ^ w := by omega
  obtain ⟨s₂, t₂, he₂, ht₂, hkeep, hindex⟩ := alg511_finishIndex_exec x rep hk j s₁
    (by omega) hn ((harr₁ 1006 (by decide) (by decide)).trans hcuff) hfinish
  refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, ?_, ?_, by rw [hindex]; exact j.isLt, ?_⟩
  · have hkn := rep.pathCount_le_vertexCount hk
    nlinarith [ht₁, ht₂]
  · intro arr ha₁ ha₂
    exact (hkeep.2 arr (by simp)).trans (harr₁ arr ha₁ ha₂)
  · simpa only [hindex, hkeep.1 21 (by decide), hkeep.1 22 (by decide)] using hfeasible

end GraphMinor.GM06
