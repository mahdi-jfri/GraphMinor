module

public import GraphMinor.GM06.Alg511StoredFromInput
import GraphMinor.Compute.GM06Alg511Numerator
import GraphMinor.Compute.GM06Alg511StoredWordBounds
import Mathlib.Tactic

/-!
# A signed numerator for the fully stored initial linkage

For VI (5.11), page 134, append the scaled numerator arithmetic to
the stored-linkage winding phase. Doubling its execution word size
suffices for the products. The exact same full linkage is retained,
and its winding is the signed numerator pair in registers 54/55
over the positive path count in register 52.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface GraphMinor.GM11

/-- The initial program stores a full linkage and computes its signed
winding numerator from retained input, with arbitrary initial scratch. -/
theorem alg511_storedNumerator_exec {w : ℕ} (x : GM06Alg511WindingInput)
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
      Exec (2 * w) gm06Alg511StoredNumeratorProg s s' t ∧
      t ≤ 671 + 88 * (gm06Alg511Words x.drawing).length +
        25 * x.drawing.endpoints.length + 116 * x.edgeTurns.length +
        x.drawing.vertexCount * (127 + 13 * x.drawing.endpoints.length) ∧
      (∀ arr, arr ∉ [1002, 1007, 1004, 1006, 1008, 3, 1100, 1005, 11, 1300, 12, 13] →
        s'.arrs arr = s.arrs arr) ∧
      s'.regs 52 = x.drawing.pathCount ∧
      s'.regs 54 < 2 ^ (2 * w) ∧ s'.regs 55 < 2 ^ (2 * w) ∧
      (s'.arrs 1300).length = x.drawing.vertexCount ∧ s'.regs 46 < x.drawing.pathCount ∧
      L.HasTheta ((((s'.regs 54 : ℤ) - (s'.regs 55 : ℤ) : ℤ) : ℝ) / x.drawing.pathCount) ∧
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
  obtain ⟨s₁, t₁, W, actual, L, he₁, ht₁, harr₁, hK, hI, hchoiceLen,
    hindex, htheta, hW, hactual⟩ :=
    alg511_storedWinding_from_input x rep hk out hsys hcount s hw hword hsquare
      hproduct hlen hout ha hn hwords
  obtain ⟨hp, hq⟩ := gm06Alg511StoredInitialWindingProg_regs_lt he₁
  have hkn : x.drawing.pathCount ≤ x.drawing.vertexCount := rep.pathCount_le_vertexCount hk
  have hkfit : x.drawing.pathCount < 2 ^ w := by omega
  have hjfit : s₁.regs 46 < 2 ^ w := hindex.trans hkfit
  have hz : 0 < 2 ^ w := Nat.two_pow_pos w
  have hpow : 2 ^ w ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by decide) (by omega)
  have hpos := gm06Alg511ProductAdd_lt_double hkfit hp hjfit
  have hneg := gm06Alg511ProductAdd_lt_double hkfit hq hz
  obtain ⟨s₂, he₂, hP, hQ, hnum, hkeep⟩ := gm06Alg511ScaledWindingProg_exec
    x.drawing.pathCount (s₁.regs 21) (s₁.regs 22) 0 (s₁.regs 46) s₁
    (hkfit.trans_le hpow) (hp.trans_le hpow) (hq.trans_le hpow) (hz.trans_le hpow)
    (hjfit.trans_le hpow) hpos hneg hK rfl rfl hI rfl
  refine ⟨s₂, t₁ + 12, W, actual, L, .seq (Exec.mono_wordSize (by omega) he₁) he₂,
    by omega, ?_, (hkeep.1 52 (by decide)).trans hK,
    by rw [hP]; exact hpos, by rw [hQ]; exact hneg,
    by rw [hkeep.2 1300 (by simp)]; exact hchoiceLen,
    by rw [hkeep.1 46 (by decide)]; exact hindex, ?_, ?_, hactual⟩
  · intro arr hnot
    exact (hkeep.2 arr (by simp)).trans (harr₁ arr hnot)
  · rw [hnum]
    simpa only [Nat.cast_zero, sub_zero] using htheta
  · intro i
    rw [hkeep.2 1300 (by simp)]
    exact hW i

end GraphMinor.GM06
