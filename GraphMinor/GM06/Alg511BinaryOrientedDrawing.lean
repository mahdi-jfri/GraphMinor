module

public import GraphMinor.GM06.Alg511BinaryDrawingReflection
public import GraphMinor.GM06.Alg511BinaryLoopState
public import GraphMinor.GM06.Alg511BinaryNormalizedWinding
import GraphMinor.GM06.Section5Feasibility
import GraphMinor.GM06.Section5ReflectionLinkage
import Mathlib.Tactic

/-!
# Executing the chosen geometric orientation

Read the reflection bit computed by binary comparison. If it is
one, execute the verified cuff/rotation/path reflection. Otherwise
keep the original drawing and linkage. In both branches the actual
successor input has positive rotations and the retained ordinary
path rows. The represented winding and target have exactly the
sign chosen by the binary comparison.

The output includes the actual proper cylinder drawing, its positive
input representation, its encoded linkage and the unchanged binary
comparison rows. This is the geometric branch of VI (5.11), page 134.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Apply the computed geometric-data reflection exactly when the
binary comparison selected the opposite plane orientation. -/
def gm06Alg511BinaryOrientDrawingProg : Cmd :=
  .ite (.reg 57) gm06Alg511BinaryReflectDrawingProg .skip

/-- Normalize and compare the binary winding/target, then execute
the chosen reflection of all retained geometric input fields. -/
def gm06Alg511BinaryOrientationPhaseProg : Cmd :=
  .seq gm06Alg511BinaryNormalizeOrientationProg gm06Alg511BinaryOrientDrawingProg

end GraphMinor.Compute

namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Compute.TwoPaths GraphMinor.Surface

/-- The explicit graph/table cost of the conditional drawing
reflection, independent of target or turn magnitudes. -/
def alg511BinaryDrawingReflectionBudget (x : GM06Alg511WindingInput) : ℕ :=
  81 + 24 * (gm06EncodeRows x.drawing.rotations).length +
    x.drawing.rotations.length * (607 + 600 * (gm06EncodeRows x.drawing.rotations).length) +
    28 * x.drawing.innerCuff.length + 28 * x.drawing.outerCuff.length +
    12 * (1 + x.drawing.pathCount + x.drawing.pathCount * x.drawing.vertexCount) +
    x.drawing.pathCount * (307 + 40 * x.drawing.pathCount + 150 * x.drawing.vertexCount +
      100 * (1 + x.drawing.pathCount + x.drawing.pathCount * x.drawing.vertexCount))

/-- The actual orientation branch produces a proper positively
represented drawing and an encoded linkage with the chosen winding.
Its target feasibility is exactly the original feasibility question,
and all three binary comparison rows and control bits survive. -/
theorem alg511_binary_orientedDrawing_exec {w : ℕ} {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    (rep : GM06Alg511PositiveDrawingRep x G) (hG : IsCylinderSection5Drawing x.drawing.pathCount G)
    (L : CylinderLinkage x.drawing.pathCount G) (rows : List (List ℕ))
    (henc : GM06LinkageRowsEncoding L rep.graphTurn.graph.initialTagged rep.graphTurn.graph.vertexLabels rep.graphTurn.graph.edgeLabels rows)
    (theta : ℝ) (hTheta : L.HasTheta theta) (flag : ℕ) (s : State) (hflag : flag < 2) (hFlag : s.regs 57 = flag)
    (hw : 2 < 2 ^ w) (hn : x.drawing.vertexCount < 2 ^ w)
    (haug : 2 * (rep.graphTurn.graph.pairs.length + x.drawing.pathCount + x.drawing.pathCount) < 2 ^ w)
    (hcode : (gm06EncodeRows x.drawing.rotations).length < 2 ^ w)
    (hwords : ∀ d ∈ gm06EncodeRows x.drawing.rotations, d < 2 ^ w)
    (hcap : 1 + x.drawing.pathCount + x.drawing.pathCount * x.drawing.vertexCount < 2 ^ w)
    (htables : alg511BinaryLoopTables x s) (hP : s.arrs 8 = gm06EncodeRows rows) (hK : s.regs 52 = x.drawing.pathCount) :
    ∃ (t : State) (u : ℕ) (y : GM06Alg511WindingInput) (H : Drawing ClosedCylinder)
      (rp : GM06Alg511PositiveDrawingRep y H) (M : CylinderLinkage y.drawing.pathCount H) (rs : List (List ℕ)),
      Exec w gm06Alg511BinaryOrientDrawingProg s t u ∧
      u ≤ 81 + 24 * (gm06EncodeRows x.drawing.rotations).length +
        x.drawing.rotations.length * (607 + 600 * (gm06EncodeRows x.drawing.rotations).length) +
        28 * x.drawing.innerCuff.length + 28 * x.drawing.outerCuff.length +
        12 * (1 + x.drawing.pathCount + x.drawing.pathCount * x.drawing.vertexCount) +
        x.drawing.pathCount * (307 + 40 * x.drawing.pathCount + 150 * x.drawing.vertexCount +
          100 * (1 + x.drawing.pathCount + x.drawing.pathCount * x.drawing.vertexCount)) ∧
      y.drawing.pathCount = x.drawing.pathCount ∧ y.drawing.vertexCount = x.drawing.vertexCount ∧
      IsCylinderSection5Drawing y.drawing.pathCount H ∧ alg511BinaryLoopTables y t ∧ t.regs 52 = y.drawing.pathCount ∧
      t.arrs 8 = gm06EncodeRows rs ∧
      GM06LinkageRowsEncoding M rp.graphTurn.graph.initialTagged rp.graphTurn.graph.vertexLabels rp.graphTurn.graph.edgeLabels rs ∧
      M.HasTheta (if flag = 1 then -theta else theta) ∧
      y.drawing.target = (if flag = 1 then -x.drawing.target else x.drawing.target) ∧
      (IsThetaFeasible y.drawing.pathCount H y.drawing.target ↔ IsThetaFeasible x.drawing.pathCount G x.drawing.target) ∧
      t.regs 57 = s.regs 57 ∧ t.regs 90 = s.regs 90 ∧
      (∀ a ∈ ([2800, 2801, 2802] : List ℕ), t.arrs a = s.arrs a) ∧
      (y = x ∨ y = x.reflected) := by
  by_cases hone : flag = 1
  · obtain ⟨t, u, he, ht, hv, heEnds, hr, hi, ho, hp, hk, henc', htheta', hfeas, hkeep⟩ :=
      alg511_binary_drawing_reflection_exec rep hG.1 L rows henc theta hTheta s hw hn haug hcode hwords hcap
        htables.1 htables.2.1 htables.2.2.1 htables.2.2.2.1 htables.2.2.2.2 hP hK
    refine ⟨t, 1 + u, x.reflected, section5ReflectedDrawing x.drawing.pathCount G,
      alg511ReflectedPositiveDrawingRep rep hG.1, alg511ReflectedStoredLinkage hG.1 L,
      gm06Alg511ReflectedPathRows rows,
      .ite_true (Crossing.eval_reg hFlag (hflag.trans_le (by omega))) (by omega) he,
      by omega, rfl, rfl, isCylinderSection5Drawing_reflected hG, ⟨hv, heEnds, hr, hi, ho⟩, hk, hp, henc',
      by simpa only [hone, ite_true, GM06Alg511WindingInput.reflected, GM06Alg511Input.reflected] using htheta', ?_, hfeas,
      hkeep.1 57 (by decide), hkeep.1 90 (by decide), ?_, Or.inr rfl⟩
    · simpa only [hone, ite_true] using alg511_reflected_target x
    · intro a ha
      apply hkeep.2 a
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl <;> decide
  · have hzero : flag = 0 := by omega
    refine ⟨s, 2, x, G, rep, L, rows,
      .ite_false (Crossing.eval_reg (hFlag.trans hzero) (Nat.two_pow_pos w)) (.skip s),
      by omega, rfl, rfl, hG, htables, hK, hP, henc, by simpa only [hone, ite_false] using hTheta,
      by simp only [hone, ite_false], Iff.rfl, rfl, rfl, (fun _ _ => rfl), Or.inl rfl⟩

/-- The executed complete orientation phase supplies every loop
input: a proper positive drawing, exact ordinary path rows, an actual
linkage at the computed binary winding, the same feasibility question,
and a constructed natural target-step index. All integer operations
are the binary normalization/comparison programs. -/
theorem alg511_binary_orientationPhase_exec {w : ℕ} (x : GM06Alg511BinaryInput)
    {G : Drawing ClosedCylinder} (rep : GM06Alg511PositiveDrawingRep x.toWindingInput G)
    (hG : IsCylinderSection5Drawing x.pathCount G)
    (L : CylinderLinkage x.pathCount G) (rows : List (List ℕ))
    (henc : GM06LinkageRowsEncoding L rep.graphTurn.graph.initialTagged rep.graphTurn.graph.vertexLabels rep.graphTurn.graph.edgeLabels rows)
    (sw : ℕ) (current : List ℕ) (s : State)
    (hTheta : L.HasTheta ((gm06Alg511BinaryRowValue (sw :: current) : ℝ) / x.pathCount))
    (hgrid : ∃ m : ℤ, (x.pathCount : ℝ) * x.toWindingInput.drawing.target = m)
    (hw : 3 < 2 ^ w) (hn : x.vertexCount < 2 ^ w)
    (hsize : x.pathCount + x.numerator.digits.length + x.denominator.digits.length + current.length + 8 < 2 ^ w)
    (haug : 2 * (rep.graphTurn.graph.pairs.length + x.pathCount + x.pathCount) < 2 ^ w)
    (hcode : (gm06EncodeRows x.rotations).length < 2 ^ w)
    (hwords : ∀ d ∈ gm06EncodeRows x.rotations, d < 2 ^ w)
    (hcap : 1 + x.pathCount + x.pathCount * x.vertexCount < 2 ^ w)
    (hsw : sw < 2) (hbits : ∀ d ∈ current, d < 2)
    (htables : alg511BinaryLoopTables x.toWindingInput s)
    (hK : s.regs 52 = x.pathCount) (hA : s.arrs 2702 = x.numerator.words)
    (hD : s.arrs 2703 = x.denominator.words) (hW : s.arrs 2804 = sw :: current)
    (hP : s.arrs 8 = gm06EncodeRows rows) :
    ∃ (t : State) (u : ℕ) (y : GM06Alg511WindingInput) (H : Drawing ClosedCylinder)
      (rp : GM06Alg511PositiveDrawingRep y H) (M : CylinderLinkage y.drawing.pathCount H)
      (rs : List (List ℕ)) (steps sc st : ℕ) (cur target : List ℕ),
      Exec w gm06Alg511BinaryOrientationPhaseProg s t u ∧
      u ≤ 10000 * (x.pathCount + x.numerator.digits.length + x.denominator.digits.length + current.length + 5) ^ 2 +
        alg511BinaryDrawingReflectionBudget x.toWindingInput ∧
      y.drawing.pathCount = x.pathCount ∧ y.drawing.vertexCount = x.vertexCount ∧
      IsCylinderSection5Drawing y.drawing.pathCount H ∧ alg511BinaryLoopTables y t ∧ t.regs 52 = y.drawing.pathCount ∧
      t.arrs 8 = gm06EncodeRows rs ∧
      GM06LinkageRowsEncoding M rp.graphTurn.graph.initialTagged rp.graphTurn.graph.vertexLabels rp.graphTurn.graph.edgeLabels rs ∧
      t.arrs 2800 = sc :: cur ∧ t.arrs 2801 = st :: target ∧
      t.arrs 2802 = 0 :: x.denominator.digits.map Bool.toNat ∧ sc < 2 ∧ st < 2 ∧
      cur.length ≤ current.length + x.denominator.digits.length ∧ target.length ≤ x.pathCount + 1 + x.numerator.digits.length ∧
      (∀ d ∈ cur, d < 2) ∧ (∀ d ∈ target, d < 2) ∧
      M.HasTheta ((gm06Alg511BinaryRowValue (t.arrs 2800) : ℝ) / ((x.pathCount : ℝ) * x.denominator.value.natAbs)) ∧
      y.drawing.target = (gm06Alg511BinaryRowValue (t.arrs 2800) : ℝ) / ((x.pathCount : ℝ) * x.denominator.value.natAbs) +
        (steps : ℝ) / x.pathCount ∧
      gm06Alg511BinaryRowValue (t.arrs 2801) = gm06Alg511BinaryRowValue (t.arrs 2800) + (steps : ℤ) * x.denominator.value.natAbs ∧
      (IsThetaFeasible y.drawing.pathCount H y.drawing.target ↔ IsThetaFeasible x.pathCount G x.toWindingInput.drawing.target) ∧
      t.regs 90 = s.regs 90 ∧ (y = x.toWindingInput ∨ y = x.toWindingInput.reflected) := by
  obtain ⟨s₁, u₁, flag, sc, st, cur, target, he₁, ht₁, hf, hflag, hcur, htarget, hinc, hsc, hst,
    hcurLen, htargetLen, hcurBits, htargetBits, hcurRatio, htargetRatio, hle, _, _, hkeep₁⟩ :=
    alg511_binary_normalize_orientation_exec x hG.1 L sw current s rep.denominator_ne_zero hTheta hw hsize hsw hbits hK hA hD hW
  have htables₁ : alg511BinaryLoopTables x.toWindingInput s₁ := htables.frame (by
    intro a ha
    apply hkeep₁.2 a
    simp only [gm06Alg511RetainedSuccessorArrays, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide)
  obtain ⟨t, u₂, y, H, rp, M, rs, he₂, ht₂, hyK, hyN, hyG, hyTables, hyReg, hyRows, hyEnc,
    hyTheta, hyTarget, hyFeas, _, hsuccess₂, hbinary, hyChoice⟩ := alg511_binary_orientedDrawing_exec rep hG L rows henc
      _ hTheta flag s₁ hflag hf (by omega) hn haug hcode hwords hcap htables₁
        ((hkeep₁.2 8 (by decide)).trans hP) ((hkeep₁.1 52 (by decide)).trans hK)
  have hcurFinal : (gm06Alg511BinaryRowValue (t.arrs 2800) : ℝ) / ((x.pathCount : ℝ) * x.denominator.value.natAbs) =
      if flag = 1 then -((gm06Alg511BinaryRowValue (sw :: current) : ℝ) / x.pathCount)
        else (gm06Alg511BinaryRowValue (sw :: current) : ℝ) / x.pathCount := by
    rw [hbinary 2800 (by decide)]
    exact hcurRatio
  have htargetFinal : (gm06Alg511BinaryRowValue (t.arrs 2801) : ℝ) / ((x.pathCount : ℝ) * x.denominator.value.natAbs) = y.drawing.target := by
    rw [hbinary 2801 (by decide), htargetRatio, hyTarget]
  have htheta : M.HasTheta ((gm06Alg511BinaryRowValue (t.arrs 2800) : ℝ) / ((x.pathCount : ℝ) * x.denominator.value.natAbs)) := by
    rw [hcurFinal]
    exact hyTheta
  have hstartGrid := ((theorem_5_10_proof y.drawing.pathCount H _ hyG).mp ⟨M, htheta⟩).1
  have hstartGrid' : ∃ m : ℤ, (x.pathCount : ℝ) *
      ((gm06Alg511BinaryRowValue (t.arrs 2800) : ℝ) / ((x.pathCount : ℝ) * x.denominator.value.natAbs)) = m := by
    simpa only [hyK, GM06Alg511BinaryInput.toWindingInput] using hstartGrid
  have htargetGrid : ∃ m : ℤ, (x.pathCount : ℝ) * y.drawing.target = m := by
    obtain ⟨m, hm⟩ := hgrid
    rw [hyTarget]
    by_cases hone : flag = 1
    · exact ⟨-m, by simp only [hone, ite_true, mul_neg, Int.cast_neg, hm]⟩
    · exact ⟨m, by simpa only [hone, ite_false] using hm⟩
  have htargetGrid' : ∃ m : ℤ, (x.pathCount : ℝ) *
      ((gm06Alg511BinaryRowValue (t.arrs 2801) : ℝ) / ((x.pathCount : ℝ) * x.denominator.value.natAbs)) = m := by
    simpa only [htargetFinal] using htargetGrid
  have hDpos : 0 < x.denominator.value.natAbs := Int.natAbs_pos.mpr rep.denominator_ne_zero
  have hleFinal : (gm06Alg511BinaryRowValue (t.arrs 2800) : ℝ) / ((x.pathCount : ℝ) * x.denominator.value.natAbs) ≤
      (gm06Alg511BinaryRowValue (t.arrs 2801) : ℝ) / ((x.pathCount : ℝ) * x.denominator.value.natAbs) := by
    rw [hbinary 2800 (by decide), hbinary 2801 (by decide)]
    exact hle
  obtain ⟨steps, hsteps, hstepValue⟩ := alg511_binary_target_steps hG.1 hDpos
    (gm06Alg511BinaryRowValue (t.arrs 2800)) (gm06Alg511BinaryRowValue (t.arrs 2801)) hstartGrid' htargetGrid'
      ((alg511_binary_scaled_le_iff hG.1 hDpos _ _).mp hleFinal)
  have ht₂' : u₂ ≤ alg511BinaryDrawingReflectionBudget x.toWindingInput := ht₂
  refine ⟨t, u₁ + u₂, y, H, rp, M, rs, steps, sc, st, cur, target, .seq he₁ he₂, by omega,
    hyK, hyN, hyG, hyTables, hyReg, hyRows, hyEnc,
    (hbinary 2800 (by decide)).trans hcur, (hbinary 2801 (by decide)).trans htarget,
    (hbinary 2802 (by decide)).trans hinc, hsc, hst, hcurLen, htargetLen, hcurBits, htargetBits,
    htheta, ?_, hstepValue, hyFeas, hsuccess₂.trans (hkeep₁.1 90 (by decide)), hyChoice⟩
  exact htargetFinal.symm.trans hsteps

end GraphMinor.GM06
