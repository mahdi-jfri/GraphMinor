module

public import GraphMinor.Compute.GM06Alg511InitialOrientation
public import GraphMinor.GM06.Alg511OrientationExec
public import GraphMinor.GM06.Alg511NumeratorExec
import GraphMinor.Compute.GM06Alg511NumeratorFields
import GraphMinor.Compute.GM06Alg511TargetWordBounds
import GraphMinor.Compute.GM06Alg511InputWordBounds
import Mathlib.Tactic

/-!
# Initial winding and orientation from the raw flow result

For VI (5.11), page 134, compose the verified numerator computation,
target reader and executed orientation choice. The required current
feasibility, graph tables, scalar words and comparison bounds are all
derived from these executions. A fixed enlargement to six times the
component word size holds the cross products. The resulting current
winding is feasible and at most the target in the chosen orientation.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface

/-- The complete initial-winding and orientation phase runs from
the retained supplied drawing and a successful raw flow output.
No current winding, selected linkage or prepared scratch is an input. -/
theorem alg511_initialOrientation_exec {w : ℕ} (x : GM06Alg511WindingInput)
    {G : Drawing ClosedCylinder} (rep : GM06Alg511GraphTurnRep x G)
    (hk : 0 < x.drawing.pathCount) (hden : x.drawing.denominator ≠ 0) (out : List ℕ)
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
    ∃ (s' : State) (t : ℕ) (flip : Bool), Exec (6 * w) gm06Alg511InitialOrientationProg s s' t ∧
      t ≤ 1139 + 110 * (gm06Alg511Words x.drawing).length +
        25 * x.drawing.endpoints.length + 194 * x.edgeTurns.length +
        x.drawing.vertexCount * (163 + 13 * x.drawing.endpoints.length + 26 * x.drawing.pathCount) +
        32 * x.drawing.pathCount ∧
      s'.arrs outArr = out ∧ s'.arrs 1000 = gm06Alg511WindingWords x ∧
      s'.arrs 1201 = gm06Alg511TurnWords (if flip then x.reflected else x).edgeTurns ∧
      s'.arrs 1210 = (if flip then x.reflected else x).drawing.innerCuff ∧
      s'.arrs 1211 = (if flip then x.reflected else x).drawing.outerCuff ∧
      s'.regs 57 = (if flip then 1 else 0) ∧ s'.regs 52 = x.drawing.pathCount ∧
      Nonempty (GM06Alg511GraphTurnRep (if flip then x.reflected else x)
        (if flip then section5ReflectedDrawing x.drawing.pathCount G else G)) ∧
      IsThetaFeasible (if flip then x.reflected else x).drawing.pathCount
        (if flip then section5ReflectedDrawing x.drawing.pathCount G else G) (gm06Alg511CurrentValue s') ∧
      gm06Alg511TargetValue s' = (if flip then x.reflected else x).drawing.target ∧
      gm06Alg511CurrentValue s' ≤ gm06Alg511TargetValue s' ∧
      (IsThetaFeasible (if flip then x.reflected else x).drawing.pathCount
        (if flip then section5ReflectedDrawing x.drawing.pathCount G else G) (gm06Alg511TargetValue s') ↔
          IsThetaFeasible x.drawing.pathCount G x.drawing.target) := by
  have hwpos : 0 < w := by
    by_contra h
    have hz : w = 0 := Nat.eq_zero_of_not_pos h
    subst w
    norm_num at hw
  have h12 : 2 ^ w ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by decide) (by omega)
  have h26 : 2 ^ (2 * w) ≤ 2 ^ (6 * w) := Nat.pow_le_pow_right (by decide) (by omega)
  have h16 := h12.trans h26
  have h16strict : 2 ^ w < 2 ^ (6 * w) := by
    have hstep : 2 ^ w < 2 ^ (w + 1) := by
      rw [Nat.pow_succ]
      have hpos := Nat.two_pow_pos w
      omega
    exact hstep.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hnfit : x.drawing.vertexCount < 2 ^ w := by omega
  have hinner : x.drawing.innerCuff ≠ [] := by
    intro he
    have hh := congrArg List.length rep.inner
    rw [he, List.length_nil, List.length_ofFn] at hh
    omega
  obtain ⟨s₁, t₁, he₁, ht₁, hK₁, hp₁, hq₁, hcurrent₁, harr₁⟩ :=
    alg511_numerator_exec x rep hk out hsys hcount s hw hword hsquare hproduct hlen hout ha hn hwords
  obtain ⟨hends₁, hturns₁, hinner₁, houter₁, hN₁⟩ := gm06Alg511NumeratorProg_fields x rep.graph s s₁ t₁ he₁
    (hw.trans_le h12) hinner ha (hn.trans_le h12) (fun v hv => (hwords v hv).trans_le h12)
    (hnfit.trans_le h12) (hsquare.trans_le h12)
  have hinput₁ : s₁.arrs 1000 = gm06Alg511WindingWords x := (harr₁ 1000 (by decide)).trans ha
  obtain ⟨s₂, t₂, he₂, ht₂, _, _, hD64, hD66, hDpos, htarget₂, hP, hQ, hK, harr₂⟩ :=
    gm06Alg511ReadNormalTargetProg_exec x s₁ hden (by omega) hinput₁
      (hn.trans_le h12) (fun v hv => (hwords v hv).trans_le h12)
  have hp₂ : s₂.regs 54 < 2 ^ (2 * w) := hP ▸ hp₁
  have hq₂ : s₂.regs 55 < 2 ^ (2 * w) := hQ ▸ hq₁
  obtain ⟨ha₂, hb₂, hd₂⟩ := gm06Alg511ReadNormalTargetProg_regs_lt he₂
  have hK₂ : s₂.regs 52 = x.drawing.pathCount := hK.trans hK₁
  have hk₂ : s₂.regs 52 < 2 ^ (2 * w) := by
    rw [hK₂]
    exact ((rep.pathCount_le_vertexCount hk).trans_lt hnfit).trans_le h12
  have hleft := gm06Alg511SumProducts_lt_triple (by omega : 0 < 2 * w) hq₂ hd₂ ha₂ hk₂
  have hright := gm06Alg511SumProducts_lt_triple (by omega : 0 < 2 * w) hp₂ hd₂ hb₂ hk₂
  rw [show 3 * (2 * w) = 6 * w by omega] at hleft hright
  have hcurrent₂ : IsThetaFeasible x.drawing.pathCount G (gm06Alg511CurrentValue s₂) := by
    dsimp only [gm06Alg511CurrentValue]
    rw [hP, hQ, hK₂]
    simpa only [Int.cast_sub, Int.cast_natCast] using hcurrent₁
  have hD : s₂.regs 64 = s₂.regs 66 := hD64.trans hD66.symm
  have htargetValue₂ : gm06Alg511TargetValue s₂ = x.drawing.target := by
    simpa only [gm06Alg511TargetValue, hD] using htarget₂
  have hturnWords : ∀ v ∈ gm06Alg511TurnWords x.edgeTurns, v + 1 < 2 ^ (6 * w) := by
    intro v hv
    exact (Nat.succ_le_of_lt (hwords v (gm06Alg511TurnWords_mem_input x v hv))).trans_lt h16strict
  obtain ⟨s₃, t₃, flip, he₃, ht₃, hkeep, hnewturns, hnewinner, hnewouter, hmode, hcount₃,
      hrep, hfeasible, htarget, hle, hanswer⟩ := alg511_orientation_exec x rep hk s₂
    (by omega) (hnfit.trans_le h16) ((gm06Alg511TurnWordCount_le_input x).trans_lt (hn.trans_le h16))
    hturnWords ((harr₂ 3 (by decide)).trans hends₁) ((harr₂ 11 (by decide)).trans hturns₁)
    ((harr₂ 1004 (by decide)).trans hinner₁) ((harr₂ 1006 (by decide)).trans houter₁)
    ((he₂.regs_eq_of_not_mem_writtenRegs (by decide)).trans hN₁) hK₂
    (hp₂.trans_le h26) (hq₂.trans_le h26) (ha₂.trans_le h26) (hb₂.trans_le h26) (hd₂.trans_le h26)
    (hD ▸ hDpos) hD hleft hright hcurrent₂ htargetValue₂
  refine ⟨s₃, t₁ + (t₂ + t₃), flip,
    .seq (Exec.mono_wordSize (by omega) he₁) (.seq (Exec.mono_wordSize (by omega) he₂) he₃),
    ?_, ?_, ?_, hnewturns, hnewinner, hnewouter, hmode, hcount₃, hrep, hfeasible, htarget, hle, hanswer⟩
  · nlinarith only [ht₁, ht₂, ht₃]
  · exact (hkeep.2 outArr (by decide)).trans ((harr₂ outArr (by decide)).trans
      ((harr₁ outArr (by decide)).trans hout))
  · exact (hkeep.2 1000 (by decide)).trans ((harr₂ 1000 (by decide)).trans hinput₁)

end GraphMinor.GM06
