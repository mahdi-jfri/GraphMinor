module

public import GraphMinor.Compute.GM06Alg511Initialize
public import GraphMinor.GM06.Alg511StoredInitialOrientationExec
public import GraphMinor.GM06.Alg511InitialChecks
import GraphMinor.GM06.Alg511CuffIndices
import Mathlib.Tactic

/-!
# Executing the initial checks and finding an oriented linkage

For VI (5.11), page 134, first test the integral grid and run the
verified maximum-flow program. Rejection proves infeasibility by
(5.10). On success, use the actual returned path system to compute
and store a full linkage, its winding and the orientation choice.
Thus no valid flow system, selected linkage or winding value is
assumed at initialization. Register 90 records successful preparation
for the successor loop, which is still needed for the target test.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface GraphMinor.GM11

/-- The initial phase of VI (5.11) runs from supplied instance words.
Failure proves infeasibility. Success yields a stored actual linkage
with its winding below the target in the computed orientation. -/
theorem alg511_initialize_exec :
    ∃ C c : ℕ, 1 ≤ C ∧ 1 ≤ c ∧ ∀ (x : GM06Alg511WindingInput)
      (G : Drawing ClosedCylinder) (rep : GM06Alg511GraphTurnRep x G)
      (hG : IsCylinderSection5Drawing x.drawing.pathCount G), x.drawing.denominator ≠ 0 →
      ∀ (s : State) (w : ℕ), 3 < 2 ^ w →
      wordSize c (disjointPathsSize x.drawing.flowInput) ≤ w →
      s.arrs 0 = gm06Alg511SearchWords x →
      (gm06Alg511SearchWords x).length < 2 ^ w →
      (∀ v ∈ gm06Alg511SearchWords x, v < 2 ^ w) →
      x.drawing.pathCount < 2 ^ w → x.drawing.numerator.natAbs < 2 ^ w →
      x.drawing.denominator.natAbs < 2 ^ w →
      x.drawing.pathCount * x.drawing.numerator.natAbs < 2 ^ w →
      1 + 3 * x.drawing.vertexCount < 2 ^ w →
      x.drawing.vertexCount * x.drawing.vertexCount < 2 ^ w →
      x.drawing.vertexCount * (gm06Alg511TurnWords x.edgeTurns).sum < 2 ^ w →
      ∃ s' t, Exec (6 * w) gm06Alg511InitializeProg s s' t ∧
        t ≤ 1717 + 66 * (gm06Alg511SearchWords x).length +
          110 * (gm06Alg511Words x.drawing).length + 25 * x.drawing.endpoints.length +
          194 * x.edgeTurns.length + x.drawing.vertexCount *
            (168 + 13 * x.drawing.endpoints.length + 26 * x.drawing.pathCount) +
          32 * x.drawing.pathCount + C * (x.drawing.pathCount + x.drawing.vertexCount + 1) ^ 3 ∧
        s'.arrs 1000 = gm06Alg511WindingWords x ∧
        (s'.regs 90 = 0 ∨ s'.regs 90 = 1) ∧
        (s'.regs 90 = 1 ↔
          (∃ m : ℤ, (x.drawing.pathCount : ℝ) * x.drawing.target = m) ∧
          Nonempty (CylinderLinkage x.drawing.pathCount G)) ∧
        (s'.regs 90 = 0 → ¬ IsThetaFeasible x.drawing.pathCount G x.drawing.target) ∧
        (s'.regs 90 = 1 → ∃ (flip : Bool) (L : CylinderLinkage x.drawing.pathCount G),
          s'.regs 57 = (if flip then 1 else 0) ∧ s'.regs 52 = x.drawing.pathCount ∧
          s'.arrs 1201 = gm06Alg511TurnWords (if flip then x.reflected else x).edgeTurns ∧
          s'.arrs 1210 = (if flip then x.reflected else x).drawing.innerCuff ∧
          s'.arrs 1211 = (if flip then x.reflected else x).drawing.outerCuff ∧
          Nonempty (GM06Alg511GraphTurnRep (if flip then x.reflected else x)
            (if flip then section5ReflectedDrawing x.drawing.pathCount G else G)) ∧
          gm06Alg511CurrentValue s' ≤ gm06Alg511TargetValue s' ∧
          gm06Alg511TargetValue s' = (if flip then x.reflected else x).drawing.target ∧
          (IsThetaFeasible (if flip then x.reflected else x).drawing.pathCount
            (if flip then section5ReflectedDrawing x.drawing.pathCount G else G)
              (gm06Alg511TargetValue s') ↔
                IsThetaFeasible x.drawing.pathCount G x.drawing.target) ∧
          (flip = false → L.HasTheta (gm06Alg511CurrentValue s')) ∧
          (flip = true → (section5ReflectedLinkage hG.1 L).HasTheta (gm06Alg511CurrentValue s')) ∧
          ∀ i : Fin x.drawing.pathCount, ∃ (b : Fin x.drawing.vertexCount)
            (W : GraphWalk (gm06Alg511LabelGraph rep.graph.pairs) (rep.source i) b)
            (actual : GraphWalk G.toGraph (rep.graph.vertex (rep.source i)).val (rep.graph.vertex b).val),
            W.support.map (fun v => v.val) = gm06Alg511SuccVertices x.drawing.vertexCount
              (s'.arrs outArr) x.drawing.vertexCount (rep.source i).val ∧
            gm06Alg511LabelWalkDarts rep.graph.pairs W =
              gm06Alg511ChosenDarts x.drawing (s'.arrs 1300) W.support ∧
            actual.support = W.support.map (fun v => (rep.graph.vertex v).val) ∧
            actual.edges = W.edges.map (fun e => (rep.graph.edge e).val) ∧
            L.pathDrawing i = walkDrawing G actual ∧
            ParametrizesSet (L.curve i) (walkDrawing G actual).U
              (rep.graph.vertex (rep.source i)).val (rep.graph.vertex b).val) := by
  obtain ⟨C, c, hC, hc, hrun⟩ := alg511_initialChecks_exec
  refine ⟨C, c, hC, hc, ?_⟩
  intro x G rep hG hden s w hw hwflow ha hn hwords hkfit hafit hdfit hprod hword hsquare hturnprod
  have hlarge : 2 ^ w ≤ 2 ^ (6 * w) := Nat.pow_le_pow_right (by decide) (by omega)
  have hw' : 1 < 2 ^ (6 * w) := (show 1 < 2 ^ w by omega).trans_le hlarge
  obtain ⟨s₁, t₁, he₁, ht₁, hsaved, hbool, hpass, hcert, hreject⟩ :=
    hrun x G rep.graph rep.source hG rep.flowA_exists_source rep.source_point
      rep.inner_mem_iff rep.outer_mem_iff hden s w (by omega) hwflow ha hn hwords
      hkfit hafit hdfit hprod
  rcases hbool with hz | hone
  · let s₂ := s₁.setReg 90 0
    have hflag : Exec (6 * w) (.assign 90 (.const 0)) s₁ s₂ 2 :=
      .assign (Crossing.eval_const (Nat.two_pow_pos _))
    refine ⟨s₂, t₁ + (1 + 2), .seq (Exec.mono_wordSize (by omega) he₁)
      (.ite_false (Crossing.eval_reg hz (Nat.two_pow_pos _)) hflag), by omega,
      hsaved, Or.inl (by simp [s₂]), ?_, fun _ => hreject hz, ?_⟩
    · constructor
      · intro h
        simp [s₂] at h
      · intro h
        have hh := hpass.mpr h
        omega
    · intro h
      simp [s₂] at h
  · obtain ⟨_, hsys, hcount, hlen⟩ := hcert hone
    have hrow : gm06Alg511WindingWords x ∈ gm06Alg511SearchRows x := by simp [gm06Alg511SearchRows]
    have hfullfit : (gm06Alg511WindingWords x).length < 2 ^ w :=
      (gm06Alg511_encoded_row_length_le hrow).trans_lt hn
    have hfullwords : ∀ v ∈ gm06Alg511WindingWords x, v < 2 ^ w := by
      intro v hv
      exact hwords v (gm06Alg511_mem_encoded_row hrow hv)
    obtain ⟨s₂, t₂, flip, W, actual, L, he₂, ht₂, hout, hinput, hnewturns,
      hnewinner, hnewouter, hmode, hK, hrep, _, htarget, hle, hanswer,
      hthetaKept, hthetaFlipped, hW, hactual⟩ :=
      alg511_storedInitialOrientation_exec x rep hG.1 hden (s₁.arrs outArr) hsys hcount s₁
        hw hword hsquare hturnprod hlen rfl hsaved hfullfit hfullwords
    let s₃ := s₂.setReg 90 1
    have hflag : Exec (6 * w) (.assign 90 (.const 1)) s₂ s₃ 2 :=
      .assign (Crossing.eval_const hw')
    have hcur : gm06Alg511CurrentValue s₃ = gm06Alg511CurrentValue s₂ := by
      simp [s₃, gm06Alg511CurrentValue]
    have htar : gm06Alg511TargetValue s₃ = gm06Alg511TargetValue s₂ := by
      simp [s₃, gm06Alg511TargetValue]
    refine ⟨s₃, t₁ + (1 + (t₂ + 2)), .seq (Exec.mono_wordSize (by omega) he₁)
      (.ite_true (Crossing.eval_reg hone hw') (by decide) (.seq he₂ hflag)), by omega,
      hinput, Or.inr (by simp [s₃]), ?_, ?_, ?_⟩
    · constructor
      · intro _
        exact hpass.mp hone
      · intro _
        simp [s₃]
    · intro hzero
      simp [s₃] at hzero
    · intro _
      refine ⟨flip, L, by simpa [s₃] using hmode, by simpa [s₃] using hK,
        hnewturns, hnewinner, hnewouter, hrep, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hcur, htar]
        exact hle
      · rw [htar]
        exact htarget
      · rw [htar]
        exact hanswer
      · intro hflip
        rw [hcur]
        exact hthetaKept hflip
      · intro hflip
        rw [hcur]
        exact hthetaFlipped hflip
      · intro i
        refine ⟨_, W i, actual i, ?_, (hW i).2, (hactual i).1,
          (hactual i).2.2.1, (hactual i).2.2.2.1, (hactual i).2.2.2.2⟩
        change (W i).support.map (fun v => v.val) = gm06Alg511SuccVertices x.drawing.vertexCount
          (s₂.arrs outArr) x.drawing.vertexCount (rep.source i).val
        rw [hout]
        have hs := congrArg (fun vs : List (Fin x.drawing.vertexCount) =>
          vs.map (fun v => v.val)) (hW i).1
        exact hs.trans (gm06Alg511SuccVertices_eq_traceWalk (s₁.arrs outArr) hsys
          x.drawing.vertexCount (rep.source i)).symm

end GraphMinor.GM06
