module

public import GraphMinor.Compute.GM06Alg511InitialChecks
public import GraphMinor.GM06.Alg511FlowLinkage
public import GraphMinor.GM06.Alg511FlowOfLinkage
import GraphMinor.GM06.Section5Feasibility
import GraphMinor.Compute.CrossingOpsBasic
import Mathlib.Tactic

/-!
# Correctness of the first two checks of VI (5.11)

The procedure on page 134 checks (5.10)(i) and then (ii). The concrete
RAM program reads the signed rational target and rejects it if the
integrality test fails. Otherwise it runs the verified maximum-flow
program. The two geometric transfers identify its result with an
actual cylinder linkage. By (5.10), rejection at either check proves
that the requested winding is not feasible. Passing these checks
still requires the winding and successor phases of (5.11).
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface

private theorem flow_preserves_saved_input :
    (1000 : ℕ) ∉ gm06Alg511FlowFlagProg.writtenArrs := by decide

/-- The first two checks of VI (5.11), page 134, run in the paper's
order and return their exact Boolean conjunction. A rejected target
is not feasible by the proved (5.10). The input contains no linkage
or decision certificate. -/
theorem alg511_initialChecks_exec :
    ∃ C c : ℕ, 1 ≤ C ∧ 1 ≤ c ∧ ∀ (x : GM06Alg511WindingInput)
      (G : Drawing ClosedCylinder)
      (rep : GM06SuccessorGraphRep (x.drawing.withLinkage []) G.toGraph)
      (source : Fin x.drawing.pathCount → Fin x.drawing.vertexCount),
      IsCylinderSection5Drawing x.drawing.pathCount G →
      (∀ a ∈ x.drawing.flowInput.A, ∃ i, source i = a) →
      (∀ i, (rep.vertex (source i)).val = cylinderM1Point x.drawing.pathCount i) →
      (∀ a : Fin x.drawing.vertexCount,
        a.val ∈ x.drawing.innerCuff ↔ (rep.vertex a).val ∈ cylinderM1 x.drawing.pathCount) →
      (∀ b : Fin x.drawing.vertexCount,
        b.val ∈ x.drawing.outerCuff ↔ (rep.vertex b).val ∈ cylinderM2 x.drawing.pathCount) →
      x.drawing.denominator ≠ 0 → ∀ (s : State) (w : ℕ), 1 < 2 ^ w →
      wordSize c (disjointPathsSize x.drawing.flowInput) ≤ w →
      s.arrs 0 = gm06Alg511SearchWords x →
      (gm06Alg511SearchWords x).length < 2 ^ w →
      (∀ v ∈ gm06Alg511SearchWords x, v < 2 ^ w) →
      x.drawing.pathCount < 2 ^ w → x.drawing.numerator.natAbs < 2 ^ w →
      x.drawing.denominator.natAbs < 2 ^ w →
      x.drawing.pathCount * x.drawing.numerator.natAbs < 2 ^ w →
      ∃ s' t, Exec w gm06Alg511InitialChecksProg s s' t ∧
        t ≤ 573 + 66 * (gm06Alg511SearchWords x).length +
          C * (x.drawing.pathCount + x.drawing.vertexCount + 1) ^ 3 ∧
        s'.arrs 1000 = gm06Alg511WindingWords x ∧
        (s'.regs 0 = 0 ∨ s'.regs 0 = 1) ∧
        (s'.regs 0 = 1 ↔
          (∃ m : ℤ, (x.drawing.pathCount : ℝ) * x.drawing.target = m) ∧
          Nonempty (CylinderLinkage x.drawing.pathCount G)) ∧
        (s'.regs 0 = 1 → IsValidDisjointPathsOutput x.drawing.flowInput
          (decDisjointPathsOut x.drawing.flowInput (s'.arrs outArr)) ∧
          IsValidPathSystem x.drawing.flowGraph x.drawing.flowInput.A x.drawing.flowInput.B
            (decUsed x.drawing.vertexCount (s'.arrs outArr))
            (decPred x.drawing.vertexCount (s'.arrs outArr))
            (decSucc x.drawing.vertexCount (s'.arrs outArr)) ∧
          (pathStarts (decUsed x.drawing.vertexCount (s'.arrs outArr))
            (decPred x.drawing.vertexCount (s'.arrs outArr))).card = x.drawing.pathCount ∧
          (s'.arrs outArr).length = 1 + 3 * x.drawing.vertexCount) ∧
        (s'.regs 0 = 0 → ¬ IsThetaFeasible x.drawing.pathCount G x.drawing.target) := by
  obtain ⟨C, c, hC, hc, hflow⟩ := gm06Alg511FlowFlagProg_exec_with_pathSystem
  refine ⟨C, c, hC, hc, ?_⟩
  intro x G rep source hG hsource hpoints hinner houter hb s w hw hwflow ha hn hwords
    hkfit hafit hdfit hprod
  have hrow : gm06Alg511WindingWords x ∈ gm06Alg511SearchRows x := by
    simp [gm06Alg511SearchRows]
  have hfullfit : (gm06Alg511WindingWords x).length < 2 ^ w :=
    (gm06Alg511_encoded_row_length_le hrow).trans_lt hn
  have hfullwords : ∀ v ∈ gm06Alg511WindingWords x, v < 2 ^ w := by
    intro v hv
    exact hwords v (gm06Alg511_mem_encoded_row hrow hv)
  have hbaseLen : (gm06Alg511Words x.drawing).length ≤ (gm06Alg511SearchWords x).length :=
    (gm06Alg511_encoded_row_length_le
      (show gm06Alg511Words x.drawing ∈ [gm06Alg511Words x.drawing,
        gm06EncodeRows (x.edgeTurns.map gm06Alg511IntegerWords)] by simp)).trans
      (gm06Alg511_encoded_row_length_le hrow)
  obtain ⟨s₁, t₁, he₁, ht₁, hinput, hsaved⟩ :=
    gm06Alg511LoadSearchProg_exec x s hw ha hn hwords
  obtain ⟨s₂, t₂, he₂, ht₂, hinput₂, hsaved₂, hbool, htest⟩ :=
    gm06Alg511ReadTargetProg_exec x s₁ hb hw hsaved hfullfit hfullwords
      hkfit hafit hdfit hprod
  have hinput' : s₂.arrs inArr = encDisjointPathsIn x.drawing.flowInput := hinput₂.trans hinput
  rcases hbool with hz | hone
  · have hcond : (Expr.reg 0).eval w s₂ = some 0 :=
      GraphMinor.Compute.Crossing.eval_reg hz (Nat.two_pow_pos w)
    have hnot : ¬ ∃ m : ℤ, (x.drawing.pathCount : ℝ) * x.drawing.target = m := by
      intro h
      have hh := htest.mpr h
      omega
    refine ⟨s₂, t₁ + (t₂ + 2), .seq he₁ (.seq he₂ (.ite_false hcond (.skip s₂))),
      by omega, hsaved₂.trans hsaved, Or.inl hz, ?_, ?_, ?_⟩
    · constructor
      · intro hh; omega
      · rintro ⟨hi, _⟩; exact False.elim (hnot hi)
    · intro hh; omega
    · intro _ hf
      exact hnot ((theorem_5_10_proof x.drawing.pathCount G x.drawing.target hG).mp hf).1
  · have hcond : (Expr.reg 0).eval w s₂ = some 1 :=
      GraphMinor.Compute.Crossing.eval_reg hone hw
    have hintegral := htest.mp hone
    obtain ⟨s₃, t₃, he₃, ht₃, hbool₃, hflag, hvalid, hpathcert⟩ := hflow x.drawing.flowInput s₂ w hw hwflow hinput'
    have hgeom :
        (∃ P : Fin x.drawing.pathCount →
          ABWalk x.drawing.flowGraph x.drawing.flowInput.A x.drawing.flowInput.B,
          PairwiseVertexDisjoint P ∧ ∀ i, (P i).walk.IsPath) ↔
        Nonempty (CylinderLinkage x.drawing.pathCount G) := by
      constructor
      · rintro ⟨P, hPdisj, hPsimple⟩
        exact alg511_exists_linkage_of_flowPaths x.drawing rep source hsource hpoints
          (fun b hb' => (houter b).mp (Finset.mem_filter.mp hb').2) P hPdisj hPsimple
      · rintro ⟨L⟩
        exact alg511_exists_flowPaths_of_linkage x.drawing rep hinner houter L
    have hlink := hflag.trans hgeom
    have ht₃' := ht₃.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left C (gm06Alg511FlowSize_le x.drawing)) 3)
    refine ⟨s₃, t₁ + (t₂ + (1 + t₃)),
      .seq he₁ (.seq he₂ (.ite_true hcond (by decide) he₃)), by omega, ?_, hbool₃, ?_,
      fun hpass => ⟨hvalid, hpathcert hpass⟩, ?_⟩
    · rw [Exec.arrs_eq_of_not_mem_writtenArrs he₃ flow_preserves_saved_input]
      exact hsaved₂.trans hsaved
    · exact ⟨fun hh => ⟨hintegral, hlink.mp hh⟩, fun hh => hlink.mpr hh.2⟩
    · intro hz hf
      have hlinkage := ((theorem_5_10_proof x.drawing.pathCount G x.drawing.target hG).mp hf).2.1
      have hh := hlink.mpr hlinkage
      omega

end GraphMinor.GM06
