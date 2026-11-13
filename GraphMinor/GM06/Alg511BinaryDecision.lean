module

public import GraphMinor.GM06.Alg511BinaryLoopResources
import GraphMinor.Compute.GM06Alg511BinaryIntegral
import Mathlib.Tactic

/-!
# Composing initialization and the bounded feasibility loop

Start with the supplied binary cylinder instance. The initializer
checks integrality and linkage existence, constructs an actual stored
linkage, computes its winding and orients the drawing. On success,
run the bounded successor loop on its computed binary rows. On
failure, return zero. The exact feasibility answer follows in both
branches, with logarithmic words and input-length time bounds.

The successor command and its precise raw execution contract are
composition parameters here. This file proves the whole assembly
for VI (5.11), pages 134–135, but does not assert the existence of
the program for VI (5.7).
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Initialize from supplied binary input, then run the bounded
successor loop exactly when both initial checks have passed. -/
def gm06Alg511BinaryDecisionProg (successor : Cmd) : Cmd :=
  .seq gm06Alg511BinaryInitializeProg
    (.ite (.reg 90) (gm06Alg511BinaryLoopProg successor) (.assign 0 (.const 0)))

end GraphMinor.Compute

namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface

/-- The complete binary decision command computes the exact original
feasibility answer from its supplied code. Its only program parameter
is the raw successor command with the input/output contract of (5.7).
All resource premises are discharged from logarithmic words in the
original complete input size, including arbitrary integer digits. -/
theorem alg511_binary_decision_exec :
    ∃ C c : ℕ, 1 ≤ C ∧ 1 ≤ c ∧ ∀ (x : GM06Alg511BinaryInput) (G : Drawing ClosedCylinder)
      (_rep : GM06Alg511BinaryDrawingRep x G), IsCylinderSection5Drawing x.pathCount G →
      ∀ (s : State) (w B : ℕ) (callee : Cmd),
      wordSize c (alg511BinarySearchInputSize x) ≤ w → s.arrs 0 = gm06Alg511BinarySearchWords x →
      (∀ (y : GM06Alg511WindingInput) (H : Drawing ClosedCylinder)
        (rp : GM06Alg511PositiveDrawingRep y H),
        (y = x.toWindingInput ∨ y = x.toWindingInput.reflected) →
        IsCylinderSection5Drawing y.drawing.pathCount H →
        ∀ (L : CylinderLinkage y.drawing.pathCount H) (rows : List (List ℕ)) (theta : ℝ)
          (henc : GM06LinkageRowsEncoding L rp.graphTurn.graph.initialTagged rp.graphTurn.graph.vertexLabels
            rp.graphTurn.graph.edgeLabels rows), L.HasTheta theta →
        ∀ ss, ss.arrs 0 = gm06EncodeSuccessorInput (y.drawing.withLinkage rows) →
          ∃ raw u, Exec w callee ss raw u ∧ u ≤ B ∧
            GM06SuccessorOutputRep (rp.withLinkage L rows henc) theta (raw.regs 0) (raw.arrs 8)) →
      ∃ t u, Exec w (gm06Alg511BinaryDecisionProg callee) s t u ∧
        u ≤ (alg511BinarySearchInputSize x + 1) * B + C * (alg511BinarySearchInputSize x + 1) ^ 3 ∧
        t.regs 0 < 2 ∧
        (t.regs 0 = 1 ↔ IsThetaFeasible x.pathCount G x.toWindingInput.drawing.target) ∧
        (t.regs 0 = 0 ↔ ¬ IsThetaFeasible x.pathCount G x.toWindingInput.drawing.target) := by
  obtain ⟨C, c, hC, hc, hinit⟩ := alg511_binary_initialize_exec
  refine ⟨C + 20010, 6 + 3 * c, by omega, by omega, ?_⟩
  intro x G rep hG s w B callee hw hinput hcall
  obtain ⟨hw3, hfit, hflow, hword, hsquare, he, hpathCap, hinitSize, haug, hrotFit, hrotWords, hinputWords⟩ :=
    alg511_binary_initialize_resources c x rep hG.1 hw
  obtain ⟨s₁, u₁, he₁, ht₁, hbit₁, hno₁, hpositive⟩ :=
    hinit x G rep hG s w hw3 hfit hflow hword hsquare he hpathCap hinitSize haug hrotFit hrotWords hinput hinputWords
  have hN : 1 ≤ (alg511BinarySearchInputSize x + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  by_cases hone : s₁.regs 90 = 1
  · obtain ⟨y, H, rp, M, rs, steps, sc, st, cur, target, hyChoice, hyK, hyN, hyG, hyTables,
      hyReg, hyRows, hyEnc, hcur, htarget, hinc, hsc, hst, hcurLen, htargetLen, hcurBits, htargetBits,
      htheta, htargetValue, hstepValue, hyFeas⟩ := hpositive hone
    obtain ⟨_, hsize, hkfit, hnfit, hefit, hpathfit, hcodefit, hbaseWords, hbaseSize, htargetSize, hcapSize, hcodeSize⟩ :=
      alg511_binary_loop_resources x y rp hyChoice hG.1 target htargetLen
        ((wordSize_mono_left (by omega) _).trans hw)
    have hDpos : 0 < x.denominator.value.natAbs := Int.natAbs_pos.mpr rep.denominator_ne_zero
    have hDvalue : gm06Alg511BinaryRowValue (0 :: x.denominator.digits.map Bool.toNat) = x.denominator.value.natAbs := by
      simp only [gm06Alg511BinaryRowValue, List.headD_cons, List.tail_cons, gm06Alg511BinarySignedValue,
        Nat.zero_ne_one, ite_false, GM06Alg511BinaryInteger.natAbs_value]
    have hDbits : ∀ d ∈ x.denominator.digits.map Bool.toNat, d < 2 := by
      intro d hd
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp hd
      cases b <;> decide
    have hDlen : (x.denominator.digits.map Bool.toNat).length ≤ alg511BinaryCurrentWidth x := by
      simp only [List.length_map, alg511BinaryCurrentWidth]
      omega
    let start : ℝ := (gm06Alg511BinaryRowValue (s₁.arrs 2800) : ℝ) /
      ((x.pathCount : ℝ) * x.denominator.value.natAbs)
    have hfmt : alg511BinaryRowFormat (s₁.arrs 2800) (alg511BinaryCurrentWidth x) :=
      ⟨sc, cur, hcur, hsc, hcurLen, hcurBits⟩
    have hL : alg511BinaryLoopLinkage rp start 0 s₁ :=
      ⟨M, rs, hyRows, hyEnc, by simpa only [Nat.cast_zero, zero_div, add_zero] using htheta⟩
    obtain ⟨t, u₂, he₂, ht₂, hbit₂, hyes₂, hno₂, _⟩ :=
      alg511_binary_loop_exec rp hyG st 0 target (x.denominator.digits.map Bool.toNat)
        (alg511BinaryCurrentWidth x) steps x.denominator.value.natAbs start (gm06Alg511BinaryRowValue (s₁.arrs 2800))
        callee s₁ hw3 hsize hkfit hnfit hefit hpathfit hcodefit hbaseWords hst (by decide) htargetBits hDbits hDlen
        hDpos hDvalue (by rw [← htarget]; exact hstepValue) ⟨M, htheta⟩ hyTables hyReg htarget hinc hfmt rfl hL
        (hcall y H rp hyChoice hyG)
    have htime₂ : u₂ ≤ (alg511BinarySearchInputSize x + 1) * B + 20000 * (alg511BinarySearchInputSize x + 1) ^ 3 :=
      alg511_binary_loop_time_le B _ _ _ _ _ _ u₂ (by omega) hcodeSize hbaseSize hcapSize htargetSize
        (by have hh := alg511_binary_target_size_le x
            have hl := gm06Alg511BinarySearchWords_length x
            simp only [List.length_map, alg511BinaryInputSize, GM06Alg511BinaryInteger.words_length] at hh ⊢
            unfold alg511BinarySearchInputSize
            omega) ht₂
    have hvalue : start + (steps : ℝ) / y.drawing.pathCount = y.drawing.target := by
      rw [hyK]
      exact htargetValue.symm
    have hyes : t.regs 0 = 1 ↔ IsThetaFeasible x.pathCount G x.toWindingInput.drawing.target := by
      rw [hyes₂, hvalue]
      exact hyFeas
    have hno : t.regs 0 = 0 ↔ ¬ IsThetaFeasible x.pathCount G x.toWindingInput.drawing.target := by
      rw [hno₂, hvalue, hyFeas]
    refine ⟨t, u₁ + (1 + u₂), .seq he₁ (.ite_true (Crossing.eval_reg hone (by omega)) (by decide) he₂),
      ?_, hbit₂, hyes, hno⟩
    nlinarith only [ht₁, htime₂, hN]
  · have hzero : s₁.regs 90 = 0 := by omega
    let t := s₁.setReg 0 0
    have he₂ : Exec w (.assign 0 (.const 0)) s₁ t 2 := .assign (Crossing.eval_const (Nat.two_pow_pos w))
    have hzeroT : t.regs 0 = 0 := State.setReg_regs_self _ _ _
    have hnot := hno₁ hzero
    refine ⟨t, u₁ + 3, .seq he₁ (.ite_false (Crossing.eval_reg hzero (Nat.two_pow_pos w)) he₂),
      ?_, by rw [hzeroT]; decide, by simp only [hzeroT, Nat.zero_ne_one, false_iff]; exact hnot, ?_⟩
    · nlinarith only [ht₁, hN]
    · exact ⟨fun _ => hnot, fun _ => hzeroT⟩

/-- The repeated flow layout explicitly lists all vertex membership
bits, so counting the vertices separately changes the actual supplied
array length by at most a factor of two. -/
theorem alg511_binary_size_le_twice_length (x : GM06Alg511BinaryInput) :
    alg511BinarySearchInputSize x ≤ 2 * (gm06Alg511BinarySearchWords x).length := by
  have hsearch := gm06Alg511BinarySearchWords_length x
  have hflow : (encDisjointPathsIn x.toWindingInput.drawing.flowInput).length =
      3 + 2 * (edgeListOf x.toWindingInput.drawing.flowInput.G).length + 2 * x.vertexCount := by
    simp only [encDisjointPathsIn, List.length_append, length_encGraph, length_bitSetList, List.length_singleton]
    change 2 + 2 * _ + x.vertexCount + x.vertexCount + 1 = _
    omega
  unfold alg511BinarySearchInputSize
  omega

/-- The complete decision assembly uses logarithmic words and has
polynomial overhead measured in the actual supplied array length,
including every integer sign and bit. The successor command remains
a parameter with its exact raw execution contract. -/
theorem alg511_binary_decision_bitlength_exec :
    ∃ C c : ℕ, 1 ≤ C ∧ 1 ≤ c ∧ ∀ (x : GM06Alg511BinaryInput) (G : Drawing ClosedCylinder)
      (_rep : GM06Alg511BinaryDrawingRep x G), IsCylinderSection5Drawing x.pathCount G →
      ∀ (s : State) (w B : ℕ) (callee : Cmd),
      wordSize c (gm06Alg511BinarySearchWords x).length ≤ w → s.arrs 0 = gm06Alg511BinarySearchWords x →
      (∀ (y : GM06Alg511WindingInput) (H : Drawing ClosedCylinder)
        (rp : GM06Alg511PositiveDrawingRep y H),
        (y = x.toWindingInput ∨ y = x.toWindingInput.reflected) →
        IsCylinderSection5Drawing y.drawing.pathCount H →
        ∀ (L : CylinderLinkage y.drawing.pathCount H) (rows : List (List ℕ)) (theta : ℝ)
          (henc : GM06LinkageRowsEncoding L rp.graphTurn.graph.initialTagged rp.graphTurn.graph.vertexLabels
            rp.graphTurn.graph.edgeLabels rows), L.HasTheta theta →
        ∀ ss, ss.arrs 0 = gm06EncodeSuccessorInput (y.drawing.withLinkage rows) →
          ∃ raw u, Exec w callee ss raw u ∧ u ≤ B ∧
            GM06SuccessorOutputRep (rp.withLinkage L rows henc) theta (raw.regs 0) (raw.arrs 8)) →
      ∃ t u, Exec w (gm06Alg511BinaryDecisionProg callee) s t u ∧
        u ≤ 2 * ((gm06Alg511BinarySearchWords x).length + 1) * B + C * ((gm06Alg511BinarySearchWords x).length + 1) ^ 3 ∧
        t.regs 0 < 2 ∧
        (t.regs 0 = 1 ↔ IsThetaFeasible x.pathCount G x.toWindingInput.drawing.target) ∧
        (t.regs 0 = 0 ↔ ¬ IsThetaFeasible x.pathCount G x.toWindingInput.drawing.target) := by
  obtain ⟨C, c, hC, hc, hrun⟩ := alg511_binary_decision_exec
  refine ⟨8 * C, 2 * c, by omega, by omega, ?_⟩
  intro x G rep hG s w B callee hw hinput hcall
  have hsize := alg511_binary_size_le_twice_length x
  have hpoly : alg511BinarySearchInputSize x + 2 ≤ ((gm06Alg511BinarySearchWords x).length + 2) ^ 2 := by
    nlinarith only [hsize, Nat.zero_le (gm06Alg511BinarySearchWords x).length]
  have hword : wordSize c (alg511BinarySearchInputSize x) ≤ w :=
    (alg511_wordSize_of_polynomial (c := c) (by decide : 1 ≤ 2) hpoly).trans
      (by simpa only [Nat.mul_comm c 2] using hw)
  obtain ⟨t, u, he, ht, hbit, hyes, hno⟩ := hrun x G rep hG s w B callee hword hinput hcall
  refine ⟨t, u, he, ?_, hbit, hyes, hno⟩
  calc
    u ≤ (2 * ((gm06Alg511BinarySearchWords x).length + 1)) * B +
        C * (2 * ((gm06Alg511BinarySearchWords x).length + 1)) ^ 3 := by
      apply ht.trans
      gcongr <;> omega
    _ = _ := by ring

/-- A polynomial successor bound yields a polynomial bound for the
whole command in the supplied bit-count input size. The degree and
constants are independent of the target and turn magnitudes. -/
theorem alg511_binary_decision_time_polynomial (C D degree size B u : ℕ)
    (hB : B ≤ D * (size + 1) ^ degree)
    (hu : u ≤ (size + 1) * B + C * (size + 1) ^ 3) :
    u ≤ (C + D) * (size + 1) ^ (degree + 3) := by
  have hN : 1 ≤ size + 1 := by omega
  have hcall : (size + 1) * B ≤ D * (size + 1) ^ (degree + 3) := by
    calc
      _ ≤ (size + 1) * (D * (size + 1) ^ degree) := Nat.mul_le_mul_left _ hB
      _ = D * (size + 1) ^ (degree + 1) := by rw [Nat.pow_succ]; ring
      _ ≤ _ := Nat.mul_le_mul_left D (Nat.pow_le_pow_right hN (by omega))
  have hinit : C * (size + 1) ^ 3 ≤ C * (size + 1) ^ (degree + 3) :=
    Nat.mul_le_mul_left C (Nat.pow_le_pow_right hN (by omega))
  nlinarith only [hu, hcall, hinit]

end GraphMinor.GM06
