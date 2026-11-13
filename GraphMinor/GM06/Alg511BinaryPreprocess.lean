module

public import GraphMinor.GM06.Alg511BinaryInitialWinding
import Mathlib.Tactic

/-!
# Binary preprocessing from the supplied cylinder instance

Run the two initial checks of VI (5.11), page 134, in their printed
order. Save their success bit before doing any winding arithmetic.
Only on success, store the actual flow linkage and compute its
binary winding numerator. The retained success bit separates proved
rejection from the computed linkage and winding handed to orientation.
The complete preprocessing has cubic time in the supplied input length.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Save the result of the two initial checks, then compute the
stored linkage and its binary winding only on success. -/
def gm06Alg511BinaryPreprocessProg : Cmd :=
  .seq gm06Alg511BinaryInitialChecksProg
    (.seq (.assign 90 (.reg 0)) (.ite (.reg 90) gm06Alg511BinaryInitialWindingProg .skip))

end GraphMinor.Compute

namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface

private theorem preprocessing_time (C N a b : ℕ) (hN : 1 ≤ N)
    (ha : a ≤ C * N) (hb : b ≤ 1000000 * N) :
    a + (2 + (1 + b)) ≤ (C + 1000010) * N := by nlinarith only [ha, hb, hN]

/-- From the complete binary input, preprocessing either proves the
target infeasible or retains an actual encoded linkage and its exact
binary winding. It supplies no linkage or winding certificate in the
input and performs no arithmetic on one-word integer magnitudes. -/
theorem alg511_binary_preprocess_exec :
    ∃ C c : ℕ, 1 ≤ C ∧ 1 ≤ c ∧ ∀ (x : GM06Alg511BinaryInput) (G : Drawing ClosedCylinder)
      (rep : GM06Alg511BinaryDrawingRep x G), IsCylinderSection5Drawing x.pathCount G →
      ∀ (s : State) (w : ℕ), 3 < 2 ^ w →
      (gm06Alg511BinarySearchWords x).length + 2 < 2 ^ w →
      x.pathCount + x.numerator.digits.length + x.denominator.digits.length + 4 < 2 ^ w →
      wordSize c (disjointPathsSize x.toWindingInput.drawing.flowInput) ≤ w →
      1 + 3 * x.vertexCount < 2 ^ w → x.vertexCount * x.vertexCount < 2 ^ w →
      x.endpoints.length < 2 ^ w → 1 + x.pathCount + x.pathCount * x.vertexCount < 2 ^ w →
      2 * x.pathCount + x.vertexCount + 2 * (gm06EncodeRows (x.edgeTurns.map GM06Alg511BinaryInteger.words)).length + 10 < 2 ^ w →
      s.arrs 0 = gm06Alg511BinarySearchWords x →
      (∀ word ∈ gm06Alg511BinarySearchWords x, word < 2 ^ w) →
      ∃ t u, Exec w gm06Alg511BinaryPreprocessProg s t u ∧
        u ≤ C * (alg511BinarySearchInputSize x + 1) ^ 3 ∧
        gm06Alg511BinaryLoadedTables x t ∧ t.regs 52 = x.pathCount ∧ t.regs 90 < 2 ∧
        (t.regs 90 = 1 ↔ (∃ m : ℤ, (x.pathCount : ℝ) * x.toWindingInput.drawing.target = m) ∧
          Nonempty (CylinderLinkage x.pathCount G)) ∧
        (t.regs 90 = 0 → ¬ IsThetaFeasible x.pathCount G x.toWindingInput.drawing.target) ∧
        (t.regs 90 = 1 → ∃ (L : CylinderLinkage x.pathCount G) (rows : List (List ℕ)) (digits : List ℕ) (sign : ℕ),
          t.arrs 8 = gm06EncodeRows rows ∧
          GM06LinkageRowsEncoding L rep.graphTurn.graph.initialTagged rep.graphTurn.graph.vertexLabels rep.graphTurn.graph.edgeLabels rows ∧
          t.arrs 2804 = sign :: digits ∧ sign < 2 ∧
          digits.length ≤ 2 * x.pathCount + x.vertexCount + (gm06EncodeRows (x.edgeTurns.map GM06Alg511BinaryInteger.words)).length + 3 ∧
          (∀ d ∈ digits, d < 2) ∧ L.HasTheta ((gm06Alg511BinaryRowValue (t.arrs 2804) : ℝ) / x.pathCount)) := by
  obtain ⟨C, c, hC, hc, hchecks⟩ := alg511_binary_initialChecks_exec
  refine ⟨C + 1000010, c, by omega, hc, ?_⟩
  intro x G rep hG s w hw hfit htarget hwflow hword hsquare hends hcap hsize hinput hwords
  obtain ⟨s₁, u₁, he₁, ht₁, htables₁, hk₁, hbit₁, hpass₁, hno₁, hpath₁⟩ :=
    hchecks x G rep hG s w hw hfit htarget hwflow hinput hwords
  let s₂ := s₁.setReg 90 (s₁.regs 0)
  have he₂ : Exec w (.assign 90 (.reg 0)) s₁ s₂ 2 := .assign (Crossing.eval_reg rfl (hbit₁.trans_le (by omega)))
  have htables₂ : gm06Alg511BinaryLoadedTables x s₂ := htables₁
  have hk₂ : s₂.regs 52 = x.pathCount := (State.setReg_regs_ne _ _ (by decide)).trans hk₁
  have hN : 1 ≤ (alg511BinarySearchInputSize x + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  by_cases hone : s₁.regs 0 = 1
  · obtain ⟨hsys, hcount, hlen⟩ := hpath₁ hone
    obtain ⟨t, u₃, L, rows, digits, sign, he₃, ht₃, htables₃, hk₃, hrows, henc, hnum, hsign, hlenDigits, hbits, htheta, hsuccess⟩ :=
      alg511_binary_initialWinding_exec x rep hG.1 (s₁.arrs outArr) hsys hcount s₂ hw hword hsquare hends hcap hsize
        hlen rfl htables₂ hk₂
    have hkeep : t.regs 90 = s₁.regs 0 := hsuccess.trans (by simp [s₂])
    refine ⟨t, u₁ + (2 + (1 + u₃)), .seq he₁ (.seq he₂
      (.ite_true (Crossing.eval_reg (by simp [s₂]) (hbit₁.trans_le (by omega))) (by omega) he₃)),
      preprocessing_time C _ _ _ hN ht₁ ht₃, htables₃, hk₃, by rw [hkeep]; exact hbit₁,
      by rw [hkeep]; exact hpass₁, ?_, ?_⟩
    · intro hz
      exact hno₁ (hkeep.symm.trans hz)
    · intro _
      exact ⟨L, rows, digits, sign, hrows, henc, hnum, hsign, hlenDigits, hbits, htheta⟩
  · have hzero : s₁.regs 0 = 0 := by omega
    refine ⟨s₂, u₁ + (2 + 2), .seq he₁ (.seq he₂
      (.ite_false (Crossing.eval_reg (by simp [s₂, hzero]) (Nat.two_pow_pos w)) (.skip s₂))),
      ?_, htables₂, hk₂, by simpa only [s₂, State.setReg_regs_self] using hbit₁,
      by simpa only [s₂, State.setReg_regs_self] using hpass₁, ?_, ?_⟩
    · have hh := preprocessing_time C _ u₁ 1 hN ht₁ (by omega)
      omega
    · intro _
      exact hno₁ hzero
    · intro hh
      have heq : s₂.regs 90 = 0 := by simp [s₂, hzero]
      omega

end GraphMinor.GM06
