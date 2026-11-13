module

public import GraphMinor.GM06.Alg511BinaryPreprocess
public import GraphMinor.GM06.Alg511BinaryOrientedDrawing
import GraphMinor.Compute.GM06RefreshContractedMasks
import Mathlib.Tactic

/-!
# Initializing the binary feasibility loop from the supplied input

Execute the initial checks, the flow linkage construction and its
binary winding, then orient the drawing using the computed comparison
bit. A rejected initial check proves infeasibility. Otherwise the
actual retained drawing, linkage and binary values satisfy the data
requirements of the bounded successor loop. The target-step index
comes from the integral winding grid, rather than from an input
certificate. This is the initialization in VI (5.11), page 134.

The time bound is cubic in the complete supplied input length. Large
integer magnitudes never occur in the word-fit premises: only digit
counts and graph/table sizes occur there.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Compute an initial linkage and winding, then normalize the
binary values and orient the drawing only if both initial checks pass. -/
def gm06Alg511BinaryInitializeProg : Cmd :=
  .seq gm06Alg511BinaryPreprocessProg
    (.ite (.reg 90) gm06Alg511BinaryOrientationPhaseProg .skip)

end GraphMinor.Compute

namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface

/-- Each supplied field is bounded by the complete search-code length. -/
theorem alg511_binary_field_length_le (x : GM06Alg511BinaryInput) (row : List ℕ)
    (hrow : row ∈ x.rows) : row.length ≤ (gm06Alg511BinarySearchWords x).length := by
  have hh := gm06Alg511_encoded_row_length_le hrow
  change row.length ≤ x.words.length at hh
  have hlen := gm06Alg511BinarySearchWords_length x
  omega

private theorem orientation_time (k n a d current rot rnum inner outer len u : ℕ)
    (hk : k ≤ n) (hn : n ≤ len) (ha : a + d ≤ len) (hw : current ≤ 3 * n + len + 3)
    (hrot : rot ≤ len) (hrows : rnum ≤ rot) (hi : inner ≤ len) (ho : outer ≤ len)
    (hu : u ≤ 10000 * (k + a + d + current + 5) ^ 2 +
      (81 + 24 * rot + rnum * (607 + 600 * rot) + 28 * inner + 28 * outer +
        12 * (1 + k + k * n) + k * (307 + 40 * k + 150 * n + 100 * (1 + k + k * n)))) :
    u ≤ 2000000 * (len + 1) ^ 3 := by
  let N := len + 1
  have hN : 1 ≤ N := by dsimp only [N]; omega
  have hkN : k ≤ N := by dsimp only [N]; omega
  have hnN : n ≤ N := by dsimp only [N]; omega
  have hrotN : rot ≤ N := by dsimp only [N]; omega
  have hrowsN : rnum ≤ N := hrows.trans hrotN
  have hiN : inner ≤ N := by dsimp only [N]; omega
  have hoN : outer ≤ N := by dsimp only [N]; omega
  have hsum : k + a + d + current + 5 ≤ 8 * N := by dsimp only [N]; omega
  have hpoly : u ≤ 640000 * N ^ 2 +
      (81 + 24 * N + N * (607 + 600 * N) + 28 * N + 28 * N +
        12 * (1 + N + N * N) + N * (307 + 40 * N + 150 * N + 100 * (1 + N + N * N))) := by
    apply hu.trans
    calc
      _ ≤ 10000 * (8 * N) ^ 2 +
          (81 + 24 * N + N * (607 + 600 * N) + 28 * N + 28 * N +
            12 * (1 + N + N * N) + N * (307 + 40 * N + 150 * N + 100 * (1 + N + N * N))) := by gcongr
      _ = _ := by ring
  have h₁ : N ≤ N ^ 3 := Nat.le_self_pow (by decide) N
  have h₂ : N ^ 2 ≤ N ^ 3 := Nat.pow_le_pow_right hN (by decide)
  change u ≤ 2000000 * N ^ 3
  nlinarith only [hpoly, hN, h₁, h₂]

/-- Starting from the complete supplied binary code, initialize
all loop data or prove infeasibility. The positive branch supplies
an actual oriented positive drawing, its encoded linkage, binary
current/target/increment rows and a constructed natural step count.
The complete initialization has cubic input-length time. -/
theorem alg511_binary_initialize_exec :
    ∃ C c : ℕ, 1 ≤ C ∧ 1 ≤ c ∧ ∀ (x : GM06Alg511BinaryInput) (G : Drawing ClosedCylinder)
      (rep : GM06Alg511BinaryDrawingRep x G), IsCylinderSection5Drawing x.pathCount G →
      ∀ (s : State) (w : ℕ), 3 < 2 ^ w →
      (gm06Alg511BinarySearchWords x).length + 2 < 2 ^ w →
      wordSize c (disjointPathsSize x.toWindingInput.drawing.flowInput) ≤ w →
      1 + 3 * x.vertexCount < 2 ^ w → x.vertexCount * x.vertexCount < 2 ^ w →
      x.endpoints.length < 2 ^ w → 1 + x.pathCount + x.pathCount * x.vertexCount < 2 ^ w →
      3 * x.pathCount + x.vertexCount + x.numerator.digits.length + x.denominator.digits.length +
        2 * (gm06EncodeRows (x.edgeTurns.map GM06Alg511BinaryInteger.words)).length + 12 < 2 ^ w →
      2 * (rep.graphTurn.graph.pairs.length + x.pathCount + x.pathCount) < 2 ^ w →
      (gm06EncodeRows x.rotations).length < 2 ^ w →
      (∀ d ∈ gm06EncodeRows x.rotations, d < 2 ^ w) →
      s.arrs 0 = gm06Alg511BinarySearchWords x →
      (∀ word ∈ gm06Alg511BinarySearchWords x, word < 2 ^ w) →
      ∃ t u, Exec w gm06Alg511BinaryInitializeProg s t u ∧
        u ≤ C * (alg511BinarySearchInputSize x + 1) ^ 3 ∧ t.regs 90 < 2 ∧
        (t.regs 90 = 0 → ¬ IsThetaFeasible x.pathCount G x.toWindingInput.drawing.target) ∧
        (t.regs 90 = 1 → ∃ (y : GM06Alg511WindingInput) (H : Drawing ClosedCylinder)
          (rp : GM06Alg511PositiveDrawingRep y H) (M : CylinderLinkage y.drawing.pathCount H)
          (rs : List (List ℕ)) (steps sc st : ℕ) (cur target : List ℕ),
          (y = x.toWindingInput ∨ y = x.toWindingInput.reflected) ∧
          y.drawing.pathCount = x.pathCount ∧ y.drawing.vertexCount = x.vertexCount ∧
          IsCylinderSection5Drawing y.drawing.pathCount H ∧ alg511BinaryLoopTables y t ∧
          t.regs 52 = y.drawing.pathCount ∧ t.arrs 8 = gm06EncodeRows rs ∧
          GM06LinkageRowsEncoding M rp.graphTurn.graph.initialTagged rp.graphTurn.graph.vertexLabels rp.graphTurn.graph.edgeLabels rs ∧
          t.arrs 2800 = sc :: cur ∧ t.arrs 2801 = st :: target ∧
          t.arrs 2802 = 0 :: x.denominator.digits.map Bool.toNat ∧ sc < 2 ∧ st < 2 ∧
          cur.length ≤ 2 * x.pathCount + x.vertexCount +
            (gm06EncodeRows (x.edgeTurns.map GM06Alg511BinaryInteger.words)).length + 3 + x.denominator.digits.length ∧
          target.length ≤ x.pathCount + 1 + x.numerator.digits.length ∧
          (∀ d ∈ cur, d < 2) ∧ (∀ d ∈ target, d < 2) ∧
          M.HasTheta ((gm06Alg511BinaryRowValue (t.arrs 2800) : ℝ) / ((x.pathCount : ℝ) * x.denominator.value.natAbs)) ∧
          y.drawing.target = (gm06Alg511BinaryRowValue (t.arrs 2800) : ℝ) / ((x.pathCount : ℝ) * x.denominator.value.natAbs) +
            (steps : ℝ) / x.pathCount ∧
          gm06Alg511BinaryRowValue (t.arrs 2801) = gm06Alg511BinaryRowValue (t.arrs 2800) + (steps : ℤ) * x.denominator.value.natAbs ∧
          (IsThetaFeasible y.drawing.pathCount H y.drawing.target ↔ IsThetaFeasible x.pathCount G x.toWindingInput.drawing.target)) := by
  obtain ⟨C, c, hC, hc, hpre⟩ := alg511_binary_preprocess_exec
  refine ⟨C + 2000010, c, by omega, hc, ?_⟩
  intro x G rep hG s w hw hfit hwflow hword hsquare hends hcap hsize haug hrotFit hrotWords hinput hwords
  obtain ⟨s₁, u₁, he₁, ht₁, htables₁, hk₁, hbit₁, hpass₁, hno₁, hpath₁⟩ :=
    hpre x G rep hG s w hw hfit (by omega) hwflow hword hsquare hends hcap (by omega) hinput hwords
  have hN : 1 ≤ (alg511BinarySearchInputSize x + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  by_cases hone : s₁.regs 90 = 1
  · obtain ⟨L, rows, digits, sign, hrows, henc, hnum, hsign, hlenDigits, hbits, htheta⟩ := hpath₁ hone
    change digits.length ≤ 2 * x.pathCount + x.vertexCount +
      (gm06EncodeRows (x.edgeTurns.map GM06Alg511BinaryInteger.words)).length + 3 at hlenDigits
    have hkn : x.pathCount ≤ x.vertexCount := rep.graphTurn.pathCount_le_vertexCount hG.1
    have hfields : alg511BinaryLoopTables x.toWindingInput s₁ :=
      ⟨htables₁.1 ⟨0, by decide⟩, htables₁.1 ⟨1, by decide⟩, htables₁.1 ⟨2, by decide⟩,
        htables₁.1 ⟨3, by decide⟩, htables₁.1 ⟨4, by decide⟩⟩
    obtain ⟨t, u₂, y, H, rp, M, rs, steps, sc, st, cur, target, he₂, ht₂, hyK, hyN, hyG, hyTables,
      hyReg, hyRows, hyEnc, hcur, htarget, hinc, hsc, hst, hcurLen, htargetLen, hcurBits, htargetBits,
      htheta₂, htargetValue, htargetStep, hyFeas, hsuccess, hyChoice⟩ :=
      alg511_binary_orientationPhase_exec x rep hG L rows henc sign digits s₁
        (by simpa only [hnum] using htheta) (hpass₁.mp hone).1 hw (by omega) (by omega)
        haug hrotFit hrotWords hcap hsign hbits hfields hk₁ (htables₁.1 ⟨6, by decide⟩)
          (htables₁.1 ⟨7, by decide⟩) hnum hrows
    have hlen := gm06Alg511BinarySearchWords_length x
    have hturn := alg511_binary_field_length_le x
      (gm06EncodeRows (x.edgeTurns.map GM06Alg511BinaryInteger.words)) (by simp [GM06Alg511BinaryInput.rows])
    have hrot := alg511_binary_field_length_le x (gm06EncodeRows x.rotations) (by simp [GM06Alg511BinaryInput.rows])
    have hi := alg511_binary_field_length_le x x.innerCuff (by simp [GM06Alg511BinaryInput.rows])
    have ho := alg511_binary_field_length_le x x.outerCuff (by simp [GM06Alg511BinaryInput.rows])
    have htargetSize := alg511_binary_target_size_le x
    simp only [alg511BinaryInputSize, GM06Alg511BinaryInteger.words_length] at htargetSize
    have hrotRows : x.rotations.length ≤ (gm06EncodeRows x.rotations).length := by
      have hh := gm06EncodeRows_length x.rotations
      omega
    have hu₂ : u₂ ≤ 2000000 * (alg511BinarySearchInputSize x + 1) ^ 3 :=
      orientation_time x.pathCount x.vertexCount x.numerator.digits.length x.denominator.digits.length
        digits.length (gm06EncodeRows x.rotations).length x.rotations.length x.innerCuff.length x.outerCuff.length
        (alg511BinarySearchInputSize x) u₂ (rep.graphTurn.pathCount_le_vertexCount hG.1)
        (by unfold alg511BinarySearchInputSize; omega)
        (by unfold alg511BinarySearchInputSize; omega)
        (by unfold alg511BinarySearchInputSize; omega)
        (by unfold alg511BinarySearchInputSize; omega) hrotRows
        (by unfold alg511BinarySearchInputSize; omega) (by unfold alg511BinarySearchInputSize; omega) ht₂
    refine ⟨t, u₁ + (1 + u₂), .seq he₁ (.ite_true
      (Crossing.eval_reg hone (by omega)) (by decide) he₂), ?_, by rw [hsuccess]; exact hbit₁,
      (fun hz => hno₁ (hsuccess.symm.trans hz)), ?_⟩
    · nlinarith only [ht₁, hu₂, hN]
    · intro _
      exact ⟨y, H, rp, M, rs, steps, sc, st, cur, target, hyChoice, hyK, hyN, hyG, hyTables,
        hyReg, hyRows, hyEnc, hcur, htarget, hinc, hsc, hst, hcurLen.trans (Nat.add_le_add_right hlenDigits _),
        htargetLen, hcurBits, htargetBits, htheta₂, htargetValue, htargetStep, hyFeas⟩
  · have hz : s₁.regs 90 = 0 := by omega
    refine ⟨s₁, u₁ + 2, .seq he₁ (.ite_false (Crossing.eval_reg hz (Nat.two_pow_pos w)) (.skip s₁)),
      by nlinarith only [ht₁, hN], hbit₁, hno₁, ?_⟩
    intro hh
    omega

end GraphMinor.GM06
