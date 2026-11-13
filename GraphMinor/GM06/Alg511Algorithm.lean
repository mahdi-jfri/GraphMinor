module

public import GraphMinor.GM06.Alg511BinaryDecision
public import GraphMinor.Compute.GM06Algorithm57Loop
import Mathlib.Tactic

/-!
# Graph Minors VI, algorithm (5.11)

Run the binary initializer, then the bounded successor loop with the
concrete program for (5.7). Each call packs the fixed drawing and the
current ordinary path rows into the six-field successor input. The
existing save-and-restore wrapper protects the drawing, binary rows
and loop registers above the callee's finite write sets.

Simple paths bound the size of every call by a quadratic polynomial
in the original supplied array length. Thus the fifth-degree bound
for (5.7) gives a tenth-degree call bound, and (5.12) bounds the number
of calls linearly. The complete decision takes polynomial time with
logarithmic words, counting all supplied integer digits.
-/

public section
namespace GraphMinor.Compute

/-- The feasibility decision of VI (5.11), using the concrete
successor program of (5.7) at each active loop round. -/
@[expose] def gm06Algorithm511Prog : Cmd :=
  gm06Alg511BinaryDecisionProg gm06Algorithm57Prog

end GraphMinor.Compute

namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface

/-- Every actual reference linkage, in either orientation, gives a
successor instance whose size is quadratic in the original array
length. The estimate uses the simple walks interpreting its rows. -/
theorem alg511_binary_successor_size_le
    (x : GM06Alg511BinaryInput) (y : GM06Alg511WindingInput)
    {H : Drawing ClosedCylinder} (rp : GM06Alg511PositiveDrawingRep y H)
    (hy : y = x.toWindingInput ∨ y = x.toWindingInput.reflected)
    (hk : 0 < x.pathCount)
    {L : CylinderLinkage y.drawing.pathCount H} {rows : List (List ℕ)}
    (henc : GM06LinkageRowsEncoding L rp.graphTurn.graph.initialTagged
      rp.graphTurn.graph.vertexLabels rp.graphTurn.graph.edgeLabels rows) :
    gm06SuccessorInputSize (y.drawing.withLinkage rows) + 1 ≤
      4 * ((gm06Alg511BinarySearchWords x).length + 1) ^ 2 := by
  let S := alg511BinarySearchInputSize x
  let n := (gm06Alg511BinarySearchWords x).length
  obtain ⟨hyK, hyN, _, hbase⟩ := alg511_binary_oriented_code_size x y hy
  have hn : x.vertexCount ≤ S := by unfold S alg511BinarySearchInputSize; omega
  have hkN : x.pathCount ≤ x.vertexCount := by
    simpa only [hyK, hyN] using rp.graphTurn.pathCount_le_vertexCount (hyK.symm ▸ hk)
  have hS : S ≤ 2 * n := alg511_binary_size_le_twice_length x
  have hcode := alg511_successor_input_length_le rp.graphTurn.graph henc
  change (gm06EncodeSuccessorInput (y.drawing.withLinkage rows)).length ≤
    (gm06EncodeSuccessorInput (y.drawing.withLinkage [])).length +
      y.drawing.pathCount + y.drawing.pathCount * y.drawing.vertexCount at hcode
  have hprod : y.drawing.pathCount * y.drawing.vertexCount ≤ (2 * n) * (2 * n) :=
    Nat.mul_le_mul (by omega) (by omega)
  change y.drawing.vertexCount + (gm06EncodeSuccessorInput (y.drawing.withLinkage rows)).length + 1 ≤ _
  nlinarith only [hcode, hprod, hbase, hn, hkN, hyK, hyN, hS]

/-- A call's quadratic size needs only a fixed multiple of the
logarithm of the original supplied array length. -/
theorem alg511_binary_successor_wordSize {M n : ℕ}
    (hM : M + 1 ≤ 4 * (n + 1) ^ 2) :
    wordSize 32 M ≤ wordSize 128 n := by
  apply alg511_wordSize_of_polynomial (by decide : 1 ≤ 4)
  calc
    M + 2 ≤ 4 * (n + 2) ^ 2 := by nlinarith only [hM, Nat.zero_le n]
    _ ≤ (n + 2) ^ 2 * (n + 2) ^ 2 :=
      Nat.mul_le_mul_right _ (by nlinarith only [Nat.zero_le n])
    _ = (n + 2) ^ 4 := by ring

/-- The actual (5.7) command has the raw call contract required by
the protected binary loop. Its input interpretation attaches the
current encoded linkage to the retained positive drawing directly. -/
theorem alg511_binary_successor_exec
    (x : GM06Alg511BinaryInput) (y : GM06Alg511WindingInput)
    {H : Drawing ClosedCylinder} (rp : GM06Alg511PositiveDrawingRep y H)
    (hy : y = x.toWindingInput ∨ y = x.toWindingInput.reflected)
    (hk : 0 < x.pathCount) (hH : IsCylinderSection5Drawing y.drawing.pathCount H)
    (L : CylinderLinkage y.drawing.pathCount H) (rows : List (List ℕ)) (theta : ℝ)
    (henc : GM06LinkageRowsEncoding L rp.graphTurn.graph.initialTagged
      rp.graphTurn.graph.vertexLabels rp.graphTurn.graph.edgeLabels rows)
    (htheta : L.HasTheta theta) (s : State) {w : ℕ}
    (hw : wordSize 128 (gm06Alg511BinarySearchWords x).length ≤ w)
    (hinput : s.arrs 0 = gm06EncodeSuccessorInput (y.drawing.withLinkage rows)) :
    ∃ raw u, Exec w gm06Algorithm57Prog s raw u ∧
      u ≤ (85217050012103 * 4 ^ 5) * ((gm06Alg511BinarySearchWords x).length + 1) ^ 10 ∧
      GM06SuccessorOutputRep (rp.withLinkage L rows henc) theta (raw.regs 0) (raw.arrs 8) := by
  have hsize := alg511_binary_successor_size_le x y rp hy hk henc
  obtain ⟨raw, u, he, ht, _, _, hout⟩ :=
    gm06Algorithm57_polynomial (rp.withLinkage L rows henc) hH htheta s hinput
  refine ⟨raw, u, he.mono_wordSize ((alg511_binary_successor_wordSize hsize).trans hw), ?_, hout⟩
  calc
    u ≤ 85217050012103 * (gm06SuccessorInputSize (y.drawing.withLinkage rows) + 1) ^ 5 := ht
    _ ≤ 85217050012103 * (4 * ((gm06Alg511BinarySearchWords x).length + 1) ^ 2) ^ 5 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsize 5)
    _ = _ := by ring

/-- Graph Minors VI, (5.11), page 134:

"(5.11) *Algorithm to decide if $\theta$ is feasible in $G$.*"

The program checks (5.10)(i) and (ii), orients the computed linkage,
and applies the proved (5.7) command until the target is reached or
its next value is infeasible. The call bound is (5.12). The supplied
input contains the drawing and the rational target, with all integer
signs and digits counted in its length. The output is Boolean and
its exact feasibility meaning holds for every represented instance.
The constants and degree are independent of all input data. -/
theorem algorithm_5_11_proof :
    ∃ C c : ℕ, 1 ≤ C ∧ 1 ≤ c ∧
      ∀ (x : GM06Alg511BinaryInput) (G : Drawing ClosedCylinder)
        (_rep : GM06Alg511BinaryDrawingRep x G), IsCylinderSection5Drawing x.pathCount G →
      ∀ (s : State), s.arrs 0 = gm06Alg511BinarySearchWords x →
      ∃ t u, Exec (wordSize c (gm06Alg511BinarySearchWords x).length) gm06Algorithm511Prog s t u ∧
        u ≤ C * ((gm06Alg511BinarySearchWords x).length + 1) ^ 11 ∧
        t.regs 0 < 2 ∧
        (t.regs 0 = 1 ↔ IsThetaFeasible x.pathCount G x.toWindingInput.drawing.target) ∧
        (t.regs 0 = 0 ↔ ¬ IsThetaFeasible x.pathCount G x.toWindingInput.drawing.target) := by
  obtain ⟨C, c, hC, hc, hrun⟩ := alg511_binary_decision_bitlength_exec
  let D : ℕ := 85217050012103 * 4 ^ 5
  refine ⟨C + 2 * D, max c 128, by omega, by omega, ?_⟩
  intro x G rep hG s hinput
  let n := (gm06Alg511BinarySearchWords x).length
  let w := wordSize (max c 128) n
  obtain ⟨t, u, he, ht, hbit, hyes, hno⟩ :=
    hrun x G rep hG s w (D * (n + 1) ^ 10) gm06Algorithm57Prog
      (wordSize_mono_left (Nat.le_max_left _ _) _) hinput (by
        intro y H rp hy hH L rows theta henc htheta ss hs
        exact alg511_binary_successor_exec x y rp hy hG.1 hH L rows theta henc htheta ss
          (wordSize_mono_left (Nat.le_max_right _ _) _) hs)
  refine ⟨t, u, he, ?_, hbit, hyes, hno⟩
  have hN : 1 ≤ n + 1 := by omega
  have hp : (n + 1) ^ 3 ≤ (n + 1) ^ 11 := Nat.pow_le_pow_right hN (by decide)
  calc
    u ≤ 2 * (n + 1) * (D * (n + 1) ^ 10) + C * (n + 1) ^ 3 := ht
    _ ≤ 2 * (n + 1) * (D * (n + 1) ^ 10) + C * (n + 1) ^ 11 :=
      Nat.add_le_add_left (Nat.mul_le_mul_left C hp) _
    _ = (C + 2 * D) * (n + 1) ^ 11 := by ring

end GraphMinor.GM06
