module

public import GraphMinor.GM06.Alg511BinaryWordSize
public import GraphMinor.GM06.Alg511BinaryLoopExec
import GraphMinor.Compute.GM06RefreshContractedMasks
import Mathlib.Tactic

/-!
# Input-length resources for the oriented binary loop

Reflection preserves the sizes of the drawing fields. An empty-path
successor code is no longer than the original supplied binary code.
Actual path rows add at most k rows with fewer than n darts each.
The current binary width is bounded by the supplied turn and target
digit counts, and each successful round adds at most one digit.

These facts place the entire bounded loop of VI (5.11), pages 134–135,
inside logarithmic words in the original complete input size. They
also bound its extra time by a fixed cubic polynomial plus the call
cap times the actual successor-program time.
-/

@[expose] public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface

/-- A uniform initial current-row width, including multiplication
by the supplied denominator magnitude. It counts digits only. -/
def alg511BinaryCurrentWidth (x : GM06Alg511BinaryInput) : ℕ :=
  2 * x.pathCount + x.vertexCount +
    (gm06EncodeRows (x.edgeTurns.map GM06Alg511BinaryInteger.words)).length + 3 + x.denominator.digits.length

private theorem empty_code_length (x : GM06Alg511Input) :
    (gm06EncodeSuccessorInput (x.withLinkage [])).length =
      9 + x.endpoints.length + (gm06EncodeRows x.rotations).length + x.innerCuff.length + x.outerCuff.length := by
  rw [gm06EncodeSuccessorInput, gm06EncodeRows_length]
  simp only [gm06SuccessorRows, GM06Alg511Input.withLinkage, List.length_cons, List.length_nil,
    List.flatten_cons, List.flatten_nil, List.length_append, gm06EncodeRows, gm06EncodeRowsPayload, List.flatMap_nil]
  omega

/-- Orientation changes no drawing-field length, so even the
reflected successor's empty-path code fits within the supplied code. -/
theorem alg511_binary_oriented_code_size (x : GM06Alg511BinaryInput) (y : GM06Alg511WindingInput)
    (hy : y = x.toWindingInput ∨ y = x.toWindingInput.reflected) :
    y.drawing.pathCount = x.pathCount ∧ y.drawing.vertexCount = x.vertexCount ∧
      y.drawing.endpoints = x.endpoints ∧
      (gm06EncodeSuccessorInput (y.drawing.withLinkage [])).length ≤ alg511BinarySearchInputSize x := by
  have hsearch := gm06Alg511BinarySearchWords_length x
  have hlen := gm06EncodeRows_length x.rows
  change x.words.length = _ at hlen
  simp only [GM06Alg511BinaryInput.rows, List.length_cons, List.length_nil,
    List.flatten_cons, List.flatten_nil, List.length_append] at hlen
  have hbase : (gm06EncodeSuccessorInput (x.toWindingInput.drawing.withLinkage [])).length ≤
      alg511BinarySearchInputSize x := by
    rw [empty_code_length]
    change 9 + x.endpoints.length + (gm06EncodeRows x.rotations).length + x.innerCuff.length + x.outerCuff.length ≤ _
    unfold alg511BinarySearchInputSize
    omega
  rcases hy with rfl | rfl
  · exact ⟨rfl, rfl, rfl, hbase⟩
  · refine ⟨rfl, rfl, rfl, ?_⟩
    have hrot : (gm06EncodeRows x.toWindingInput.reflected.drawing.rotations).length =
        (gm06EncodeRows x.rotations).length :=
      gm06Alg511ReflectedTable_code_length false (x.endpoints.length / 2) x.pathCount x.rotations
    have hi : x.toWindingInput.reflected.drawing.innerCuff.length = x.innerCuff.length := by
      simp only [GM06Alg511WindingInput.reflected, GM06Alg511Input.reflected,
        GM06Alg511BinaryInput.toWindingInput, gm06Alg511ReflectCuffWords, List.length_map, List.length_range]
    have ho : x.toWindingInput.reflected.drawing.outerCuff.length = x.outerCuff.length := by
      simp only [GM06Alg511WindingInput.reflected, GM06Alg511Input.reflected,
        GM06Alg511BinaryInput.toWindingInput, gm06Alg511ReflectCuffWords, List.length_map, List.length_range]
    rw [empty_code_length, hrot, hi, ho]
    rw [empty_code_length] at hbase
    exact hbase

/-- Every loop capacity and binary digit width fits in logarithmic
words of the original supplied size, in either computed orientation.
The bound on each base-code word follows from the actual positive
input representation, including both cuff families. -/
theorem alg511_binary_loop_resources (x : GM06Alg511BinaryInput) (y : GM06Alg511WindingInput)
    {H : Drawing ClosedCylinder} (rp : GM06Alg511PositiveDrawingRep y H)
    (hy : y = x.toWindingInput ∨ y = x.toWindingInput.reflected) (hk : 0 < x.pathCount)
    (target : List ℕ) (htarget : target.length ≤ x.pathCount + 1 + x.numerator.digits.length)
    {w : ℕ} (hw : wordSize 6 (alg511BinarySearchInputSize x) ≤ w) :
    3 < 2 ^ w ∧
      max (alg511BinaryCurrentWidth x) target.length + (1 + y.drawing.vertexCount / y.drawing.pathCount) + 2 < 2 ^ w ∧
      y.drawing.pathCount < 2 ^ w ∧ y.drawing.vertexCount + 2 < 2 ^ w ∧
      y.drawing.endpoints.length < 2 ^ w ∧
      1 + y.drawing.pathCount + y.drawing.pathCount * y.drawing.vertexCount < 2 ^ w ∧
      (gm06EncodeSuccessorInput (y.drawing.withLinkage [])).length +
        y.drawing.pathCount + y.drawing.pathCount * y.drawing.vertexCount < 2 ^ w ∧
      (∀ d ∈ gm06EncodeSuccessorInput (y.drawing.withLinkage []), d < 2 ^ w) ∧
      alg511BinaryCurrentWidth x ≤ 6 * (alg511BinarySearchInputSize x + 1) ∧
      target.length ≤ 3 * (alg511BinarySearchInputSize x + 1) ∧
      1 + y.drawing.vertexCount / y.drawing.pathCount ≤ alg511BinarySearchInputSize x + 1 ∧
      (gm06EncodeSuccessorInput (y.drawing.withLinkage [])).length +
        y.drawing.pathCount + y.drawing.pathCount * y.drawing.vertexCount ≤ 3 * (alg511BinarySearchInputSize x + 1) ^ 2 := by
  let S := alg511BinarySearchInputSize x
  have hS : 0 ≤ S := Nat.zero_le S
  have hsmall : ∀ q : ℕ, q ≤ 16 * (S + 1) ^ 2 → q < 2 ^ w := by
    intro q hq
    exact hq.trans_lt ((alg511_quadratic_allowance_fits S).trans_le (Nat.pow_le_pow_right (by decide) hw))
  obtain ⟨hyK, hyN, hyE, hcode⟩ := alg511_binary_oriented_code_size x y hy
  change (gm06EncodeSuccessorInput (y.drawing.withLinkage [])).length ≤ S at hcode
  have hn : x.vertexCount ≤ S := by unfold S alg511BinarySearchInputSize; omega
  have hkn : x.pathCount ≤ x.vertexCount := by
    simpa only [hyK, hyN] using rp.graphTurn.pathCount_le_vertexCount (by simpa only [hyK] using hk)
  have hsearch := gm06Alg511BinarySearchWords_length x
  have hbits : x.numerator.digits.length + x.denominator.digits.length ≤ S := by
    have hh := alg511_binary_target_size_le x
    simp only [alg511BinaryInputSize, GM06Alg511BinaryInteger.words_length] at hh
    unfold S alg511BinarySearchInputSize
    omega
  have hturn : (gm06EncodeRows (x.edgeTurns.map GM06Alg511BinaryInteger.words)).length ≤ S := by
    have hh := alg511_binary_field_length_le x
      (gm06EncodeRows (x.edgeTurns.map GM06Alg511BinaryInteger.words)) (by simp [GM06Alg511BinaryInput.rows])
    unfold S alg511BinarySearchInputSize
    omega
  have hwidth : alg511BinaryCurrentWidth x ≤ 6 * (S + 1) := by
    unfold alg511BinaryCurrentWidth
    omega
  have htw : target.length ≤ 3 * (S + 1) := by omega
  have hcap : 1 + y.drawing.vertexCount / y.drawing.pathCount ≤ S + 1 := by
    have hh := Nat.div_le_self y.drawing.vertexCount y.drawing.pathCount
    omega
  have hE : y.drawing.endpoints.length ≤ S :=
    (gm06Alg511_encoded_row_length_le (rows := gm06SuccessorRows (y.drawing.withLinkage []))
      (by simp [gm06SuccessorRows, GM06Alg511Input.withLinkage])).trans hcode
  have hprod : y.drawing.pathCount * y.drawing.vertexCount ≤ S * S :=
    Nat.mul_le_mul (by omega) (by omega)
  have hC : (gm06EncodeSuccessorInput (y.drawing.withLinkage [])).length +
      y.drawing.pathCount + y.drawing.pathCount * y.drawing.vertexCount ≤ 3 * (S + 1) ^ 2 := by
    nlinarith only [hS, hcode, hprod, hyK, hkn, hn]
  have hmax : max (alg511BinaryCurrentWidth x) target.length ≤ 6 * (S + 1) :=
    max_le hwidth (by omega)
  refine ⟨hsmall 3 (by nlinarith only [hS]), hsmall _ (by nlinarith only [hS, hmax, hcap]),
    hsmall _ (by nlinarith only [hS, hyK, hkn, hn]), hsmall _ (by nlinarith only [hS, hyN, hn]),
    hsmall _ (by nlinarith only [hS, hE]), hsmall _ (by nlinarith only [hS, hyK, hkn, hn, hprod]),
    hsmall _ (by nlinarith only [hC]), ?_, hwidth, htw, hcap, hC⟩
  have hbaseWords : ∀ d ∈ gm06EncodeSuccessorInput (y.drawing.withLinkage []), d ≤ 6 * (S + 1) := by
    apply alg511_encoded_words_le _ _ (by change (gm06EncodeSuccessorInput (y.drawing.withLinkage [])).length ≤ _; nlinarith only [hS, hcode])
    intro row hr d hd
    have hrowLen : row.length ≤ S := (gm06Alg511_encoded_row_length_le hr).trans hcode
    simp only [gm06SuccessorRows, GM06Alg511Input.withLinkage,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · have heq := List.mem_singleton.mp hd
      omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hd
      have hb := gm06Alg511Endpoint_getD_lt y.drawing rp.graphTurn.graph i hi
      have hv : y.drawing.endpoints.getD i 0 = y.drawing.endpoints[i] := by simp [hi]
      rw [hv] at hb
      omega
    · apply alg511_encoded_words_le _ _ (by omega) (fun row hr d hd => ?_) d hd
      have hb := rp.rotation_darts_lt row hr d hd
      have hends : y.drawing.endpoints.length = 2 * rp.graphTurn.graph.pairs.length := by
        have hh := rp.graphTurn.graph.endpoints
        change y.drawing.endpoints = _ at hh
        rw [hh, gm06EndpointWords_length, List.length_map]
      omega
    · rw [rp.graphTurn.inner] at hd
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
      have hb := (rp.graphTurn.source i).isLt
      omega
    · rw [rp.graphTurn.outer] at hd
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
      have hb := (rp.graphTurn.target i).isLt
      omega
    · have heq : d = 0 := by simpa [gm06EncodeRows, gm06EncodeRowsPayload] using hd
      omega
  intro d hd
  have hh := hbaseWords d hd
  exact hsmall d (by nlinarith only [hS, hh])

/-- The loop's own binary and packing overhead is cubic in input
length. The successor contributes its per-call bound times at most
one plus the input size; its target distance contributes no factor. -/
theorem alg511_binary_loop_time_le (B code base cap target increment N u : ℕ)
    (hN : 1 ≤ N) (hcode : code ≤ 3 * N ^ 2) (hbase : base ≤ 6 * N)
    (hcap : cap ≤ N) (htarget : target ≤ 3 * N) (hinc : increment ≤ N)
    (hu : u ≤ 430 + 350 * (base + target + 1) +
      cap * (12 + alg511BinaryRoundBudget B code base cap target increment)) :
    u ≤ N * B + 20000 * N ^ 3 := by
  have hN₂ : N ≤ N ^ 2 := Nat.le_self_pow (by decide) N
  have hN₃ : N ≤ N ^ 3 := Nat.le_self_pow (by decide) N
  have hR : alg511BinaryRoundBudget B code base cap target increment ≤
      B + 215 + 68 * (3 * N ^ 2) + 24 * (6 * N + N + 3 * N + N + 3) +
        (400 + 350 * (6 * N + N + N + 1)) + (404 + 350 * (6 * N + N + 3 * N + 1)) + 4 := by
    unfold alg511BinaryRoundBudget
    gcongr
  have hR' : alg511BinaryRoundBudget B code base cap target increment ≤ B + 10000 * N ^ 2 := by
    nlinarith only [hR, hN, hN₂]
  have htotal : u ≤ 430 + 350 * (6 * N + 3 * N + 1) + N * (12 + (B + 10000 * N ^ 2)) := by
    apply hu.trans
    gcongr
  nlinarith only [htotal, hN, hN₃]

end GraphMinor.GM06
