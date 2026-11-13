module

public import GraphMinor.GM06.Alg511BinaryInitialize
import GraphMinor.Compute.GM06RefreshContractedMasks
import Mathlib.Tactic

/-!
# Logarithmic words for the supplied binary instance

The supplied integer signs and digits are bits, even when the integers
are arbitrarily large. Every other input word is a graph label or a
length prefix. Bound those words by the complete supplied input size,
and bound all initialization capacities by a fixed polynomial in that
size. The maximum-flow instance size is also polynomial in it.

Consequently a fixed multiple of the logarithm of the complete input
length meets the execution premises of the binary initializer for
VI (5.11), page 134. These bounds count bits, never integer magnitudes.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface

/-- Length prefixes and supplied data words remain within a
common bound whenever the complete row code and its data do. -/
theorem alg511_encoded_words_le (rows : List (List ℕ)) (R : ℕ)
    (hlen : (gm06EncodeRows rows).length ≤ R)
    (hdata : ∀ row ∈ rows, ∀ d ∈ row, d ≤ R) :
    ∀ d ∈ gm06EncodeRows rows, d ≤ R := by
  intro d hd
  rcases List.mem_cons.mp hd with rfl | hd
  · have hcount := gm06EncodeRows_length rows
    omega
  · obtain ⟨row, hr, hd⟩ := List.mem_flatMap.mp hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact (gm06Alg511_encoded_row_length_le hr).trans hlen
    · exact hdata row hr d hd

/-- A polynomial change in the instance size multiplies the
logarithmic word constant by its fixed degree. -/
theorem alg511_wordSize_of_polynomial {c M n d : ℕ} (hd : 1 ≤ d)
    (hM : M + 2 ≤ (n + 2) ^ d) : wordSize c M ≤ wordSize (c * d) n := by
  have hp : M + 2 < 2 ^ (d * (Nat.log 2 (n + 2) + 1)) := by
    calc
      M + 2 ≤ (n + 2) ^ d := hM
      _ < (2 ^ (Nat.log 2 (n + 2) + 1)) ^ d :=
        Nat.pow_lt_pow_left (lt_two_pow_log_succ n) (by omega)
      _ = _ := by rw [← Nat.pow_mul, Nat.mul_comm]
  have hl := Nat.log_lt_of_lt_pow (by omega : M + 2 ≠ 0) hp
  unfold wordSize
  calc
    c * (Nat.log 2 (M + 2) + 1) ≤ c * (d * (Nat.log 2 (n + 2) + 1)) :=
      Nat.mul_le_mul_left c (by omega)
    _ = _ := (Nat.mul_assoc _ _ _).symm

/-- One uniform quadratic allowance covers graph capacities and
all binary digit widths needed during initialization. -/
theorem alg511_quadratic_allowance_fits (n : ℕ) :
    16 * (n + 1) ^ 2 < 2 ^ wordSize 6 n := by
  apply lt_two_pow_wordSize_of_lt_pow (by decide)
  calc
    16 * (n + 1) ^ 2 ≤ 16 * (n + 2) ^ 2 := by gcongr; omega
    _ ≤ (n + 2) ^ 4 * (n + 2) ^ 2 := Nat.mul_le_mul_right _ (by
      have hh := Nat.pow_le_pow_left (by omega : 2 ≤ n + 2) 4
      simpa using hh)
    _ = _ := by ring

/-- The supplied binary drawing words and their repeated ordinary
flow layout are bounded by the complete input length. -/
theorem alg511_binary_input_words_le (x : GM06Alg511BinaryInput) {G : Drawing ClosedCylinder}
    (rep : GM06Alg511BinaryDrawingRep x G) (hk : 0 < x.pathCount) :
    (∀ d ∈ gm06Alg511BinarySearchWords x, d ≤ 6 * (alg511BinarySearchInputSize x + 1)) ∧
    (∀ d ∈ gm06EncodeRows x.rotations, d ≤ 6 * (alg511BinarySearchInputSize x + 1)) := by
  let S := alg511BinarySearchInputSize x
  have hn : x.vertexCount ≤ S := by unfold S alg511BinarySearchInputSize; omega
  have hkn : x.pathCount ≤ x.vertexCount := rep.graphTurn.pathCount_le_vertexCount hk
  have hsearch := gm06Alg511BinarySearchWords_length x
  have hsearchSize : (gm06Alg511BinarySearchWords x).length ≤ S := by unfold S alg511BinarySearchInputSize; omega
  have hfull : x.words.length ≤ S := by unfold S alg511BinarySearchInputSize; omega
  have hfield : ∀ row ∈ x.rows, row.length ≤ S := by
    intro row hr
    have hh := alg511_binary_field_length_le x row hr
    unfold S alg511BinarySearchInputSize
    omega
  have hE : x.endpoints.length = 2 * rep.graphTurn.graph.pairs.length := by
    have hh := rep.graphTurn.graph.endpoints
    change x.endpoints = _ at hh
    rw [hh, gm06EndpointWords_length, List.length_map]
  have hElen := hfield x.endpoints (by simp [GM06Alg511BinaryInput.rows])
  have hrotLen := hfield (gm06EncodeRows x.rotations) (by simp [GM06Alg511BinaryInput.rows])
  have hturnLen := hfield (gm06EncodeRows (x.edgeTurns.map GM06Alg511BinaryInteger.words))
    (by simp [GM06Alg511BinaryInput.rows])
  have hrot : ∀ d ∈ gm06EncodeRows x.rotations, d ≤ 6 * (S + 1) := by
    apply alg511_encoded_words_le _ _ (by omega)
    intro row hr d hd
    have hb := rep.rotation_darts_lt row hr d hd
    change d < 2 * (rep.graphTurn.graph.pairs.length + x.pathCount + x.pathCount) at hb
    omega
  have hturn : ∀ d ∈ gm06EncodeRows (x.edgeTurns.map GM06Alg511BinaryInteger.words), d ≤ 6 * (S + 1) := by
    apply alg511_encoded_words_le _ _ (by omega)
    intro row hr d hd
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hr
    have hb := z.words_lt_two d hd
    omega
  have hbinary : ∀ d ∈ x.words, d ≤ 6 * (S + 1) := by
    apply alg511_encoded_words_le _ _ (by change x.words.length ≤ _; omega)
    intro row hr d hd
    simp only [GM06Alg511BinaryInput.rows, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have heq := List.mem_singleton.mp hd
      omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hd
      have hb := gm06Alg511Endpoint_getD_lt x.toWindingInput.drawing rep.graphTurn.graph i hi
      change x.endpoints.getD i 0 < x.vertexCount at hb
      have hv : x.endpoints.getD i 0 = x.endpoints[i] := by simp [hi]
      rw [hv] at hb
      omega
    · exact hrot d hd
    · change d ∈ x.toWindingInput.drawing.innerCuff at hd
      rw [rep.graphTurn.inner] at hd
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
      have hb := (rep.graphTurn.source i).isLt
      change _ < x.vertexCount at hb
      omega
    · change d ∈ x.toWindingInput.drawing.outerCuff at hd
      rw [rep.graphTurn.outer] at hd
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
      have hb := (rep.graphTurn.target i).isLt
      change _ < x.vertexCount at hb
      omega
    · have heq := List.mem_singleton.mp hd
      omega
    · have hb := x.numerator.words_lt_two d hd
      omega
    · have hb := x.denominator.words_lt_two d hd
      omega
    · exact hturn d hd
  have hflow : ∀ d ∈ encDisjointPathsIn x.toWindingInput.drawing.flowInput, d ≤ 6 * (S + 1) := by
    let flow := x.toWindingInput.drawing.flowInput
    have hf : (encDisjointPathsIn flow).length ≤ S := by
      change (encDisjointPathsIn x.toWindingInput.drawing.flowInput).length ≤ S
      unfold S alg511BinarySearchInputSize
      omega
    have hm : (edgeListOf flow.G).length ≤ S := by
      have hl : (encDisjointPathsIn flow).length = 3 + 2 * (edgeListOf flow.G).length + 2 * flow.n := by
        simp only [encDisjointPathsIn, List.length_append, length_encGraph, length_bitSetList, List.length_singleton]
        omega
      omega
    change (edgeListOf x.toWindingInput.drawing.flowInput.G).length ≤ S at hm
    intro d hd
    simp only [encDisjointPathsIn, List.mem_append, List.mem_singleton] at hd
    rcases hd with ((hd | hd) | hd) | hd
    · simp only [encGraph, List.mem_append] at hd
      rcases hd with hd | hd
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl
        · change x.vertexCount ≤ _
          omega
        · omega
      · obtain ⟨p, _, hd⟩ := List.mem_flatMap.mp hd
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl
        · have hb := p.1.isLt
          change _ < x.vertexCount at hb
          omega
        · have hb := p.2.isLt
          change _ < x.vertexCount at hb
          omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hd
      have hb := getElem_bitSetList_le_one flow.A i hi
      change (bitSetList x.toWindingInput.drawing.flowInput.A)[i] ≤ 1 at hb
      omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hd
      have hb := getElem_bitSetList_le_one flow.B i hi
      change (bitSetList x.toWindingInput.drawing.flowInput.B)[i] ≤ 1 at hb
      omega
    · subst d
      change x.pathCount ≤ _
      omega
  refine ⟨?_, hrot⟩
  apply alg511_encoded_words_le _ _ (by change (gm06Alg511BinarySearchWords x).length ≤ _; omega)
  intro row hr d hd
  rcases List.mem_cons.mp hr with rfl | hr
  · exact hbinary d hd
  · have heq := List.mem_singleton.mp hr
    subst row
    exact hflow d hd

/-- Maximum flow uses a polynomial-size ordinary graph instance,
so its logarithmic word requirement is logarithmic in the supplied
binary search code as well. -/
theorem alg511_binary_flow_wordSize (c : ℕ) (x : GM06Alg511BinaryInput)
    {G : Drawing ClosedCylinder} (rep : GM06Alg511BinaryDrawingRep x G) (hk : 0 < x.pathCount) :
    wordSize c (disjointPathsSize x.toWindingInput.drawing.flowInput) ≤
      wordSize (3 * c) (alg511BinarySearchInputSize x) := by
  let flow := x.toWindingInput.drawing.flowInput
  have hkn : x.pathCount ≤ x.vertexCount := rep.graphTurn.pathCount_le_vertexCount hk
  have hlen := gm06Alg511BinarySearchWords_length x
  have hflow : (encDisjointPathsIn flow).length = 3 + 2 * flow.G.edgeFinset.card + 2 * x.vertexCount := by
    simp only [encDisjointPathsIn, List.length_append, length_encGraph, length_edgeListOf_eq_card_edgeFinset,
      length_bitSetList, List.length_singleton]
    change 2 + 2 * flow.G.edgeFinset.card + x.vertexCount + x.vertexCount + 1 = _
    omega
  change (encDisjointPathsIn x.toWindingInput.drawing.flowInput).length =
    3 + 2 * flow.G.edgeFinset.card + 2 * x.vertexCount at hflow
  have hM : disjointPathsSize flow ≤ (alg511BinarySearchInputSize x + 1) ^ 2 := by
    change (x.pathCount + 1) * (x.vertexCount + flow.G.edgeFinset.card + 1) ≤ _
    calc
      _ ≤ (alg511BinarySearchInputSize x + 1) * (alg511BinarySearchInputSize x + 1) := by
        apply Nat.mul_le_mul <;> unfold alg511BinarySearchInputSize <;> omega
      _ = _ := (Nat.pow_two _).symm
  have hp : disjointPathsSize flow + 2 ≤ (alg511BinarySearchInputSize x + 2) ^ 3 := by
    calc
      _ ≤ (alg511BinarySearchInputSize x + 1) ^ 2 + 2 := Nat.add_le_add_right hM 2
      _ ≤ (alg511BinarySearchInputSize x + 2) ^ 2 := by nlinarith only [Nat.zero_le (alg511BinarySearchInputSize x)]
      _ ≤ (alg511BinarySearchInputSize x + 2) ^ 3 := Nat.pow_le_pow_right (by omega) (by decide)
  simpa only [Nat.mul_comm c 3] using alg511_wordSize_of_polynomial (c := c) (by decide : 1 ≤ 3) hp

/-- Every word premise of the complete binary initializer follows
from a single logarithmic word size in the complete supplied input.
No target, turn or accumulated integer magnitude is bounded. -/
theorem alg511_binary_initialize_resources (c : ℕ) (x : GM06Alg511BinaryInput)
    {G : Drawing ClosedCylinder} (rep : GM06Alg511BinaryDrawingRep x G) (hk : 0 < x.pathCount)
    {w : ℕ} (hw : wordSize (6 + 3 * c) (alg511BinarySearchInputSize x) ≤ w) :
    3 < 2 ^ w ∧ (gm06Alg511BinarySearchWords x).length + 2 < 2 ^ w ∧
      wordSize c (disjointPathsSize x.toWindingInput.drawing.flowInput) ≤ w ∧
      1 + 3 * x.vertexCount < 2 ^ w ∧ x.vertexCount * x.vertexCount < 2 ^ w ∧
      x.endpoints.length < 2 ^ w ∧ 1 + x.pathCount + x.pathCount * x.vertexCount < 2 ^ w ∧
      3 * x.pathCount + x.vertexCount + x.numerator.digits.length + x.denominator.digits.length +
        2 * (gm06EncodeRows (x.edgeTurns.map GM06Alg511BinaryInteger.words)).length + 12 < 2 ^ w ∧
      2 * (rep.graphTurn.graph.pairs.length + x.pathCount + x.pathCount) < 2 ^ w ∧
      (gm06EncodeRows x.rotations).length < 2 ^ w ∧
      (∀ d ∈ gm06EncodeRows x.rotations, d < 2 ^ w) ∧
      (∀ d ∈ gm06Alg511BinarySearchWords x, d < 2 ^ w) := by
  let S := alg511BinarySearchInputSize x
  have hS : 0 ≤ S := Nat.zero_le S
  have h6 : wordSize 6 S ≤ w := (wordSize_mono_left (by omega) S).trans hw
  have hsmall : ∀ q : ℕ, q ≤ 16 * (S + 1) ^ 2 → q < 2 ^ w := by
    intro q hq
    exact hq.trans_lt ((alg511_quadratic_allowance_fits S).trans_le (Nat.pow_le_pow_right (by decide) h6))
  have hkn : x.pathCount ≤ x.vertexCount := rep.graphTurn.pathCount_le_vertexCount hk
  have hn : x.vertexCount ≤ S := by unfold S alg511BinarySearchInputSize; omega
  have hlen := gm06Alg511BinarySearchWords_length x
  have hsearch : (gm06Alg511BinarySearchWords x).length ≤ S := by unfold S alg511BinarySearchInputSize; omega
  have hfield : ∀ row ∈ x.rows, row.length ≤ S := by
    intro row hr
    exact (alg511_binary_field_length_le x row hr).trans hsearch
  have he := hfield x.endpoints (by simp [GM06Alg511BinaryInput.rows])
  have hr := hfield (gm06EncodeRows x.rotations) (by simp [GM06Alg511BinaryInput.rows])
  have ht := hfield (gm06EncodeRows (x.edgeTurns.map GM06Alg511BinaryInteger.words))
    (by simp [GM06Alg511BinaryInput.rows])
  have hb : x.numerator.digits.length + x.denominator.digits.length ≤ S := by
    have hh := alg511_binary_target_size_le x
    simp only [alg511BinaryInputSize, GM06Alg511BinaryInteger.words_length] at hh
    unfold S alg511BinarySearchInputSize
    omega
  have hE : x.endpoints.length = 2 * rep.graphTurn.graph.pairs.length := by
    have hh := rep.graphTurn.graph.endpoints
    change x.endpoints = _ at hh
    rw [hh, gm06EndpointWords_length, List.length_map]
  have hprod : x.pathCount * x.vertexCount ≤ S * S := Nat.mul_le_mul (hkn.trans hn) hn
  have hsquare : x.vertexCount * x.vertexCount ≤ S * S := Nat.mul_le_mul hn hn
  have hflow : wordSize c (disjointPathsSize x.toWindingInput.drawing.flowInput) ≤ w :=
    (alg511_binary_flow_wordSize c x rep hk).trans ((wordSize_mono_left (by omega) S).trans hw)
  obtain ⟨hinputWords, hrotWords⟩ := alg511_binary_input_words_le x rep hk
  refine ⟨hsmall 3 (by nlinarith only [hS]), hsmall _ (by nlinarith only [hS, hsearch]), hflow,
    hsmall _ (by nlinarith only [hS, hn]), hsmall _ (by nlinarith only [hS, hsquare]),
    hsmall _ (by nlinarith only [hS, he]), hsmall _ (by nlinarith only [hS, hprod, hkn, hn]),
    hsmall _ (by nlinarith only [hS, hkn, hn, hb, ht]), hsmall _ (by nlinarith only [hS, hE, he, hkn, hn]),
    hsmall _ (by nlinarith only [hS, hr]), ?_, ?_⟩
  · intro d hd
    have hh := hrotWords d hd
    change d ≤ 6 * (S + 1) at hh
    exact hsmall d (by nlinarith only [hS, hh])
  · intro d hd
    have hh := hinputWords d hd
    change d ≤ 6 * (S + 1) at hh
    exact hsmall d (by nlinarith only [hS, hh])

/-- The complete initialization runs in cubic supplied-input time
with logarithmic words, on every represented proper cylinder drawing.
There are no additional resource or integer-magnitude premises. -/
theorem alg511_binary_initialize_polynomial :
    ∃ C c : ℕ, 1 ≤ C ∧ 1 ≤ c ∧ ∀ (x : GM06Alg511BinaryInput) (G : Drawing ClosedCylinder)
      (_rep : GM06Alg511BinaryDrawingRep x G), IsCylinderSection5Drawing x.pathCount G →
      ∀ (s : State), s.arrs 0 = gm06Alg511BinarySearchWords x →
      ∃ t u, Exec (wordSize c (alg511BinarySearchInputSize x)) gm06Alg511BinaryInitializeProg s t u ∧
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
  obtain ⟨C, c, hC, hc, hrun⟩ := alg511_binary_initialize_exec
  refine ⟨C, 6 + 3 * c, hC, by omega, ?_⟩
  intro x G rep hG s hinput
  obtain ⟨hw, hfit, hflow, hword, hsquare, he, hcap, hsize, haug, hrotFit, hrotWords, hwords⟩ :=
    alg511_binary_initialize_resources c x rep hG.1 (Nat.le_refl _)
  exact hrun x G rep hG s _ hw hfit hflow hword hsquare he hcap hsize haug hrotFit hrotWords hinput hwords

end GraphMinor.GM06
