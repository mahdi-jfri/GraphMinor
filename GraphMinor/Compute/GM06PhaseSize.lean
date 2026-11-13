module

public import GraphMinor.Compute.GM06PhaseCut
public import GraphMinor.Compute.GM06PhaseComponentData

/-!
# Uniform current-size bounds for the finite phases

The programs in VI (5.7), page 133, keep permanent label spaces.
A single size counts those spaces and the actual current input rows.
Induced component records are bounded by the original rotation code.
Their saved physical buffer has quadratic capacity. A cubic word
budget therefore covers these records and the quadratic search keys.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Permanent slots and current structural row sizes, with a positive margin. -/
def gm06PhaseSize (x : GM06SuccessorInput) (m : ℕ) : ℕ :=
  x.vertexCount + m + x.endpoints.length + x.innerCuff.length + x.outerCuff.length +
    x.linkage.length + x.linkage.flatten.length + (gm06EncodeRows x.rotations).length +
    x.rotations.flatten.length + 1

/-- The phase size is positive even for the empty graph. -/
theorem gm06PhaseSize_pos (x : GM06SuccessorInput) (m : ℕ) : 1 ≤ gm06PhaseSize x m := by
  unfold gm06PhaseSize
  omega

/-- Every original count and row-code length is bounded by the phase size. -/
theorem gm06PhaseSize_bounds (x : GM06SuccessorInput) (m : ℕ) :
    x.vertexCount ≤ gm06PhaseSize x m ∧
      m + x.innerCuff.length + x.outerCuff.length ≤ gm06PhaseSize x m ∧
      (gm06EncodeRows x.linkage).length ≤ gm06PhaseSize x m ∧
      (gm06EncodeRows x.rotations).length ≤ gm06PhaseSize x m ∧
      x.rotations.flatten.length ≤ gm06PhaseSize x m ∧
      x.innerCuff.length ≤ gm06PhaseSize x m := by
  have hp := gm06FaceCode_length x.linkage
  unfold gm06PhaseSize
  omega

/-- The current-core cut bound uses exactly this size. -/
theorem gm06PhaseCutCost_le_size (x : GM06SuccessorInput) (m : ℕ) :
    gm06PhaseCutCost x m ≤ 8100000 * gm06PhaseSize x m ^ 3 :=
  gm06PhaseCutCost_le_polynomial x m

/-- Every induced component code fits in twice the input rotation code. -/
theorem gm06PhaseComponents_code_length {m : ℕ} (x : GM06SuccessorInput)
    (hnd : x.rotations.flatten.Nodup) (part : GM06CutData) (hp : part ∈ gm06PhaseComponents x m) :
    (gm06EncodeRows part.rotations).length ≤ 2 * (gm06EncodeRows x.rotations).length := by
  obtain ⟨hlen, _, hsub, _⟩ := gm06PhaseComponents_encoding x hnd part hp
  have hs := gm06CutDataOfLinkage_sizes x.vertexCount m x.endpoints x.linkage x.innerCuff x.outerCuff
    x.rotations (List.range x.vertexCount)
  have hd := gm06SplitRotationRows_length_le
    (gm06BuildCutTables x.vertexCount m x.endpoints x.linkage x.innerCuff x.outerCuff) x.rotations
  have hl := hsub.length_le
  have hc := gm06FaceCode_length part.rotations
  have ho := gm06FaceCode_length x.rotations
  change (gm06SplitRotationRows _ x.rotations).flatten.length ≤ _ at hd
  change part.rotations.flatten.length ≤ (gm06SplitRotationRows _ x.rotations).flatten.length at hl
  rw [hs.1] at hlen
  omega

/-- Each word of a computed component record has the input-derived
row-length or copied-label bound, including the record's row headers. -/
theorem gm06PhaseComponents_code_words {w m : ℕ} (x : GM06SuccessorInput)
    (hnd : x.rotations.flatten.Nodup)
    (hkeys : ∀ d ∈ x.rotations.flatten, d < 2 * (m + x.innerCuff.length + x.outerCuff.length))
    (hcode : 2 * (gm06EncodeRows x.rotations).length < 2 ^ w)
    (hlabels : 4 * (m + x.innerCuff.length + x.outerCuff.length) < 2 ^ w)
    (part : GM06CutData) (hp : part ∈ gm06PhaseComponents x m) :
    ∀ a ∈ gm06EncodeRows part.rotations, a < 2 ^ w := by
  have hc := gm06PhaseComponents_code_length x hnd part hp
  have hl := gm06FaceCode_length part.rotations
  obtain ⟨_, _, hsub, _⟩ := gm06PhaseComponents_encoding x hnd part hp
  have hd := gm06CutDataOfLinkage_dart_bounds (n := x.vertexCount) x.endpoints x.linkage x.innerCuff x.outerCuff
    x.rotations (List.range x.vertexCount) hkeys
  intro a ha
  simp only [gm06EncodeRows, List.mem_cons, gm06EncodeRowsPayload, List.mem_flatMap] at ha
  rcases ha with rfl | ⟨row, hr, ha⟩
  · omega
  · simp only [gm06EncodeNatList, List.mem_cons] at ha
    rcases ha with rfl | ha
    · have hs : [row].Sublist part.rotations := List.singleton_sublist.mpr hr
      have hb : row.length ≤ part.rotations.flatten.length := by simpa using hs.flatten.length_le
      omega
    · exact (hd.1 a (hsub.subset (List.mem_flatten.mpr ⟨row, hr, ha⟩))).trans hlabels

/-- The physical component-record buffer has quadratic capacity. -/
theorem gm06PhaseRecordCapacity_le (x : GM06SuccessorInput) (m : ℕ) :
    1 + x.innerCuff.length * (1 + 2 * (gm06EncodeRows x.rotations).length) ≤
      4 * gm06PhaseSize x m ^ 2 := by
  let N := gm06PhaseSize x m
  have hN : 1 ≤ N := gm06PhaseSize_pos x m
  have hk : x.innerCuff.length ≤ N := by dsimp only [N, gm06PhaseSize]; omega
  have hr : (gm06EncodeRows x.rotations).length ≤ N := by dsimp only [N, gm06PhaseSize]; omega
  have hfactor : 1 + 2 * (gm06EncodeRows x.rotations).length ≤ 3 * N := by omega
  have hmul := Nat.mul_le_mul hk hfactor
  change _ ≤ 4 * N ^ 2
  nlinarith only [hmul, hN]

/-- The cubic word budget covers every quadratic allocation and
linear count used by the phase. -/
theorem gm06Phase_word_bound {w N a : ℕ} (hN : 1 ≤ N)
    (hword : 10000 * N ^ 3 < 2 ^ w) (ha : a ≤ 100 * N ^ 2 + 100 * N + 100) : a < 2 ^ w := by
  have hNN : N ≤ N * N := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left N hN
  have hNNN : N * N ≤ N * N * N := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (N * N) hN
  have hcube : N ^ 3 = N * N * N := by ring
  have hsquare : N ^ 2 = N * N := by ring
  have hone : 1 ≤ N * N * N := hN.trans (hNN.trans hNNN)
  rw [hcube] at hword
  rw [hsquare] at ha
  omega

end GraphMinor.Compute
