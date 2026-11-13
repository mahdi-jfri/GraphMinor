module

public import GraphMinor.GM06.Alg57CurrentBounds
public import GraphMinor.Compute.GM06SuccessorDegreeTime
import GraphMinor.GM06.Alg57RowBounds

/-!
# Logarithmic words for the ordinary input of VI (5.7)

All geometric input meanings use finite original labels. Endpoint
and cuff words are vertex labels. Path words are ordinary directed
labels. Rotation words are augmented directed labels, including both
cuffs. The count and length headers are bounded by their actual
encoded arrays. These facts bound every supplied input word from
the ordinary input relation, without an extra word-bound hypothesis.

A fixed logarithmic word size then holds the initial counts, code,
loop fuel and uniform current-row budget used by the early scans.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

private theorem row_length_le_code (rows : List (List ℕ)) {row : List ℕ} (hr : row ∈ rows) :
    row.length ≤ (gm06EncodeRows rows).length := by
  have hs := (List.sublist_flatten_of_mem hr).length_le
  rw [gm06EncodeRows_length]
  omega

/-- The original vertex, edge and path counts and both encoded
row tables are bounded by the ordinary finite input size. -/
theorem GM06SuccessorInputRep.size_bounds
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06SuccessorInputRep x G L) :
    let N := gm06SuccessorInputSize x
    x.vertexCount ≤ N ∧ G.E.ncard ≤ N ∧ k ≤ N ∧
      (gm06EncodeRows x.rotations).length ≤ N ∧
      (gm06EncodeRows x.linkage).length ≤ N ∧
      (gm06EncodeSuccessorInput x).length ≤ N := by
  dsimp only
  have hcode : (gm06EncodeSuccessorInput x).length ≤ gm06SuccessorInputSize x :=
    Nat.le_add_left _ _
  have hrows (row : List ℕ) (hr : row ∈ gm06SuccessorRows x) :
      row.length ≤ gm06SuccessorInputSize x := (row_length_le_code _ hr).trans hcode
  have hend := hrows x.endpoints (by simp [gm06SuccessorRows])
  have hinner := hrows x.innerCuff (by simp [gm06SuccessorRows])
  have hends : x.endpoints.length = 2 * G.E.ncard := rep.graph.endpoints_length
  have hcuff : x.innerCuff.length = k := rep.cuff_lengths.1
  refine ⟨Nat.le_add_right _ _, by omega, by omega,
    hrows _ (by simp [gm06SuccessorRows]), hrows _ (by simp [gm06SuccessorRows]), hcode⟩

/-- Every actual input word, including all length headers, is at
most seven times one plus the ordinary finite input size. -/
theorem GM06SuccessorInputRep.code_words_le_seven_size
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06SuccessorInputRep x G L)
    (hG : IsCylinderSection5Drawing k G) :
    ∀ z ∈ gm06EncodeSuccessorInput x, z ≤ 7 * (gm06SuccessorInputSize x + 1) := by
  obtain ⟨hn, hm, hk, _, _, hlen⟩ := rep.size_bounds
  obtain ⟨cur, htag, _, _⟩ := rep.exists_currentDrawingRep
  have htagLen : cur.tagged.length = G.E.ncard := by
    rw [htag, GM06SuccessorGraphRep.initialTagged, List.length_map]
    exact rep.graph.pairCount_eq
  have hfield : ∀ row ∈ gm06SuccessorRows x, ∀ z ∈ row,
      z ≤ 7 * (gm06SuccessorInputSize x + 1) := by
    intro row hrow z hz
    simp only [gm06SuccessorRows, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl
    · have hz' : z = x.vertexCount := List.mem_singleton.mp hz
      omega
    · have hz' := rep.graph.endpoint_lt hz
      omega
    · have hz' := cur.rotation_code_words_le hG z hz
      rw [htagLen] at hz'
      omega
    · rw [rep.inner, List.mem_ofFn] at hz
      obtain ⟨i, rfl⟩ := hz
      have hi := (rep.source i).isLt
      omega
    · rw [rep.outer, List.mem_ofFn] at hz
      obtain ⟨i, rfl⟩ := hz
      have hi := (rep.target i).isLt
      omega
    · have hz' := cur.linkage.code_words_le z hz
      rw [htagLen] at hz'
      omega
  apply gm06EncodeRows_words_le
  · simp only [gm06SuccessorRows, List.length_cons, List.length_nil]
    omega
  · have hh := gm06EncodeRows_length (gm06SuccessorRows x)
    change (gm06EncodeSuccessorInput x).length = _ at hh
    omega
  · intro z hz
    obtain ⟨row, hrow, hz⟩ := List.mem_flatten.mp hz
    exact hfield row hrow z hz

private theorem linear_budget_le_fourth (N : ℕ) : 8 + 28 * N ≤ (N + 2) ^ 4 := by
  ring_nf
  omega

/-- A fixed logarithmic word size holds the ordinary input and the
initial loop bounds derived from its actual finite interpretation. -/
theorem GM06SuccessorInputRep.initial_word_caps
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06SuccessorInputRep x G L)
    (hG : IsCylinderSection5Drawing k G) :
    let N := gm06SuccessorInputSize x
    let w := wordSize 32 N
    3 < 2 ^ w ∧ x.vertexCount * x.vertexCount < 2 ^ w ∧
      4 * (1 + x.vertexCount + 2 * G.E.ncard + 4 * k) < 2 ^ w ∧
      2 * (x.vertexCount + G.E.ncard) + 1 < 2 ^ w ∧
      (gm06EncodeSuccessorInput x).length < 2 ^ w ∧
      ∀ z ∈ gm06EncodeSuccessorInput x, z < 2 ^ w := by
  dsimp only
  let N := gm06SuccessorInputSize x
  obtain ⟨hn, hm, hk, _, _, hlen⟩ := rep.size_bounds
  have hpow : (N + 2) ^ 4 < 2 ^ wordSize 32 N :=
    (Nat.pow_le_pow_right (by omega : 0 < N + 2) (by decide : 4 ≤ 32)).trans_lt
      (pow_lt_two_pow_wordSize (by decide : 1 ≤ 32) N)
  have hlinear : 8 + 28 * N < 2 ^ wordSize 32 N := (linear_budget_le_fourth N).trans_lt hpow
  have hsq : x.vertexCount * x.vertexCount ≤ (N + 2) ^ 4 := by
    calc
      x.vertexCount * x.vertexCount ≤ (N + 2) * (N + 2) := Nat.mul_le_mul (by omega) (by omega)
      _ ≤ (N + 2) ^ 4 := by
        simpa only [pow_two] using Nat.pow_le_pow_right (by omega : 0 < N + 2) (by decide : 2 ≤ 4)
  dsimp only [N] at hlinear hpow hsq
  refine ⟨by omega, hsq.trans_lt hpow, by omega, by omega, by omega, ?_⟩
  intro z hz
  have hh := rep.code_words_le_seven_size hG z hz
  omega

end GraphMinor.GM06
