module

public import GraphMinor.Compute.F92PreparePaths
public import GraphMinor.Compute.F92Encode

/-!
# Uniform cost and word bounds for the `F` program

All scans have linear cost in vertices and edges, with the height and number of subwalls
fixed. These estimates collect their constants and choose one word-size constant covering
the graph encoding, wall encodings, adjacency arrays and encoded segment body.
-/

@[expose] public section

namespace GraphMinor.Compute.Alg92

/-- Constant for the parsing phase. -/
def f92ParseFactor (h k : ℕ) : ℕ :=
  f92InitFactor h k + 3 + k * (41 + 4 * h + 214 * elemWallNumVerts h)

/-- A coefficient that bounds every length used by the program. -/
def f92WordCoeff (h k : ℕ) : ℕ :=
  10 + h + 2 * elemWallNumVerts h + (k + 1) * (4 + 3 * elemWallNumVerts h) + k

/-- The number of simple edges is at most the number of input edges. -/
theorem f92_edgeList_length_le {l m p h k r : ℕ} (x : Alg92Input l m p h k r) :
    (edgeListOf x.G.toSimpleGraph).length ≤ x.G.numEdges := by
  rw [length_edgeListOf_eq_card_edgeFinset]
  exact edgeFinset_card_toSimpleGraph_le_numEdges x.G

/-- One word-size constant supplies every explicit bound needed by the phases. -/
theorem f92_word_bounds {l m p h k r w : ℕ} (x : Alg92Input l m p h k r)
    (hw : wordSize (f92WordCoeff h k + 1) (alg92Size x) ≤ w) :
    4 < 2 ^ w ∧ x.n + 1 < 2 ^ w ∧ h < 2 ^ w ∧
    3 + 2 * elemWallNumVerts h < 2 ^ w ∧ x.G.numEdges < 2 ^ w ∧
    (encAlg92In x).length < 2 ^ w ∧
    2 * (edgeListOf x.G.toSimpleGraph).length < 2 ^ w ∧
    1 + k * (x.n + 1) < 2 ^ w := by
  let N := alg92Size x
  let A := f92WordCoeff h k
  have hN1 : 1 ≤ N := by dsimp [N, alg92Size]; omega
  have hn : x.n ≤ N := by dsimp [N, alg92Size]; omega
  have he : x.G.numEdges ≤ N := by dsimp [N, alg92Size]; omega
  have hm : x.G.numActivePairs ≤ N := (Alg91.numActivePairs_le_numEdges x.G).trans he
  have hpow : A * (N + 2) < 2 ^ w :=
    (mul_lt_two_pow_wordSize_of_succ_le (A := A) (c := A + 1) (n := N) le_rfl).trans_le
      (Nat.pow_le_pow_right (by omega) hw)
  have hA : 10 + h + 2 * elemWallNumVerts h +
      (k + 1) * (4 + 3 * elemWallNumVerts h) + k = A := rfl
  have hAN : A ≤ A * (N + 2) := by
    have hh := Nat.mul_le_mul_left A (show 1 ≤ N + 2 by omega)
    simpa using hh
  have h2N : 2 * N ≤ A * (N + 2) := by
    have hh := Nat.mul_le_mul_right (N + 2) (show 2 ≤ A by omega)
    omega
  have hinLen := length_encAlg92In_le x
  have hmax := maxWallEncLen_le_mul h x.n N hN1 hn
  have hinput : (encAlg92In x).length ≤
      (5 + (k + 1) * (4 + 3 * elemWallNumVerts h)) * N := by
    have hmul := Nat.mul_le_mul_left (k + 1) hmax
    have hconst : 2 + 3 * x.G.numActivePairs ≤ 5 * N := by omega
    have hdistrib : (5 + (k + 1) * (4 + 3 * elemWallNumVerts h)) * N =
        5 * N + (k + 1) * ((4 + 3 * elemWallNumVerts h) * N) := by ring
    omega
  have hinputA : (5 + (k + 1) * (4 + 3 * elemWallNumVerts h)) * N ≤ A * (N + 2) := by
    have hh := Nat.mul_le_mul_right N
      (show 5 + (k + 1) * (4 + 3 * elemWallNumVerts h) ≤ A by omega)
    exact hh.trans (Nat.mul_le_mul_left A (show N ≤ N + 2 by omega))
  have hedge := Nat.mul_le_mul_left 2 ((f92_edgeList_length_le x).trans he)
  have henc : 1 + k * (x.n + 1) ≤ A * (N + 2) := by
    have hkn := Nat.mul_le_mul_left k (show x.n + 1 ≤ N + 2 by omega)
    have hkA := Nat.mul_le_mul_right (N + 2) (show k + 1 ≤ A by omega)
    rw [Nat.add_mul, Nat.one_mul] at hkA
    omega
  exact ⟨by omega, by omega, by omega, by omega, by omega,
    hinput.trans_lt (hinputA.trans_lt hpow), by omega, henc.trans_lt hpow⟩

/-- Cost coefficient for encoding all segment records. -/
def f92EncodeFactor (k : ℕ) : ℕ := 22 + k * (68 * k + 114) + 36 * k

/-- The serialization estimate is linear in a size bounding the vertex count. -/
theorem f92EncodeCost_le (k n N : ℕ) (hN : 1 ≤ N) (hn : n ≤ N) :
    22 + k * (34 * (k * (n + 1)) + 36 * n + 78) + 18 * (k * (n + 1)) ≤
      f92EncodeFactor k * N := by
  have hnp : n + 1 ≤ 2 * N := by omega
  have hK : k * (n + 1) ≤ (2 * k) * N := by
    calc
      k * (n + 1) ≤ k * (2 * N) := Nat.mul_le_mul_left k hnp
      _ = (2 * k) * N := by ring
  have h34 := Nat.mul_le_mul_left 34 hK
  have h36 := Nat.mul_le_mul_left 36 hn
  have h78 := Nat.mul_le_mul_left 78 hN
  have hstep : 34 * (k * (n + 1)) + 36 * n + 78 ≤ (68 * k + 114) * N := by
    have heq : (68 * k + 114) * N = 34 * ((2 * k) * N) + 36 * N + 78 * N := by ring
    omega
  have htotal := Nat.mul_le_mul_left k hstep
  have h18 := Nat.mul_le_mul_left 18 hK
  have h22 := Nat.mul_le_mul_left 22 hN
  have heq : f92EncodeFactor k * N = 22 * N + k * ((68 * k + 114) * N) +
      18 * ((2 * k) * N) := by unfold f92EncodeFactor; ring
  omega

/-- A cost coefficient for all three phases. -/
def f92TotalFactor (h k : ℕ) : ℕ :=
  f92ParseFactor h k + 102 + 357 * k + f92EncodeFactor k

/-- The explicit bounds of parsing, searching, segment construction and encoding add to
one constant times the input size. -/
theorem f92TotalCost_le {l m p h k r : ℕ} (x : Alg92Input l m p h k r) :
    f92ParseFactor h k * alg92Size x + 31 + 34 * x.n +
      17 * (2 * (edgeListOf x.G.toSimpleGraph).length) +
      k * (69 + 145 * x.n + 29 * totalAdjEntries (edgeNeighbors (edgeListOf x.G.toSimpleGraph))) +
      (2 + x.n + k * (25 + 60 * x.n)) +
      (22 + k * (34 * (k * (x.n + 1)) + 36 * x.n + 78) + 18 * (k * (x.n + 1))) ≤
      f92TotalFactor h k * alg92Size x := by
  let N := alg92Size x
  have hN : 1 ≤ N := by dsimp [N, alg92Size]; omega
  have hn : x.n ≤ N := by dsimp [N, alg92Size]; omega
  have he : x.G.numEdges ≤ N := by dsimp [N, alg92Size]; omega
  have hM : 2 * (edgeListOf x.G.toSimpleGraph).length ≤ 2 * N :=
    Nat.mul_le_mul_left 2 ((f92_edgeList_length_le x).trans he)
  have htot : totalAdjEntries (edgeNeighbors (edgeListOf x.G.toSimpleGraph)) =
      2 * (edgeListOf x.G.toSimpleGraph).length :=
    totalAdjEntries_edgeNeighbors _ (isSimpleEdgeList_edgeListOf _).1
  rw [htot]
  have h31 := Nat.mul_le_mul_left 31 hN
  have h34 := Nat.mul_le_mul_left 34 hn
  have h17 := Nat.mul_le_mul_left 17 hM
  have h69 := Nat.mul_le_mul_left 69 hN
  have h145 := Nat.mul_le_mul_left 145 hn
  have h29 := Nat.mul_le_mul_left 29 hM
  have hsearch : 69 + 145 * x.n + 29 * (2 * (edgeListOf x.G.toSimpleGraph).length) ≤ 272 * N := by omega
  have hsearchK := Nat.mul_le_mul_left k hsearch
  have h25 := Nat.mul_le_mul_left 25 hN
  have h60 := Nat.mul_le_mul_left 60 hn
  have hbuild : 25 + 60 * x.n ≤ 85 * N := by omega
  have hbuildK := Nat.mul_le_mul_left k hbuild
  have h2 := Nat.mul_le_mul_left 2 hN
  have hencode := f92EncodeCost_le k x.n N hN hn
  have hfactor : f92TotalFactor h k * N = f92ParseFactor h k * N +
      102 * N + k * (272 * N) + k * (85 * N) + f92EncodeFactor k * N := by
    unfold f92TotalFactor; ring
  change _ ≤ f92TotalFactor h k * N
  dsimp only [N] at *
  omega

end GraphMinor.Compute.Alg92
