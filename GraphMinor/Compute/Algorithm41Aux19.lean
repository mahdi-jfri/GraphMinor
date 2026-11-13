module

public import GraphMinor.Compute.Algorithm41Aux18

/-!
# Global Word Bounds for GM XIII (4.1)

A fixed coefficient, depending only on the folio parameters, bounds every array
length, table identifier, and output index by that coefficient times the input
size. A logarithmic Word RAM word size therefore suffices for all passes.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Linear bound on the allocated arena capacity. -/
def K_cap41 (δ ξ ω : ℕ) : ℕ := 1 + 2 * arena41Coeff δ ξ ω

/-- The arena capacity is linear in the input size. -/
theorem arena41Capacity_le_size {ξ ω : ℕ} (inp : Alg41CoreInput ξ ω) (δ : ℕ) :
    arena41Capacity δ ξ ω inp.G.numVerts inp.t ≤ K_cap41 δ ξ ω * alg41CoreSize inp := by
  have ht := inp.ht_le
  have hs : 1 ≤ alg41CoreSize inp := by unfold alg41CoreSize; omega
  have hnt : inp.G.numVerts + inp.t + 1 ≤ 2 * alg41CoreSize inp := by unfold alg41CoreSize; omega
  have hmul := Nat.mul_le_mul_right (arena41Coeff δ ξ ω) hnt
  unfold arena41Capacity K_cap41
  simp only [Nat.add_mul, Nat.one_mul]
  rw [Nat.mul_assoc, Nat.mul_comm (alg41CoreSize inp), ← Nat.mul_assoc] at hmul
  simp only [Nat.add_mul, Nat.one_mul] at hmul
  omega

/-- Fixed bound on all word coefficients used by the core program. -/
def B_word41 (δ ξ ω : ℕ) : ℕ :=
  100 + K_cap41 δ ξ ω + L_stream41 δ ξ ω + V_max δ ξ ω + C_max δ ξ ω +
    L_code41 δ ξ ω + T_max δ ξ ω + M_max ξ ω

private theorem scaled41_word_lt {w B c s : ℕ} (hc : c ≤ B) (h : B * s < 2 ^ w) :
    c * s < 2 ^ w := (Nat.mul_le_mul_right s hc).trans_lt h

private theorem const41_word_lt {w B c s : ℕ} (hc : c ≤ B) (hs : 1 ≤ s)
    (h : B * s < 2 ^ w) : c < 2 ^ w := by
  have hmul := Nat.mul_le_mul_left c hs
  rw [Nat.mul_one] at hmul
  exact hmul.trans_lt (scaled41_word_lt hc h)

/-- One linear bound suffices for the tree, workspace, and table words. -/
theorem core41_word_bounds {w δ ξ ω : ℕ} (inp : Alg41CoreInput ξ ω)
    (h : B_word41 δ ξ ω * alg41CoreSize inp < 2 ^ w) :
    Alg41WordBounds w δ ξ ω inp ∧
      3 < 2 ^ w ∧ 7 * alg41CoreSize inp < 2 ^ w ∧
      arena41Capacity δ ξ ω inp.G.numVerts inp.t < 2 ^ w ∧
      inp.G.numVerts + inp.G.numEdges < 2 ^ w ∧
      V_max δ ξ ω < 2 ^ w ∧ C_max δ ξ ω < 2 ^ w ∧
      2 + Q_max ξ ω + 2 * δ < 2 ^ w := by
  have hs : 1 ≤ alg41CoreSize inp := by unfold alg41CoreSize; omega
  have hconst : ∀ c ≤ B_word41 δ ξ ω, c < 2 ^ w := fun c hc => const41_word_lt hc hs h
  have hsize : alg41CoreSize inp < 2 ^ w := by
    simpa using scaled41_word_lt (show 1 ≤ B_word41 δ ξ ω by unfold B_word41; omega) h
  have hcap : arena41Capacity δ ξ ω inp.G.numVerts inp.t < 2 ^ w :=
    (arena41Capacity_le_size inp δ).trans_lt
      (scaled41_word_lt (show K_cap41 δ ξ ω ≤ B_word41 δ ξ ω by unfold B_word41; omega) h)
  obtain ⟨_, hQ, hS, htcap, htQ, htS, _⟩ := arena41Capacity_bounds δ ξ ω inp.G.numVerts inp.t
  have ht := inp.ht_le
  have ht3 : 3 * inp.t ≤ 6 * alg41CoreSize inp := by unfold alg41CoreSize; omega
  have h6 := scaled41_word_lt (show 6 ≤ B_word41 δ ξ ω by unfold B_word41; omega) h
  have hn : inp.G.numVerts < 2 ^ w := by unfold alg41CoreSize at hsize; omega
  have hm1 : inp.G.numEdges + 1 < 2 ^ w := by unfold alg41CoreSize at hsize; omega
  have hnm : inp.G.numVerts + inp.G.numEdges < 2 ^ w := by unfold alg41CoreSize at hsize; omega
  refine ⟨⟨hconst 72 (by unfold B_word41; omega), hn, hm1, ht3.trans_lt h6,
      htQ.trans_lt hcap, htS.trans_lt hcap,
      hconst _ (by unfold B_word41; omega), hconst _ (by unfold B_word41; omega)⟩,
    hconst 3 (by unfold B_word41; omega),
    scaled41_word_lt (show 7 ≤ B_word41 δ ξ ω by unfold B_word41; omega) h,
    hcap, hnm, hconst _ (by unfold B_word41; omega), hconst _ (by unfold B_word41; omega), ?_⟩
  have hcode := hconst (L_code41 δ ξ ω) (by unfold B_word41; omega)
  unfold L_code41 at hcode
  omega

/-- A fixed coefficient also bounds every word of the final written output stream. -/
theorem stream41_word_bound {w δ ξ ω : ℕ} (inp : Alg41CoreInput ξ ω)
    (h : B_word41 δ ξ ω * alg41CoreSize inp < 2 ^ w) :
    (encFolioSetRep (computeFolioDP inp.G inp.Z δ inp.ht inp.p inp.hp inp.τ).toFolioSetRep ++
      encRawCertModels (computeFolioDP inp.G inp.Z δ inp.ht inp.p inp.hp inp.τ).toRawList).length < 2 ^ w := by
  have hZ : inp.Z.card ≤ Q_max ξ ω := by have := inp.hZ; unfold Q_max; omega
  have hlen := stream41_length_le (computeFolioDP inp.G inp.Z δ inp.ht inp.p inp.hp inp.τ) hZ
  have hbound := scaled41_word_lt
    (show L_stream41 δ ξ ω ≤ B_word41 δ ξ ω by unfold B_word41; omega) h
  rw [alg41CoreSize, Nat.add_comm inp.G.numEdges inp.G.numVerts] at hbound
  exact hlen.trans_lt hbound

/-- A logarithmic word size covers any fixed linear coefficient. -/
theorem linear41_lt_two_pow_wordSize (B s : ℕ) :
    B * s < 2 ^ wordSize (B + 1) s := by
  have h1 : B ≤ (s + 2) ^ B :=
    (Nat.le_of_lt Nat.lt_two_pow_self).trans (Nat.pow_le_pow_left (by omega) B)
  have h2 : B * s ≤ (s + 2) ^ (B + 1) := by
    rw [Nat.pow_succ]
    exact Nat.mul_le_mul h1 (by omega)
  exact h2.trans_lt (pow_lt_two_pow_wordSize (by omega) s)

end GraphMinor.Compute
