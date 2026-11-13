module

public import GraphMinor.Compute.GM06Alg34GapPayloadTables
public import GraphMinor.Compute.GM06Alg34GapUpdate
public import GraphMinor.Compute.GM06Alg34CuffParse
import Mathlib.Tactic.Ring

/-!
# Complete induced drawing and gap payload replacement

Read the original cuff, construct and install the induced base payload,
then use its preserved old complement tables to update the supplied gap
incidence list. Both outputs are the exact finite induced input. The
whole pass uses logarithmic words and has a cubic RAM time bound.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Replace the base drawing and its external gap incidence by their induced payloads. -/
def gm06GapPayloadBuildProg : Cmd :=
  .seq gm06ReadDiscCuffProg (.seq gm06PayloadBuildProg gm06GapUpdateProg)

private theorem gap_payload_budget (n : ℕ) :
    100 * (n + 1) + 1000 * (n + 2) ^ 3 +
      (17 + n * (26 * (n * n) + 37 * n + 74)) ≤ 1200 * (n + 2) ^ 3 := by
  ring_nf
  omega

private theorem gap_time_mono {N k n t : ℕ} (hN : N ≤ n) (hk : k ≤ n)
    (ht : t ≤ 17 + k * (26 * (N * N) + 37 * N + 74)) :
    t ≤ 17 + n * (26 * (n * n) + 37 * n + 74) := by
  have hsq := Nat.mul_le_mul hN hN
  have hm := Nat.mul_le_mul hk
    (show 26 * (N * N) + 37 * N + 74 ≤ 26 * (n * n) + 37 * n + 74 by omega)
  omega

private theorem total_time {n N k t₁ t₂ t₃ : ℕ} (hN : N ≤ n) (hk : k ≤ n)
    (ht₁ : t₁ ≤ 100 * (n + 1)) (ht₂ : t₂ ≤ 1000 * (n + 2) ^ 3)
    (ht₃ : t₃ ≤ 17 + k * (26 * (N * N) + 37 * N + 74)) :
    t₁ + (t₂ + t₃) ≤ 1200 * (n + 2) ^ 3 := by
  have ht := Nat.add_le_add ht₁ (Nat.add_le_add ht₂ (gap_time_mono hN hk ht₃))
  have hh := gap_payload_budget n
  rw [Nat.add_assoc] at hh
  exact ht.trans hh

/-- From a supplied disc cuff and region-incidence array, the RAM
computes both exact induced payloads in cubic time with logarithmic words. -/
theorem gm06GapPayloadBuildProg_exec (x : GM06DrawingData) (vs L : List (Fin x.n))
    (g : Fin L.length → Fin x.regions.length) (hL : x.cuffs = [L])
    {c : ℕ} (hc : 3 ≤ c) {s : State} (hinput : s.arrs 0 = x.words)
    (hmask : s.arrs 4 = gm06VertexMask vs)
    (hgap : s.arrs 47 = List.ofFn (fun j => (g j).val)) :
    ∃ s' t, Exec (wordSize c x.size) gm06GapPayloadBuildProg s s' t ∧
      t ≤ 1200 * (x.size + 2) ^ 3 ∧ s'.arrs 0 = (x.inducedData vs).words ∧
      s'.arrs 47 = (x.gapRegionsAfterDeletion vs L (List.ofFn g)).map Fin.val ∧
      (∀ A : ℕ, 50 ≤ A → s'.arrs A = s.arrs A) := by
  have hc1 : 1 ≤ c := by omega
  have hc2 : 2 ≤ c := by omega
  have hsize : x.size < 2 ^ wordSize c x.size := lt_two_pow_wordSize_of_le hc1 (Nat.le_succ _)
  have hNle := x.cellCount_le_size
  have hN := hNle.trans_lt hsize
  have hsquare : x.cellCount * x.cellCount < 2 ^ wordSize c x.size :=
    (Nat.mul_le_mul (hNle.trans (by omega : x.size ≤ x.size + 2))
      (hNle.trans (by omega : x.size ≤ x.size + 2))).trans_lt
      (sq_lt_two_pow_wordSize (n := x.size) hc2)
  have hw : 1 < 2 ^ wordSize c x.size := by
    have hh := x.five_le_words_length
    have hle := x.words_length_le_size
    omega
  have hKle : L.length ≤ x.size := by
    have hh := x.cuffWords_singleton_length hL
    have hp := x.divisionOffset_lt_length
    have hle := x.words_length_le_size
    dsimp only [GM06DrawingData.divisionOffset] at hp
    omega
  obtain ⟨s₁, t₁, he₁, ht₁, hcuff, _, _, _, _, _, _, harr₁, _⟩ :=
    gm06ReadDiscCuffProg_exec x hL hc1 hinput
  have hin₁ := (harr₁ 0 (by decide)).trans hinput
  have hv₁ := (harr₁ 4 (by decide)).trans hmask
  obtain ⟨s₂, t₂, he₂, ht₂, hbase⟩ := gm06PayloadBuildProg_exec x vs hc hin₁ hv₁
  obtain ⟨hv₂, hsize₂, hn₂, hm₂, hroot₂, hranks₂, hadj₂, hlen₂⟩ :=
    gm06GapPayloadBuild_tables x vs hc2 hin₁ hv₁ he₂
  have hcuff₂ : s₂.arrs 2 = L.map Fin.val :=
    (gm06GapPayloadBuild_array_frame he₂ (Or.inl rfl)).trans hcuff
  have hgap₂ : s₂.arrs 47 = List.ofFn (fun j => (g j).val) :=
    (gm06GapPayloadBuild_array_frame he₂ (Or.inr (by decide))).trans
      ((harr₁ 47 (by decide)).trans hgap)
  obtain ⟨s₃, t₃, he₃, ht₃, hgap₃, harr₃, _⟩ :=
    gm06GapUpdateProg_exec x vs L g hw hN hsquare (hKle.trans_lt hsize)
      hsize₂ hn₂ hm₂ hcuff₂ hgap₂ hv₂ hadj₂ hlen₂ hroot₂ hranks₂
  refine ⟨s₃, t₁ + (t₂ + t₃), .seq he₁ (.seq he₂ he₃), ?_,
    (harr₃ 0 (by decide) (by decide) (by decide) (by decide)).trans hbase, hgap₃, ?_⟩
  · exact total_time hNle hKle ht₁ ht₂ ht₃
  · intro A hA
    exact (harr₃ A (by omega) (by omega) (by omega) (by omega)).trans
      ((gm06GapPayloadBuild_array_frame he₂ (Or.inr (by omega))).trans (harr₁ A (by omega)))

end GraphMinor.Compute
