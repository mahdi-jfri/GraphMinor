module

public import GraphMinor.Compute.GM06Alg34DeletionLabelTables
public import GraphMinor.Compute.GM06Alg34DeletionRegionTables
public import GraphMinor.Compute.GM06Alg34ClosureMatrixProg
import Mathlib.Tactic.Ring

/-!
# Preparing every table for the induced deletion payload

Read the original input to compute its closure matrix, save the cuff
cursor, compute the surviving labels and endpoints, and construct the
complement graph and canonical roots. All inputs to serialization are
computed from the original array and the retained vertex mask. The
complete preparation has a cubic bound with logarithmic words.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Compute every finite table needed to serialize an induced deletion. -/
def gm06DeletionPrepareProg : Cmd :=
  .seq gm06ClosureMatrixProg (.seq gm06DeletionLabelTablesProg gm06DeletionRegionTablesProg)

private theorem preparation_budget (n : ℕ) :
    120 * (n + 1) ^ 2 + (134 * n + 36) +
      (n * (26 * (n * n) + 46 * n + 80) + 149 * (n * n) + 48 * n + 37) ≤
      600 * (n + 1) ^ 3 := by
  ring_nf
  omega

/-- Starting with the original array and retained vertex mask, the RAM
computes all exact deletion tables in at most `600 * (size + 1)^3`
steps with logarithmic words and arbitrary other scratch contents. -/
theorem gm06DeletionPrepareProg_exec (x : GM06DrawingData) (vs : List (Fin x.n))
    {c : ℕ} (hc : 2 ≤ c) {s : State} (hinput : s.arrs 0 = x.words)
    (hmask : s.arrs 4 = gm06VertexMask vs) :
    ∃ s' t, Exec (wordSize c x.size) gm06DeletionPrepareProg s s' t ∧
      t ≤ 600 * (x.size + 1) ^ 3 ∧ s'.arrs 0 = x.words ∧
      s'.arrs 4 = gm06VertexMask vs ∧ s'.arrs 5 = gm06VertexRanks vs ∧
      s'.arrs 6 = gm06EdgeMask x vs ∧ s'.arrs 7 = gm06EdgeRanks x vs ∧
      s'.arrs 8 = (x.inducedData vs).endpointWords ∧
      s'.arrs 12 = gm06ClosureMatrixData x ∧ s'.arrs 36 = gm06RootMask x vs ∧
      s'.regs 4 = x.cellCount ∧ s'.regs 170 = x.cellCount ∧
      s'.regs 100 = x.n ∧ s'.regs 101 = x.ends.length ∧ s'.regs 102 = x.regions.length ∧
      s'.regs 131 = (x.activeVertices vs).length ∧ s'.regs 137 = (x.activeEdges vs).length ∧
      s'.regs 203 = (x.regionRoots vs).length ∧ s'.regs 176 = x.cuffOffset ∧
      IsAdjList (x.complementGraph vs) 30 31 32 (adjListOf (x.complementGraph vs)) s' ∧
      (s'.arrs 32).length = x.cellCount * x.cellCount := by
  have hc1 : 1 ≤ c := by omega
  have hsize : x.size < 2 ^ wordSize c x.size := lt_two_pow_wordSize_of_le hc1 (Nat.le_succ _)
  have hlength := x.words_length_lt_wordSize hc1
  have hcounts := x.counts_le_size
  have hNsize := x.cellCount_le_size
  have hN := hNsize.trans_lt hsize
  have hsquare : x.cellCount * x.cellCount < 2 ^ wordSize c x.size :=
    (Nat.mul_le_mul (hNsize.trans (by omega)) (hNsize.trans (by omega))).trans_lt
      (sq_lt_two_pow_wordSize hc)
  have hw3 : 3 < 2 ^ wordSize c x.size := by have hh := x.five_le_words_length; omega
  have hw1 : 1 < 2 ^ wordSize c x.size := by omega
  let tail := x.regionWords ++ (x.cuffWords ++ x.divisionWords)
  have hstream : AtStream 0 3 (x.endpointWords ++ tail) s := by
    refine ⟨[x.n, x.ends.length, x.regions.length], rfl, ?_⟩
    rw [hinput, x.words_layout]
    simp only [tail, List.append_assoc]
  obtain ⟨s₁, t₁, hex₁, ht₁, hclosure, hcellCount, hcursor, _, hn₁, hm₁, hr₁, harr₁, _⟩ :=
    gm06ClosureMatrixProg_exec x hc hinput
  obtain ⟨s₂, t₂, hex₂, ht₂, hV, hE, hR, hends, hnewV, hnewE, hsaved, harr₂, hreg₂⟩ :=
    gm06DeletionLabelTablesProg_exec x vs tail hw3 (hcounts.1.trans_lt hsize)
      (x.regionOffset_lt_length.trans hlength) (x.cuffOffset_lt_length.trans hlength)
      (hstream.of_arr_eq (harr₁ 0 (by decide))) hm₁ hcursor
      ((harr₁ 4 (by decide)).trans hmask)
  have hkeep : ∀ q : ℕ, q = 100 ∨ q = 101 ∨ q = 102 ∨ q = 170 → s₂.regs q = s₁.regs q := by
    intro q hq
    apply hreg₂ q <;> rcases hq with rfl | rfl | rfl | rfl <;> decide
  have hc₂ : s₂.regs 170 = x.cellCount := (hkeep _ (Or.inr (Or.inr (Or.inr rfl)))).trans hcellCount
  have hn₂ : s₂.regs 100 = x.n := (hkeep _ (Or.inl rfl)).trans hn₁
  have hm₂ : s₂.regs 101 = x.ends.length := (hkeep _ (Or.inr (Or.inl rfl))).trans hm₁
  have hr₂ : s₂.regs 102 = x.regions.length := (hkeep _ (Or.inr (Or.inr (Or.inl rfl)))).trans hr₁
  have hclosure₂ : s₂.arrs 12 = gm06ClosureMatrixData x :=
    (harr₂ _ (by decide) (by decide) (by decide) (by decide)).trans hclosure
  have hmask₂ : s₂.arrs 4 = gm06VertexMask vs :=
    (harr₂ _ (by decide) (by decide) (by decide) (by decide)).trans
      ((harr₁ _ (by decide)).trans hmask)
  obtain ⟨s₃, t₃, hex₃, ht₃, hroots, hnewR, hsize₃, hlists, hlen, harr₃, hreg₃⟩ :=
    gm06DeletionRegionTablesProg_exec x vs hw1 hN hsquare hclosure₂ hc₂ hn₂ hm₂ hmask₂ hE
  have hnewSize : (x.activeEdges vs).length ≤ x.size := by
    have hle : (x.activeEdges vs).length ≤ x.ends.length := by
      rw [← gm06EdgeMask_sum]; exact gm06EdgeMask_sum_le x vs
    exact hle.trans hcounts.2.1
  have hlabelsTime : t₂ ≤ 134 * x.size + 36 := by omega
  have hNsquare : x.cellCount * x.cellCount ≤ x.size * x.size := Nat.mul_le_mul hNsize hNsize
  have hrootTime : x.cellCount * (26 * (x.cellCount * x.cellCount) + 46 * x.cellCount + 80) ≤
      x.size * (26 * (x.size * x.size) + 46 * x.size + 80) :=
    Nat.mul_le_mul hNsize (by omega)
  have hregionsTime : t₃ ≤ x.size * (26 * (x.size * x.size) + 46 * x.size + 80) +
      149 * (x.size * x.size) + 48 * x.size + 37 := by omega
  refine ⟨s₃, t₁ + (t₂ + t₃), Exec.seq hex₁ (Exec.seq hex₂ hex₃),
    (show t₁ + (t₂ + t₃) ≤ 120 * (x.size + 1) ^ 2 + (134 * x.size + 36) +
      (x.size * (26 * (x.size * x.size) + 46 * x.size + 80) +
        149 * (x.size * x.size) + 48 * x.size + 37) by omega).trans (preparation_budget x.size),
    ?_, (harr₃ 4 (by decide)).trans hmask₂,
    (harr₃ 5 (by decide)).trans hV, (harr₃ 6 (by decide)).trans hE,
    (harr₃ 7 (by decide)).trans hR, (harr₃ 8 (by decide)).trans hends,
    (harr₃ 12 (by decide)).trans hclosure₂, hroots, hsize₃,
    (hreg₃ 170 (by decide) (by decide)).trans hc₂,
    (hreg₃ 100 (by decide) (by decide)).trans hn₂,
    (hreg₃ 101 (by decide) (by decide)).trans hm₂,
    (hreg₃ 102 (by decide) (by decide)).trans hr₂,
    (hreg₃ 131 (by decide) (by decide)).trans hnewV,
    (hreg₃ 137 (by decide) (by decide)).trans hnewE, hnewR,
    (hreg₃ 176 (by decide) (by decide)).trans hsaved, hlists, hlen⟩
  exact (harr₃ 0 (by decide)).trans ((harr₂ 0 (by decide) (by decide) (by decide) (by decide)).trans
    ((harr₁ 0 (by decide)).trans hinput))

end GraphMinor.Compute
