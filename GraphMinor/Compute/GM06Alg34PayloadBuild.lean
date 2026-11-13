module

public import GraphMinor.Compute.GM06Alg34DeletionPrepare
public import GraphMinor.Compute.GM06Alg34PayloadWrite
public import GraphMinor.Compute.GM06Alg34PayloadCopy
public import GraphMinor.Compute.GM06Alg34PayloadBudget
import Mathlib.Tactic.Ring

/-!
# Complete RAM construction of an induced drawing input

Starting with the original encoded drawing and a retained-vertex mask,
compute all incidence and component tables, allocate the output,
serialize every section, and install the exact result in array 0.
The entire construction takes cubic time and logarithmic word size.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Prepare, serialize, and install the drawing induced by the retained mask. -/
def gm06PayloadBuildProg : Cmd :=
  .seq gm06DeletionPrepareProg (.seq gm06PayloadAllocProg
    (.seq gm06PayloadWriteProg gm06PayloadCopyProg))

private theorem total_budget (n : ℕ) :
    600 * (n + 1) ^ 3 + ((n + 2) ^ 3 + 19) +
      200 * (n + 2) ^ 3 + (16 * (n + n * (n + 2)) + 9) ≤
      1000 * (n + 2) ^ 3 := by
  ring_nf
  omega

/-- The complete construction computes the exact induced input from
array data alone, with arbitrary initial scratch contents, in cubic
RAM time and logarithmic words. -/
theorem gm06PayloadBuildProg_exec (x : GM06DrawingData) (vs : List (Fin x.n))
    {c : ℕ} (hc : 3 ≤ c) {s : State} (hinput : s.arrs 0 = x.words)
    (hmask : s.arrs 4 = gm06VertexMask vs) :
    ∃ s' t, Exec (wordSize c x.size) gm06PayloadBuildProg s s' t ∧
      t ≤ 1000 * (x.size + 2) ^ 3 ∧ s'.arrs 0 = (x.inducedData vs).words := by
  have hc1 : 1 ≤ c := by omega
  have hc2 : 2 ≤ c := by omega
  have hsize : x.size < 2 ^ wordSize c x.size :=
    lt_two_pow_wordSize_of_le hc1 (Nat.le_succ _)
  have hlength := x.words_length_lt_wordSize hc1
  have hNsize := x.cellCount_le_size
  have hN := hNsize.trans_lt hsize
  have hsquare := (Nat.mul_le_mul (hNsize.trans (by omega)) (hNsize.trans (by omega))).trans_lt
    (sq_lt_two_pow_wordSize (n := x.size) hc2)
  have hn := x.counts_le_size.1.trans_lt hsize
  have hw3 : 3 < 2 ^ wordSize c x.size :=
    (show 3 < x.words.length from (by have h := x.five_le_words_length; omega)).trans hlength
  have hcapacity := gm06PayloadCapacity_lt_wordSize x hc
  have hbudget := (gm06SerializationBudget_le_capacity x).trans_lt hcapacity
  have hnewSize := (gm06Induced_size_le_capacity x vs).trans_lt hcapacity
  obtain ⟨s₁, t₁, hex₁, ht₁, hin₁, hmask₁, hrank₁, heMask₁, heRank₁, hends₁,
    hmat₁, hroot₁, hsize₁, hc₁, hn₁, hm₁, _, hnewN₁, hnewE₁, hnewR₁, hsave₁, hadj₁, hlen₁⟩ :=
    gm06DeletionPrepareProg_exec x vs hc2 hinput hmask
  obtain ⟨s₂, t₂, hex₂, ht₂, hbuf₂, hpos₂, ha₂, hg₂⟩ :=
    gm06PayloadAllocProg_exec x vs hc hin₁ hn₁
  obtain ⟨s₃, t₃, hex₃, ht₃, hbuf₃, hpos₃, _⟩ :=
    gm06PayloadWriteProg_exec x vs hw3 hn hN hsquare hlength hbudget
      ((ha₂ 0 (by decide)).trans hin₁)
      ((ha₂ 4 (by decide)).trans hmask₁) ((ha₂ 5 (by decide)).trans hrank₁)
      ((ha₂ 6 (by decide)).trans heMask₁) ((ha₂ 7 (by decide)).trans heRank₁)
      ((ha₂ 8 (by decide)).trans hends₁) ((ha₂ 12 (by decide)).trans hmat₁)
      ((ha₂ 36 (by decide)).trans hroot₁)
      ((hg₂ 4 (by decide)).trans hsize₁) ((hg₂ 170 (by decide)).trans hc₁)
      ((hg₂ 100 (by decide)).trans hn₁) ((hg₂ 101 (by decide)).trans hm₁)
      ((hg₂ 131 (by decide)).trans hnewN₁) ((hg₂ 137 (by decide)).trans hnewE₁)
      ((hg₂ 203 (by decide)).trans hnewR₁) ((hg₂ 176 (by decide)).trans hsave₁)
      (hadj₁.of_arrs_eq (ha₂ 30 (by decide)) (ha₂ 31 (by decide)) (ha₂ 32 (by decide)))
      (by rw [ha₂ 32 (by decide)]; exact hlen₁) hbuf₂ hpos₂
  obtain ⟨s₄, t₄, hex₄, ht₄, hnewInput, _, _⟩ :=
    gm06PayloadCopyProg_exec (x.inducedData vs) (by omega) hnewSize hbuf₃ hpos₃
  have htime₃ := ht₃.trans (gm06PayloadWriteTime_le x vs)
  have hwords := gm06Induced_words_length_le x vs
  refine ⟨s₄, t₁ + (t₂ + (t₃ + t₄)), .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), ?_, hnewInput⟩
  have htot : t₁ + (t₂ + (t₃ + t₄)) ≤
      600 * (x.size + 1) ^ 3 + ((x.size + 2) ^ 3 + 19) +
        200 * (x.size + 2) ^ 3 + (16 * (x.size + x.size * (x.size + 2)) + 9) := by
    change t₂ ≤ (x.size + 2) ^ 3 + 19 at ht₂
    omega
  exact htot.trans (total_budget x.size)

end GraphMinor.Compute
