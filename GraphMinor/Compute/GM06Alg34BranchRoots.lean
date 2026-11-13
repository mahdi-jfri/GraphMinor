module

public import GraphMinor.Compute.GM06Alg34VertexRootRanks
public import GraphMinor.Compute.GM06Alg34SaveRootMask
public import GraphMinor.Compute.GM06Alg34VertexAdjList
import Mathlib.Tactic.Ring

/-!
# Preparing canonical component branches from the original array

Build the endpoint adjacency lists, compute every canonical component
root and its rank, then save the root mask outside the payload scratch
area. The preparation reads only the supplied word array and returns
both the exact component count and the retained canonical flags.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Compute and retain the canonical component flags and their count. -/
def gm06BranchRootsProg : Cmd :=
  .seq gm06VertexAdjListProg (.seq gm06VertexRootMaskProg
    (.seq gm06VertexRootRanksProg gm06SaveRootMaskProg))

private theorem roots_budget (n : ℕ) :
    27 * (n * n) + 62 * n + 54 +
      (n * (26 * (n * n) + 46 * n + 80) + n + 6) +
      (23 * n + 8) + (16 * n + 9) ≤ 300 * (n + 1) ^ 3 := by
  ring_nf
  omega

/-- Exact canonical component preparation takes cubic time and
logarithmic words from the original array, with arbitrary scratch contents. -/
theorem gm06BranchRootsProg_exec (x : GM06DrawingData) {c : ℕ} (hc : 2 ≤ c)
    {s : State} (hinput : s.arrs 0 = x.words) :
    ∃ s' t, Exec (wordSize c x.size) gm06BranchRootsProg s s' t ∧
      t ≤ 300 * (x.size + 1) ^ 3 ∧ s'.arrs 0 = x.words ∧
      s'.arrs 40 = gm06VertexRootMask x ∧ s'.regs 4 = x.n ∧ s'.regs 100 = x.n ∧
      s'.regs 203 = x.componentRoots.length := by
  have hc1 : 1 ≤ c := by omega
  have hsize := lt_two_pow_wordSize_of_le hc1 (n := x.size) (Nat.le_succ _)
  have hn := x.counts_le_size.1.trans_lt hsize
  have hw : 1 < 2 ^ wordSize c x.size := by have hh := x.five_le_words_length; have hh' := x.words_length_le_size; omega
  have hsquare := (Nat.mul_le_mul (x.counts_le_size.1.trans (by omega))
    (x.counts_le_size.1.trans (by omega))).trans_lt (sq_lt_two_pow_wordSize (n := x.size) hc)
  obtain ⟨s₁, t₁, hex₁, ht₁, hadj₁, hlen₁, hsize₁, hcount₁, _, _, ha₁⟩ :=
    gm06VertexAdjListProg_exec x hc hinput
  obtain ⟨s₂, t₂, hex₂, ht₂, hm₂, ha₂, hg₂⟩ :=
    gm06VertexRootMaskProg_exec x hw hn hsquare hsize₁ hadj₁ hlen₁
  obtain ⟨s₃, t₃, hex₃, ht₃, _, hcount₃, ha₃, hg₃⟩ :=
    gm06VertexRootRanksProg_exec x hw hn hm₂
  have hsize₃ : s₃.regs 4 = x.n :=
    (hg₃ 4 (by decide) (by decide)).trans ((hg₂ 4 (by decide) (by decide)).trans hsize₁)
  obtain ⟨s₄, t₄, hex₄, ht₄, hm₄, ha₄, hg₄⟩ :=
    gm06SaveRootMaskProg_exec x hw hn ((ha₃ 36 (by decide)).trans hm₂) hsize₃
  have hns := x.counts_le_size.1
  have hms := x.counts_le_size.2.1
  have hsq := Nat.mul_le_mul hns hns
  have hprod := Nat.mul_le_mul hns (show
    26 * (x.n * x.n) + 46 * x.n + 80 ≤ 26 * (x.size * x.size) + 46 * x.size + 80 by omega)
  refine ⟨s₄, t₁ + (t₂ + (t₃ + t₄)), .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    (show t₁ + (t₂ + (t₃ + t₄)) ≤ 27 * (x.size * x.size) + 62 * x.size + 54 +
      (x.size * (26 * (x.size * x.size) + 46 * x.size + 80) + x.size + 6) +
      (23 * x.size + 8) + (16 * x.size + 9) by omega).trans (roots_budget x.size),
    ?_, hm₄, (hg₄ 4 (by decide)).trans hsize₃, ?_, (hg₄ 203 (by decide)).trans hcount₃⟩
  · exact (ha₄ 0 (by decide)).trans ((ha₃ 0 (by decide)).trans
      ((ha₂ 0 (by decide) (by decide) (by decide) (by decide)).trans ((ha₁ 0 (by decide)).trans hinput)))
  · exact (hg₄ 100 (by decide)).trans ((hg₃ 100 (by decide) (by decide)).trans
      ((hg₂ 100 (by decide) (by decide)).trans hcount₁))

end GraphMinor.Compute
