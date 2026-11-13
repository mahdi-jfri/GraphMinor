module

public import GraphMinor.Compute.GM02CompactFilteredEdges

/-!
# Building the compact edge array of a recursive child

Compute ranks of the retained child vertices, filter the parent edge
list by the canonical side rule, and replace every surviving endpoint
by its rank. The result is the exact compact child edge array. The
program derives its edge count from the filter and its vertex count
from the rank scan.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical GraphMinor.Compute.Crossing TwoPaths

/-- Rank the child vertices, filter the parent edges, and rewrite their endpoints. -/
def gm02BuildChildEdgesProg (deleted rank dst : Arr) : Cmd :=
  .seq (compactRankProg deleted rank 310 311 312)
    (.seq filterEdgesProg (gm02RankEdgeWordsProg 17 rank dst))

/-- The three passes construct exactly the compact child edge words in linear time. -/
theorem gm02BuildChildEdgesProg_exec {n w : ℕ} (F : SimpleGraph (Fin n))
    [DecidableRel F.Adj] (A B : Finset (Fin n)) (deleted rank dst : Arr)
    (hdr : deleted ≠ rank) (hr0 : rank ≠ 0) (hr13 : rank ≠ 13)
    (hr14 : rank ≠ 14) (hr17 : rank ≠ 17) (h17d : 17 ≠ dst) (hrd : rank ≠ dst)
    (s : State) (hw : 3 < 2 ^ w) (hn : n < 2 ^ w)
    (hlen : 8 + 2 * (edgeListOf F).length < 2 ^ w)
    (hin : s.arrs 0 = encGraph F) (hA : s.arrs 13 = bitSetList A)
    (hB : s.arrs 14 = bitSetList B) (hZ : s.arrs deleted = bitSetList Bᶜ)
    (hm : s.regs 1 = (edgeListOf F).length) :
    ∃ s' t, Exec w (gm02BuildChildEdgesProg deleted rank dst) s s' t ∧
      t ≤ 20 * n + 102 * (edgeListOf F).length + 44 ∧
      s'.arrs dst = flatEdges
        (edgeListOf ((gm02FilteredSide F A B).comap (compactEmb Bᶜ))) ∧
      s'.arrs rank = List.ofFn (fun v : Fin n => compactRank Bᶜ v.val) ∧
      s'.regs 312 = B.card ∧
      s'.regs 22 = (edgeListOf (gm02FilteredSide F A B)).length ∧
      (∀ a, a ≠ rank → a ≠ 17 → a ≠ dst → s'.arrs a = s.arrs a) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hrank, hcount, _, ha₁, hr₁⟩ :=
    compactRankProg_exec Bᶜ deleted rank 310 311 312 hdr (by decide) (by decide)
      (by decide) (by omega) hn hZ
  obtain ⟨s₂, t₂, he₂, ht₂, hm₂, harr₂, ha₂, hr₂⟩ :=
    gm02FilterSide_exec F A B hw hn hlen s₁
      ((ha₁ 0 hr0.symm).trans hin)
      (IsBitSet.of_bitSetList _ _ _ ((ha₁ 14 hr14.symm).trans hB))
      (IsBitSet.of_bitSetList _ _ _ ((ha₁ 13 hr13.symm).trans hA))
      ((hr₁ 1 (by decide) (by decide) (by decide)).trans hm)
  have hmle := gm02FilteredSide_edgeList_length_le F A B
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, hout⟩ :=
    gm02RankEdgeWordsProg_exec Bᶜ (edgeListOf (gm02FilteredSide F A B)) 17 rank dst h17d hrd
      0 0 _ s₂ hn (by omega) harr₂ ((ha₂ rank hr17).trans hrank) hm₂
  refine ⟨s₃, t₁ + (t₂ + t₃), Exec.seq he₁ (Exec.seq he₂ he₃), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · exact hout.trans (gm02CompactFilteredSide_edgeWords F A B).symm
  · exact (hk₃.2 rank (by simpa only [List.mem_singleton] using hrd)).trans
      ((ha₂ rank hr17).trans hrank)
  · have hc : s₁.regs 312 = B.card := by simpa only [compl_compl] using hcount
    exact (hk₃.1 312 (by decide)).trans
      ((hr₂ 312 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)).trans hc)
  · exact (hk₃.1 22 (by decide)).trans hm₂
  · intro a har ha17 had
    exact (hk₃.2 a (by simpa only [List.mem_singleton] using had)).trans
      ((ha₂ a ha17).trans (ha₁ a har))

end GraphMinor.Compute
