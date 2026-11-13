module

public import GraphMinor.Compute.GM02BuildChildEdges
public import GraphMinor.Compute.GM02RankPairArray
public import GraphMinor.Compute.GM02PackChild
public import GraphMinor.Compute.GM02FilteredChildInput

/-!
# Constructing a complete plain recursive child input

The side filter and rank scan construct the compact graph edges and
counts. Reuse the same ranks for the prescribed pairs, then pack the
three headers and both endpoint arrays. This builds the exact compact
terminated input in linear parent vertex, edge, and pair time.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical GraphMinor.GM02 GraphMinor.Compute.Crossing TwoPaths

/-- Build compact graph and matching arrays, then pack the plain child input. -/
def gm02BuildCompactChildProg (deleted rank edges rawPairs pairs dst : Arr) : Cmd :=
  .seq (gm02BuildChildEdgesProg deleted rank edges)
    (.seq (gm02LookupTemplateWordsProg rawPairs rank pairs) (gm02PackChildProg edges pairs dst))

/-- The combined construction writes exactly the compact filtered child encoding. -/
theorem gm02BuildCompactChildProg_exec {n w : ℕ} (F : SimpleGraph (Fin n))
    [DecidableRel F.Adj] (A B : Finset (Fin n)) (T : Termination {v : Fin n | v ∉ Bᶜ})
    (deleted rank edges rawPairs pairs dst : Arr)
    (hdr : deleted ≠ rank) (hr0 : rank ≠ 0) (hr13 : rank ≠ 13)
    (hr14 : rank ≠ 14) (hr17 : rank ≠ 17) (h17e : 17 ≠ edges) (hre : rank ≠ edges)
    (hpr : rawPairs ≠ rank) (hp17 : rawPairs ≠ 17) (hpe : rawPairs ≠ edges)
    (hpp : rawPairs ≠ pairs) (hrp : rank ≠ pairs) (hep : edges ≠ pairs)
    (hed : edges ≠ dst) (hpd : pairs ≠ dst) (s : State)
    (hn : n < 2 ^ w)
    (hlen : 8 + 2 * (edgeListOf F).length + 2 * T.index < 2 ^ w)
    (hin : s.arrs 0 = encGraph F) (hA : s.arrs 13 = bitSetList A)
    (hB : s.arrs 14 = bitSetList B) (hZ : s.arrs deleted = bitSetList Bᶜ)
    (hm : s.regs 1 = (edgeListOf F).length)
    (hPairs : s.arrs rawPairs = flatEdges (edgeListOf T.pairGraph)) :
    ∃ s' t, Exec w (gm02BuildCompactChildProg deleted rank edges rawPairs pairs dst) s s' t ∧
      t ≤ 20 * n + 134 * (edgeListOf F).length + 62 * T.index + 108 ∧
      s'.arrs dst = (gm02FilteredChildInput F A B T).enc ∧
      (∀ a, a ≠ rank → a ≠ 17 → a ≠ edges → a ≠ pairs → a ≠ dst →
        s'.arrs a = s.arrs a) := by
  have hw : 3 < 2 ^ w := by omega
  have hb : B.card < 2 ^ w :=
    (show B.card ≤ n by simpa only [Fintype.card_fin] using Finset.card_le_univ B).trans_lt hn
  obtain ⟨s₁, t₁, he₁, ht₁, hEdges₁, hRank₁, hN₁, hM₁, ha₁⟩ :=
    gm02BuildChildEdgesProg_exec F A B deleted rank edges hdr hr0 hr13 hr14 hr17 h17e hre s hw hn
      (by omega) hin hA hB hZ hm
  have hPairs₁ := (ha₁ rawPairs hpr hp17 hpe).trans hPairs
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hPairs₂⟩ := gm02RankPairArray_exec Bᶜ T rawPairs rank pairs
    hpp hrp s₁ (by omega) hn (by omega) hPairs₁ hRank₁
  let E := flatEdges (edgeListOf ((gm02FilteredSide F A B).comap (compactEmb Bᶜ)))
  let P := flatEdges (edgeListOf (gm02CompactTermination Bᶜ T).pairGraph)
  have hE₂ : s₂.arrs edges = E :=
    (hk₂.2 edges (by simpa only [List.mem_singleton] using hep)).trans hEdges₁
  have hEl : E.length = 2 * (edgeListOf (gm02FilteredSide F A B)).length := by
    rw [length_flatEdges]
    congr 1
    have hh := gm02FilteredChildInput_edgeCount F A B T
    convert hh using 1; congr 2
  have hPl : P.length = 2 * T.index := by
    rw [length_flatEdges, gm02Termination_pairList_length, gm02CompactTermination_index]
  have hmle := gm02FilteredSide_edgeList_length_le F A B
  have hnc : Bᶜᶜ.card < 2 ^ w := by simpa only [compl_compl] using hb
  obtain ⟨s₃, t₃, he₃, ht₃, hout, ha₃, _⟩ := gm02PackChildProg_exec edges pairs dst hed hpd E P s₂
    hE₂ hPairs₂ hPl ((hk₂.1 312 (by decide)).trans hN₁)
    ((hk₂.1 22 (by decide)).trans hM₁) (by rw [hEl, hPl]; omega) hb (by omega)
    (all_lt_flatEdges _ hnc) (all_lt_flatEdges _ hnc)
  refine ⟨s₃, t₁ + (t₂ + t₃), Exec.seq he₁ (Exec.seq he₂ he₃), ?_, ?_, ?_⟩
  · rw [hEl, hPl] at ht₃
    omega
  · exact hout.trans (gm02FilteredChildInput_enc F A B T).symm
  · intro a har ha17 hae hap had
    exact (ha₃ a had).trans
      ((hk₂.2 a (by simpa only [List.mem_singleton] using hap)).trans (ha₁ a har ha17 hae))

end GraphMinor.Compute
