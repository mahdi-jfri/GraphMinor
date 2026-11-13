module

public import GraphMinor.GM01.CombTailMinor
public import GraphMinor.GM01.CombBlocks
import GraphMinor.GM01.MinorModelMaps
import Lean.Elab.Tactic.Omega

/-!
# The minor in the final comb block

The parenthesis in the proof of Graph Minors I, (4.1), page 55, uses the
remaining spine length `N−2n+2`. The last block is the region after the
cut at zero-based index `2n−3`. A consecutive comb starting at index
`2n−2` lies in that region. The root-path invariance identifies this
region with the block in `H`, and target inclusion retains its minor
model there.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- The long comb retained in the final block, as used in the proof of
Graph Minors I, (4.1), page 55. Any length fitting after `2n−2` is allowed;
the paper takes that length to be `2δ`. -/
theorem comb_lastBlock_minor_model {α β : Type*} [Nonempty β] {γ L n m : ℕ}
    (hn : 2 ≤ n) (htail : 2 * n ≤ L) (hbound : 2 * n - 2 + m ≤ L)
    {G K R : Graph α β} (hK : K ≤ G)
    {c : (pathComb γ L).verts → α} (hc : Injective c)
    (hcentres : ∀ v, c v ∈ V(K))
    (P : (pathComb γ L).coe.edgeSet → Graph α β)
    (hPaths : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds K (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e e' : (pathComb γ L).coe.edgeSet, e ≠ e' →
      V(P e) ∩ V(P e') ⊆ range c ∧ Disjoint E(P e) E(P e'))
    (hE : E(K) = ⋃ e, E(P e)) (root : α)
    (hR : IsGraphPathWithEnds G R root (c (rootedPathComb γ L (by omega)).root))
    (hmeet : V(K) ∩ V(R) ⊆ {c (rootedPathComb γ L (by omega)).root}) :
    ∃ (ηv : (pathComb γ m).verts → Set α) (ηe : Sym2 (pathComb γ m).verts → β),
      IsMinorModel (Graph.ofSimpleGraph (pathComb γ m).coe)
        ((subgraphUnion G K R).induce
          (combBlock (by omega : 0 < L) (subgraphUnion G K R) c
            (⟨n - 1, by omega⟩ : Fin n))) ηv ηe := by
  let i : Fin L := ⟨2 * n - 3, by omega⟩
  let last : Fin L := ⟨L - 1, by omega⟩
  let D := vertexAvoidanceRegion K
    (c ⟨Sum.inl last, pathComb_spine_mem γ L last⟩)
    (c ⟨Sum.inl i, pathComb_spine_mem γ L i⟩)
  obtain ⟨ηv, ηe, hmodel⟩ := comb_tail_minor_model hc hcentres P hPaths hInter
    i (2 * n - 2) (by change 2 * n - 3 < 2 * n - 2; omega) hbound
  have hPN : ∀ e, P e ≤ K := by
    intro e
    obtain ⟨_, _, _, hP, _⟩ := hPaths e
    exact hP.le
  have hRanges : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b} := by
    intro e
    obtain ⟨a, b, he, _, hRange⟩ := hPaths e
    exact ⟨a, b, he, hRange⟩
  have hRegionEq := comb_root_path_region_eq hK hR.le hc hPN hE hRanges
    (fun e f hne ↦ (hInter e f hne).1) i last
    (by change 2 * n - 3 < L - 1; omega) (hcentres _) hmeet
  have hBlockEq : combBlock (by omega : 0 < L) (subgraphUnion G K R) c
      (⟨n - 1, by omega⟩ : Fin n) = D := by
    have hlt : n - 1 < n := by omega
    have hnot : ¬ n - 1 + 1 < n := by omega
    have hzero : 2 * (n - 1) ≠ 0 := by omega
    have hlong : 2 * (n - 1) < L := by omega
    simp only [combBlock, orderedRegionBlock, hlt, hnot, ↓reduceIte, sdiff_empty,
      combSpineRegion, hzero, hlong, ↓reduceDIte]
    have hindex : 2 * (n - 1) - 1 = 2 * n - 3 := by omega
    simpa only [D, i, last, hindex] using hRegionEq
  have hKH : K ≤ subgraphUnion G K R := le_subgraphUnion_left hK hR.le
  have hTarget : K.induce D ≤ (subgraphUnion G K R).induce D := by
    refine ⟨Subset.rfl, ?_⟩
    intro e x y he
    exact ⟨he.1.mono hKH, he.2⟩
  refine ⟨ηv, ηe, ?_⟩
  rw [hBlockEq]
  exact minorModel_mono hmodel hTarget

end GraphMinor.GM01
