module

public import GraphMinor.GM21.VertexSplitting

/-!
# Graph Minors XXI, (2.4) in the form claim (2) of (6.3) uses

Claim (2) of the proof of (6.3) (page 28 of the preprint) splits vertices of `G` and says:
"But by (2.4), it follows that $G'$ has an exhaustive vital $(p + 4q)$-linkage". The statement of
(2.4) gives only some vital linkage of `G'`. Exhaustiveness needs to know which linkage: the one
built in the proof of (2.4), `splitSpanningSubgraph G' L`, which has the edges of `L` and all
vertices of `G'`. This file records what claim (2) needs about it
(`isVitalPLinkage_split_and`): it is a vital `(p + 2)`-linkage, it has the same edges as `L`, and
its terminals are terminals of `L` or one of the two new vertices. Every subgraph of `G'` whose
edges are edges of `L` lies in it (`le_splitSpanningSubgraph`).
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Hypergraph

universe u v

variable {α : Type u} {β : Type v}

/-- A subgraph of `G'` whose edges are edges of `L` is a subgraph of `splitSpanningSubgraph G' L`. -/
theorem le_splitSpanningSubgraph {G' L K : Hypergraph α β} (hK : K ≤ G')
    (hKE : K.edgeSet ⊆ L.edgeSet) : K ≤ splitSpanningSubgraph G' L where
  vertexSet_subset := hK.vertexSet_subset
  edgeSet_subset := fun e he => ⟨hK.edgeSet_subset he, hKE he⟩
  ends_eq e he := by
    rw [← hK.ends_eq e he]
    ext x
    simp only [Hypergraph.ends, mem_ofPred_eq, splitSpanningSubgraph]
    exact ⟨fun h => h.2, fun h => ⟨⟨hK.edgeSet_subset he, hKE he⟩, h⟩⟩

/-- **Graph Minors XXI, (2.4), with the linkage of its proof** (page 3 of the preprint). If
`G'` is obtained from `G` by splitting `v` into `v₁, v₂`, and `L` is a vital `p`-linkage in `G`,
then `L' = splitSpanningSubgraph G' L` is a vital `(p + 2)`-linkage in `G'`, it has the edges of
`L`, and each terminal of `L'` is `v₁`, `v₂` or a terminal of `L`. -/
theorem isVitalPLinkage_split_and {G G' L : Hypergraph α β} {v v₁ v₂ : α} {δ₁ δ₂ : Set β}
    {p : ℕ} (hs : IsVertexSplit G G' v v₁ v₂ δ₁ δ₂) (hL : IsVitalPLinkage G L p) :
    IsVitalPLinkage G' (splitSpanningSubgraph G' L) (p + 2) ∧
      (splitSpanningSubgraph G' L).edgeSet = L.edgeSet ∧
      terminals (splitSpanningSubgraph G' L) ⊆ insert v₁ (insert v₂ (terminals L)) := by
  set L' := splitSpanningSubgraph G' L
  have hL'_link : IsLinkage G' L' := isLinkage_splitSpanningSubgraph hs hL.1.1
  have hE_L' : L.edgeSet = L'.edgeSet := by
    simp only [L', splitSpanningSubgraph, hs.edgeSet_eq,
      inter_eq_self_of_subset_right hL.1.1.1.edgeSet_subset]
  refine ⟨isVitalPLinkage_splitSpanningSubgraph hs hL, hE_L'.symm, ?_⟩
  obtain ⟨hinc_other, _, _, _⟩ :=
    isVertexSplit_incidentEdges_props hs hL.1.1.1 (splitSpanningSubgraph_le G' L) hE_L'
  obtain ⟨_, _, _, _, hv_notG', hV_other, _, _, _, _, _⟩ := isVertexSplit_basic_props hs
  intro x hx
  by_cases hxv₁ : x = v₁
  · exact Or.inl hxv₁
  by_cases hxv₂ : x = v₂
  · exact Or.inr (Or.inl hxv₂)
  right; right
  have hxv : x ≠ v := fun h => hv_notG' (h ▸ hx.1)
  have hxG : x ∈ G.vertexSet := (hV_other x hxv hxv₁ hxv₂).mp hx.1
  have hxL : x ∈ L.vertexSet := by rwa [hL.1.2.1]
  have hnot2 : (incidentEdges L x).ncard ≠ 2 := by
    rw [hinc_other x hxv hxv₁ hxv₂]
    exact fun h2 => (hL'_link.notMem_terminals_iff hx.1).mpr h2 hx
  by_contra hx_not_term
  exact hnot2 ((hL.1.1.notMem_terminals_iff hxL).mp hx_not_term)

end GM21
end GraphMinor
