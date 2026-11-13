module

public import GraphMinor.GM21.Defs
public import GraphMinor.GM10.TangleLemmas

/-!
# Graph Minors XXI, proof of (6.4): separations from a set of vertices and edges

Claim (1) of the proof of (6.4) (page 25 of the preprint) says that the pair
$(A(F), B(F))$ is a separation of `G`. We build both sides from the vertex and edge sets of the
inside: `B` is the subgraph of `G` with a given vertex set `W` and edge set `F` (`subOn G W F`),
and `A` keeps the other edges and all vertices except those of `W \ X`, where `X` is to be the
common boundary. If every edge of `F` has its ends in `W`, and no other edge of `G` has an end in
`W \ X`, then `(A, B)` is a separation of `G` with `V(A ∩ B) = X` (`isSeparation_subOn`).
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Hypergraph GraphMinor.GM10

universe u v

variable {α : Type u} {β : Type v}

/-- The subgraph of `G` with vertex set `W ∩ V(G)` and edge set `F ∩ E(G)`. It is a subgraph of
`G` when every edge of `F` has its ends in `W` (`subOn_le`). -/
def subOn (G : Hypergraph α β) (W : Set α) (F : Set β) : Hypergraph α β where
  vertexSet := W ∩ G.vertexSet
  edgeSet := F ∩ G.edgeSet
  Inc e x := G.Inc e x ∧ e ∈ F ∧ x ∈ W
  vertex_mem_of_inc _ _ h := ⟨h.2.2, G.vertex_mem_of_inc h.1⟩
  edge_mem_of_inc _ _ h := ⟨h.2.1, G.edge_mem_of_inc h.1⟩
  vertexSet_finite := G.vertexSet_finite.subset inter_subset_right
  edgeSet_finite := G.edgeSet_finite.subset inter_subset_right

theorem subOn_le {G : Hypergraph α β} {W : Set α} {F : Set β}
    (h : ∀ e ∈ F, e ∈ G.edgeSet → G.ends e ⊆ W) : subOn G W F ≤ G where
  vertexSet_subset := inter_subset_right
  edgeSet_subset := inter_subset_right
  ends_eq e he := by
    ext x
    simp only [ends, subOn, mem_ofPred_eq]
    exact ⟨fun hx => ⟨hx, he.1, h e he.1 he.2 hx⟩, fun hx => hx.1⟩

/-- A subgraph `M ≤ G` whose vertices and edges lie in `W` and `F` is a subgraph of
`subOn G W F`. -/
theorem le_subOn {G M : Hypergraph α β} {W : Set α} {F : Set β} (hM : M ≤ G)
    (hW : M.vertexSet ⊆ W) (hF : M.edgeSet ⊆ F) : M ≤ subOn G W F where
  vertexSet_subset x hx := ⟨hW hx, hM.vertexSet_subset hx⟩
  edgeSet_subset e he := ⟨hF he, hM.edgeSet_subset he⟩
  ends_eq e he := by
    ext x
    simp only [ends, subOn, mem_ofPred_eq]
    constructor
    · intro hx
      exact (GM10.inc_iff_of_le hM he).2 hx.1
    · intro hx
      exact ⟨(GM10.inc_iff_of_le hM he).1 hx, hF he, hW (M.vertex_mem_of_inc hx)⟩

/-- **The separation of claim (1).** Let `W ⊆ V(G)` and `F ⊆ E(G)` be such that every edge of `F`
has its ends in `W`, and let `X ⊆ W` be such that no edge of `G` outside `F` has an end in
`W \ X`. Then `(A, B)`, with `B = subOn G W F` and `A` the rest of `G` together with `X`, is a
separation of `G`, and `V(A ∩ B) = X`. -/
theorem isSeparation_subOn {G : Hypergraph α β} {W X : Set α} {F : Set β}
    (hW : W ⊆ G.vertexSet) (hX : X ⊆ W) (hF : ∀ e ∈ F, e ∈ G.edgeSet → G.ends e ⊆ W)
    (hout : ∀ e ∈ G.edgeSet, e ∉ F → ∀ x, G.Inc e x → x ∉ W \ X) :
    G.IsSeparation (subOn G (G.vertexSet \ (W \ X)) (G.edgeSet \ F)) (subOn G W F) ∧
      (subOn G (G.vertexSet \ (W \ X)) (G.edgeSet \ F) ∩ subOn G W F).vertexSet = X := by
  have hA : subOn G (G.vertexSet \ (W \ X)) (G.edgeSet \ F) ≤ G := by
    apply subOn_le
    intro e he heG x hx
    exact ⟨G.vertex_mem_of_inc hx, hout e heG he.2 x hx⟩
  have hB : subOn G W F ≤ G := subOn_le hF
  refine ⟨⟨hA, hB, ?_, ?_⟩, ?_⟩
  · apply le_antisymm (GM10.union_le hA hB)
    refine (GM10.le_iff_of_le le_rfl (GM10.union_le hA hB)).2 ⟨?_, ?_⟩
    · intro x hx
      by_cases hxW : x ∈ W \ X
      · exact Or.inr ⟨hxW.1, hx⟩
      · exact Or.inl ⟨⟨hx, hxW⟩, hx⟩
    · intro e he
      by_cases heF : e ∈ F
      · exact Or.inr ⟨heF, he⟩
      · exact Or.inl ⟨⟨he, heF⟩, he⟩
  · ext e
    simp only [subOn, mem_empty_iff_false, iff_false]
    rintro ⟨⟨⟨-, h1⟩, -⟩, h2, -⟩
    exact h1 h2
  · ext x
    simp only [subOn]
    constructor
    · rintro ⟨⟨⟨hxG, hxWX⟩, -⟩, hxW, -⟩
      by_contra hxX
      exact hxWX ⟨hxW, hxX⟩
    · intro hxX
      have hxW := hX hxX
      exact ⟨⟨⟨hW hxW, fun h => h.2 hxX⟩, hW hxW⟩, hxW, hW hxW⟩

/-- Monotonicity of `subOn`. -/
theorem subOn_mono {G : Hypergraph α β} {W W' : Set α} {F F' : Set β}
    (hFW : ∀ e ∈ F, e ∈ G.edgeSet → G.ends e ⊆ W) (hW : W ⊆ W') (hF : F ⊆ F') :
    subOn G W F ≤ subOn G W' F' where
  vertexSet_subset x hx := ⟨hW hx.1, hx.2⟩
  edgeSet_subset e he := ⟨hF he.1, he.2⟩
  ends_eq e he := by
    ext x
    simp only [ends, subOn, mem_ofPred_eq]
    exact ⟨fun hx => ⟨hx.1, he.1, hFW e he.1 he.2 hx.1⟩,
      fun hx => ⟨hx.1, hF he.1, hW hx.2.2⟩⟩

end GM21
end GraphMinor
