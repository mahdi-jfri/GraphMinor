module

public import GraphMinor.GM21.Section8
public import GraphMinor.GM21.InfVert

/-!
# Graph Minors XXI: (8.4) for every type of vertices

The proof of (8.4) in `GraphMinor.GM21.Section8` splits vertices, and each split needs two new
vertices outside `V(G)`. There the new vertices are taken from the type `α` of vertices, so that
proof assumes `α` is infinite (`theorem_8_4_of_infinite`).

Here we remove this hypothesis. We move the graph, its pseudo-presentation and its tangle into
`α ⊕ ULift ℕ` by `Sum.inl` (the map `mapInl` of `GraphMinor.GM21.InfVert`). The moved graph has a
pseudo-presentation of the same depth and defect, which surrounds the moved tangle, and a vital
`p`-linkage moves to a vital `p`-linkage. So `theorem_8_4_of_infinite`, applied in
`α ⊕ ULift ℕ`, gives (8.4) for `α`.

Proves:
- `theorem_8_4_proof`: Graph Minors XXI, (8.4), with no hypothesis on `α`.
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Topology Hypergraph GraphMinor.Surface GraphMinor.GM10

universe u v w

variable {α : Type u} {β : Type v}

/-- Disjoint paths move along `Sum.inl`. -/
lemma hasDisjointPaths_mapInl (H : Hypergraph α β) {X Y : Set α} {k : ℕ}
    (h : HasDisjointPaths H.skeleton X Y k) :
    HasDisjointPaths (mapInl H).skeleton (Sum.inl '' X) (Sum.inl '' Y) k := by
  obtain ⟨P, hP⟩ := h
  let f : H.skeleton →g (mapInl H).skeleton :=
    ⟨Sum.inl, fun hadj => (mapInl_skeleton_adj_iff H _ _).mpr hadj⟩
  have hf : Function.Injective f := Sum.inl_injective
  refine ⟨fun i => ⟨Sum.inl (P i).first, Sum.inl (P i).last, (P i).walk.map f,
    (P i).isPath.map hf,
    mem_image_of_mem _ (P i).first_mem, mem_image_of_mem _ (P i).last_mem⟩, ?_⟩
  intro i j hij
  refine Set.disjoint_left.mpr fun x hxi hxj => ?_
  simp only [mem_ofPred_eq, SimpleGraph.Walk.support_map, List.mem_map] at hxi hxj
  obtain ⟨a, ha, rfl⟩ := hxi
  obtain ⟨b, hb, hba⟩ := hxj
  cases hf hba
  exact Set.disjoint_left.mp (hP hij) ha hb

/-- `μ(F)` commutes with moving along `Sum.inl`. -/
lemma supportGraph_mapInl {S : Type w} [TopologicalSpace S] (G : Hypergraph α β) (Γ : Drawing S)
    (μ : BoundaryUnit S → Hypergraph α β) (F : Set S) :
    supportGraph (mapInl G) Γ (fun x => mapInl (μ x)) F = mapInl (supportGraph G Γ μ F) := by
  refine Hypergraph.ext ?_ rfl ?_
  · change Sum.inl '' G.vertexSet ∩
        ((⋃ s ∈ {s ∈ drawingSpaces Γ | s ⊆ F}, Sum.inl '' (μ (.space s)).vertexSet) ∪
         (⋃ u ∈ Γ.V ∩ F, Sum.inl '' (μ (.vertex u)).vertexSet)) =
      Sum.inl '' (G.vertexSet ∩
        ((⋃ s ∈ {s ∈ drawingSpaces Γ | s ⊆ F}, (μ (.space s)).vertexSet) ∪
         (⋃ u ∈ Γ.V ∩ F, (μ (.vertex u)).vertexSet)))
    rw [image_inter Sum.inl_injective, image_union, image_iUnion₂, image_iUnion₂]
  · funext e x
    apply propext
    simp only [supportGraph, mapInl]
    constructor
    · rintro ⟨⟨v, rfl, hG⟩, ⟨s, hs, hsF, v', hv', hinc⟩ | ⟨u, hu, v', hv', hinc⟩⟩
      · cases Sum.inl_injective hv'
        exact ⟨v, rfl, hG, Or.inl ⟨s, hs, hsF, hinc⟩⟩
      · cases Sum.inl_injective hv'
        exact ⟨v, rfl, hG, Or.inr ⟨u, hu, hinc⟩⟩
    · rintro ⟨v, rfl, hG, ⟨s, hs, hsF, hinc⟩ | ⟨u, hu, hinc⟩⟩
      · exact ⟨⟨v, rfl, hG⟩, Or.inl ⟨s, hs, hsF, v, rfl, hinc⟩⟩
      · exact ⟨⟨v, rfl, hG⟩, Or.inr ⟨u, hu, v, rfl, hinc⟩⟩

/-- A pseudo-presentation moves along `Sum.inl` to a pseudo-presentation with the same drawing,
supports and depths. -/
lemma isPseudoPresentation_mapInl {S : Type w} [TopologicalSpace S]
    {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S}
    {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
    (h : IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q) :
    IsPseudoPresentation (mapInl G) Γ (mapInl Γ_sub) (Sum.inl ∘ ιV) ιE r F_star
      (fun x => mapInl (μ x)) q := by
  have hinter : ∀ A B : Set α, (Sum.inl '' A ∩ Sum.inl '' B : Set (InfVert α)) =
      Sum.inl '' (A ∩ B) := fun A B => (image_inter Sum.inl_injective).symm
  refine
    { is_surface := h.is_surface
      is_connected_surface := h.is_connected_surface
      is_proper_drawing := h.is_proper_drawing
      cuff_vertices_ge_two := h.cuff_vertices_ge_two
      drawing_subgraph := mapInl_le_iff.mpr h.drawing_subgraph
      drawing_iso :=
        { ιV_injOn := Sum.inl_injective.comp_injOn h.ιV_injOn
          ιV_image := by
            rw [image_comp, h.ιV_image]
            rfl
          ιE_injOn := h.ιE_injOn
          ιE_image := h.ιE_image
          inc_iff := fun e he u hu => by
            rw [← h.inc_iff e he u hu]
            exact ⟨fun ⟨v, hv, hinc⟩ => Sum.inl_injective hv ▸ hinc,
              fun hinc => ⟨ιV u, rfl, hinc⟩⟩ }
      supports_isSupport := h.supports_isSupport
      supports_disjoint := h.supports_disjoint
      bd_vertices_covered := h.bd_vertices_covered
      q_pos := h.q_pos
      μ_vertex := fun j u hu => ?_
      μ_space := fun j s hs hsF => mapInl_le_iff.mpr (h.μ_space j s hs hsF)
      p1_union_V := ?_
      p1_union_E := ?_
      p1_edge_disjoint_drawing := h.p1_edge_disjoint_drawing
      p1_edge_disjoint_spaces := h.p1_edge_disjoint_spaces
      p1_diff_cuff_disjoint := fun C₁ hC₁ C₂ hC₂ hne x₁ x₂ h₁ h₂ =>
        (disjoint_image_iff Sum.inl_injective).mpr (h.p1_diff_cuff_disjoint C₁ hC₁ C₂ hC₂ hne x₁ x₂ h₁ h₂)
      p2_space := fun j s hs u₁ u₂ hsF hends => ?_
      p3_order := fun C hC x₁ x₂ u₁ hu₁ u₂ hu₂ h₁ h₂ hord => by
        rw [← mapInl_inter, ← mapInl_union, mapInl_le_iff]
        exact h.p3_order C hC x₁ x₂ u₁ hu₁ u₂ hu₂ h₁ h₂ hord
      p4_inter_null := fun C hC => ?_ }
  · obtain ⟨hle, hE, hcard, hint⟩ := h.μ_vertex j u hu
    refine ⟨mapInl_le_iff.mpr hle, hE, (mapInl_ncard_vertexSet _).trans hcard, ?_⟩
    change Sum.inl '' _ ∩ Sum.inl '' _ = _
    rw [hinter, hint, image_singleton]
    rfl
  · simp only [supportGraph_mapInl]
    change Sum.inl '' G.vertexSet =
      Sum.inl '' Γ_sub.vertexSet ∪ ⋃ j, Sum.inl '' (supportGraph G Γ μ (F_star j)).vertexSet
    rw [h.p1_union_V, image_union, image_iUnion]
  · simp only [supportGraph_mapInl]
    exact h.p1_union_E
  · obtain ⟨hint, hle₁, hle₂, hpaths⟩ := h.p2_space j s hs u₁ u₂ hsF hends
    refine ⟨?_, mapInl_le_iff.mpr hle₁, mapInl_le_iff.mpr hle₂,
      hasDisjointPaths_mapInl _ hpaths⟩
    change Sum.inl '' _ ∩ Sum.inl '' _ = _
    rw [hinter, hint, image_pair]
    rfl
  · obtain ⟨u₀, hu₀⟩ : (Γ.V ∩ C).Nonempty :=
      nonempty_of_ncard_ne_zero (by have := h.cuff_vertices_ge_two C hC; omega)
    refine eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    simp only [mem_iInter] at hx
    obtain ⟨v, -, rfl⟩ := hx u₀ hu₀
    have hv : v ∈ ⋂ u ∈ Γ.V ∩ C, (μ (.vertex u)).vertexSet := by
      simp only [mem_iInter]
      intro u hu
      obtain ⟨v', hv', hvv'⟩ := hx u hu
      exact Sum.inl_injective hvv' ▸ hv'
    rw [h.p4_inter_null C hC] at hv
    exact hv

/-- **Graph Minors XXI, (8.4)** (page 36 of the preprint):
"For every surface $\Sigma$ and all integers $p, r \ge 0$ and $q \ge 1$, there exists
$\theta \ge 1$ such that, if a graph $G$ has a pseudo-presentation in $\Sigma$ of depth $\le q$ and
defect $\le r$ which surrounds a tangle of order $\ge \theta$, then $G$ has no vital
$p$-linkage."

The paper's induction splits vertices, and each split takes two new vertices. We move `G` into
`α ⊕ ULift ℕ` by `Sum.inl`, where new vertices exist, and apply `theorem_8_4_of_infinite` there. -/
theorem theorem_8_4_proof
    (S : Type) [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsSurface S) (p r q : ℕ) (hq : 1 ≤ q) :
    ∃ θ : ℕ, 1 ≤ θ ∧
      ∀ {α : Type u} {β : Type v} (G : Hypergraph α β), G.IsGraph →
        ∀ (Γ : Drawing S) (Γ_sub : Hypergraph α β) (ιV : S → α) (ιE : Set S → β)
          (r' : ℕ) (F_star : Fin r' → Set S)
          (μ : BoundaryUnit S → Hypergraph α β)
          (θ_G : ℕ) (𝒯 : Set (Hypergraph α β × Hypergraph α β)),
          r' ≤ r →
          PseudoPresentationHasDepthLe G Γ Γ_sub ιV ιE r' F_star μ q →
          θ ≤ θ_G →
          IsTangle G θ_G 𝒯 →
          PseudoPresentationSurroundsTangle Γ r' F_star μ 𝒯 →
          ¬ HasVitalPLinkage G p := by
  obtain ⟨θ, hθ_pos, h84⟩ := theorem_8_4_of_infinite.{u, v} S hS p r q hq
  refine ⟨θ, hθ_pos, ?_⟩
  intro α β G hG Γ Γ_sub ιV ιE r' F_star μ θ_G 𝒯 hr ⟨qv, hpp, hqv, hr0⟩ hθ h𝒯 hsurr hvit
  refine h84 (mapInl G) (mapInl_isGraph hG) Γ (mapInl Γ_sub) (Sum.inl ∘ ιV) ιE r' F_star
    (fun x => mapInl (μ x)) θ_G (Prod.map mapInl mapInl '' 𝒯) hr
    ⟨qv, isPseudoPresentation_mapInl hpp, hqv, hr0⟩ hθ (mapInl_isTangle h𝒯) ?_
    (mapInl_hasVitalPLinkage hvit)
  intro s hs hsF
  obtain ⟨B, hB⟩ := hsurr s hs hsF
  exact ⟨mapInl B, (μ (.space s), B), hB, rfl⟩

end GM21
end GraphMinor
