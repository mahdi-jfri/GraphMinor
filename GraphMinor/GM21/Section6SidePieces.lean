module

public import GraphMinor.GM21.Section6RestrictPres
public import GraphMinor.GM21.Section6SplitPresentation
import GraphMinor.GM21.Section6Angles
import GraphMinor.GM21.Section6SideSupports

/-!
# Graph Minors XXI, (6.3), claim (4): one side of a line, with supports cut in pieces

`Section6RestrictPres.lean` restricts a presentation to one side `Σ₁` of a line `F` when every set
`F_j* ∩ Σ₁` is a support. In claim (4) of the proof of (6.3) (page 29 of the preprint) this can
fail: when a support `F_j*` holds both ends of `F`, the set `F_j* ∩ Σ₁` can be two disjoint arcs.

This file allows any list of supports `K_1, …, K_{r₁}` of `Γ` inside `Σ₁`, with `K_i ⊆ F_{τ i}*`,
mutually disjoint, such that every vertex of `Γ` and every space of `Γ` in some `F_j* ∩ Σ₁` lies in
some `K_i` with `τ i = j`. The graph `G₁ = (Γ ∩ Σ₁) ∪ μ(bd(Σ) ∩ Σ₁)` is the same as before. Then
`Γ ∩ Σ₁`, the supports `K_i`, the graphs `μ(K_i)` and the restriction of `μ` satisfy all
conditions of a presentation except that the graphs `μ(K_i)` need not be vertex-disjoint
(`isOverlappingPresentation_side`). Two pieces of one `F_j*` can share vertices of `μ`. The proof is
the proof of `isPresentation_side` with `K_i` in place of `F_{σ i}* ∩ Σ₁`.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace Side

open Set Topology Function GraphMinor.Surface GraphMinor.GM21.Supports Hypergraph
open GraphMinor.GM21.Split

universe u v w

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S] [T2Space S]
  {Γ : Drawing S} {S₁ S₂ F : Set S} {a b : S}
  {G : Hypergraph α β} {Γ_sub : Hypergraph α β} {ιV : S → α} {ιE : Set S → β} {r : ℕ}
  {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β} {μ : BoundaryUnit S → Hypergraph α β}
  {q : Fin r → ℕ}
  (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) (h : IsSideOfLine Γ S₁ S₂ F a b)
  {r₁ : ℕ} {K : Fin r₁ → Set S} {τ : Fin r₁ → Fin r}
include hP

omit [T2Space S] hP in
/-- If every unit of `I` lies in some `K i` with `τ i = j`, then the vertices and edges of `μ(I)` are
vertices and edges of the graphs `μ(K i)`. -/
theorem supportGraph_subset_iUnion {j : Fin r} {I : Set S}
    (hKV : ∀ u ∈ Γ.V ∩ I, ∃ i, τ i = j ∧ u ∈ K i)
    (hKs : ∀ s ∈ drawingSpaces Γ, s ⊆ I → ∃ i, τ i = j ∧ s ⊆ K i) :
    (supportGraph G Γ μ I).vertexSet ⊆ ⋃ i, (supportGraph G Γ μ (K i)).vertexSet ∧
      (supportGraph G Γ μ I).edgeSet ⊆ ⋃ i, (supportGraph G Γ μ (K i)).edgeSet := by
  constructor
  · rintro x ⟨hxG, hx | hx⟩
    · obtain ⟨s, ⟨hs, hsI⟩, hxs⟩ := mem_iUnion₂.mp hx
      obtain ⟨i, -, hsK⟩ := hKs s hs hsI
      exact mem_iUnion.mpr ⟨i, hxG, Or.inl (mem_biUnion (x := s) ⟨hs, hsK⟩ hxs)⟩
    · obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hx
      obtain ⟨i, -, huK⟩ := hKV u hu
      exact mem_iUnion.mpr ⟨i, hxG, Or.inr (mem_biUnion (x := u) ⟨hu.1, huK⟩ hxu)⟩
  · rintro e ⟨heG, he | he⟩
    · obtain ⟨s, ⟨hs, hsI⟩, hes⟩ := mem_iUnion₂.mp he
      obtain ⟨i, -, hsK⟩ := hKs s hs hsI
      exact mem_iUnion.mpr ⟨i, heG, Or.inl (mem_biUnion (x := s) ⟨hs, hsK⟩ hes)⟩
    · obtain ⟨u, hu, heu⟩ := mem_iUnion₂.mp he
      obtain ⟨i, -, huK⟩ := hKV u hu
      exact mem_iUnion.mpr ⟨i, heG, Or.inr (mem_biUnion (x := u) ⟨hu.1, huK⟩ heu)⟩

include h

/-- **One side of a line, with supports cut in pieces** (Graph Minors XXI, proof of (6.3),
claim (4), page 29 of the preprint: "there is a presentation of $G_i$ in $\Sigma_i$ of depth $\le q$
... using $\Gamma_i$"). Let `K_1, …, K_{r₁}` be mutually disjoint supports of `Γ` with
`K_i ⊆ F_{τ i}* ∩ S₁`, such that every vertex of `Γ` and every space of `Γ` in `F_j* ∩ S₁` lies in
some `K_i` with `τ i = j`. Then `Γ ∩ S₁`, the supports `K_i`, the graphs `μ(K_i)` and the
restriction of `μ` satisfy all conditions of a presentation of `G₁` in `S₁` except the disjointness
of the graphs `μ(K_i)`. -/
theorem isOverlappingPresentation_side (hconn : ConnectedSpace S₁)
    (hKF : ∀ i, K i ⊆ F_star (τ i) ∩ S₁) (hKsup : ∀ i, IsSupportOfDrawing Γ (K i))
    (hKdisj : Pairwise (fun i i' => Disjoint (K i) (K i')))
    (hKV : ∀ j, ∀ u ∈ Γ.V ∩ (F_star j ∩ S₁), ∃ i, τ i = j ∧ u ∈ K i)
    (hKs : ∀ j, ∀ s ∈ drawingSpaces Γ, s ⊆ F_star j ∩ S₁ → ∃ i, τ i = j ∧ s ⊆ K i) :
    IsOverlappingPresentation (sideGraph G Γ Γ_sub ιV ιE F_star μ S₁)
      (sideDrawing Γ h.isClosed_left) (sideSub Γ Γ_sub ιV ιE S₁) (ιV ∘ Subtype.val)
      (fun e => ιE (Subtype.val '' e)) r₁ (fun i => Subtype.val ⁻¹' K i)
      (fun i => supportGraph G Γ μ (K i)) (sideMu μ S₁) (q ∘ τ) := by
  have hS := hP.is_surface
  have hFbd : ∀ j, F_star j ⊆ bd S := fun j => subset_bd_of_isSupportOfDrawing
    (hP.supports_isSupport j)
  have hKS₁ : ∀ i, K i ⊆ S₁ := fun i => (hKF i).trans inter_subset_right
  have hKFj : ∀ i, K i ⊆ F_star (τ i) := fun i => (hKF i).trans inter_subset_left
  have hKbd : ∀ i, K i ⊆ bd S := fun i => (hKFj i).trans (hFbd (τ i))
  have hKcl : ∀ i, IsClosed (K i) := fun i => isClosed_of_isSupportOfDrawing hS (hKsup i)
  -- `μ(K i) ≤ μ(F_{τ i}* ∩ S₁)`.
  have hKle : ∀ i, supportGraph G Γ μ (K i) ≤ supportGraph G Γ μ (F_star (τ i) ∩ S₁) :=
    fun i => supportGraph_mono hP (τ i) inter_subset_left (hKF i)
  have hKleH : ∀ i, supportGraph G Γ μ (K i) ≤ H (τ i) := fun i =>
    (hKle i).trans (supportGraph_inter_le_H hP (τ i))
  -- The union over all `j` of `μ(F_j* ∩ S₁)` is the union of the graphs `μ(K i)`.
  have hU := fun j => supportGraph_subset_iUnion (G := G) (μ := μ) (j := j) (I := F_star j ∩ S₁)
    (hKV j) (hKs j)
  have hUV : (⋃ j, (supportGraph G Γ μ (F_star j ∩ S₁)).vertexSet) =
      ⋃ i, (supportGraph G Γ μ (K i)).vertexSet := by
    apply Subset.antisymm
    · exact iUnion_subset fun j => (hU j).1
    · exact iUnion_subset fun i => (hKle i).vertexSet_subset.trans
        (subset_iUnion (fun j => (supportGraph G Γ μ (F_star j ∩ S₁)).vertexSet) (τ i))
  have hUE : (⋃ j, (supportGraph G Γ μ (F_star j ∩ S₁)).edgeSet) =
      ⋃ i, (supportGraph G Γ μ (K i)).edgeSet := by
    apply Subset.antisymm
    · exact iUnion_subset fun j => (hU j).2
    · exact iUnion_subset fun i => (hKle i).edgeSet_subset.trans
        (subset_iUnion (fun j => (supportGraph G Γ μ (F_star j ∩ S₁)).edgeSet) (τ i))
  have hsub := sideSub_le hP h.isClosed_left
  exact {
    is_surface := h.surface_left
    is_connected_surface := hconn
    is_proper_drawing := h.isProper_sideDrawing hS hP.is_proper_drawing
    cuff_vertices_ge_two := two_le_ncard_sideDrawing_cuff hS h.surface_left h.isClosed_left
      h.isClosed_right h.union_eq h.inter_eq h.proper.1 h.inter_bd h.left_mem h.right_mem
      hP.cuff_vertices_ge_two
    drawing_subgraph := sideSub_le_sideGraph hP h.isClosed_left
    drawing_iso := isDrawingIso_side hP h
    supports_isSupport := by
      intro i
      obtain ⟨u, w, huw⟩ := hKsup i
      have hends := ends_mem_of_supportHasEnds huw
      exact ⟨_, _, supportHasEnds_preimage (u := ⟨u, hKS₁ i hends.1⟩)
        (v := ⟨w, hKS₁ i hends.2.1⟩) hS h.surface_left h.surface_right h.union_eq h.inter_eq
        h.proper.1 h.isClosed_left huw (hKS₁ i)⟩
    supports_disjoint := fun i i' hii' => (hKdisj hii').preimage _
    bd_vertices_covered := by
      rintro x ⟨hxV, hxbd⟩
      rw [sideDrawing_V] at hxV
      have hxbd' : x.1 ∈ bd S := by
        rcases (h.mem_bd_iff hS).mp hxbd with hxF | hx
        · exact h.mem_bd_of_mem_V hxF hxV
        · exact hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp (hP.bd_vertices_covered ⟨hxV, hxbd'⟩)
      obtain ⟨i, -, hi⟩ := hKV j x.1 ⟨hxV, hj, x.2⟩
      exact mem_iUnion.mpr ⟨i, hi⟩
    v1_sub := fun i => (hKle i).trans (supportGraph_inter_le_sideGraph hP (τ i))
    v1_union_V := by
      rw [vertexSet_sideGraph hP h.isClosed_left, hUV, Set.union_comm]
    v1_union_E := by
      rw [edgeSet_sideGraph hP h.isClosed_left, hUE, Set.union_comm]
    v1_inter_V := by
      intro i
      have hR : (ιV ∘ Subtype.val) '' ((sideDrawing Γ h.isClosed_left).V ∩
          Subtype.val ⁻¹' K i) = ιV '' (Γ.V ∩ K i) := by
        rw [sideDrawing_V, ← preimage_inter, image_comp, Subtype.image_preimage_coe]
        congr 1
        ext x
        have hk : x ∈ K i → x ∈ S₁ := fun hx => hKS₁ i hx
        simp only [mem_inter_iff]
        tauto
      rw [hR, vertexSet_sideSub (S₁ := S₁) hP]
      apply Subset.antisymm
      · rintro x ⟨hx, hxΓ⟩
        have hxΓ' : x ∈ Γ_sub.vertexSet := by
          rw [← hP.ιV_image]; exact image_mono inter_subset_left hxΓ
        exact supportGraph_vertexSet_inter_subset hP (τ i) (hKFj i) (hKcl i) ⟨hx, hxΓ'⟩
      · rintro _ ⟨x, ⟨hxV, hxK⟩, rfl⟩
        exact ⟨(μ_vertex_le_supportGraph_of_subset hP (τ i) (hKFj i)
          ⟨hxV, hxK⟩).vertexSet_subset (ιV_mem_μ_vertex hP (τ i) ⟨hxV, hKFj i hxK⟩),
          x, ⟨hxV, hKS₁ i hxK⟩, rfl⟩
    v1_inter_E := fun i => (hP.v1_inter_E (τ i)).mono (hKleH i).edgeSet_subset
      hsub.edgeSet_subset
    q_pos := fun i => hP.q_pos (τ i)
    μ_vertex_sub := by
      rintro i x ⟨hxV, hxK⟩
      rw [sideDrawing_V] at hxV
      have hx' : x.1 ∈ Γ.V ∩ F_star (τ i) := ⟨hxV, hKFj i hxK⟩
      obtain ⟨-, he, hcard, hint⟩ := hP.μ_vertex_sub (τ i) x.1 hx'
      refine ⟨μ_vertex_le_supportGraph_of_subset hP (τ i) (hKFj i) ⟨hxV, hxK⟩,
        he, hcard, ?_⟩
      rw [vertexSet_sideSub (S₁ := S₁) hP, comp_apply]
      apply Subset.antisymm
      · rintro y ⟨hy, hyΓ⟩
        rw [← hint]
        exact ⟨hy, by rw [← hP.ιV_image]; exact image_mono inter_subset_left hyΓ⟩
      · rintro y rfl
        exact ⟨ιV_mem_μ_vertex hP (τ i) hx', x.1, ⟨hxV, x.2⟩, rfl⟩
    μ_space_sub := by
      intro i s₁ hs₁ hs₁K
      have hbd : s₁ ⊆ Subtype.val ⁻¹' bd S := hs₁K.trans (preimage_mono (hKbd i))
      exact μ_space_le_supportGraph_of_subset hP (τ i) (hKFj i)
        (h.image_mem_spaces hS hs₁ hbd) (image_subset_iff.mpr hs₁K)
    v2_eq := by
      intro i
      rw [h.supportGraph_side hS _ μ (hKS₁ i) (hKbd i)]
      exact (supportGraph_eq_of_le' μ (sideGraph_le hP h.isClosed_left)
        ((hKle i).trans (supportGraph_inter_le_sideGraph hP (τ i)))).symm
    v3_space := by
      intro i s₁ hs₁ u₁ u₂ hs₁K hends
      have hbd : s₁ ⊆ Subtype.val ⁻¹' bd S := hs₁K.trans (preimage_mono (hKbd i))
      have hends' := h.spaceHasEnds_image hS hends hbd
      obtain ⟨hint, h1, h2, hpaths⟩ := hP.v3_space (τ i) _ hends'.1 u₁.1 u₂.1
        ((image_subset_iff.mpr hs₁K).trans (hKFj i)) hends'
      refine ⟨?_, h1, h2, hpaths⟩
      rw [sideMu_space, vertexSet_sideSub (S₁ := S₁) hP, comp_apply, comp_apply]
      apply Subset.antisymm
      · rintro y ⟨hy, hyΓ⟩
        rw [← hint]
        exact ⟨hy, by rw [← hP.ιV_image]; exact image_mono inter_subset_left hyΓ⟩
      · intro y hy
        have hy' : y ∈ (μ (.space (Subtype.val '' s₁))).vertexSet ∩ Γ_sub.vertexSet := by
          rw [hint]; exact hy
        refine ⟨hy'.1, ?_⟩
        rcases hy with rfl | rfl
        · exact ⟨u₁.1, ⟨hends'.2.1.1, u₁.2⟩, rfl⟩
        · exact ⟨u₂.1, ⟨hends'.2.2.1.1, u₂.2⟩, rfl⟩
    v4_between := by
      intro i s₁ s₂ x hbtw
      have hK : Subtype.val ⁻¹' K i ⊆ (Subtype.val ⁻¹' bd S : Set S₁) :=
        preimage_mono (hKbd i)
      have h1 := liesBetweenInSupport_image hS h.isClosed_left h.isClosed_right h.union_eq
        h.inter_eq h.isClosed_line h.inter_bd h.left_mem h.right_mem hbtw hK
      have h2 := liesBetweenInSupport_mono hS hP.cuff_vertices_ge_two
        (hP.supports_isSupport (τ i)) ((image_preimage_subset _ _).trans (hKFj i)) h1
      exact hP.v4_between (τ i) _ _ _ h2 }

end Side
end GM21
end GraphMinor
