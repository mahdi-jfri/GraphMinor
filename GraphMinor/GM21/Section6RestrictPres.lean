module

public import GraphMinor.GM21.Section6Restrict
import GraphMinor.GM21.Section6Angles
import GraphMinor.GM12.Section3SubspaceArcs
import GraphMinor.GM12.Section3SubspaceDrawing
import GraphMinor.GM10.TangleLemmas

/-!
# Graph Minors XXI, Section 6: the presentation of one side of a line

Let `Γ, F_1^*, …, F_r^*, H_1, …, H_r, μ` be a presentation of `G` in `Σ`, and let `Σ₁` be a side of
a proper line `F` (`IsSideOfLine`). This file proves that `Γ ∩ Σ₁`, the supports `F_j^* ∩ Σ₁`, the
graphs `μ(F_j^* ∩ Σ₁)` and the restriction of `μ` form a presentation of
`G₁ = (Γ ∩ Σ₁) ∪ μ(bd(Σ) ∩ Σ₁)` in `Σ₁` (`isPresentation_side`), of depth at most the depth of the
given one (`presentationHasDepthLe_side`). This is the presentation described in the proofs of
(6.5), (6.6), (6.7) and of claim (4) of (6.3) in *Graph Minors XXI* (pages 25–29 of the preprint).

The supports of the new presentation are the sets `F_j^* ∩ Σ₁` that are not empty, listed by an
injective map `σ`. We ask that each of them be a support of `Γ`. Every field is checked by moving
between `Σ₁` and `Σ`: the spaces of `Γ ∩ Σ₁` inside `bd(Σ)` are the spaces of `Γ` inside `Σ₁`
(`Section6Side.lean`), and betweenness in a support of `Γ ∩ Σ₁` gives betweenness in the support
of `Γ` that contains it (`Section6SideSupports.lean`). The key step is that
`μ₁(F_j^* ∩ Σ₁)`, computed in `Σ₁`, is the graph `μ(F_j^* ∩ Σ₁)` computed in `Σ`
(`supportGraph_side`).
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace Side

open Set Topology Function GraphMinor.Surface GraphMinor.GM21.Supports Hypergraph

universe u v w

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]

omit [TopologicalSpace S] in
@[simp] theorem sideMu_vertex (μ : BoundaryUnit S → Hypergraph α β) (S₁ : Set S) (x : S₁) :
    sideMu μ S₁ (.vertex x) = μ (.vertex x.1) := rfl

omit [TopologicalSpace S] in
@[simp] theorem sideMu_space (μ : BoundaryUnit S → Hypergraph α β) (S₁ : Set S) (s : Set S₁) :
    sideMu μ S₁ (.space s) = μ (.space (Subtype.val '' s)) := rfl

omit [TopologicalSpace S] in
theorem preimage_inter_side (S₁ X : Set S) :
    (Subtype.val : S₁ → S) ⁻¹' (X ∩ S₁) = Subtype.val ⁻¹' X := by
  ext x
  simp only [mem_preimage, mem_inter_iff, Subtype.coe_prop, and_true]

/-- A space of a drawing is not empty. -/
theorem nonempty_of_mem_drawingSpaces {T : Type*} [TopologicalSpace T] {Γ : Drawing T}
    {s : Set T} (hs : s ∈ drawingSpaces Γ) : s.Nonempty := by
  obtain ⟨x, hx, rfl⟩ := hs
  exact ⟨x, mem_connectedComponentIn hx⟩

/-- `μ` of the empty set has no vertex and no edge. -/
theorem supportGraph_of_eq_empty (G : Hypergraph α β) (Γ : Drawing S)
    (μ : BoundaryUnit S → Hypergraph α β) {I : Set S} (hI : I = ∅) :
    (supportGraph G Γ μ I).vertexSet = ∅ ∧ (supportGraph G Γ μ I).edgeSet = ∅ := by
  subst hI
  constructor
  · ext v
    simp only [supportGraph, mem_empty_iff_false, iff_false]
    rintro ⟨-, hv | hv⟩
    · obtain ⟨s, ⟨hs, hs0⟩, -⟩ := mem_iUnion₂.mp hv
      obtain ⟨x, hx⟩ := nonempty_of_mem_drawingSpaces hs
      exact hs0 hx
    · obtain ⟨u, hu, -⟩ := mem_iUnion₂.mp hv
      exact hu.2
  · ext e
    simp only [supportGraph, mem_empty_iff_false, iff_false]
    rintro ⟨-, he | he⟩
    · obtain ⟨s, ⟨hs, hs0⟩, -⟩ := mem_iUnion₂.mp he
      obtain ⟨x, hx⟩ := nonempty_of_mem_drawingSpaces hs
      exact hs0 hx
    · obtain ⟨u, hu, -⟩ := mem_iUnion₂.mp he
      exact hu.2

/-- Two graphs `μ(K)` and `μ'(K')`, for drawings in two spaces, are equal when the spaces and the
vertices in `K` and `K'` carry the same graphs. -/
theorem supportGraph_eq_of_iff {T : Type*} [TopologicalSpace T] (G : Hypergraph α β)
    {Γ : Drawing S} {Γ' : Drawing T} {μ : BoundaryUnit S → Hypergraph α β}
    {μ' : BoundaryUnit T → Hypergraph α β} {K : Set S} {K' : Set T}
    (hsp : ∀ P : Hypergraph α β → Prop,
      (∃ s ∈ drawingSpaces Γ', s ⊆ K' ∧ P (μ' (.space s))) ↔
        (∃ s ∈ drawingSpaces Γ, s ⊆ K ∧ P (μ (.space s))))
    (hv : ∀ P : Hypergraph α β → Prop,
      (∃ u ∈ Γ'.V ∩ K', P (μ' (.vertex u))) ↔ (∃ u ∈ Γ.V ∩ K, P (μ (.vertex u)))) :
    supportGraph G Γ' μ' K' = supportGraph G Γ μ K := by
  have hV : ∀ P : Hypergraph α β → Prop,
      ((∃ s ∈ drawingSpaces Γ', s ⊆ K' ∧ P (μ' (.space s))) ∨
        (∃ u ∈ Γ'.V ∩ K', P (μ' (.vertex u)))) ↔
      ((∃ s ∈ drawingSpaces Γ, s ⊆ K ∧ P (μ (.space s))) ∨
        (∃ u ∈ Γ.V ∩ K, P (μ (.vertex u)))) := fun P => or_congr (hsp P) (hv P)
  apply Hypergraph.ext
  · ext x
    simp only [supportGraph, mem_inter_iff, mem_union, mem_iUnion₂, mem_ofPred_eq, exists_prop,
      and_assoc]
    have hk := hV (fun A => x ∈ A.vertexSet)
    simp only [mem_inter_iff, and_assoc] at hk
    exact and_congr_right fun _ => hk
  · ext e
    simp only [supportGraph, mem_inter_iff, mem_union, mem_iUnion₂, mem_ofPred_eq, exists_prop,
      and_assoc]
    have hk := hV (fun A => e ∈ A.edgeSet)
    simp only [mem_inter_iff, and_assoc] at hk
    exact and_congr_right fun _ => hk
  · funext e x
    simp only [supportGraph]
    exact propext (and_congr_right fun _ => hV (fun A => A.Inc e x))

/-- If `G' ≤ G` contains `μ(F)` computed in `G`, then `μ(F)` computed in `G'` is the same graph. -/
theorem supportGraph_eq_of_le' {Γ : Drawing S} {G G' : Hypergraph α β}
    (μ : BoundaryUnit S → Hypergraph α β) {F : Set S} (hG' : G' ≤ G)
    (hsub : supportGraph G Γ μ F ≤ G') :
    supportGraph G' Γ μ F = supportGraph G Γ μ F := by
  apply Hypergraph.ext
  · ext x
    simp only [supportGraph, mem_inter_iff]
    exact ⟨fun h => ⟨hG'.vertexSet_subset h.1, h.2⟩,
      fun h => ⟨hsub.vertexSet_subset h, h.2⟩⟩
  · ext e
    simp only [supportGraph, mem_inter_iff]
    exact ⟨fun h => ⟨hG'.edgeSet_subset h.1, h.2⟩,
      fun h => ⟨hsub.edgeSet_subset h, h.2⟩⟩
  · funext e x
    apply propext
    simp only [supportGraph]
    constructor
    · rintro ⟨hinc, hrest⟩
      exact ⟨GM10.inc_of_le hG' hinc, hrest⟩
    · rintro ⟨hinc, hrest⟩
      have hinc' : (supportGraph G Γ μ F).Inc e x := ⟨hinc, hrest⟩
      exact ⟨GM10.inc_of_le hsub hinc', hrest⟩

/-- `μ(s) ≤ μ(I)` for a space `s ⊆ I ⊆ F_j*`. -/
theorem μ_space_le_supportGraph_of_subset {G : Hypergraph α β} {Γ : Drawing S}
    {Γ_sub : Hypergraph α β} {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S}
    {H : Fin r → Hypergraph α β} {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
    (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) (j : Fin r) {I : Set S}
    (hI : I ⊆ F_star j) {s : Set S} (hs : s ∈ drawingSpaces Γ) (hsI : s ⊆ I) :
    μ (.space s) ≤ supportGraph G Γ μ I := by
  have hle := μ_space_le hP j hs (hsI.trans hI)
  rw [GM10.le_iff_of_le hle (supportGraph_le hP j hI)]
  exact ⟨fun x hx => ⟨hle.vertexSet_subset hx, Or.inl (mem_biUnion (x := s) ⟨hs, hsI⟩ hx)⟩,
    fun e he => ⟨hle.edgeSet_subset he, Or.inl (mem_biUnion (x := s) ⟨hs, hsI⟩ he)⟩⟩

variable [T2Space S] {Γ : Drawing S} {S₁ S₂ F : Set S} {a b : S}

namespace IsSideOfLine

variable (h : IsSideOfLine Γ S₁ S₂ F a b)
include h

/-- The spaces of `Γ ∩ S₁` inside `bd(S)` are spaces of `Γ`. -/
theorem image_mem_spaces (hS : IsSurface S) {s₁ : Set S₁}
    (hs₁ : s₁ ∈ drawingSpaces (sideDrawing Γ h.isClosed_left))
    (hbd : s₁ ⊆ Subtype.val ⁻¹' bd S) : Subtype.val '' s₁ ∈ drawingSpaces Γ :=
  image_mem_drawingSpaces hS h.isClosed_left h.isClosed_right h.union_eq h.inter_eq
    h.isClosed_line h.inter_bd h.left_mem h.right_mem hs₁ hbd

/-- The spaces of `Γ` inside `S₁` are spaces of `Γ ∩ S₁`. -/
theorem preimage_mem_spaces (hS : IsSurface S) {s : Set S} (hs : s ∈ drawingSpaces Γ)
    (hsS₁ : s ⊆ S₁) :
    (Subtype.val : S₁ → S) ⁻¹' s ∈ drawingSpaces (sideDrawing Γ h.isClosed_left) :=
  preimage_mem_drawingSpaces hS h.isClosed_left h.isClosed_right h.union_eq h.inter_eq
    h.isClosed_line h.inter_bd h.left_mem h.right_mem hs hsS₁

/-- The boundary of `S₁` is `F ∪ (bd(S) ∩ S₁)`. -/
theorem mem_bd_iff (hS : IsSurface S) {x : S₁} : x ∈ bd S₁ ↔ x.1 ∈ F ∪ bd S :=
  mem_bd_side_iff' hS h.surface_left h.surface_right h.union_eq h.inter_eq h.proper.1

/-- **`μ(K)` read in `S₁`.** For `K ⊆ S₁ ∩ bd(S)`, the graph `μ₁(K)` computed from `Γ ∩ S₁` and
the restriction `μ₁` of `μ` is the graph `μ(K)` computed from `Γ` and `μ`. The spaces of `Γ ∩ S₁`
inside `K` are the spaces of `Γ` inside `K`, and the vertices of `Γ ∩ S₁` in `K` are the vertices
of `Γ` in `K`. -/
theorem supportGraph_side (hS : IsSurface S) (G : Hypergraph α β)
    (μ : BoundaryUnit S → Hypergraph α β) {K : Set S} (hKS₁ : K ⊆ S₁) (hKbd : K ⊆ bd S) :
    supportGraph G (sideDrawing Γ h.isClosed_left) (sideMu μ S₁) (Subtype.val ⁻¹' K) =
      supportGraph G Γ μ K := by
  apply supportGraph_eq_of_iff
  · intro P
    constructor
    · rintro ⟨s₁, hs₁, hs₁K, hP⟩
      exact ⟨_, h.image_mem_spaces hS hs₁ (hs₁K.trans (preimage_mono hKbd)),
        image_subset_iff.mpr hs₁K, hP⟩
    · rintro ⟨s, hs, hsK, hP⟩
      refine ⟨_, h.preimage_mem_spaces hS hs (hsK.trans hKS₁), preimage_mono hsK, ?_⟩
      rw [sideMu_space, Subtype.image_preimage_coe, inter_eq_right.mpr (hsK.trans hKS₁)]
      exact hP
  · intro P
    constructor
    · rintro ⟨x, ⟨hxV, hxK⟩, hP⟩
      rw [sideDrawing_V] at hxV
      exact ⟨x.1, ⟨hxV, hxK⟩, hP⟩
    · rintro ⟨x, ⟨hxV, hxK⟩, hP⟩
      refine ⟨⟨x, hKS₁ hxK⟩, ⟨?_, hxK⟩, hP⟩
      rw [sideDrawing_V]
      exact hxV

/-- The drawing `Γ ∩ S₁` is proper in `S₁`: a point of it in `bd(S₁)` lies in `bd(S)` or in `F`,
and in both cases it is a vertex. -/
theorem isProper_sideDrawing (hS : IsSurface S) (hΓ : Γ.IsProper) :
    (sideDrawing Γ h.isClosed_left).IsProper := by
  rintro x ⟨hxbd, hxU⟩
  have hxU' : x.1 ∈ Γ.U := by
    rw [sideDrawing, GM12.drawingInSubspace_U] at hxU
    rcases hxU with (⟨⟨hx, -⟩, -⟩ | hx) | hx
    · exact Γ.V_subset_U hx
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      exact Γ.V_subset_U hxe.2
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      exact Γ.closure_subset_U he.2 hxe
  rw [sideDrawing_V]
  rcases (h.mem_bd_iff hS).mp hxbd with hxF | hxbd'
  · rcases h.inter_U ⟨hxF, hxU'⟩ with hx | hx
    · rw [mem_preimage, hx]; exact h.left_mem
    · rw [mem_preimage, hx]; exact h.right_mem
  · exact hΓ ⟨hxbd', hxU'⟩

/-- The ends of a space of `Γ ∩ S₁` inside `bd(S)` are the ends of the corresponding space of
`Γ`. -/
theorem spaceHasEnds_image (hS : IsSurface S) {s₁ : Set S₁} {u₁ u₂ : S₁}
    (hs : SpaceHasEnds (sideDrawing Γ h.isClosed_left) s₁ u₁ u₂)
    (hbd : s₁ ⊆ Subtype.val ⁻¹' bd S) :
    SpaceHasEnds Γ (Subtype.val '' s₁) u₁.1 u₂.1 := by
  obtain ⟨hsp, ⟨hu₁V, -⟩, ⟨hu₂V, -⟩, hne, hline, hcl⟩ := hs
  rw [sideDrawing_V] at hu₁V hu₂V
  have hbdcl : IsClosed (Subtype.val ⁻¹' bd S : Set S₁) :=
    (cuff_statement.{w} S hS).1.preimage continuous_subtype_val
  have hclbd : closure s₁ ⊆ Subtype.val ⁻¹' bd S := closure_minimal hbd hbdcl
  have hu₁ : u₁ ∈ closure s₁ := by rw [hcl]; exact Or.inr (Or.inl rfl)
  have hu₂ : u₂ ∈ closure s₁ := by rw [hcl]; exact Or.inr (Or.inr rfl)
  have himg : Subtype.val '' (s₁ ∪ {u₁, u₂}) = Subtype.val '' s₁ ∪ {u₁.1, u₂.1} := by
    rw [image_union, image_pair]
  refine ⟨h.image_mem_spaces hS hsp hbd, ⟨hu₁V, hclbd hu₁⟩, ⟨hu₂V, hclbd hu₂⟩,
    fun h' => hne (Subtype.ext h'), ?_, ?_⟩
  · rw [← himg]
    exact GM12.isLineWithEnds_subtype_image hline
  · rw [← himg, ← hcl, h.isClosed_left.isClosedEmbedding_subtypeVal.closure_image_eq]

end IsSideOfLine

/-! ## The presentation of one side -/

section Presentation

variable {G : Hypergraph α β} {Γ_sub : Hypergraph α β} {ιV : S → α} {ιE : Set S → β} {r : ℕ}
  {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β} {μ : BoundaryUnit S → Hypergraph α β}
  {q : Fin r → ℕ}
  (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) (h : IsSideOfLine Γ S₁ S₂ F a b)
  {r₁ : ℕ} {σ : Fin r₁ → Fin r}
include hP h

omit [T2Space S] h in
theorem vertexSet_sideSub :
    (sideSub Γ Γ_sub ιV ιE S₁).vertexSet = ιV '' (Γ.V ∩ S₁) := by
  refine inter_eq_left.mpr ?_
  rw [← hP.ιV_image]
  exact image_mono inter_subset_left

omit [T2Space S] h in
theorem edgeSet_sideSub :
    (sideSub Γ Γ_sub ιV ιE S₁).edgeSet = ιE '' {e | e ∈ Γ.E ∧ e ⊆ S₁} := by
  refine inter_eq_left.mpr ?_
  rw [← hP.ιE_image]
  exact image_mono fun e he => he.1

/-- `(ιV, ιE)` maps `Γ ∩ S₁` onto the subgraph `sideSub` of `Γ`. -/
theorem isDrawingIso_side :
    IsDrawingIso (sideDrawing Γ h.isClosed_left) (sideSub Γ Γ_sub ιV ιE S₁)
      (ιV ∘ Subtype.val) (fun e => ιE (Subtype.val '' e)) where
  ιV_injOn := by
    rw [sideDrawing_V]
    exact hP.ιV_injOn.comp Subtype.val_injective.injOn fun x hx => hx
  ιV_image := by
    rw [sideDrawing_V, image_comp, Subtype.image_preimage_coe, Set.inter_comm,
      vertexSet_sideSub (S₁ := S₁) hP]
  ιE_injOn := by
    rw [sideDrawing_E]
    rintro _ ⟨e, ⟨he, heS⟩, rfl⟩ _ ⟨e', ⟨he', he'S⟩, rfl⟩ hee
    simp only [Subtype.image_preimage_coe, inter_eq_right.mpr heS,
      inter_eq_right.mpr he'S] at hee
    rw [hP.ιE_injOn he he' hee]
  ιE_image := by
    rw [sideDrawing_E, edgeSet_sideSub (S₁ := S₁) hP, image_image]
    apply image_congr
    rintro e ⟨-, heS⟩
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr heS]
  inc_iff := by
    rw [sideDrawing_E, sideDrawing_V]
    rintro _ ⟨e, ⟨he, heS⟩, rfl⟩ x hxV
    simp only [Subtype.image_preimage_coe, inter_eq_right.mpr heS, comp_apply]
    rw [GM12.closure_subtype_preimage heS, mem_preimage, ← hP.inc_iff e he x.1 hxV]
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, ⟨e, ⟨he, heS⟩, rfl⟩, ⟨x.1, ⟨hxV, x.2⟩, rfl⟩⟩⟩

omit [T2Space S] h in
/-- `μ(F_j* ∩ S₁) ≤ H_j`. -/
theorem supportGraph_inter_le_H (j : Fin r) : supportGraph G Γ μ (F_star j ∩ S₁) ≤ H j := by
  rw [hP.v2_eq j]
  exact supportGraph_mono hP j subset_rfl inter_subset_left

/-- **Restricting a presentation to one side of a line** (Graph Minors XXI, proofs of (6.5),
(6.6), (6.7) and of claim (4) of (6.3), pages 25–29 of the preprint). Let `σ` list the indices `j`
with `F_j* ∩ S₁` not empty, each of these sets being a support of `Γ`. Then `Γ ∩ S₁`, the supports
`F_{σ i}* ∩ S₁`, the graphs `μ(F_{σ i}* ∩ S₁)` and the restriction of `μ` form a presentation of
`G₁ = (Γ ∩ S₁) ∪ μ(bd(S) ∩ S₁)` in `S₁`. -/
theorem isPresentation_side (hconn : ConnectedSpace S₁) (hσ : Injective σ)
    (hσsup : ∀ i, IsSupportOfDrawing Γ (F_star (σ i) ∩ S₁))
    (hσall : ∀ j, (F_star j ∩ S₁).Nonempty → ∃ i, σ i = j) :
    IsPresentation (sideGraph G Γ Γ_sub ιV ιE F_star μ S₁) (sideDrawing Γ h.isClosed_left)
      (sideSub Γ Γ_sub ιV ιE S₁) (ιV ∘ Subtype.val) (fun e => ιE (Subtype.val '' e)) r₁
      (fun i => Subtype.val ⁻¹' F_star (σ i)) (fun i => supportGraph G Γ μ (F_star (σ i) ∩ S₁))
      (sideMu μ S₁) (q ∘ σ) := by
  have hS := hP.is_surface
  have hFbd : ∀ j, F_star j ⊆ bd S := fun j => subset_bd_of_isSupportOfDrawing
    (hP.supports_isSupport j)
  have hKbd : ∀ j, F_star j ∩ S₁ ⊆ bd S := fun j => inter_subset_left.trans (hFbd j)
  -- The union over all `j` of `μ(F_j* ∩ S₁)` is the union over the listed ones.
  have hUV : (⋃ j, (supportGraph G Γ μ (F_star j ∩ S₁)).vertexSet) =
      ⋃ i, (supportGraph G Γ μ (F_star (σ i) ∩ S₁)).vertexSet := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      by_cases hne : (F_star j ∩ S₁).Nonempty
      · obtain ⟨i, rfl⟩ := hσall j hne
        exact mem_iUnion.mpr ⟨i, hj⟩
      · rw [(supportGraph_of_eq_empty G Γ μ (not_nonempty_iff_eq_empty.mp hne)).1] at hj
        exact hj.elim
    · exact iUnion_subset fun i => subset_iUnion_of_subset (σ i) subset_rfl
  have hUE : (⋃ j, (supportGraph G Γ μ (F_star j ∩ S₁)).edgeSet) =
      ⋃ i, (supportGraph G Γ μ (F_star (σ i) ∩ S₁)).edgeSet := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      by_cases hne : (F_star j ∩ S₁).Nonempty
      · obtain ⟨i, rfl⟩ := hσall j hne
        exact mem_iUnion.mpr ⟨i, hj⟩
      · rw [(supportGraph_of_eq_empty G Γ μ (not_nonempty_iff_eq_empty.mp hne)).2] at hj
        exact hj.elim
    · exact iUnion_subset fun i => subset_iUnion_of_subset (σ i) subset_rfl
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
      obtain ⟨u, w, huw⟩ := hσsup i
      have hends := ends_mem_of_supportHasEnds huw
      have hK : F_star (σ i) ∩ S₁ ⊆ S₁ := inter_subset_right
      have := supportHasEnds_preimage (u := ⟨u, hK hends.1⟩) (v := ⟨w, hK hends.2.1⟩) hS
        h.surface_left h.surface_right h.union_eq h.inter_eq h.proper.1 h.isClosed_left huw hK
      rw [preimage_inter_side] at this
      exact ⟨_, _, this⟩
    supports_disjoint := by
      intro i i' hii'
      exact ((hP.supports_disjoint (hσ.ne hii')).preimage _)
    bd_vertices_covered := by
      rintro x ⟨hxV, hxbd⟩
      rw [sideDrawing_V] at hxV
      have hxbd' : x.1 ∈ bd S := by
        rcases (h.mem_bd_iff hS).mp hxbd with hxF | hx
        · exact h.mem_bd_of_mem_V hxF hxV
        · exact hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp (hP.bd_vertices_covered ⟨hxV, hxbd'⟩)
      obtain ⟨i, rfl⟩ := hσall j ⟨x.1, hj, x.2⟩
      exact mem_iUnion.mpr ⟨i, hj⟩
    v1_sub := fun i => supportGraph_inter_le_sideGraph hP (σ i)
    v1_union_V := by
      rw [vertexSet_sideGraph hP h.isClosed_left, hUV, Set.union_comm]
    v1_union_E := by
      rw [edgeSet_sideGraph hP h.isClosed_left, hUE, Set.union_comm]
    v1_disjoint := by
      intro i i' hii'
      exact (hP.v1_disjoint (hσ.ne hii')).mono
        (supportGraph_inter_le_H (S₁ := S₁) hP (σ i)).vertexSet_subset
        (supportGraph_inter_le_H (S₁ := S₁) hP (σ i')).vertexSet_subset
    v1_inter_V := by
      intro i
      have hR : (ιV ∘ Subtype.val) '' ((sideDrawing Γ h.isClosed_left).V ∩
          Subtype.val ⁻¹' F_star (σ i)) = ιV '' (Γ.V ∩ (F_star (σ i) ∩ S₁)) := by
        rw [sideDrawing_V, ← preimage_inter, image_comp, Subtype.image_preimage_coe]
        congr 1
        ext x
        simp only [mem_inter_iff]
        tauto
      rw [hR, vertexSet_sideSub (S₁ := S₁) hP]
      apply Subset.antisymm
      · rintro x ⟨hx, hxΓ⟩
        have hxΓ' : x ∈ Γ_sub.vertexSet := by
          rw [← hP.ιV_image]; exact image_mono inter_subset_left hxΓ
        exact supportGraph_vertexSet_inter_subset hP (σ i) inter_subset_left
          ((isClosed_of_isSupportOfDrawing hS (hP.supports_isSupport (σ i))).inter
            h.isClosed_left) ⟨hx, hxΓ'⟩
      · rintro _ ⟨x, ⟨hxV, hxK⟩, rfl⟩
        exact ⟨(μ_vertex_le_supportGraph_of_subset hP (σ i) inter_subset_left
          ⟨hxV, hxK⟩).vertexSet_subset (ιV_mem_μ_vertex hP (σ i) ⟨hxV, hxK.1⟩),
          x, ⟨hxV, hxK.2⟩, rfl⟩
    v1_inter_E := fun i => (hP.v1_inter_E (σ i)).mono
      (supportGraph_inter_le_H (S₁ := S₁) hP (σ i)).edgeSet_subset hsub.edgeSet_subset
    q_pos := fun i => hP.q_pos (σ i)
    μ_vertex_sub := by
      rintro i x ⟨hxV, hxF⟩
      rw [sideDrawing_V] at hxV
      have hx' : x.1 ∈ Γ.V ∩ F_star (σ i) := ⟨hxV, hxF⟩
      obtain ⟨-, he, hcard, hint⟩ := hP.μ_vertex_sub (σ i) x.1 hx'
      refine ⟨μ_vertex_le_supportGraph_of_subset hP (σ i) inter_subset_left ⟨hxV, hxF, x.2⟩,
        he, hcard, ?_⟩
      rw [vertexSet_sideSub (S₁ := S₁) hP, comp_apply]
      apply Subset.antisymm
      · rintro y ⟨hy, hyΓ⟩
        rw [← hint]
        exact ⟨hy, by rw [← hP.ιV_image]; exact image_mono inter_subset_left hyΓ⟩
      · rintro y rfl
        exact ⟨ιV_mem_μ_vertex hP (σ i) hx', x.1, ⟨hxV, x.2⟩, rfl⟩
    μ_space_sub := by
      intro i s₁ hs₁ hs₁F
      have hbd : s₁ ⊆ Subtype.val ⁻¹' bd S := hs₁F.trans (preimage_mono (hFbd (σ i)))
      exact μ_space_le_supportGraph_of_subset hP (σ i) inter_subset_left
        (h.image_mem_spaces hS hs₁ hbd) (by rintro _ ⟨y, hy, rfl⟩; exact ⟨hs₁F hy, y.2⟩)
    v2_eq := by
      intro i
      rw [← preimage_inter_side S₁ (F_star (σ i)), h.supportGraph_side hS _ μ inter_subset_right
        (hKbd (σ i))]
      exact (supportGraph_eq_of_le' μ (sideGraph_le hP h.isClosed_left)
        (supportGraph_inter_le_sideGraph hP (σ i))).symm
    v3_space := by
      intro i s₁ hs₁ u₁ u₂ hs₁F hends
      have hbd : s₁ ⊆ Subtype.val ⁻¹' bd S := hs₁F.trans (preimage_mono (hFbd (σ i)))
      have hends' := h.spaceHasEnds_image hS hends hbd
      obtain ⟨hint, h1, h2, hpaths⟩ := hP.v3_space (σ i) _ hends'.1 u₁.1 u₂.1
        (image_subset_iff.mpr hs₁F) hends'
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
      have hK : Subtype.val ⁻¹' F_star (σ i) ⊆ (Subtype.val ⁻¹' bd S : Set S₁) :=
        preimage_mono (hFbd (σ i))
      have h1 := liesBetweenInSupport_image hS h.isClosed_left h.isClosed_right h.union_eq
        h.inter_eq h.isClosed_line h.inter_bd h.left_mem h.right_mem hbtw hK
      have h2 := liesBetweenInSupport_mono hS hP.cuff_vertices_ge_two
        (hP.supports_isSupport (σ i)) (image_preimage_subset _ _) h1
      exact hP.v4_between (σ i) _ _ _ h2 }

/-- **The presentation of one side has depth at most `d`** (Graph Minors XXI, proofs of (6.5),
(6.6), (6.7) and of claim (4) of (6.3), pages 25–29 of the preprint): the presentation of
`isPresentation_side` has depth at most the depth `d` of the given one. It has at least one
support, since the end `a` of `F` is a vertex of `Γ` in `bd(S) ∩ S₁`. -/
theorem presentationHasDepthLe_side {d : ℕ} (hq : ∀ j, q j ≤ d) (hconn : ConnectedSpace S₁)
    (hσ : Injective σ) (hσsup : ∀ i, IsSupportOfDrawing Γ (F_star (σ i) ∩ S₁))
    (hσall : ∀ j, (F_star j ∩ S₁).Nonempty → ∃ i, σ i = j) :
    PresentationHasDepthLe (sideGraph G Γ Γ_sub ιV ιE F_star μ S₁)
      (sideDrawing Γ h.isClosed_left) (sideSub Γ Γ_sub ιV ιE S₁) (ιV ∘ Subtype.val)
      (fun e => ιE (Subtype.val '' e)) r₁ (fun i => Subtype.val ⁻¹' F_star (σ i))
      (fun i => supportGraph G Γ μ (F_star (σ i) ∩ S₁)) (sideMu μ S₁) d := by
  refine ⟨q ∘ σ, isPresentation_side hP h hconn hσ hσsup hσall, fun i => hq (σ i), ?_⟩
  intro hr
  have haF : a ∈ F := h.proper.1.left_mem
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hP.bd_vertices_covered ⟨h.left_mem, h.ends_mem_bd.1⟩)
  obtain ⟨i, -⟩ := hσall j ⟨a, hj, h.line_subset_left haF⟩
  subst hr
  exact i.elim0

end Presentation

end Side
end GM21
end GraphMinor
