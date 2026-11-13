module

public import GraphMinor.GM21.Defs

/-!
# Graph Minors XXI: moving a graph into an infinite vertex type

The proof of (8.4) splits vertices, and each split needs two new vertices outside `V(G)`. The
paper takes them freely. In Lean the type `α` of vertices may be finite, so we move the graph into
`α ⊕ ULift ℕ` by `Sum.inl`, where new vertices always exist, and move the conclusion back.

This file defines the move (`mapInl`) and its inverse (`unmapInl`) and shows that they respect
subgraphs, unions, intersections, separations, tangles, linkages and vital linkages.
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Topology Hypergraph GraphMinor.Surface GraphMinor.GM10

universe u v

abbrev InfVert (α : Type u) : Type u := α ⊕ ULift.{u} ℕ

instance {α : Type u} : Infinite (InfVert α) :=
  Infinite.of_injective (fun n : ULift.{u} ℕ => (Sum.inr n : InfVert α)) Sum.inr_injective

/-- Push a hypergraph `H : Hypergraph α β` forward along `Sum.inl : α → InfVert α`. -/
def mapInl {α : Type u} {β : Type v} (H : Hypergraph α β) : Hypergraph (InfVert α) β where
  vertexSet := Sum.inl '' H.vertexSet
  edgeSet := H.edgeSet
  Inc e x := ∃ v : α, x = Sum.inl v ∧ H.Inc e v
  vertex_mem_of_inc := by
    rintro e _ ⟨v, rfl, hinc⟩
    exact mem_image_of_mem Sum.inl (H.vertex_mem_of_inc hinc)
  edge_mem_of_inc := by
    rintro e _ ⟨_, _, hinc⟩
    exact H.edge_mem_of_inc hinc
  vertexSet_finite := H.vertexSet_finite.image Sum.inl
  edgeSet_finite := H.edgeSet_finite

/-- Pull a hypergraph `H' : Hypergraph (InfVert α) β` back along `Sum.inl : α → InfVert α`. -/
def unmapInl {α : Type u} {β : Type v} (H' : Hypergraph (InfVert α) β) : Hypergraph α β where
  vertexSet := Sum.inl ⁻¹' H'.vertexSet
  edgeSet := H'.edgeSet
  Inc e v := H'.Inc e (Sum.inl v)
  vertex_mem_of_inc _ _ h := H'.vertex_mem_of_inc h
  edge_mem_of_inc _ _ h := H'.edge_mem_of_inc h
  vertexSet_finite := H'.vertexSet_finite.preimage Sum.inl_injective.injOn
  edgeSet_finite := H'.edgeSet_finite

@[simp]
lemma unmapInl_mapInl {α : Type u} {β : Type v} (H : Hypergraph α β) :
    unmapInl (mapInl H) = H := by
  refine Hypergraph.ext ?_ rfl ?_
  · exact preimage_image_eq H.vertexSet Sum.inl_injective
  · funext e v
    apply propext
    simp only [unmapInl, mapInl, Sum.inl.injEq]
    exact ⟨fun ⟨_, rfl, h⟩ => h, fun h => ⟨v, rfl, h⟩⟩

lemma mapInl_ends {α : Type u} {β : Type v} (H : Hypergraph α β) (e : β) :
    (mapInl H).ends e = Sum.inl '' H.ends e := by
  ext x
  simp only [Hypergraph.ends, mapInl, mem_ofPred_eq, mem_image]
  exact ⟨fun ⟨v, hx, hinc⟩ => ⟨v, hinc, hx.symm⟩, fun ⟨v, hinc, hx⟩ => ⟨v, hx.symm, hinc⟩⟩

lemma unmapInl_ends {α : Type u} {β : Type v} (H' : Hypergraph (InfVert α) β) (e : β) :
    (unmapInl H').ends e = Sum.inl ⁻¹' H'.ends e := rfl

lemma mapInl_unmapInl {α : Type u} {β : Type v} {G : Hypergraph α β}
    {H' : Hypergraph (InfVert α) β} (h : H' ≤ mapInl G) :
    mapInl (unmapInl H') = H' := by
  have hV_sub : H'.vertexSet ⊆ range (Sum.inl : α → InfVert α) :=
    h.vertexSet_subset.trans (image_subset_range _ _)
  refine Hypergraph.ext ?_ rfl ?_
  · exact image_preimage_eq_of_subset hV_sub
  · funext e x
    apply propext
    simp only [mapInl, unmapInl]
    constructor
    · rintro ⟨v, rfl, hinc⟩
      exact hinc
    · intro hinc
      obtain ⟨v, rfl⟩ := hV_sub (H'.vertex_mem_of_inc hinc)
      exact ⟨v, rfl, hinc⟩

lemma mapInl_le_iff {α : Type u} {β : Type v} {A B : Hypergraph α β} :
    mapInl A ≤ mapInl B ↔ A ≤ B := by
  constructor
  · intro h
    refine ⟨?_, h.edgeSet_subset, fun e he => ?_⟩
    · intro v hv
      have : (Sum.inl v : InfVert α) ∈ (mapInl B).vertexSet :=
        h.vertexSet_subset (mem_image_of_mem Sum.inl hv)
      rcases this with ⟨_, hx, heq⟩
      exact Sum.inl_injective heq ▸ hx
    · have he' := h.ends_eq e he
      rw [mapInl_ends, mapInl_ends] at he'
      exact Sum.inl_injective.image_injective he'
  · intro h
    refine ⟨image_mono h.vertexSet_subset, h.edgeSet_subset, fun e he => ?_⟩
    rw [mapInl_ends, mapInl_ends, h.ends_eq e he]

lemma unmapInl_le {α : Type u} {β : Type v} {A' B' : Hypergraph (InfVert α) β} (h : A' ≤ B') :
    unmapInl A' ≤ unmapInl B' where
  vertexSet_subset := preimage_mono h.vertexSet_subset
  edgeSet_subset := h.edgeSet_subset
  ends_eq e he := by
    change Sum.inl ⁻¹' (B'.ends e) = Sum.inl ⁻¹' (A'.ends e)
    rw [h.ends_eq e he]

lemma mapInl_union {α : Type u} {β : Type v} (A B : Hypergraph α β) :
    mapInl (A ∪ B) = mapInl A ∪ mapInl B := by
  refine Hypergraph.ext (image_union _ _ _) rfl ?_
  funext e x
  apply propext
  simp only [mapInl, GM10.union_inc]
  constructor
  · rintro ⟨v, rfl, h1 | h2⟩
    · exact Or.inl ⟨v, rfl, h1⟩
    · exact Or.inr ⟨v, rfl, h2⟩
  · rintro (⟨v, rfl, h1⟩ | ⟨v, rfl, h2⟩)
    · exact ⟨v, rfl, Or.inl h1⟩
    · exact ⟨v, rfl, Or.inr h2⟩

lemma mapInl_inter {α : Type u} {β : Type v} (A B : Hypergraph α β) :
    mapInl (A ∩ B) = mapInl A ∩ mapInl B := by
  refine Hypergraph.ext (image_inter Sum.inl_injective) rfl ?_
  funext e x
  apply propext
  simp only [mapInl, GM10.inter_inc]
  constructor
  · rintro ⟨v, rfl, h1, h2⟩
    exact ⟨⟨v, rfl, h1⟩, ⟨v, rfl, h2⟩⟩
  · rintro ⟨⟨v₁, rfl, h1⟩, ⟨v₂, heq, h2⟩⟩
    cases Sum.inl_injective heq
    exact ⟨v₁, rfl, h1, h2⟩

lemma mapInl_ncard_vertexSet {α : Type u} {β : Type v} (H : Hypergraph α β) :
    (mapInl H).vertexSet.ncard = H.vertexSet.ncard :=
  (Sum.inl_injective.injOn).ncard_image

lemma mapInl_isGraph {α : Type u} {β : Type v} {G : Hypergraph α β} (hG : G.IsGraph) :
    (mapInl G).IsGraph := by
  intro e he
  rw [mapInl_ends]
  obtain ⟨hne, hle⟩ := hG e he
  exact ⟨hne.image _, (Sum.inl_injective.injOn.ncard_image).trans_le hle⟩

lemma mapInl_isGraph_iff {α : Type u} {β : Type v} {G : Hypergraph α β} :
    (mapInl G).IsGraph ↔ G.IsGraph := by
  refine ⟨fun hG e he => ?_, mapInl_isGraph⟩
  obtain ⟨hne, hle⟩ := hG e he
  rw [mapInl_ends] at hne hle
  exact ⟨hne.of_image, (Sum.inl_injective.injOn.ncard_image).symm.trans_le hle⟩

lemma mapInl_isSeparation_iff {α : Type u} {β : Type v} {G A B : Hypergraph α β} :
    (mapInl G).IsSeparation (mapInl A) (mapInl B) ↔ G.IsSeparation A B := by
  constructor
  · intro h
    refine ⟨mapInl_le_iff.mp h.left_le, mapInl_le_iff.mp h.right_le, ?_, ?_⟩
    · rw [← unmapInl_mapInl (A ∪ B), mapInl_union, h.union_eq, unmapInl_mapInl]
    · have hE := h.edgeSet_inter_eq
      rwa [← mapInl_inter] at hE
  · intro h
    refine ⟨mapInl_le_iff.mpr h.left_le, mapInl_le_iff.mpr h.right_le, ?_, ?_⟩
    · rw [← mapInl_union, h.union_eq]
    · rw [← mapInl_inter]
      exact h.edgeSet_inter_eq

lemma mapInl_separationOrder {α : Type u} {β : Type v} (A B : Hypergraph α β) :
    separationOrder (mapInl A) (mapInl B) = separationOrder A B := by
  unfold separationOrder
  rw [← mapInl_inter, mapInl_ncard_vertexSet]

lemma mapInl_isTangle {α : Type u} {β : Type v} {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯) :
    IsTangle (mapInl G) θ (Prod.map mapInl mapInl '' 𝒯) where
  one_le := h𝒯.one_le
  isSeparation _ _ := by
    rintro ⟨⟨A, B⟩, hAB, rfl, rfl⟩
    exact mapInl_isSeparation_iff.mpr (h𝒯.isSeparation hAB)
  order_lt _ _ := by
    rintro ⟨⟨A, B⟩, hAB, rfl, rfl⟩
    rw [mapInl_separationOrder]
    exact h𝒯.order_lt hAB
  axiom1 A' B' hsep' hord' := by
    have hA' : mapInl (unmapInl A') = A' := mapInl_unmapInl hsep'.left_le
    have hB' : mapInl (unmapInl B') = B' := mapInl_unmapInl hsep'.right_le
    rw [← hA', ← hB'] at hsep' hord' ⊢
    have hsep : G.IsSeparation (unmapInl A') (unmapInl B') := mapInl_isSeparation_iff.mp hsep'
    rw [mapInl_separationOrder] at hord'
    rcases h𝒯.axiom1 hsep hord' with hm | hm
    · exact Or.inl ⟨(unmapInl A', unmapInl B'), hm, rfl⟩
    · exact Or.inr ⟨(unmapInl B', unmapInl A'), hm, rfl⟩
  axiom2 _ _ _ _ _ _ := by
    rintro ⟨⟨A₁, B₁⟩, h₁, rfl, rfl⟩ ⟨⟨A₂, B₂⟩, h₂, rfl, rfl⟩ ⟨⟨A₃, B₃⟩, h₃, rfl, rfl⟩ hU
    rw [← mapInl_union, ← mapInl_union] at hU
    have hU' := congrArg unmapInl hU
    rw [unmapInl_mapInl, unmapInl_mapInl] at hU'
    exact h𝒯.axiom2 h₁ h₂ h₃ hU'
  axiom3 _ _ := by
    rintro ⟨⟨A, B⟩, hAB, rfl, rfl⟩ hV
    apply h𝒯.axiom3 hAB
    exact Sum.inl_injective.image_injective hV

lemma mapInl_skeleton_adj_iff {α : Type u} {β : Type v} (H : Hypergraph α β) (x y : α) :
    (mapInl H).skeleton.Adj (Sum.inl x) (Sum.inl y) ↔ H.skeleton.Adj x y := by
  simp only [Hypergraph.skeleton, mapInl, ne_eq, Sum.inl.injEq]
  exact ⟨fun ⟨hne, e, ⟨_, rfl, h1⟩, ⟨_, rfl, h2⟩⟩ => ⟨hne, e, h1, h2⟩,
    fun ⟨hne, e, h1, h2⟩ => ⟨hne, e, ⟨x, rfl, h1⟩, ⟨y, rfl, h2⟩⟩⟩

lemma mapInl_skeleton_reachable_iff {α : Type u} {β : Type v} (H : Hypergraph α β) (x y : α) :
    (mapInl H).skeleton.Reachable (Sum.inl x) (Sum.inl y) ↔ H.skeleton.Reachable x y := by
  constructor
  · rintro ⟨p⟩
    have hwalk : ∀ {a b : InfVert α} (w : (mapInl H).skeleton.Walk a b) (x' y' : α),
        a = Sum.inl x' → b = Sum.inl y' → H.skeleton.Reachable x' y' := by
      intro a b w
      induction w with
      | nil =>
        intro x' y' hx hy
        cases Sum.inl_injective (hx.symm.trans hy)
        exact SimpleGraph.Reachable.refl _
      | @cons a c b hadj w' ih =>
        intro x' y' rfl rfl
        rcases hadj with ⟨hne, e, ⟨_, h1_eq, h1⟩, ⟨z, rfl, h2⟩⟩
        cases Sum.inl_injective h1_eq
        have hadj_H : H.skeleton.Adj x' z := ⟨mt (congrArg Sum.inl) hne, e, h1, h2⟩
        exact hadj_H.reachable.trans (ih z y' rfl rfl)
    exact hwalk p x y rfl rfl
  · rintro ⟨p⟩
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons a c b hadj _ ih =>
      exact ((mapInl_skeleton_adj_iff H a c).mpr hadj).reachable.trans ih

lemma mapInl_isComponentOf_iff {α : Type u} {β : Type v} {H C : Hypergraph α β} :
    IsComponentOf (mapInl H) (mapInl C) ↔ IsComponentOf H C := by
  constructor
  · rintro ⟨hle, hne, hconn, hmax⟩
    refine ⟨mapInl_le_iff.mp hle, ?_, ?_, ?_⟩
    · rcases hne with ⟨_, ⟨x, hx, rfl⟩⟩
      exact ⟨x, hx⟩
    · intro x hx y hy
      exact (mapInl_skeleton_reachable_iff C x y).mp
        (hconn (Sum.inl x) (mem_image_of_mem _ hx) (Sum.inl y) (mem_image_of_mem _ hy))
    · intro C' hC' hne' hconn' hle'
      have hconn_map : ∀ a ∈ (mapInl C').vertexSet, ∀ b ∈ (mapInl C').vertexSet,
          (mapInl C').skeleton.Reachable a b := by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        exact (mapInl_skeleton_reachable_iff C' x y).mpr (hconn' x hx y hy)
      have heq := hmax (mapInl C') (mapInl_le_iff.mpr hC') (hne'.image _)
        hconn_map (mapInl_le_iff.mpr hle')
      simpa using congrArg unmapInl heq
  · rintro ⟨hle, hne, hconn, hmax⟩
    refine ⟨mapInl_le_iff.mpr hle, hne.image _, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact (mapInl_skeleton_reachable_iff C x y).mpr (hconn x hx y hy)
    · intro C' hC' hne' hconn' hle'
      have hC'_eq : mapInl (unmapInl C') = C' := mapInl_unmapInl hC'
      rw [← hC'_eq] at hC' hne' hconn' hle' ⊢
      congr 1
      apply hmax (unmapInl C') (mapInl_le_iff.mp hC')
      · rcases hne' with ⟨_, ⟨x, hx, rfl⟩⟩
        exact ⟨x, hx⟩
      · intro x hx y hy
        exact (mapInl_skeleton_reachable_iff (unmapInl C') x y).mp
          (hconn' (Sum.inl x) (mem_image_of_mem _ hx) (Sum.inl y) (mem_image_of_mem _ hy))
      · exact mapInl_le_iff.mp hle'

lemma mapInl_incidentEdges {α : Type u} {β : Type v} (H : Hypergraph α β) (x : α) :
    incidentEdges (mapInl H) (Sum.inl x) = incidentEdges H x := by
  ext e
  simp [incidentEdges, mapInl]

lemma mapInl_vertexDegree {α : Type u} {β : Type v} (H : Hypergraph α β) (x : α) :
    vertexDegree (mapInl H) (Sum.inl x) = vertexDegree H x := by
  unfold vertexDegree
  rw [mapInl_incidentEdges]
  congr 2
  ext e
  simp only [mem_ofPred_eq, mapInl_ends]
  exact and_congr_right fun _ =>
    ⟨fun h a ha b hb => Sum.inl_injective (h (mem_image_of_mem _ ha) (mem_image_of_mem _ hb)),
      fun h => h.image _⟩

lemma mapInl_terminals {α : Type u} {β : Type v} (L : Hypergraph α β) :
    terminals (mapInl L) = Sum.inl '' terminals L := by
  ext a
  simp only [terminals, IsTerminal, mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hdeg⟩
    rw [mapInl_vertexDegree] at hdeg
    exact ⟨x, ⟨hx, hdeg⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hdeg⟩, rfl⟩
    rw [mapInl_vertexDegree]
    exact ⟨mem_image_of_mem _ hx, hdeg⟩

lemma mapInl_isPathGraph_iff {α : Type u} {β : Type v} {P : Hypergraph α β} :
    IsPathGraph (mapInl P) ↔ IsPathGraph P := by
  constructor
  · rintro ⟨hG, hne, hconn, h2, hinj, hdeg2, hex1⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e he
      obtain ⟨hne_e, hle_e⟩ := hG e he
      rw [mapInl_ends] at hne_e hle_e
      exact ⟨hne_e.of_image, (Sum.inl_injective.injOn.ncard_image).symm.trans_le hle_e⟩
    · rcases hne with ⟨_, ⟨x, hx, rfl⟩⟩; exact ⟨x, hx⟩
    · intro x hx y hy
      exact (mapInl_skeleton_reachable_iff P x y).mp
        (hconn (Sum.inl x) (mem_image_of_mem _ hx) (Sum.inl y) (mem_image_of_mem _ hy))
    · intro e he
      have h := h2 e he
      rwa [mapInl_ends, Sum.inl_injective.injOn.ncard_image] at h
    · intro e₁ he₁ e₂ he₂ hends
      apply hinj e₁ he₁ e₂ he₂
      rw [mapInl_ends, mapInl_ends, hends]
    · intro x hx
      have h := hdeg2 (Sum.inl x) (mem_image_of_mem _ hx)
      rwa [mapInl_incidentEdges] at h
    · intro H hHP hne_E
      obtain ⟨_, ⟨x, hx, rfl⟩, h1⟩ := hex1 (mapInl H) (mapInl_le_iff.mpr hHP) hne_E
      rw [mapInl_incidentEdges] at h1
      exact ⟨x, hx, h1⟩
  · rintro ⟨hG, hne, hconn, h2, hinj, hdeg2, hex1⟩
    refine ⟨mapInl_isGraph hG, hne.image _, ?_, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact (mapInl_skeleton_reachable_iff P x y).mpr (hconn x hx y hy)
    · intro e he
      rw [mapInl_ends, Sum.inl_injective.injOn.ncard_image]
      exact h2 e he
    · intro e₁ he₁ e₂ he₂ hends
      rw [mapInl_ends, mapInl_ends] at hends
      exact hinj e₁ he₁ e₂ he₂ (Sum.inl_injective.image_injective hends)
    · rintro _ ⟨x, hx, rfl⟩
      rw [mapInl_incidentEdges]
      exact hdeg2 x hx
    · intro H' hH'P hne_E
      have hH'_eq : mapInl (unmapInl H') = H' := mapInl_unmapInl hH'P
      rw [← hH'_eq] at hH'P hne_E ⊢
      obtain ⟨x, hx, h1⟩ := hex1 (unmapInl H') (mapInl_le_iff.mp hH'P) hne_E
      refine ⟨Sum.inl x, mem_image_of_mem _ hx, ?_⟩
      rwa [mapInl_incidentEdges]

lemma mapInl_isLinkage_iff {α : Type u} {β : Type v} {G L : Hypergraph α β} :
    IsLinkage (mapInl G) (mapInl L) ↔ IsLinkage G L := by
  constructor
  · rintro ⟨hle, hgr, hcomp⟩
    refine ⟨mapInl_le_iff.mp hle, mapInl_isGraph_iff.mp hgr, fun C hC => ?_⟩
    exact mapInl_isPathGraph_iff.mp (hcomp (mapInl C) (mapInl_isComponentOf_iff.mpr hC))
  · rintro ⟨hle, hgr, hcomp⟩
    refine ⟨mapInl_le_iff.mpr hle, mapInl_isGraph hgr, fun C' hC' => ?_⟩
    have hC'_eq : mapInl (unmapInl C') = C' := mapInl_unmapInl hC'.1
    rw [← hC'_eq] at hC' ⊢
    exact mapInl_isPathGraph_iff.mpr (hcomp (unmapInl C') (mapInl_isComponentOf_iff.mp hC'))

lemma mapInl_linkagePattern {α : Type u} {β : Type v} (L : Hypergraph α β) :
    linkagePattern (mapInl L) = (Set.image Sum.inl) '' linkagePattern L := by
  ext B'
  simp only [linkagePattern, mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨C', hC', rfl⟩
    have hC'_eq : mapInl (unmapInl C') = C' := mapInl_unmapInl hC'.1
    rw [← hC'_eq] at hC' ⊢
    have hC : IsComponentOf L (unmapInl C') := mapInl_isComponentOf_iff.mp hC'
    refine ⟨terminals L ∩ (unmapInl C').vertexSet, ⟨unmapInl C', hC, rfl⟩, ?_⟩
    rw [mapInl_terminals, image_inter Sum.inl_injective]
    rfl
  · rintro ⟨B, ⟨C, hC, rfl⟩, rfl⟩
    refine ⟨mapInl C, mapInl_isComponentOf_iff.mpr hC, ?_⟩
    rw [mapInl_terminals, image_inter Sum.inl_injective]
    rfl

lemma mapInl_hasVitalPLinkage {α : Type u} {β : Type v} {G : Hypergraph α β} {p : ℕ}
    (h : HasVitalPLinkage G p) :
    HasVitalPLinkage (mapInl G) p := by
  rcases h with ⟨L, ⟨hlink, hV_eq, huniq⟩, _, hcard⟩
  refine ⟨mapInl L, ⟨mapInl_isLinkage_iff.mpr hlink, ?_, ?_⟩,
    mapInl_isLinkage_iff.mpr hlink, ?_⟩
  · change Sum.inl '' L.vertexSet = Sum.inl '' G.vertexSet
    rw [hV_eq]
  · intro L' hL' hpat
    have hL'_eq : mapInl (unmapInl L') = L' := mapInl_unmapInl hL'.1
    rw [← hL'_eq] at hL' hpat ⊢
    congr 1
    apply huniq (unmapInl L') (mapInl_isLinkage_iff.mp hL')
    rw [mapInl_linkagePattern, mapInl_linkagePattern] at hpat
    exact (Set.image_injective.mpr Sum.inl_injective.image_injective) hpat
  · rw [mapInl_terminals, Sum.inl_injective.injOn.ncard_image]
    exact hcard

end GM21
end GraphMinor
