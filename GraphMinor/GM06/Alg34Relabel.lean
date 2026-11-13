module

public import GraphMinor.GM22.Section3Disc

/-!
# Relabelling the graphs used by the disc algorithm

Vertex and edge embeddings preserve forests and divisions. These facts
allow the finite input labels of VI (3.4) to be compared with the vertices
and edges of a drawing, without choosing geometric coordinates in a program.
-/

public section
namespace GraphMinor.GM06

open Set Surface GM22 Graph

variable {α β γ η : Type*} (f : α ↪ γ) (g : β ↪ η)

/-- Relabelling vertices and edges preserves the absence of circuits. -/
theorem alg34_forest_map_iff (H : Graph α β) :
    IsGraphForest (H.mapEmbed f g) ↔ IsGraphForest H := by
  constructor
  · intro h u W hW
    obtain ⟨W', hs, he⟩ := mapEmbed_walk f g W
    have htail : (W.support.map f).tail = W.support.tail.map f := by
      cases W.support <;> rfl
    have hsimple : W'.IsSimpleClosed := by
      constructor
      · rw [hs, htail]
        exact hW.1.map f.injective
      · rw [he]
        exact hW.2.map g.injective
    have hz := h (f u) W' hsimple
    simpa only [GraphWalk.length, he, List.length_map] using hz
  · intro h z W hW
    have hz : z ∈ (H.mapEmbed f g).vertexSet := by
      cases W with
      | nil hv => exact hv
      | cons hl _ => exact hl.left_mem
    obtain ⟨u, hu, rfl⟩ := hz
    obtain ⟨W₀, hs, he⟩ := comapEmbed_walk f g W
    have htail : (W₀.support.map f).tail = W₀.support.tail.map f := by
      cases W₀.support <;> rfl
    have hsimple : W₀.IsSimpleClosed := by
      constructor
      · have hh := hW.1
        rw [hs, htail] at hh
        exact List.Nodup.of_map f hh
      · have hh := hW.2
        rw [he] at hh
        exact List.Nodup.of_map g hh
    have hz := h u W₀ hsimple
    simpa only [GraphWalk.length, he, List.length_map] using hz

/-- An injective relabelling of the vertices preserves a division. -/
theorem alg34_division_image {Δ : Set (Set α)} (h : IsDivision Δ) :
    IsDivision ((Set.image f) '' Δ) := by
  refine ⟨h.1.image _, ?_, ?_⟩
  · rintro _ ⟨δ, hδ, rfl⟩
    exact (h.2.1 δ hδ).image f
  · rintro _ ⟨δ, hδ, rfl⟩ _ ⟨ε, hε, rfl⟩ hne
    apply Set.disjoint_left.mpr
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, heq⟩
    have heq' : b = a := f.injective heq
    subst b
    exact Set.disjoint_left.mp (h.2.2 hδ hε (fun hδε => hne (congrArg _ hδε))) ha hb

/-- A division on injectively relabelled vertices is a division on the
original vertices as well. -/
theorem alg34_division_of_image {Δ : Set (Set α)}
    (h : IsDivision ((Set.image f) '' Δ)) : IsDivision Δ := by
  refine ⟨h.1.of_finite_image f.injective.image_injective.injOn, ?_, ?_⟩
  · intro δ hδ
    obtain ⟨_, a, ha, rfl⟩ := h.2.1 _ ⟨δ, hδ, rfl⟩
    exact ⟨a, ha⟩
  · intro δ hδ ε hε hne
    apply Set.disjoint_left.mpr
    intro a ha hb
    have hd := h.2.2 (show f '' δ ∈ (Set.image f) '' Δ from ⟨δ, hδ, rfl⟩)
      (show f '' ε ∈ (Set.image f) '' Δ from ⟨ε, hε, rfl⟩)
      (fun heq => hne (f.injective.image_injective heq))
    exact Set.disjoint_left.mp hd ⟨a, ha, rfl⟩ ⟨a, hb, rfl⟩

private theorem alg34_map_injective : Function.Injective (Graph.mapEmbed f g) := by
  intro H K heq
  exact le_antisymm ((mapEmbed_le_iff f g).mp heq.le)
    ((mapEmbed_le_iff f g).mp heq.ge)

/-- A realization can be read with any injective vertex and edge labels.
The component indexed by the image of a division block is the relabelled
component indexed by that block. -/
theorem alg34_realization_map {G H : Graph α β} {Δ : Set (Set α)}
    (h : IsRealization G Δ H) :
    IsRealization (G.mapEmbed f g) ((Set.image f) '' Δ) (H.mapEmbed f g) := by
  obtain ⟨hΔ, hsub, hHG, hforest, C, hCinj, hC, hcomponents⟩ := h
  refine ⟨alg34_division_image f hΔ, ?_, mapEmbed_mono f g hHG,
    (alg34_forest_map_iff f g H).mpr hforest,
    fun δ => (C (f ⁻¹' δ)).mapEmbed f g, ?_, ?_, ?_⟩
  · rintro _ ⟨δ', ⟨δ, hδ, rfl⟩, a, ha, rfl⟩
    exact ⟨a, hsub ⟨δ, hδ, ha⟩, rfl⟩
  · rintro _ ⟨δ, hδ, rfl⟩ _ ⟨ε, hε, rfl⟩ heq
    simp only [preimage_image_eq _ f.injective] at heq
    exact congrArg (Set.image f) (hCinj hδ hε (alg34_map_injective f g heq))
  · rintro _ ⟨δ, hδ, rfl⟩
    simp only [preimage_image_eq _ f.injective]
    refine ⟨(isGraphComponent_mapEmbed_iff f g).mpr (hC δ hδ).1, ?_⟩
    exact image_mono (hC δ hδ).2
  · ext K
    rw [mem_graphComponents_mapEmbed_iff f g]
    constructor
    · rintro ⟨K₀, hK₀, rfl⟩
      rw [hcomponents] at hK₀
      obtain ⟨δ, hδ, rfl⟩ := hK₀
      refine ⟨f '' δ, ⟨δ, hδ, rfl⟩, ?_⟩
      simp only [preimage_image_eq _ f.injective]
    · rintro ⟨_, ⟨δ, hδ, rfl⟩, rfl⟩
      dsimp only
      rw [preimage_image_eq _ f.injective]
      exact ⟨C δ, hcomponents.symm ▸ ⟨δ, hδ, rfl⟩, rfl⟩

/-- A realization with relabelled vertices and edges gives a realization
with the original labels. The division and containment assumptions are
exactly the input conditions of VI, Section 1, page 116. -/
theorem alg34_realization_of_map {G H : Graph α β} {Δ : Set (Set α)}
    (hΔ : IsDivision Δ) (hsub : divisionUnion Δ ⊆ G.vertexSet)
    (h : IsRealization (G.mapEmbed f g) ((Set.image f) '' Δ) (H.mapEmbed f g)) :
    IsRealization G Δ H := by
  obtain ⟨_, _, hHG, hforest, C, hCinj, hC, hcomponents⟩ := h
  let D : Set α → Graph α β := fun δ => (C (f '' δ)).comapEmbed f g
  have hmem : ∀ δ ∈ Δ, f '' δ ∈ (Set.image f) '' Δ := fun δ hδ => ⟨δ, hδ, rfl⟩
  have hmap : ∀ δ ∈ Δ, (D δ).mapEmbed f g = C (f '' δ) := by
    intro δ hδ
    exact (mapEmbed_comapEmbed_of_le f g (hC _ (hmem δ hδ)).1.1).1
  have hD : ∀ δ ∈ Δ, IsGraphComponent (D δ) H ∧ δ ⊆ (D δ).vertexSet := by
    intro δ hδ
    refine ⟨(isGraphComponent_mapEmbed_iff f g).mp ?_, ?_⟩
    · rw [hmap δ hδ]
      exact (hC _ (hmem δ hδ)).1
    · intro a ha
      have hf : f a ∈ (C (f '' δ)).vertexSet :=
        (hC _ (hmem δ hδ)).2 ⟨a, ha, rfl⟩
      rw [← hmap δ hδ] at hf
      exact f.injective.mem_set_image.mp hf
  refine ⟨hΔ, hsub, (mapEmbed_le_iff f g).mp hHG,
    (alg34_forest_map_iff f g H).mp hforest, D, ?_, hD, ?_⟩
  · intro δ hδ ε hε heq
    apply f.injective.image_injective
    apply hCinj (hmem δ hδ) (hmem ε hε)
    rw [← hmap δ hδ, ← hmap ε hε, heq]
  · ext K
    constructor
    · intro hK
      have hKmap : K.mapEmbed f g ∈ graphComponents (H.mapEmbed f g) :=
        (isGraphComponent_mapEmbed_iff f g).mpr hK
      rw [hcomponents] at hKmap
      obtain ⟨_, ⟨δ, hδ, rfl⟩, heq⟩ := hKmap
      refine ⟨δ, hδ, alg34_map_injective f g ?_⟩
      exact (hmap δ hδ).trans heq
    · rintro ⟨δ, hδ, rfl⟩
      exact (hD δ hδ).1

/-- Feasibility is unchanged by injective vertex and edge labels. The
hypotheses say that the supplied blocks form a division of vertices of the
graph, as required by VI, Section 1, page 116. No geometric information
or reduction sequence is needed for this relabelling step. -/
theorem alg34_feasible_map_iff (G : Graph α β) (Δ : Set (Set α))
    (hΔ : IsDivision Δ) (hsub : divisionUnion Δ ⊆ G.vertexSet) :
    IsFeasible (G.mapEmbed f g) ((Set.image f) '' Δ) ↔ IsFeasible G Δ := by
  constructor
  · rintro ⟨H', hH'⟩
    obtain ⟨heq, _⟩ := mapEmbed_comapEmbed_of_le f g hH'.2.2.1
    refine ⟨H'.comapEmbed f g, alg34_realization_of_map f g hΔ hsub ?_⟩
    rw [heq]
    exact hH'
  · rintro ⟨H, hH⟩
    exact ⟨H.mapEmbed f g, alg34_realization_map f g hH⟩

end GraphMinor.GM06
