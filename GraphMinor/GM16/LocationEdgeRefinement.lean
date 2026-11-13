module

public import GraphMinor.GM16.SingleEdgeSeparation
public import GraphMinor.GM16.LocationCore
import GraphMinor.GM09.Basic

/-!
# Refining a location to remove core edges

For the lifted location in XVI (1.3), pages 51–52, add single-edge
separations for core edges incident with the exceptional vertices.
Their right sides keep every vertex. The result is still a location,
with the same core vertices and those chosen core edges removed.
-/

@[expose] public section
namespace GraphMinor.GM16
open Set Graph GM06 GM09
universe u v

/-- Refine a location by removing specified core edges on separate
left sides, each of order at most two. -/
def refineLocationEdges {α : Type u} {β : Type v} (G : Graph α β)
    (ℒ : Set (Graph α β × Graph α β)) (K : Set β) :
    Set (Graph α β × Graph α β) := ℒ ∪ singleEdgePair G '' K

/-- Adding the single-edge separations of core edges preserves the
location condition. -/
theorem IsGraphLocation.refineEdges {α : Type u} {β : Type v}
    {G : Graph α β} {ℒ : Set (Graph α β × Graph α β)} {K : Set β}
    (h : IsGraphLocation G ℒ) (hKfin : K.Finite)
    (hK : K ⊆ E(graphLocationCore G ℒ)) :
    IsGraphLocation G (refineLocationEdges G ℒ K) := by
  have hKG : K ⊆ E(G) := hK.trans (graphLocationCore_le G ℒ).edgeSet_mono
  have hRight : ∀ e ∈ K, ∀ p ∈ ℒ, e ∈ E(p.2) := by
    intro e he p hp
    have heCore := hK he
    rw [edgeSet_graphLocationCore h] at heCore
    exact heCore.2 p hp
  refine ⟨h.finite.union (hKfin.image _), ?_, ?_⟩
  · rintro p (hp | ⟨e, he, rfl⟩)
    · exact h.isSeparation hp
    · exact singleEdgePair_isSeparation (hKG he)
  · rintro p (hp | ⟨e, he, rfl⟩) q (hq | ⟨f, hf, rfl⟩) hne
    · exact h.left_le_right hp hq hne
    · apply le_singleEdgePair_right (h.isSeparation hp).1
      intro hfA
      exact disjoint_left.mp (h.isSeparation hp).2.2.2.2 hfA (hRight f hf p hp)
    · exact singleEdgeGraph_le_of_mem (h.isSeparation hq).2.1 (hRight e he q hq)
    · have hef : e ≠ f := fun heq => hne (congrArg (singleEdgePair G) heq)
      apply le_singleEdgePair_right (singleEdgeGraph_le G e)
      rw [edgeSet_singleEdgeGraph (hKG he)]
      exact fun hfe => hef (mem_singleton_iff.mp hfe).symm

/-- The refinement keeps every old core vertex. -/
theorem vertexSet_refined_core {α : Type u} {β : Type v}
    (G : Graph α β) (ℒ : Set (Graph α β × Graph α β)) (K : Set β) :
    V(graphLocationCore G (refineLocationEdges G ℒ K)) = V(graphLocationCore G ℒ) := by
  ext x
  constructor
  · rintro ⟨hxG, hxAll⟩
    exact ⟨hxG, fun p hp => hxAll p (Or.inl hp)⟩
  · rintro ⟨hxG, hxAll⟩
    refine ⟨hxG, ?_⟩
    rintro p (hp | ⟨e, he, rfl⟩)
    · exact hxAll p hp
    · exact hxG

/-- The refinement removes precisely its chosen core edges. -/
theorem edgeSet_refined_core {α : Type u} {β : Type v}
    {G : Graph α β} {ℒ : Set (Graph α β × Graph α β)} {K : Set β}
    (h : IsGraphLocation G ℒ) (hKfin : K.Finite)
    (hK : K ⊆ E(graphLocationCore G ℒ)) :
    E(graphLocationCore G (refineLocationEdges G ℒ K)) = E(graphLocationCore G ℒ) \ K := by
  rw [edgeSet_graphLocationCore (h.refineEdges hKfin hK), edgeSet_graphLocationCore h]
  ext e
  constructor
  · rintro ⟨heG, heAll⟩
    refine ⟨⟨heG, fun p hp => heAll p (Or.inl hp)⟩, ?_⟩
    intro heK
    have heRight : e ∈ E(G.deleteEdges {e}) := heAll _ (Or.inr ⟨e, heK, rfl⟩)
    exact heRight.2 (mem_singleton e)
  · rintro ⟨⟨heG, heAll⟩, heNot⟩
    refine ⟨heG, ?_⟩
    rintro p (hp | ⟨f, hf, rfl⟩)
    · exact heAll p hp
    · refine ⟨heG, ?_⟩
      intro hef
      have heq : e = f := mem_singleton_iff.mp hef
      subst f
      exact heNot hf

/-- The orders of the old separators stay the same, and the added
separators have order at most two. -/
theorem refinedLocation_separator_bound {α : Type u} {β : Type v}
    {G : Graph α β} {ℒ : Set (Graph α β × Graph α β)} {K : Set β} {k : ℕ}
    (hOrder : ∀ p ∈ ℒ, (V(p.1) ∩ V(p.2)).ncard ≤ k) (hK : K ⊆ E(G))
    {p : Graph α β × Graph α β} (hp : p ∈ refineLocationEdges G ℒ K) :
    (V(p.1) ∩ V(p.2)).ncard ≤ max k 2 := by
  rcases hp with hp | ⟨e, he, rfl⟩
  · exact (hOrder p hp).trans (le_max_left _ _)
  · exact (singleEdgePair_order_le_two (hK he)).trans (le_max_right _ _)

end GraphMinor.GM16
