module

public import GraphMinor.GM16.Defs
import GraphMinor.GM09.Basic

/-!
# Extending a location from a society to its graph

In the proof of XVI (1.3), page 51, a separation inside a society is
extended by adjoining the complementary graph to its right side.
When the society boundary stays on the right, this preserves its
separator. The same construction sends a local location to a location.
-/

@[expose] public section
namespace GraphMinor.GM16
open Set Graph GM06 GM09 GM14
universe u v

/-- The separation `(Aᵢʲ, Bᵢʲ ∪ C(Aⱼ, Ωⱼ))` of XVI, page 51. -/
def extendLocationPair {α : Type u} {β : Type v} (G C : Graph α β)
    (p : Graph α β × Graph α β) : Graph α β × Graph α β :=
  (p.1, subgraphUnion G p.2 C)

/-- Adjoining the complementary graph extends a separation to the full
 graph. Keeping the original separator on the right preserves its order. -/
theorem extendLocationPair_isSeparation {α : Type u} {β : Type v}
    {G A C U V : Graph α β} (hAC : IsGraphSeparation G A C)
    (hUV : IsGraphSeparation A U V) (hbd : V(A) ∩ V(C) ⊆ V(V)) :
    IsGraphSeparation G U (subgraphUnion G V C) ∧
      V(U) ∩ V(subgraphUnion G V C) = V(U) ∩ V(V) := by
  have hUG := hUV.1.trans hAC.1
  have hVG := hUV.2.1.trans hAC.1
  refine ⟨⟨hUG, subgraphUnion_le hVG hAC.2.1, ?_, ?_, ?_⟩, ?_⟩
  · rw [vertexSet_subgraphUnion, ← union_assoc, hUV.2.2.1, hAC.2.2.1]
  · rw [edgeSet_subgraphUnion hVG hAC.2.1, ← union_assoc, hUV.2.2.2.1,
      hAC.2.2.2.1]
  · rw [edgeSet_subgraphUnion hVG hAC.2.1, disjoint_union_right]
    exact ⟨hUV.2.2.2.2, hAC.2.2.2.2.mono_left hUV.1.edgeSet_mono⟩
  · rw [vertexSet_subgraphUnion]
    ext x
    constructor
    · rintro ⟨hxU, hxV | hxC⟩
      · exact ⟨hxU, hxV⟩
      · exact ⟨hxU, hbd ⟨hUV.1.vertexSet_mono hxU, hxC⟩⟩
    · rintro ⟨hxU, hxV⟩
      exact ⟨hxU, Or.inl hxV⟩

/-- The local location of a large society remains a location after
 adjoining the society complement, as used in XVI, page 51. -/
theorem IsGraphLocation.extend {α : Type u} {β : Type v}
    {G A C : Graph α β} {ℒ : Set (Graph α β × Graph α β)}
    (h : IsGraphLocation A ℒ) (hAC : IsGraphSeparation G A C)
    (hbd : ∀ p ∈ ℒ, V(A) ∩ V(C) ⊆ V(p.2)) :
    IsGraphLocation G (extendLocationPair G C '' ℒ) := by
  refine ⟨h.finite.image _, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact (extendLocationPair_isSeparation hAC (h.isSeparation hp) (hbd p hp)).1
  · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hne
    have hpq : p ≠ q := fun heq => hne (congrArg (extendLocationPair G C) heq)
    exact (h.left_le_right hp hq hpq).trans
      (le_subgraphUnion_left ((h.isSeparation hq).2.1.trans hAC.1) hAC.2.1)

end GraphMinor.GM16
