module

public import GraphMinor.GM06.Section3Dual
import Mathlib.Topology.Connected.Clopen

/-!
# Connected subsets stay in one drawing component

For the retained barrier in VI (5.5), page 130, the cuffs and a
linkage path form a connected point set in the augmented drawing.
A preconnected subset meeting one graph component lies entirely
in it: the finitely many other component point sets form a closed
set disjoint from that component.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- A preconnected subset of a finite drawing meeting a graph
component is contained in that component's point set. -/
theorem subset_compPointSet_of_isPreconnected
    {S : Type*} [TopologicalSpace S] [T2Space S] (G : Drawing S)
    {C : Graph S (Set S)} (hC : IsGraphComponent C G.toGraph)
    {X : Set S} (hX : IsPreconnected X) (hXG : X ⊆ G.U)
    (hmeet : (X ∩ compPointSet C).Nonempty) : X ⊆ compPointSet C := by
  let T := graphComponents G.toGraph \ {C}
  let B := ⋃ K ∈ T, compPointSet K
  have hT : T.Finite := (finite_graphComponents G).subset sdiff_subset
  have hBc : IsClosed B := hT.isClosed_biUnion (fun K hK => isClosed_compPointSet G hK.1)
  have hdis : Disjoint (compPointSet C) B := by
    apply disjoint_left.mpr
    intro x hxC hxB
    obtain ⟨K, hK, hxK⟩ := mem_iUnion₂.mp hxB
    exact disjoint_left.mp (disjoint_compPointSet_of_ne G hC hK.1
      (fun he => hK.2 he.symm)) hxC hxK
  have hcover : X ⊆ compPointSet C ∪ B := by
    intro x hx
    have hxG := hXG hx
    rw [← biUnion_compPointSet_eq_U G] at hxG
    obtain ⟨K, hK, hxK⟩ := mem_iUnion₂.mp hxG
    by_cases he : K = C
    · exact Or.inl (he ▸ hxK)
    · exact Or.inr (mem_iUnion₂.mpr ⟨K, ⟨hK, he⟩, hxK⟩)
  have hinter : X ∩ (compPointSet C ∩ B) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨_, hxC, hxB⟩
    exact disjoint_left.mp hdis hxC hxB
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hX (compPointSet C) B
    (isClosed_compPointSet G hC) hBc hcover hinter with h | h
  · exact h
  · obtain ⟨x, hxX, hxC⟩ := hmeet
    exact False.elim (disjoint_left.mp hdis hxC (h hxX))

end GraphMinor.GM06
