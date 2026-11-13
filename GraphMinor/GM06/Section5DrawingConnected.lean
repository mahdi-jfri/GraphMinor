module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section3Induce
import Mathlib.Topology.Connected.Clopen

/-!
# From connected point sets to graph walks

A finite drawing with a preconnected point set and at least one vertex
has a connected graph. Its component point sets are closed and pairwise
disjoint. Preconnectedness therefore forces the entire point set into
the component of a chosen vertex. This converts the cuff connectivity
used in VI (5.1) into graph connectivity.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface

universe u

/-- A drawing with a preconnected point set and a vertex has a
connected graph. -/
theorem isGraphConnected_of_isPreconnected_U
    {S : Type u} [TopologicalSpace S] [T2Space S] {G : Drawing S}
    (hpre : IsPreconnected G.U) (hne : G.V.Nonempty) : IsGraphConnected G.toGraph := by
  classical
  obtain ⟨a, ha⟩ := hne
  let K := compOf G.toGraph a
  have hK : IsGraphComponent K G.toGraph := isGraphComponent_compOf ha
  have haK : a ∈ Graph.vertexSet K := self_mem_reachSet ha
  let B := ⋃ C ∈ graphComponents G.toGraph \ {K}, compPointSet C
  have hfin : (graphComponents G.toGraph \ {K}).Finite :=
    (finite_graphComponents G).subset sdiff_subset
  have hBc : IsClosed B := hfin.isClosed_biUnion
    (fun C hC => isClosed_compPointSet G hC.1)
  have hdis : Disjoint (compPointSet K) B := by
    apply disjoint_left.mpr
    intro x hxK hxB
    obtain ⟨C, hC, hxC⟩ := mem_iUnion₂.mp hxB
    have hKC : K ≠ C := fun heq => hC.2 heq.symm
    exact disjoint_left.mp (disjoint_compPointSet_of_ne G hK hC.1 hKC) hxK hxC
  have hcover : G.U ⊆ compPointSet K ∪ B := by
    intro x hx
    rw [← biUnion_compPointSet_eq_U G] at hx
    obtain ⟨C, hC, hxC⟩ := mem_iUnion₂.mp hx
    by_cases heq : C = K
    · exact Or.inl (heq ▸ hxC)
    · exact Or.inr (mem_iUnion₂.mpr ⟨C, ⟨hC, heq⟩, hxC⟩)
  have hinter : G.U ∩ (compPointSet K ∩ B) = ∅ := by
    ext x
    exact ⟨fun hx => False.elim (disjoint_left.mp hdis hx.2.1 hx.2.2), False.elim⟩
  have hUK : G.U ⊆ compPointSet K := by
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hpre
      (compPointSet K) B (isClosed_compPointSet G hK) hBc hcover hinter with h | h
    · exact h
    · exact False.elim (disjoint_left.mp hdis (Or.inl haK) (h (G.V_subset_U ha)))
  have hVK : G.V ⊆ Graph.vertexSet K := by
    intro x hx
    rcases hUK (G.V_subset_U hx) with hxK | hxE
    · exact hxK
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hxE
      exact False.elim (((hK.1.edgeSet_mono he).2.1 hxe).2 hx)
  refine ⟨⟨a, ha⟩, ?_⟩
  intro x hx y hy
  obtain ⟨W⟩ := hK.2.1.2 x (hVK hx) y (hVK hy)
  exact ⟨W.mono hK.1⟩

end GraphMinor.GM06
