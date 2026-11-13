module

public import GraphMinor.GM08.Defs6to18
import GraphMinor.GM22.Section3Disc
import GraphMinor.GM07.Section3

/-!
# Points of one ring are not inside another

In the proof of Graph Minors VIII, (11.1) we apply the sleeve argument to `F_1, …, F_t` in turn.
For this we need that a sleeve for `F_k` has no vertex inside any other `F_j`. Points inside `F_k`
are not inside `F_j`, because the two open discs are disjoint. A point `x` of `F_k` itself lies in
the closure of the open disc inside `F_k`. If `x` were inside `F_j`, the open disc inside `F_j`
would be a neighbourhood of `x`, so it would meet the open disc inside `F_k`, which is again
impossible (`not_insideOArc_of_mem`).
-/

public section

namespace GraphMinor
namespace GM08

open Set Topology Surface

universe u

variable {S : Type u} [TopologicalSpace S]

/-- Every point of a closed disc is a manifold point. -/
theorem isManifoldPoint_of_univ (hS : IsClosedDisc (univ : Set S)) (x : S) : IsManifoldPoint x := by
  obtain ⟨e⟩ := hS
  exact (GM07.isSurface_of_homeo (e.trans (Homeomorph.Set.univ S))
    GM22.isSurface_closedUnitDisc).2.2 x

/-- If the open discs inside `F₁` and `F₂` are disjoint and some point is inside `F₁`, then no
point of `F₁` is inside `F₂`. -/
theorem not_insideOArc_of_mem (hS : IsClosedDisc (univ : Set S)) {F₁ F₂ : Set S}
    (hdisj : BoundDisjointOpenDiscs univ F₁ F₂) {y : S} (hy : InsideOArc univ F₁ y) {x : S}
    (hx : x ∈ F₁) : ¬ InsideOArc univ F₂ x := by
  rintro ⟨D₂, hD₂, hx₂⟩
  obtain ⟨D₁, hD₁, -⟩ := hy
  -- `x` is in the closure of the open disc inside `F₁`.
  have hxcl : x ∈ closure (discInt D₁) := by
    refine hD₁.2.1.subset_closure_discInt (discBd_subset D₁ ?_)
    rw [hD₁.2.2.1]
    exact hx
  -- The open disc inside `F₂` is a neighbourhood of `x`, so it meets the open disc inside `F₁`.
  have hopen : IsOpen (discInt D₂) := hD₂.2.1.isOpen_discInt (isManifoldPoint_of_univ hS)
  obtain ⟨z, hz₂, hz₁⟩ := mem_closure_iff.mp hxcl _ hopen hx₂
  exact Set.disjoint_left.mp hdisj (show InsideOArc univ F₁ z from ⟨D₁, hD₁, hz₁⟩)
    (show InsideOArc univ F₂ z from ⟨D₂, hD₂, hz₂⟩)

/-- Every vertex of a sleeve for `F` is inside `F` or on `F`. -/
theorem SleeveData.inside_or_mem {D : Drawing S} {F : Set S} (sd : SleeveData D univ F)
    {x : S} (hx : x ∈ (⋃ j, (sd.circuitDraw j).V) ∪ (⋃ i, (sd.spoke i).V)) :
    InsideOArc univ F x ∨ x ∈ F := by
  rcases hx with hx | hx
  · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    left
    refine sd.circuit_inside j x ?_
    rw [← (sd.isCircuit_draw j).2.2]
    exact (sd.circuitDraw j).V_subset_U hj
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    by_cases hxF : x ∈ F
    · exact Or.inr hxF
    · obtain ⟨-, -, -, -, -, -, -, henc, -⟩ := sd.isPath_spoke i
      exact Or.inl (henc x ⟨(sd.spoke i).V_subset_U hi, hxF⟩)

/-- A sleeve for `F` with a vertex has a point inside `F`: a point of its innermost circuit. -/
theorem SleeveData.exists_inside {D : Drawing S} {F : Set S} (sd : SleeveData D univ F)
    {x : S} (hx : x ∈ (⋃ j, (sd.circuitDraw j).V) ∪ (⋃ i, (sd.spoke i).V)) :
    ∃ y, InsideOArc univ F y := by
  rcases sd.inside_or_mem hx with h | -
  · exact ⟨x, h⟩
  rcases hx with hx | hx
  · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    refine ⟨x, sd.circuit_inside j x ?_⟩
    rw [← (sd.isCircuit_draw j).2.2]
    exact (sd.circuitDraw j).V_subset_U hj
  · obtain ⟨i, -⟩ := mem_iUnion.mp hx
    obtain ⟨hs, u, -, -, hu, -⟩ := sd.isPath_spoke i
    exact ⟨u, sd.circuit_inside ⟨0, hs⟩ u hu⟩

/-- A vertex of a sleeve for `F₁` is not inside `F₂`, when `F₁` and `F₂` bound disjoint open
discs. -/
theorem SleeveData.not_insideOArc (hS : IsClosedDisc (univ : Set S)) {D : Drawing S}
    {F₁ F₂ : Set S} (sd : SleeveData D univ F₁) (hdisj : BoundDisjointOpenDiscs univ F₁ F₂)
    {x : S} (hx : x ∈ (⋃ j, (sd.circuitDraw j).V) ∪ (⋃ i, (sd.spoke i).V)) :
    ¬ InsideOArc univ F₂ x := by
  rcases sd.inside_or_mem hx with h | h
  · exact fun h₂ => Set.disjoint_left.mp hdisj h h₂
  · obtain ⟨y, hy⟩ := sd.exists_inside hx
    exact not_insideOArc_of_mem hS hdisj hy h

end GM08
end GraphMinor
