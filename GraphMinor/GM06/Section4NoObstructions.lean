module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section3Basic

/-!
# Consequences of excluding the obstructions in VI (4.2)

For a boundary segment routed in H, exclusion of (4.1)(i) supplies the
minimal boundary path. Exclusion of Reduction 2(ii) puts its vertices
on the surface boundary. Exclusion of (4.1)(ii) keeps them in the chosen
component, and exclusion of (4.1)(iii) identifies the subpaths to the
fixed terminal vertex up to homotopy. These are the steps used on
page 126 to place the path in G′.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

universe u

/-- Excluding (4.1)(i) supplies the minimal boundary path for a routed
boundary segment in the proof of VI (4.2). -/
theorem exists_minimalBoundaryPath_of_not_condition41
    {S : Type u} [TopologicalSpace S] {G H Hst : Drawing S} {A : Set S} {s t : S}
    (hno : ¬ Section4Condition41Applies G H)
    (hA : A ∈ segmentsOf (bd S) (H.V ∩ bd S))
    (hs : s ∈ H.V ∩ bd S) (ht : t ∈ H.V ∩ bd S) (hst : s ≠ t)
    (hsA : s ∈ closure A) (htA : t ∈ closure A)
    (hHst : IsSubpathOf H Hst s t) (hHA : PathHomotopicToArc Hst s t A) :
    ∃ P : Drawing S, IsMinimalBoundaryPath G s t A P := by
  by_contra hn
  exact hno ⟨A, hA, s, hs, t, ht, hst, hsA, htA, ⟨Hst, hHst, hHA⟩, Or.inl hn⟩

/-- Excluding Reduction 2(ii) puts every vertex of the minimal boundary
path on the surface boundary, as used in VI (4.2), page 126. -/
theorem minimalBoundaryPath_vertices_boundary_of_not_reduction2
    {S : Type u} [TopologicalSpace S] {G H Hst P : Drawing S} {A : Set S} {s t : S}
    (hno : ¬ Section4Reduction2Applies G H)
    (hA : A ∈ segmentsOf (bd S) (H.V ∩ bd S))
    (hs : s ∈ H.V ∩ bd S) (ht : t ∈ H.V ∩ bd S) (hst : s ≠ t)
    (hsA : s ∈ closure A) (htA : t ∈ closure A)
    (hHst : IsSubpathOf H Hst s t) (hHA : PathHomotopicToArc Hst s t A)
    (hP : IsMinimalBoundaryPath G s t A P) : P.V ⊆ bd S := by
  intro v hv
  by_contra hvbd
  exact hno ⟨A, hA, s, hs, t, ht, hst, hsA, htA, ⟨Hst, hHst, hHA⟩,
    P, hP, Or.inr (Or.inl ⟨v, hv, hvbd⟩)⟩

/-- Excluding (4.1)(ii) and Reduction 2(ii) keeps all vertices of the
minimal boundary path among the boundary vertices of the chosen
component. This is the vertex assertion for G′ in VI (4.2), page 126. -/
theorem minimalBoundaryPath_vertices_component_of_no_obstructions
    {S : Type u} [TopologicalSpace S] {G H Hst P : Drawing S} {A : Set S} {s t : S}
    (hno41 : ¬ Section4Condition41Applies G H) (hno2 : ¬ Section4Reduction2Applies G H)
    (hbd : H.V ∩ bd S = G.V ∩ bd S)
    {K : Graph S (Set S)} (hK : IsGraphComponent K H.toGraph) (hsK : s ∈ Graph.vertexSet K)
    (hA : A ∈ segmentsOf (bd S) (H.V ∩ bd S))
    (hs : s ∈ H.V ∩ bd S) (ht : t ∈ H.V ∩ bd S) (hst : s ≠ t)
    (hsA : s ∈ closure A) (htA : t ∈ closure A)
    (hHst : IsSubpathOf H Hst s t) (hHA : PathHomotopicToArc Hst s t A)
    (hP : IsMinimalBoundaryPath G s t A P) : P.V ⊆ Graph.vertexSet K ∩ bd S := by
  have hPVbd := minimalBoundaryPath_vertices_boundary_of_not_reduction2 hno2
    hA hs ht hst hsA htA hHst hHA hP
  intro v hv
  have hvbd : v ∈ bd S := hPVbd hv
  have hvH : v ∈ H.V ∩ bd S := hbd.symm ▸ ⟨hP.1.1 hv, hvbd⟩
  refine ⟨?_, hvbd⟩
  by_contra hvK
  let L := compOf H.toGraph v
  have hL : IsGraphComponent L H.toGraph := isGraphComponent_compOf hvH.1
  have hvL : v ∈ Graph.vertexSet L := self_mem_reachSet hvH.1
  have hKL : K ≠ L := by intro he; apply hvK; rw [he]; exact hvL
  have hsL : s ∉ Graph.vertexSet L := fun hsL =>
    Set.disjoint_left.mp (hK.disjoint_vertexSet_of_ne hL hKL) hsK hsL
  exact hno41 ⟨A, hA, s, hs, t, ht, hst, hsA, htA, ⟨Hst, hHst, hHA⟩,
    Or.inr (Or.inl ⟨P, hP, L, hL, Or.inl hsL, v, hv, hvL, hvbd⟩)⟩

/-- Excluding (4.1)(iii) identifies the forest path and the minimal
boundary subpath from a boundary vertex to the terminal vertex. -/
theorem pathsHomotopic_of_not_condition41
    {S : Type u} [TopologicalSpace S]
    {G H Hst P Hvt Qvt : Drawing S} {A : Set S} {s t v : S}
    (hno : ¬ Section4Condition41Applies G H)
    (hA : A ∈ segmentsOf (bd S) (H.V ∩ bd S))
    (hs : s ∈ H.V ∩ bd S) (ht : t ∈ H.V ∩ bd S) (hst : s ≠ t)
    (hsA : s ∈ closure A) (htA : t ∈ closure A)
    (hHst : IsSubpathOf H Hst s t) (hHA : PathHomotopicToArc Hst s t A)
    (hP : IsMinimalBoundaryPath G s t A P) (hv : v ∈ P.V ∩ bd S)
    (hHvt : IsSubpathOf H Hvt v t) (hQvt : IsSubpathOf P Qvt v t) :
    PathsHomotopic Hvt Qvt v t := by
  by_contra hn
  exact hno ⟨A, hA, s, hs, t, ht, hst, hsA, htA, ⟨Hst, hHst, hHA⟩,
    Or.inr (Or.inr ⟨P, hP, v, hv, Hvt, Qvt, hHvt, hQvt, hn⟩)⟩

end GraphMinor.GM06
