module

public import GraphMinor.GM06.Defs
public import GraphMinor.Compute.GM06UsedEndpointSpec
import GraphMinor.GM06.Section5PathIncidentEdge
import GraphMinor.GM11.Walks

/-!
# The computed endpoint mask protects the given paths

The input path rows name their actual drawing edges. The endpoint
scan marks both ends of each such edge. Since every path vertex
meets a path edge, every vertex of the given linkage belongs to
the computed mask. These facts justify the protected-vertex tests
in the Reduction 2 scan of VI (5.7), page 133.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.Compute

/-- Interpreting the marked edge labels as the path edges proves that
the computed endpoint mask contains all path vertices. -/
theorem path_vertices_subset_computed_endpoint_mask
    {S : Type*} [TopologicalSpace S] {n : ℕ} {G P : Drawing S} {s t : S}
    (hP : IsPathDrawing P s t) (hPG : P.IsSubdrawing G)
    (es : List (Fin n × Fin n)) (vertex : Fin n → S) (edge : Fin es.length → Set S)
    (D : Finset (Fin (2 * es.length)))
    (hlinks : ∀ i : Fin es.length,
      ((⟨2 * i.val, by omega⟩ : Fin (2 * es.length)) ∈ D ∨
        (⟨2 * i.val + 1, by omega⟩ : Fin (2 * es.length)) ∈ D) →
      G.toGraph.IsLink (edge i) (vertex es[i.val].1) (vertex es[i.val].2))
    (hrows : ∀ e ∈ P.E, ∃ i : Fin es.length, edge i = e ∧
      ((⟨2 * i.val, by omega⟩ : Fin (2 * es.length)) ∈ D ∨
        (⟨2 * i.val + 1, by omega⟩ : Fin (2 * es.length)) ∈ D)) :
    P.V ⊆ vertex '' ((gm06UsedEndpointRows es D).flatten.toFinset : Set (Fin n)) := by
  intro a ha
  obtain ⟨e, he, b, hl⟩ := isPathDrawing_exists_incident_edge hP ha
  obtain ⟨i, hie, hused⟩ := hrows e he
  have hlG : G.toGraph.IsLink e a b := (hPG.isLink_iff he).mp hl
  have hiG := hlinks i hused
  rw [hie] at hiG
  rcases hlG.eq_and_eq_or_eq_and_eq hiG with h | h
  · refine ⟨es[i.val].1, (gm06UsedEndpointRows_mem_iff es D _).mpr ⟨i, hused, Or.inl rfl⟩, h.1.symm⟩
  · refine ⟨es[i.val].2, (gm06UsedEndpointRows_mem_iff es D _).mpr ⟨i, hused, Or.inr rfl⟩, h.1.symm⟩

/-- The same endpoint-mask computation protects each of the supplied
linkage paths, using their ordinary edge-label interpretation. -/
theorem linkage_vertices_subset_computed_endpoint_mask
    {k n : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (es : List (Fin n × Fin n)) (vertex : Fin n → ClosedCylinder)
    (edge : Fin es.length → Set ClosedCylinder)
    (D : Finset (Fin (2 * es.length)))
    (hlinks : ∀ i : Fin es.length,
      ((⟨2 * i.val, by omega⟩ : Fin (2 * es.length)) ∈ D ∨
        (⟨2 * i.val + 1, by omega⟩ : Fin (2 * es.length)) ∈ D) →
      G.toGraph.IsLink (edge i) (vertex es[i.val].1) (vertex es[i.val].2))
    (hrows : ∀ j : Fin k, ∀ e ∈ (L.pathDrawing j).E,
      ∃ i : Fin es.length, edge i = e ∧
        ((⟨2 * i.val, by omega⟩ : Fin (2 * es.length)) ∈ D ∨
          (⟨2 * i.val + 1, by omega⟩ : Fin (2 * es.length)) ∈ D)) :
    ∀ j : Fin k, (L.pathDrawing j).V ⊆
      vertex '' ((gm06UsedEndpointRows es D).flatten.toFinset : Set (Fin n)) := by
  intro j
  exact path_vertices_subset_computed_endpoint_mask (L.isPath j) (L.isSubdrawing j).1
    es vertex edge D hlinks (hrows j)

/-- If every marked edge label names an edge of a given path, every
computed vertex mark lies on a given path. -/
theorem computed_endpoint_mask_subset_linkage_vertices
    {k n : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (es : List (Fin n × Fin n)) (vertex : Fin n → ClosedCylinder)
    (edge : Fin es.length → Set ClosedCylinder)
    (D : Finset (Fin (2 * es.length)))
    (hlinks : ∀ i : Fin es.length,
      ((⟨2 * i.val, by omega⟩ : Fin (2 * es.length)) ∈ D ∨
        (⟨2 * i.val + 1, by omega⟩ : Fin (2 * es.length)) ∈ D) →
      G.toGraph.IsLink (edge i) (vertex es[i.val].1) (vertex es[i.val].2))
    (hrows : ∀ i : Fin es.length,
      ((⟨2 * i.val, by omega⟩ : Fin (2 * es.length)) ∈ D ∨
        (⟨2 * i.val + 1, by omega⟩ : Fin (2 * es.length)) ∈ D) →
      ∃ j : Fin k, edge i ∈ (L.pathDrawing j).E) :
    vertex '' ((gm06UsedEndpointRows es D).flatten.toFinset : Set (Fin n)) ⊆
      ⋃ j : Fin k, (L.pathDrawing j).V := by
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨i, hused, hv⟩ := (gm06UsedEndpointRows_mem_iff es D v).mp hv
  obtain ⟨j, hj⟩ := hrows i hused
  have hl := ((L.isSubdrawing j).1.isLink_iff hj).mpr (hlinks i hused)
  apply mem_iUnion.mpr
  refine ⟨j, ?_⟩
  rcases hv with rfl | rfl
  · exact hl.left_mem
  · exact hl.right_mem

/-- With the exact interpretation of the given path-edge labels, the
computed endpoint mask is exactly the union of the given path vertices. -/
theorem computed_endpoint_mask_eq_linkage_vertices
    {k n : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (es : List (Fin n × Fin n)) (vertex : Fin n → ClosedCylinder)
    (edge : Fin es.length → Set ClosedCylinder)
    (D : Finset (Fin (2 * es.length)))
    (hlinks : ∀ i : Fin es.length,
      ((⟨2 * i.val, by omega⟩ : Fin (2 * es.length)) ∈ D ∨
        (⟨2 * i.val + 1, by omega⟩ : Fin (2 * es.length)) ∈ D) →
      G.toGraph.IsLink (edge i) (vertex es[i.val].1) (vertex es[i.val].2))
    (hcover : ∀ j : Fin k, ∀ e ∈ (L.pathDrawing j).E,
      ∃ i : Fin es.length, edge i = e ∧
        ((⟨2 * i.val, by omega⟩ : Fin (2 * es.length)) ∈ D ∨
          (⟨2 * i.val + 1, by omega⟩ : Fin (2 * es.length)) ∈ D))
    (hrows : ∀ i : Fin es.length,
      ((⟨2 * i.val, by omega⟩ : Fin (2 * es.length)) ∈ D ∨
        (⟨2 * i.val + 1, by omega⟩ : Fin (2 * es.length)) ∈ D) →
      ∃ j : Fin k, edge i ∈ (L.pathDrawing j).E) :
    vertex '' ((gm06UsedEndpointRows es D).flatten.toFinset : Set (Fin n)) =
      ⋃ j : Fin k, (L.pathDrawing j).V := by
  refine subset_antisymm
    (computed_endpoint_mask_subset_linkage_vertices L es vertex edge D hlinks hrows) ?_
  exact iUnion_subset (linkage_vertices_subset_computed_endpoint_mask L es vertex edge D hlinks hcover)

end GraphMinor.GM06
