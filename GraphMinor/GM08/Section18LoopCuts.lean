module

public import GraphMinor.GM19.CutMap
import GraphMinor.GM08.Section18LoopGraphs
import GraphMinor.GM08.Section18GraphCut
import GraphMinor.Surface.Classification

/-!
# Constructing the cuts for the two-loop shapes

The finite graph representations of a barbell and of two meeting circles
have no isolated vertices. If the shapes miss the boundary, every edge is
an interior edge. Their circles together with the cuffs, and the barbell's
joining line, give the input to the proved graph-cut construction. These
are the existence parts of type (iv) in VIII (18.2); their measure bounds
are separate.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

/-- A boundary-disjoint barbell has an actual finite-fibre cut map. This
constructs the first type (iv) cut of VIII (18.2), page 286, without yet
asserting the measure decrease. -/
theorem exists_cutMap_of_barbell_off_boundary {S : Type} [TopologicalSpace S]
    [ConnectedSpace S] (hS : IsSurface S) {A B P : Set S} {u v : S}
    (hA : IsOArc A) (hB : IsOArc B) (hAB : Disjoint A B)
    (hP : IsLineWithEnds P u v) (hu : u ∈ A) (hv : v ∈ B)
    (hPA : P ∩ A = {u}) (hPB : P ∩ B = {v})
    (hoff : (A ∪ B ∪ P) ∩ bd S = ∅) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (ψ : Y → S),
      IsSurface Y ∧ GM19.IsCutMap ψ (A ∪ B ∪ P) := by
  have : T2Space S := hS.2.1
  obtain ⟨V, E, hg, hno, hgr, _, _⟩ := exists_graph_barbell hA hB hAB hP hu hv hPA hPB
  have huv : u ≠ v := fun he => disjoint_left.mp hAB hu (he.symm ▸ hv)
  have hframe : GM19.IsCutFrame S (insert A (insert B (cuffs S))) {P} := by
    refine ⟨(((cuff_statement S hS).2.1).insert B).insert A, finite_singleton P,
      ?_, ?_, ?_⟩
    · rintro C (rfl | rfl | hC)
      · exact hA
      · exact hB
      · exact (cuff_statement S hS).2.2 C hC
    · exact fun C hC => Or.inr (Or.inr hC)
    · rintro L rfl
      exact ⟨u, v, huv, hP, ⟨A, Or.inl rfl, hu⟩, ⟨B, Or.inr (Or.inl rfl), hv⟩⟩
  have hcover : bd S ∪ gr V E = ⋃₀ insert A (insert B (cuffs S)) ∪ ⋃₀ ({P} : Set (Set S)) := by
    rw [hgr, sUnion_insert, sUnion_insert, sUnion_cuffs, sUnion_singleton]
    ac_rfl
  obtain ⟨Y, tY, ψ, hY, hcut⟩ := exists_cutMap_of_graph_frame hS hg hno
    (by rw [hgr, hoff]; exact empty_subset _) hframe hcover
  exact ⟨Y, tY, ψ, hY, hgr ▸ hcut⟩

/-- Two boundary-disjoint circles meeting at one point have an actual
finite-fibre cut map. This constructs the other type (iv) cut of VIII
(18.2), page 286, without yet asserting the measure decrease. -/
theorem exists_cutMap_of_meeting_circles_off_boundary {S : Type} [TopologicalSpace S]
    [ConnectedSpace S] (hS : IsSurface S) {A B : Set S} {u : S}
    (hA : IsOArc A) (hB : IsOArc B) (hAB : A ∩ B = {u})
    (hoff : (A ∪ B) ∩ bd S = ∅) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (ψ : Y → S),
      IsSurface Y ∧ GM19.IsCutMap ψ (A ∪ B) := by
  have : T2Space S := hS.2.1
  obtain ⟨V, E, hg, hno, hgr, _⟩ := exists_graph_meeting_circles hA hB hAB
  have hframe : GM19.IsCutFrame S (insert A (insert B (cuffs S))) ∅ := by
    refine ⟨(((cuff_statement S hS).2.1).insert B).insert A, finite_empty, ?_, ?_, ?_⟩
    · rintro C (rfl | rfl | hC)
      · exact hA
      · exact hB
      · exact (cuff_statement S hS).2.2 C hC
    · exact fun C hC => Or.inr (Or.inr hC)
    · simp
  have hcover : bd S ∪ gr V E = ⋃₀ insert A (insert B (cuffs S)) ∪ ⋃₀ (∅ : Set (Set S)) := by
    rw [hgr, sUnion_insert, sUnion_insert, sUnion_cuffs, sUnion_empty, union_empty]
    ac_rfl
  obtain ⟨Y, tY, ψ, hY, hcut⟩ := exists_cutMap_of_graph_frame hS hg hno
    (by rw [hgr, hoff]; exact empty_subset _) hframe hcover
  exact ⟨Y, tY, ψ, hY, hgr ▸ hcut⟩

end GraphMinor.GM08
