module

public import GraphMinor.GM19.CutMap
import GraphMinor.GM08.Section18BranchGraphs
import GraphMinor.GM08.Section18GraphCut
import GraphMinor.Surface.Classification
import GraphMinor.Surface.CutLift

/-!
# Constructing the theta and whiskered-circle cuts

The theta is the union of two of its subcircles, so these circles together
with the old cuffs give its cut frame. A whiskered circle has one circle
and a joining line ending on a cuff. Their graph representations and
boundary contacts satisfy the proved finite-drawing cut construction.
These are the existence steps for types (v) and (vi) of VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

/-- Construct the boundary-disjoint theta cut of type (v) in VIII (18.2),
page 286. The measure bound is separate. -/
theorem exists_cutMap_of_theta_off_boundary {S : Type} [TopologicalSpace S]
    [ConnectedSpace S] (hS : IsSurface S) {P Q R : Set S} {u v : S} (huv : u ≠ v)
    (hP : IsLineWithEnds P u v) (hQ : IsLineWithEnds Q u v) (hR : IsLineWithEnds R u v)
    (hPQ : P ∩ Q = {u, v}) (hPR : P ∩ R = {u, v}) (hQR : Q ∩ R = {u, v})
    (hoff : (P ∪ Q ∪ R) ∩ bd S = ∅) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (ψ : Y → S),
      IsSurface Y ∧ GM19.IsCutMap ψ (P ∪ Q ∪ R) := by
  have : T2Space S := hS.2.1
  obtain ⟨V, E, hg, hno, hgr, _, _⟩ := exists_graph_theta huv hP hQ hR hPQ hPR hQR
  have hframe : GM19.IsCutFrame S (insert (P ∪ Q) (insert (P ∪ R) (cuffs S))) ∅ := by
    refine ⟨(((cuff_statement S hS).2.1).insert (P ∪ R)).insert (P ∪ Q), finite_empty,
      ?_, ?_, ?_⟩
    · rintro C (rfl | rfl | hC)
      · exact oArc_of_lines hP hQ hPQ
      · exact oArc_of_lines hP hR hPR
      · exact (cuff_statement S hS).2.2 C hC
    · exact fun C hC => Or.inr (Or.inr hC)
    · simp
  have hcover : bd S ∪ gr V E =
      ⋃₀ insert (P ∪ Q) (insert (P ∪ R) (cuffs S)) ∪ ⋃₀ (∅ : Set (Set S)) := by
    rw [hgr, sUnion_insert, sUnion_insert, sUnion_cuffs, sUnion_empty, union_empty]
    simp only [union_assoc, union_left_comm, union_comm]
    rw [← union_assoc P P, union_self]
  obtain ⟨Y, tY, ψ, hY, hcut⟩ := exists_cutMap_of_graph_frame hS hg hno
    (by rw [hgr, hoff]; exact empty_subset _) hframe hcover
  exact ⟨Y, tY, ψ, hY, hgr ▸ hcut⟩

/-- Construct the whiskered-circle cut of type (vi) in VIII (18.2),
page 286. The only boundary contact is the free end on its cuff.
The measure bound is separate. -/
theorem exists_cutMap_of_whiskered_circle {S : Type} [TopologicalSpace S]
    [ConnectedSpace S] (hS : IsSurface S) {A P C : Set S} {u v : S}
    (hA : IsOArc A) (hP : IsLineWithEnds P u v) (huv : u ≠ v) (hPA : P ∩ A = {u})
    (hC : C ∈ cuffs S) (hv : v ∈ C) (hbd : (A ∪ P) ∩ bd S = {v}) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (ψ : Y → S),
      IsSurface Y ∧ GM19.IsCutMap ψ (A ∪ P) := by
  have : T2Space S := hS.2.1
  obtain ⟨V, E, hg, hno, hgr, _, hvV⟩ := exists_graph_whiskered_circle hA hP huv hPA
  have huA : u ∈ A := (hPA.symm ▸ mem_singleton u : u ∈ P ∩ A).2
  have hframe : GM19.IsCutFrame S (insert A (cuffs S)) {P} := by
    refine ⟨((cuff_statement S hS).2.1).insert A, finite_singleton P, ?_, subset_insert _ _, ?_⟩
    · rintro D (rfl | hD)
      · exact hA
      · exact (cuff_statement S hS).2.2 D hD
    · rintro L rfl
      exact ⟨u, v, huv, hP, ⟨A, Or.inl rfl, huA⟩, ⟨C, Or.inr hC, hv⟩⟩
  have hcover : bd S ∪ gr V E = ⋃₀ insert A (cuffs S) ∪ ⋃₀ ({P} : Set (Set S)) := by
    rw [hgr, sUnion_insert, sUnion_cuffs, sUnion_singleton]
    ac_rfl
  obtain ⟨Y, tY, ψ, hY, hcut⟩ := exists_cutMap_of_graph_frame hS hg hno
    (by rw [hgr, hbd]; exact singleton_subset_iff.mpr hvV) hframe hcover
  exact ⟨Y, tY, ψ, hY, hgr ▸ hcut⟩

end GraphMinor.GM08
