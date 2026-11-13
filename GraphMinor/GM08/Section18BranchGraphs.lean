module

public import GraphMinor.Surface.SurfaceGraph
import GraphMinor.GM08.Section18CircleGraph
import GraphMinor.Surface.CutLift

/-!
# Finite graphs for the theta and whiskered-circle shapes

For a theta, represent the circle formed by two branches, mark their ends,
and add the third branch as an edge. For a whiskered circle, mark the
attachment point, add the free end as a vertex, and add the whisker as an
edge. The resulting graphs have no isolated vertices. These prepare the
last two branched cut constructions in VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe w

/-- A theta has a finite graph representation with its two branch points
marked. This prepares type (v) in VIII (18.2), page 286. -/
theorem exists_graph_theta {S : Type w} [TopologicalSpace S] [T2Space S]
    {P Q R : Set S} {u v : S} (huv : u ≠ v)
    (hP : IsLineWithEnds P u v) (hQ : IsLineWithEnds Q u v) (hR : IsLineWithEnds R u v)
    (hPQ : P ∩ Q = {u, v}) (hPR : P ∩ R = {u, v}) (hQR : Q ∩ R = {u, v}) :
    ∃ V : Set S, ∃ E : Set (Set S), IsGraph V E ∧ V ⊆ ⋃₀ E ∧
      gr V E = P ∪ Q ∪ R ∧ u ∈ V ∧ v ∈ V := by
  have hcircle := oArc_of_lines hP hQ hPQ
  have hmarks : ({u, v} : Set S) ⊆ P ∪ Q := by
    rintro x (rfl | rfl)
    · exact Or.inl hP.left_mem
    · exact Or.inl hP.right_mem
  obtain ⟨V, E, hg, hno, hgr, hmarked⟩ := exists_graph_oArc_with_finite_marks
    hcircle ((finite_singleton v).insert u) hmarks
  have huV : u ∈ V := hmarked (Or.inl rfl)
  have hvV : v ∈ V := hmarked (Or.inr rfl)
  have hmeet : R ∩ gr V E = {u, v} := by
    rw [hgr, inter_union_distrib_left, inter_comm R P, hPR, inter_comm R Q, hQR, union_self]
  obtain ⟨hg', hgr'⟩ := hg.add_arc huv hR huV hvV hmeet
  refine ⟨V, insert R E, hg', hno.trans (sUnion_mono (subset_insert _ _)), ?_, huV, hvV⟩
  rw [hgr', hgr]

/-- A whiskered circle has a finite graph representation with its
attachment and free end marked. This prepares type (vi) in VIII (18.2),
page 286. -/
theorem exists_graph_whiskered_circle {S : Type w} [TopologicalSpace S] [T2Space S]
    {A P : Set S} {u v : S} (hA : IsOArc A) (hP : IsLineWithEnds P u v)
    (huv : u ≠ v) (hPA : P ∩ A = {u}) :
    ∃ V : Set S, ∃ E : Set (Set S), IsGraph V E ∧ V ⊆ ⋃₀ E ∧
      gr V E = A ∪ P ∧ u ∈ V ∧ v ∈ V := by
  have huA : u ∈ A := (hPA.symm ▸ mem_singleton u : u ∈ P ∩ A).2
  obtain ⟨V, E, hg, hno, hgr, hmarked⟩ := exists_graph_oArc_with_finite_marks
    hA (finite_singleton u) (singleton_subset_iff.mpr huA)
  obtain ⟨E', hg', hgr', hEE'⟩ := hg.add_point v
  have huV : u ∈ insert v V := mem_insert_of_mem v (hmarked (mem_singleton u))
  have hvV : v ∈ insert v V := mem_insert _ _
  have hmeet : P ∩ gr (insert v V) E' = {u, v} := by
    rw [hgr', hgr]
    apply Subset.antisymm
    · rintro x ⟨hxP, rfl | hxA⟩
      · exact Or.inr rfl
      · exact Or.inl (hPA.subset ⟨hxP, hxA⟩)
    · rintro x (rfl | rfl)
      · exact ⟨hP.left_mem, mem_insert_of_mem v huA⟩
      · exact ⟨hP.right_mem, mem_insert _ _⟩
  obtain ⟨hg'', hgr''⟩ := hg'.add_arc huv hP huV hvV hmeet
  refine ⟨insert v V, insert P E', hg'', ?_, ?_, huV, hvV⟩
  · rintro x (rfl | hxV)
    · exact ⟨P, mem_insert _ _, hP.right_mem⟩
    · exact sUnion_mono (subset_insert _ _) (hEE' (hno hxV))
  · rw [hgr'', hgr', hgr, insert_union]
    exact insert_eq_of_mem (show v ∈ A ∪ P from Or.inr hP.right_mem)

end GraphMinor.GM08
