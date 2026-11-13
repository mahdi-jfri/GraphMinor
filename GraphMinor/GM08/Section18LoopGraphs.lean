module

public import GraphMinor.Surface.SurfaceGraph
import GraphMinor.GM08.Section18CircleGraph
import GraphMinor.GM08.Section18GraphUnion

/-!
# Finite graphs for the two-loop schism shapes

Represent each circle by a finite graph with its attachment point marked.
Disjoint circles combine as disjoint graphs, after which the connecting
line is an extra edge. Circles meeting at one point combine along that
vertex. These are the graph preparations for type (iv) of VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe w

private theorem gr_union {S : Type w} [TopologicalSpace S]
    (V W : Set S) (E D : Set (Set S)) :
    gr (V ∪ W) (E ∪ D) = gr V E ∪ gr W D := by
  simp only [gr, sUnion_union]
  ac_rfl

private theorem no_isolated_union {S : Type w} {V W : Set S} {E D : Set (Set S)}
    (hV : V ⊆ ⋃₀ E) (hW : W ⊆ ⋃₀ D) : V ∪ W ⊆ ⋃₀ (E ∪ D) := by
  rintro x (hx | hx)
  · exact sUnion_mono subset_union_left (hV hx)
  · exact sUnion_mono subset_union_right (hW hx)

/-- A barbell has a finite graph representation with its attachment points
as vertices and no isolated vertices. This prepares type (iv) in the
triangulation argument of VIII (18.2), page 286. -/
theorem exists_graph_barbell {S : Type w} [TopologicalSpace S] [T2Space S]
    {A B P : Set S} {u v : S} (hA : IsOArc A) (hB : IsOArc B)
    (hAB : Disjoint A B) (hP : IsLineWithEnds P u v) (hu : u ∈ A) (hv : v ∈ B)
    (hPA : P ∩ A = {u}) (hPB : P ∩ B = {v}) :
    ∃ V : Set S, ∃ E : Set (Set S), IsGraph V E ∧ V ⊆ ⋃₀ E ∧
      gr V E = A ∪ B ∪ P ∧ u ∈ V ∧ v ∈ V := by
  obtain ⟨V, E, hg, hnoV, hgrA, hmarkU⟩ := exists_graph_oArc_with_finite_marks
    hA (finite_singleton u) (singleton_subset_iff.mpr hu)
  obtain ⟨W, D, hh, hnoW, hgrB, hmarkV⟩ := exists_graph_oArc_with_finite_marks
    hB (finite_singleton v) (singleton_subset_iff.mpr hv)
  have hinter : gr V E ∩ gr W D ⊆ V ∩ W := by
    rw [hgrA, hgrB]
    exact fun x hx => (disjoint_left.mp hAB hx.1 hx.2).elim
  have hgraph := isGraph_union_of_inter_subset_vertices hg hh hinter
  have hgr : gr (V ∪ W) (E ∪ D) = A ∪ B := by rw [gr_union, hgrA, hgrB]
  have huV : u ∈ V ∪ W := Or.inl (hmarkU (mem_singleton u))
  have hvV : v ∈ V ∪ W := Or.inr (hmarkV (mem_singleton v))
  have huv : u ≠ v := fun he => disjoint_left.mp hAB hu (he.symm ▸ hv)
  have hmeet : P ∩ gr (V ∪ W) (E ∪ D) = {u, v} := by
    rw [hgr, inter_union_distrib_left, hPA, hPB]
    ext x
    simp only [mem_union, mem_singleton_iff, mem_insert_iff]
  obtain ⟨hgraph', hgr'⟩ := hgraph.add_arc huv hP huV hvV hmeet
  refine ⟨V ∪ W, insert P (E ∪ D), hgraph', ?_, ?_, huV, hvV⟩
  · exact (no_isolated_union hnoV hnoW).trans (sUnion_mono (subset_insert _ _))
  · rw [hgr', hgr]

/-- Two circles meeting at one point have a finite graph representation
with that attachment point marked. This prepares the other type (iv)
shape in VIII (18.2), page 286. -/
theorem exists_graph_meeting_circles {S : Type w} [TopologicalSpace S] [T2Space S]
    {A B : Set S} {u : S} (hA : IsOArc A) (hB : IsOArc B) (hAB : A ∩ B = {u}) :
    ∃ V : Set S, ∃ E : Set (Set S), IsGraph V E ∧ V ⊆ ⋃₀ E ∧ gr V E = A ∪ B ∧ u ∈ V := by
  have huA : u ∈ A := (hAB.symm ▸ mem_singleton u : u ∈ A ∩ B).1
  have huB : u ∈ B := (hAB.symm ▸ mem_singleton u : u ∈ A ∩ B).2
  obtain ⟨V, E, hg, hnoV, hgrA, hmarkV⟩ := exists_graph_oArc_with_finite_marks
    hA (finite_singleton u) (singleton_subset_iff.mpr huA)
  obtain ⟨W, D, hh, hnoW, hgrB, hmarkW⟩ := exists_graph_oArc_with_finite_marks
    hB (finite_singleton u) (singleton_subset_iff.mpr huB)
  have huV : u ∈ V := hmarkV (mem_singleton u)
  have huW : u ∈ W := hmarkW (mem_singleton u)
  have hinter : gr V E ∩ gr W D ⊆ V ∩ W := by
    rw [hgrA, hgrB, hAB]
    rintro x rfl
    exact ⟨huV, huW⟩
  refine ⟨V ∪ W, E ∪ D, isGraph_union_of_inter_subset_vertices hg hh hinter,
    no_isolated_union hnoV hnoW, ?_, Or.inl huV⟩
  rw [gr_union, hgrA, hgrB]

end GraphMinor.GM08
