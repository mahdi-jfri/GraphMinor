module

public import GraphMinor.LRPlanarity.TreeNeighborhoodPathTubeInterior
import GraphMinor.Surface.SurfaceGraph

/-!
# Distinct original edges have separated subdivision paths

Part IV, Section 7b of the planarity note subdivides edges without
changing their images. An internal vertex on one original edge cannot lie
on another, since drawing edges meet only at common original endpoints.
Two distinct original edges also cannot share a straight subdivision piece:
the two ends of that piece would give two distinct points in their
intersection, which has at most one point.
-/

public section
namespace GraphMinor.LRPlanarity

open Set SimpleGraph

private theorem pair_eq_of_distinct_mem {A : Type*} {a b x y : A}
    (hx : x ∈ ({a,b} : Set A)) (hy : y ∈ ({a,b} : Set A)) (hne : x ≠ y) :
    s(x,y) = s(a,b) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact (hne rfl).elim
  · rfl
  · exact Sym2.eq_swap
  · exact (hne rfl).elim

/-- Distinct edges of a plane drawing have at most one common point. -/
theorem drawing_distinct_edges_inter_subsingleton {V : Type*} {G : SimpleGraph V}
    (drawing : HP25.PlaneEmbedding G univ) {a b c d : V}
    (hab : G.Adj a b) (hcd : G.Adj c d) (hne : s(a,b) ≠ s(c,d)) :
    (drawing.line a b ∩ drawing.line c d).Subsingleton := by
  intro x hx y hy
  have hinter := drawing.inter a (mem_univ _) b (mem_univ _) c (mem_univ _) d (mem_univ _)
    hab hcd hne
  obtain ⟨u, hu, rfl⟩ := hinter hx
  obtain ⟨v, hv, rfl⟩ := hinter hy
  by_cases huv : u = v
  · exact congrArg drawing.pt huv
  · exact (hne ((pair_eq_of_distinct_mem hu.1 hv.1 huv).symm.trans
      (pair_eq_of_distinct_mem hu.2 hv.2 huv))).elim

/-- Part IV, Section 7b: exact simple subdivision paths of distinct original
edges have no common straight piece, and no internal vertex of either path
lies on the other. The map of original vertices is specified by its point
coordinates in the two drawings. -/
theorem original_edge_subdivision_paths_separated {U V : Type*}
    {G : SimpleGraph U} {H : SimpleGraph V}
    (original : HP25.PlaneEmbedding G univ) (subdivision : HP25.PlaneEmbedding H univ)
    (vertex : U → V) (hpoint : ∀ u, subdivision.pt (vertex u) = original.pt u)
    {a b c d : U} (hab : G.Adj a b) (hcd : G.Adj c d) (hne : s(a,b) ≠ s(c,d))
    (w : H.Walk (vertex a) (vertex b)) (q : H.Walk (vertex c) (vertex d))
    (hw : w.IsPath) (hq : q.IsPath)
    (himagew : subdivision.pathImage w.support = original.line a b)
    (himageq : subdivision.pathImage q.support = original.line c d) :
    (∀ z ∈ w.support.tail.dropLast, z ∉ q.support) ∧
    (∀ z ∈ q.support.tail.dropLast, z ∉ w.support) ∧
    (∀ e ∈ w.darts, ∀ f ∈ q.darts, s(e.fst,e.snd) ≠ s(f.fst,f.snd)) := by
  have hvab : vertex a ≠ vertex b := by
    intro he
    exact (G.ne_of_adj hab) (original.injOn (mem_univ _) (mem_univ _)
      ((hpoint a).symm.trans ((congrArg subdivision.pt he).trans (hpoint b))))
  have hvcd : vertex c ≠ vertex d := by
    intro he
    exact (G.ne_of_adj hcd) (original.injOn (mem_univ _) (mem_univ _)
      ((hpoint c).symm.trans ((congrArg subdivision.pt he).trans (hpoint d))))
  have hwnil : ¬w.Nil := fun h => hvab (hw.nil_iff_eq.mp h)
  have hqnil : ¬q.Nil := fun h => hvcd (hq.nil_iff_eq.mp h)
  have hwon : ∀ z ∈ w.support, subdivision.pt z ∈ original.line a b := by
    intro z hz
    rw [← himagew]
    exact path_vertex_mem_pathImage subdivision w hw hwnil hz
  have hqon : ∀ z ∈ q.support, subdivision.pt z ∈ original.line c d := by
    intro z hz
    rw [← himageq]
    exact path_vertex_mem_pathImage subdivision q hq hqnil hz
  have hinter := original.inter a (mem_univ _) b (mem_univ _) c (mem_univ _) d (mem_univ _)
    hab hcd hne
  refine ⟨?_, ?_, ?_⟩
  · intro z hz hzq
    obtain ⟨u, hu, he⟩ := hinter ⟨hwon z (walk_internal_mem_support w hz), hqon z hzq⟩
    rcases hu.1 with hua | hub
    · have hza : z = vertex a := subdivision.injOn (mem_univ _) (mem_univ _)
        (he.symm.trans ((congrArg original.pt hua).trans (hpoint a).symm))
      exact path_start_not_mem_internal hw (hza ▸ hz)
    · have hzb : z = vertex b := subdivision.injOn (mem_univ _) (mem_univ _)
        (he.symm.trans ((congrArg original.pt hub).trans (hpoint b).symm))
      exact path_end_not_mem_internal hw (hzb ▸ hz)
  · intro z hz hzw
    obtain ⟨u, hu, he⟩ := hinter ⟨hwon z hzw, hqon z (walk_internal_mem_support q hz)⟩
    rcases hu.2 with huc | hud
    · have hzc : z = vertex c := subdivision.injOn (mem_univ _) (mem_univ _)
        (he.symm.trans ((congrArg original.pt huc).trans (hpoint c).symm))
      exact path_start_not_mem_internal hq (hzc ▸ hz)
    · have hzd : z = vertex d := subdivision.injOn (mem_univ _) (mem_univ _)
        (he.symm.trans ((congrArg original.pt hud).trans (hpoint d).symm))
      exact path_end_not_mem_internal hq (hzd ▸ hz)
  · intro e he f hf heq
    have hlineeq : subdivision.line e.fst e.snd = subdivision.line f.fst f.snd := by
      rcases Sym2.eq_iff.mp heq with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · rw [hs, ht]
      · rw [hs, ht, subdivision.line_comm]
    have hew : subdivision.line e.fst e.snd ⊆ original.line a b := by
      rw [← himagew, walk_pathImage_eq_dart_union]
      intro x hx
      exact mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨he, hx⟩⟩
    have hfq : subdivision.line f.fst f.snd ⊆ original.line c d := by
      rw [← himageq, walk_pathImage_eq_dart_union]
      intro x hx
      exact mem_iUnion.mpr ⟨f, mem_iUnion.mpr ⟨hf, hx⟩⟩
    have hends := subdivision.isLine e.fst (mem_univ _) e.snd (mem_univ _) e.adj
    have hfst : subdivision.pt e.fst ∈ original.line a b ∩ original.line c d :=
      ⟨hew hends.left_mem, hfq (hlineeq ▸ hends.left_mem)⟩
    have hsnd : subdivision.pt e.snd ∈ original.line a b ∩ original.line c d :=
      ⟨hew hends.right_mem, hfq (hlineeq ▸ hends.right_mem)⟩
    have hpoints := drawing_distinct_edges_inter_subsingleton original hab hcd hne hfst hsnd
    exact (H.ne_of_adj e.adj) (subdivision.injOn (mem_univ _) (mem_univ _) hpoints)

end GraphMinor.LRPlanarity
