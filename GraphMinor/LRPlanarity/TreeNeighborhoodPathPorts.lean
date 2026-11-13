module

public import GraphMinor.LRPlanarity.TreeNeighborhoodPlacement
public import GraphMinor.LRPlanarity.TreeNeighborhoodPathTubeInterior
import GraphMinor.LRPlanarity.TreeNeighborhoodPorts
import GraphMinor.LRPlanarity.TreeNeighborhoodCenterlines
import GraphMinor.Surface.DiscUnion
import GraphMinor.Surface.SurfaceGraph
import GraphMinor.LRPlanarity.TreeNeighborhoodSubdivisionSeparation

/-!
# Endpoint polygon tails of a subdivision path

Part IV, Section 7b of the planarity note makes the endpoint polygon avoid
all later segments of an incident edge. In the straight arrangement, a
simple path never revisits its start. Every piece after the first is
nonincident to that start, so the polygon avoids the rest of the path.
Its intersection and frontier port are therefore those of the first
straight piece. Reversing the path gives the target-end assertion.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface SimpleGraph

/-- Reversing a walk does not change its geometric image. -/
theorem walk_pathImage_reverse {V : Type*} {G : SimpleGraph V}
    (drawing : HP25.PlaneEmbedding G univ) {u v : V} (w : G.Walk u v) :
    drawing.pathImage w.reverse.support = drawing.pathImage w.support := by
  rw [walk_pathImage_eq_dart_union, walk_pathImage_eq_dart_union]
  apply Subset.antisymm
  · intro x hx
    obtain ⟨e, he'⟩ := mem_iUnion.mp hx
    obtain ⟨he, hxe⟩ := mem_iUnion.mp he'
    refine mem_iUnion.mpr ⟨e.symm, mem_iUnion.mpr ⟨Walk.mem_darts_reverse.mp he, ?_⟩⟩
    change x ∈ drawing.line e.snd e.fst
    rw [drawing.line_comm]
    exact hxe
  · intro x hx
    obtain ⟨e, he'⟩ := mem_iUnion.mp hx
    obtain ⟨he, hxe⟩ := mem_iUnion.mp he'
    refine mem_iUnion.mpr ⟨e.symm, mem_iUnion.mpr ⟨Walk.mem_darts_reverse.mpr ?_, ?_⟩⟩
    · simpa only [Dart.symm_symm] using he
    · change x ∈ drawing.line e.snd e.fst
      rw [drawing.line_comm]
      exact hxe

/-- A vertex polygon misses the image of every path not visiting its vertex,
when it misses every nonincident drawing edge. -/
theorem polygon_disjoint_walk_image {V : Type*} {G : SimpleGraph V}
    (drawing : HP25.PlaneEmbedding G univ) (P : V → Set ℂ)
    (haway : ∀ z u v, G.Adj u v → u ≠ z → v ≠ z → Disjoint (P z) (drawing.line u v))
    {u v z : V} (w : G.Walk u v) (hz : z ∉ w.support) :
    Disjoint (P z) (drawing.pathImage w.support) := by
  rw [Set.disjoint_left]
  intro x hxP hxw
  rw [walk_pathImage_eq_dart_union] at hxw
  obtain ⟨e, he'⟩ := mem_iUnion.mp hxw
  obtain ⟨he, hxe⟩ := mem_iUnion.mp he'
  obtain ⟨hfst, hsnd⟩ := walk_dart_ends_mem_support w he
  exact Set.disjoint_left.mp (haway z e.fst e.snd e.adj
    (fun h => hz (h ▸ hfst)) (fun h => hz (h ▸ hsnd))) hxP hxe

/-- Part IV, Section 7b: a nonempty simple subdivision path has one source
polygon frontier port and a straight initial tail inside that polygon. -/
theorem exists_path_source_polygon_port {V : Type*} {G : SimpleGraph V}
    (drawing : HP25.PlaneEmbedding G univ)
    (hstraight : ∀ u v, G.Adj u v → drawing.line u v = segment ℝ (drawing.pt u) (drawing.pt v))
    (angle : ∀ u, {v // G.Adj u v} → ℝ) (directions : V → Finset ℝ) (r : V → ℝ)
    (hangle : ∀ u v, eC (angle u v) =
      ‖drawing.pt v.val - drawing.pt u‖⁻¹ • (drawing.pt v.val - drawing.pt u))
    (hmem : ∀ u v, angle u v ∈ directions u) (hr : ∀ u, 0 < r u)
    (hlength : ∀ u v, u ≠ v → r u + r v < dist (drawing.pt u) (drawing.pt v))
    (haway : ∀ z u v, G.Adj u v → u ≠ z → v ≠ z → Disjoint
      (vertexPolygonAt (drawing.pt z) (directions z) (r z)) (drawing.line u v))
    {u t : V} (w : G.Walk u t) (hw : w.IsPath) (hnil : ¬w.Nil) :
    ∃ a : ℂ, a ≠ drawing.pt u ∧
      vertexPolygonAt (drawing.pt u) (directions u) (r u) ∩ drawing.pathImage w.support =
        segment ℝ (drawing.pt u) a ∧
      frontier (vertexPolygonAt (drawing.pt u) (directions u) (r u)) ∩
        drawing.pathImage w.support = {a} := by
  cases w with
  | nil => exact (hnil Walk.Nil.nil).elim
  | @cons u v t huv q =>
    let μ := angle u ⟨v,huv⟩
    let len := ‖drawing.pt v - drawing.pt u‖
    have hptne : drawing.pt u ≠ drawing.pt v := by
      intro he
      exact (G.ne_of_adj huv) (drawing.injOn (mem_univ _) (mem_univ _) he)
    have hcoord : drawing.pt u + eC μ * (len : ℂ) = drawing.pt v :=
      endpoint_eq_direction_length hptne (hangle _ _)
    have hsmall : r u < len := by
      have hsum := hlength u v (G.ne_of_adj huv)
      rw [dist_eq_norm, norm_sub_rev] at hsum
      exact lt_trans (lt_add_of_pos_right _ (hr v)) hsum
    have htail := vertexPolygonAt_straight_edge_tail (drawing.pt u) (directions u)
      (hr u) hsmall (hmem u ⟨v,huv⟩)
    change vertexPolygonAt (drawing.pt u) (directions u) (r u) ∩
      segment ℝ (drawing.pt u) (drawing.pt u + eC μ * (len : ℂ)) = _ ∧ _ at htail
    rw [hcoord, ← hstraight u v huv] at htail
    have hu : u ∉ q.support := (Walk.cons_isPath_iff huv q).mp hw |>.2
    have hdis := polygon_disjoint_walk_image drawing
      (fun z => vertexPolygonAt (drawing.pt z) (directions z) (r z)) haway q hu
    have hfrontsub : frontier (vertexPolygonAt (drawing.pt u) (directions u) (r u)) ⊆
        vertexPolygonAt (drawing.pt u) (directions u) (r u) :=
      fun x hx => (vertexPolygonAt_isClosedDisc _ _ (hr u)).isCompact.isClosed.closure_eq ▸
        frontier_subset_closure hx
    refine ⟨drawing.pt u + r u • eC μ, ?_, ?_, ?_⟩
    · intro he
      have hn : eC μ ≠ 0 := fun h => by
        have hh := norm_eC μ
        rw [h, norm_zero] at hh
        exact zero_ne_one hh
      have hh := congrArg (fun z : ℂ => z - drawing.pt u) he
      simp only [add_sub_cancel_left, sub_self] at hh
      exact smul_ne_zero (hr u).ne' hn hh
    · rw [Walk.support_cons, ← q.cons_tail_support, drawing.pathImage_cons_cons,
        q.cons_tail_support, inter_union_distrib_left, hdis.inter_eq, union_empty]
      exact htail.1
    · rw [Walk.support_cons, ← q.cons_tail_support, drawing.pathImage_cons_cons,
        q.cons_tail_support, inter_union_distrib_left,
        (hdis.mono_left hfrontsub).inter_eq, union_empty]
      exact htail.2

/-- Points on incident edge tails are distinct when each lies in its own
source polygon and differs from the original vertex point. This proves
port injectivity without choosing common angle representatives for paths. -/
theorem incidence_tail_points_injective {V : Type*} {G : SimpleGraph V}
    (drawing : HP25.PlaneEmbedding G univ) (P : V → Set ℂ)
    (point : {e : V × V // G.Adj e.1 e.2} → ℂ)
    (hPsep : Pairwise (fun u v => Disjoint (P u) (P v)))
    (hP : ∀ e, point e ∈ P e.val.1)
    (hline : ∀ e, point e ∈ drawing.line e.val.1 e.val.2)
    (hnot : ∀ e, point e ≠ drawing.pt e.val.1) : Function.Injective point := by
  intro e f he
  have hsource : e.val.1 = f.val.1 := by
    by_contra hne
    exact Set.disjoint_left.mp (hPsep hne) (hP e) (he.symm ▸ hP f)
  obtain ⟨⟨u,v⟩,huv⟩ := e
  obtain ⟨⟨u',w⟩,huw⟩ := f
  dsimp only at hsource
  subst u'
  have htarget : v = w := by
    by_contra hne
    have hedge : s(u,v) ≠ s(u,w) := by
      intro heq
      rcases Sym2.eq_iff.mp heq with ⟨_,ht⟩ | ⟨hs,_⟩
      · exact hne ht
      · exact (G.ne_of_adj huw) hs
    have hboth : point ⟨(u,v),huv⟩ ∈ drawing.line u v ∩ drawing.line u w :=
      ⟨hline ⟨(u,v),huv⟩, he.symm ▸ hline ⟨(u,w),huw⟩⟩
    have hu : drawing.pt u ∈ drawing.line u v ∩ drawing.line u w :=
      ⟨(drawing.isLine _ (mem_univ _) _ (mem_univ _) huv).left_mem,
        (drawing.isLine _ (mem_univ _) _ (mem_univ _) huw).left_mem⟩
    exact hnot ⟨(u,v),huv⟩ (drawing_distinct_edges_inter_subsingleton drawing huv huw hedge hboth hu)
  exact Subtype.ext (Prod.ext rfl htarget)

end GraphMinor.LRPlanarity
