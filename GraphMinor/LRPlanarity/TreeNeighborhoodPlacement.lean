module

public import GraphMinor.LRPlanarity.TreeNeighborhoodPolygons
import GraphMinor.LRPlanarity.PolygonalizationDiscs
import Mathlib.Tactic.Linarith

/-!
# Simultaneous placement of small vertex polygons

Part IV, Section 7b of the planarity note makes all vertex polygons small
enough to be disjoint and to avoid the nonincident and later incident edge
pieces. Those pieces form compact forbidden sets missing the vertex point.
The polygon of radius r lies inside the disc of radius 2r, so shrinking the
separated vertex discs leaves room for every polygon.
-/

@[expose] public section
namespace GraphMinor.LRPlanarity

open Set Metric Topology Surface

/-- Part IV, Section 7b: the vertex polygon translated to its vertex point. -/
def vertexPolygonAt (center : ℂ) (directions : Finset ℝ) (r : ℝ) : Set ℂ :=
  (fun z => center + z) '' vertexPolygon directions r

/-- A translated positive-radius vertex polygon is a closed disc. -/
theorem vertexPolygonAt_isClosedDisc (center : ℂ) (directions : Finset ℝ) {r : ℝ}
    (hr : 0 < r) : IsClosedDisc (vertexPolygonAt center directions r) := by
  obtain ⟨hdisc, _⟩ := ((vertexPolygon_isClosedDisc directions hr).1).image
    (f := fun z => center + z) (f' := fun z => z - center)
    (continuous_const.add continuous_id).continuousOn
    (continuous_id.sub continuous_const).continuousOn
    (fun z _ => by simp)
  exact hdisc

/-- The vertex point is inside its positive-radius vertex polygon. -/
theorem center_mem_interior_vertexPolygonAt (center : ℂ) (directions : Finset ℝ) {r : ℝ}
    (hr : 0 < r) : center ∈ interior (vertexPolygonAt center directions r) := by
  have hzero : (0 : ℂ) ∈ interior (vertexPolygon directions r) :=
    mem_interior.mpr ⟨ball (0 : ℂ) r, ball_subset_vertexPolygon directions r,
      isOpen_ball, mem_ball_self hr⟩
  have hm := mem_image_of_mem (Homeomorph.addLeft center) hzero
  rw [(Homeomorph.addLeft center).image_interior] at hm
  change center + 0 ∈ interior ((fun z => center + z) '' vertexPolygon directions r) at hm
  simpa only [vertexPolygonAt, add_zero] using hm

/-- A translated vertex polygon remains inside the doubled-radius disc. -/
theorem vertexPolygonAt_subset_closedBall (center : ℂ) (directions : Finset ℝ) (r : ℝ) :
    vertexPolygonAt center directions r ⊆ closedBall center (2 * r) := by
  rintro x ⟨z, hz, rfl⟩
  have hm := vertexPolygon_subset_closedBall directions r hz
  rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
  exact mem_closedBall_zero_iff.mp hm

/-- Part IV, Section 7b: choose all vertex polygons disjoint and small enough
to miss the prescribed compact forbidden sets. -/
theorem exists_small_vertex_polygons {ι : Type*} [Finite ι]
    (point : ι → ℂ) (hinj : Function.Injective point) (directions : ι → Finset ℝ)
    (K : ι → Set ℂ) (hK : ∀ v, IsCompact (K v)) (hmiss : ∀ v, point v ∉ K v) :
    ∃ r : ι → ℝ,
      (∀ v, 0 < r v ∧ IsClosedDisc (vertexPolygonAt (point v) (directions v) (r v)) ∧
        point v ∈ interior (vertexPolygonAt (point v) (directions v) (r v)) ∧
        Disjoint (vertexPolygonAt (point v) (directions v) (r v)) (K v)) ∧
      Pairwise (fun u v => Disjoint (vertexPolygonAt (point u) (directions u) (r u))
        (vertexPolygonAt (point v) (directions v) (r v))) := by
  obtain ⟨R, hR, hballs⟩ := exists_separated_vertex_discs point hinj K hK hmiss
  let r : ι → ℝ := fun v => R v / 3
  have hr : ∀ v, 0 < r v := fun v => div_pos (hR v).1 (by norm_num)
  have hsmall : ∀ v, vertexPolygonAt (point v) (directions v) (r v) ⊆ closedBall (point v) (R v) := by
    intro v
    apply (vertexPolygonAt_subset_closedBall _ _ _).trans
    apply closedBall_subset_closedBall
    dsimp only [r]
    linarith [(hR v).1]
  refine ⟨r, fun v => ⟨hr v, vertexPolygonAt_isClosedDisc _ _ (hr v),
    center_mem_interior_vertexPolygonAt _ _ (hr v), (hR v).2.mono_left (hsmall v)⟩, ?_⟩
  intro u v huv
  exact (hballs u v huv).mono (hsmall u) (hsmall v)

/-- The polygons can also be chosen with the sum of any two radii strictly
less than the distance between their centers. This leaves a positive length
for every shortened straight edge in Part IV, Section 7b. -/
theorem exists_small_vertex_polygons_distance_bounds {ι : Type*} [Finite ι]
    (point : ι → ℂ) (hinj : Function.Injective point) (directions : ι → Finset ℝ)
    (K : ι → Set ℂ) (hK : ∀ v, IsCompact (K v)) (hmiss : ∀ v, point v ∉ K v) :
    ∃ r : ι → ℝ,
      (∀ v, 0 < r v ∧ IsClosedDisc (vertexPolygonAt (point v) (directions v) (r v)) ∧
        point v ∈ interior (vertexPolygonAt (point v) (directions v) (r v)) ∧
        Disjoint (vertexPolygonAt (point v) (directions v) (r v)) (K v)) ∧
      Pairwise (fun u v => Disjoint (vertexPolygonAt (point u) (directions u) (r u))
        (vertexPolygonAt (point v) (directions v) (r v))) ∧
      (∀ u v, u ≠ v → r u + r v < dist (point u) (point v)) := by
  obtain ⟨R, hR, hballs⟩ := exists_separated_vertex_discs point hinj K hK hmiss
  let r : ι → ℝ := fun v => R v / 3
  have hr : ∀ v, 0 < r v := fun v => div_pos (hR v).1 (by norm_num)
  have hsmall : ∀ v, vertexPolygonAt (point v) (directions v) (r v) ⊆ closedBall (point v) (R v) := by
    intro v
    apply (vertexPolygonAt_subset_closedBall _ _ _).trans
    apply closedBall_subset_closedBall
    dsimp only [r]
    linarith [(hR v).1]
  have hdist : ∀ u v, u ≠ v → R u < dist (point u) (point v) := by
    intro u v huv
    apply lt_of_not_ge
    intro hle
    exact disjoint_left.mp (hballs u v huv)
      (mem_closedBall.mpr (by simpa only [dist_comm] using hle))
      (mem_closedBall_self (hR v).1.le)
  refine ⟨r, fun v => ⟨hr v, vertexPolygonAt_isClosedDisc _ _ (hr v),
    center_mem_interior_vertexPolygonAt _ _ (hr v), (hR v).2.mono_left (hsmall v)⟩,
    fun u v huv => (hballs u v huv).mono (hsmall u) (hsmall v), ?_⟩
  intro u v huv
  have hu := hdist u v huv
  have hv := hdist v u huv.symm
  rw [dist_comm (point v)] at hv
  dsimp only [r]
  linarith [(hR u).1, (hR v).1]

end GraphMinor.LRPlanarity
