module

public import GraphMinor.LRPlanarity.TreeNeighborhoodStrips
import GraphMinor.LRPlanarity.TreeNeighborhoodFacets
import GraphMinor.LRPlanarity.PolygonalizationDiscs

/-!
# Disjoint attachment intervals on one vertex polygon

Part IV, Section 7b of the planarity note requires the strip intervals on
one polygon to be pairwise disjoint. Their tangency points are distinct
because the incident directions are distinct. Choose disjoint small discs
around those finitely many points and shorten each facet interval to stay
inside its own disc.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Metric Surface

/-- Part IV, Section 7b: finitely many distinct prescribed directions have
pairwise disjoint positive-width attachment intervals on the vertex polygon. -/
theorem exists_disjoint_vertex_facet_intervals {ι : Type*} [Finite ι]
    (directions : Finset ℝ) {r : ℝ} (hr : 0 < r) (angle : ι → ℝ)
    (hangle : ∀ i, angle i ∈ directions) (hinj : Function.Injective (fun i => eC (angle i))) :
    ∃ width : ι → ℝ,
      (∀ i, 0 < width i ∧ vertexFacetInterval (angle i) r (width i) ⊆
        discBd (vertexPolygon directions r)) ∧
      Pairwise (fun i j => Disjoint (vertexFacetInterval (angle i) r (width i))
        (vertexFacetInterval (angle j) r (width j))) := by
  classical
  let point : ι → ℂ := fun i => r • eC (angle i)
  have hpoint : Function.Injective point := fun i j he =>
    hinj ((smul_right_injective ℂ hr.ne') he)
  obtain ⟨radius, hradius, hballs⟩ := exists_separated_vertex_discs point hpoint
    (fun _ => ∅) (fun _ => isCompact_empty) (fun _ => notMem_empty _)
  have hlocal := fun i => exists_vertexPolygon_facet_interval directions hr (hangle i)
  choose δ hδ hfacet using hlocal
  let width : ι → ℝ := fun i => min (δ i) (radius i)
  have hw : ∀ i, 0 < width i := fun i => lt_min (hδ i) (hradius i).1
  have hinside : ∀ i, vertexFacetInterval (angle i) r (width i) ⊆
      closedBall (point i) (radius i) := by
    intro i x hx
    obtain ⟨t, ht, rfl⟩ := hx
    apply mem_closedBall.mpr
    change dist (point i + t • (Complex.I * eC (angle i))) (point i) ≤ radius i
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      norm_mul, Complex.norm_I, norm_eC, mul_one, mul_one]
    exact (abs_le.mpr ht).trans (min_le_right _ _)
  refine ⟨width, fun i => ⟨hw i, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨t, ht, rfl⟩ := hx
    rw [(vertexPolygon_isClosedDisc directions hr).2]
    exact hfacet i t ((abs_le.mpr ht).trans (min_le_left _ _))
  · intro i j hij
    exact (hballs i j hij).mono (hinside i) (hinside j)

end GraphMinor.LRPlanarity
