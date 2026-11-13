module

public import GraphMinor.LRPlanarity.TreeNeighborhoodStrips
import GraphMinor.LRPlanarity.PolygonalizationNeighborhoods

/-!
# Simultaneous choice of thin strip widths

Part IV, Section 7b of the planarity note uses finitely many positive
separation distances to choose all strip widths. Compact disjoint centerlines
have disjoint open metric neighborhoods avoiding the prescribed obstacles.
Choose each width below both its facet bound and half its neighborhood
radius. The whole strip then stays in its assigned neighborhood.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Metric Surface

/-- Part IV, Section 7b: choose positive strip widths simultaneously below
prescribed local facet bounds, keeping all strips disjoint and avoiding their
closed obstacles. The hypotheses concern the compact centerline configuration. -/
theorem exists_separated_thin_strips {ι : Type*} [Finite ι]
    (center : ι → ℂ) (angle a b bound : ι → ℝ) (F : ι → Set ℂ)
    (hlength : ∀ i, a i < b i) (hbound : ∀ i, 0 < bound i)
    (hcenters : Pairwise (fun i j => Disjoint (stripCenterline (center i) (angle i) (a i) (b i))
      (stripCenterline (center j) (angle j) (a j) (b j))))
    (hF : ∀ i, IsClosed (F i))
    (havoid : ∀ i, Disjoint (stripCenterline (center i) (angle i) (a i) (b i)) (F i)) :
    ∃ width : ι → ℝ,
      (∀ i, 0 < width i ∧ width i ≤ bound i ∧
        IsClosedDisc (orientedStrip (center i) (angle i) (a i) (b i) (width i)) ∧
        Disjoint (orientedStrip (center i) (angle i) (a i) (b i) (width i)) (F i)) ∧
      Pairwise (fun i j => Disjoint (orientedStrip (center i) (angle i) (a i) (b i) (width i))
        (orientedStrip (center j) (angle j) (a j) (b j) (width j))) := by
  let K : ι → Set ℂ := fun i => stripCenterline (center i) (angle i) (a i) (b i)
  have hcompact : ∀ i, IsCompact (K i) := by
    intro i
    apply isCompact_Icc.image
    fun_prop
  obtain ⟨δ, hδ, hneighborhoods⟩ := exists_disjoint_middle_neighborhoods K F hcompact hcenters hF havoid
  let width : ι → ℝ := fun i => min (bound i) (δ i / 2)
  have hw : ∀ i, 0 < width i := fun i => lt_min (hbound i) (half_pos (hδ i).1)
  have hwidthδ : ∀ i, width i < δ i :=
    fun i => (min_le_right _ _).trans_lt (half_lt_self (hδ i).1)
  have hsmall : ∀ i, orientedStrip (center i) (angle i) (a i) (b i) (width i) ⊆ thickening (δ i) (K i) :=
    fun i => (orientedStrip_subset_cthickening _ _ _ _ _).trans
      (cthickening_subset_thickening' (hδ i).1 (hwidthδ i) (K i))
  refine ⟨width, fun i => ⟨hw i, min_le_left _ _, orientedStrip_isClosedDisc _ _ (hlength i) (hw i),
    (hδ i).2.mono_left (hsmall i)⟩, ?_⟩
  intro i j hij
  exact (hneighborhoods hij).mono (hsmall i) (hsmall j)

end GraphMinor.LRPlanarity
