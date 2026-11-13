module

public import GraphMinor.GM06.Section5CutGapRegionPoint
public import GraphMinor.GM06.Section5CutRegion
import GraphMinor.GM06.Section5DiscEdgeIncidence
import GraphMinor.GM06.Section5GapEdge

/-!
# The added gap edge is incident with the chosen cut region

The gap midpoint belongs to the selected cover region. Equality of
lifted closures puts its cut-disc preimage in the closure of the
chosen cut region. Edge-side incidence then extends from this point
to the whole added gap edge. Density of the open arc also puts both
gap ends in that edge closure. These are the two incidence facts
used by the one-path corner argument of VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

/-- The added edge containing the open initial gap is incident with
the chosen cut region, and its closure contains the whole gap arc. -/
theorem cut_gap_edge_incidence
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (F : Drawing D)
    (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
    (g : Curve D) (hgcoord : ∀ t, (g t).1 = (1, 2 * (1 + (t : ℝ)) * π))
    {e : Set D} (he : e ∈ F.E) (hgap : g '' Ioo 0 1 ⊆ e) :
    e ⊆ closure (((fun p : D => planeToCylinderCover p.1) ⁻¹' cylinderCoverRegion 1 G 0) \ bd D) ∧
      range g ⊆ closure e := by
  let a : D → CylinderCover := fun p => planeToCylinderCover p.1
  let r := (a ⁻¹' cylinderCoverRegion 1 G 0) \ bd D
  obtain ⟨hr, hcl⟩ := preimage_coverRegion_sdiff_boundary_mem_regions L hG hθ hD hBd hstrip F hFU
  obtain ⟨t, ht, htr⟩ := exists_cut_initial_gap_point_in_coverRegion hG g hgcoord
  have hemb := isClosedEmbedding_single_strip_coverMap hD hstrip
  have hgt : g t ∈ closure r := by
    obtain ⟨q, hq, heq⟩ := hcl.symm ▸ subset_closure htr
    exact hemb.injective heq ▸ hq
  have hbd : bd D ⊆ F.U := by rw [hFU]; exact subset_union_right
  have hmeet : (e ∩ g '' Ioo 0 1).Nonempty := ⟨g t, hgap ⟨t, ht, rfl⟩, t, ht, rfl⟩
  refine ⟨edge_subset_closure_of_incident_disc_region (show IsClosedDiscSpace D from hD)
    hbd hr he ⟨g t, hgap ⟨t, ht, rfl⟩, hgt⟩, ?_⟩
  exact (arc_interior_subset_edge he (hgap.trans he.2.1) hmeet).2

end GraphMinor.GM06
