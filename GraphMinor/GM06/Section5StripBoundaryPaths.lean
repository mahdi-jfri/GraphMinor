module

public import GraphMinor.GM06.Defs
public import GraphMinor.Surface.Defs
import GraphMinor.GM06.Section5StripDisc
import GraphMinor.GM06.Section5StripImage
import GraphMinor.GM06.Section5StripInjective
import GraphMinor.GM06.Section5StripBoundary
import GraphMinor.GM06.Section5ClosedStrip
import GraphMinor.GM06.Section5RegionInterior
import GraphMinor.Surface.EdgeLens
import GraphMinor.Surface.DiscMerge

/-!
# Linkage paths and cuff points on the closed strip boundary

For the sector comparison in VI (5.1), page 129, the two linkage
paths bounding a strip lie on its intrinsic disc boundary. This
follows from their lifted boundary curves under the injective
projection. Any cuff point in the closed strip is also on its disc
boundary, since an intrinsic interior point would be an interior
point of the cylinder.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- The two neighbouring linkage paths lie on the boundary of the
closed strip disc used in VI (5.1). -/
theorem linkage_paths_subset_discBd_closure_strip
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage k G)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ) (i : Fin k) :
    (L.pathDrawing i).U ⊆ discBd (closure (cylinderStrip L i)) ∧
      (L.pathDrawing (finSuccCycle i)).U ⊆ discBd (closure (cylinderStrip L i)) := by
  obtain ⟨D, hD, hBd, hstrip⟩ := exists_closedDisc_of_liftedStripBoundary L hG hθ ((i.val : ℤ) + 1)
  have hi := injOn_radialCylinderProjection_stripDisc L hG hk hθ _ hD hBd hstrip
  have hproj := (hD.image_injOn continuous_radialCylinderProjection.continuousOn hi).2
  rw [image_stripDisc_eq_closure_strip L hG hθ i hD hBd hstrip, hBd] at hproj
  constructor
  · intro x hx
    rw [hproj]
    obtain ⟨t, ht⟩ := (L.curve_parametrizes i).2.1.symm ▸ hx
    refine ⟨liftedLinkageCurve hG.1 L ((i.val : ℤ) + 1) t,
      Or.inl (Or.inl (Or.inl ⟨t, rfl⟩)), ?_⟩
    rw [radialCylinderProjection_liftedLinkageCurve, modIdx_natCast_succ]
    exact ht
  · intro x hx
    rw [hproj]
    obtain ⟨t, ht⟩ := (L.curve_parametrizes (finSuccCycle i)).2.1.symm ▸ hx
    refine ⟨liftedLinkageCurve hG.1 L (((i.val : ℤ) + 1) + 1) t,
      Or.inl (Or.inl (Or.inr ⟨t, rfl⟩)), ?_⟩
    rw [radialCylinderProjection_liftedLinkageCurve, modIdx_natCast_succ_add_one]
    exact ht

/-- A cuff point in a closed strip lies on the strip disc boundary. -/
theorem mem_discBd_closure_strip_of_mem_cuff
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage k G)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ) (i : Fin k)
    {x : ClosedCylinder} (hx : x ∈ closure (cylinderStrip L i)) (hxbd : x ∈ bd ClosedCylinder) :
    x ∈ discBd (closure (cylinderStrip L i)) := by
  by_contra hn
  exact hxbd (isInteriorPoint_of_mem_discInt isSurface_closedCylinder.2.2
    (isClosedDisc_closure_cylinderStrip L hk hG hθ i) ⟨hx, hn⟩)

end GraphMinor.GM06
