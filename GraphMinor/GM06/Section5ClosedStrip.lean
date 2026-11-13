module

public import GraphMinor.GM06.Defs
public import GraphMinor.Surface.Defs
public import GraphMinor.GM06.Section5BoundaryGap
import GraphMinor.GM06.Section5StripDisc
import GraphMinor.GM06.Section5StripImage
import GraphMinor.GM06.Section5StripInjective
import GraphMinor.Surface.EdgeLens
import GraphMinor.GM06.Section5StripBoundary
import GraphMinor.GM06.Section5StripCuffs

/-!
# The closed cylinder strip as a disc

For the local boundary argument in VI (5.1), page 129, the closure
of a strip between distinct consecutive linkage paths is a closed
disc. Project the disc between the corresponding lifts. For at
least two paths this projection is injective, so it transports both
the disc and its boundary. The projected boundary lies on linkage
paths or cuffs.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- With at least two linkage paths, the closure of each cylinder
strip is a closed disc, as used in VI (5.1). -/
theorem isClosedDisc_closure_cylinderStrip
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage k G)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ) (i : Fin k) :
    IsClosedDisc (closure (cylinderStrip L i)) := by
  obtain ⟨D, hD, hBd, hstrip⟩ := exists_closedDisc_of_liftedStripBoundary L hG hθ ((i.val : ℤ) + 1)
  have hi := injOn_radialCylinderProjection_stripDisc L hG hk hθ _ hD hBd hstrip
  have hproj := hD.image_injOn continuous_radialCylinderProjection.continuousOn hi
  rw [image_stripDisc_eq_closure_strip L hG hθ i hD hBd hstrip] at hproj
  exact hproj.1

/-- The boundary of the closed strip consists only of linkage and
cuff points. This gives the boundary germ at an initial vertex for
the local sector argument in VI (5.1). -/
theorem discBd_closure_cylinderStrip_subset
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage k G)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ) (i : Fin k) :
    discBd (closure (cylinderStrip L i)) ⊆
      (⋃ j, (L.pathDrawing j).U) ∪ bd ClosedCylinder := by
  obtain ⟨D, hD, hBd, hstrip⟩ := exists_closedDisc_of_liftedStripBoundary L hG hθ ((i.val : ℤ) + 1)
  have hi := injOn_radialCylinderProjection_stripDisc L hG hk hθ _ hD hBd hstrip
  have hproj := (hD.image_injOn continuous_radialCylinderProjection.continuousOn hi).2
  rw [image_stripDisc_eq_closure_strip L hG hθ i hD hBd hstrip, hBd] at hproj
  rw [hproj]
  exact image_liftedStripBoundary_subset_linkage_union_boundary hG.1 L _

/-- The four boundary pieces of the closed strip: its two neighbouring
paths, the initial cuff gap, and the terminal cuff. This separates
the boundary pieces that can approach the initial vertex in VI (5.1). -/
theorem discBd_closure_cylinderStrip_subset_four_pieces
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage k G)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ) (i : Fin k) :
    discBd (closure (cylinderStrip L i)) ⊆
      (L.pathDrawing i).U ∪ (L.pathDrawing (finSuccCycle i)).U ∪
        range (initialCuffGapCurve k i) ∪ cylinderCuff2 := by
  obtain ⟨D, hD, hBd, hstrip⟩ := exists_closedDisc_of_liftedStripBoundary L hG hθ ((i.val : ℤ) + 1)
  have hi := injOn_radialCylinderProjection_stripDisc L hG hk hθ _ hD hBd hstrip
  have hproj := (hD.image_injOn continuous_radialCylinderProjection.continuousOn hi).2
  rw [image_stripDisc_eq_closure_strip L hG hθ i hD hBd hstrip, hBd] at hproj
  intro x hx
  have hxcl := discBd_subset (closure (cylinderStrip L i)) hx
  rw [hproj] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  rcases hp with ((hp | hp) | hp) | hp
  · obtain ⟨t, rfl⟩ := hp
    apply Or.inl ∘ Or.inl ∘ Or.inl
    rw [radialCylinderProjection_liftedLinkageCurve, modIdx_natCast_succ]
    exact (L.curve_parametrizes i).2.1 ▸ mem_range_self t
  · obtain ⟨t, rfl⟩ := hp
    apply Or.inl ∘ Or.inl ∘ Or.inr
    rw [radialCylinderProjection_liftedLinkageCurve, modIdx_natCast_succ_add_one]
    exact (L.curve_parametrizes _).2.1 ▸ mem_range_self t
  · apply Or.inl ∘ Or.inr
    apply closure_strip_inter_initial_cuff_subset_gap L hG hθ i
    refine ⟨hxcl, ?_⟩
    change max 1 (min 2 p.1) = 1
    rw [mem_singleton_iff.mp hp.1]
    norm_num
  · apply Or.inr
    change max 1 (min 2 p.1) = 2
    rw [mem_singleton_iff.mp hp.1]
    norm_num

end GraphMinor.GM06
