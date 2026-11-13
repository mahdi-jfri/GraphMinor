module

public import GraphMinor.GM06.Section5CutStripProjection
public import GraphMinor.GM07.CutStages
import GraphMinor.GM06.Section5LiftCover
import GraphMinor.GM06.Section5StripImage
import GraphMinor.GM06.Section5StripDisc
import GraphMinor.Surface.DiscNbhd

/-!
# The lifted one-path disc is a cut cylinder

The disc projection is a quotient map with finite fibers. Its boundary
lies exactly above the old cuffs and the linkage path, and interior
points have no other point above their images. Thus it is the actual
cut along the sole linkage path. This permits using the proved
pullback construction for the graph in the one-path argument of VI
Section 5, while keeping the two sides of the path distinct.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

private theorem isSurface_closed_disc_subtype {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D) :
    IsSurface D := by
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD.isCompact
  have hU : IsClosedDisc (univ : Set D) := by
    obtain ⟨e⟩ := hD
    exact ⟨e.trans (Homeomorph.Set.univ D).symm⟩
  exact ⟨inferInstance, inferInstance, fun p => isManifoldPoint_of_disc hU Filter.univ_mem⟩

private theorem mem_discBd_iff_subtype_mem_bd {D : Set (ℝ × ℝ)} (p : D) :
    p.1 ∈ discBd D ↔ p ∈ bd D := by
  constructor
  · rintro ⟨q, hq, heq⟩
    exact (Subtype.ext heq : q = p) ▸ hq
  · intro hp
    exact ⟨p, hp, rfl⟩

/-- The boundary of the cut strip disc is exactly the preimage of
the two cylinder cuffs and the sole linkage path. -/
theorem preimage_boundary_union_path_single_strip
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) :
    (fun p : D => radialCylinderProjection p.1) ⁻¹'
      (bd ClosedCylinder ∪ (L.pathDrawing 0).U) = bd D := by
  ext p
  constructor
  · intro hp
    by_contra hn
    have hpInt : p.1 ∈ discInt D :=
      ⟨p.2, fun h => hn ((mem_discBd_iff_subtype_mem_bd p).mp h)⟩
    rcases hp with hp | hp
    · have hr := discInt_subset_open_radial_strip hD hstrip hpInt
      rw [bd_closedCylinder] at hp
      rcases hp with hp | hp
      · change (radialCylinderProjection p.1).1.1 = 1 at hp
        rw [radialCylinderProjection_fst (hstrip p.2)] at hp
        exact (ne_of_gt hr.1) hp
      · change (radialCylinderProjection p.1).1.1 = 2 at hp
        rw [radialCylinderProjection_fst (hstrip p.2)] at hp
        exact (ne_of_lt hr.2) hp
    · exact stripDiscInterior_projection_not_mem_linkage L hG hθ 1 hD hBd hstrip hpInt
        (radialCylinderProjection_fst (hstrip p.2)) rfl (mem_iUnion.mpr ⟨0, hp⟩)
  · intro hp
    have hpB : p.1 ∈ liftedStripBoundary hG.1 L 1 :=
      hBd ▸ (mem_discBd_iff_subtype_mem_bd p).mpr hp
    have h := image_liftedStripBoundary_subset_linkage_union_boundary hG.1 L 1 ⟨p.1, hpB, rfl⟩
    rcases h with h | h
    · right
      obtain ⟨j, hj⟩ := mem_iUnion.mp h
      have hj0 : j = 0 := Subsingleton.elim _ _
      exact hj0 ▸ hj
    · exact Or.inl h

/-- The canonical lifted strip disc, with angular projection, is a
cut of the cylinder along the sole linkage path. Its finite fibers
are the actual matching seam points, not an assumed cut operation. -/
theorem isCutAlongSet_single_strip_projection
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) :
    GM07.IsCutAlongSet (L.pathDrawing 0).U
      (fun p : D => radialCylinderProjection p.1) := by
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD.isCompact
  let f : D → ClosedCylinder := fun p => radialCylinderProjection p.1
  have hf : Continuous f := continuous_radialCylinderProjection.comp continuous_subtype_val
  have hs : Function.Surjective f := surjective_single_strip_projection L hG hθ hD hBd hstrip
  have hb := preimage_boundary_union_path_single_strip L hG hθ hD hBd hstrip
  refine ⟨isSurface_closed_disc_subtype hD, hf.isClosedMap.isQuotientMap hf hs, hb, ?_, ?_⟩
  · intro p hp q heq
    apply single_strip_projection_inj_off_path L hG hθ hD hBd hstrip ?_ heq
    intro hpath
    exact hp (hb ▸ (Or.inr hpath : f p ∈ bd ClosedCylinder ∪ (L.pathDrawing 0).U))
  · exact finite_fiber_single_strip_projection L hG hθ hD hBd hstrip

end GraphMinor.GM06
