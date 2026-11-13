module

public import GraphMinor.GM06.Defs
public import GraphMinor.Surface.DiscGrow
import GraphMinor.GM06.Section5DiscardedSingleStripDrawing
import GraphMinor.GM06.Section5DiscAttachedSubdrawingEnclosures
import GraphMinor.GM06.Section5CutEnclosureProjection
import GraphMinor.GM06.Section5CutStripBoundary
import GraphMinor.GM06.Section5CutInitialGap
import GraphMinor.GM06.Section5CutStripProjection
import GraphMinor.GM06.Section5StripDisc
import GraphMinor.GM06.Section5SeparationGeometry
import GraphMinor.GM06.Section5
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM11.Walks

/-!
# Actual cylinder enclosures for one discarded linkage side

For VI (5.5), page 130, after clockwise discarded-edge exhaustion,
cut along the retained sole linkage. Remove the isolated clockwise
initial copy from the discarded cut drawing. The disc-space enclosure
construction applies at the other copy. Each enclosure meets the
cut boundary only there, so projection is injective on the whole
disc. The projected family covers every original discarded point
except the attachment, with boundaries off the original drawing
except at that attachment.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- A one-path discarded side without clockwise initial edges has
an actual finite cylinder-disc enclosure family. -/
theorem exists_single_path_discarded_enclosures_of_no_clockwise_edges
    {G G₁ G₂ : Drawing ClosedCylinder} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hG₁ : IsCylinderSection5Drawing 1 G₁)
    (hLP : (L.pathDrawing 0).IsSubdrawing G₁)
    (hsep : IsGraphSeparation G.toGraph G₁.toGraph G₂.toGraph)
    (hover : G₁.V ∩ G₂.V ⊆ {cylinderM1Point 1 0})
    (hno : ∀ e ∈ G₂.E, ¬ IsClockwiseInitialEdge L 0 e) :
    ∃ F : Set (Set ClosedCylinder), F.Finite ∧
      (∀ E ∈ F, IsClosedDisc E ∧ discBd E ∩ G.U ⊆ {cylinderM1Point 1 0}) ∧
      G₂.U \ {cylinderM1Point 1 0} ⊆ ⋃ E ∈ F, discInt E := by
  obtain ⟨θ, hθ⟩ := CylinderLinkage.exists_hasTheta hG.1 L
  obtain ⟨D, hD, hBd, hstrip⟩ := exists_closedDisc_of_liftedStripBoundary L hG hθ 1
  obtain ⟨Γ, hΓU, hΓV, hEdges⟩ := exists_augmented_drawing_on_single_strip L hG hθ hD hBd hstrip
  obtain ⟨g, hgcoord, hgi, hgbd, hgproj⟩ := exists_single_strip_initial_gap_curve L hG hBd
  let f : D → ClosedCylinder := fun p => radialCylinderProjection p.1
  have hf : Continuous f := continuous_radialCylinderProjection.comp continuous_subtype_val
  have hg0 : f (g 0) = cylinderM1Point 1 0 := by
    rw [show f (g 0) = initialCuffGapCurve 1 0 0 from hgproj 0]
    exact (initialCuffGapCurve_props hG 0).1
  have hg1 : f (g 1) = cylinderM1Point 1 0 := by
    rw [show f (g 1) = initialCuffGapCurve 1 0 1 from hgproj 1]
    have hh := (initialCuffGapCurve_props hG 0).2.1
    exact hh.trans (congrArg (cylinderM1Point 1) (Subsingleton.elim _ _))
  obtain ⟨H, hHΓ, hHU, hHB, hcover, hoverH⟩ := exists_discarded_drawing_on_single_strip
    L hG hG₁ hθ hLP hsep hover hno hD hBd hstrip Γ hΓU hΓV hEdges g hgcoord hgbd
  have hsG : cylinderM1Point 1 0 ∈ G.V :=
    (L.isSubdrawing 0).1.1 (isPathDrawing_end_vertices (L.isPath 0)).1
  have hgV (t : unitInterval) (he : f (g t) = cylinderM1Point 1 0) : g t ∈ Γ.V := by
    rw [hΓV]
    change f (g t) ∈ G.V
    rw [he]; exact hsG
  have hbdΓ : bd D ⊆ Γ.U := hΓU ▸ subset_union_right
  let A := f ⁻¹' G₁.U ∪ bd D
  have hAc : IsClosed A := (G₁.isClosed_U.preimage hf).union
    (isClosed_bd_of_isClosedDiscSpace (show IsClosedDiscSpace D from hD))
  obtain ⟨F, hF, hdisc, hcov⟩ := exists_disc_space_enclosures_for_attached_subdrawing
    (show IsClosedDiscSpace D from hD) hHΓ hbdΓ (hgV 0 hg0) (hgV 1 hg1)
    (hgbd (mem_range_self 0)) (hgbd (mem_range_self 1)) (hgi.ne zero_ne_one)
    hAc subset_union_right hcover hoverH
  have him (E) (hE : E ∈ F) := cut_enclosure_image_disc L hG hθ hD hBd hstrip
    (hdisc E hE).1 (hdisc E hE).2.2
  refine ⟨(fun E => f '' E) '' F, hF.image _, ?_, ?_⟩
  · rintro _ ⟨E, hE, rfl⟩
    refine ⟨(him E hE).1, ?_⟩
    rw [(him E hE).2.1]
    rintro y ⟨⟨x, hxb, hxy⟩, hyG⟩
    change f x = y at hxy
    have hxΓ : x ∈ Γ.U := by
      rw [hΓU]
      apply Or.inl
      change f x ∈ G.U
      rw [hxy]; exact hyG
    have hxs : x = g 0 := (hdisc E hE).2.1 ⟨hxb, hxΓ⟩
    exact hxy.symm.trans ((congrArg f hxs).trans hg0)
  · rintro y ⟨hy₂, hys⟩
    obtain ⟨x, hxy⟩ := surjective_single_strip_projection L hG hθ hD hBd hstrip y
    change f x = y at hxy
    have hx1 : x ≠ g 1 := fun he => hys (hxy.symm.trans ((congrArg f he).trans hg1))
    have hx0 : x ≠ g 0 := fun he => hys (hxy.symm.trans ((congrArg f he).trans hg0))
    have hxH : x ∈ H.U := by
      rw [hHU]
      refine ⟨?_, hx1⟩
      change f x ∈ G₂.U
      rw [hxy]; exact hy₂
    obtain ⟨E, hE, hxE⟩ := mem_iUnion₂.mp (hcov ⟨hxH, hx0⟩)
    refine mem_iUnion₂.mpr ⟨f '' E, mem_image_of_mem _ hE, ?_⟩
    rw [(him E hE).2.2]
    exact ⟨x, hxE, hxy⟩

end GraphMinor.GM06
