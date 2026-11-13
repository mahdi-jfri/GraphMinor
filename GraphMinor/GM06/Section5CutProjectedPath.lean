module

public import GraphMinor.GM06.Section5CutPathInjection
public import GraphMinor.GM06.Section5CutPointContact
import GraphMinor.GM06.Section5FullPreimageCarry
import GraphMinor.GM06.Section5CarriedPath
import GraphMinor.GM06.Section5CutStripProjection

/-!
# Projecting the first-contact cut path into the original graph

Each open edge of a path meeting the cut boundary only at its ends
misses that boundary. The augmented edge classification makes it
a full lifted original edge. With distinct projected ends, projection
is injective on the path, so the constructed carrying map gives an
original graph subpath with exactly the projected point set. Its
only contacts with the linkage are its ends. This is the original
path used in the one-path proof of VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- A cut path with interior off the boundary and distinct projected
ends projects to an original subpath meeting the linkage only at its ends. -/
theorem exists_original_path_of_cut_path_point_contact
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    {F : Drawing D} (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
    (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E \ (L.pathDrawing 0).E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)
    {Q : Drawing D} {s t : D} (hQ : IsSubpathOf F Q s t)
    (hpoint : Q.U ∩ bd D ⊆ {s, t})
    (hends : radialCylinderProjection s.1 ≠ radialCylinderProjection t.1) :
    ∃ P : Drawing ClosedCylinder,
      IsSubpathOf G P (radialCylinderProjection s.1) (radialCylinderProjection t.1) ∧
      P.U = (fun p : D => radialCylinderProjection p.1) '' Q.U ∧
      P.U ∩ (L.pathDrawing 0).U ⊆ {radialCylinderProjection s.1, radialCylinderProjection t.1} := by
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD.isCompact
  let f : D → ClosedCylinder := fun p => radialCylinderProjection p.1
  have hc : Continuous f := continuous_radialCylinderProjection.comp continuous_subtype_val
  have hsurj := surjective_single_strip_projection L hG hθ hD hBd hstrip
  have hinj := injOn_cut_projection_of_path_point_contact L hG hθ hD hBd hstrip hpoint hends
  have hEdgesQ : ∀ ec ∈ Q.E, ∃ e ∈ G.E, ec = f ⁻¹' e := by
    intro ec hec
    have heDis := edge_disjoint_of_path_point_contact hQ.2.2 hpoint hec
    rcases hEdges ec (hQ.1.2 hec) with heBd | ⟨e, he, heq⟩
    · obtain ⟨p, hp⟩ := hec.1
      exact False.elim (disjoint_left.mp heDis hp (heBd hp))
    · exact ⟨e, he.1, heq⟩
  have hcarry := isCarry_of_full_preimage_edges hc hc.isClosedMap hsurj hFV hQ.1 hinj hEdgesQ
  obtain ⟨P, hP, hPU⟩ := exists_path_image_of_isCarry hc hc.isClosedMap hcarry hQ.2.2 hends
  refine ⟨P, hP, hPU, ?_⟩
  rintro x ⟨hxP, hxL⟩
  rw [hPU] at hxP
  obtain ⟨p, hp, hpx⟩ := hxP
  have hpBd : p ∈ bd D := by
    rw [← preimage_boundary_union_path_single_strip L hG hθ hD hBd hstrip]
    right
    change f p ∈ (L.pathDrawing 0).U
    rw [hpx]
    exact hxL
  rcases hpoint ⟨hp, hpBd⟩ with hps | hpt
  · exact Or.inl (hpx.symm.trans (congrArg f hps))
  · exact Or.inr (hpx.symm.trans (congrArg f (mem_singleton_iff.mp hpt)))

end GraphMinor.GM06
