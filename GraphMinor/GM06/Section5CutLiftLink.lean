module

public import GraphMinor.GM06.Section5CutEdgePreimage
public import GraphMinor.GM06.Section5CutLinks
import GraphMinor.GM06.Section5CutStripProjection
import GraphMinor.GM11.Walks

/-!
# Lifting a link at a vertex off the seam

Away from the linkage the cut projection has one preimage. Every
incident original edge is a non-seam edge, whose full preimage is
an edge of the augmented cut drawing. Closedness of projection
lifts its incidence at that unique vertex, so its graph link lifts
as well. This is the local step for carrying a path to the boundary
core in the one-path proof of VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- Every original link at a vertex off the linkage lifts to a link
of the cut drawing with the prescribed initial lift. -/
theorem exists_cut_link_at_non_seam_vertex
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (F : Drawing D)
    (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
    (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
    (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)
    {x : D} (hxF : x ∈ F.V) (hxP : radialCylinderProjection x.1 ∉ (L.pathDrawing 0).V)
    {e : Set ClosedCylinder} {v : ClosedCylinder}
    (hl : G.toGraph.IsLink e (radialCylinderProjection x.1) v) :
    ∃ y : D, F.toGraph.IsLink ((fun p : D => radialCylinderProjection p.1) ⁻¹' e) x y ∧
      radialCylinderProjection y.1 = v := by
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD.isCompact
  let f : D → ClosedCylinder := fun p => radialCylinderProjection p.1
  have hc : Continuous f := continuous_radialCylinderProjection.comp continuous_subtype_val
  have hxGU : radialCylinderProjection x.1 ∈ G.V := hl.left_mem
  have hxPU : radialCylinderProjection x.1 ∉ (L.pathDrawing 0).U := by
    intro h
    apply hxP
    rw [(L.pathDrawing 0).U_eq] at h
    rcases h with hv | h
    · exact hv
    · obtain ⟨d, hd, hxd⟩ := mem_iUnion₂.mp h
      have hm : radialCylinderProjection x.1 ∈ closure d ∩ (L.pathDrawing 0).V := by
        rw [(L.isSubdrawing 0).1.closure_inter_V hd]
        exact ⟨hxd, hxGU⟩
      exact hm.2
  have heP : e ∉ (L.pathDrawing 0).E := by
    intro heP
    have hxcl : radialCylinderProjection x.1 ∈ closure e :=
      (show radialCylinderProjection x.1 ∈ closure e ∩ G.V from
        hl.2.2.2.symm ▸ mem_insert _ {v}).1
    have hm : radialCylinderProjection x.1 ∈ closure e ∩ (L.pathDrawing 0).V := by
      rw [(L.isSubdrawing 0).1.closure_inter_V heP]
      exact ⟨hxcl, hxGU⟩
    exact hxP hm.2
  have hec := full_preimage_non_seam_edge_mem L hG hθ hD hBd hstrip F hFU hFV hEdges hl.1 heP
  apply exists_isLink_full_preimage_of_unique_fiber hc hc.isClosedMap
    (surjective_single_strip_projection L hG hθ hD hBd hstrip) hFV hec hxF hl
  intro y hy
  exact (single_strip_projection_inj_off_path L hG hθ hD hBd hstrip hxPU hy.symm).symm

end GraphMinor.GM06
