module

public import GraphMinor.GM06.Section5CutStripSurface
import GraphMinor.GM06.Section5CutDiscardedSubdrawing
import GraphMinor.GM06.Section5CutDiscardedRightExclusion
import GraphMinor.GM06.Section5CutInitialFiber
import GraphMinor.GM06.Section5SeparationGeometry
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM11.Walks

/-!
# The discarded one-path drawing attaches at one cut vertex

For VI (5.5), page 130, exhaust clockwise discarded edges and
cut along the retained linkage. Every discarded point on the cut
boundary projects to the original attachment. The clockwise copy
is isolated from the discarded cut edges and can be removed. The
actual remaining discarded cut subdrawing then meets both the cut
boundary and the retained closed side only at the other copy.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- After clockwise exhaustion, the discarded side on the one-path
cut disc is an actual subdrawing attached only at the other initial copy. -/
theorem exists_discarded_drawing_on_single_strip
    {G G₁ G₂ : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hG₁ : IsCylinderSection5Drawing 1 G₁)
    (hθ : L.HasTheta θ) (hLP : (L.pathDrawing 0).IsSubdrawing G₁)
    (hsep : IsGraphSeparation G.toGraph G₁.toGraph G₂.toGraph)
    (hover : G₁.V ∩ G₂.V ⊆ {cylinderM1Point 1 0})
    (hno : ∀ e ∈ G₂.E, ¬ IsClockwiseInitialEdge L 0 e)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (F : Drawing D)
    (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
    (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
    (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E \ (L.pathDrawing 0).E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)
    (g : Curve D) (hgcoord : ∀ t, (g t).1 = (1, 2 * (1 + (t : ℝ)) * Real.pi))
    (hgbd : range g ⊆ bd D) :
    ∃ H : Drawing D, H.IsSubdrawing F ∧
      H.U = ((fun p : D => radialCylinderProjection p.1) ⁻¹' G₂.U) \ {g 1} ∧
      H.U ∩ bd D ⊆ {g 0} ∧
      F.U ⊆ ((fun p : D => radialCylinderProjection p.1) ⁻¹' G₁.U ∪ bd D) ∪ H.U ∧
      (((fun p : D => radialCylinderProjection p.1) ⁻¹' G₁.U) ∪ bd D) ∩ H.U ⊆ {g 0} := by
  let f : D → ClosedCylinder := fun p => radialCylinderProjection p.1
  have hf : Continuous f := continuous_radialCylinderProjection.comp continuous_subtype_val
  have h₂ : G₂.IsSubdrawing G := ⟨hsep.2.1.vertexSet_mono, hsep.2.1.edgeSet_mono⟩
  have hgeom := discarded_side_meets_retained_and_boundary_only_at_initial hG hG₁ 0 hsep hover
  have hsets := point_sets_of_graph_separation hsep
  have hproj (x : D) (hx₂ : f x ∈ G₂.U) (hxB : x ∈ bd D) : f x = cylinderM1Point 1 0 := by
    rw [← preimage_boundary_union_path_single_strip L hG hθ hD hBd hstrip] at hxB
    rcases hxB with hxC | hxP
    · exact hgeom.2 ⟨hx₂, hxC⟩
    · exact hgeom.1 ⟨hLP.U_subset hxP, hx₂⟩
  have hB : (f ⁻¹' G₂.U) ∩ bd D ⊆ f ⁻¹' G₂.V := by
    rintro x ⟨hx₂, hxB⟩
    have hsG : cylinderM1Point 1 0 ∈ G.V :=
      (L.isSubdrawing 0).1.1 (isPathDrawing_end_vertices (L.isPath 0)).1
    apply vertex_mem_of_mem_subdrawing_point_set h₂ hx₂
    rw [hproj x hx₂ hxB]
    exact hsG
  have heP (e) (he : e ∈ G₂.E) : e ∉ (L.pathDrawing 0).E := by
    intro hp
    exact disjoint_left.mp hsep.2.2.2.2 (hLP.2 hp) he
  have hnoCut : ∀ ec ∈ F.E, (∃ e ∈ G₂.E, ec = f ⁻¹' e) → g 1 ∉ closure ec := by
    intro ec hec hex
    obtain ⟨e, he, heq⟩ := hex
    exact right_gap_end_not_mem_closure_cut_edge_of_not_clockwise
      L hG hθ hD hBd hstrip hec (h₂.2 he) (heP e he) heq (hno e he) g hgcoord
  have hcover : f ⁻¹' G₂.U ⊆ F.U := by
    rw [hFU]
    exact (preimage_mono h₂.U_subset).trans subset_union_left
  obtain ⟨H, hHF, hHU⟩ := exists_discarded_cut_subdrawing_without_isolated_copy f hf h₂ hFV
    hcover (bd D) hB (fun ec hec => (hEdges ec hec).imp id (fun ⟨e, he, heq⟩ => ⟨e, he.1, heq⟩))
    (g 1) hnoCut
  have hends (x : D) (hx : x ∈ H.U) (hs : f x = cylinderM1Point 1 0) : x = g 0 := by
    have hxU := hHU ▸ hx
    rcases eq_gap_end_of_projecting_to_initial L hG hθ hD hBd hstrip g hgcoord hs with he | he
    · exact he
    · exact False.elim (hxU.2 he)
  have hHB : H.U ∩ bd D ⊆ {g 0} := by
    rintro x ⟨hxH, hxB⟩
    have hx₂ : f x ∈ G₂.U := (hHU ▸ hxH).1
    exact hends x hxH (hproj x hx₂ hxB)
  refine ⟨H, hHF, hHU, hHB, ?_, ?_⟩
  · intro x hxF
    rw [hFU] at hxF
    rcases hxF with hxG | hxB
    · rcases hsets.1 ▸ hxG with hx₁ | hx₂
      · exact Or.inl (Or.inl hx₁)
      · by_cases he : x = g 1
        · exact Or.inl (Or.inr (he.symm ▸ hgbd (mem_range_self 1)))
        · exact Or.inr (hHU.symm ▸ ⟨hx₂, he⟩)
    · exact Or.inl (Or.inr hxB)
  · rintro x ⟨hx₁ | hxB, hxH⟩
    · have hx₂ : f x ∈ G₂.U := (hHU ▸ hxH).1
      exact hends x hxH (hgeom.1 ⟨hx₁, hx₂⟩)
    · exact hHB ⟨hxH, hxB⟩

end GraphMinor.GM06
