module

public import GraphMinor.GM06.Section5CutVertexAccess
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM06.Section5WalkConnectedAvoid
import GraphMinor.GM06.Section5InitialLoop
import GraphMinor.GM06.DiscRegions
import GraphMinor.Surface.Fan
import GraphMinor.GM11.Walks

/-!
# The cut drawing remains connected after removing an initial copy

The punctured disc boundary is connected. Every interior vertex can
reach it by the lifted avoiding walks. An interior edge also joins
this core, since otherwise its two ends would be the removed copy
and its projection would be an original loop excluded by Reduction 2.
Joining these connected pieces proves punctured connectedness, which
supplies distinct corners at the initial copy in VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- The augmented one-path cut drawing stays connected after deleting
either lift of the initial vertex, when Reduction 2 is unavailable. -/
theorem isConnected_punctured_single_strip_drawing_of_no_reduction2
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    (hno2 : ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage 1 H),
      IsCylinderSection5Drawing 1 H → ¬ Section5Reduction2Step 1 G L H M)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (F : Drawing D)
    (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
    (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
    (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)
    (s : D) (hsproj : radialCylinderProjection s.1 = cylinderM1Point 1 0) :
    IsConnected (F.U \ {s}) := by
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD.isCompact
  let f : D → ClosedCylinder := fun p => radialCylinderProjection p.1
  have hc : Continuous f := continuous_radialCylinderProjection.comp continuous_subtype_val
  have hsurj := surjective_single_strip_projection L hG hθ hD hBd hstrip
  have hsP : cylinderM1Point 1 0 ∈ (L.pathDrawing 0).V :=
    (isPathDrawing_end_vertices (L.isPath 0)).1
  have hsV : s ∈ F.V := by
    rw [hFV]
    change radialCylinderProjection s.1 ∈ G.V
    rw [hsproj]
    exact (L.isSubdrawing 0).1.1 hsP
  have hsBd : s ∈ bd D := by
    rw [← preimage_boundary_union_path_single_strip L hG hθ hD hBd hstrip]
    right
    change radialCylinderProjection s.1 ∈ (L.pathDrawing 0).U
    rw [hsproj]
    exact (L.pathDrawing 0).V_subset_U hsP
  let X := F.U \ {s}
  let C := bd D \ {s}
  have hC : IsConnected C :=
    (isPathConnected_oArc_diff (show IsClosedDiscSpace D from hD).isOArc_bd hsBd).isConnected
  have hCX : C ⊆ X := by
    rintro z ⟨hz, hn⟩
    refine ⟨?_, hn⟩
    rw [hFU]
    exact Or.inr hz
  obtain ⟨a, ha⟩ := hC.nonempty
  have hvertex (b : D) (hb : b ∈ F.V \ {s}) :
      ∃ Y ⊆ X, a ∈ Y ∧ b ∈ Y ∧ IsConnected Y := by
    by_cases hbBd : b ∈ bd D
    · exact ⟨C, hCX, ha, ⟨hbBd, hb.2⟩, hC⟩
    have hbproj : radialCylinderProjection b.1 ≠ cylinderM1Point 1 0 := by
      intro hp
      apply hbBd
      rw [← preimage_boundary_union_path_single_strip L hG hθ hD hBd hstrip]
      right
      change radialCylinderProjection b.1 ∈ (L.pathDrawing 0).U
      rw [hp]
      exact (L.pathDrawing 0).V_subset_U hsP
    obtain ⟨y, hyBd, R, hR⟩ := exists_cut_walk_to_boundary_avoiding_initial_of_no_reduction2 L hG hθ hno2
      hD hBd hstrip F hFU hFV hEdges hb.1 hbproj
    have hnR : ∀ z ∈ R.support, z ≠ s := by
      intro z hz hzs
      apply hR z hz
      exact (congrArg f hzs).trans hsproj
    obtain ⟨Y, hY, hbY, hyY, hcY⟩ := exists_connected_subset_of_walk_avoiding_vertex hsV R hnR
    have hyC : y ∈ C := ⟨hyBd, hnR y R.end_mem_support⟩
    exact ⟨C ∪ Y, union_subset hCX hY, Or.inl ha, Or.inr hbY,
      hC.union ⟨y, hyC, hyY⟩ hcY⟩
  refine ⟨⟨a, hCX ha⟩, ?_⟩
  apply isPreconnected_of_forall a
  intro x hx
  by_cases hxC : x ∈ C
  · exact ⟨C, hCX, ha, hxC, hC.isPreconnected⟩
  have hxBd : x ∉ bd D := fun h => hxC ⟨h, hx.2⟩
  by_cases hxV : x ∈ F.V
  · obtain ⟨Y, hY, haY, hxY, hcY⟩ := hvertex x ⟨hxV, hx.2⟩
    exact ⟨Y, hY, haY, hxY, hcY.isPreconnected⟩
  obtain ⟨ec, hec, hxec⟩ := F.exists_edge_of_mem hx.1 hxV
  obtain ⟨e, he, heq⟩ : ∃ e ∈ G.E, ec = f ⁻¹' e := by
    rcases hEdges ec hec with hbd | h
    · exact False.elim (hxBd (hbd hxec))
    · exact h
  obtain ⟨u, v, hl⟩ := F.toGraph.exists_isLink_of_mem_edgeSet hec
  have hex : ∃ b, b ∈ F.V \ {s} ∧ b ∈ closure ec := by
    by_cases hv : v = s
    · have hu : u ≠ s := by
        intro hu
        have hloop : F.toGraph.IsLink ec s s := by simpa only [hu, hv] using hl
        have hproj := isLink_of_full_preimage_edge hc hc.isClosedMap hsurj hFV he heq hloop
        change G.toGraph.IsLink e (radialCylinderProjection s.1) (radialCylinderProjection s.1) at hproj
        rw [hsproj] at hproj
        exact not_isLoop_at_initial_of_no_reduction2 L hG hno2 0 e hproj
      refine ⟨u, ⟨hl.left_mem, hu⟩, ?_⟩
      exact (show u ∈ closure ec ∩ F.V from hl.2.2.2.symm ▸ mem_insert _ {v}).1
    · refine ⟨v, ⟨hl.right_mem, hv⟩, ?_⟩
      exact (show v ∈ closure ec ∩ F.V from hl.2.2.2.symm ▸ mem_insert_of_mem u rfl).1
  obtain ⟨b, hb, hbcl⟩ := hex
  obtain ⟨Y, hY, haY, hbY, hcY⟩ := hvertex b hb
  have heC : IsConnected (closure ec \ {s}) := by
    refine ⟨⟨b, hbcl, hb.2⟩, hec.2.2.1.isConnected.isPreconnected.subset_closure ?_ sdiff_subset⟩
    intro y hy
    exact ⟨subset_closure hy, fun heq => (hec.2.1 hy).2 (mem_singleton_iff.mp heq ▸ hsV)⟩
  have heX : closure ec \ {s} ⊆ X := by
    rintro y ⟨hy, hn⟩
    exact ⟨F.closure_subset_U hec hy, hn⟩
  have hjoin : IsConnected (Y ∪ (closure ec \ {s})) := hcY.union ⟨b, hbY, hbcl, hb.2⟩ heC
  exact ⟨Y ∪ (closure ec \ {s}), union_subset hY heX, Or.inl haY,
    Or.inr ⟨subset_closure hxec, hx.2⟩, hjoin.isPreconnected⟩


/-- The augmented one-path cut drawing stays connected after deleting
either lift of the initial vertex, when no reduction applies. -/
theorem isConnected_punctured_single_strip_drawing
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies 1 G L)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (F : Drawing D)
    (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
    (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
    (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)
    (s : D) (hsproj : radialCylinderProjection s.1 = cylinderM1Point 1 0) :
    IsConnected (F.U \ {s}) := by
  exact isConnected_punctured_single_strip_drawing_of_no_reduction2 L hG hθ
    (fun H M hH h2 => hno ⟨H, M, hH, Or.inr (Or.inl h2)⟩) hD hBd hstrip F hFU hFV hEdges s hsproj

end GraphMinor.GM06
