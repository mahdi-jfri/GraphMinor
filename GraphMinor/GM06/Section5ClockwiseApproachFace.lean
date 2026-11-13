module

public import GraphMinor.GM06.Section5CutEdgeDeletion
import GraphMinor.GM06.Section5CutArbitraryRegion
import GraphMinor.GM06.Section5ClockwiseCutIncidence
import GraphMinor.GM06.Section5DeletedEdgeDiscFaces
import GraphMinor.GM06.Section5DiscRegionBridge
import GraphMinor.GM06.Section5CutStripSurface
import GraphMinor.GM11.Regions

/-!
# The prescribed-side old approach face after a clockwise deletion

For the one-path case of VI (5.5), page 131, delete the full lifted
edge from the augmented cut drawing. The new cylinder region gives
a whole cut-disc face containing that edge. Its closure projects
onto the cylinder region closure. The clockwise certificate makes
the right initial copy incident with the lifted edge. The old-face
choice in the disc then gives an old face incident with that copy
and with a lift of the specified last region point.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- Choose the old approach face while retaining the clockwise
initial copy, including for a one-path cylinder in VI (5.5). -/
theorem exists_clockwise_cut_approach_face
    {G G' : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (F : Drawing D)
    (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
    (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
    (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)
    (hPH : (L.pathDrawing 0).U ⊆ G'.U)
    (g : Curve D) (hgcoord : ∀ t, (g t).1 = (1, 2 * (1 + (t : ℝ)) * Real.pi))
    {e : Set ClosedCylinder} (he : e ∈ G.E) (hside : IsClockwiseInitialEdge L 0 e)
    (hU : G'.U = G.U \ e) (hV : G'.V = G.V)
    {R : Set ClosedCylinder} (hR : R ∈ G'.R) (heR : e ⊆ R)
    {w : ClosedCylinder} (hw : w ∈ closure R) :
    ∃ (v : D) (r : Set D), radialCylinderProjection v.1 = w ∧ r ∈ F.R ∧
      r ⊆ (fun p : D => radialCylinderProjection p.1) ⁻¹' R \ bd D ∧
      g 1 ∈ closure r ∧ v ∈ closure r := by
  let ec := (fun p : D => radialCylinderProjection p.1) ⁻¹' e
  have heP : e ∉ (L.pathDrawing 0).E := by
    intro heP
    obtain ⟨x, hx⟩ := he.1
    have hxG' := hPH (heP.2.1 hx).1
    rw [hU] at hxG'
    exact hxG'.2 hx
  obtain ⟨hec, heBd, hnewU, _⟩ := full_preimage_edge_deletion_on_single_strip
    L hG hθ hD hBd hstrip F hFU hFV hEdges he heP hU hV
  have hreg := preimage_arbitrary_region_sdiff_boundary_mem_regions
    L hG hθ hD hBd hstrip hPH hR hnewU
  let Z := (fun p : D => radialCylinderProjection p.1) ⁻¹' R \ bd D
  have heZ : ec ⊆ Z := by
    intro p hp
    exact ⟨heR hp, fun h => disjoint_left.mp heBd hp h⟩
  have hscl : g 1 ∈ closure ec :=
    right_gap_end_mem_closure_cut_edge_of_clockwise L hG hθ hD hBd hstrip g hgcoord hside
  obtain ⟨v, hvcl, hvw⟩ := hreg.2.symm ▸ hw
  have hDisc : IsClosedDiscSpace D := by
    obtain ⟨a⟩ := hD
    exact ⟨a⟩
  have hbdF : bd D ⊆ F.U := by rw [hFU]; exact subset_union_right
  obtain ⟨r, hr, hrZ, hsr, hvr⟩ := exists_old_disc_region_at_deleted_edge_region_closure
    hDisc hbdF hec heBd hreg.1 heZ hscl hvcl
  exact ⟨v, r, hvw, hr, hrZ, hsr, hvr⟩

/-- The actual approach curve from the prescribed right initial copy
to a lift of the last region point, for VI (5.5), page 131. Its
interior misses the original cylinder drawing. -/
theorem exists_clockwise_cut_approach_curve
    {G G' : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (F : Drawing D)
    (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
    (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
    (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)
    (hPH : (L.pathDrawing 0).U ⊆ G'.U)
    (g : Curve D) (hgcoord : ∀ t, (g t).1 = (1, 2 * (1 + (t : ℝ)) * Real.pi))
    {e : Set ClosedCylinder} (he : e ∈ G.E) (hside : IsClockwiseInitialEdge L 0 e)
    (hU : G'.U = G.U \ e) (hV : G'.V = G.V)
    {R : Set ClosedCylinder} (hR : R ∈ G'.R) (heR : e ⊆ R)
    {w : ClosedCylinder} (hw : w ∈ closure R)
    (hTarget : w ∈ G.V ∨ w ∈ bd ClosedCylinder) :
    ∃ (v : D) (q : Curve D), radialCylinderProjection v.1 = w ∧
      q 0 = g 1 ∧ q 1 = v ∧
      ∀ t : unitInterval, 0 < t → t < 1 → radialCylinderProjection (q t).1 ∉ G.U := by
  obtain ⟨v, r, hvw, hr, _, hsr, hvr⟩ := exists_clockwise_cut_approach_face
    L hG hθ hD hBd hstrip F hFU hFV hEdges hPH g hgcoord he hside hU hV hR heR hw
  have hbdF : bd D ⊆ F.U := by rw [hFU]; exact subset_union_right
  have hsBd : g 1 ∈ bd D := by
    rw [← preimage_boundary_union_path_single_strip L hG hθ hD hBd hstrip]
    apply Or.inl
    rw [bd_closedCylinder]
    apply Or.inl
    change max 1 (min 2 (g 1).1.1) = 1
    rw [hgcoord 1]
    norm_num
  have hvF : v ∈ F.U := by
    rcases hTarget with hvG | hvBd
    · rw [hFU]
      apply Or.inl
      change radialCylinderProjection v.1 ∈ G.U
      rw [hvw]
      exact G.V_subset_U hvG
    · apply hbdF
      rw [← preimage_boundary_union_path_single_strip L hG hθ hD hBd hstrip]
      apply Or.inl
      change radialCylinderProjection v.1 ∈ bd ClosedCylinder
      rw [hvw]
      exact hvBd
  have hDisc : IsClosedDiscSpace D := by
    obtain ⟨a⟩ := hD
    exact ⟨a⟩
  obtain ⟨q, hq0, hq1, hqR⟩ := exists_curve_between_drawing_points_through_disc_region
    hDisc hbdF hr (hbdF hsBd) hvF hsr hvr
  refine ⟨v, q, hvw, hq0, hq1, ?_⟩
  intro t ht0 ht1 htG
  have htF : q t ∈ F.U := by rw [hFU]; exact Or.inl htG
  exact GM11.region_subset hr (hqR t ht0 ht1) htF

/-- Retain a specified lifted last-contact point when choosing the
old approach face. The contact is a point of the actual new cut-face
closure, so its copy is fixed before the return curve is constructed. -/
theorem exists_clockwise_cut_approach_face_at_contact
    {G G' : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (F : Drawing D)
    (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
    (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
    (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)
    (hPH : (L.pathDrawing 0).U ⊆ G'.U)
    (g : Curve D) (hgcoord : ∀ t, (g t).1 = (1, 2 * (1 + (t : ℝ)) * Real.pi))
    {e : Set ClosedCylinder} (he : e ∈ G.E) (hside : IsClockwiseInitialEdge L 0 e)
    (hU : G'.U = G.U \ e) (hV : G'.V = G.V)
    {R : Set ClosedCylinder} (hR : R ∈ G'.R) (heR : e ⊆ R)
    (v : D)
    (hvcl : v ∈ closure ((fun p : D => radialCylinderProjection p.1) ⁻¹' R \ bd D)) :
    ∃ r ∈ F.R, r ⊆ (fun p : D => radialCylinderProjection p.1) ⁻¹' R \ bd D ∧
      g 1 ∈ closure r ∧ v ∈ closure r := by
  let ec := (fun p : D => radialCylinderProjection p.1) ⁻¹' e
  have heP : e ∉ (L.pathDrawing 0).E := by
    intro heP
    obtain ⟨x, hx⟩ := he.1
    have hxG' := hPH (heP.2.1 hx).1
    rw [hU] at hxG'
    exact hxG'.2 hx
  obtain ⟨hec, heBd, hnewU, _⟩ := full_preimage_edge_deletion_on_single_strip
    L hG hθ hD hBd hstrip F hFU hFV hEdges he heP hU hV
  have hreg := preimage_arbitrary_region_sdiff_boundary_mem_regions
    L hG hθ hD hBd hstrip hPH hR hnewU
  let Z := (fun p : D => radialCylinderProjection p.1) ⁻¹' R \ bd D
  have heZ : ec ⊆ Z := by
    intro p hp
    exact ⟨heR hp, fun h => disjoint_left.mp heBd hp h⟩
  have hscl : g 1 ∈ closure ec :=
    right_gap_end_mem_closure_cut_edge_of_clockwise L hG hθ hD hBd hstrip g hgcoord hside
  have hDisc : IsClosedDiscSpace D := by
    obtain ⟨a⟩ := hD
    exact ⟨a⟩
  have hbdF : bd D ⊆ F.U := by rw [hFU]; exact subset_union_right
  obtain ⟨r, hr, hrZ, hsr, hvr⟩ := exists_old_disc_region_at_deleted_edge_region_closure
    hDisc hbdF hec heBd hreg.1 heZ hscl hvcl
  exact ⟨r, hr, hrZ, hsr, hvr⟩

/-- Approach the fixed endpoint copy of the lifted helix segment
from the right initial copy, retaining its side and avoiding the
original graph at all interior parameters, in VI (5.5), page 131. -/
theorem exists_clockwise_cut_approach_curve_at_contact
    {G G' : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (F : Drawing D)
    (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
    (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
    (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)
    (hPH : (L.pathDrawing 0).U ⊆ G'.U)
    (g : Curve D) (hgcoord : ∀ t, (g t).1 = (1, 2 * (1 + (t : ℝ)) * Real.pi))
    {e : Set ClosedCylinder} (he : e ∈ G.E) (hside : IsClockwiseInitialEdge L 0 e)
    (hU : G'.U = G.U \ e) (hV : G'.V = G.V)
    {R : Set ClosedCylinder} (hR : R ∈ G'.R) (heR : e ⊆ R)
    (v : D)
    (hvcl : v ∈ closure ((fun p : D => radialCylinderProjection p.1) ⁻¹' R \ bd D))
    (hTarget : radialCylinderProjection v.1 ∈ G.V ∨
      radialCylinderProjection v.1 ∈ bd ClosedCylinder) :
    ∃ q : Curve D, q 0 = g 1 ∧ q 1 = v ∧
      ∀ t : unitInterval, 0 < t → t < 1 → radialCylinderProjection (q t).1 ∉ G.U := by
  obtain ⟨r, hr, _, hsr, hvr⟩ := exists_clockwise_cut_approach_face_at_contact
    L hG hθ hD hBd hstrip F hFU hFV hEdges hPH g hgcoord he hside hU hV hR heR v hvcl
  have hbdF : bd D ⊆ F.U := by rw [hFU]; exact subset_union_right
  have hsBd : g 1 ∈ bd D := by
    rw [← preimage_boundary_union_path_single_strip L hG hθ hD hBd hstrip]
    apply Or.inl
    rw [bd_closedCylinder]
    apply Or.inl
    change max 1 (min 2 (g 1).1.1) = 1
    rw [hgcoord 1]
    norm_num
  have hvF : v ∈ F.U := by
    rcases hTarget with hvG | hvBd
    · rw [hFU]
      exact Or.inl (G.V_subset_U hvG)
    · apply hbdF
      rw [← preimage_boundary_union_path_single_strip L hG hθ hD hBd hstrip]
      exact Or.inl hvBd
  have hDisc : IsClosedDiscSpace D := by
    obtain ⟨a⟩ := hD
    exact ⟨a⟩
  obtain ⟨q, hq0, hq1, hqR⟩ := exists_curve_between_drawing_points_through_disc_region
    hDisc hbdF hr (hbdF hsBd) hvF hsr hvr
  refine ⟨q, hq0, hq1, ?_⟩
  intro t ht0 ht1 htG
  have htF : q t ∈ F.U := by rw [hFU]; exact Or.inl htG
  exact GM11.region_subset hr (hqR t ht0 ht1) htF

end GraphMinor.GM06
