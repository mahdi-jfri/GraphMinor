module

public import GraphMinor.GM06.Section5OpenCutSheet
import GraphMinor.GM06.Section5RegionPoint
import GraphMinor.GM06.Section5CoverRegion

/-!
# The cut sheet is the selected cover component

The open sheet of the one-path cut disc is contained in the component
selected by the following initial gap. Conversely, that component cannot
leave the closed disc image without crossing the seam. Its connectedness
therefore keeps it inside the sheet. This retains the side information
needed for the one-path case of VI Section 5.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- The following component in the angular cover is exactly the cut-disc
sheet off the sole linkage path. -/
theorem cylinderCoverStrip_eq_single_strip_sheet
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) :
    cylinderCoverStrip L 1 = (planeToCylinderCover '' D) ∩
      cylinderCoverProjection ⁻¹' (L.pathDrawing 0).Uᶜ := by
  classical
  let K := planeToCylinderCover '' D
  let I := K ∩ cylinderCoverProjection ⁻¹' (L.pathDrawing 0).Uᶜ
  obtain ⟨s, hs, hproj, hrange⟩ := exists_open_sheet_on_single_strip L hG hθ hD hBd hstrip
  have hri : range s = I := hrange
  have hK : IsClosed K := (hD.isCompact.image continuous_planeToCylinderCover).isClosed
  have hI : IsOpen I := by
    rw [← hri]
    exact hs.isOpen_range
  have hIR : I ⊆ cylinderCoverStrip L 1 := by
    rintro p ⟨⟨q, hq, hp⟩, hoff⟩
    apply mem_cylinderCoverStrip_of_mem_disc L hG hθ 1 hD hBd hstrip
    · rw [← hp]
      change (max 1 (min 2 q.1), q.2) ∈ D
      rw [min_eq_right (hstrip hq).2, max_eq_right (hstrip hq).1]
      exact hq
    · intro h
      obtain ⟨j, hj⟩ := mem_iUnion.mp h
      have hj0 : j = 0 := Subsingleton.elim _ _
      rw [hj0] at hj
      exact hoff hj
  have hR : cylinderCoverStrip L 1 ⊆ I ∪ Kᶜ := by
    intro p hp
    by_cases hpK : p ∈ K
    · left
      refine ⟨hpK, ?_⟩
      have hdom := connectedComponentIn_subset _ _ hp
      change cylinderCoverProjection p ∈ univ \ ⋃ j, (L.pathDrawing j).U at hdom
      exact fun h => hdom.2 (mem_iUnion.mpr ⟨0, h⟩)
    · exact Or.inr hpK
  have hdisj : Disjoint I Kᶜ := disjoint_compl_right.mono_left inter_subset_left
  have hchoice : cylinderCoverStrip L 1 ⊆ I ∨ cylinderCoverStrip L 1 ⊆ Kᶜ :=
    isPreconnected_connectedComponentIn.subset_or_subset hI hK.isOpen_compl hdisj hR
  have hx : cylinderN1Point 1 0 ∈ (L.pathDrawing 0).Uᶜ :=
    fun h => cylinderN1Point_not_mem_U hG 0 ((L.isSubdrawing 0).2 h)
  have hsI : s ⟨cylinderN1Point 1 0, hx⟩ ∈ I := by
    rw [← hri]
    exact mem_range_self _
  apply subset_antisymm
  · rcases hchoice with h | h
    · exact h
    · exact False.elim (h (hIR hsI) hsI.1)
  · exact hIR

/-- The closure of the following lifted region stays in the closed cut disc.
This includes its incidences with either seam copy. -/
theorem closure_cylinderCoverRegion_subset_single_strip
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) :
    closure (cylinderCoverRegion 1 G 0) ⊆ planeToCylinderCover '' D := by
  have hsub : cylinderCoverRegion 1 G 0 ⊆ planeToCylinderCover '' D := by
    have h := cylinderCoverRegion_subset_strip L 0
    change cylinderCoverRegion 1 G 0 ⊆ cylinderCoverStrip L 1 at h
    rw [cylinderCoverStrip_eq_single_strip_sheet L hG hθ hD hBd hstrip] at h
    exact h.trans inter_subset_left
  exact closure_minimal hsub
    (hD.isCompact.image continuous_planeToCylinderCover).isClosed

end GraphMinor.GM06
