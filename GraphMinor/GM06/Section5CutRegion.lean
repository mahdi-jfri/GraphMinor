module

public import GraphMinor.GM06.Section5CutRegionCoordinates
public import GraphMinor.GM06.Section5CutStripSurface
import GraphMinor.GM06.Section5CoverRegion
import GraphMinor.GM06.Section5RegionInterior
import GraphMinor.GM06.Section5RegionPoint
import GraphMinor.GM11.Regions
import GraphMinor.GM07.Section11f
import GraphMinor.Surface.DiscNbhd
import GraphMinor.Surface.Cuffs

/-!
# The chosen region of the augmented cut-disc drawing

Remove the disc boundary from the pullback of the selected cover region.
This preserves connectedness and its closure. Every new frontier point
lies in the original drawing or on the disc boundary, so the resulting
set is a whole region of the augmented drawing. This supplies the region
whose boundary is followed in the one-path case of VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

private theorem closure_component_subset_union_compl
    {X : Type*} [TopologicalSpace X] (S : Set X) (b : X) :
    closure (connectedComponentIn S b) ⊆ connectedComponentIn S b ∪ Sᶜ := by
  intro p hp
  by_cases hb : b ∈ S
  · by_cases hpS : p ∈ S
    · left
      have hconn : IsPreconnected (insert p (connectedComponentIn S b)) :=
        isPreconnected_connectedComponentIn.subset_closure (subset_insert _ _)
          (insert_subset hp subset_closure)
      exact hconn.subset_connectedComponentIn
        (mem_insert_of_mem _ (mem_connectedComponentIn hb))
        (insert_subset hpS (connectedComponentIn_subset S b)) (mem_insert _ _)
    · exact Or.inr hpS
  · rw [connectedComponentIn_eq_empty hb, closure_empty] at hp
    exact False.elim hp

/-- A connected open set avoiding a drawing is a whole region when its
frontier lies in the drawing. -/
theorem region_of_connected_open_frontier
    {X : Type*} [TopologicalSpace X] {F : Drawing X} {Y : Set X}
    (hY : IsConnected Y) (hYo : IsOpen Y) (hdis : Disjoint Y F.U)
    (hfr : frontier Y ⊆ F.U) : Y ∈ F.R := by
  obtain ⟨a, ha⟩ := hY.nonempty
  have haoff : a ∈ univ \ F.U := ⟨mem_univ _, fun h => disjoint_left.mp hdis ha h⟩
  let R := connectedComponentIn (univ \ F.U) a
  have haR : a ∈ R := mem_connectedComponentIn haoff
  have hYR : Y ⊆ R := hY.isPreconnected.subset_connectedComponentIn ha
    (fun x hx => ⟨mem_univ _, fun hxF => disjoint_left.mp hdis hx hxF⟩)
  have hcover : R ⊆ Y ∪ (closure Y)ᶜ := by
    intro x hx
    by_cases hxY : x ∈ Y
    · exact Or.inl hxY
    · refine Or.inr ?_
      intro hxcl
      have hxfr : x ∈ frontier Y := ⟨hxcl, by rw [hYo.interior_eq]; exact hxY⟩
      exact (connectedComponentIn_subset _ a hx).2 (hfr hxfr)
  have hsplit : Disjoint Y (closure Y)ᶜ :=
    disjoint_left.mpr fun x hx hxcl => hxcl (subset_closure hx)
  have hRY : R ⊆ Y := by
    rcases isPreconnected_connectedComponentIn.subset_or_subset hYo
      isClosed_closure.isOpen_compl hsplit hcover with h | h
    · exact h
    · exact False.elim (h haR (subset_closure ha))
  exact ⟨a, haoff, Subset.antisymm hRY hYR⟩

/-- The selected cover region, pulled into the cut disc and with the
boundary removed, is a region of the augmented finite drawing. Its closure
still records all incidences with both seam copies. -/
theorem preimage_coverRegion_sdiff_boundary_mem_regions
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (F : Drawing D)
    (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D) :
    let a : D → CylinderCover := fun p => planeToCylinderCover p.1
    (a ⁻¹' cylinderCoverRegion 1 G 0) \ bd D ∈ F.R ∧
      a '' closure ((a ⁻¹' cylinderCoverRegion 1 G 0) \ bd D) =
        closure (cylinderCoverRegion 1 G 0) := by
  let a : D → CylinderCover := fun p => planeToCylinderCover p.1
  let Y := a ⁻¹' cylinderCoverRegion 1 G 0
  let Z := Y \ bd D
  have hS : IsSurface D := by
    let : CompactSpace D := isCompact_iff_compactSpace.mp hD.isCompact
    have hU : IsClosedDisc (univ : Set D) := by
      obtain ⟨e⟩ := hD
      exact ⟨e.trans (Homeomorph.Set.univ D).symm⟩
    exact ⟨inferInstance, inferInstance, fun p => isManifoldPoint_of_disc hU Filter.univ_mem⟩
  obtain ⟨hYo, hYp, hcl⟩ := preimage_coverRegion_on_single_strip L hG hθ hD hBd hstrip
  have hZo : IsOpen Z := hYo.sdiff (cuff_statement D hS).1
  have hZp : IsPreconnected Z := GM07.isPreconnected_diff_bd hS hYo hYp
  have hclZ : closure Z = closure Y := closure_sdiff_boundary_of_isOpen hS hYo
  have hp := cylinderInitialLift_mem_closure_coverRegion hG (0 : Fin 1)
  obtain ⟨q, hq, _⟩ := hcl.symm ▸ hp
  have hqZ : q ∈ closure Z := hclZ.symm ▸ hq
  obtain ⟨z, _, hz⟩ := mem_closure_iff.mp hqZ univ isOpen_univ (mem_univ q)
  have hdis : Disjoint Z F.U := by
    apply disjoint_left.mpr
    intro x hx hxF
    rw [hFU] at hxF
    rcases hxF with hxG | hxbd
    · exact (connectedComponentIn_subset _ _ hx.1).2 hxG
    · exact hx.2 hxbd
  have hfr : frontier Z ⊆ F.U := by
    intro x hx
    rw [hFU]
    by_cases hxbd : x ∈ bd D
    · exact Or.inr hxbd
    · have hxY : x ∈ closure Y := hclZ ▸ hx.1
      have hxR : a x ∈ closure (cylinderCoverRegion 1 G 0) := hcl ▸ mem_image_of_mem a hxY
      have hcases := closure_component_subset_union_compl
        (cylinderCoverProjection ⁻¹' (univ \ G.U))
        _ hxR
      rcases hcases with hin | hout
      · exact False.elim (hx.2 (hZo.interior_eq.symm ▸ ⟨hin, hxbd⟩))
      · left
        change radialCylinderProjection x.1 ∈ G.U
        exact by_contra fun h => hout ⟨mem_univ _, h⟩
  refine ⟨region_of_connected_open_frontier ⟨⟨z, hz⟩, hZp⟩ hZo hdis hfr, ?_⟩
  change a '' closure Z = _
  rw [hclZ]
  exact hcl

end GraphMinor.GM06
