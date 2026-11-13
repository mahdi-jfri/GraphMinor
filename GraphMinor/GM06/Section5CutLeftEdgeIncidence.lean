module

public import GraphMinor.GM06.Section5CutInitialFiber
import GraphMinor.GM06.Section5CutRightEdgeExclusion
import GraphMinor.GM06.Section5CutStripProjection
import GraphMinor.GM06.Section5CoverDisc

/-!
# An extra initial edge lifts at the left copy

Closedness of the cut projection lifts incidence with the original
initial vertex to one of its two preimages. The initial fiber has
exactly the two gap ends. Incidence at the right end would permit
corrected Reduction 1, so every original non-seam initial edge is
incident with the left end. This supplies the extra edge in the
one-path corner argument of VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

/-- When Reduction 1 is unavailable, the full lift of a non-seam edge incident
with the original initial vertex is incident with its left copy. -/
theorem left_gap_end_mem_closure_cut_initial_edge_of_no_reduction1
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    (hno1 : ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage 1 H),
      IsCylinderSection5Drawing 1 H → ¬ Section5Reduction1Step 1 G L H M)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    {F : Drawing D} {ec : Set D} (hec : ec ∈ F.E)
    {e : Set ClosedCylinder} (he : e ∈ G.E) (heP : e ∉ (L.pathDrawing 0).E)
    (heq : ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)
    (hs : cylinderM1Point 1 0 ∈ closure e)
    (g : Curve D) (hgcoord : ∀ t, (g t).1 = (1, 2 * (1 + (t : ℝ)) * π)) :
    g 0 ∈ closure ec := by
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD.isCompact
  let f : D → ClosedCylinder := fun p => radialCylinderProjection p.1
  have hc : Continuous f := continuous_radialCylinderProjection.comp continuous_subtype_val
  have him : f '' ec = e := by
    rw [heq, image_preimage_eq _ (surjective_single_strip_projection L hG hθ hD hBd hstrip)]
  have hcl : f '' closure ec = closure e := by
    rw [← hc.isClosedMap.closure_image_eq_of_continuous hc, him]
  obtain ⟨p, hp, hpproj⟩ := hcl.symm ▸ hs
  rcases eq_gap_end_of_projecting_to_initial L hG hθ hD hBd hstrip g hgcoord hpproj with hp0 | hp1
  · exact hp0 ▸ hp
  · have ha1 : planeToCylinderCover (g 1).1 = (⟨1, by norm_num⟩, 4 * π) := by
      rw [hgcoord]
      apply Prod.ext
      · apply Subtype.ext
        change max 1 (min 2 (1 : ℝ)) = 1
        norm_num
      · change 2 * (1 + (1 : ℝ)) * π = 4 * π
        ring
    have hinc : (⟨1, by norm_num⟩, 4 * π) ∈
        closure ((fun p : D => planeToCylinderCover p.1) '' ec) := by
      rw [← ha1]
      exact mem_closure_image
        (continuous_planeToCylinderCover.comp continuous_subtype_val).continuousAt (hp1 ▸ hp)
    exact False.elim (not_right_initialLift_mem_closure_cut_edge_of_no_reduction1 L hG hθ hno1 hD hBd hstrip hec he heP heq hinc)


/-- In an unreduced drawing, the full lift of a non-seam edge incident
with the original initial vertex is incident with its left copy. -/
theorem left_gap_end_mem_closure_cut_initial_edge
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies 1 G L)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    {F : Drawing D} {ec : Set D} (hec : ec ∈ F.E)
    {e : Set ClosedCylinder} (he : e ∈ G.E) (heP : e ∉ (L.pathDrawing 0).E)
    (heq : ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)
    (hs : cylinderM1Point 1 0 ∈ closure e)
    (g : Curve D) (hgcoord : ∀ t, (g t).1 = (1, 2 * (1 + (t : ℝ)) * π)) :
    g 0 ∈ closure ec := by
  exact left_gap_end_mem_closure_cut_initial_edge_of_no_reduction1 L hG hθ
    (fun H M hH h1 => hno ⟨H, M, hH, Or.inl h1⟩) hD hBd hstrip hec he heP heq hs g hgcoord

end GraphMinor.GM06
