module

public import GraphMinor.GM06.Section5CutStripSurface
import GraphMinor.GM06.Section5CutStripProjection
import GraphMinor.Surface.Wedge
import GraphMinor.Surface.DiscGrow

/-!
# Projecting a cut enclosure with one boundary contact

For the one-path Reduction 2 argument of VI (5.5), page 130,
an enclosure meets the cut boundary only at one initial copy.
The only nontrivial fibres of the cut projection lie on that
boundary, so the projection is injective on the enclosure. Its
image is a cylinder disc, with boundary and interior transported
by the same map.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- A subset of the cut disc meeting its boundary at most once
has injective projection back to the cylinder. -/
theorem injOn_cut_projection_of_one_boundary_contact
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    {E : Set D} {s : D} (hpoint : E ∩ bd D ⊆ {s}) :
    InjOn (fun p : D => radialCylinderProjection p.1) E := by
  intro p hp q hq heq
  change radialCylinderProjection p.1 = radialCylinderProjection q.1 at heq
  by_cases hpP : radialCylinderProjection p.1 ∈ (L.pathDrawing 0).U
  · have hqP : radialCylinderProjection q.1 ∈ (L.pathDrawing 0).U := heq ▸ hpP
    have hpBd : p ∈ bd D := by
      rw [← preimage_boundary_union_path_single_strip L hG hθ hD hBd hstrip]
      exact Or.inr hpP
    have hqBd : q ∈ bd D := by
      rw [← preimage_boundary_union_path_single_strip L hG hθ hD hBd hstrip]
      exact Or.inr hqP
    exact (show p = s from hpoint ⟨hp, hpBd⟩).trans (show q = s from hpoint ⟨hq, hqBd⟩).symm
  · exact single_strip_projection_inj_off_path L hG hθ hD hBd hstrip hpP heq

/-- An enclosing disc with one cut-boundary contact projects to
a cylinder disc, with its boundary and interior images unchanged. -/
theorem cut_enclosure_image_disc
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    {E : Set D} (hE : IsClosedDisc E) {s : D} (hpoint : E ∩ bd D ⊆ {s}) :
    let f : D → ClosedCylinder := fun p => radialCylinderProjection p.1
    IsClosedDisc (f '' E) ∧ discBd (f '' E) = f '' discBd E ∧ discInt (f '' E) = f '' discInt E := by
  dsimp only
  let : Nonempty D := ⟨s⟩
  have hi := injOn_cut_projection_of_one_boundary_contact L hG hθ hD hBd hstrip hpoint
  obtain ⟨hEc, hEb⟩ := isClosedDisc_image_injOn hE hE.isCompact
    (continuous_radialCylinderProjection.comp continuous_subtype_val).continuousOn hi
  change discBd ((fun p : D => radialCylinderProjection p.1) '' E) =
    (fun p : D => radialCylinderProjection p.1) '' discBd E at hEb
  refine ⟨hEc, hEb, ?_⟩
  change _ \ discBd _ = _ '' (E \ discBd E)
  rw [hEb, hi.image_sdiff_subset (GraphMinor.Surface.discBd_subset E)]

end GraphMinor.GM06
