module

public import GraphMinor.GM06.Section5CutStripSurface
import GraphMinor.GM06.Section5CutStripProjection

/-!
# Projection is injective on a cut path with distinct projected ends

Off the linkage, the cut projection is injective. Points above the
linkage lie on the cut boundary. A path meeting that boundary only
at its ends can therefore have no identified pair unless its two
ends project to the same vertex. Excluding that case proves the
injectivity needed to project the first-contact path in VI (5.1),
page 129, to an original graph path.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- A cut path meeting the boundary only at its ends projects
injectively when its two projected ends are distinct. -/
theorem injOn_cut_projection_of_path_point_contact
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    {Q : Drawing D} {s t : D} (hpoint : Q.U ∩ bd D ⊆ {s, t})
    (hends : radialCylinderProjection s.1 ≠ radialCylinderProjection t.1) :
    InjOn (fun p : D => radialCylinderProjection p.1) Q.U := by
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
    have hpEnds : p = s ∨ p = t := by
      simpa only [mem_insert_iff, mem_singleton_iff] using hpoint ⟨hp, hpBd⟩
    have hqEnds : q = s ∨ q = t := by
      simpa only [mem_insert_iff, mem_singleton_iff] using hpoint ⟨hq, hqBd⟩
    rcases hpEnds with rfl | rfl <;> rcases hqEnds with rfl | rfl
    · rfl
    · exact False.elim (hends heq)
    · exact False.elim (hends heq.symm)
    · rfl
  · exact single_strip_projection_inj_off_path L hG hθ hD hBd hstrip hpP heq

end GraphMinor.GM06
