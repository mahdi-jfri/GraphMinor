module

public import GraphMinor.GM06.Defs
public import GraphMinor.Surface.DiscGrow
import GraphMinor.GM06.Section5BoundaryDiscDetour
import GraphMinor.GM06.Section5RegionInterior
import GraphMinor.Surface.Cylinder

/-!
# A helix detour around a disc attached at one vertex

For Reduction 2 of VI (5.5), page 130, an enclosure may meet the
retained drawing at its attachment vertex on the disc boundary.
If the helix misses that vertex, the boundary-puncture retraction
introduces no new drawing contact. It removes interior vertex times
and preserves winding by the constructed relative homotopy.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- Detour a helix missing the attachment around an enclosing disc
whose boundary meets the drawing only at that attachment. -/
theorem exists_helix_detour_past_boundary_attachment
    {k : ℕ} {G : Drawing ClosedCylinder} (f : Curve ClosedCylinder)
    (hf : IsHelix k G f) {D : Set ClosedCylinder} (hD : IsClosedDisc D)
    {s : ClosedCylinder} (hs : s ∈ discBd D) (hsf : s ∉ range f)
    (hbd : discBd D ∩ G.U ⊆ {s})
    (h0 : f 0 ∉ discInt D) (h1 : f 1 ∉ discInt D) :
    ∃ g : Curve ClosedCylinder, IsHelix k G g ∧
      Disjoint (range g) (discInt D) ∧ s ∉ range g ∧
      curvePhi k G g ≤ curvePhi k G f ∧ range g ⊆ range f ∪ discBd D := by
  obtain ⟨g, hhom, havoid, hsg, hfixed, honto⟩ :=
    exists_curve_detour_avoiding_boundary_attachment isSurface_closedCylinder.2.2
      hD f hs hsf h0 h1
  have hnew (t) (ht : f t ∈ discInt D) : g t ∉ G.U := by
    intro htG
    have he : g t = s := hbd ⟨honto t ht, htG⟩
    exact hsg ⟨t, he⟩
  have hsub : curveVertexHits G g ⊆ curveVertexHits G f := by
    intro t ht
    by_cases hft : f t ∈ discInt D
    · exact False.elim (hnew t hft (G.V_subset_U ht))
    · change f t ∈ G.V
      change g t ∈ G.V at ht
      rwa [hfixed t hft] at ht
  have hnormal : IsNormalCurve G g := by
    rintro x ⟨⟨t, rfl⟩, ht⟩
    by_cases hft : f t ∈ discInt D
    · exact False.elim (hnew t hft ht)
    · rw [hfixed t hft] at ht ⊢
      exact hf.1 ⟨mem_range_self t, ht⟩
  refine ⟨g, ⟨hnormal, (hfixed 0 h0).symm ▸ hf.2.1,
    (hfixed 1 h1).symm ▸ hf.2.2.1, hf.2.2.2.subset hsub⟩,
    havoid, hsg, ?_, ?_⟩
  · have hcount : curveL G g ≤ curveL G f := ncard_le_ncard hsub hf.2.2.2
    change windingNumber g + (k : ℝ)⁻¹ * (curveL G g : ℝ) ≤
      windingNumber f + (k : ℝ)⁻¹ * (curveL G f : ℝ)
    rw [windingNumber_eq_of_homotopic hhom]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcount)
      (inv_nonneg.mpr (Nat.cast_nonneg k : (0 : ℝ) ≤ k)))
  · rintro _ ⟨t, rfl⟩
    by_cases ht : f t ∈ discInt D
    · exact Or.inr (honto t ht)
    · exact Or.inl (hfixed t ht ▸ mem_range_self t)

end GraphMinor.GM06
