module

public import GraphMinor.GM06.Defs
public import GraphMinor.Surface.DiscGrow
import GraphMinor.GM06.Section5AttachedDiscVisitControl
import GraphMinor.GM06.Section5NormalCoverSimplification
import GraphMinor.GM06.Section5CoverCurve
import GraphMinor.GM06.Section5CoverSides
import GraphMinor.GM06.Section5RegionInterior
import GraphMinor.GM06.Section4
import GraphMinor.Surface.DiscMerge

/-!
# Detouring any helix around an attached disc

For Reduction 2 of VI (5.5), page 130, first simplify the angular
lift of the input helix. This preserves its endpoints and winding
and does not increase its vertex count. The attachment-visit lemma
then gives the disc detour, even if the helix visits the attachment.
The final range bound retains all avoidance established earlier.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- An attached disc can be avoided without increasing helix
potential, with no restriction on visits to its attachment vertex. -/
theorem exists_helix_detour_around_attached_disc
    {k : ℕ} {G : Drawing ClosedCylinder} (f : Curve ClosedCylinder) (hf : IsHelix k G f)
    {D : Set ClosedCylinder} (hD : IsClosedDisc D)
    {s : ClosedCylinder} (hs : s ∈ discBd D) (hsG : s ∈ G.V)
    (hbd : discBd D ∩ G.U ⊆ {s}) :
    ∃ g : Curve ClosedCylinder, IsHelix k G g ∧ Disjoint (range g) (discInt D) ∧
      curvePhi k G g ≤ curvePhi k G f ∧ range g ⊆ range f ∪ discBd D := by
  have h0 : f 0 ∉ discInt D := by
    intro ht
    have hbd0 : f 0 ∈ bd ClosedCylinder := by
      obtain ⟨i, hi⟩ := hf.2.1
      rw [← hi, bd_closedCylinder]
      exact Or.inl rfl
    exact hbd0 (isInteriorPoint_of_mem_discInt isSurface_closedCylinder.2.2 hD ht)
  have h1 : f 1 ∉ discInt D := by
    intro ht
    have hbd1 : f 1 ∈ bd ClosedCylinder := by
      obtain ⟨i, hi⟩ := hf.2.2.1
      rw [← hi, bd_closedCylinder]
      exact Or.inr rfl
    exact hbd1 (isInteriorPoint_of_mem_discInt isSurface_closedCylinder.2.2 hD ht)
  let A := cylinderCurveLiftAt f (cylinderAngleLift f 0)
  have hA (t) : cylinderCoverProjection (A t) = f t :=
    cylinderCoverProjection_curveLiftAt f _ (exp_cylinderAngleLift f 0) t
  obtain ⟨g, q, hq, hproj, hg, hw, hLg, hgr, hq0, hq1⟩ :=
    exists_helix_from_normal_cover_curve f hf.1 hf.2.1 hf.2.2.1 A hA
  have hg0 : g 0 = f 0 := (hproj 0).symm.trans ((congrArg cylinderCoverProjection hq0).trans (hA 0))
  have hg1 : g 1 = f 1 := (hproj 1).symm.trans ((congrArg cylinderCoverProjection hq1).trans (hA 1))
  have hsub : range A ∩ cylinderCoverProjection ⁻¹' G.V ⊆ A '' curveVertexHits G f := by
    rintro _ ⟨⟨t, rfl⟩, ht⟩
    refine ⟨t, ?_, rfl⟩
    change f t ∈ G.V
    change cylinderCoverProjection (A t) ∈ G.V at ht
    rwa [hA] at ht
  have hcount : curveL G g ≤ curveL G f := hLg.trans
    ((ncard_le_ncard hsub (hf.2.2.2.image A)).trans (ncard_image_le hf.2.2.2))
  have hφg : curvePhi k G g ≤ curvePhi k G f := by
    change windingNumber g + (k : ℝ)⁻¹ * (curveL G g : ℝ) ≤
      windingNumber f + (k : ℝ)⁻¹ * (curveL G f : ℝ)
    rw [hw]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcount)
      (inv_nonneg.mpr (Nat.cast_nonneg k : (0 : ℝ) ≤ k)))
  obtain ⟨u, hu, huD, hφu, hur⟩ := exists_attached_disc_helix_detour_of_injective_lift
    g hg q hq hproj hD hs hsG hbd (hg0 ▸ h0) (hg1 ▸ h1)
  exact ⟨u, hu, huD, hφu.trans hφg, hur.trans (union_subset_union_left _ hgr)⟩

end GraphMinor.GM06
