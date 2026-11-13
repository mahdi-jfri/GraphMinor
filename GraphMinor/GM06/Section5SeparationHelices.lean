module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5SeparationGeometry
import GraphMinor.GM11.Walks
import Mathlib.Tactic.Linarith

/-!
# Helices and the two sides of a separation

For Reduction 2 of VI (5.5), page 130, passing from a drawing to
a subdrawing preserves normality and can only remove vertex visits.
In the reverse direction, a helix that avoids the discarded side
except at its attachment vertex already has the same normality and
vertex-hit set in the old drawing. The remaining Reduction 2 argument
constructs such an avoiding helix.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- Deleting a subdrawing's complement preserves a helix and can
only decrease its potential by removing vertex visits. -/
theorem helix_mono_of_subdrawing
    {k : ℕ} {G H : Drawing ClosedCylinder} (hHG : H.IsSubdrawing G)
    (f : Curve ClosedCylinder) (hf : IsHelix k G f) :
    IsHelix k H f ∧ curvePhi k H f ≤ curvePhi k G f := by
  have hnormal : IsNormalCurve H f := by
    rintro x ⟨hxf, hxH⟩
    exact vertex_mem_of_mem_subdrawing_point_set hHG hxH (hf.1 ⟨hxf, hHG.U_subset hxH⟩)
  have hsub : curveVertexHits H f ⊆ curveVertexHits G f := fun t ht => hHG.1 ht
  have hfin : (curveVertexHits H f).Finite := hf.2.2.2.subset hsub
  have hcount : curveL H f ≤ curveL G f := ncard_le_ncard hsub hf.2.2.2
  refine ⟨⟨hnormal, hf.2.1, hf.2.2.1, hfin⟩, ?_⟩
  have hreal : (curveL H f : ℝ) ≤ curveL G f := Nat.cast_le.mpr hcount
  have hmul := mul_le_mul_of_nonneg_left hreal (inv_nonneg.mpr (Nat.cast_nonneg k : (0 : ℝ) ≤ k))
  change windingNumber f + (k : ℝ)⁻¹ * (curveL H f : ℝ) ≤
    windingNumber f + (k : ℝ)⁻¹ * (curveL G f : ℝ)
  linarith only [hmul]

/-- A retained-side helix avoiding the discarded point set except
at the attachment is already an old helix with exactly the same potential. -/
theorem helix_of_separation_avoids_discarded_side
    {k : ℕ} {G G₁ G₂ : Drawing ClosedCylinder}
    (hsep : IsGraphSeparation G.toGraph G₁.toGraph G₂.toGraph)
    {s : ClosedCylinder} (hs : s ∈ G₁.V)
    (f : Curve ClosedCylinder) (hf : IsHelix k G₁ f)
    (havoid : range f ∩ G₂.U ⊆ {s}) :
    IsHelix k G f ∧ curvePhi k G f = curvePhi k G₁ f := by
  have h₁ : G₁.IsSubdrawing G := ⟨hsep.1.vertexSet_mono, hsep.1.edgeSet_mono⟩
  have hU := (point_sets_of_graph_separation hsep).1
  have hnormal : IsNormalCurve G f := by
    rintro x ⟨hxF, hxU⟩
    rcases hU ▸ hxU with hx₁ | hx₂
    · exact h₁.1 (hf.1 ⟨hxF, hx₁⟩)
    · have hxs : x = s := havoid ⟨hxF, hx₂⟩
      exact hxs ▸ h₁.1 hs
  have hhits : curveVertexHits G f = curveVertexHits G₁ f := by
    ext t
    constructor
    · intro ht
      rcases hU ▸ G.V_subset_U ht with ht₁ | ht₂
      · exact vertex_mem_of_mem_subdrawing_point_set h₁ ht₁ ht
      · have hts : f t = s := havoid ⟨mem_range_self t, ht₂⟩
        change f t ∈ G₁.V
        exact hts ▸ hs
    · exact fun ht => h₁.1 ht
  exact ⟨⟨hnormal, hf.2.1, hf.2.2.1, hhits.symm ▸ hf.2.2.2⟩,
    by simp only [curvePhi, curveL, hhits]⟩

end GraphMinor.GM06
