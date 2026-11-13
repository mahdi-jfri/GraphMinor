module

public import GraphMinor.GM06.Section5RadialProjection
import GraphMinor.GM06.Section5EndpointVertexCount
import GraphMinor.GM06.Section4Winding
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Projecting and counting the prescribed-side approach

For VI (5.5), page 131, project the approach chosen in the cut disc.
Its source is the right initial copy, at angle four pi. Its interior
misses the drawing, so only its endpoint parameters can be vertex
times. The angular coordinate of the cut-disc curve is an actual
lift of its projection. Thus its displacement gives the winding
without losing the side information.
-/

public section
namespace GraphMinor.GM06
open Set Real GraphMinor.Surface

open Classical in
/-- Project a cut-disc approach from the right initial copy. This
retains its endpoints, normality, exact count and lifted winding
for the one-path Reduction 1 proof of VI (5.5). -/
theorem exists_projected_right_cut_approach
    {G : Drawing ClosedCylinder} (hG : IsCylinderSection5Drawing 1 G)
    {D : Set (ℝ × ℝ)} (g q : Curve D)
    (hgcoord : ∀ t, (g t).1 = (1, 2 * (1 + (t : ℝ)) * π))
    (hq0 : q 0 = g 1) {v : D} (hq1 : q 1 = v)
    {w : ClosedCylinder} (hvw : radialCylinderProjection v.1 = w)
    (hTarget : w ∈ G.V ∨ w ∉ G.U)
    (hInterior : ∀ t : unitInterval, 0 < t → t < 1 →
      radialCylinderProjection (q t).1 ∉ G.U) :
    ∃ a : Curve ClosedCylinder,
      (∀ t, a t = radialCylinderProjection (q t).1) ∧
      a 0 = cylinderM1Point 1 0 ∧ a 1 = w ∧ IsNormalCurve G a ∧
      (curveVertexHits G a).Finite ∧ curveL G a = 1 + (if w ∈ G.V then 1 else 0) ∧
      windingNumber a = (v.1.2 - 4 * π) / (2 * π) := by
  classical
  let a : Curve ClosedCylinder :=
    ⟨fun t => radialCylinderProjection (q t).1,
      continuous_radialCylinderProjection.comp (continuous_subtype_val.comp q.continuous)⟩
  have ha0 : a 0 = cylinderM1Point 1 0 := by
    change radialCylinderProjection (q 0).1 = _
    rw [hq0, hgcoord 1]
    apply Subtype.ext
    apply Prod.ext
    · change max 1 (min 2 1) = 1
      norm_num
    · change Circle.exp (2 * (1 + ((1 : unitInterval) : ℝ)) * π) =
        (cylinderM1Point 1 0).1.2
      norm_num [cylinderM1Point, cylinderPoint]
      have he : (4 : ℝ) * π = 2 * π + 2 * π := by ring
      rw [he, Circle.exp_add_two_pi, Circle.exp_two_pi]
  have ha1 : a 1 = w := by change radialCylinderProjection (q 1).1 = w; rw [hq1, hvw]
  have hsV : cylinderM1Point 1 0 ∈ G.V := by
    have hmem : cylinderM1Point 1 0 ∈ cylinderM1 1 ∪ cylinderM2 1 := Or.inl ⟨0, rfl⟩
    exact (show cylinderM1Point 1 0 ∈ G.V ∩ bd ClosedCylinder from hG.2.2.symm ▸ hmem).1
  have hstart : a 0 ∈ G.V := ha0.symm ▸ hsV
  have hcount := curveL_of_interior_disjoint_drawing a hstart hInterior
  have hEnd : a 1 ∈ G.V ∨ a 1 ∉ G.U := ha1.symm ▸ hTarget
  have hnormal := isNormalCurve_of_interior_disjoint_drawing a hstart hEnd hInterior
  have hlen : curveL G a = 1 + (if w ∈ G.V then 1 else 0) := by
    simpa only [ha1] using hcount.2
  refine ⟨a, (fun _ => rfl), ha0, ha1, hnormal, hcount.1, hlen, ?_⟩
  let b : C(unitInterval, ℝ) := ⟨fun t => (q t).1.2,
    continuous_snd.comp (continuous_subtype_val.comp q.continuous)⟩
  have hb (t : unitInterval) : Circle.exp (b t) = (a t).1.2 := rfl
  rw [windingNumber_eq_of_exp_lift b hb]
  change ((q 1).1.2 - (q 0).1.2) / (2 * π) = _
  rw [hq1, hq0, hgcoord 1]
  norm_num

end GraphMinor.GM06
