module

public import GraphMinor.GM06.Section5ReflectionDrawing
import GraphMinor.GM06.Section5ReflectionBoundary

/-!
# Reflecting helices and their vertex counts

In the orientation reversal of VI (5.10), page 134, reflected
helices keep exactly the same vertex-visit parameters. Their winding
changes sign and their prescribed dual ends are permuted. Therefore
the lower helix expression after reflection is the negative of the
old upper potential, as required for the minimum feasible winding.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- Simultaneous reflection of drawing and curve preserves every
parameter at which a vertex is visited. -/
theorem curveVertexHits_section5ReflectedCurve (k : ℕ) (G : Drawing ClosedCylinder)
    (f : Curve ClosedCylinder) :
    curveVertexHits (section5ReflectedDrawing k G) (section5ReflectedCurve k f) = curveVertexHits G f := by
  ext t
  exact section5ReflectedDrawing_mem_V k G (f t)

/-- Reflection preserves the number of vertex-visit parameters. -/
theorem curveL_section5ReflectedCurve (k : ℕ) (G : Drawing ClosedCylinder)
    (f : Curve ClosedCylinder) :
    curveL (section5ReflectedDrawing k G) (section5ReflectedCurve k f) = curveL G f := by
  unfold curveL
  rw [curveVertexHits_section5ReflectedCurve]

/-- Reflection takes a helix to a helix in the reflected drawing. -/
theorem isHelix_section5ReflectedCurve
    {k : ℕ} {G : Drawing ClosedCylinder} (hk : 0 < k)
    (f : Curve ClosedCylinder) (hf : IsHelix k G f) :
    IsHelix k (section5ReflectedDrawing k G) (section5ReflectedCurve k f) := by
  have hn : IsNormalCurve (section5ReflectedDrawing k G) (section5ReflectedCurve k f) := by
    rintro x ⟨⟨t, rfl⟩, hxG⟩
    apply (section5ReflectedDrawing_mem_V k G (f t)).mpr
    exact hf.1 ⟨mem_range_self t, (section5ReflectedDrawing_mem_U k G (f t)).mp hxG⟩
  refine ⟨hn, ?_, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hf.2.1
    refine ⟨Fin.rev i, ?_⟩
    change cylinderN1Point k (Fin.rev i) = section5CylinderReflection k (f 0)
    rw [← hi, section5CylinderReflection_N1 hk]
  · obtain ⟨i, hi⟩ := hf.2.2.1
    refine ⟨Fin.rev i, ?_⟩
    change cylinderN2Point k (Fin.rev i) = section5CylinderReflection k (f 1)
    rw [← hi, section5CylinderReflection_N2 hk]
  · rw [curveVertexHits_section5ReflectedCurve]
    exact hf.2.2.2

/-- The reflected lower expression is the negative of the original
upper helix potential. -/
theorem reflected_lower_eq_neg_curvePhi (k : ℕ) (G : Drawing ClosedCylinder)
    (f : Curve ClosedCylinder) :
    windingNumber (section5ReflectedCurve k f) -
        (k : ℝ)⁻¹ * (curveL (section5ReflectedDrawing k G) (section5ReflectedCurve k f) : ℝ) =
      -curvePhi k G f := by
  rw [windingNumber_section5ReflectedCurve, curveL_section5ReflectedCurve]
  unfold curvePhi
  ring

end GraphMinor.GM06
