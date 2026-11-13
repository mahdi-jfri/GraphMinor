module

public import GraphMinor.GM06.Section5PolarRimCoordinates
public import GraphMinor.Surface.CrossCut
import GraphMinor.GM06.Section5PolarDiscInterior

/-!
# Polar rays as parametrized arcs

For the directed-end labels in VI (5.7), page 133, the segment
from the centre of a polar chart to a rim direction is an arc.
The norm recovers its radial parameter. At positive radius the
point also determines its direction, so distinct such arcs meet
only at the centre.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval
universe u

/-- The radial segment from the centre of an embedded disc to a rim point. -/
@[expose] noncomputable def polarRayMap {S : Type u} [TopologicalSpace S]
    (Φ : C(ClosedUnitDisc, S)) (w : Circle) : C(I, S) where
  toFun t := Φ (polarDiscPoint t w)
  continuous_toFun := by
    have heq : (fun t : I => Φ (polarDiscPoint t w)) =
        fun t : I => Φ (discScale t (polarDiscPoint 1 w)) := by
      funext t
      rw [discScale_polarDiscPoint_one]
    rw [heq]
    exact Φ.continuous.comp (continuous_discScale.comp
      (continuous_id.prodMk continuous_const))

/-- The radial segment starts at the centre. -/
theorem polarRayMap_zero {S : Type u} [TopologicalSpace S]
    (Φ : C(ClosedUnitDisc, S)) (w : Circle) : polarRayMap Φ w 0 = Φ polarCentre := by
  change Φ (polarDiscPoint 0 w) = _
  have hh : polarDiscPoint 0 w = polarCentre := Subtype.ext (by simp [polarDiscPoint, polarCentre])
  rw [hh]

/-- The radial segment ends at its specified rim point. -/
theorem polarRayMap_one {S : Type u} [TopologicalSpace S]
    (Φ : C(ClosedUnitDisc, S)) (w : Circle) : polarRayMap Φ w 1 = polarRimMap Φ w := rfl

/-- An injective disc chart parametrizes each radial segment injectively. -/
theorem isArcMap_polarRayMap {S : Type u} [TopologicalSpace S]
    {Φ : C(ClosedUnitDisc, S)} (hΦ : Function.Injective Φ) (w : Circle) :
    IsArcMap (polarRayMap Φ w) := by
  refine ⟨(polarRayMap Φ w).continuous, ?_⟩
  intro r s hrs
  have hpoint := hΦ hrs
  apply Subtype.ext
  have hn := congrArg (fun z : ClosedUnitDisc => ‖z.1‖) hpoint
  simpa only [norm_polarDiscPoint] using hn

/-- A noncentral point in radial coordinates has only one direction. -/
theorem polarDiscPoint_direction_eq {r s : I} {w z : Circle}
    (hr : 0 < r) (h : polarDiscPoint r w = polarDiscPoint s z) : w = z := by
  have hn := congrArg (fun p : ClosedUnitDisc => ‖p.1‖) h
  simp only [norm_polarDiscPoint] at hn
  have hrs : r = s := Subtype.ext hn
  subst s
  have hh := congrArg (fun p : ClosedUnitDisc => planeOf.symm p.1) h
  change planeOf.symm (planeOf ((r : ℂ) * w)) =
    planeOf.symm (planeOf ((r : ℂ) * z)) at hh
  simp only [planeOf.symm_apply_apply] at hh
  apply Circle.ext
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt (show (0 : ℝ) < r from hr))) hh

end GraphMinor.GM06
