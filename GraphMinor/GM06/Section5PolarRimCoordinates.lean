module

public import GraphMinor.GM11.PolarChart

/-!
# Radial and rim coordinates in a polar disc

The seed construction for VI (5.5), page 130, uses the same
angular coordinate at every radius. These coordinates identify
radial scaling with the scaling operation of the polar chart.
-/

@[expose] public section
namespace GraphMinor.GM06
open Set Topology Metric GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- The point of the Euclidean closed disc with radius c and direction w. -/
noncomputable def polarDiscPoint (c : I) (w : Circle) : ClosedUnitDisc :=
  ⟨planeOf ((c : ℂ) * w), by
    simp only [ClosedUnitDisc, mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map,
      norm_mul, Complex.norm_real, Circle.norm_coe, mul_one, Real.norm_of_nonneg c.2.1]
    exact c.2.2⟩

/-- Radial scaling preserves the angular coordinate. -/
theorem discScale_polarDiscPoint_one (c : I) (w : Circle) :
    discScale c (polarDiscPoint 1 w) = polarDiscPoint c w := by
  apply Subtype.ext
  change (c : ℝ) • planeOf (((1 : I) : ℂ) * w) = planeOf ((c : ℂ) * w)
  simp only [Icc.coe_one, Complex.ofReal_one, one_mul]
  rw [← map_smul]
  rfl

/-- A point on the polar rim is different from the centre. -/
theorem polarDiscPoint_one_ne_centre (w : Circle) : polarDiscPoint 1 w ≠ polarCentre := by
  intro he
  have he' := congrArg (fun x : ClosedUnitDisc => ‖x.1‖) he
  have hleft : ‖(polarDiscPoint 1 w).1‖ = 1 := by
    simp [polarDiscPoint]
  have hright : ‖(polarCentre : ClosedUnitDisc).1‖ = 0 := by simp [polarCentre]
  rw [hleft, hright] at he'
  exact one_ne_zero he'

/-- The rim of an embedded polar disc, with its angular parameter. -/
noncomputable def polarRimMap {S : Type*} [TopologicalSpace S]
    (Φ : C(ClosedUnitDisc, S)) : C(Circle, S) where
  toFun w := Φ (polarDiscPoint 1 w)
  continuous_toFun := Φ.continuous.comp (by
    apply Continuous.subtype_mk
    change Continuous (fun w : Circle => planeOf (((1 : I) : ℂ) * w))
    fun_prop)

end GraphMinor.GM06
