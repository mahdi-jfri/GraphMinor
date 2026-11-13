module

public import GraphMinor.GM11.LocalCone
public import GraphMinor.GM06.Section5PolarRimCoordinates

/-!
# Access curves along polar rays

For VI (5.5), page 130, a rim direction in a retained region gives
an access curve from the attachment. The polar embedding makes
these radial curves injective, with the centre as their only
possible common point for distinct angular directions.
-/

@[expose] public section
namespace GraphMinor.GM06
open Set Topology Metric GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- The access curve following one direction from the polar centre. -/
noncomputable def polarRayCurve {S : Type*} [TopologicalSpace S]
    (Φ : C(ClosedUnitDisc, S)) (w : Circle) : C(I, S) where
  toFun c := Φ (polarDiscPoint c w)
  continuous_toFun := Φ.continuous.comp (by
    apply Continuous.subtype_mk
    change Continuous (fun c : I => planeOf ((c : ℂ) * w))
    fun_prop)

/-- Each polar access curve starts at the attachment. -/
theorem polarRayCurve_zero
    {S : Type*} [TopologicalSpace S] {Γ : Drawing S} {s : S}
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ s Φ) (w : Circle) :
    polarRayCurve Φ w 0 = s := by
  have he : polarDiscPoint 0 w = polarCentre := by
    apply Subtype.ext
    simp [polarDiscPoint, polarCentre]
  change Φ (polarDiscPoint 0 w) = s
  rw [he, hp.centre]

/-- Injectivity of the disc chart makes every radial access curve injective. -/
theorem polarRayCurve_injective
    {S : Type*} [TopologicalSpace S] {Γ : Drawing S} {s : S}
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ s Φ) (w : Circle) :
    Function.Injective (polarRayCurve Φ w) := by
  intro c d he
  have he' := congrArg (fun x : ClosedUnitDisc => ‖x.1‖) (hp.inj he)
  have hn (t : I) : ‖(polarDiscPoint t w).1‖ = (t : ℝ) := by
    simp [polarDiscPoint, norm_mul, Complex.norm_real, Real.norm_of_nonneg t.2.1]
  apply Subtype.ext
  simpa only [hn] using he'

end GraphMinor.GM06
