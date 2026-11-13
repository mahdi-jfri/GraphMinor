module

public import GraphMinor.GM11.LocalCone
public import GraphMinor.GM06.Section5PolarRimCoordinates
import GraphMinor.Surface.DiscGrow
import GraphMinor.Surface.DiscArcs

/-!
# Interior points of the polar disc have radius less than one

For VI (5.5), page 130, the attached seed covers all discarded
points in the open polar neighbourhood. The embedded disc chart
identifies its boundary with the unit rim. An interior image point
therefore has strictly smaller radius.
-/

public section
namespace GraphMinor.GM06
open Set Topology Metric GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- The radius of a polar point is its radial parameter. -/
theorem norm_polarDiscPoint (c : I) (w : Circle) : ‖(polarDiscPoint c w).1‖ = (c : ℝ) := by
  simp [polarDiscPoint, norm_mul, Complex.norm_real, Real.norm_of_nonneg c.2.1]

/-- A point whose image is in the interior of an embedded polar
disc has coordinate norm less than one. -/
theorem norm_lt_one_of_mem_interior_polar_disc
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {s : S}
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ s Φ)
    {x : ClosedUnitDisc} (hx : Φ x ∈ interior (range Φ)) : ‖x.1‖ < 1 := by
  have hemb := (Φ.continuous.isClosedEmbedding hp.inj).isEmbedding
  let e : ClosedUnitDisc ≃ₜ range Φ := hemb.toHomeomorph
  have hD : IsClosedDisc (range Φ) := ⟨e⟩
  have hxnot : Φ x ∉ discBd (range Φ) := by
    rw [interior_eq_sdiff_discBd hS hD] at hx
    exact hx.2
  have hxle : ‖x.1‖ ≤ 1 := mem_closedBall_zero_iff.mp x.2
  apply lt_of_le_of_ne hxle
  intro he
  apply hxnot
  rw [disc_boundary (range Φ) e]
  exact ⟨x, mem_sphere_zero_iff_norm.mpr he, rfl⟩

end GraphMinor.GM06
