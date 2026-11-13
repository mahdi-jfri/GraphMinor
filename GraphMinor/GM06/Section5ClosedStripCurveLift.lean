module

public import GraphMinor.GM06.Section5LinkageStripCircle
public import GraphMinor.GM06.Section5RadialProjection
import GraphMinor.GM06.Section5StripInjective

/-!
# Lifting a curve to a closed strip with injective projection

For at least two paths in VI (5.5), page 131, the closed linkage
strip projects injectively. Compactness makes its projection a
homeomorphism onto its image. A curve lying in that image therefore
lifts continuously to the closed strip, with unique endpoint copies.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- A curve in the image of a closed linkage strip lifts to that
strip when k is at least two, as used in VI (5.5), page 131. -/
theorem exists_curve_lift_to_injective_strip
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (hk : 1 < k) (hθ : L.HasTheta θ) (m : ℤ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L m)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (f : Curve ClosedCylinder) (hf : range f ⊆ radialCylinderProjection '' D) :
    ∃ q : Curve D, ∀ t, radialCylinderProjection (q t).1 = f t := by
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD.isCompact
  let φ : D → ClosedCylinder := fun p => radialCylinderProjection p.1
  have hφc : Continuous φ := continuous_radialCylinderProjection.comp continuous_subtype_val
  have hinj := injOn_radialCylinderProjection_stripDisc L hG hk hθ m hD hBd hstrip
  have hφi : Function.Injective φ := fun p q h => Subtype.ext (hinj p.2 q.2 h)
  let e : D ≃ₜ range φ := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofInjective φ hφi) hφc.rangeFactorization
  have hfRange (t : unitInterval) : f t ∈ range φ := by
    obtain ⟨p, hp, hpf⟩ := hf (mem_range_self t)
    exact ⟨⟨p, hp⟩, hpf⟩
  let q : Curve D := ⟨fun t => e.symm ⟨f t, hfRange t⟩,
    e.symm.continuous.comp (f.continuous.subtype_mk hfRange)⟩
  refine ⟨q, ?_⟩
  intro t
  exact congrArg Subtype.val (e.apply_symm_apply ⟨f t, hfRange t⟩)

end GraphMinor.GM06
