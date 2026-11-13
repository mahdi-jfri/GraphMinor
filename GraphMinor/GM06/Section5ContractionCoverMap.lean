module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM06.Section5CoverTranslation
import GraphMinor.GM06.Section5CoverSides
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Fibres of a lifted contraction away from the collapsed vertex

For the winding-sensitive lifting in VI (5.5), page 130, the lift of
the contraction is bijective away from lifts of the collapsed vertex.
Two points above the same cylinder point differ by a full-turn
translation, and equivariance fixes the required sheet uniquely.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- Two points of the angular cover with the same projection differ
by an integral full-turn translation. -/
theorem exists_cover_translation_of_projection_eq
    {p q : CylinderCover} (he : cylinderCoverProjection p = cylinderCoverProjection q) :
    ∃ z : ℤ, p = cylinderCoverTranslation z q := by
  have hrad := congrArg (fun x : ClosedCylinder => x.1.1) he
  have hang := congrArg (fun x : ClosedCylinder => x.1.2) he
  obtain ⟨z, hz⟩ := Circle.exp_eq_exp.mp hang
  refine ⟨z, Prod.ext (Subtype.ext hrad) hz⟩

/-- Equivariance makes a cover map injective on each fibre of the
cover projection, even above an exceptional contraction value. -/
theorem cover_map_injective_on_projection_fibre
    (Φ : C(CylinderCover, CylinderCover))
    (htrans : ∀ z p, Φ (cylinderCoverTranslation z p) = cylinderCoverTranslation z (Φ p))
    {p q : CylinderCover} (hbase : cylinderCoverProjection p = cylinderCoverProjection q)
    (he : Φ p = Φ q) : p = q := by
  obtain ⟨z, hz⟩ := exists_cover_translation_of_projection_eq hbase
  have hangle : (Φ q).2 + (z : ℝ) * (2 * Real.pi) = (Φ q).2 := by
    have hh := he
    rw [hz, htrans] at hh
    exact congrArg Prod.snd hh
  apply Prod.ext
  · have hh : p.1 = (cylinderCoverTranslation z q).1 := congrArg Prod.fst hz
    exact hh
  · have hpa : p.2 = q.2 + (z : ℝ) * (2 * Real.pi) := congrArg Prod.snd hz
    linarith only [hangle, hpa]

/-- The cover lift of a contraction is injective off the exceptional
value, provided it commutes with full-turn translations. -/
theorem cover_contraction_injective_away_from_value
    (π : C(ClosedCylinder, ClosedCylinder)) (Φ : C(CylinderCover, CylinderCover))
    (s : ClosedCylinder)
    (hproj : ∀ p, cylinderCoverProjection (Φ p) = π (cylinderCoverProjection p))
    (htrans : ∀ z p, Φ (cylinderCoverTranslation z p) = cylinderCoverTranslation z (Φ p))
    (hinj : ∀ x y, π x ≠ s → π y ≠ s → π x = π y → x = y)
    {p q : CylinderCover} (hp : cylinderCoverProjection (Φ p) ≠ s)
    (he : Φ p = Φ q) : p = q := by
  have hbase : cylinderCoverProjection p = cylinderCoverProjection q :=
    hinj _ _ (hproj p ▸ hp) (by rw [← hproj q, ← he]; exact hp)
      ((hproj p).symm.trans ((congrArg cylinderCoverProjection he).trans (hproj q)))
  exact cover_map_injective_on_projection_fibre Φ htrans hbase he

/-- Every nonexceptional target sheet has a preimage under the lifted
contraction, using surjectivity of the cylinder contraction off its value. -/
theorem cover_contraction_surjective_away_from_value
    (π : C(ClosedCylinder, ClosedCylinder)) (Φ : C(CylinderCover, CylinderCover))
    (s : ClosedCylinder)
    (hproj : ∀ p, cylinderCoverProjection (Φ p) = π (cylinderCoverProjection p))
    (htrans : ∀ z p, Φ (cylinderCoverTranslation z p) = cylinderCoverTranslation z (Φ p))
    (hsurj : ∀ x, x ≠ s → ∃ y, π y = x)
    (q : CylinderCover) (hq : cylinderCoverProjection q ≠ s) : ∃ p, Φ p = q := by
  obtain ⟨x, hx⟩ := hsurj _ hq
  obtain ⟨a, ha⟩ := Circle.exp_surjective x.1.2
  let p : CylinderCover := (⟨x.1.1, x.2.1⟩, a)
  have hpx : cylinderCoverProjection p = x := by
    apply Subtype.ext
    exact Prod.ext rfl ha
  have hΦp : cylinderCoverProjection (Φ p) = cylinderCoverProjection q := by
    rw [hproj, hpx, hx]
  obtain ⟨z, hz⟩ := exists_cover_translation_of_projection_eq hΦp.symm
  exact ⟨cylinderCoverTranslation z p, (htrans z p).trans hz.symm⟩

end GraphMinor.GM06
