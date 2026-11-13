module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM06.Section5CoverTranslation
import GraphMinor.GM06.Section5ContractionCoverMap
import GraphMinor.GM06.Section5ContractionCoverBound
import Mathlib.Topology.LocalAtTarget

/-!
# The actual inverse of a lifted contraction off its exceptional values

In VI (5.5), page 130, unchanged pieces of the helix lift through
the contraction away from the collapsed vertex. Properness makes
the lifted map closed, and its off-fibre bijection is consequently
a homeomorphism. This gives continuous lifts in the chosen sheets.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- The actual lifted contraction is a homeomorphism off its
exceptional values, with its actual map as forward function. -/
theorem exists_homeomorph_away_from_cover_contraction
    (π : C(ClosedCylinder, ClosedCylinder)) (Φ : C(CylinderCover, CylinderCover))
    (s : ClosedCylinder)
    (hproj : ∀ p, cylinderCoverProjection (Φ p) = π (cylinderCoverProjection p))
    (htrans : ∀ z p, Φ (cylinderCoverTranslation z p) = cylinderCoverTranslation z (Φ p))
    (hinj : ∀ x y, π x ≠ s → π y ≠ s → π x = π y → x = y)
    (hsurj : ∀ x, x ≠ s → ∃ y, π y = x) :
    ∃ h : {p : CylinderCover // cylinderCoverProjection (Φ p) ≠ s} ≃ₜ
        {q : CylinderCover // cylinderCoverProjection q ≠ s},
      ∀ p, (h p).1 = Φ p.1 := by
  let φ : {p : CylinderCover // cylinderCoverProjection (Φ p) ≠ s} →
      {q : CylinderCover // cylinderCoverProjection q ≠ s} := fun p => ⟨Φ p, p.2⟩
  have hi : Function.Injective φ := by
    intro p q he
    exact Subtype.ext (cover_contraction_injective_away_from_value π Φ s hproj htrans hinj
      p.2 (congrArg Subtype.val he))
  have hs : Function.Surjective φ := by
    intro q
    obtain ⟨p, hp⟩ := cover_contraction_surjective_away_from_value π Φ s hproj htrans hsurj q q.2
    exact ⟨⟨p, by rw [hp]; exact q.2⟩, Subtype.ext hp⟩
  have hc : Continuous φ := (Φ.continuous.comp continuous_subtype_val).subtype_mk _
  have hclosed : IsClosedMap φ :=
    (isClosedMap_cover_of_commutes_with_translation Φ htrans).restrictPreimage
      {q : CylinderCover | cylinderCoverProjection q ≠ s}
  exact ⟨(Equiv.ofBijective φ ⟨hi, hs⟩).toHomeomorphOfContinuousClosed hc hclosed, fun _ => rfl⟩

/-- A curve missing every lift of the collapsed vertex lifts
continuously through the actual cover contraction. -/
theorem exists_curve_lift_avoiding_cover_contraction
    (π : C(ClosedCylinder, ClosedCylinder)) (Φ : C(CylinderCover, CylinderCover))
    (s : ClosedCylinder)
    (hproj : ∀ p, cylinderCoverProjection (Φ p) = π (cylinderCoverProjection p))
    (htrans : ∀ z p, Φ (cylinderCoverTranslation z p) = cylinderCoverTranslation z (Φ p))
    (hinj : ∀ x y, π x ≠ s → π y ≠ s → π x = π y → x = y)
    (hsurj : ∀ x, x ≠ s → ∃ y, π y = x)
    (f : C(unitInterval, CylinderCover)) (hf : ∀ t, cylinderCoverProjection (f t) ≠ s) :
    ∃ g : C(unitInterval, CylinderCover), ∀ t, Φ (g t) = f t := by
  obtain ⟨h, hh⟩ := exists_homeomorph_away_from_cover_contraction π Φ s hproj htrans hinj hsurj
  let g : C(unitInterval, CylinderCover) :=
    ⟨fun t => (h.symm ⟨f t, hf t⟩).1,
      continuous_subtype_val.comp (h.symm.continuous.comp (f.continuous.subtype_mk hf))⟩
  refine ⟨g, fun t => ?_⟩
  exact (hh _).symm.trans (congrArg Subtype.val (h.apply_symm_apply ⟨f t, hf t⟩))

/-- Any section of the actual cover contraction is continuous away
from the exceptional values, since there it equals the unique inverse. -/
theorem continuousOn_section_away_from_cover_contraction
    (π : C(ClosedCylinder, ClosedCylinder)) (Φ : C(CylinderCover, CylinderCover))
    (s : ClosedCylinder)
    (hproj : ∀ p, cylinderCoverProjection (Φ p) = π (cylinderCoverProjection p))
    (htrans : ∀ z p, Φ (cylinderCoverTranslation z p) = cylinderCoverTranslation z (Φ p))
    (hinj : ∀ x y, π x ≠ s → π y ≠ s → π x = π y → x = y)
    (hsurj : ∀ x, x ≠ s → ∃ y, π y = x)
    (ρ : CylinderCover → CylinderCover) (hρ : ∀ q, Φ (ρ q) = q) :
    ContinuousOn ρ {q | cylinderCoverProjection q ≠ s} := by
  obtain ⟨h, hh⟩ := exists_homeomorph_away_from_cover_contraction π Φ s hproj htrans hinj hsurj
  have hinv (q : {q : CylinderCover // cylinderCoverProjection q ≠ s}) :
      Φ (h.symm q).1 = q.1 :=
    (hh _).symm.trans (congrArg Subtype.val (h.apply_symm_apply q))
  have heq : (fun q : {q : CylinderCover // cylinderCoverProjection q ≠ s} => ρ q.1) =
      fun q => (h.symm q).1 := by
    funext q
    apply cover_contraction_injective_away_from_value π Φ s hproj htrans hinj
      (by rw [hρ]; exact q.2)
    exact (hρ _).trans (hinv q).symm
  apply continuousOn_iff_continuous_domRestrict.mpr
  change Continuous (fun q : {q : CylinderCover // cylinderCoverProjection q ≠ s} => ρ q.1)
  rw [heq]
  exact continuous_subtype_val.comp h.symm.continuous

end GraphMinor.GM06
