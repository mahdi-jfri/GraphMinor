module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM06.Section5CoverTranslation
public import Mathlib.Topology.Maps.Proper.Basic
import GraphMinor.GM06.Section5ContractionCoverMap
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Bounded angular displacement of a lifted contraction

The lifted contraction used in VI (5.5), page 130, commutes with
full turns. Its angular displacement therefore has the same values
on every sheet. Continuity on one compact fundamental strip bounds
that displacement on the entire cover.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- A continuous map of the cylinder cover commuting with full turns
has uniformly bounded angular displacement. -/
theorem exists_bound_cover_angular_displacement
    (Φ : C(CylinderCover, CylinderCover))
    (htrans : ∀ z p, Φ (cylinderCoverTranslation z p) = cylinderCoverTranslation z (Φ p)) :
    ∃ C : ℝ, ∀ p, |(Φ p).2 - p.2| ≤ C := by
  let D : Set CylinderCover := univ ×ˢ Icc (-Real.pi) Real.pi
  have hD : IsCompact D := isCompact_univ.prod isCompact_Icc
  have hc : Continuous (fun p : CylinderCover => |(Φ p).2 - p.2|) :=
    ((continuous_snd.comp Φ.continuous).sub continuous_snd).abs
  obtain ⟨C, hC⟩ := (hD.image hc).bddAbove
  refine ⟨C, fun p => ?_⟩
  let q : CylinderCover := (p.1, (Circle.exp p.2).val.arg)
  have hqD : q ∈ D := ⟨mem_univ _, (Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩
  have hpq : cylinderCoverProjection p = cylinderCoverProjection q := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (Circle.exp_arg _).symm
  obtain ⟨z, hz⟩ := exists_cover_translation_of_projection_eq hpq
  have hb : |(Φ q).2 - q.2| ≤ C := hC (mem_image_of_mem _ hqD)
  rw [hz, htrans]
  change |(Φ q).2 + (z : ℝ) * (2 * Real.pi) -
    (q.2 + (z : ℝ) * (2 * Real.pi))| ≤ C
  convert hb using 1
  congr 1
  ring

/-- Full-turn equivariance makes a continuous cover map proper:
compact target sets have compact preimages in a bounded strip. -/
theorem isProperMap_cover_of_commutes_with_translation
    (Φ : C(CylinderCover, CylinderCover))
    (htrans : ∀ z p, Φ (cylinderCoverTranslation z p) = cylinderCoverTranslation z (Φ p)) :
    IsProperMap Φ := by
  obtain ⟨C, hC⟩ := exists_bound_cover_angular_displacement Φ htrans
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨Φ.continuous, fun K hK => ?_⟩
  obtain ⟨B, hB⟩ := (hK.image continuous_snd.abs).bddAbove
  have hbound (p : CylinderCover) (hp : p ∈ Φ ⁻¹' K) : |p.2| ≤ B + C := by
    have hb : |(Φ p).2| ≤ B := hB (mem_image_of_mem _ hp)
    calc
      |p.2| = |(p.2 - (Φ p).2) + (Φ p).2| := by congr 1; ring
      _ ≤ |p.2 - (Φ p).2| + |(Φ p).2| := abs_add_le _ _
      _ ≤ C + B := add_le_add (by rw [abs_sub_comm]; exact hC p) hb
      _ = B + C := add_comm _ _
  have hcompact : IsCompact (univ ×ˢ Icc (-(B + C)) (B + C) : Set CylinderCover) :=
    isCompact_univ.prod isCompact_Icc
  exact hcompact.of_isClosed_subset (hK.isClosed.preimage Φ.continuous)
    (fun p hp => ⟨mem_univ _, abs_le.mp (hbound p hp)⟩)

/-- The lifted contraction is closed, which allows region closures
to be pulled back while retaining their angular sheets. -/
theorem isClosedMap_cover_of_commutes_with_translation
    (Φ : C(CylinderCover, CylinderCover))
    (htrans : ∀ z p, Φ (cylinderCoverTranslation z p) = cylinderCoverTranslation z (Φ p)) :
    IsClosedMap Φ :=
  (isProperMap_cover_of_commutes_with_translation Φ htrans).isClosedMap

end GraphMinor.GM06
