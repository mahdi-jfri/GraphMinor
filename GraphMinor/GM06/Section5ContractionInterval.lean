module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM06.Section5CoverTranslation
import GraphMinor.GM06.Section5ContractionCoverRegions
import GraphMinor.GM06.Section5ContractionExceptionalPiece
import GraphMinor.GM06.Section5ContractionMixedPiece
import GraphMinor.GM06.Section5ContractionCoverInverse
import GraphMinor.GM06.Section5ContractionSection
import GraphMinor.GM06.Section5ContractionLiftedNeighbourContact
import GraphMinor.GM06.Section5LiftedRegionBridge
import GraphMinor.GM06.Section4
import GraphMinor.GM11.Walks

/-!
# Replacing one vertex-free interval through contraction

For Reduction 3 of VI (5.5), page 130, retain the inverse lift
when both ends are nonexceptional. At an exceptional end, replace
its approach by the neighbour approach in the prescribed region
and sheet. Reversal handles the opposite endpoint. This gives the
local replacement used for each interval between consecutive vertex visits.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- Every lifted interval whose interior misses the augmented new
drawing has an old replacement between its section endpoints. -/
theorem exists_lifted_region_replacement
    {k : ℕ} {G F F' : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (hGF : G.IsSubdrawing F)
    (hFU : F.U = G.U ∪ bd ClosedCylinder) (i : Fin k)
    {e : Set ClosedCylinder} {v : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink e (cylinderM1Point k i) v)
    (hv : v ≠ cylinderM1Point k i) (hvC : v ∉ cylinderCuff2)
    (π : C(ClosedCylinder, ClosedCylinder)) (Φ : C(CylinderCover, CylinderCover))
    (hproj : ∀ p, cylinderCoverProjection (Φ p) = π (cylinderCoverProjection p))
    (htrans : ∀ z p, Φ (cylinderCoverTranslation z p) = cylinderCoverTranslation z (Φ p))
    (hfix : ∀ p, cylinderCoverProjection p ∈ bd ClosedCylinder → Φ p = p)
    (hinj : ∀ x y, π x ≠ cylinderM1Point k i → π y ≠ cylinderM1Point k i → π x = π y → x = y)
    (hsurj : ∀ x, x ≠ cylinderM1Point k i → ∃ y, π y = x)
    (hU : F'.U = π '' F.U) (hs : cylinderM1Point k i ∈ F'.U)
    (hfibre : π ⁻¹' {cylinderM1Point k i} = closure e)
    (ρ : CylinderCover → CylinderCover) (hρ : ∀ q, Φ (ρ q) = q)
    (hρv : ∀ q, cylinderCoverProjection q = cylinderM1Point k i → cylinderCoverProjection (ρ q) = v)
    (f : C(unitInterval, CylinderCover))
    (hf : ∀ t, 0 < t → t < 1 → cylinderCoverProjection (f t) ∉ F'.U) :
    ∃ g : C(unitInterval, CylinderCover), g 0 = ρ (f 0) ∧ g 1 = ρ (f 1) ∧
      ∀ t, 0 < t → t < 1 → cylinderCoverProjection (g t) ∉ F.U := by
  by_cases hf0 : cylinderCoverProjection (f 0) = cylinderM1Point k i
  · by_cases hf1 : cylinderCoverProjection (f 1) = cylinderM1Point k i
    · exact exists_lifted_region_replacement_between_exceptional_values L hG hGF hFU i
        hval hl hv hvC π Φ hproj htrans hfix hinj hsurj hU hs hfibre ρ hρ hρv f hf hf0 hf1
    · let f' : C(unitInterval, CylinderCover) := ⟨fun t => f (unitInterval.symm t), by fun_prop⟩
      have hf' (t) (ht0 : 0 < t) (ht1 : t < 1) : cylinderCoverProjection (f' t) ∉ F'.U := by
        apply hf
        · change (0 : ℝ) < 1 - (t : ℝ)
          have ht : (t : ℝ) < 1 := ht1
          linarith only [ht]
        · change 1 - (t : ℝ) < 1
          have ht : 0 < (t : ℝ) := ht0
          linarith only [ht]
      have hf'0 : f' 0 = f 1 := by change f (unitInterval.symm 0) = _; rw [unitInterval.symm_zero]
      have hf'1 : f' 1 = f 0 := by change f (unitInterval.symm 1) = _; rw [unitInterval.symm_one]
      obtain ⟨g', hg'0, hg'1, hg'⟩ := exists_lifted_region_replacement_ending_at_exceptional_value
        L hG hGF hFU i hval hl hv hvC π Φ hproj htrans hfix hinj hsurj hU hs hfibre
        ρ hρ hρv f' hf' (by rw [hf'0]; exact hf1) (by rw [hf'1]; exact hf0)
      let g : C(unitInterval, CylinderCover) := ⟨fun t => g' (unitInterval.symm t), by fun_prop⟩
      refine ⟨g, ?_, ?_, ?_⟩
      · change g' (unitInterval.symm 0) = _
        rw [unitInterval.symm_zero, hg'1, hf'1]
      · change g' (unitInterval.symm 1) = _
        rw [unitInterval.symm_one, hg'0, hf'0]
      · intro t ht0 ht1
        apply hg'
        · change (0 : ℝ) < 1 - (t : ℝ)
          have ht : (t : ℝ) < 1 := ht1
          linarith only [ht]
        · change 1 - (t : ℝ) < 1
          have ht : 0 < (t : ℝ) := ht0
          linarith only [ht]
  · by_cases hf1 : cylinderCoverProjection (f 1) = cylinderM1Point k i
    · exact exists_lifted_region_replacement_ending_at_exceptional_value L hG hGF hFU i
        hval hl hv hvC π Φ hproj htrans hfix hinj hsurj hU hs hfibre ρ hρ hρv f hf hf0 hf1
    · have havoid (t) : cylinderCoverProjection (f t) ≠ cylinderM1Point k i := by
        by_cases ht0 : t = 0
        · rw [ht0]; exact hf0
        by_cases ht1 : t = 1
        · rw [ht1]; exact hf1
        have htpos : 0 < t := lt_of_le_of_ne bot_le (show t ≠ 0 from ht0).symm
        have htlt : t < 1 := lt_of_le_of_ne le_top (show t ≠ 1 from ht1)
        intro he
        exact hf t htpos htlt (he ▸ hs)
      have hρc := continuousOn_section_away_from_cover_contraction π Φ (cylinderM1Point k i)
        hproj htrans hinj hsurj ρ hρ
      let g : C(unitInterval, CylinderCover) :=
        ⟨fun t => ρ (f t), hρc.comp_continuous f.continuous havoid⟩
      exact ⟨g, rfl, rfl, fun t ht0 ht1 => not_mem_drawing_of_cover_contraction_section
        π Φ hproj hU ρ hρ (hf t ht0 ht1)⟩

end GraphMinor.GM06
