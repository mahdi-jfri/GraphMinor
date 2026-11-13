module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM06.Section5CoverTranslation
import GraphMinor.GM06.Section5ContractionCoverRegions
import GraphMinor.GM06.Section5ContractionCoverInverse
import GraphMinor.GM06.Section5ContractionLiftedNeighbourContact
import GraphMinor.GM06.Section5LiftedRegionBridge
import GraphMinor.GM06.Section4
import GraphMinor.GM11.Walks

/-!
# Replacing an interval ending at an exceptional value

For Reduction 3 of VI (5.5), page 130, keep the old inverse lift
of an initial half of a vertex-free interval. Join its midpoint
to the prescribed old neighbour through the same lifted region.
The inverse remains continuous on the retained half because its
initial point is nonexceptional and its remaining points miss the drawing.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- Replace a vertex-free lifted interval whose initial value is
nonexceptional and whose final value is exceptional. -/
theorem exists_lifted_region_replacement_ending_at_exceptional_value
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
    (hf : ∀ t, 0 < t → t < 1 → cylinderCoverProjection (f t) ∉ F'.U)
    (hf0 : cylinderCoverProjection (f 0) ≠ cylinderM1Point k i)
    (hf1 : cylinderCoverProjection (f 1) = cylinderM1Point k i) :
    ∃ g : C(unitInterval, CylinderCover), g 0 = ρ (f 0) ∧ g 1 = ρ (f 1) ∧
      ∀ t, 0 < t → t < 1 → cylinderCoverProjection (g t) ∉ F.U := by
  obtain ⟨Y, hY, hfin, hf0cl, hf1cl⟩ := exists_component_containing_curve_interior f
    (B := cylinderCoverProjection ⁻¹' F'.Uᶜ) hf
  have hFibSub : π ⁻¹' {cylinderM1Point k i} ⊆ F.U := by
    rw [hfibre]
    exact F.closure_subset_U (hGF.2 hl.1)
  have hC := preimage_lifted_component_of_contraction π Φ (cylinderM1Point k i)
    hproj htrans hinj hsurj hU hFibSub hs hY
  have hsbd : cylinderM1Point k i ∈ bd ClosedCylinder := by
    rw [bd_closedCylinder]
    exact Or.inl rfl
  have h1fix : Φ (f 1) = f 1 := hfix _ (hf1 ▸ hsbd)
  have h1cl := section_neighbour_mem_closure_preimage_lifted_region hG hGF hFU i
    hval hl hv π Φ hproj htrans hinj hsurj hU hs hfibre ρ hρ hρv (f 1) hf1 h1fix hY hf1cl
  let m : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
  have hm0 : 0 < m := by change (0 : ℝ) < 1 / 2; norm_num
  have hm1 : m < 1 := by change (1 / 2 : ℝ) < 1; norm_num
  have htime (t : unitInterval) (ht : 0 < t) : 0 < t * m ∧ t * m < 1 := by
    have hpos : 0 < (t : ℝ) * (m : ℝ) := mul_pos ht hm0
    have hle : (t : ℝ) * (m : ℝ) ≤ (m : ℝ) := mul_le_of_le_one_left hm0.le t.2.2
    exact ⟨hpos, lt_of_le_of_lt hle hm1⟩
  let P : C(unitInterval, CylinderCover) := ⟨fun t => f (t * m), by fun_prop⟩
  have hP0 : P 0 = f 0 := by change f (0 * m) = _; rw [zero_mul]
  have hP1 : P 1 = f m := by change f (1 * m) = _; rw [one_mul]
  have hPavoid (t) : cylinderCoverProjection (P t) ≠ cylinderM1Point k i := by
    by_cases ht : t = 0
    · rw [ht, hP0]; exact hf0
    · have htpos : 0 < t := lt_of_le_of_ne bot_le (show t ≠ 0 from ht).symm
      have hp := hf (t * m) (htime t htpos).1 (htime t htpos).2
      intro he
      exact hp (he ▸ hs)
  have hρc := continuousOn_section_away_from_cover_contraction π Φ (cylinderM1Point k i)
    hproj htrans hinj hsurj ρ hρ
  let a : C(unitInterval, CylinderCover) :=
    ⟨fun t => ρ (P t), hρc.comp_continuous P.continuous hPavoid⟩
  have ha0 : a 0 = ρ (f 0) := congrArg ρ hP0
  have ha1 : a 1 = ρ (f m) := congrArg ρ hP1
  have ha (t) (ht : 0 < t) : a t ∈ Φ ⁻¹' Y := by
    change Φ (ρ (P t)) ∈ Y
    rw [hρ]
    exact hfin (t * m) (htime t ht).1 (htime t ht).2
  have hx : ρ (f m) ∈ Φ ⁻¹' Y := by
    change Φ (ρ (f m)) ∈ Y
    rw [hρ]
    exact hfin m hm0 hm1
  obtain ⟨b, hb0, hb1, hb⟩ := exists_curve_from_contraction_neighbour_to_cover_region_point
    L hG i hGF hval hl hv hvC (ρ (f 1)) (hρv _ hf1) hC h1cl hx
  let p : Path (ρ (f 0)) (ρ (f m)) := ⟨a, ha0, ha1⟩
  let q : Path (ρ (f 1)) (ρ (f m)) := ⟨b, hb0, hb1⟩
  let g := (p.trans q.symm).toContinuousMap
  have hg0 : g 0 = ρ (f 0) := Path.source _
  have hg1 : g 1 = ρ (f 1) := Path.target _
  have hg (t) (ht0 : 0 < t) (ht1 : t < 1) : g t ∈ Φ ⁻¹' Y := by
    change (p.trans q.symm) t ∈ Φ ⁻¹' Y
    rw [Path.trans_apply]
    split_ifs with hhalf
    · apply ha
      change (0 : ℝ) < 2 * (t : ℝ)
      have ht : 0 < (t : ℝ) := ht0
      linarith only [ht]
    · apply hb
      change (0 : ℝ) < 1 - (2 * (t : ℝ) - 1)
      have ht : (t : ℝ) < 1 := ht1
      linarith only [ht]
  have hCsub : Φ ⁻¹' Y ⊆ cylinderCoverProjection ⁻¹' F.Uᶜ := by
    obtain ⟨x, _, heq⟩ := hC
    rw [← heq]
    exact connectedComponentIn_subset _ _
  exact ⟨g, hg0, hg1, fun t ht0 ht1 => hCsub (hg t ht0 ht1)⟩

end GraphMinor.GM06
