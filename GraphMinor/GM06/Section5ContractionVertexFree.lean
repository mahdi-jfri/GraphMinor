module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM06.Section5CoverTranslation
import GraphMinor.GM06.Section5ContractionCoverRegions
import GraphMinor.GM06.Section5ContractionInterval
import GraphMinor.GM06.Section5CoverSides
import GraphMinor.GM06.Section5ContractionExceptionalPiece
import GraphMinor.GM06.Section5ContractionMixedPiece
import GraphMinor.GM06.Section5ContractionCoverInverse
import GraphMinor.GM06.Section5ContractionSection
import GraphMinor.GM06.Section5ContractionLiftedNeighbourContact
import GraphMinor.GM06.Section5LiftedRegionBridge
import GraphMinor.GM06.Section4
import GraphMinor.GM11.Walks

/-!
# The vertex-free base case of contraction-curve induction

For Reduction 3 of VI (5.5), page 130, replace one interval with
no interior vertex visits by its constructed lifted-region curve.
Its endpoints have exactly the old section vertex memberships and
its interior avoids the old drawing. Thus it is normal and has
exactly the same vertex-hit set as the original interval.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- The base case with no interior vertex visits preserves
normality, finite vertex hits and their exact count. -/
theorem exists_cover_path_replacement_of_no_interior_vertex_hits
    {k : ℕ} {G G' F F' : Drawing ClosedCylinder} (L : CylinderLinkage k G)
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
    (hUG : G'.U = π '' G.U) (hVG : G'.V = π '' G.V)
    (hsV : cylinderM1Point k i ∈ G'.V) (hF'U : F'.U = G'.U ∪ bd ClosedCylinder)
    {a b : CylinderCover} (p : Path a b)
    (hnormal : IsNormalCurve G' (p.map continuous_cylinderCoverProjection).toContinuousMap)
    (hfin : (curveVertexHits G' (p.map continuous_cylinderCoverProjection).toContinuousMap).Finite)
    (hno : ∀ t, 0 < t → t < 1 → cylinderCoverProjection (p t) ∉ G'.V)
    (hoffbd : ∀ t, 0 < t → t < 1 → cylinderCoverProjection (p t) ∉ bd ClosedCylinder) :
    ∃ q : Path (ρ a) (ρ b),
      IsNormalCurve G (q.map continuous_cylinderCoverProjection).toContinuousMap ∧
      (curveVertexHits G (q.map continuous_cylinderCoverProjection).toContinuousMap).Finite ∧
      curveL G (q.map continuous_cylinderCoverProjection).toContinuousMap =
        curveL G' (p.map continuous_cylinderCoverProjection).toContinuousMap := by
  have havoid (t) (ht0 : 0 < t) (ht1 : t < 1) : cylinderCoverProjection (p t) ∉ F'.U := by
    rw [hF'U]
    rintro (htU | htbd)
    · exact hno t ht0 ht1 (hnormal ⟨mem_range_self t, htU⟩)
    · exact hoffbd t ht0 ht1 htbd
  obtain ⟨g, hg0, hg1, hgoff⟩ := exists_lifted_region_replacement L hG hGF hFU i
    hval hl hv hvC π Φ hproj htrans hfix hinj hsurj hU hs hfibre ρ hρ hρv p.toContinuousMap havoid
  have hg0a : g 0 = ρ a := hg0.trans (congrArg ρ p.source)
  have hg1b : g 1 = ρ b := hg1.trans (congrArg ρ p.target)
  let q : Path (ρ a) (ρ b) := ⟨g, hg0a, hg1b⟩
  let fG : Curve ClosedCylinder := (q.map continuous_cylinderCoverProjection).toContinuousMap
  let fG' : Curve ClosedCylinder := (p.map continuous_cylinderCoverProjection).toContinuousMap
  have hvtx (z : CylinderCover) : cylinderCoverProjection (ρ z) ∈ G.V ↔ cylinderCoverProjection z ∈ G'.V :=
    vertex_mem_iff_of_cover_contraction_section π Φ (cylinderM1Point k i) v hproj hinj
      hVG hl.2.2.1 hsV ρ hρ hρv z
  have hends (z : CylinderCover)
      (hz : cylinderCoverProjection z ∈ G'.U → cylinderCoverProjection z ∈ G'.V)
      (hold : cylinderCoverProjection (ρ z) ∈ G.U) : cylinderCoverProjection (ρ z) ∈ G.V := by
    apply (hvtx z).2
    apply hz
    exact hUG ▸ ⟨_, hold, projection_section_cover_contraction π Φ hproj ρ hρ z⟩
  have hgoffG (t) (ht0 : 0 < t) (ht1 : t < 1) : fG t ∉ G.U := by
    intro hgt
    exact hgoff t ht0 ht1 (hFU ▸ Or.inl hgt)
  have hgNorm : IsNormalCurve G fG := by
    rintro x ⟨⟨t, rfl⟩, htU⟩
    by_cases ht0 : t = 0
    · change cylinderCoverProjection (g t) ∈ G.V
      change cylinderCoverProjection (g t) ∈ G.U at htU
      rw [ht0, hg0a] at htU ⊢
      exact hends a (fun haU => hnormal ⟨⟨0, by exact congrArg cylinderCoverProjection p.source⟩, haU⟩) htU
    · by_cases ht1 : t = 1
      · change cylinderCoverProjection (g t) ∈ G.V
        change cylinderCoverProjection (g t) ∈ G.U at htU
        rw [ht1, hg1b] at htU ⊢
        exact hends b (fun hbU => hnormal ⟨⟨1, by exact congrArg cylinderCoverProjection p.target⟩, hbU⟩) htU
      · exact False.elim (hgoffG t (lt_of_le_of_ne bot_le (show t ≠ 0 from ht0).symm)
          (lt_of_le_of_ne le_top (show t ≠ 1 from ht1)) htU)
  have hhits : curveVertexHits G fG = curveVertexHits G' fG' := by
    ext t
    change cylinderCoverProjection (g t) ∈ G.V ↔ cylinderCoverProjection (p t) ∈ G'.V
    by_cases ht0 : t = 0
    · rw [ht0, hg0a, p.source]
      exact hvtx a
    · by_cases ht1 : t = 1
      · rw [ht1, hg1b, p.target]
        exact hvtx b
      · have htpos : 0 < t := lt_of_le_of_ne bot_le (show t ≠ 0 from ht0).symm
        have htlt : t < 1 := lt_of_le_of_ne le_top (show t ≠ 1 from ht1)
        exact ⟨fun h => False.elim (hgoffG t htpos htlt (G.V_subset_U h)),
          fun h => False.elim (hno t htpos htlt h)⟩
  refine ⟨q, hgNorm, hhits.symm ▸ hfin, ?_⟩
  change curveL G fG = curveL G' fG'
  simp only [curveL, hhits]

end GraphMinor.GM06
