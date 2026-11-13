module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM06.Section5CoverTranslation
import GraphMinor.GM06.Section5ContractionCoverRegions
import GraphMinor.GM06.Section5ContractionVertexFree
import GraphMinor.GM06.Section5FiniteVisitCount
import GraphMinor.GM06.Section5SubpathCount
import GraphMinor.GM06.Section5CurveCount
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
# Finite-visit gluing for contraction curves

For Reduction 3 of VI (5.5), page 130, split a normal curve at its
last interior vertex visit. Its suffix has the proved vertex-free
replacement, and its prefix has fewer interior visits. Concatenate
the two old replacements. Their common endpoint is one old vertex,
so the exact cut-count identity preserves the original vertex count.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- Replace a finite-hit lifted normal path through contraction,
retaining its section endpoints, normality and exact vertex count. -/
theorem exists_cover_path_replacement_of_finite_vertex_hits
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
    (hoffbd : ∀ t, 0 < t → t < 1 → cylinderCoverProjection (p t) ∉ G'.V →
      cylinderCoverProjection (p t) ∉ bd ClosedCylinder) :
    ∃ q : Path (ρ a) (ρ b),
      IsNormalCurve G (q.map continuous_cylinderCoverProjection).toContinuousMap ∧
      (curveVertexHits G (q.map continuous_cylinderCoverProjection).toContinuousMap).Finite ∧
      curveL G (q.map continuous_cylinderCoverProjection).toContinuousMap =
        curveL G' (p.map continuous_cylinderCoverProjection).toContinuousMap := by
  classical
  generalize hn : (curveVertexHits G' (p.map continuous_cylinderCoverProjection).toContinuousMap ∩ Ioo 0 1).ncard = n
  induction n using Nat.strong_induction_on generalizing a b p with
  | h n ih =>
    by_cases hne : (curveVertexHits G' (p.map continuous_cylinderCoverProjection).toContinuousMap ∩ Ioo 0 1).Nonempty
    · obtain ⟨τ, hτmem, hmax⟩ := (hfin.inter_of_left (Ioo 0 1)).isCompact.exists_isGreatest hne
      have hτ : τ ∈ Ioo (0 : unitInterval) 1 := hτmem.2
      have hτV : cylinderCoverProjection (p τ) ∈ G'.V := hτmem.1
      let P := p.map continuous_cylinderCoverProjection
      have hpreNorm : IsNormalCurve G' ((p.subpath 0 τ).map continuous_cylinderCoverProjection).toContinuousMap :=
        isNormalCurve_path_subpath P hnormal 0 τ
      have hpostNorm : IsNormalCurve G' ((p.subpath τ 1).map continuous_cylinderCoverProjection).toContinuousMap :=
        isNormalCurve_path_subpath P hnormal τ 1
      have hpreFin : (curveVertexHits G' ((p.subpath 0 τ).map continuous_cylinderCoverProjection).toContinuousMap).Finite :=
        (curveL_subpath P (ne_of_lt hτ.1) hfin).1
      have hpostFin : (curveVertexHits G' ((p.subpath τ 1).map continuous_cylinderCoverProjection).toContinuousMap).Finite :=
        (curveL_subpath P (ne_of_lt hτ.2) hfin).1
      have hpreBd : ∀ t, 0 < t → t < 1 → cylinderCoverProjection ((p.subpath 0 τ) t) ∉ G'.V →
          cylinderCoverProjection ((p.subpath 0 τ) t) ∉ bd ClosedCylinder := by
        intro t ht0 ht1 htV
        have htime := convexComb_mem_Ioo_of_lt hτ.1 ⟨ht0, ht1⟩
        exact hoffbd _ htime.1 (htime.2.trans hτ.2) htV
      have hpostNo : ∀ t, 0 < t → t < 1 → cylinderCoverProjection ((p.subpath τ 1) t) ∉ G'.V := by
        intro t ht0 ht1 htV
        have htime := convexComb_mem_Ioo_of_lt hτ.2 ⟨ht0, ht1⟩
        have hmem : Icc.convexComb τ 1 t ∈ curveVertexHits G' P.toContinuousMap ∩ Ioo 0 1 :=
          ⟨htV, hτ.1.trans htime.1, htime.2⟩
        exact (not_lt_of_ge (hmax hmem)) htime.1
      have hpostBd : ∀ t, 0 < t → t < 1 → cylinderCoverProjection ((p.subpath τ 1) t) ∉ bd ClosedCylinder := by
        intro t ht0 ht1
        have htime := convexComb_mem_Ioo_of_lt hτ.2 ⟨ht0, ht1⟩
        exact hoffbd _ (hτ.1.trans htime.1) htime.2 (hpostNo t ht0 ht1)
      have hless : (curveVertexHits G' ((p.subpath 0 τ).map continuous_cylinderCoverProjection).toContinuousMap ∩ Ioo 0 1).ncard < n := by
        rw [← hn]
        exact interior_vertex_hits_prefix_ncard_lt P hfin hτ hτV
      obtain ⟨q₁, hq₁norm, hq₁fin, hq₁count⟩ := ih _ hless
        (p := p.subpath 0 τ) hpreNorm hpreFin hpreBd rfl
      obtain ⟨q₂, hq₂norm, hq₂fin, hq₂count⟩ := exists_cover_path_replacement_of_no_interior_vertex_hits
        L hG hGF hFU i hval hl hv hvC π Φ hproj htrans hfix hinj hsurj hU hs hfibre
        ρ hρ hρv hUG hVG hsV hF'U (p.subpath τ 1) hpostNorm hpostFin hpostNo hpostBd
      let q : Path (ρ a) (ρ b) :=
        ⟨(q₁.trans q₂).toContinuousMap,
          (Path.source _).trans (congrArg ρ p.source),
          (Path.target _).trans (congrArg ρ p.target)⟩
      have hqeq : (q.map continuous_cylinderCoverProjection).toContinuousMap =
          ((q₁.map continuous_cylinderCoverProjection).trans (q₂.map continuous_cylinderCoverProjection)).toContinuousMap := by
        change ((q₁.trans q₂).map continuous_cylinderCoverProjection).toContinuousMap = _
        rw [Path.map_trans]
      have hnorm := isNormalCurve_path_trans (q₁.map continuous_cylinderCoverProjection)
        (q₂.map continuous_cylinderCoverProjection) hq₁norm hq₂norm
      have hcount := curveL_path_trans_add (q₁.map continuous_cylinderCoverProjection)
        (q₂.map continuous_cylinderCoverProjection) hq₁fin hq₂fin
      have hjoin : cylinderCoverProjection (ρ (p τ)) ∈ G.V :=
        (vertex_mem_iff_of_cover_contraction_section π Φ (cylinderM1Point k i) v hproj hinj
          hVG hl.2.2.1 hsV ρ hρ hρv (p τ)).2 hτV
      have hsplit := curveL_two_subpaths_at_vertex P hfin hτ hτV
      rw [ite_eq_left hjoin, hq₁count, hq₂count] at hcount
      refine ⟨q, hqeq.symm ▸ hnorm, hqeq.symm ▸ hcount.1, ?_⟩
      rw [hqeq]
      have hc := hcount.2
      change curveL G' ((p.subpath 0 τ).map continuous_cylinderCoverProjection).toContinuousMap +
        curveL G' ((p.subpath τ 1).map continuous_cylinderCoverProjection).toContinuousMap =
        curveL G' P.toContinuousMap + 1 at hsplit
      change curveL G ((q₁.map continuous_cylinderCoverProjection).trans
        (q₂.map continuous_cylinderCoverProjection)).toContinuousMap = curveL G' P.toContinuousMap
      omega
    · have hno : ∀ t, 0 < t → t < 1 → cylinderCoverProjection (p t) ∉ G'.V := by
        intro t ht0 ht1 htV
        exact hne ⟨t, htV, ht0, ht1⟩
      exact exists_cover_path_replacement_of_no_interior_vertex_hits
        L hG hGF hFU i hval hl hv hvC π Φ hproj htrans hfix hinj hsurj hU hs hfibre
        ρ hρ hρv hUG hVG hsV hF'U p hnormal hfin hno
        (fun t ht0 ht1 => hoffbd t ht0 ht1 (hno t ht0 ht1))

end GraphMinor.GM06
