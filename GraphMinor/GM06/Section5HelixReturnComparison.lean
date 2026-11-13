module

public import GraphMinor.GM06.Section5InitialCuffBacktrack
public import GraphMinor.GM06.Section5CoverInitialCrossings
import GraphMinor.GM06.Section5EarlierWindingBound
import GraphMinor.GM06.Section5EarlierPrefixCount
import GraphMinor.GM06.Section5HelixPrefixPotential
import GraphMinor.GM06.Section5EndpointVertexCount

/-!
# Comparing the replacement helix with the old pieces

VI (5.5), page 132, bounds the negative auxiliary winding by the
vertex times before the return begins. The joining-vertex formula
identifies that count with the old-prefix count minus one. The
potential identity then shows that the replacement helix has no
larger potential. This lemma carries out that comparison for an
actual lifted return, deriving every count and winding inequality.
-/

public section
namespace GraphMinor.GM06
open Set Real GraphMinor.Surface

private theorem initial_gap_index_of_cover_point {k : ℕ} (hk : 0 < k)
    (p : CylinderCover) (hp : cylinderCoverProjection p ∈ cylinderN1 k) :
    ∃ m : ℤ, p.2 = (2 * (m : ℝ) + 1) * π / k := by
  obtain ⟨j, hj⟩ := hp
  have he : Circle.exp p.2 = Circle.exp ((2 * ((j.1 + 1 : ℕ) : ℝ) + 1) * π / k) :=
    congrArg (fun x : ClosedCylinder => x.1.2) hj.symm
  obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp he
  refine ⟨(j.1 + 1 : ℤ) + n * (k : ℤ), ?_⟩
  rw [hn]
  push_cast
  field_simp [Nat.cast_ne_zero.mpr hk.ne']
  ring

private theorem normal_path_symm {H : Drawing ClosedCylinder} {a b : ClosedCylinder}
    (p : Path a b) (hp : IsNormalCurve H p.toContinuousMap) : IsNormalCurve H p.symm.toContinuousMap := by
  rintro x ⟨⟨t, rfl⟩, htH⟩
  exact hp ⟨mem_range_self (unitInterval.symm t), htH⟩

/-- The local potential comparison in VI (5.5), page 132. The inputs
are the actual old and new curve pieces and the auxiliary cover's
geometric return location. The crossing and potential bounds are
proved internally. -/
theorem helix_replacement_comparison_of_return_strip
    {k : ℕ} {G H : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (hH : IsCylinderSection5Drawing k H)
    (hθ : L.HasTheta θ) (hPH : ∀ i, (L.pathDrawing i).U ⊆ H.U)
    (hHU : H.U ⊆ G.U) (hV : H.V = G.V) (m : ℤ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L m)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (i : Fin k) {a x w b : ClosedCylinder}
    (p : Path a x) (q : Path x w) (g : Path (cylinderM1Point k i) w) (r : Path w b)
    (ha : a ∈ cylinderN1 k) (hb : b ∈ cylinderN2 k) (hx : x ∈ G.V)
    (hw : w ∈ G.V ∨ w ∉ G.U)
    (hpN : IsNormalCurve H p.toContinuousMap) (hqN : IsNormalCurve H q.toContinuousMap)
    (hrN : IsNormalCurve G r.toContinuousMap)
    (hp : (curveVertexHits G p.toContinuousMap).Finite)
    (hr : (curveVertexHits G r.toContinuousMap).Finite)
    (hqNoVertex : ∀ t : unitInterval, 0 < t → t < 1 → q t ∉ G.V)
    (hgOff : ∀ t : unitInterval, 0 < t → t < 1 → g t ∉ G.U) :
    let h : Path (cylinderN1Point k i) (cylinderM1Point k i) :=
      ⟨initialCuffHalfBacktrackCurve k i, initialCuffHalfBacktrackCurve_zero i,
        initialCuffHalfBacktrackCurve_one i⟩
    let aux := p.trans ((q.trans g.symm).trans h.symm)
    ∀ B : C(unitInterval, CylinderCover),
      (∀ t, cylinderCoverProjection (B t) = aux t) →
      (∀ t, leftHalfTime 1 ≤ t → cylinderCoverCoordinates (B t) ∈
        D ∪ ({1} ×ˢ Icc (2 * ((m : ℝ) + 1) * π / k)
          ((2 * ((m : ℝ) + 1) + 1) * π / k))) →
      (B 1).2 = (2 * ((m : ℝ) + 1) + 1) * π / k →
      ∃ f : Curve ClosedCylinder, IsHelix k G f ∧
        curvePhi k G f ≤ curvePhi k H ((p.trans q).trans r).toContinuousMap := by
  classical
  dsimp only
  let h : Path (cylinderN1Point k i) (cylinderM1Point k i) :=
    ⟨initialCuffHalfBacktrackCurve k i, initialCuffHalfBacktrackCurve_zero i,
      initialCuffHalfBacktrackCurve_one i⟩
  let aux := p.trans ((q.trans g.symm).trans h.symm)
  intro B hBproj hReturn hAngle1
  have hs : cylinderM1Point k i ∈ G.V := by
    have hv : cylinderM1Point k i ∈ cylinderM1 k ∪ cylinderM2 k := Or.inl ⟨i, rfl⟩
    exact (show cylinderM1Point k i ∈ G.V ∩ bd ClosedCylinder from hG.2.2.symm ▸ hv).1
  have hgStart : g.toContinuousMap 0 ∈ G.V := (Path.source g).symm ▸ hs
  have hgEnd : g.toContinuousMap 1 ∈ G.V ∨ g.toContinuousMap 1 ∉ G.U :=
    (Path.target g).symm ▸ hw
  have hgN := isNormalCurve_of_interior_disjoint_drawing g.toContinuousMap hgStart hgEnd hgOff
  have hgNH : IsNormalCurve H g.toContinuousMap := by
    intro z hz
    rw [hV]
    exact hgN ⟨hz.1, hHU hz.2⟩
  have hhNH : IsNormalCurve H h.toContinuousMap := (initialCuffHalfBacktrackCurve_props hH i).1
  have hretN := isNormalCurve_path_trans (q.trans g.symm) h.symm
    (isNormalCurve_path_trans q g.symm hqN (normal_path_symm g hgNH)) (normal_path_symm h hhNH)
  have hauxN : IsNormalCurve H aux.toContinuousMap := isNormalCurve_path_trans p _ hpN hretN
  obtain ⟨_, hNewFin, hAuxFin, hIdentity⟩ :=
    helix_prefix_replacement_potential_identity hG i p q g r hx hp hr hqNoVertex hgOff
  have hHits (c : Curve ClosedCylinder) : curveVertexHits H c = curveVertexHits G c := by
    simp only [curveVertexHits, hV]
  have hAuxFinH : (curveVertexHits H aux.toContinuousMap).Finite :=
    (hHits aux.toContinuousMap).symm ▸ hAuxFin
  have hBa : cylinderCoverProjection (B 0) = a := (hBproj 0).trans (Path.source aux)
  obtain ⟨m₀, hAngle0⟩ := initial_gap_index_of_cover_point hG.1 (B 0) (hBa.symm ▸ ha)
  have hB0 : (B 0).1.1 = 1 := by
    obtain ⟨j, hj⟩ := ha
    have he := congrArg (fun z : ClosedCylinder => z.1.1) hBa
    rw [← hj] at he
    exact he
  have hB1 : (B 1).1.1 = 1 :=
    congrArg (fun z : ClosedCylinder => z.1.1) ((hBproj 1).trans (Path.target aux))
  have hBound := negative_scaled_winding_le_earlier_hits_of_return_strip L hG hθ hPH m hD hBd hstrip
    aux.toContinuousMap hauxN hAuxFinH B hBproj hB0 hB1 (leftHalfTime 1) hReturn m₀ hAngle0 hAngle1
  rw [hHits aux.toContinuousMap] at hBound
  have hCount := earlier_vertex_hits_path_trans_ncard p ((q.trans g.symm).trans h.symm) hx hp
  have hCountR : ((curveVertexHits G aux.toContinuousMap ∩ Iio (leftHalfTime 1)).ncard : ℝ) + 1 =
      (curveL G p.toContinuousMap : ℝ) := by exact_mod_cast hCount
  have hCountEq : ((curveVertexHits G aux.toContinuousMap ∩ Iio (leftHalfTime 1)).ncard : ℝ) =
      (curveL G p.toContinuousMap : ℝ) - 1 := by linarith only [hCountR]
  have hScaled := mul_le_mul_of_nonneg_left hBound (inv_nonneg.mpr (Nat.cast_nonneg k))
  have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hG.1.ne'
  have hCancel : (k : ℝ)⁻¹ * (-((k : ℝ) * windingNumber aux.toContinuousMap)) =
      -windingNumber aux.toContinuousMap := by
    rw [mul_neg, ← mul_assoc, inv_mul_cancel₀ hkne, one_mul]
  rw [hCancel, hCountEq] at hScaled
  have hNonneg : 0 ≤ windingNumber aux.toContinuousMap +
      (k : ℝ)⁻¹ * ((curveL G p.toContinuousMap : ℝ) - 1) := by linarith only [hScaled]
  have hNewLe : curvePhi k G ((h.trans g).trans r).toContinuousMap ≤
      curvePhi k G ((p.trans q).trans r).toContinuousMap := by
    linarith only [hIdentity, hNonneg]
  have hPhiOld : curvePhi k H ((p.trans q).trans r).toContinuousMap =
      curvePhi k G ((p.trans q).trans r).toContinuousMap := by
    simp only [curvePhi, curveL, curveVertexHits, hV]
  let f := ((h.trans g).trans r).toContinuousMap
  have hNewN : IsNormalCurve G f := isNormalCurve_path_trans (h.trans g) r
    (isNormalCurve_path_trans h g (initialCuffHalfBacktrackCurve_props hG i).1 hgN) hrN
  refine ⟨f, ⟨hNewN, ?_, ?_, hNewFin⟩, ?_⟩
  · change ((h.trans g).trans r) 0 ∈ cylinderN1 k
    rw [Path.source]
    exact ⟨i, rfl⟩
  · change ((h.trans g).trans r) 1 ∈ cylinderN2 k
    rw [Path.target]
    exact hb
  · rw [hPhiOld]
    exact hNewLe

end GraphMinor.GM06
