module

public import GraphMinor.GM06.Section5InitialCuffBacktrack
import GraphMinor.GM06.Section5EndpointVertexCount
import GraphMinor.GM06.Section5HelixSurgeryIdentities
import GraphMinor.GM06.Section5HelixConcatenation

/-!
# Cancelling the counts in the replacement-prefix comparison

In VI (5.5), pages 131–132, split the old helix at its last earlier
vertex hit and its last region visit. The intervening region segment
and the new region approach both have only their endpoint vertex
times. Their counts therefore agree. The initial half gap contributes
one vertex time, and the shared suffix cancels. The potential
difference is the auxiliary winding plus k inverse times the number
of vertex hits before the earlier join.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- The exact potential identity behind the final count addition
in VI (5.5), page 132. The counts of both region pieces are proved
from their interior vertex avoidance. -/
theorem helix_prefix_replacement_potential_identity
    {k : ℕ} {G : Drawing ClosedCylinder} (hG : IsCylinderSection5Drawing k G)
    (i : Fin k) {a x w b : ClosedCylinder}
    (p : Path a x) (q : Path x w) (g : Path (cylinderM1Point k i) w) (r : Path w b)
    (hx : x ∈ G.V)
    (hp : (curveVertexHits G p.toContinuousMap).Finite)
    (hr : (curveVertexHits G r.toContinuousMap).Finite)
    (hqNoVertex : ∀ t : unitInterval, 0 < t → t < 1 → q t ∉ G.V)
    (hgOff : ∀ t : unitInterval, 0 < t → t < 1 → g t ∉ G.U) :
    let h : Path (cylinderN1Point k i) (cylinderM1Point k i) :=
      ⟨initialCuffHalfBacktrackCurve k i, initialCuffHalfBacktrackCurve_zero i,
        initialCuffHalfBacktrackCurve_one i⟩
    let aux := p.trans ((q.trans g.symm).trans h.symm)
    (curveVertexHits G ((p.trans q).trans r).toContinuousMap).Finite ∧
      (curveVertexHits G ((h.trans g).trans r).toContinuousMap).Finite ∧
      (curveVertexHits G aux.toContinuousMap).Finite ∧
      curvePhi k G ((p.trans q).trans r).toContinuousMap -
        curvePhi k G ((h.trans g).trans r).toContinuousMap =
          windingNumber aux.toContinuousMap + (k : ℝ)⁻¹ * (curveL G p.toContinuousMap - 1 : ℝ) := by
  classical
  dsimp only
  let h : Path (cylinderN1Point k i) (cylinderM1Point k i) :=
    ⟨initialCuffHalfBacktrackCurve k i, initialCuffHalfBacktrackCurve_zero i,
      initialCuffHalfBacktrackCurve_one i⟩
  have hs : cylinderM1Point k i ∈ G.V := by
    have hv : cylinderM1Point k i ∈ cylinderM1 k ∪ cylinderM2 k := Or.inl ⟨i, rfl⟩
    exact (show cylinderM1Point k i ∈ G.V ∩ bd ClosedCylinder from hG.2.2.symm ▸ hv).1
  have hqStart : q 0 ∈ G.V := (Path.source q).symm ▸ hx
  have hgStart : g 0 ∈ G.V := (Path.source g).symm ▸ hs
  have hqCount := curveL_of_interior_disjoint_vertices q.toContinuousMap hqStart hqNoVertex
  have hgCount := curveL_of_interior_disjoint_drawing g.toContinuousMap hgStart hgOff
  have hqEnd : q.toContinuousMap 1 = w := Path.target q
  have hgEnd : g.toContinuousMap 1 = w := Path.target g
  have hqL : curveL G q.toContinuousMap = 1 + (if w ∈ G.V then 1 else 0) := by
    simpa only [hqEnd] using hqCount.2
  have hgL : curveL G g.toContinuousMap = 1 + (if w ∈ G.V then 1 else 0) := by
    simpa only [hgEnd] using hgCount.2
  have hh := initialCuffHalfBacktrackCurve_props hG i
  have hhfin : (curveVertexHits G h.toContinuousMap).Finite := hh.2 ▸ finite_singleton 1
  have hhL : curveL G h.toContinuousMap = 1 := by rw [curveL, hh.2, ncard_singleton]
  have hpq := curveL_path_trans_add p q hp hqCount.1
  have hOld := curveL_path_trans_add (p.trans q) r hpq.1 hr
  have hhg := curveL_path_trans_add h g hhfin hgCount.1
  have hNew := curveL_path_trans_add (h.trans g) r hhg.1 hr
  have hpqL := hpq.2
  have hhgL := hhg.2
  rw [ite_eq_left hx, hqL] at hpqL
  rw [ite_eq_left hs, hhL, hgL] at hhgL
  have hOldL : curveL G ((p.trans q).trans r).toContinuousMap =
      curveL G p.toContinuousMap + curveL G r.toContinuousMap := by
    have ho := hOld.2
    omega
  have hNewL : curveL G ((h.trans g).trans r).toContinuousMap =
      1 + curveL G r.toContinuousMap := by
    have hn := hNew.2
    omega
  have hgRev := curveL_path_symm g hgCount.1
  have hhRev := curveL_path_symm h hhfin
  have hqg := curveL_path_trans_add q g.symm hqCount.1 hgRev.1
  have hqgh := curveL_path_trans_add (q.trans g.symm) h.symm hqg.1 hhRev.1
  have haux := curveL_path_trans_add p ((q.trans g.symm).trans h.symm) hp hqgh.1
  have hw : windingNumber ((p.trans q).trans r).toContinuousMap -
      windingNumber ((h.trans g).trans r).toContinuousMap =
      windingNumber (p.trans ((q.trans g.symm).trans h.symm)).toContinuousMap := by
    simp only [windingNumber_path_trans, windingNumber_path_symm]
    ring
  refine ⟨hOld.1, hNew.1, haux.1, ?_⟩
  change curvePhi k G ((p.trans q).trans r).toContinuousMap -
    curvePhi k G ((h.trans g).trans r).toContinuousMap = _
  rw [curvePhi, curvePhi, hOldL, hNewL]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [← hw]
  ring

end GraphMinor.GM06
