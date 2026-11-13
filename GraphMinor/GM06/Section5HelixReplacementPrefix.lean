module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5RegionBridge
import GraphMinor.GM06.Section5InitialCuffBacktrack
import GraphMinor.GM06.Section5CurveCount
import GraphMinor.GM06.Section5AdjoinBoundary
import GraphMinor.GM06.Section5RegionInterior
import GraphMinor.Surface.CutComp
import GraphMinor.GM11.Regions

/-!
# The replacement prefix of a helix

VI (5.5), page 131, first moves backwards on the initial cuff from
a dual point to the initial vertex. If the join is another point,
continue through the old approach region. The resulting prefix is
normal. It has one vertex time when the join is the initial vertex
or is not a vertex, and two when the join is another vertex.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

private theorem prefix_with_region_approach
    {k : ℕ} {G : Drawing ClosedCylinder} (hG : IsCylinderSection5Drawing k G)
    (i : Fin k) {w : ClosedCylinder}
    (g : Path (cylinderM1Point k i) w) (hg : IsNormalCurve G g.toContinuousMap)
    (hgfin : (curveVertexHits G g.toContinuousMap).Finite) :
    ∃ p : Path (cylinderN1Point k i) w,
      IsNormalCurve G p.toContinuousMap ∧ (curveVertexHits G p.toContinuousMap).Finite ∧
        curveL G p.toContinuousMap = curveL G g.toContinuousMap := by
  let h : Path (cylinderN1Point k i) (cylinderM1Point k i) :=
    ⟨initialCuffHalfBacktrackCurve k i, initialCuffHalfBacktrackCurve_zero i,
      initialCuffHalfBacktrackCurve_one i⟩
  have hh := initialCuffHalfBacktrackCurve_props hG i
  have hhfin : (curveVertexHits G h.toContinuousMap).Finite := hh.2 ▸ finite_singleton 1
  have hhL : curveL G h.toContinuousMap = 1 := by
    rw [curveL, hh.2, ncard_singleton]
  have hsV : cylinderM1Point k i ∈ G.V := by
    have hmem : cylinderM1Point k i ∈ cylinderM1 k ∪ cylinderM2 k := Or.inl ⟨i, rfl⟩
    exact (show cylinderM1Point k i ∈ G.V ∩ bd ClosedCylinder from hG.2.2.symm ▸ hmem).1
  have hcount := curveL_path_trans_add h g hhfin hgfin
  have hlen := hcount.2
  rw [ite_eq_left hsV, hhL] at hlen
  exact ⟨h.trans g, isNormalCurve_path_trans h g hh.1 hg, hcount.1, by omega⟩

open Classical in
/-- Construct the normal prefix used to replace a helix in the
Reduction 1 case of VI (5.5), page 131, with its exact vertex count. -/
theorem exists_helix_replacement_prefix
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k)
    {r : Set ClosedCylinder} (hr : r ∈ G.R)
    (hsr : cylinderM1Point k i ∈ closure r) {w : ClosedCylinder}
    (hwr : w ∈ closure r) (hw : w ∈ G.V ∨ w ∉ G.U) :
    ∃ p : Path (cylinderN1Point k i) w,
      IsNormalCurve G p.toContinuousMap ∧ (curveVertexHits G p.toContinuousMap).Finite ∧
        curveL G p.toContinuousMap =
          if w = cylinderM1Point k i then 1 else if w ∈ G.V then 2 else 1 := by
  classical
  have hsV : cylinderM1Point k i ∈ G.V := by
    have hmem : cylinderM1Point k i ∈ cylinderM1 k ∪ cylinderM2 k := Or.inl ⟨i, rfl⟩
    exact (show cylinderM1Point k i ∈ G.V ∩ bd ClosedCylinder from hG.2.2.symm ▸ hmem).1
  by_cases hws : w = cylinderM1Point k i
  · subst w
    let h : Path (cylinderN1Point k i) (cylinderM1Point k i) :=
      ⟨initialCuffHalfBacktrackCurve k i, initialCuffHalfBacktrackCurve_zero i,
        initialCuffHalfBacktrackCurve_one i⟩
    have hh := initialCuffHalfBacktrackCurve_props hG i
    refine ⟨h, hh.1, hh.2 ▸ finite_singleton 1, ?_⟩
    rw [ite_eq_left rfl, curveL, hh.2, ncard_singleton]
  · obtain ⟨F, _, hFU, hFV⟩ := exists_drawing_adjoining_boundary L hG
    by_cases hwV : w ∈ G.V
    · obtain ⟨g, hg0, hg1, _, hgN, hgHits⟩ :=
        exists_curve_between_vertices_through_region hFU hFV hr hsV hwV hsr hwr
      let q : Path (cylinderM1Point k i) w := ⟨g, hg0, hg1⟩
      have hfin : (curveVertexHits G q.toContinuousMap).Finite :=
        hgHits ▸ (finite_singleton (1 : unitInterval)).insert 0
      obtain ⟨p, hpN, hpFin, hpL⟩ := prefix_with_region_approach hG i q hgN hfin
      refine ⟨p, hpN, hpFin, ?_⟩
      rw [ite_eq_right hws, ite_eq_left hwV, hpL, curveL, hgHits]
      exact ncard_pair (by norm_num : (0 : unitInterval) ≠ 1)
    · let : LocallyConnectedSpace ClosedCylinder := IsSurface.locallyConnected isSurface_closedCylinder
      have hwU : w ∉ G.U := hw.resolve_left hwV
      have hwr' : w ∈ r := (GM11.closure_region_subset hr hwr).resolve_right hwU
      obtain ⟨g, hg0, hg1, _, hgN, hgHits⟩ :=
        exists_curve_from_vertex_to_region_point hFU hFV hr hsV hwr' hsr
      let q : Path (cylinderM1Point k i) w := ⟨g, hg0, hg1⟩
      have hfin : (curveVertexHits G q.toContinuousMap).Finite := hgHits ▸ finite_singleton 0
      obtain ⟨p, hpN, hpFin, hpL⟩ := prefix_with_region_approach hG i q hgN hfin
      refine ⟨p, hpN, hpFin, ?_⟩
      rw [ite_eq_right hws, ite_eq_right hwV, hpL, curveL, hgHits, ncard_singleton]

end GraphMinor.GM06
