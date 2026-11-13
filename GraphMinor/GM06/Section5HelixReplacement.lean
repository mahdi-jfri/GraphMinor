module

public import GraphMinor.GM06.Defs
public import Mathlib.Topology.Subpath
import GraphMinor.GM06.Section5DeletedEdgeCylinderFaces
import GraphMinor.GM06.Section5DeletedEdgeTail
import GraphMinor.GM06.Section5HelixReplacementPrefix
import GraphMinor.GM06.Section5RegionVisit
import GraphMinor.GM06.Section5RegionPoint
import GraphMinor.GM06.Section5SubpathCount
import GraphMinor.GM06.Section5CurveCount
import GraphMinor.GM06.Section5RegionInterior
import GraphMinor.Surface.CutComp

/-!
# Assembling the replacement helix

In VI (5.5), page 131, choose an old approach region at the last
visit to the deleted-edge region. Join the counted prefix through
that region to the unchanged suffix. Normality of both pieces and
the exact concatenation formula give a helix in the original drawing
and its vertex count. The potential comparison also needs the
winding bound from the rest of the paper's argument.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

open Classical in
/-- The replacement curve and its exact count in the Reduction 1
proof of VI (5.5), page 131. The retained suffix is parametrized
linearly, including when the last region time is terminal. -/
theorem exists_replacement_helix_of_deleted_edge
    {k : ℕ} {G G' : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k)
    {e : Set ClosedCylinder} (he : e ∈ G.E)
    (hs : cylinderM1Point k i ∈ closure e)
    (hV : G'.V = G.V) (hU : G'.U = G.U \ e)
    (f : Curve ClosedCylinder) (hf : IsHelix k G' f)
    {R : Set ClosedCylinder} (hR : R ∈ G'.R) (heR : e ⊆ R)
    {z : unitInterval} (hz : IsGreatest (closure (f ⁻¹' R)) z) :
    ∃ p : Path (cylinderN1Point k i) (f z),
      let q := (⟨f, rfl, rfl⟩ : Path (f 0) (f 1)).subpath z 1
      IsHelix k G (p.trans q).toContinuousMap ∧
      curveL G (p.trans q).toContinuousMap + (if f z ∈ G.V then 1 else 0) =
        (if f z = cylinderM1Point k i then 1 else if f z ∈ G.V then 2 else 1) +
          (curveVertexHits G' f ∩ Icc z 1).ncard := by
  classical
  let : LocallyConnectedSpace ClosedCylinder := IsSurface.locallyConnected isSurface_closedCylinder
  have hend : f 1 ∉ G.U := by
    obtain ⟨j, hj⟩ := hf.2.2.1
    rw [← hj]
    exact cylinderN2Point_not_mem_U hG j
  have hende : f 1 ∉ e := fun h => hend (he.2.1 h).1
  have hlast := last_region_visit_mem_vertex_or_terminal f hf.1 hR hz
  obtain ⟨r, hr, _, hsr, hwr⟩ :=
    exists_old_cylinder_region_at_deleted_edge_region_closure L hG he hU hR heR hs hlast.1
  have hw : f z ∈ G.V ∨ f z ∉ G.U := by
    rcases hlast.2 with hv | hz1
    · exact Or.inl (hV ▸ hv)
    · exact Or.inr (hz1.symm ▸ hend)
  obtain ⟨p, hpN, hpFin, hpL⟩ := exists_helix_replacement_prefix L hG i hr hsr hwr hw
  let old : Path (f 0) (f 1) := ⟨f, rfl, rfl⟩
  let q := old.subpath z 1
  have hqN : IsNormalCurve G q.toContinuousMap :=
    isNormalCurve_tail_of_deleted_edge he hV hU f hf.1 hende hR heR hz
  have hendV : old 1 ∉ G'.V := by
    rw [hV]
    exact fun h => hend (G.V_subset_U h)
  have hqCount := curveL_subpath_of_end_not_vertex old z 1 hendV hf.2.2.2
  have hqHits : curveVertexHits G q.toContinuousMap = curveVertexHits G' q.toContinuousMap := by
    simp only [curveVertexHits, hV]
  have hqFin : (curveVertexHits G q.toContinuousMap).Finite := hqHits.symm ▸ hqCount.1
  have hqL : curveL G q.toContinuousMap = (curveVertexHits G' f ∩ Icc z 1).ncard := by
    rw [curveL, hqHits]
    simpa only [curveL, q, old, uIcc_of_le (show z ≤ 1 from le_top)] using hqCount.2
  have hcount := curveL_path_trans_add p q hpFin hqFin
  refine ⟨p, ⟨isNormalCurve_path_trans p q hpN hqN, ?_, ?_, hcount.1⟩, ?_⟩
  · change (p.trans q) 0 ∈ cylinderN1 k
    rw [Path.source]
    exact ⟨i, rfl⟩
  · change (p.trans q) 1 ∈ cylinderN2 k
    rw [Path.target]
    exact hf.2.2.1
  · rw [← hpL, ← hqL]
    exact hcount.2

end GraphMinor.GM06
