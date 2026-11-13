module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section5SingleEdgePath
import GraphMinor.GM06.Section5LiftedRegionAccess
import GraphMinor.GM06.Section5Initial
import GraphMinor.GM06.Section5TerminalBacktrack
import GraphMinor.GM06.Section5HelixConcatenation
import GraphMinor.GM06.Section5AdjoinBoundary
import GraphMinor.GM06.Section5RegionPoint
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM11.Regions

/-!
# The unreduced tight helix

This is the base case of the induction in VI (5.3), including one
linkage path. The prescribed-side access curve contributes winding
θ − 1/(2k), and the outer-cuff backtrack contributes −1/(2k). Their
join meets one vertex, so its potential is θ. Statement (5.1) supplies
the valency-one path when no reduction applies and the next winding
is infeasible.
-/

public section
namespace GraphMinor.GM06
open Set Real GraphMinor.Surface
/-- The valency-one base case of VI (5.3), pages 132–133. Approach
the sole linkage edge's terminal vertex through the initial region
on the prescribed lifted side, then move backwards by half a gap
on the outer cuff. This includes k = 1. -/
theorem exists_tight_helix_of_initial_valency_one {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ) (i : Fin k)
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    {a : Set ClosedCylinder} {v : ClosedCylinder}
    (hl : G.toGraph.IsLink a (cylinderM1Point k i) v) (hvC : v ∈ cylinderCuff2) :
    ∃ f : Curve ClosedCylinder, IsHelix k G f ∧ curvePhi k G f = θ := by
  have hvt := (linkage_path_eq_closed_edge_of_valency_one L hG i hval hl hvC).1
  obtain ⟨g, hg0, hg1, hgr, hgw⟩ :=
    exists_region_access_curve_of_initial_valency_one L hG hθ i hval hl hvC
  have hgv : ∀ t : unitInterval, g t ∈ G.V ↔ t = 1 := by
    intro t
    constructor
    · intro ht
      by_contra hn
      have ht1 : t < 1 := lt_of_le_of_ne t.2.2 hn
      exact GM11.region_subset (cylinderRegion_mem_regions hG i) (hgr t ht1) (G.V_subset_U ht)
    · rintro rfl
      rw [hg1]
      exact hl.2.2.1
  obtain ⟨j, hj⟩ := L.curve_one_mem i
  let h := terminalCuffBacktrackCurve k j
  have hh0 : h 0 = v := by
    rw [terminalCuffBacktrackCurve_zero, hj]
    exact hvt.symm
  have hh1 : h 1 = cylinderN2Point k (finPredCycle j) := terminalCuffBacktrackCurve_one hG.1 j
  let pg : Path (cylinderN1Point k i) v := ⟨g, hg0, hg1⟩
  let ph : Path v (cylinderN2Point k (finPredCycle j)) := ⟨h, hh0, hh1⟩
  let f : Curve ClosedCylinder := (pg.trans ph).toContinuousMap
  have hhv : ∀ t : unitInterval, h t ∈ G.V ↔ t = 0 := terminalCuffBacktrackCurve_mem_vertices_iff hG j
  have hcount := concatenated_vertex_hits pg ph hgv hhv
  have hnormalg : IsNormalCurve G g := by
    rintro z ⟨⟨t, rfl⟩, htG⟩
    by_cases ht : t = 1
    · exact (hgv t).mpr ht
    · exact False.elim (GM11.region_subset (cylinderRegion_mem_regions hG i)
        (hgr t (lt_of_le_of_ne t.2.2 ht)) htG)
  have hnormalh : IsNormalCurve G h := by
    rintro z ⟨⟨t, rfl⟩, htG⟩
    apply hG.2.1
    refine ⟨?_, htG⟩
    rw [bd_closedCylinder]
    exact Or.inr (terminalCuffBacktrackCurve_mem_cuff2 j t)
  have hfr : range f = range g ∪ range h := by
    change range (pg.trans ph) = _
    rw [Path.trans_range]
    rfl
  refine ⟨f, ⟨?_, ?_, ?_, hcount.1⟩, ?_⟩
  · intro z hz
    rw [hfr] at hz
    rcases hz.1 with hg | hh
    · exact hnormalg ⟨hg, hz.2⟩
    · exact hnormalh ⟨hh, hz.2⟩
  · change (pg.trans ph) 0 ∈ cylinderN1 k
    rw [Path.source]
    exact ⟨i, rfl⟩
  · change (pg.trans ph) 1 ∈ cylinderN2 k
    rw [Path.target]
    exact ⟨finPredCycle j, rfl⟩
  · have hfw := windingNumber_path_trans pg ph
    change windingNumber f = windingNumber g + windingNumber h at hfw
    rw [curvePhi, hfw, hgw, windingNumber_terminalCuffBacktrackCurve hG.1 j, hcount.2]
    push_cast
    field_simp [Nat.cast_ne_zero.mpr hG.1.ne']
    ring
/-- The unreduced two-or-more-path instance of the valency-one
construction in VI (5.3), pages 132–133. -/
theorem exists_tight_helix_of_unreduced_valency_one
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage k G)
    (_hk : 1 < k) (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ)
    (_hno : ¬ Section5AnyReductionApplies k G L) (i : Fin k)
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    {a : Set ClosedCylinder} {v : ClosedCylinder}
    (hl : G.toGraph.IsLink a (cylinderM1Point k i) v) (hvC : v ∈ cylinderCuff2) :
    ∃ f : Curve ClosedCylinder, IsHelix k G f ∧ curvePhi k G f = θ :=
  exists_tight_helix_of_initial_valency_one L hG hθ i hval hl hvC

/-- The complete unreduced case of VI (5.3), pages 132–133.
Statement (5.1) supplies the valency-one start, because the next
winding is not feasible. -/
theorem exists_tight_helix_of_no_reduction
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies k G L)
    (hnext : ¬ IsThetaFeasible k G (θ + 1 / (k : ℝ))) :
    ∃ f : Curve ClosedCylinder, IsHelix k G f ∧ curvePhi k G f = θ := by
  rcases theorem_5_1_proof k G L θ hG hθ hno with hval | hfeas
  · obtain ⟨i, hi, a, _, v, hv, hl⟩ := hval
    exact exists_tight_helix_of_initial_valency_one L hG hθ i hi hl hv.2
  · exact False.elim (hnext hfeas)

end GraphMinor.GM06

