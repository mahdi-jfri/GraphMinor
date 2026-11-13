module

public import GraphMinor.GM06.Section5SinglePathPrefixExclusion
import GraphMinor.GM06.Section5OwnPathSplice
import GraphMinor.GM06.Section5ReplaceLinkagePath
import GraphMinor.GM06.Section5EndpointObstruction

/-!
# A left-seam return gives corrected Reduction 4

The old lifted prefix fails incidence by the proved one-path
initial-arc argument. An incident replacement path reaching the same
lifted contact can therefore replace it. Concatenate this path with
the old tail, allowing a singleton tail at the terminal vertex,
and construct the new linkage. These are exactly the data of the
corrected side condition for Reduction 4 in VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- A first noninitial return to the left old-path lift gives an actual
corrected Reduction 4, including a contact at the terminal vertex. -/
theorem reduction4_applies_of_single_path_left_return
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies 1 G L)
    (hval : vertexValency G.toGraph (cylinderM1Point 1 0) ≠ 1)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (u : unitInterval) (hu : 0 < u) (huV : L.curve 0 u ∈ (L.pathDrawing 0).V)
    {Q : Drawing ClosedCylinder} (hQ : IsSubpathOf G Q (cylinderM1Point 1 0) (L.curve 0 u))
    (hcontact : Q.U ∩ (L.pathDrawing 0).U ⊆ {cylinderM1Point 1 0, L.curve 0 u})
    (q : Curve ClosedCylinder) (hq : ParametrizesSet q Q.U (cylinderM1Point 1 0) (L.curve 0 u))
    (hqR : range (cylinderCurveLiftAt q (cylinderInitialLift 1 0).2) ⊆
      closure (cylinderCoverRegion 1 G 0))
    (hqEnd : cylinderCurveLiftAt q (cylinderInitialLift 1 0).2 1 =
      cylinderCurveLiftAt (L.curve 0) (cylinderInitialLift 1 0).2 u) :
    Section5AnyReductionApplies 1 G L := by
  have hvs : L.curve 0 u ≠ cylinderM1Point 1 0 := by
    intro h
    have heq : L.curve 0 u = L.curve 0 0 := h.trans (L.curve_parametrizes 0).2.2.1.symm
    exact hu.ne' ((L.curve_parametrizes 0).1 heq)
  obtain ⟨T, R, hTail, _, hR, hRU⟩ := exists_path_after_own_linkage_tail
    (L.isSubdrawing 0).1 hQ.1 (L.isPath 0) hQ.2.2 huV hvs hcontact
  have hdisj : ∀ j : Fin 1, j ≠ 0 → Disjoint R.U (L.pathDrawing j).U := by
    intro j hj
    exact False.elim (hj (Subsingleton.elim _ _))
  obtain ⟨L', hRi, _, hunchanged⟩ := exists_linkage_replacing_path L 0 hR.1 hR.2.2 hdisj
  have hbad := single_path_initial_lift_prefix_not_subset_coverRegion L hG hθ hno hval hD hBd hstrip u hu huV
  have huR : cylinderCurveLiftAt (L.curve 0) (cylinderInitialLift 1 0).2 u ∈
      closure (cylinderCoverRegion 1 G 0) := hqEnd ▸ hqR (mem_range_self 1)
  refine ⟨G, L', hG, Or.inr (Or.inr (Or.inr ?_))⟩
  refine ⟨rfl, Or.inr ⟨rfl, 0, u, T, Q, q, huV, huR, hbad, hTail,
    hQ.1, hQ.2.1, hQ.2.2, hq, hqR, hqEnd, ?_, hunchanged⟩⟩
  rw [hRi, hRU]

end GraphMinor.GM06
