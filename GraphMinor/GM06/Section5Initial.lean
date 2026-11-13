module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5SinglePathInitial
import GraphMinor.GM06.Section5RegionContact
import GraphMinor.GM06.Section5SpliceWinding
import GraphMinor.GM06.Section5ValencyOneCase
import GraphMinor.GM06.Section5SingleStrip

/-!
# Graph Minors VI, (5.1): the unreduced linkage

At a start of valency one, the constructed Reduction 3 forces its
neighbour onto the outer cuff. Otherwise the region-boundary contact assertions give a path
through each strip to the next old path, away from its initial vertex. Join
each resulting path to the next old tail. The strip confinement gives
pairwise disjointness and makes the winding increase by one over k.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- The cyclic construction in VI (5.1), page 129, gives the next
feasible winding when no initial vertex has valency one. -/
theorem isThetaFeasible_next_of_no_initial_valency_one
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage k G)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies k G L)
    (hval : ∀ i, vertexValency G.toGraph (cylinderM1Point k i) ≠ 1) :
    IsThetaFeasible k G (θ + 1 / (k : ℝ)) := by
  exact isThetaFeasible_next_of_region_contacts L hG hk hθ hno
    (fun i => closure_region_inter_path_subset_start L hk hG hθ hno i (hval i))

/-- Graph Minors VI, (5.1), page 129. In the unreduced situation,
either a valency-one start has its neighbour on the outer cuff, or
the cyclic region-path construction gives the next feasible winding. -/
theorem theorem_5_1_proof : Statement51 := by
  classical
  intro k G L θ hG hθ hno
  by_cases hv : ∃ i : Fin k, vertexValency G.toGraph (cylinderM1Point k i) = 1
  · obtain ⟨i, hi⟩ := hv
    exact Or.inl ⟨i, hi, exists_cuff2_neighbour_of_valency_one L hG hno i hi⟩
  · have hval : ∀ i, vertexValency G.toGraph (cylinderM1Point k i) ≠ 1 :=
      fun i hi => hv ⟨i, hi⟩
    by_cases hk1 : k = 1
    · subst k
      apply Or.inr
      simpa using isThetaFeasible_successor_of_single_path_unreduced L hG hθ hno (hval 0)
    · have hk : 1 < k := by have hkpos := hG.1; omega
      exact Or.inr (isThetaFeasible_next_of_no_initial_valency_one L hk hG hθ hno hval)

end GraphMinor.GM06
