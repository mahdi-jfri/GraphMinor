module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section4Claim2
import GraphMinor.GM06.Section4NoBad
import GraphMinor.GM06.Section4Components

/-!
# Graph Minors VI (4.2)

Claim (2) would supply an interval-based bad component if any bad
component existed. The comparison graph and (4.3) exclude such a
component. Each component therefore has at most one vertex per cuff.
Exclusion of Reduction 1 gives at least two boundary vertices in total,
so both cuffs contain exactly one, as the paper concludes on page 127.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

/-- Graph Minors VI (4.2), page 125:
"If $\Sigma$ is a cylinder and neither (4.1) nor reduction 1 nor reduction 2 applies, then each component of $H$ has exactly one vertex in each cuff of $\Sigma$."
The proof on pages 125–127 uses both claims and the final comparison
graph argument. -/
theorem theorem_4_2_proof : Statement42 := by
  intro G H hG hH hforest hbd hno41 hno1 hno2
  have hnobad : ∀ K : Graph ClosedCylinder (Set ClosedCylinder),
      IsGraphComponent K H.toGraph → ¬ IsBadComponent K := by
    intro K hK hbad
    obtain ⟨L, hL, hLbad, hbases⟩ := lemma_4_2_claim_2 hH hforest hbd hno1 ⟨K, hK, hbad⟩
    exact not_bad_of_intervalBasedOn_both_cuffs hG hH hforest hbd hno41 hno1 hno2 hL hbases hLbad
  intro K hK
  have hone : ∀ C ∈ cuffs ClosedCylinder, (Graph.vertexSet K ∩ C).ncard ≤ 1 := by
    intro C hC
    exact Nat.le_of_not_gt fun hgt => hnobad K hK ⟨C, hC, hgt⟩
  have h1 : (Graph.vertexSet K ∩ cylinderCuff1).ncard ≤ 1 :=
    hone cylinderCuff1 (by rw [cuffs_closedCylinder]; exact Or.inl rfl)
  have h2 : (Graph.vertexSet K ∩ cylinderCuff2).ncard ≤ 1 :=
    hone cylinderCuff2 (by rw [cuffs_closedCylinder]; exact Or.inr rfl)
  have htotal := component_boundary_two_le_of_not_reduction1 hH hforest hbd hno1 hK
  have hsum := ncard_union_le (Graph.vertexSet K ∩ cylinderCuff1) (Graph.vertexSet K ∩ cylinderCuff2)
  rw [← inter_union_distrib_left, ← bd_closedCylinder] at hsum
  omega

end GraphMinor.GM06
