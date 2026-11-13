module

public import GraphMinor.Compute.Algorithm99SpecFinal
public import GraphMinor.Compute.Algorithm99Final
public import GraphMinor.Compute.Algorithm99Small

/-!
# Algorithm (9.9), including its caller interface

One choice of the subroutines gives the same width bound for the standalone
program and the shifted caller program. The small-parameter programs handle
`p ≤ 1`. For larger parameters the core loop and the proved output conversions
supply both forms of the algorithm.
-/

public section
namespace GraphMinor.Compute

/-- Graph Minors XIII, Algorithm (9.9), with its standalone and caller forms,
from Shiloach's algorithm, (7.2), (9.7), and the steps (5)--(7) program claim. -/
theorem algorithm_9_9_of_case3Steps (hShiloach : Shiloach80Statement)
    (h72 : Algorithm72Statement) (h97 : Algorithm97Statement)
    (hC3 : Case3StepsClaim) : Algorithm99Statement case3Decoder := by
  intro pp h h2 he
  by_cases hp : pp ≤ 1
  · exact ⟨0, algorithm_9_9_of_le_one hp h 0⟩
  · obtain ⟨h', ω, h2', he', P72, P97, C72, c72, C97, c97, hR72, hR97,
        C, C_blk, c, hC⟩ := alg99_parts hShiloach h72 h97 hC3 pp h h2 he
    let B := max 40 (max (folioCallerArrBase P72) (folioCallerArrBase P97))
    let Q := max 100 (max (folioCallerRegBase P72) (folioCallerRegBase P97))
    have hB : 40 ≤ B := le_max_left _ _
    have hB72 : folioCallerArrBase P72 ≤ B :=
      (le_max_left _ _).trans (le_max_right _ _)
    have hB97 : folioCallerArrBase P97 ≤ B :=
      (le_max_right _ _).trans (le_max_right _ _)
    have hQ : 100 ≤ Q := le_max_left _ _
    have hQ72 : folioCallerRegBase P72 ≤ Q :=
      (le_max_left _ _).trans (le_max_right _ _)
    have hQ97 : folioCallerRegBase P97 ≤ Q :=
      (le_max_right _ _).trans (le_max_right _ _)
    obtain ⟨P, hP⟩ := hC B Q hB
    obtain ⟨K4, hK4⟩ := alg99Step4Cost_le (pp.choose 2 + 5) h h' B
    refine ⟨ω, ⟨alg99MainProg P72 P97 P pp h h2 h' h2' B Q, ?_⟩, ?_⟩
    · exact alg99MainProg_computes hR72 hR97 hP hK4 hB hB72 hB97 (by omega) hQ72 hQ97
    · exact alg99Spec_of_runs hR72 hR97 hP hK4 hB hB72 hB97 hQ hQ72 hQ97

end GraphMinor.Compute
