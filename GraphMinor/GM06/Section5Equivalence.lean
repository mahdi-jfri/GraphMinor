module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5TightHelix
import GraphMinor.GM06.Section5HelixPullback
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section5ReductionTheta

/-!
# Equivalence under cylinder reductions

Graph Minors VI (5.6) uses (5.4) in one direction. In the other direction,
(5.3) gives a tight helix in the reduced drawing, and (5.5) brings it back.
The bound (5.2) then rules out the next winding number in the original drawing.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

/-- Graph Minors VI, (5.6), page 133, from (5.3) and (5.5):
"If $(G', \mathscr{L}')$ is produced from $(G, \mathscr{L})$ by one of the reductions 1,...,
4, then $\theta(\mathscr{L}') + 1/k$ is feasible in $G'$ if and only if $\theta(\mathscr{L})$
+ 1/k$ is feasible in $G$." -/
theorem theorem_5_6_proof : Statement56 := by
  intro k G G' L L' θ θ' hG hG' hL hL' hRed
  refine ⟨theorem_5_4_proof k G G' L L' θ θ' hG hG' hL hL' hRed, ?_⟩
  intro hnext
  by_contra hnext'
  obtain ⟨f', hf', hphi'⟩ := theorem_5_3_proof k G' θ' hG' ⟨L', hL'⟩ hnext'
  obtain ⟨f, hf, hphi⟩ := theorem_5_5_proof k G G' L L' f' hG hG' hRed hf'
  have heq := theta_eq_of_reduction k G G' L L' θ θ' hG.1 hL hL' hRed
  have hbound := (theorem_5_2_proof k G (θ + 1 / (k : ℝ)) f hG hnext hf).2
  change θ + 1 / (k : ℝ) ≤ curvePhi k G f at hbound
  have hpos : 0 < 1 / (k : ℝ) := div_pos zero_lt_one (Nat.cast_pos.mpr hG.1)
  linarith

end GraphMinor.GM06
