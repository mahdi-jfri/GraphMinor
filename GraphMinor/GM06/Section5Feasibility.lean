module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5
import GraphMinor.GM06.Section5Extrema
import GraphMinor.GM06.Section5TightHelix
import GraphMinor.GM06.Section5LowerHelix
import GraphMinor.GM06.Section5Interval
import Mathlib.Tactic.Linarith

/-!
# The full helix characterization of feasibility

Graph Minors VI (5.10), page 134, follows the paper's extreme
winding argument. Choose the least and greatest feasible windings.
The upper tight helix from (5.3) and its orientation-reversed lower
counterpart force every number satisfying the helix bounds between
those extremes. Integrality and (5.9) then make it feasible. The
necessity direction is the proved winding integrality and (5.2).
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- Graph Minors VI (5.10), page 134, in both directions: winding
integrality, existence of a linkage and all helix bounds characterize feasibility. -/
theorem theorem_5_10_proof : Statement510 := by
  intro k G θ hG
  refine ⟨theorem_5_10_mp k G θ hG, ?_⟩
  rintro ⟨hint, hlink, hbounds⟩
  obtain ⟨lo, hi, hlo, hhi, hext⟩ := exists_min_max_feasible k G hG hlink
  have hpos : 0 < 1 / (k : ℝ) := div_pos zero_lt_one (Nat.cast_pos.mpr hG.1)
  have hnext : ¬ IsThetaFeasible k G (hi + 1 / (k : ℝ)) := by
    intro hh
    have hle := (hext _ hh).2
    linarith
  obtain ⟨fhi, hfhi, hφhi⟩ := theorem_5_3_proof k G hi hG hhi hnext
  obtain ⟨flo, hflo, hφlo⟩ := exists_tight_lower_helix_of_minimum hG hlo
    (fun ψ hψ => (hext ψ hψ).1)
  have hθhi : θ ≤ hi := by
    have hh := (hbounds fhi hfhi).2
    change θ ≤ curvePhi k G fhi at hh
    rwa [hφhi] at hh
  have hloθ : lo ≤ θ := by
    have hh := (hbounds flo hflo).1
    rwa [hφlo] at hh
  exact theorem_5_9_proof k G lo θ hi hG hloθ hθhi hlo hhi hint

end GraphMinor.GM06
