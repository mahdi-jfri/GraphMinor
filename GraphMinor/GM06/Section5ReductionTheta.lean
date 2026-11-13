module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section5Reduction4

/-!
# Winding preservation through the four cylinder reductions

Reductions 1 and 2 keep all linkage curves. The contraction in
Reduction 3 gives an endpoint-fixed homotopy. Reduction 4 preserves
the common winding through a different unchanged linkage path.
These are the winding identities used in VI (5.3) and (5.6).
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- Each of the four reductions preserves the common winding number of the
specified linkage, as used in Graph Minors VI (5.6), page 133. -/
theorem theta_eq_of_reduction (k : ℕ) (G G' : Drawing ClosedCylinder)
    (L : CylinderLinkage k G) (L' : CylinderLinkage k G') (θ θ' : ℝ)
    (hk : 0 < k) (hL : L.HasTheta θ) (hL' : L'.HasTheta θ')
    (hRed : Section5ReductionStep k G L G' L') : θ' = θ := by
  let j : Fin k := ⟨0, hk⟩
  rcases hRed with h1 | h2 | h3 | h4
  · rcases h1 with ⟨_, _, _, _, _, _, _, _, hcurve⟩
    rw [← hL' j, ← hL j, hcurve]
  · rcases h2 with ⟨_, _, _, _, _, _, _, _, hcurve⟩
    rw [← hL' j, ← hL j, hcurve]
  · rcases h3 with ⟨_, _, _, π_map, H_id, _, _, _, _, _, _,
      hH0, hH1, hHbd, _, _, _, _, _, _, _, _, hcurves, _⟩
    have h0 : L.curve j 0 ∈ bd ClosedCylinder := by
      rw [(L.curve_parametrizes j).2.2.1]
      exact cylinderM1Point_mem_bd k j
    have h1 : L.curve j 1 ∈ bd ClosedCylinder := by
      obtain ⟨i, hi⟩ := L.curve_one_mem j
      rw [← hi]
      exact cylinderM2Point_mem_bd k i
    have hhom := curvesHomotopic_comp_pi_map hH0 hH1 hHbd h0 h1
    rw [← hL' j, ← hL j, windingNumber_eq_of_homotopic (hcurves j).2,
      ← windingNumber_eq_of_homotopic hhom]
  · exact theta_eq_of_reduction4 L L' hL hL' h4

end GraphMinor.GM06
