module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5Initial
import GraphMinor.GM06.Section5ValencyOneCase
import GraphMinor.GM06.Section5TightHelixBase
import GraphMinor.GM06.Section5

/-!
# The terminal feasibility test in VI (5.7)

When no reduction applies, (5.1) constructs the next winding unless
an initial vertex has valency one. In that case its sole neighbour is
on the other cuff. The valency-one helix construction gives potential
equal to the current winding, so (5.2) excludes the next winding.
Thus testing the initial valencies decides this terminal case.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Surface

/-- The terminal decision in VI (5.7), page 133: an unreduced instance
has the next winding exactly when no initial vertex has valency one. -/
theorem isThetaFeasible_next_iff_no_initial_valency_one
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies k G L) :
    IsThetaFeasible k G (θ + 1 / (k : ℝ)) ↔
      ∀ i : Fin k, vertexValency G.toGraph (cylinderM1Point k i) ≠ 1 := by
  constructor
  · intro hfeas i hi
    obtain ⟨e, _, t, ht, hl⟩ := exists_cuff2_neighbour_of_valency_one L hG hno i hi
    obtain ⟨f, hf, hphi⟩ :=
      exists_tight_helix_of_initial_valency_one L hG hθ i hi hl ht.2
    have hupper := (theorem_5_2_proof k G (θ + 1 / (k : ℝ)) f hG hfeas hf).2
    change θ + 1 / (k : ℝ) ≤ curvePhi k G f at hupper
    rw [hphi] at hupper
    have hpos : (0 : ℝ) < 1 / (k : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hG.1)
    exact (not_le_of_gt (lt_add_of_pos_right θ hpos)) hupper
  · intro hval
    rcases theorem_5_1_proof k G L θ hG hθ hno with h | h
    · obtain ⟨i, hi, _⟩ := h
      exact False.elim (hval i hi)
    · exact h

end GraphMinor.GM06
