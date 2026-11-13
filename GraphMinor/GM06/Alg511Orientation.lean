module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM06.Section5ReflectionDrawing
import GraphMinor.GM06.Section5ReflectionLinkage
import Mathlib.Tactic

/-!
# Choosing orientation for VI (5.11)

The procedure on page 134 reverses the plane orientation when the
initial linkage winding is greater than the target. The existing
reflection of cylinder drawings negates every feasible winding and
preserves the Section 5 drawing conditions. Apply it simultaneously
to the drawing, linkage and target. The resulting initial winding
is at most the resulting target, and feasibility is unchanged by
this choice of coordinates.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Surface

/-- The orientation choice of VI (5.11), page 134, preserves the
feasibility question and puts the initial winding below the target. -/
theorem alg511_orient_initial_linkage {k : ℕ} {G : Drawing ClosedCylinder}
    (hG : IsCylinderSection5Drawing k G) (L : CylinderLinkage k G)
    {current target : ℝ} (hcurrent : L.HasTheta current) :
    ∃ (G' : Drawing ClosedCylinder) (L' : CylinderLinkage k G') (current' target' : ℝ),
      IsCylinderSection5Drawing k G' ∧ L'.HasTheta current' ∧ current' ≤ target' ∧
      (IsThetaFeasible k G' target' ↔ IsThetaFeasible k G target) ∧
      ((G' = G ∧ current' = current ∧ target' = target) ∨
        (G' = section5ReflectedDrawing k G ∧ current' = -current ∧ target' = -target)) := by
  by_cases hle : current ≤ target
  · exact ⟨G, L, current, target, hG, hcurrent, hle, Iff.rfl,
      Or.inl ⟨rfl, rfl, rfl⟩⟩
  · exact ⟨section5ReflectedDrawing k G, section5ReflectedLinkage hG.1 L,
      -current, -target, isCylinderSection5Drawing_reflected hG,
      hasTheta_section5ReflectedLinkage hG.1 L hcurrent,
      neg_le_neg (le_of_lt (lt_of_not_ge hle)),
      isThetaFeasible_reflected_iff hG.1 target, Or.inr ⟨rfl, rfl, rfl⟩⟩

end GraphMinor.GM06
