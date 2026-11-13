module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5

/-!
# Terminal positions from linkage winding

The indexed lift fixes the initial angle. Its angular displacement gives
the terminal formula in the base case of (5.3).
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface Real
/-- The terminal position used in VI (5.3), page 132, obtained from
the lifted linkage curve and its common winding. -/
theorem CylinderLinkage.curve_one_eq_of_hasTheta {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hk : 0 < k) (hθ : L.HasTheta θ) (i : Fin k) :
    L.curve i 1 = cylinderPoint 2 (by simp)
      (2 * ((i.1 + 1 : ℕ) : ℝ) * π / (k : ℝ) + 2 * π * θ) := by
  let m : ℤ := (i.1 : ℤ) + 1
  have hi : modIdx k hk m = i := modIdx_natCast_succ hk i
  have hp := liftedLinkageCurve_props hk L hθ m
  dsimp only at hp
  have hexp := hp.2.2.2.2.2 1
  rw [hi, hp.2.2.2.2.1] at hexp
  have hr : (L.curve i 1).1.1 = 2 := by
    obtain ⟨j, hj⟩ := L.curve_one_mem i
    rw [← hj]
    rfl
  apply Subtype.ext
  apply Prod.ext hr
  change (L.curve i 1).1.2 = Circle.exp _
  rw [← hexp]
  congr 2
end GraphMinor.GM06
