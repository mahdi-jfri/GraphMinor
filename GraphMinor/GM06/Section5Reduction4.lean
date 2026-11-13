module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5SidedReduction4Winding

/-!
# Winding preservation for a linkage rerouting

For VI Reduction 4, page 129, an unchanged linkage path preserves the
common winding when at least two paths are present. With one path,
the corrected incidence condition fixes the lifted contact, and the
shared-tail comparison proves the winding identity.
-/

public section

namespace GraphMinor.GM06

open GraphMinor.Surface

/-- The common winding number is preserved by the corrected Reduction 4
of Graph Minors VI, page 129, including the one-path side correction
(see the correction to Reduction 4 and (5.6) in `corrections/GM06.md`). -/
theorem theta_eq_of_reduction4
    {k : ℕ} {G G' : Drawing ClosedCylinder}
    (L : CylinderLinkage k G) (L' : CylinderLinkage k G') {θ θ' : ℝ}
    (hL : L.HasTheta θ) (hL' : L'.HasTheta θ')
    (hRed : Section5Reduction4Step k G L G' L') : θ' = θ := by
  rcases hRed.2 with ⟨hk, h⟩ | ⟨hk, h⟩
  · obtain ⟨i, v, A, B, Q, _, _, _, _, _, _, _, _, _, _, hother⟩ := h
    haveI : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
    obtain ⟨j, hji⟩ := exists_ne i
    rw [← hL' j, ← hL j, (hother j hji).2]
  · subst k
    exact theta_eq_of_sided_reduction4_one L L' hL hL' h

end GraphMinor.GM06
