module

public import GraphMinor.GM06.Section5CutStripSurface
import GraphMinor.GM06.Section5SingleStripFibers
import GraphMinor.GM06.Section5StripImage

/-!
# The two seam copies of the one-path cut disc

Over the sole linkage path, the cut disc has exactly its two seam
copies. Choose a point on one copy with the prescribed projection.
The proved fiber classification says that every other point above
it is on that copy or the other one. This identifies the target
set for the first-contact step in VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- The part of a one-path strip disc projecting to the linkage is
exactly the union of its two seam copies. -/
theorem preimage_path_inter_single_strip_eq_seams
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ) (m : ℤ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L m)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) :
    D ∩ radialCylinderProjection ⁻¹' (L.pathDrawing 0).U =
      range (liftedLinkageCurve hG.1 L m) ∪
        range (liftedLinkageCurve hG.1 L (m + 1)) := by
  have hproj (n : ℤ) (t : unitInterval) :
      radialCylinderProjection (liftedLinkageCurve hG.1 L n t) = L.curve 0 t := by
    rw [radialCylinderProjection_liftedLinkageCurve]
    have hi : modIdx 1 hG.1 n = 0 := Subsingleton.elim _ _
    rw [hi]
  have hmem (n : ℤ) (t : unitInterval) :
      radialCylinderProjection (liftedLinkageCurve hG.1 L n t) ∈ (L.pathDrawing 0).U := by
    rw [hproj]
    exact (L.curve_parametrizes 0).2.1 ▸ mem_range_self t
  ext p
  constructor
  · rintro ⟨hp, hpP⟩
    obtain ⟨t, ht⟩ := (L.curve_parametrizes 0).2.1.symm ▸ hpP
    have hq : liftedLinkageCurve hG.1 L m t ∈ D := by
      apply discBd_subset D
      rw [hBd]
      exact Or.inl (Or.inl (Or.inl (mem_range_self t)))
    have heq : radialCylinderProjection p =
        radialCylinderProjection (liftedLinkageCurve hG.1 L m t) := ht.symm.trans (hproj m t).symm
    rcases radialCylinderProjection_single_strip_fibers L hG hθ m hD hBd hstrip hp hq heq with
      h | ⟨u, hu | hu⟩
    · exact Or.inl ⟨t, h.symm⟩
    · exact Or.inr ⟨u, hu.1.symm⟩
    · exact Or.inl ⟨u, hu.2.symm⟩
  · intro hp
    constructor
    · apply discBd_subset D
      rw [hBd]
      exact Or.inl (Or.inl hp)
    · rcases hp with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · exact hmem m t
      · exact hmem (m + 1) t

end GraphMinor.GM06
