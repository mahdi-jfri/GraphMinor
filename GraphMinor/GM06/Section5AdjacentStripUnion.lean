module

public import GraphMinor.GM06.Section5LinkageStripCircle
import GraphMinor.GM06.Section5AdjacentStripDiscs
import GraphMinor.GM06.Section5LiftedPaths
import GraphMinor.Surface.DiscUnion
import GraphMinor.GM11.Fan

/-!
# The union of two adjacent lifted strips

For the neighbourhood argument in VI (5.1), page 129, join two
adjacent lifted strip discs along their common linkage curve. The
disc union theorem gives another closed disc. Its boundary has only
the two outer linkage curves and the cuff lines. Thus the shared
initial point is away from every boundary piece except its cuff.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- Two adjacent lifted strip discs form a closed disc whose
boundary is confined to the outer lifts and the two cuff lines. -/
theorem adjacent_liftedStripDiscs_union
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) (m : ℤ)
    {D E : Set (ℝ × ℝ)} (hD : IsClosedDisc D) (hE : IsClosedDisc E)
    (hBdD : discBd D = liftedStripBoundary hG.1 L m)
    (hBdE : discBd E = liftedStripBoundary hG.1 L (m + 1))
    (hstripD : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (hstripE : E ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) :
    IsClosedDisc (D ∪ E) ∧ discBd (D ∪ E) ⊆
      range (liftedLinkageCurve hG.1 L m) ∪ range (liftedLinkageCurve hG.1 L (m + 1 + 1)) ∪
        {p : ℝ × ℝ | p.1 = 1 ∨ p.1 = 2} := by
  let f := liftedLinkageCurve hG.1 L (m + 1)
  have hf := isArcMap_liftedLinkageCurve hG.1 L (m + 1)
  have hleft : range f ⊆ discBd D := by rw [hBdD]; exact fun _ hx => Or.inl (Or.inl (Or.inr hx))
  have hright : range f ⊆ discBd E := by rw [hBdE]; exact fun _ hx => Or.inl (Or.inl (Or.inl hx))
  obtain ⟨hU, hBdU⟩ := disc_union D E (range f) (f 0) (f 1) hD hE
    (GM11.isLineWithEnds_range f hf.2)
    (inter_adjacent_liftedStripDiscs L hG hθ m hD hE hBdD hBdE hstripD hstripE) hleft hright
  have hends (p : ℝ × ℝ) (hp : p ∈ range f) (hnot : p ∉ range f \ {f 0, f 1}) :
      p.1 = 1 ∨ p.1 = 2 := by
    have hpends : p ∈ ({f 0, f 1} : Set (ℝ × ℝ)) := by
      by_contra hn
      exact hnot ⟨hp, hn⟩
    have hh := liftedLinkageCurve_props_raw hG.1 L (m + 1)
    rcases hpends with hp0 | hp1
    · exact Or.inl (congrArg Prod.fst hp0 |>.trans hh.2.1)
    · exact Or.inr (congrArg Prod.fst (mem_singleton_iff.mp hp1) |>.trans hh.2.2.1)
  refine ⟨hU, ?_⟩
  intro p hp
  rw [hBdU] at hp
  rcases hp.1 with hpD | hpE
  · rw [hBdD] at hpD
    rcases hpD with ((hpD | hpD) | hpD) | hpD
    · exact Or.inl (Or.inl hpD)
    · exact Or.inr (hends p hpD hp.2)
    · exact Or.inr (Or.inl (mem_singleton_iff.mp hpD.1))
    · exact Or.inr (Or.inr (mem_singleton_iff.mp hpD.1))
  · rw [hBdE] at hpE
    rcases hpE with ((hpE | hpE) | hpE) | hpE
    · exact Or.inr (hends p hpE hp.2)
    · exact Or.inl (Or.inr hpE)
    · exact Or.inr (Or.inl (mem_singleton_iff.mp hpE.1))
    · exact Or.inr (Or.inr (mem_singleton_iff.mp hpE.1))

end GraphMinor.GM06
