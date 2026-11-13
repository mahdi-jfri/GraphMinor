module

public import GraphMinor.GM06.Defs
public import GraphMinor.Surface.DiscGrow
import GraphMinor.GM06.Section5DiscDetour
import GraphMinor.GM06.Section5RegionInterior
import GraphMinor.GM06.Section5SimpleLiftedHelix
import GraphMinor.GM06.Section5SimpleLiftImageInterior
import GraphMinor.Surface.Cylinder
import GraphMinor.GM06.Section4

/-!
# Disc detours preserve helix potential

In the Reduction 2 argument of VI (5.5), page 130, a disc missing
the retained drawing and the cuffs contains no retained vertex.
Pushing a helix out of that disc therefore preserves its vertex
visits and its winding. A simple angular-cover representative leaves
an omitted interior point available for the disc retraction.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- A disc detour disjoint from the drawing and cuffs preserves
normality, every vertex time, and the winding of a helix. -/
theorem exists_helix_detour_outside_disc
    {k : ℕ} {G : Drawing ClosedCylinder} (f : Curve ClosedCylinder)
    (hf : IsHelix k G f) {D : Set ClosedCylinder} (hD : IsClosedDisc D)
    (hDU : Disjoint D G.U) (hDb : Disjoint D (bd ClosedCylinder))
    {a : ClosedCylinder} (ha : a ∈ discInt D) (haf : a ∉ range f) :
    ∃ g : Curve ClosedCylinder, IsHelix k G g ∧
      Disjoint (range g) (discInt D) ∧
      curvePhi k G g = curvePhi k G f ∧
      (∀ t, f t ∉ discInt D → g t = f t) ∧
      range g ⊆ range f ∪ D := by
  have h0 : f 0 ∉ discInt D := by
    intro ht
    exact disjoint_left.mp hDb ht.1 (by
      rw [bd_closedCylinder]
      exact Or.inl (by obtain ⟨j, hj⟩ := hf.2.1; rw [← hj]; rfl))
  have h1 : f 1 ∉ discInt D := by
    intro ht
    exact disjoint_left.mp hDb ht.1 (by
      rw [bd_closedCylinder]
      exact Or.inr (by obtain ⟨j, hj⟩ := hf.2.2.1; rw [← hj]; rfl))
  obtain ⟨g, hhom, havoid, hfixed, hbd⟩ := exists_curve_detour_outside_disc
    isSurface_closedCylinder.2.2 hD f ha haf h0 h1
  have hhit (t) : g t ∈ G.V ↔ f t ∈ G.V := by
    by_cases ht : f t ∈ discInt D
    · have hgn : g t ∉ G.U := fun h => disjoint_left.mp hDU
        (discBd_subset D (hbd t ht)) h
      have hfn : f t ∉ G.U := fun h => disjoint_left.mp hDU ht.1 h
      exact ⟨fun h => False.elim (hgn (G.V_subset_U h)),
        fun h => False.elim (hfn (G.V_subset_U h))⟩
    · rw [hfixed t ht]
  have hnormal : IsNormalCurve G g := by
    rintro x ⟨⟨t, rfl⟩, ht⟩
    by_cases hft : f t ∈ discInt D
    · exact False.elim (disjoint_left.mp hDU (discBd_subset D (hbd t hft)) ht)
    · rw [hfixed t hft] at ht ⊢
      exact hf.1 ⟨mem_range_self t, ht⟩
  have hhits : curveVertexHits G g = curveVertexHits G f := by
    ext t
    exact hhit t
  refine ⟨g, ⟨hnormal, (hfixed 0 h0).symm ▸ hf.2.1,
    (hfixed 1 h1).symm ▸ hf.2.2.1, hhits.symm ▸ hf.2.2.2⟩, havoid, ?_, hfixed, ?_⟩
  · simp only [curvePhi, curveL, hhits, windingNumber_eq_of_homotopic hhom]
  · rintro _ ⟨t, rfl⟩
    by_cases ht : f t ∈ discInt D
    · exact Or.inr (discBd_subset D (hbd t ht))
    · exact Or.inl (hfixed t ht ▸ mem_range_self t)

/-- Every closed disc disjoint from the drawing and the cuffs can
be avoided without increasing a helix's potential. -/
theorem exists_helix_avoiding_disc
    {k : ℕ} {G : Drawing ClosedCylinder} (f : Curve ClosedCylinder)
    (hf : IsHelix k G f) {D : Set ClosedCylinder} (hD : IsClosedDisc D)
    (hDU : Disjoint D G.U) (hDb : Disjoint D (bd ClosedCylinder)) :
    ∃ g : Curve ClosedCylinder, IsHelix k G g ∧
      Disjoint (range g) (discInt D) ∧ curvePhi k G g ≤ curvePhi k G f ∧
      range g ⊆ range f ∪ D := by
  obtain ⟨g, q, hq, hproj, hg, hw, hL, hsub⟩ := exists_helix_with_injective_cover_lift f hf
  have hgr : range g = cylinderCoverProjection '' range q := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨q t, mem_range_self t, hproj t⟩
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, (hproj t).symm⟩
  have hempty : interior (range g) = ∅ := by
    rw [hgr]
    exact interior_projection_injective_cover_curve_eq_empty q hq
  have hne : ¬ discInt D ⊆ range g := by
    intro hsub
    have hsub' := interior_maximal hsub (hD.isOpen_discInt isSurface_closedCylinder.2.2)
    rw [hempty] at hsub'
    exact hD.nonempty_discInt.ne_empty (eq_empty_of_subset_empty hsub')
  obtain ⟨a, ha, haf⟩ := not_subset.mp hne
  obtain ⟨u, hu, huD, hφ, hfix, hur⟩ := exists_helix_detour_outside_disc g hg hD hDU hDb ha haf
  have hφg : curvePhi k G g ≤ curvePhi k G f := by
    change windingNumber g + (k : ℝ)⁻¹ * (curveL G g : ℝ) ≤
      windingNumber f + (k : ℝ)⁻¹ * (curveL G f : ℝ)
    rw [hw]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hL)
      (inv_nonneg.mpr (Nat.cast_nonneg k : (0 : ℝ) ≤ k)))
  exact ⟨u, hu, huD, hφ.le.trans hφg, hur.trans (union_subset_union_left D hsub)⟩

end GraphMinor.GM06
