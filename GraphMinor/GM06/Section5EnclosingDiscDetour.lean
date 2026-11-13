module

public import GraphMinor.GM06.Defs
public import GraphMinor.Surface.DiscGrow
import GraphMinor.GM06.Section5DiscDetour
import GraphMinor.GM06.Section5RegionInterior
import GraphMinor.GM06.Section5SimpleLiftedHelix
import GraphMinor.GM06.Section5SimpleLiftImageInterior
import GraphMinor.GM06.Section4
import GraphMinor.Surface.DiscMerge

/-!
# Detours around discs containing unused components

For Reduction 2 in VI (5.5), page 130, an enclosing disc may
contain retained components as well as discarded ones. Only its
boundary must miss the drawing. Retraction onto that boundary
removes vertex times in the disc interior and creates none, while
the relative homotopy preserves winding.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- Detouring around an enclosing disc whose boundary misses the
drawing removes vertex times and preserves winding. -/
theorem exists_helix_detour_of_disc_boundary_disjoint
    {k : ℕ} {G : Drawing ClosedCylinder} (f : Curve ClosedCylinder)
    (hf : IsHelix k G f) {D : Set ClosedCylinder} (hD : IsClosedDisc D)
    (hDU : Disjoint (discBd D) G.U)
    (h0 : f 0 ∉ discInt D) (h1 : f 1 ∉ discInt D)
    {a : ClosedCylinder} (ha : a ∈ discInt D) (haf : a ∉ range f) :
    ∃ g : Curve ClosedCylinder, IsHelix k G g ∧
      Disjoint (range g) (discInt D) ∧ curvePhi k G g ≤ curvePhi k G f ∧
      range g ⊆ range f ∪ discBd D := by
  obtain ⟨g, hhom, havoid, hfixed, hbd⟩ := exists_curve_detour_outside_disc
    isSurface_closedCylinder.2.2 hD f ha haf h0 h1
  have hsub : curveVertexHits G g ⊆ curveVertexHits G f := by
    intro t ht
    by_cases hft : f t ∈ discInt D
    · exact False.elim (disjoint_left.mp hDU (hbd t hft) (G.V_subset_U ht))
    · change f t ∈ G.V
      change g t ∈ G.V at ht
      rwa [hfixed t hft] at ht
  have hfin := hf.2.2.2.subset hsub
  have hnormal : IsNormalCurve G g := by
    rintro x ⟨⟨t, rfl⟩, ht⟩
    by_cases hft : f t ∈ discInt D
    · exact False.elim (disjoint_left.mp hDU (hbd t hft) ht)
    · rw [hfixed t hft] at ht ⊢
      exact hf.1 ⟨mem_range_self t, ht⟩
  refine ⟨g, ⟨hnormal, (hfixed 0 h0).symm ▸ hf.2.1,
    (hfixed 1 h1).symm ▸ hf.2.2.1, hfin⟩, havoid, ?_, ?_⟩
  · have hcount : curveL G g ≤ curveL G f := ncard_le_ncard hsub hf.2.2.2
    change windingNumber g + (k : ℝ)⁻¹ * (curveL G g : ℝ) ≤
      windingNumber f + (k : ℝ)⁻¹ * (curveL G f : ℝ)
    rw [windingNumber_eq_of_homotopic hhom]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcount)
      (inv_nonneg.mpr (Nat.cast_nonneg k : (0 : ℝ) ≤ k)))
  · rintro _ ⟨t, rfl⟩
    by_cases ht : f t ∈ discInt D
    · exact Or.inr (hbd t ht)
    · exact Or.inl (hfixed t ht ▸ mem_range_self t)

/-- A disc whose boundary misses the drawing can be avoided without increasing potential,
even when it encloses components of the retained drawing. -/
theorem exists_helix_avoiding_enclosing_disc_of_boundary_disjoint
    {k : ℕ} {G : Drawing ClosedCylinder} (f : Curve ClosedCylinder)
    (hf : IsHelix k G f) {D : Set ClosedCylinder} (hD : IsClosedDisc D)
    (hDU : Disjoint (discBd D) G.U) :
    ∃ g : Curve ClosedCylinder, IsHelix k G g ∧
      Disjoint (range g) (discInt D) ∧ curvePhi k G g ≤ curvePhi k G f ∧
      range g ⊆ range f ∪ discBd D := by
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
  have h0 : g 0 ∉ discInt D := by
    intro ht
    obtain ⟨j, hj⟩ := hg.2.1
    have hb : g 0 ∈ bd ClosedCylinder := by
      rw [← hj, bd_closedCylinder]; exact Or.inl rfl
    exact hb (isInteriorPoint_of_mem_discInt isSurface_closedCylinder.2.2 hD ht)
  have h1 : g 1 ∉ discInt D := by
    intro ht
    obtain ⟨j, hj⟩ := hg.2.2.1
    have hb : g 1 ∈ bd ClosedCylinder := by
      rw [← hj, bd_closedCylinder]; exact Or.inr rfl
    exact hb (isInteriorPoint_of_mem_discInt isSurface_closedCylinder.2.2 hD ht)
  obtain ⟨u, hu, huD, hφu, hur⟩ := exists_helix_detour_of_disc_boundary_disjoint
    g hg hD hDU h0 h1 ha haf
  have hφg : curvePhi k G g ≤ curvePhi k G f := by
    change windingNumber g + (k : ℝ)⁻¹ * (curveL G g : ℝ) ≤
      windingNumber f + (k : ℝ)⁻¹ * (curveL G f : ℝ)
    rw [hw]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hL)
      (inv_nonneg.mpr (Nat.cast_nonneg k : (0 : ℝ) ≤ k)))
  exact ⟨u, hu, huD, hφu.trans hφg, hur.trans (union_subset_union_left _ hsub)⟩

/-- An enclosing disc off the cuffs is a special case of the
boundary-disjoint enclosing-disc detour. -/
theorem exists_helix_avoiding_enclosing_disc
    {k : ℕ} {G : Drawing ClosedCylinder} (f : Curve ClosedCylinder)
    (hf : IsHelix k G f) {D : Set ClosedCylinder} (hD : IsClosedDisc D)
    (hDU : Disjoint (discBd D) G.U) (_hDb : Disjoint D (bd ClosedCylinder)) :
    ∃ g : Curve ClosedCylinder, IsHelix k G g ∧
      Disjoint (range g) (discInt D) ∧ curvePhi k G g ≤ curvePhi k G f ∧
      range g ⊆ range f ∪ discBd D :=
  exists_helix_avoiding_enclosing_disc_of_boundary_disjoint f hf hD hDU

end GraphMinor.GM06
