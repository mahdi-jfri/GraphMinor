module

public import GraphMinor.GM06.Section5LinkageStripCircle
import GraphMinor.GM06.Section5StripCuffs
import GraphMinor.GM06.Section5StripAvoidance
import GraphMinor.Surface.DiscGrow
import GraphMinor.Surface.PlaneOrientation

/-!
# Separated lifted strip discs are disjoint

For the winding calculation in VI (5.1), page 129, the disc between
two consecutive linkage lifts must not overlap a distant copy.
Its boundary paths miss the other disc by the lift-exclusion lemma.
The cuff intervals miss it by the strict order of their endpoints.
A connected disc missing another disc's boundary stays on one side.
Its initial endpoint is outside the other disc, so the discs are disjoint.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface

private theorem disjoint_lifted_boundary_disc_of_index_gap
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) {m n : ℤ} (hmn : m + 1 < n)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L m)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) :
    Disjoint (liftedStripBoundary hG.1 L n) D := by
  have hn := disjoint_stripDisc_of_other_index L hG hθ
    (show n ≠ m by omega) (show n ≠ m + 1 by omega) hD hBd hstrip
  have hn₁ := disjoint_stripDisc_of_other_index L hG hθ
    (show n + 1 ≠ m by omega) (show n + 1 ≠ m + 1 by omega) hD hBd hstrip
  have horder := liftedLinkageCurve_ends_lt_of_index_lt hG.1 L hθ hmn
  apply disjoint_left.mpr
  intro p hp hpD
  rcases hp with ((hp | hp) | hp) | hp
  · exact disjoint_left.mp hn hp hpD
  · exact disjoint_left.mp hn₁ hp hpD
  · have hrad : p.1 = 1 := mem_singleton_iff.mp hp.1
    have hbounds := stripDisc_radius_one_mem_interval L hG hθ m hD hBd hstrip hpD hrad
    exact (not_lt_of_ge hbounds.2) (horder.1.trans_le hp.2.1)
  · have hrad : p.1 = 2 := mem_singleton_iff.mp hp.1
    have hbounds := stripDisc_radius_two_mem_interval L hG hθ m hD hBd hstrip hpD hrad
    exact (not_lt_of_ge hbounds.2) (horder.2.trans_le hp.2.1)

/-- Closed discs between nonadjacent indexed lifts are disjoint,
as used to identify the lifted strip in VI (5.1), page 129. -/
theorem disjoint_liftedStripDiscs_of_index_gap
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) {m n : ℤ} (hmn : m + 1 < n)
    {D E : Set (ℝ × ℝ)} (hD : IsClosedDisc D) (hE : IsClosedDisc E)
    (hBdD : discBd D = liftedStripBoundary hG.1 L m)
    (hBdE : discBd E = liftedStripBoundary hG.1 L n)
    (hstripD : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (hstripE : E ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) : Disjoint D E := by
  have hbd : Disjoint D (discBd E) := by
    rw [hBdE]
    exact (disjoint_lifted_boundary_disc_of_index_gap L hG hθ hmn hD hBdD hstripD).symm
  have hpD : liftedLinkageCurve hG.1 L m 0 ∈ D := by
    apply discBd_subset D
    rw [hBdD]
    exact Or.inl (Or.inl (Or.inl (mem_range_self 0)))
  have hpE : liftedLinkageCurve hG.1 L m 0 ∉ E := by
    intro hp
    have hbounds := stripDisc_radius_one_mem_interval L hG hθ n hE hBdE hstripE hp
      (liftedLinkageCurve_props_raw hG.1 L m).2.1
    have horder := liftedLinkageCurve_ends_lt_of_index_lt hG.1 L hθ
      (show m < n by omega)
    exact (not_lt_of_ge hbounds.1) horder.1
  let e : ℂ ≃ₜ ℝ × ℝ := Complex.equivRealProdCLM.toHomeomorph
  have hman (p : ℝ × ℝ) : IsManifoldPoint p := by
    have hh := isManifoldPoint_of_isOpenEmbedding e.isOpenEmbedding
      (isManifoldPoint_complex (e.symm p))
    simpa only [e.apply_symm_apply] using hh
  rcases hE.side hman hD.isPathConnected.isConnected.isPreconnected hbd with hin | hout
  · exact False.elim (hpE (hin hpD).1)
  · exact hout

end GraphMinor.GM06
