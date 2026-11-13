module

public import GraphMinor.GM06.Section5LinkageStripCircle
import GraphMinor.GM06.Section5StripCuffs
import GraphMinor.GM06.Section5StripAvoidance
import GraphMinor.Surface.PlaneOrientation
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Tactic

/-!
# Adjacent strip discs have just their common path in common

For the strip gluing in VI Reduction 3, page 129, consecutive closed
strip discs meet exactly along their shared linkage lift. The
interior of the first disc misses the boundary of the second. The
disc-side lemma and the ordered initial endpoints exclude nesting.
The radial bounds then identify every remaining common cuff point
with an endpoint of the shared lift.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

/-- Adjacent closed lifted strip discs meet exactly along their common
linkage curve. This holds also for one linkage path, when consecutive
lifts project to the same path on the cylinder. -/
theorem inter_adjacent_liftedStripDiscs
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) (m : ℤ)
    {D E : Set (ℝ × ℝ)} (hD : IsClosedDisc D) (hE : IsClosedDisc E)
    (hBdD : discBd D = liftedStripBoundary hG.1 L m)
    (hBdE : discBd E = liftedStripBoundary hG.1 L (m + 1))
    (hstripD : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (hstripE : E ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) :
    D ∩ E = range (liftedLinkageCurve hG.1 L (m + 1)) := by
  have hfarD := disjoint_stripDisc_of_other_index L hG hθ
    (m := m) (n := m + 1 + 1) (by omega) (by omega) hD hBdD hstripD
  have hfarE := disjoint_stripDisc_of_other_index L hG hθ
    (m := m + 1) (n := m) (by omega) (by omega) hE hBdE hstripE
  have hdisbd : Disjoint (discInt D) (discBd E) := by
    apply disjoint_left.mpr
    intro p hp hpE
    rw [hBdE] at hpE
    rcases hpE with ((hpE | hpE) | hpE) | hpE
    · apply hp.2
      rw [hBdD]
      exact Or.inl (Or.inl (Or.inr hpE))
    · exact disjoint_left.mp hfarD hpE hp.1
    · have hp1 : p.1 = 1 := mem_singleton_iff.mp hpE.1
      have hh := (discInt_subset_open_radial_strip hD hstripD hp).1
      rw [hp1] at hh
      exact lt_irrefl _ hh
    · have hp2 : p.1 = 2 := mem_singleton_iff.mp hpE.1
      have hh := (discInt_subset_open_radial_strip hD hstripD hp).2
      rw [hp2] at hh
      exact lt_irrefl _ hh
  have hpD : liftedLinkageCurve hG.1 L m 0 ∈ D := by
    apply discBd_subset D
    rw [hBdD]
    exact Or.inl (Or.inl (Or.inl (mem_range_self 0)))
  have hpE : liftedLinkageCurve hG.1 L m 0 ∉ E :=
    fun hp => disjoint_left.mp hfarE (mem_range_self 0) hp
  let e : ℂ ≃ₜ ℝ × ℝ := Complex.equivRealProdCLM.toHomeomorph
  have hman (p : ℝ × ℝ) : IsManifoldPoint p := by
    have hh := isManifoldPoint_of_isOpenEmbedding e.isOpenEmbedding
      (isManifoldPoint_complex (e.symm p))
    simpa only [e.apply_symm_apply] using hh
  have hdis : Disjoint (discInt D) E := by
    rcases hE.side hman hD.isPreconnected_discInt hdisbd with hin | hout
    · have hc : closure (discInt D) ⊆ E :=
        closure_minimal (fun p hp => (hin hp).1) hE.isClosed
      exact False.elim (hpE (hc (hD.subset_closure_discInt hpD)))
    · exact hout
  apply subset_antisymm
  · rintro p ⟨hpD, hpE'⟩
    have hpbd : p ∈ discBd D := by
      by_contra hn
      exact disjoint_left.mp hdis ⟨hpD, hn⟩ hpE'
    rw [hBdD] at hpbd
    rcases hpbd with ((hpbd | hpbd) | hpbd) | hpbd
    · exact False.elim (disjoint_left.mp hfarE hpbd hpE')
    · exact hpbd
    · have hp1 : p.1 = 1 := mem_singleton_iff.mp hpbd.1
      have hbounds := stripDisc_radius_one_mem_interval L hG hθ (m + 1)
        hE hBdE hstripE hpE' hp1
      have hangle := le_antisymm hpbd.2.2 hbounds.1
      exact ⟨0, Prod.ext ((liftedLinkageCurve_props_raw hG.1 L (m + 1)).2.1.trans hp1.symm)
        hangle.symm⟩
    · have hp2 : p.1 = 2 := mem_singleton_iff.mp hpbd.1
      have hbounds := stripDisc_radius_two_mem_interval L hG hθ (m + 1)
        hE hBdE hstripE hpE' hp2
      have hangle := le_antisymm hpbd.2.2 hbounds.1
      exact ⟨1, Prod.ext ((liftedLinkageCurve_props_raw hG.1 L (m + 1)).2.2.1.trans hp2.symm)
        hangle.symm⟩
  · intro p hp
    constructor
    · apply discBd_subset D
      rw [hBdD]
      exact Or.inl (Or.inl (Or.inr hp))
    · apply discBd_subset E
      rw [hBdE]
      exact Or.inl (Or.inl (Or.inl hp))

end GraphMinor.GM06
