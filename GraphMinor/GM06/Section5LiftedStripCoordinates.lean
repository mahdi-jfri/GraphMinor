module

public import GraphMinor.GM06.Section5LinkageStripCircle
import GraphMinor.GM06.Section5StripCoordinates
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Tactic

/-!
# Compatible coordinates on the lifted linkage strips

For Reduction 3 of VI, page 129, the closed disc between two
consecutive linkage lifts is parametrized by a square. The two
vertical sides retain the given path parameters. The horizontal
sides parametrize the cuff intervals linearly. Thus the coordinate
maps of adjacent strips agree on the common linkage curve.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

/-- A lifted linkage strip has injective square coordinates that
agree exactly with the two linkage curves and the cuff intervals. -/
theorem exists_lifted_strip_coordinates
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) (m : ℤ) {D : Set (ℝ × ℝ)}
    (hD : IsClosedDisc D) (hDb : discBd D = liftedStripBoundary hG.1 L m) :
    ∃ F : C(unitInterval × unitInterval, ℝ × ℝ),
      Function.Injective F ∧ range F = D ∧
      (∀ t, F (0, t) = liftedLinkageCurve hG.1 L m t) ∧
      (∀ t, F (1, t) = liftedLinkageCurve hG.1 L (m + 1) t) ∧
      (∀ u, F (u, 0) = (1, (1 - u.1) * (liftedLinkageCurve hG.1 L m 0).2 +
        u.1 * (liftedLinkageCurve hG.1 L (m + 1) 0).2)) ∧
      (∀ u, F (u, 1) = (2, (1 - u.1) * (liftedLinkageCurve hG.1 L m 1).2 +
        u.1 * (liftedLinkageCurve hG.1 L (m + 1) 1).2)) := by
  let e : ℂ ≃ₜ ℝ × ℝ := Complex.equivRealProdCLM.toHomeomorph
  have hre (p : ℝ × ℝ) : (e.symm p).re = p.1 := by
    change (Complex.equivRealProdCLM.symm p).re = p.1
    rw [Complex.equivRealProdCLM_symm_apply]
    simp
  have him (p : ℝ × ℝ) : (e.symm p).im = p.2 := by
    change (Complex.equivRealProdCLM.symm p).im = p.2
    rw [Complex.equivRealProdCLM_symm_apply]
    simp
  let f : C(unitInterval, ℂ) := (⟨e.symm, e.symm.continuous⟩ : C(ℝ × ℝ, ℂ)).comp (liftedLinkageCurve hG.1 L m)
  let g : C(unitInterval, ℂ) := (⟨e.symm, e.symm.continuous⟩ : C(ℝ × ℝ, ℂ)).comp (liftedLinkageCurve hG.1 L (m + 1))
  have hf : IsArcMap f := ⟨f.continuous,
    e.symm.injective.comp (isArcMap_liftedLinkageCurve hG.1 L m).2⟩
  have hg : IsArcMap g := ⟨g.continuous,
    e.symm.injective.comp (isArcMap_liftedLinkageCurve hG.1 L (m + 1)).2⟩
  have hfr (t) : (f t).re = (liftedLinkageCurve hG.1 L m t).1 := hre _
  have hgr (t) : (g t).re = (liftedLinkageCurve hG.1 L (m + 1) t).1 := hre _
  have hfi (t) : (f t).im = (liftedLinkageCurve hG.1 L m t).2 := him _
  have hgi (t) : (g t).im = (liftedLinkageCurve hG.1 L (m + 1) t).2 := him _
  have hfp : range f = e.symm '' range (liftedLinkageCurve hG.1 L m) := by
    rw [← range_comp]
    rfl
  have hgp : range g = e.symm '' range (liftedLinkageCurve hG.1 L (m + 1)) := by
    rw [← range_comp]
    rfl
  have hdis : Disjoint (range f) (range g) := by
    rw [hfp, hgp]
    apply disjoint_left.mpr
    rintro z ⟨a, ha, heA⟩ ⟨b, hb, heB⟩
    have hab := e.symm.injective (heA.trans heB.symm)
    exact disjoint_left.mp (disjoint_range_liftedLinkageCurve hG.1 L
      (m := m) (n := m + 1) (by omega)) ha (hab.symm ▸ hb)
  have hc := hD.image e.symm.continuous.continuousOn e.continuous.continuousOn
    (fun p _ => e.apply_symm_apply p)
  have hside (r a b : ℝ) : e.symm '' (({r} : Set ℝ) ×ˢ Icc a b) =
      ({r} : Set ℝ) ×ℂ Icc a b := by
    rw [e.symm.image_eq_preimage_symm]
    rfl
  have hcb : discBd (e.symm '' D) = range f ∪ range g ∪
      (({1} : Set ℝ) ×ℂ Icc (f 0).im (g 0).im) ∪
      (({2} : Set ℝ) ×ℂ Icc (f 1).im (g 1).im) := by
    rw [hc.2, hDb]
    simp only [liftedStripBoundary, image_union, ← hfp, ← hgp, hside, hfi, hgi]
  have hm := liftedLinkageCurve_props_raw hG.1 L m
  have hn := liftedLinkageCurve_props_raw hG.1 L (m + 1)
  have ho := liftedLinkageCurve_consecutive_ends hG.1 L hθ m
  obtain ⟨F, hiF, hrF, hlF, hhF, hbF, htF⟩ := exists_coordinates_of_proper_strip_arcs
    f g hf hg (by rw [hfr]; exact hm.2.1) (by rw [hgr]; exact hn.2.1)
    (by rw [hfr]; exact hm.2.2.1) (by rw [hgr]; exact hn.2.2.1)
    (fun t ht => by rw [hfr]; exact liftedLinkageCurve_interior_radius L hG m ht)
    (fun t ht => by rw [hgr]; exact liftedLinkageCurve_interior_radius L hG (m + 1) ht)
    hdis (by rw [hfi, hgi]; exact ho.1) (by rw [hfi, hgi]; exact ho.2) hc.1 hcb
  refine ⟨(⟨e, e.continuous⟩ : C(ℂ, ℝ × ℝ)).comp F, e.injective.comp hiF, ?_, ?_, ?_, ?_, ?_⟩
  · change range (e ∘ F) = D
    rw [range_comp, hrF, image_image]
    simp only [e.apply_symm_apply, image_id']
  · intro t
    change e (F (0, t)) = _
    rw [hlF]
    exact e.apply_symm_apply _
  · intro t
    change e (F (1, t)) = _
    rw [hhF]
    exact e.apply_symm_apply _
  · intro u
    change e (F (u, 0)) = _
    rw [hbF]
    change (1, (1 - u.1) * (f 0).im + u.1 * (g 0).im) = _
    rw [hfi, hgi]
  · intro u
    change e (F (u, 1)) = _
    rw [htF]
    change (2, (1 - u.1) * (f 1).im + u.1 * (g 1).im) = _
    rw [hfi, hgi]

end GraphMinor.GM06
