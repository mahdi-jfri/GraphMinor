module

public import GraphMinor.GM06.Section5LinkageStripCircle
public import GraphMinor.Surface.DiscGrow
import GraphMinor.GM06.Section5DiscCoordinates
import GraphMinor.Surface.PlaneDisc
import Mathlib.Analysis.Complex.Basic

/-!
# The disc bounded by a lifted linkage strip

In the strip argument of VI (5.1), page 129, the circle made from two
consecutive lifted paths bounds a closed disc. Schoenflies supplies
the disc in complex coordinates. Bounds on its boundary's real
coordinate hold on the whole disc, so the disc stays in the radial
strip. Mapping back gives the planar disc between the linkage lifts.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface

/-- A circle contained in a closed radial strip bounds a closed disc
contained in that strip. -/
theorem exists_closedDisc_in_radial_strip_of_isOArc
    {B : Set (ℝ × ℝ)} (hB : IsOArc B)
    (hstrip : B ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) :
    ∃ D : Set (ℝ × ℝ), IsClosedDisc D ∧ discBd D = B ∧
      D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2} := by
  let e : ℂ ≃ₜ ℝ × ℝ := Complex.equivRealProdCLM.toHomeomorph
  let C := e.symm '' B
  have hC : IsOArc C := hB.image e.symm.continuous.continuousOn e.continuous.continuousOn
    (fun p _ => e.apply_symm_apply p)
  obtain ⟨hD, hDb⟩ := isClosedDisc_closedInner hC
  have hbound : ∀ z ∈ discBd (closedInner C), 1 ≤ z.re ∧ z.re ≤ 2 := by
    intro z hz
    rw [hDb] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    have he : (e.symm p).re = p.1 := by
      change (Complex.equivRealProdCLM.symm p).re = p.1
      rw [Complex.equivRealProdCLM_symm_apply]
      simp
    rw [he]
    exact hstrip hp
  have hDstrip := re_bounds_of_discBd_bounds hD hbound
  have hback := hD.image e.continuous.continuousOn e.symm.continuous.continuousOn
    (fun z _ => e.symm_apply_apply z)
  have him : e '' C = B := by
    change e '' (e.symm '' B) = B
    rw [image_image]
    exact (image_congr (fun p _ => e.apply_symm_apply p)).trans (image_id' B)
  refine ⟨e '' closedInner C, hback.1, ?_, ?_⟩
  · rw [hback.2, hDb, him]
  · rintro p ⟨z, hz, rfl⟩
    exact hDstrip z hz

/-- The interior of a disc contained between the cuff lines misses
both lines. Equality would be an interior coordinate extremum. -/
theorem discInt_subset_open_radial_strip
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) :
    discInt D ⊆ {p : ℝ × ℝ | 1 < p.1 ∧ p.1 < 2} := by
  let e : ℂ ≃ₜ ℝ × ℝ := Complex.equivRealProdCLM.toHomeomorph
  have him := hD.image e.symm.continuous.continuousOn e.continuous.continuousOn
    (fun p _ => e.apply_symm_apply p)
  have hre (p : ℝ × ℝ) : (e.symm p).re = p.1 := by
    change (Complex.equivRealProdCLM.symm p).re = p.1
    rw [Complex.equivRealProdCLM_symm_apply]
    simp
  have hb : ∀ z ∈ e.symm '' D, 1 ≤ z.re ∧ z.re ≤ 2 := by
    rintro z ⟨p, hp, rfl⟩
    rw [hre]
    exact hstrip hp
  intro p hp
  have hz : e.symm p ∈ discInt (e.symm '' D) := by
    refine ⟨mem_image_of_mem e.symm hp.1, ?_⟩
    rw [him.2]
    rintro ⟨q, hq, heq⟩
    exact hp.2 ((e.symm.injective heq) ▸ hq)
  change 1 < p.1 ∧ p.1 < 2
  simpa only [hre] using re_strict_bounds_of_discInt him.1 hb (e.symm p) hz

/-- The four pieces bounding consecutive linkage lifts enclose a
closed disc within the radial strip, as used for VI (5.1). -/
theorem exists_closedDisc_of_liftedStripBoundary
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) (m : ℤ) :
    ∃ D : Set (ℝ × ℝ), IsClosedDisc D ∧ discBd D = liftedStripBoundary hG.1 L m ∧
      D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2} :=
  exists_closedDisc_in_radial_strip_of_isOArc (isOArc_liftedStripBoundary L hG hθ m)
    (liftedStripBoundary_subset_radial_strip hG.1 L m)

end GraphMinor.GM06
