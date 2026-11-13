module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5CoverCuffVertices
import GraphMinor.GM06.Section5CoverStripDiscSheet
import GraphMinor.GM06.Section5StripCuffs

/-!
# The chosen lifted strip on the initial cuff

For the orientation test in VI (5.7), page 133, the selected
cover strip meets the initial cuff in the open angular interval
between its two initial vertices. The lifted disc gives the closed
interval bound. Its ends are linkage points, so they are excluded.
Conversely, the open interval is connected, misses all integral
initial angles, and contains the strip's defining gap point.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

/-- On the initial cuff, each cover strip is exactly the open interval
between its two indexed initial angles, also for one linkage path. -/
theorem mem_cover_strip_on_initial_cuff_iff
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) (m : ℤ) (p : CylinderCover) (hp1 : p.1.1 = 1) :
    p ∈ cylinderCoverStrip L m ↔
      p.2 ∈ Ioo (2 * (m : ℝ) * π / k) (2 * ((m + 1 : ℤ) : ℝ) * π / k) := by
  let s : ℝ := 2 * π / k
  have hs : 0 < s := div_pos (mul_pos (by norm_num) pi_pos) (Nat.cast_pos.mpr hG.1)
  have heq (z : ℤ) : 2 * (z : ℝ) * π / k = s * (z : ℝ) := by dsimp [s]; ring
  constructor
  · intro hp
    have hpOff : cylinderCoverProjection p ∉ ⋃ j, (L.pathDrawing j).U :=
      (connectedComponentIn_subset _ _ hp).2
    obtain ⟨D, hD, hBd, hstrip, hsheet⟩ := exists_cover_strip_disc_sheet L hG hθ m
    have hpK := (hsheet ▸ hp).1
    obtain ⟨x, hx, hxp⟩ := hpK
    have hcoord : cylinderCoverCoordinates p = x := by
      rw [← hxp]
      apply Prod.ext
      · change max 1 (min 2 x.1) = x.1
        rw [min_eq_right (hstrip hx).2, max_eq_right (hstrip hx).1]
      · rfl
    have hpD : cylinderCoverCoordinates p ∈ D := hcoord.symm ▸ hx
    have hb := stripDisc_radius_one_mem_interval L hG hθ m hD hBd hstrip hpD hp1
    rw [(liftedLinkageCurve_props_raw hG.1 L m).2.2.2.1,
      (liftedLinkageCurve_props_raw hG.1 L (m + 1)).2.2.2.1] at hb
    have hne (z : ℤ) : p.2 ≠ 2 * (z : ℝ) * π / k := fun hh =>
      hpOff ((cover_initial_cuff_mem_linkage_iff_integer_angle L hG p hp1).mpr ⟨z, hh⟩)
    exact ⟨lt_of_le_of_ne hb.1 (hne m).symm, lt_of_le_of_ne hb.2 (hne (m + 1))⟩
  · intro hpint
    let f : ℝ → CylinderCover := fun a => (⟨1, by norm_num⟩, a)
    have hfc : Continuous f := by fun_prop
    let a := 2 * (m : ℝ) * π / k
    let b := 2 * ((m + 1 : ℤ) : ℝ) * π / k
    have hgap : a < b := by
      change 2 * (m : ℝ) * π / k < 2 * ((m + 1 : ℤ) : ℝ) * π / k
      rw [heq, heq, Int.cast_add, Int.cast_one]
      exact (mul_lt_mul_iff_right₀ hs).mpr (lt_add_one _)
    have hmid : (2 * (m : ℝ) + 1) * π / k = (a + b) / 2 := by
      dsimp [a, b]
      push_cast
      ring
    have hseed : (2 * (m : ℝ) + 1) * π / k ∈ Ioo a b := by
      rw [hmid]
      constructor <;> linarith only [hgap]
    have hsub : f '' Ioo a b ⊆ cylinderCoverProjection ⁻¹'
        (univ \ ⋃ j, (L.pathDrawing j).U) := by
      rintro _ ⟨u, hu, rfl⟩
      refine ⟨mem_univ _, ?_⟩
      intro hh
      obtain ⟨n, hn⟩ := (cover_initial_cuff_mem_linkage_iff_integer_angle L hG (f u) rfl).mp hh
      change u = 2 * (n : ℝ) * π / k at hn
      have hmn : (m : ℝ) < (n : ℝ) := by
        apply (mul_lt_mul_iff_right₀ hs).mp
        simpa only [a, heq, hn] using hu.1
      have hnm : (n : ℝ) < ((m + 1 : ℤ) : ℝ) := by
        apply (mul_lt_mul_iff_right₀ hs).mp
        simpa only [b, heq, hn] using hu.2
      have hmnZ : m < n := by exact_mod_cast hmn
      have hnmZ : n < m + 1 := by exact_mod_cast hnm
      omega
    have hpimage : p ∈ f '' Ioo a b :=
      ⟨p.2, hpint, Prod.ext (Subtype.ext hp1.symm) rfl⟩
    exact (isPreconnected_Ioo.image f hfc.continuousOn).subset_connectedComponentIn
      ⟨_, hseed, rfl⟩ hsub hpimage

end GraphMinor.GM06
