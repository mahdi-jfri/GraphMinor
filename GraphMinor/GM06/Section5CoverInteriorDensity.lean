module

public import GraphMinor.GM06.Defs

/-!
# Every open cover neighbourhood meets the strict radial interior

The local side argument for VI (5.7), page 133, needs a point off
the cuffs, even when its starting neighbourhood meets a cuff.
Move the radial coordinate a positive amount toward the middle
radius while keeping the angle fixed. Continuity keeps a small
part of this curve in the neighbourhood, and every positive part
of the curve has radius strictly between the two cuff radii.
-/

public section
namespace GraphMinor.GM06
open Set Topology unitInterval

/-- Every nonempty open subset of the angular cover has a point
whose radius is strictly between the two cuff radii. -/
theorem exists_strict_radius_point_in_open_cover
    {O : Set CylinderCover} (hOo : IsOpen O) (hOne : O.Nonempty) :
    ∃ p ∈ O, 1 < p.1.1 ∧ p.1.1 < 2 := by
  obtain ⟨p, hpO⟩ := hOne
  have hbounds (t : I) :
      1 ≤ (1 - (t : ℝ)) * p.1.1 + (t : ℝ) * (3 / 2) ∧
      (1 - (t : ℝ)) * p.1.1 + (t : ℝ) * (3 / 2) ≤ 2 := by
    have h₁ := mul_nonneg (sub_nonneg.mpr t.2.2) (sub_nonneg.mpr p.1.2.1)
    have h₂ := mul_nonneg (sub_nonneg.mpr t.2.2) (sub_nonneg.mpr p.1.2.2)
    have ht := t.2.1
    constructor <;> nlinarith only [h₁, h₂, ht]
  let q : C(I, CylinderCover) :=
    ⟨fun t => (⟨(1 - (t : ℝ)) * p.1.1 + (t : ℝ) * (3 / 2), hbounds t⟩, p.2), by fun_prop⟩
  have hq0 : q 0 = p := by
    apply Prod.ext
    · apply Subtype.ext
      simp [q]
    · rfl
  have hpre : IsOpen (q ⁻¹' O) := hOo.preimage q.continuous
  have h0pre : (0 : I) ∈ q ⁻¹' O := by
    change q 0 ∈ O
    rw [hq0]
    exact hpO
  have h0cl : (0 : I) ∈ closure (Ioo (0 : I) 1) := by
    rw [closure_Ioo (zero_ne_one : (0 : I) ≠ 1)]
    exact ⟨le_rfl, zero_le_one⟩
  obtain ⟨t, htO, ht⟩ := mem_closure_iff.mp h0cl _ hpre h0pre
  have h₁ := mul_nonneg (sub_nonneg.mpr t.2.2) (sub_nonneg.mpr p.1.2.1)
  have h₂ := mul_nonneg (sub_nonneg.mpr t.2.2) (sub_nonneg.mpr p.1.2.2)
  have htpos : (0 : ℝ) < t := ht.1
  refine ⟨q t, htO, ?_, ?_⟩
  · change 1 < (1 - (t : ℝ)) * p.1.1 + (t : ℝ) * (3 / 2)
    nlinarith only [h₁, htpos]
  · change (1 - (t : ℝ)) * p.1.1 + (t : ℝ) * (3 / 2) < 2
    nlinarith only [h₂, htpos]

end GraphMinor.GM06
