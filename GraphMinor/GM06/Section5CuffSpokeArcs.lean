module

public import GraphMinor.GM06.Section5InitialCuffHalfArcs
public import GraphMinor.GM11.Rotation

/-!
# Cuff edge spokes follow the two fixed half-cuff arcs

The virtual cuff edge from one initial vertex to the next has
angular length 2π/k. Its first half follows the positive half-cuff
arc. The last half of the preceding edge follows the negative
half-cuff arc from the shared vertex. Both statements hold for
k = 1, when the edge is a loop and its two directed ends differ.
These parametrizations identify the cuff markers used by VI (5.7).
-/

public section
namespace GraphMinor.GM06
open Set Real GraphMinor.Surface GraphMinor.GM11 unitInterval

private theorem divided_time_mem_unitInterval {k : ℕ} (hk : 0 < k) (t : I) :
    (t : ℝ) / k ∈ I := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  exact ⟨div_nonneg t.2.1 hkR.le,
    (div_le_iff₀ hkR).mpr (by simpa only [one_mul] using t.2.2.trans hk1)⟩

/-- The spoke at the start of a positive cuff gap lies in the
positive half-cuff arc, also when the gap is the full one-path cuff. -/
theorem positive_cuff_spoke_range_subset {k : ℕ} (hk : 0 < k) (θ : ℝ)
    (f h : I → ClosedCylinder)
    (hf : ∀ t, f t = cylinderPoint 1 (by norm_num) (θ + 2 * π * (t : ℝ) / k))
    (hh : ∀ t, h t = cylinderPoint 1 (by norm_num) (θ + π * (t : ℝ))) :
    range (f ∘ halfPar false) ⊆ range h := by
  rintro _ ⟨t, rfl⟩
  let r : I := ⟨(t : ℝ) / k, divided_time_mem_unitInterval hk t⟩
  refine ⟨r, ?_⟩
  change h r = f (halfPar false t)
  rw [hh, hf]
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change Circle.exp _ = Circle.exp _
    congr 1
    rw [halfPar_coe]
    simp only [Bool.false_eq_true, ite_false]
    dsimp only [r]
    ring

/-- The spoke at the end of the preceding positive cuff gap lies in
the negative half-cuff arc from the shared vertex, including k = 1. -/
theorem negative_cuff_spoke_range_subset {k : ℕ} (hk : 0 < k) (θ : ℝ)
    (f g : I → ClosedCylinder)
    (hf : ∀ t, f t = cylinderPoint 1 (by norm_num)
      (θ - 2 * π / k + 2 * π * (t : ℝ) / k))
    (hg : ∀ t, g t = cylinderPoint 1 (by norm_num) (θ - π * (t : ℝ))) :
    range (f ∘ halfPar true) ⊆ range g := by
  rintro _ ⟨t, rfl⟩
  let r : I := ⟨(t : ℝ) / k, divided_time_mem_unitInterval hk t⟩
  refine ⟨r, ?_⟩
  change g r = f (halfPar true t)
  rw [hg, hf]
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change Circle.exp _ = Circle.exp _
    congr 1
    rw [halfPar_coe]
    simp only [ite_true]
    dsimp only [r]
    ring

end GraphMinor.GM06
