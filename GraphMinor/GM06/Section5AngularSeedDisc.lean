module

public import GraphMinor.Surface.DiscGrow
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import GraphMinor.Surface.PolyMoves
import GraphMinor.GM06.Section5RadialCircleExtension

/-!
# Discs following a chosen angular interval

The local enclosure in VI (5.5), page 130, starts with a disc whose
boundary passes through the attachment. Extend angular coordinates
radially and apply them to a half-disc. Strictly positive radial and
angular coordinates give interior points, while the origin remains
on the boundary.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- A change of angular coordinates gives a seed disc with the origin
on its boundary. Its radial membership and interior membership retain
the chosen circle coordinates. -/
theorem exists_angular_seed_disc (h : Circle ≃ₜ Circle) :
    ∃ D : Set ℂ, IsClosedDisc D ∧ 0 ∈ discBd D ∧
      (∀ z ∈ D, ‖z‖ ≤ 1) ∧
      (∀ (r : ℝ), 0 < r → r ≤ 1 → ∀ w : Circle,
        (r : ℂ) * h w ∈ D ↔ 0 ≤ (w : ℂ).im) ∧
      (∀ (r : ℝ), 0 < r → r < 1 → ∀ w : Circle,
        0 < (w : ℂ).im → (r : ℂ) * h w ∈ discInt D) := by
  obtain ⟨R, hR0, hRn, hRray⟩ := exists_radial_circle_homeomorph h
  obtain ⟨hhalf, hbd⟩ := isClosedDisc_halfD (σ := 1) one_ne_zero
  have him := hhalf.image R.continuous.continuousOn R.symm.continuous.continuousOn
    (fun z _ => R.symm_apply_apply z)
  refine ⟨R '' halfD 1, him.1, ?_, ?_, ?_, ?_⟩
  · rw [him.2]
    exact ⟨0, by rw [hbd]; right; simp, hR0⟩
  · rintro z ⟨x, hx, rfl⟩
    rw [hRn]
    exact hx.1
  · intro r hr hr1 w
    rw [← hRray r hr.le w]
    constructor
    · rintro ⟨z, hz, he⟩
      have heq := R.injective he
      rw [heq] at hz
      have hsign : 0 ≤ r * (w : ℂ).im := by simpa [halfD] using hz.2
      exact (mul_nonneg_iff_of_pos_left hr).mp hsign
    · intro hw
      refine ⟨(r : ℂ) * w, ?_, rfl⟩
      constructor
      · simpa [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le] using hr1
      · simpa using mul_nonneg hr.le hw
  · intro r hr hr1 w hw
    rw [← hRray r hr.le w]
    have hn : ‖(r : ℂ) * w‖ = r := by
      simp [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]
    have hi : ((r : ℂ) * (w : ℂ)).im = r * (w : ℂ).im := by simp
    have hx : (r : ℂ) * (w : ℂ) ∈ halfD 1 := by
      refine ⟨?_, ?_⟩
      · rw [hn]; exact hr1.le
      · simpa [hi] using (mul_pos hr hw).le
    refine ⟨⟨_, hx, rfl⟩, ?_⟩
    rw [him.2]
    rintro ⟨z, hz, he⟩
    have heq := R.injective he
    rw [heq, hbd] at hz
    rcases hz with hz | hz
    · exact hr1.ne (hn.symm.trans hz.1)
    · exact (mul_pos hr hw).ne' (hi.symm.trans hz.2)

end GraphMinor.GM06
