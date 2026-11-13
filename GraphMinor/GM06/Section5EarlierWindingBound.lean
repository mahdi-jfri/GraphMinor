module

public import GraphMinor.GM06.Section5CoverInitialCrossings
import GraphMinor.GM06.Section4Winding

/-!
# The earlier-prefix winding bound

In the one-path case of VI (5.5), page 132, the auxiliary return
ends above the following dual point at angle five pi. If its winding
is negative, count the linkage lifts with indices from three up to
the initial gap index. All these crossings occur before the return
strip. Their number is exactly the negative winding. If the winding
is nonnegative the required lower bound follows from nonnegativity
of the count.
-/

public section
namespace GraphMinor.GM06
open Set Real GraphMinor.Surface

/-- The one-path earlier-prefix bound in VI (5.5), page 132, for
the actual auxiliary cover curve with its prescribed-side return. -/
theorem negative_winding_le_earlier_hits_of_return_strip
    {G H : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    (hPH : ∀ i, (L.pathDrawing i).U ⊆ H.U)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (f : Curve ClosedCylinder) (hf : IsNormalCurve H f)
    (hfin : (curveVertexHits H f).Finite)
    (B : C(unitInterval, CylinderCover)) (hBproj : ∀ t, cylinderCoverProjection (B t) = f t)
    (hB0 : (B 0).1.1 = 1) (hB1 : (B 1).1.1 = 1)
    (τ : unitInterval)
    (hReturn : ∀ t, τ ≤ t → cylinderCoverCoordinates (B t) ∈
      D ∪ ({1} ×ˢ Icc (4 * π) (5 * π)))
    (m₀ : ℤ) (hangle0 : (B 0).2 = (2 * (m₀ : ℝ) + 1) * π)
    (hangle1 : (B 1).2 = 5 * π) :
    -windingNumber f ≤ ((curveVertexHits H f ∩ Iio τ).ncard : ℝ) := by
  let A : C(unitInterval, ℝ) := ⟨fun t => (B t).2, continuous_snd.comp B.continuous⟩
  have hA (t : unitInterval) : Circle.exp (A t) = (f t).1.2 :=
    congrArg (fun x : ClosedCylinder => x.1.2) (hBproj t)
  have hwind : windingNumber f = 2 - (m₀ : ℝ) := by
    rw [windingNumber_eq_of_exp_lift A hA]
    change ((B 1).2 - (B 0).2) / (2 * π) = _
    rw [hangle1, hangle0]
    field_simp [pi_ne_zero]
    ring
  by_cases hm0 : m₀ ≤ 2
  · have hmR : (m₀ : ℝ) ≤ 2 := by exact_mod_cast hm0
    have hn : (0 : ℝ) ≤ (curveVertexHits H f ∩ Iio τ).ncard := Nat.cast_nonneg _
    rw [hwind]
    linarith only [hmR, hn]
  · have hm3 : 3 ≤ m₀ := by omega
    let T := Finset.Icc (3 : ℤ) m₀
    have hT : ∀ m ∈ T, 3 ≤ m := by
      intro m hm
      exact (Finset.mem_Icc.mp hm).1
    have hbetween : ∀ m ∈ T,
        ((B 0).2 < 2 * (m : ℝ) * π / 1 ∧ 2 * (m : ℝ) * π / 1 < (B 1).2) ∨
        ((B 1).2 < 2 * (m : ℝ) * π / 1 ∧ 2 * (m : ℝ) * π / 1 < (B 0).2) := by
      intro m hm
      have hlo : (3 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
      have hhi : (m : ℝ) ≤ m₀ := by exact_mod_cast (Finset.mem_Icc.mp hm).2
      rw [hangle0, hangle1, div_one]
      exact Or.inr ⟨by nlinarith only [hlo, pi_pos], by nlinarith only [hhi, pi_pos]⟩
    have hcount := card_cover_initial_crossings_le_earlier_hits L hG hθ hPH hD hBd hstrip
      f hf hfin B hBproj hB0 hB1 τ hReturn T hT hbetween
    have hcardZ : (T.card : ℤ) = m₀ - 2 := by
      dsimp [T]
      rw [Int.card_Icc]
      omega
    have hcardR : (T.card : ℝ) = (m₀ : ℝ) - 2 := by exact_mod_cast hcardZ
    have hcountR : (T.card : ℝ) ≤ (curveVertexHits H f ∩ Iio τ).ncard := Nat.cast_le.mpr hcount
    rw [hwind]
    linarith only [hcardR, hcountR]

/-- The earlier-prefix inequality of VI (5.5), page 132, for any
path count and indexed return strip. The right side counts actual
vertex times before the return, and the left side is −k times the
auxiliary winding. -/
theorem negative_scaled_winding_le_earlier_hits_of_return_strip
    {k : ℕ} {G H : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ)
    (hPH : ∀ i, (L.pathDrawing i).U ⊆ H.U) (m : ℤ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L m)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (f : Curve ClosedCylinder) (hf : IsNormalCurve H f)
    (hfin : (curveVertexHits H f).Finite)
    (B : C(unitInterval, CylinderCover)) (hBproj : ∀ t, cylinderCoverProjection (B t) = f t)
    (hB0 : (B 0).1.1 = 1) (hB1 : (B 1).1.1 = 1)
    (τ : unitInterval)
    (hReturn : ∀ t, τ ≤ t → cylinderCoverCoordinates (B t) ∈
      D ∪ ({1} ×ˢ Icc (2 * ((m : ℝ) + 1) * π / k)
        ((2 * ((m : ℝ) + 1) + 1) * π / k)))
    (m₀ : ℤ) (hangle0 : (B 0).2 = (2 * (m₀ : ℝ) + 1) * π / k)
    (hangle1 : (B 1).2 = (2 * ((m : ℝ) + 1) + 1) * π / k) :
    -((k : ℝ) * windingNumber f) ≤ ((curveVertexHits H f ∩ Iio τ).ncard : ℝ) := by
  let A : C(unitInterval, ℝ) := ⟨fun t => (B t).2, continuous_snd.comp B.continuous⟩
  have hA (t : unitInterval) : Circle.exp (A t) = (f t).1.2 :=
    congrArg (fun x : ClosedCylinder => x.1.2) (hBproj t)
  have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hG.1.ne'
  have hwind : (k : ℝ) * windingNumber f = (m : ℝ) + 1 - (m₀ : ℝ) := by
    rw [windingNumber_eq_of_exp_lift A hA]
    change (k : ℝ) * (((B 1).2 - (B 0).2) / (2 * π)) = _
    rw [hangle1, hangle0]
    field_simp [hkne, pi_ne_zero]
    ring
  by_cases hm0 : m₀ ≤ m + 1
  · have hmR : (m₀ : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hm0
    have hn : (0 : ℝ) ≤ (curveVertexHits H f ∩ Iio τ).ncard := Nat.cast_nonneg _
    rw [hwind]
    linarith only [hmR, hn]
  · have hm2 : m + 2 ≤ m₀ := by omega
    let T := Finset.Icc (m + 2) m₀
    have hT : ∀ n ∈ T, m + 2 ≤ n := by
      intro n hn
      exact (Finset.mem_Icc.mp hn).1
    have hscale : (0 : ℝ) < π / k := div_pos pi_pos (Nat.cast_pos.mpr hG.1)
    have hbetween : ∀ n ∈ T,
        ((B 0).2 < 2 * (n : ℝ) * π / k ∧ 2 * (n : ℝ) * π / k < (B 1).2) ∨
        ((B 1).2 < 2 * (n : ℝ) * π / k ∧ 2 * (n : ℝ) * π / k < (B 0).2) := by
      intro n hn
      have hlo : (m : ℝ) + 2 ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hhi : (n : ℝ) ≤ m₀ := by exact_mod_cast (Finset.mem_Icc.mp hn).2
      rw [hangle0, hangle1]
      simp only [mul_div_assoc]
      exact Or.inr ⟨by nlinarith only [hlo, hscale], by nlinarith only [hhi, hscale]⟩
    have hcount := card_cover_initial_crossings_le_earlier_hits_general L hG hθ hPH m hD hBd hstrip
      f hf hfin B hBproj hB0 hB1 τ hReturn T hT hbetween
    have hcardZ : (T.card : ℤ) = m₀ - m - 1 := by
      dsimp [T]
      rw [Int.card_Icc]
      omega
    have hcardR : (T.card : ℝ) = (m₀ : ℝ) - m - 1 := by exact_mod_cast hcardZ
    have hcountR : (T.card : ℝ) ≤ (curveVertexHits H f ∩ Iio τ).ncard := Nat.cast_le.mpr hcount
    rw [hwind]
    linarith only [hcardR, hcountR]

end GraphMinor.GM06
