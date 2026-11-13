module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5
import Mathlib.Data.Int.LeastGreatest

/-!
# Extreme feasible winding numbers

Graph Minors VI (5.10), page 134, chooses a greatest and a least feasible winding
number from an existing linkage. The integer condition and the bound (5.12)
justify this choice: the feasible integer multiples of `k` form a bounded,
nonempty set of integers.
-/

public section

namespace GraphMinor.GM06

open GraphMinor.Surface

/-- The choice of extreme feasible winding numbers in the proof of Graph Minors VI
(5.10), page 134: "let $\theta_1$ be maximum and $\theta_2$ minimum such that
$\theta_1, \theta_2$ are feasible. (This is possible by (ii).)"
The bound (5.12) and integrality make both extrema attained. -/
theorem exists_min_max_feasible (k : ℕ) (G : Drawing ClosedCylinder)
    (hG : IsCylinderSection5Drawing k G) (hL : Nonempty (CylinderLinkage k G)) :
    ∃ lo hi : ℝ, IsThetaFeasible k G lo ∧ IsThetaFeasible k G hi ∧
      ∀ θ : ℝ, IsThetaFeasible k G θ → lo ≤ θ ∧ θ ≤ hi := by
  obtain ⟨L⟩ := hL
  obtain ⟨a, ha⟩ := L.exists_hasTheta hG.1
  have ha' : IsThetaFeasible k G a := ⟨L, ha⟩
  have hk : (0 : ℝ) < k := Nat.cast_pos.mpr hG.1
  have hk0 := ne_of_gt hk
  let B : ℝ := (1 / ((k : ℝ) ^ 2)) * (G.V.ncard : ℝ)
  have hbound : ∀ θ : ℝ, IsThetaFeasible k G θ → a - B ≤ θ ∧ θ ≤ a + B := by
    intro θ hθ
    have h := theorem_5_12_proof k G θ a hG hθ ha'
    exact ⟨by linarith [(abs_le.mp h).1], by linarith [(abs_le.mp h).2]⟩
  let P : ℤ → Prop := fun m => IsThetaFeasible k G ((m : ℝ) / k)
  have hnonempty : ∃ m : ℤ, P m := by
    obtain ⟨m, hm⟩ := linkage_winding_int hG.1 ha'
    refine ⟨m, ?_⟩
    change IsThetaFeasible k G ((m : ℝ) / k)
    rw [← hm, mul_div_cancel_left₀ _ hk0]
    exact ha'
  obtain ⟨lower, hlower⟩ := exists_int_le ((k : ℝ) * (a - B))
  obtain ⟨upper, hupper⟩ := exists_int_ge ((k : ℝ) * (a + B))
  have hlow : ∃ b : ℤ, ∀ m : ℤ, P m → b ≤ m := by
    refine ⟨lower, ?_⟩
    intro m hm
    suffices h : (lower : ℝ) ≤ (m : ℝ) by exact_mod_cast h
    have h := mul_le_mul_of_nonneg_left (hbound _ hm).1 hk.le
    rw [mul_div_cancel₀ _ hk0] at h
    exact hlower.trans h
  have hupp : ∃ b : ℤ, ∀ m : ℤ, P m → m ≤ b := by
    refine ⟨upper, ?_⟩
    intro m hm
    suffices h : (m : ℝ) ≤ (upper : ℝ) by exact_mod_cast h
    have h := mul_le_mul_of_nonneg_left (hbound _ hm).2 hk.le
    rw [mul_div_cancel₀ _ hk0] at h
    exact h.trans hupper
  obtain ⟨l, hl, hlmin⟩ := Int.exists_least_of_bdd hlow hnonempty
  obtain ⟨u, hu, humax⟩ := Int.exists_greatest_of_bdd hupp hnonempty
  refine ⟨(l : ℝ) / k, (u : ℝ) / k, hl, hu, ?_⟩
  intro θ hθ
  obtain ⟨m, hm⟩ := linkage_winding_int hG.1 hθ
  have heq : (m : ℝ) / k = θ := by rw [← hm, mul_div_cancel_left₀ _ hk0]
  have hmP : P m := by change IsThetaFeasible k G ((m : ℝ) / k); rw [heq]; exact hθ
  rw [← heq]
  exact ⟨div_le_div_of_nonneg_right (Int.cast_le.mpr (hlmin m hmP)) hk.le,
    div_le_div_of_nonneg_right (Int.cast_le.mpr (humax m hmP)) hk.le⟩

end GraphMinor.GM06
