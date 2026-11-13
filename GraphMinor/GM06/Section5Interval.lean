module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5TightHelix
import GraphMinor.GM06.Section5

/-!
# Feasible winding numbers form an interval

The proof of Graph Minors VI (5.8) combines the helix bound (5.2) with (5.3).
The proof of (5.9) then advances through the integer multiples of `1 / k`.
The hypothesis (5.3) supplies a tight helix at a failed next winding number.
-/

public section

namespace GraphMinor.GM06

open GraphMinor.Surface

/-- Graph Minors VI, (5.8), page 133, from (5.3):
"If $\theta$ is feasible in $G$, the following are equivalent:"
The three conditions are a tight helix, failure of the next winding number,
and failure of every larger winding number. -/
theorem theorem_5_8_proof : Statement58 := by
  intro k G θ hG hθ
  have hpos : 0 < 1 / (k : ℝ) := div_pos zero_lt_one (Nat.cast_pos.mpr hG.1)
  refine ⟨⟨?_, theorem_5_3_proof k G θ hG hθ⟩, ⟨?_, ?_⟩⟩
  · intro hf
    exact (theorem_5_8_of_helix k G θ hG hf).2
  · intro hnext
    exact (theorem_5_8_of_helix k G θ hG (theorem_5_3_proof k G θ hG hθ hnext)).1
  · intro hnone
    exact hnone (θ + 1 / (k : ℝ)) (lt_add_of_pos_right θ hpos)

private theorem feasible_add_steps (k : ℕ)
    (G : Drawing ClosedCylinder) (a b : ℝ) (hG : IsCylinderSection5Drawing k G)
    (ha : IsThetaFeasible k G a) (hb : IsThetaFeasible k G b) :
    ∀ n : ℕ, a + (n : ℝ) / k ≤ b → IsThetaFeasible k G (a + (n : ℝ) / k) := by
  intro n
  induction n with
  | zero => simpa using fun (_ : a + (0 : ℝ) / k ≤ b) => ha
  | succ n ih =>
    intro hbound
    have hk : (0 : ℝ) < k := Nat.cast_pos.mpr hG.1
    have hstep : a + ((n + 1 : ℕ) : ℝ) / k =
        (a + (n : ℝ) / k) + 1 / k := by push_cast; ring
    have hlt : a + (n : ℝ) / k < b := by
      rw [hstep] at hbound
      exact lt_of_lt_of_le (lt_add_of_pos_right _ (div_pos zero_lt_one hk)) hbound
    have hcurrent := ih (le_of_lt hlt)
    rw [hstep]
    by_contra hnext
    exact ((theorem_5_8_proof k G _ hG hcurrent).2.mp hnext) b hlt hb

/-- Graph Minors VI, (5.9), page 134, from (5.3) through (5.8):
"If $\theta_1 \le \theta_2 \le \theta_3$ and $\theta_1, \theta_3$ are feasible in $G$ and $k\theta_2$
is an integer, then $\theta_2$ is feasible in $G$."
The integer gap from the first winding number counts the applications of (5.8). -/
theorem theorem_5_9_proof : Statement59 := by
  intro k G a c b hG hac hcb ha hb hc
  obtain ⟨ma, hma⟩ := linkage_winding_int hG.1 ha
  obtain ⟨mc, hmc⟩ := hc
  have hk : (0 : ℝ) < k := Nat.cast_pos.mpr hG.1
  have hgap : 0 ≤ mc - ma := by
    have hle : (ma : ℝ) ≤ mc := by
      rw [← hma, ← hmc]
      exact mul_le_mul_of_nonneg_left hac hk.le
    exact sub_nonneg.mpr (Int.cast_le.mp hle)
  have hcast : ((mc - ma).toNat : ℝ) = (mc : ℝ) - ma := by
    have hz : ((mc - ma).toNat : ℤ) = mc - ma := Int.toNat_of_nonneg hgap
    exact_mod_cast hz
  have heq : a + ((mc - ma).toNat : ℝ) / k = c := by
    rw [hcast]
    apply (mul_right_cancel₀ (ne_of_gt hk))
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hk)]
    nlinarith [hma, hmc]
  have h := feasible_add_steps k G a b hG ha hb (mc - ma).toNat
  rw [heq] at h
  exact h hcb

end GraphMinor.GM06
