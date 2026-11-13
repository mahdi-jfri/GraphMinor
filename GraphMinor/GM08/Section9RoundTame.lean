module

public import GraphMinor.GM08.Section9Annulus
import GraphMinor.GM08.Section9Tame

/-!
# A finite-crossing replacement of a round ring

For the foundation step of VIII (9.1), replace a round ring in a thin
annulus. Its two arcs stay on opposite sides of the logarithm cut, so the
replacement still encloses the inner ball. Arc erasure keeps the new ring
in the old ring and the fixed curve family. This preserves normality.
-/

public section

namespace GraphMinor.GM08

open Set Surface Topology Complex Metric

local notation "𝕀" => unitInterval

/-- A round ring can be replaced in any prescribed thin annulus by a ring
with finitely many pieces off a fixed finite arc family. The new ring
still surrounds the inner ball and stays in the old ring and that family.
This is the enclosure-preserving step needed to tame rings in VIII (9.1). -/
theorem exists_tame_round_ring (G : List (𝕀 → ℂ)) (hG : ∀ γ ∈ G, IsArcMap γ)
    {α r β ρ : ℝ} (hα : 0 ≤ α) (hαr : α < r) (hr : 0 < r) (hrβ : r < β)
    (hρ : 0 < ρ)
    (hfree : ∀ z ∈ ball (r : ℂ) ρ, ∀ γ ∈ G, z ∉ range γ) :
    ∃ P E : Set ℂ, IsOArc P ∧ FinConn (P \ ⋃ γ ∈ G, range γ) ∧
      P ⊆ sphere 0 r ∪ ⋃ γ ∈ G, range γ ∧ Disjoint P (closedBall 0 α) ∧
      IsClosedDisc E ∧ discBd E = P ∧ closedBall 0 α ⊆ E ∧ E ⊆ ball 0 β := by
  classical
  have hpi := Real.pi_pos
  have hpi3 : 3 < Real.pi := Real.pi_gt_three
  -- the angle
  set τ : ℝ := min 1 (ρ / (2 * r)) with hτdef
  have hτ0 : 0 < τ := lt_min one_pos (by positivity)
  have hτ1 : τ ≤ 1 := min_le_left _ _
  have hτ2 : r * τ < ρ := by
    have h3 : τ ≤ ρ / (2 * r) := min_le_right _ _
    have h4 : r * τ ≤ r * (ρ / (2 * r)) := mul_le_mul_of_nonneg_left h3 (by linarith)
    have h5 : r * (ρ / (2 * r)) = ρ / 2 := by
      field_simp
    linarith
  -- the round circle as two arcs
  obtain ⟨a₀, b₀, hab, ha₀, hb₀, -⟩ := circle_two_arcs' (Circle.exp (-τ)) (θ := 2 * τ)
    ⟨by positivity, by nlinarith⟩
  have hrpos : (0 : ℝ) < r := hr
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hrpos.ne'
  let κ : Circle → ℂ := fun w => (r : ℂ) * w
  have hκc : Continuous κ := by fun_prop
  have hκi : Function.Injective κ := fun w w' he =>
    Circle.ext (mul_left_cancel₀ hrc he)
  have hκn : ∀ w, ‖κ w‖ = r := fun w => by
    simp [κ, abs_of_pos hrpos]
  let Ω₀ : Set ℂ := {z | α < ‖z‖ ∧ ‖z‖ < β}
  have hΩ₀ : IsOpen Ω₀ := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  have hΩ₀b : Ω₀ ⊆ ball 0 β := fun z hz => mem_ball_zero_iff.mpr hz.2
  have hκΩ : ∀ w, κ w ∈ Ω₀ := fun w => ⟨by rw [hκn]; exact hαr, by rw [hκn]; exact hrβ⟩
  have hκb : ∀ w, κ w ∈ ball (0 : ℂ) β := fun w => hΩ₀b (hκΩ w)
  have hslit : ∀ w : Circle, (w : ℂ) ≠ -1 → κ w ∈ Complex.slitPlane := fun w hw => by
    have h1 := circle_mem_slitPlane hw
    rw [Complex.mem_slitPlane_iff] at h1 ⊢
    simp only [κ, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, add_zero]
    rcases h1 with h1 | h1
    · exact .inl (mul_pos hrpos h1)
    · exact .inr (mul_ne_zero hrpos.ne' h1)
  have hslit' : ∀ w : Circle, (w : ℂ) ≠ 1 → -κ w ∈ Complex.slitPlane := fun w hw => by
    have h1 : -κ w = κ (-w) := by
      simp [κ]
    rw [h1]
    refine hslit (-w) fun h => hw ?_
    simpa using h
  have ha₀ne : ∀ s, (a₀ s : ℂ) ≠ -1 := fun s he => by
    have h1 : a₀ s = Circle.exp Real.pi := Circle.ext (by simpa using he)
    rw [ha₀, ← Circle.exp_add] at h1
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h1
    have hs0 := s.2.1
    have hs1 := s.2.2
    have h2 : -τ ≤ -τ + s.1 * (2 * τ) := by nlinarith
    have h3 : -τ + s.1 * (2 * τ) ≤ τ := by nlinarith
    rcases le_or_gt 0 m with h | h
    · have h4 : (0 : ℝ) ≤ m := by exact_mod_cast h
      nlinarith
    · have h4 : (m : ℝ) ≤ -1 := by exact_mod_cast (by omega : m ≤ -1)
      nlinarith
  have hb₀ne : ∀ s, (b₀ s : ℂ) ≠ 1 := fun s he => by
    have h1 : b₀ s = Circle.exp 0 := Circle.ext (by simpa using he)
    rw [hb₀, ← Circle.exp_add] at h1
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h1
    have hs0 := s.2.1
    have hs1 := s.2.2
    have hτ3 : 2 * τ ≤ 2 := by linarith
    have hlow : 2 * τ ≤ 2 * Real.pi - s.1 * (2 * Real.pi - 2 * τ) := by nlinarith
    have hup : 2 * Real.pi - s.1 * (2 * Real.pi - 2 * τ) ≤ 2 * Real.pi := by nlinarith
    rcases le_or_gt m 0 with h | h
    · have h4 : (m : ℝ) ≤ 0 := by exact_mod_cast h
      nlinarith
    · have h4 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
      nlinarith
  let a : 𝕀 → ℂ := fun s => κ (a₀ s)
  let b : 𝕀 → ℂ := fun s => κ (b₀ s)
  have ha : IsArcMap a := ⟨hκc.comp hab.1.1, hκi.comp hab.1.2⟩
  have hb : IsArcMap b := ⟨hκc.comp hab.2.1, hκi.comp hab.2.2⟩
  have hp0 : a 0 = (r : ℂ) * Complex.exp (-τ * Complex.I) := by
    simp only [a, κ, ha₀, Set.Icc.coe_zero, zero_mul, ← Circle.exp_add, Circle.coe_exp]
    congr 2
    push_cast
    ring
  have hq0 : a 1 = (r : ℂ) * Complex.exp (τ * Complex.I) := by
    simp only [a, κ, ha₀, Set.Icc.coe_one, one_mul, ← Circle.exp_add, Circle.coe_exp]
    congr 2
    push_cast
    ring
  have hnear : ∀ θ : ℝ, |θ| ≤ τ → (r : ℂ) * Complex.exp (θ * Complex.I) ∈ ball (r : ℂ) ρ := by
    intro θ hθ
    rw [mem_ball, dist_eq_norm]
    have h1 : (r : ℂ) * Complex.exp (θ * Complex.I) - r = r * (Complex.exp (θ * Complex.I) - 1) := by
      ring
    rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
    have h2 : ‖Complex.exp (θ * Complex.I) - 1‖ ≤ ‖θ‖ := by
      have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ)
      rwa [mul_comm] at this
    rw [Real.norm_eq_abs] at h2
    calc r * ‖Complex.exp (θ * Complex.I) - 1‖ ≤ r * τ :=
      mul_le_mul_of_nonneg_left (h2.trans hθ) hrpos.le
      _ < ρ := hτ2
  have hpG : ∀ γ ∈ G, a 0 ∉ range γ := fun γ hγ => by
    rw [hp0]
    exact hfree _ (by simpa using hnear (-τ) (by rw [abs_neg, abs_of_pos hτ0])) γ hγ
  have hqG : ∀ γ ∈ G, a 1 ∉ range γ := fun γ hγ => by
    rw [hq0]
    exact hfree _ (hnear τ (by rw [abs_of_pos hτ0])) γ hγ
  let Na : Set ℂ := Ω₀ ∩ Complex.slitPlane
  let Nb : Set ℂ := Ω₀ ∩ (fun z => -z) ⁻¹' Complex.slitPlane
  have hNa : IsOpen Na := hΩ₀.inter Complex.isOpen_slitPlane
  have hNb : IsOpen Nb := hΩ₀.inter (Complex.isOpen_slitPlane.preimage continuous_neg)
  have haN : range a ⊆ Na := by
    rintro _ ⟨s, rfl⟩
    exact ⟨hκΩ _, hslit _ (ha₀ne s)⟩
  have hbN : range b ⊆ Nb := by
    rintro _ ⟨s, rfl⟩
    exact ⟨hκΩ _, hslit' _ (hb₀ne s)⟩
  obtain ⟨ε₁, hε₁, hth₁⟩ := (isCompact_range ha.1).exists_thickening_subset_open hNa haN
  obtain ⟨ε₂, hε₂, hth₂⟩ := (isCompact_range hb.1).exists_thickening_subset_open hNb hbN
  have hab' : IsTwoArcs a b := ⟨ha, hb, congrArg κ hab.3, congrArg κ hab.4,
    fun s t he => hab.5 s t (hκi he)⟩
  obtain ⟨a', b', ha', hb', ha'0, ha'1, hb'0, hb'1, hm', hnearA, hnearB, htame, hsubA, hsubB⟩ :=
    exists_tame_pair_in_union G hG ha hb hab'.3 hab'.4 hab'.5 hpG hqG (lt_min hε₁ hε₂)
  have hra' : range a' ⊆ Na :=
    (hnearA.trans (thickening_mono (min_le_left _ _) _)).trans hth₁
  have hrb' : range b' ⊆ Nb :=
    (hnearB.trans (thickening_mono (min_le_right _ _) _)).trans hth₂
  let P := range a' ∪ range b'
  have hPO : IsOArc P := oArc_of_two_arcs ha' hb'
    (ha'0.trans hb'0.symm) (ha'1.trans hb'1.symm) hm'
  have hPann : ∀ z ∈ P, α < ‖z‖ ∧ ‖z‖ < β := by
    rintro z (hz | hz)
    · exact (hra' hz).1
    · exact (hrb' hz).1
  have hlog : ¬ HasLogOn P fun z => z := by
    apply not_hasLogOn_of_two_sides (isPreconnected_range ha'.1) (isPreconnected_range hb'.1)
      (fun z hz => (hra' hz).2) (fun z hz => (hrb' hz).2) hrpos
      ⟨hτ0, by linarith [hτ1]⟩ (ha'0.trans hp0) (ha'1.trans hq0)
      (mem_range_self 0) (mem_range_self 1)
    · exact ⟨0, hb'0.trans ha'0.symm⟩
    · exact ⟨1, hb'1.trans ha'1.symm⟩
  obtain ⟨hin, hout⟩ := closedBall_subset_inner_of_annulus hα (lt_trans hαr hrβ) hPO
    (Set.disjoint_left.mpr fun z hz hz' => (not_le_of_gt (hPann z hz).1)
      (mem_closedBall_zero_iff.mp hz')) (fun z hz => mem_ball_zero_iff.mpr (hPann z hz).2) hlog
  have hsub : P ⊆ sphere 0 r ∪ ⋃ γ ∈ G, range γ := by
    rintro z (hz | hz)
    · rcases hsubA hz with ⟨t, rfl⟩ | hz
      · exact Or.inl (mem_sphere_zero_iff_norm.mpr (hκn _))
      · exact Or.inr hz
    · rcases hsubB hz with ⟨t, rfl⟩ | hz
      · exact Or.inl (mem_sphere_zero_iff_norm.mpr (hκn _))
      · exact Or.inr hz
  obtain ⟨hE, hbd⟩ := isClosedDisc_closedInner hPO
  exact ⟨P, closedInner P, hPO, htame, hsub,
    Set.disjoint_left.mpr (fun z hz hz' => (not_le_of_gt (hPann z hz).1)
      (mem_closedBall_zero_iff.mp hz')), hE, hbd,
    fun z hz => Or.inl (hin hz), hout⟩

end GraphMinor.GM08
