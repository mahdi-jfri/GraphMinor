module

public import GraphMinor.Surface.DiscMerge

/-!
# Keeping the inside of a ring during finite-crossing replacement

In the foundation step of VIII (9.1), a replacement of a round ring must
keep the drawing on the same side. A circle in a thin annulus encloses the
smaller concentric ball when its coordinate has no continuous logarithm.
This is the logarithm argument of `Surface.closedBall_subset_inner`, with
arbitrary inner and outer radii so that finitely many drawing points can
be kept away from the annulus.
-/

public section

namespace GraphMinor.GM08

open Set Surface Topology Complex Metric

/-- A circle in an annulus with nonzero winding encloses the inner ball,
and its closed inside lies in the outer ball. This controls which drawing
edges are enclosed when a ring is replaced in the proof of VIII (9.1). -/
theorem closedBall_subset_inner_of_annulus {P : Set ℂ} {ρ R : ℝ}
    (hρ : 0 ≤ ρ) (hρR : ρ < R) (hP : IsOArc P)
    (hinner : Disjoint P (closedBall 0 ρ)) (houter : P ⊆ ball 0 R)
    (hlog : ¬ HasLogOn P fun z => z) :
    closedBall 0 ρ ⊆ inner P ∧ closedInner P ⊆ ball 0 R := by
  obtain ⟨φ⟩ := hP
  have J := isJordanParts φ
  have hR : 0 < R := lt_of_le_of_lt hρ hρR
  obtain ⟨r, hr, hr0, hPr⟩ : ∃ r < R, 0 ≤ r ∧ P ⊆ closedBall 0 r := by
    by_cases hne : P.Nonempty
    · obtain ⟨z, hz, hmax⟩ := J.isCompact.exists_isMaxOn hne continuous_norm.continuousOn
      refine ⟨‖z‖, mem_ball_zero_iff.mp (houter hz), norm_nonneg _, fun w hw => ?_⟩
      exact mem_closedBall_zero_iff.mpr (hmax hw)
    · exact ⟨0, hR, le_rfl, fun w hw => absurd ⟨w, hw⟩ hne⟩
  have hfar : (closedBall (0 : ℂ) r)ᶜ ⊆ outer P := by
    have hconn := isPreconnected_compl_closedBall r hr0
    have hdisj : (closedBall (0 : ℂ) r)ᶜ ⊆ inner P ∪ outer P := by
      rw [J.union_eq]
      exact fun z hz hzP => hz (hPr hzP)
    rcases hconn.subset_or_subset J.isOpen_inner J.isOpen_outer J.disjoint hdisj with h | h
    · exfalso
      obtain ⟨M, hM⟩ := J.isBounded_inner.subset_closedBall 0
      have hmem : ((max M r + 1 : ℝ) : ℂ) ∈ (closedBall (0 : ℂ) r)ᶜ := by
        have : ‖((max M r + 1 : ℝ) : ℂ)‖ = max M r + 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
          have := le_max_right M r
          linarith
        simp only [mem_compl_iff, mem_closedBall_zero_iff, this, not_le]
        linarith [le_max_right M r]
      have hbound := hM (h hmem)
      simp only [mem_closedBall_zero_iff] at hbound
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by
        have := le_max_right M r
        linarith)] at hbound
      linarith [le_max_left M r]
    · exact h
  have hbounded : inner P ⊆ closedBall 0 r := fun z hz => by
    by_contra hcon
    exact Set.disjoint_left.mp J.disjoint hz (hfar hcon)
  have h0mem : (0 : ℂ) ∈ closedBall (0 : ℂ) ρ := by simpa using hρ
  have h0P : (0 : ℂ) ∉ P := fun h => Set.disjoint_left.mp hinner h h0mem
  have hmem : ∀ z ∈ closedBall (0 : ℂ) ρ, z ∈ inner P ∪ outer P := fun z hz => by
    rw [J.union_eq]
    exact fun h => Set.disjoint_left.mp hinner h hz
  have hc := (convex_closedBall (0 : ℂ) ρ).isPreconnected.subset_or_subset
    J.isOpen_inner J.isOpen_outer J.disjoint hmem
  have hin : closedBall 0 ρ ⊆ inner P := by
    rcases hc with h | h
    · exact h
    exfalso
    let q : ℂ := (R + 1 : ℝ)
    have hqnorm : ‖q‖ = R + 1 := by
      dsimp only [q]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have hqo : q ∈ outer P := hfar (by
      simp only [mem_compl_iff, mem_closedBall_zero_iff, hqnorm, not_le]
      linarith)
    have hcomp : q ∈ connectedComponentIn Pᶜ 0 :=
      J.isConnected_outer.isPreconnected.subset_connectedComponentIn (h h0mem)
        (fun z hz => hz.1) hqo
    have hl := hasLogOn_div_of_same_component J.isCompact.isClosed h0P hcomp
    have hl2 : HasLogOn P fun z : ℂ => q - z := hasLogOn_of_slitPlane (by fun_prop) fun z hz => by
      left
      have hzR : ‖z‖ < R := mem_ball_zero_iff.mp (houter hz)
      have hzre := (abs_le.mp (Complex.abs_re_le_norm z)).2
      simp only [Complex.sub_re, q, Complex.ofReal_re]
      linarith
    have hl3 : HasLogOn P fun _ : ℂ => (-1 : ℂ) := hasLogOn_const (by norm_num)
    refine hlog ((((hl.inv).mul hl2).mul hl3).congr fun z hz => ?_)
    have hz0 : z ≠ 0 := fun h => h0P (h ▸ hz)
    have hzq : z - q ≠ 0 := fun h => by
      have hzR : ‖z‖ < R := mem_ball_zero_iff.mp (houter hz)
      rw [sub_eq_zero.mp h, hqnorm] at hzR
      linarith
    simp only [sub_zero]
    field_simp
    ring
  refine ⟨hin, union_subset ?_ houter⟩
  exact hbounded.trans (closedBall_subset_ball hr)

end GraphMinor.GM08
