module

public import GraphMinor.GM06.Alg57ChartOrientation
import GraphMinor.GM19.CircleOrder
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Model sectors in the unit disc

The charts at a vertex of a drawing and at a point of an edge show the edges as rays. The two
sides of a ray near the centre are thin sectors. This file sets up these sectors in `ℂ`.

`sector A B R` is the closed sector of radius `R` from the direction `A` counterclockwise to
the direction `B`, for an angle below `π`. It is an intersection of a disc and two half-planes,
so it is convex. `openSector A B R` is its open version.

The key computation is `circleCyclic_ray`: seen from a point on the counterclockwise side of a
ray, points that move out along the ray turn counterclockwise. Together with
`planePos_chart_convex` this gives the orientation of the boundary of a sector, read along its
bounding ray.
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Metric Topology GraphMinor.Surface

/-- The coordinate across the ray of direction `A`: positive on its counterclockwise side. -/
noncomputable def across (A : Circle) (z : ℂ) : ℝ := (((A⁻¹ : Circle) : ℂ) * z).im

theorem continuous_across (A : Circle) : Continuous (across A) := by
  unfold across; fun_prop

theorem across_add (A : Circle) (z z' : ℂ) : across A (z + z') = across A z + across A z' := by
  simp [across, mul_add]

theorem across_smul (A : Circle) (l : ℝ) (z : ℂ) : across A ((l : ℂ) * z) = l * across A z := by
  simp only [across]
  rw [mul_left_comm, Complex.im_ofReal_mul]

theorem across_ray (A : Circle) (t : ℝ) : across A ((t : ℂ) * A) = 0 := by
  simp only [across]
  rw [mul_left_comm, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one, mul_one]
  simp

/-- The closed sector of radius `R` from direction `A` counterclockwise to direction `B`. -/
def sector (A B : Circle) (R : ℝ) : Set ℂ :=
  {z | ‖z‖ ≤ R ∧ 0 ≤ across A z ∧ across B z ≤ 0}

/-- The open sector of radius `R` from direction `A` counterclockwise to direction `B`. -/
def openSector (A B : Circle) (R : ℝ) : Set ℂ :=
  {z | ‖z‖ < R ∧ 0 < across A z ∧ across B z < 0}

theorem isClosed_sector (A B : Circle) (R : ℝ) : IsClosed (sector A B R) := by
  change IsClosed ({z : ℂ | ‖z‖ ≤ R} ∩ ({z | 0 ≤ across A z} ∩ {z | across B z ≤ 0}))
  exact (isClosed_le continuous_norm continuous_const).inter
    ((isClosed_le continuous_const (continuous_across A)).inter
    (isClosed_le (continuous_across B) continuous_const))

theorem isOpen_openSector (A B : Circle) (R : ℝ) : IsOpen (openSector A B R) := by
  change IsOpen ({z : ℂ | ‖z‖ < R} ∩ ({z | 0 < across A z} ∩ {z | across B z < 0}))
  exact (isOpen_lt continuous_norm continuous_const).inter
    ((isOpen_lt continuous_const (continuous_across A)).inter
    (isOpen_lt (continuous_across B) continuous_const))

theorem convex_sector (A B : Circle) (R : ℝ) : Convex ℝ (sector A B R) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_, ?_⟩
  · calc ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * R + b * R := by gcongr; exacts [hx.1, hy.1]
      _ = R := by rw [← add_mul, hab, one_mul]
  · rw [Complex.real_smul, Complex.real_smul, across_add, across_smul, across_smul]
    nlinarith [hx.2.1, hy.2.1]
  · rw [Complex.real_smul, Complex.real_smul, across_add, across_smul, across_smul]
    nlinarith [hx.2.2, hy.2.2]

theorem convex_openSector (A B : Circle) (R : ℝ) : Convex ℝ (openSector A B R) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_, ?_⟩
  · calc ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ < a * R + b * R := by
        rcases eq_or_lt_of_le ha with h | h
        · rw [← h] at hab ⊢; rw [zero_add] at hab; subst hab; simp [hy.1]
        · nlinarith [hx.1, hy.1, norm_nonneg y]
      _ = R := by rw [← add_mul, hab, one_mul]
  · rw [Complex.real_smul, Complex.real_smul, across_add, across_smul, across_smul]
    rcases eq_or_lt_of_le ha with h | h
    · rw [← h] at hab ⊢; rw [zero_add] at hab; subst hab; simp [hy.2.1]
    · nlinarith [hx.2.1, hy.2.1]
  · rw [Complex.real_smul, Complex.real_smul, across_add, across_smul, across_smul]
    rcases eq_or_lt_of_le ha with h | h
    · rw [← h] at hab ⊢; rw [zero_add] at hab; subst hab; simp [hy.2.2]
    · nlinarith [hx.2.2, hy.2.2]

theorem openSector_subset_sector (A B : Circle) (R : ℝ) : openSector A B R ⊆ sector A B R :=
  fun _ h => ⟨h.1.le, h.2.1.le, h.2.2.le⟩

theorem openSector_subset_interior (A B : Circle) (R : ℝ) :
    openSector A B R ⊆ interior (sector A B R) :=
  interior_maximal (openSector_subset_sector A B R) (isOpen_openSector A B R)

theorem sector_subset_closedBall (A B : Circle) (R : ℝ) : sector A B R ⊆ closedBall 0 R :=
  fun _ h => mem_closedBall_zero_iff.mpr h.1

theorem sector_mono {A B : Circle} {R R' : ℝ} (h : R ≤ R') : sector A B R ⊆ sector A B R' :=
  fun _ hz => ⟨hz.1.trans h, hz.2⟩

theorem openSector_mono {A B : Circle} {R R' : ℝ} (h : R ≤ R') :
    openSector A B R ⊆ openSector A B R' :=
  fun _ hz => ⟨hz.1.trans_le h, hz.2⟩

/-- A closed sector lies in the closure of its open part, when the open part is not empty. -/
theorem sector_subset_closure_openSector {A B : Circle} {R : ℝ} {p : ℂ}
    (hp : p ∈ openSector A B R) : sector A B R ⊆ closure (openSector A B R) := by
  intro z hz
  have hlim : Filter.Tendsto (fun s : ℝ => ((1 - s : ℝ) : ℂ) * z + (s : ℂ) * p)
      (𝓝[>] 0) (𝓝 z) := by
    have : Continuous fun s : ℝ => ((1 - s : ℝ) : ℂ) * z + (s : ℂ) * p := by fun_prop
    have h0 := this.tendsto 0
    simp only [sub_zero, Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul,
      add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
  obtain ⟨hs0, hs1⟩ := hs
  refine ⟨?_, ?_, ?_⟩
  · calc ‖((1 - s : ℝ) : ℂ) * z + (s : ℂ) * p‖
        ≤ ‖((1 - s : ℝ) : ℂ) * z‖ + ‖(s : ℂ) * p‖ := norm_add_le _ _
      _ = (1 - s) * ‖z‖ + s * ‖p‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg hs0.le]
      _ < R := by nlinarith [hz.1, hp.1]
  · rw [across_add, across_smul, across_smul]; nlinarith [hz.2.1, hp.2.1]
  · rw [across_add, across_smul, across_smul]; nlinarith [hz.2.2, hp.2.2]

/-- The counterclockwise rotation of a direction by the angle `θ`. -/
noncomputable def turnBy (A : Circle) (θ : ℝ) : Circle := A * Circle.exp θ

theorem across_turnBy (A : Circle) (θ : ℝ) (z : ℂ) :
    across (turnBy A θ) z = Real.cos θ * across A z - Real.sin θ * (((A⁻¹ : Circle) : ℂ) * z).re := by
  simp only [across, turnBy, mul_inv_rev, Circle.coe_mul, Circle.coe_inv_eq_conj,
    Circle.coe_exp]
  rw [mul_comm ((starRingEnd ℂ) (Complex.exp (θ * Complex.I))), mul_assoc]
  rw [← Complex.exp_conj]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [show (θ : ℂ) * -Complex.I = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I]
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
  simp [Complex.mul_im, Complex.mul_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  ring

/-- The coordinate along the ray of direction `A`. -/
noncomputable def along (A : Circle) (z : ℂ) : ℝ := (((A⁻¹ : Circle) : ℂ) * z).re

theorem eq_along_across (A : Circle) (z : ℂ) :
    z = (A : ℂ) * ((along A z : ℂ) + (across A z : ℂ) * Complex.I) := by
  simp only [along, across]
  rw [Complex.re_add_im, ← mul_assoc, ← Circle.coe_mul, mul_inv_cancel, Circle.coe_one, one_mul]

theorem across_turnBy' (A : Circle) (θ : ℝ) (z : ℂ) :
    across (turnBy A θ) z = Real.cos θ * across A z - Real.sin θ * along A z :=
  across_turnBy A θ z

theorem along_ray (A : Circle) (t : ℝ) : along A ((t : ℂ) * A) = t := by
  simp only [along]
  rw [mul_left_comm, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one, mul_one]
  simp

theorem norm_eq_along_across (A : Circle) (z : ℂ) :
    ‖z‖ ^ 2 = along A z ^ 2 + across A z ^ 2 := by
  conv_lhs => rw [eq_along_across A z]
  rw [norm_mul, Circle.norm_coe, one_mul, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp; ring

/-- The point with coordinates `a` along and `b` across the ray of `A`. -/
noncomputable def coordPt (A : Circle) (a b : ℝ) : ℂ := (A : ℂ) * ((a : ℂ) + (b : ℂ) * Complex.I)

theorem along_coordPt (A : Circle) (a b : ℝ) : along A (coordPt A a b) = a := by
  simp only [along, coordPt]
  rw [← mul_assoc, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one, one_mul]
  simp

theorem across_coordPt (A : Circle) (a b : ℝ) : across A (coordPt A a b) = b := by
  simp only [across, coordPt]
  rw [← mul_assoc, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one, one_mul]
  simp

theorem norm_coordPt (A : Circle) (a b : ℝ) : ‖coordPt A a b‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [norm_eq_along_across A, along_coordPt, across_coordPt]

theorem coordPt_zero (A : Circle) (a : ℝ) : coordPt A a 0 = (a : ℂ) * A := by
  simp [coordPt, mul_comm]

/-- The thin sector on the counterclockwise side of the ray of `W`. -/
noncomputable def secP (W : Circle) (ε R : ℝ) : Set ℂ := sector W (turnBy W ε) R

/-- The thin sector on the clockwise side of the ray of `W`. -/
noncomputable def secM (W : Circle) (ε R : ℝ) : Set ℂ := sector (turnBy W (-ε)) W R

/-- The open thin sector on the counterclockwise side of the ray of `W`. -/
noncomputable def osecP (W : Circle) (ε R : ℝ) : Set ℂ := openSector W (turnBy W ε) R

/-- The open thin sector on the clockwise side of the ray of `W`. -/
noncomputable def osecM (W : Circle) (ε R : ℝ) : Set ℂ := openSector (turnBy W (-ε)) W R

/-- The open double sector about the ray of `W`. -/
noncomputable def dsec (W : Circle) (ε R : ℝ) : Set ℂ := openSector (turnBy W (-ε)) (turnBy W ε) R

section Thin

variable {W : Circle} {ε R : ℝ}

theorem mem_osecP_coord (hε : 0 < ε) (hε' : ε < Real.pi / 2) (hR : 0 < R) :
    coordPt W (R / 2) (Real.sin ε * (R / 2) / 2) ∈ osecP W ε R := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hε (by linarith [Real.pi_pos])
  have hs1 := Real.sin_le_one ε
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith, hε'⟩
  have hc1 := Real.cos_le_one ε
  refine ⟨?_, ?_, ?_⟩
  · have h := norm_coordPt W (R / 2) (Real.sin ε * (R / 2) / 2)
    have h2 : (Real.sin ε * (R / 2) / 2) ^ 2 ≤ (R / 2) ^ 2 := by
      rw [div_pow, mul_pow]
      nlinarith [mul_le_mul_of_nonneg_right (Real.sin_sq_le_one ε) (sq_nonneg (R / 2))]
    have hlt : ‖coordPt W (R / 2) (Real.sin ε * (R / 2) / 2)‖ ^ 2 < R ^ 2 := by nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hR.le hlt
  · rw [across_coordPt]; positivity
  · rw [across_turnBy', across_coordPt, along_coordPt]; nlinarith [mul_pos hs hR]

theorem mem_osecM_coord (hε : 0 < ε) (hε' : ε < Real.pi / 2) (hR : 0 < R) :
    coordPt W (R / 2) (-(Real.sin ε * (R / 2) / 2)) ∈ osecM W ε R := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hε (by linarith [Real.pi_pos])
  have hs1 := Real.sin_le_one ε
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith, hε'⟩
  have hc1 := Real.cos_le_one ε
  refine ⟨?_, ?_, ?_⟩
  · have h := norm_coordPt W (R / 2) (-(Real.sin ε * (R / 2) / 2))
    have h2 : (-(Real.sin ε * (R / 2) / 2)) ^ 2 ≤ (R / 2) ^ 2 := by
      rw [neg_sq, div_pow, mul_pow]
      nlinarith [mul_le_mul_of_nonneg_right (Real.sin_sq_le_one ε) (sq_nonneg (R / 2))]
    have hlt : ‖coordPt W (R / 2) (-(Real.sin ε * (R / 2) / 2))‖ ^ 2 < R ^ 2 := by nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hR.le hlt
  · rw [across_turnBy', across_coordPt, along_coordPt, Real.cos_neg, Real.sin_neg]
    nlinarith [mul_pos hs hR]
  · rw [across_coordPt]; nlinarith [mul_pos hs hR]

theorem ray_mem_secP (hε : 0 < ε) (hε' : ε < Real.pi / 2) {t : ℝ} (ht : 0 ≤ t) (htR : t ≤ R) :
    (t : ℂ) * W ∈ secP W ε R := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hε (by linarith [Real.pi_pos])
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg ht]; exact htR
  · rw [across_ray]
  · rw [across_turnBy', across_ray, along_ray]; nlinarith

theorem ray_mem_secM (hε : 0 < ε) (hε' : ε < Real.pi / 2) {t : ℝ} (ht : 0 ≤ t) (htR : t ≤ R) :
    (t : ℂ) * W ∈ secM W ε R := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hε (by linarith [Real.pi_pos])
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg ht]; exact htR
  · rw [across_turnBy', across_ray, along_ray, Real.cos_neg, Real.sin_neg]; nlinarith
  · rw [across_ray]

theorem ray_mem_frontier_secP (hε : 0 < ε) (hε' : ε < Real.pi / 2) {t : ℝ} (ht : 0 ≤ t)
    (htR : t ≤ R) : (t : ℂ) * W ∈ frontier (secP W ε R) := by
  refine ⟨subset_closure (ray_mem_secP hε hε' ht htR), fun hint => ?_⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hint)
  have hz : coordPt W t (-(δ / 2)) ∈ ball ((t : ℂ) * W) δ := by
    rw [mem_ball, dist_eq_norm, ← coordPt_zero]
    have : coordPt W t (-(δ / 2)) - coordPt W t 0 = coordPt W 0 (-(δ / 2)) := by
      simp [coordPt]; ring
    rw [this]
    have h := norm_coordPt W 0 (-(δ / 2))
    have hlt : ‖coordPt W 0 (-(δ / 2))‖ ^ 2 < δ ^ 2 := by rw [h]; nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hδ.le hlt
  have := (hball hz).2.1
  rw [across_coordPt] at this
  linarith

theorem ray_mem_frontier_secM (hε : 0 < ε) (hε' : ε < Real.pi / 2) {t : ℝ} (ht : 0 ≤ t)
    (htR : t ≤ R) : (t : ℂ) * W ∈ frontier (secM W ε R) := by
  refine ⟨subset_closure (ray_mem_secM hε hε' ht htR), fun hint => ?_⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hint)
  have hz : coordPt W t (δ / 2) ∈ ball ((t : ℂ) * W) δ := by
    rw [mem_ball, dist_eq_norm, ← coordPt_zero]
    have : coordPt W t (δ / 2) - coordPt W t 0 = coordPt W 0 (δ / 2) := by
      simp [coordPt]; ring
    rw [this]
    have h := norm_coordPt W 0 (δ / 2)
    have hlt : ‖coordPt W 0 (δ / 2)‖ ^ 2 < δ ^ 2 := by rw [h]; nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hδ.le hlt
  have := (hball hz).2.2
  rw [across_coordPt] at this
  linarith

theorem osecP_subset_secP : osecP W ε R ⊆ secP W ε R := openSector_subset_sector _ _ _

theorem osecM_subset_secM : osecM W ε R ⊆ secM W ε R := openSector_subset_sector _ _ _

theorem disjoint_osecP_osecM : Disjoint (osecP W ε R) (osecM W ε R) := by
  rw [Set.disjoint_left]
  intro z h1 h2
  exact absurd h1.2.1 (not_lt.mpr h2.2.2.le)

theorem ray_mem_dsec (hε : 0 < ε) (hε' : ε < Real.pi / 2) {t : ℝ} (ht : 0 < t) (htR : t < R) :
    (t : ℂ) * W ∈ dsec W ε R := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hε (by linarith [Real.pi_pos])
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg ht.le]
    exact htR
  · rw [across_turnBy', across_ray, along_ray, Real.cos_neg, Real.sin_neg]; nlinarith
  · rw [across_turnBy', across_ray, along_ray]; nlinarith

/-- The double sector off the ray is the union of the two open thin sectors. -/
theorem dsec_cases (hε : 0 < ε) (hε' : ε < Real.pi / 2) {z : ℂ} (hz : z ∈ dsec W ε R) :
    z ∈ osecP W ε R ∨ z ∈ osecM W ε R ∨ (0 < along W z ∧ z = (along W z : ℂ) * W) := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hε (by linarith [Real.pi_pos])
  obtain ⟨hn, h1, h2⟩ := hz
  rw [across_turnBy', Real.cos_neg, Real.sin_neg] at h1
  rw [across_turnBy'] at h2
  rcases lt_trichotomy (across W z) 0 with h | h | h
  · right; left
    refine ⟨hn, ?_, h⟩
    rw [across_turnBy', Real.cos_neg, Real.sin_neg]; exact h1
  · right; right
    rw [h] at h2
    have ha : 0 < along W z := by nlinarith
    refine ⟨ha, ?_⟩
    conv_lhs => rw [eq_along_across W z]
    rw [h]; simp [mul_comm]
  · left
    refine ⟨hn, h, ?_⟩
    rw [across_turnBy']; exact h2

theorem osecP_subset_dsec (hε : 0 < ε) (hε' : ε < Real.pi / 2) :
    osecP W ε R ⊆ dsec W ε R := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hε (by linarith [Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith, hε'⟩
  rintro z ⟨hn, h1, h2⟩
  rw [across_turnBy'] at h2
  refine ⟨hn, ?_, ?_⟩
  · rw [across_turnBy', Real.cos_neg, Real.sin_neg]
    have : 0 < along W z := by
      by_contra hneg; push Not at hneg; nlinarith
    nlinarith
  · rw [across_turnBy']; exact h2

theorem osecM_subset_dsec (hε : 0 < ε) (hε' : ε < Real.pi / 2) :
    osecM W ε R ⊆ dsec W ε R := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hε (by linarith [Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith, hε'⟩
  rintro z ⟨hn, h1, h2⟩
  rw [across_turnBy', Real.cos_neg, Real.sin_neg] at h1
  refine ⟨hn, ?_, ?_⟩
  · rw [across_turnBy', Real.cos_neg, Real.sin_neg]; exact h1
  · rw [across_turnBy']
    have : 0 < along W z := by
      by_contra hneg; push Not at hneg; nlinarith
    nlinarith

end Thin

/-! ### Directions to points of a ray -/

theorem unitOf_eq_exp_arg (z : ℂ) (hz : z ≠ 0) : unitOf z hz = Circle.exp (Complex.arg z) := by
  apply Circle.ext
  rw [coe_unitOf, Circle.coe_exp]
  have h := Complex.norm_mul_exp_arg_mul_I z
  have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
  rw [inv_mul_eq_iff_eq_mul₀ hn]
  exact h.symm

theorem unitOf_mul_circle (L : Circle) (z : ℂ) (hz : z ≠ 0) (h : (L : ℂ) * z ≠ 0) :
    unitOf ((L : ℂ) * z) h = L * unitOf z hz := by
  apply Circle.ext
  rw [coe_unitOf, Circle.coe_mul, coe_unitOf, norm_mul, Circle.norm_coe, one_mul]
  ring

/-- Turning three points of the circle by the same rotation keeps their cyclic order. -/
theorem circleCyclic_mul_left (g : Circle) {a b c : Circle} :
    CircleCyclic (g * a) (g * b) (g * c) ↔ CircleCyclic a b c := by
  constructor
  · rintro ⟨s, t, hs, hst, ht, hb, hc⟩
    refine ⟨s, t, hs, hst, ht, ?_, ?_⟩
    · apply mul_left_cancel (a := g); rw [hb, mul_assoc]
    · apply mul_left_cancel (a := g); rw [hc, mul_assoc]
  · rintro ⟨s, t, hs, hst, ht, hb, hc⟩
    exact ⟨s, t, hs, hst, ht, by rw [hb, mul_assoc], by rw [hc, mul_assoc]⟩

/-- The real part over the norm of `x - b i` grows with `x`. -/
theorem div_sqrt_strictMono {b : ℝ} (hb : 0 < b) :
    StrictMono fun x : ℝ => x / Real.sqrt (x ^ 2 + b ^ 2) := by
  have key : ∀ x : ℝ, x / Real.sqrt (x ^ 2 + b ^ 2) = Real.sin (Real.arctan (x / b)) := by
    intro x
    rw [Real.sin_arctan]
    have h1 : x ^ 2 + b ^ 2 = b ^ 2 * (1 + (x / b) ^ 2) := by field_simp; ring
    rw [h1, Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq hb.le]
    field_simp
  intro x y hxy
  simp only [key]
  apply Real.strictMonoOn_sin
  · exact ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩
  · exact ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩
  · exact Real.arctan_strictMono (div_lt_div_of_pos_right hxy hb)

theorem norm_sub_real (t : ℝ) (c : ℂ) : ‖(t : ℂ) - c‖ = Real.sqrt ((t - c.re) ^ 2 + c.im ^ 2) := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  simp [sq]

/-- Seen from a point on the counterclockwise side of the ray of `L`, points moving out along
the ray turn counterclockwise. -/
theorem circleCyclic_ray (L : Circle) {q : ℂ} (hq : 0 < across L q) {t₁ t₂ t₃ : ℝ}
    (h12 : t₁ < t₂) (h23 : t₂ < t₃) (h1 : (t₁ : ℂ) * L - q ≠ 0) (h2 : (t₂ : ℂ) * L - q ≠ 0)
    (h3 : (t₃ : ℂ) * L - q ≠ 0) :
    CircleCyclic (unitOf _ h1) (unitOf _ h2) (unitOf _ h3) := by
  set c : ℂ := ((L⁻¹ : Circle) : ℂ) * q with hc
  have hcim : 0 < c.im := hq
  have hfac : ∀ t : ℝ, (t : ℂ) * L - q = (L : ℂ) * ((t : ℂ) - c) := by
    intro t
    rw [hc, mul_sub, ← mul_assoc, ← Circle.coe_mul, mul_inv_cancel, Circle.coe_one, one_mul,
      mul_comm]
  have hne : ∀ t : ℝ, (t : ℂ) - c ≠ 0 := by
    intro t h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hu : ∀ (t : ℝ) (h : (t : ℂ) * L - q ≠ 0),
      unitOf _ h = L * Circle.exp (Complex.arg ((t : ℂ) - c)) := by
    intro t h
    have h' : (L : ℂ) * ((t : ℂ) - c) ≠ 0 := by rw [← hfac]; exact h
    have e : unitOf _ h = unitOf _ h' := by congr 1 <;> simp [hfac]
    rw [e, unitOf_mul_circle L _ (hne t), unitOf_eq_exp_arg]
  rw [hu, hu, hu, circleCyclic_mul_left]
  have harg : ∀ t : ℝ, Complex.arg ((t : ℂ) - c) =
      -Real.arccos ((t - c.re) / Real.sqrt ((t - c.re) ^ 2 + c.im ^ 2)) := by
    intro t
    rw [Complex.arg_of_im_neg (by simp; linarith), norm_sub_real]
    simp
  have hmono := div_sqrt_strictMono hcim
  have hmem : ∀ t : ℝ, (t - c.re) / Real.sqrt ((t - c.re) ^ 2 + c.im ^ 2) ∈ Icc (-1 : ℝ) 1 := by
    intro t
    have hpos : 0 < Real.sqrt ((t - c.re) ^ 2 + c.im ^ 2) := Real.sqrt_pos.mpr (by positivity)
    have habs : |t - c.re| ≤ Real.sqrt ((t - c.re) ^ 2 + c.im ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by nlinarith)
    rw [mem_Icc, le_div_iff₀ hpos, div_le_iff₀ hpos]
    constructor <;> [linarith [neg_abs_le (t - c.re)]; linarith [le_abs_self (t - c.re)]]
  have hlt : ∀ {x y : ℝ}, x < y → Complex.arg ((x : ℂ) - c) < Complex.arg ((y : ℂ) - c) := by
    intro x y hxy
    rw [harg, harg, neg_lt_neg_iff]
    exact Real.strictAntiOn_arccos (hmem x) (hmem y) (hmono (by linarith))
  have hneg : Complex.arg ((t₃ : ℂ) - c) < 0 := Complex.arg_neg_iff.mpr (by simp; linarith)
  have hlow := Complex.neg_pi_lt_arg ((t₁ : ℂ) - c)
  exact circleCyclic_exp_of_lt (hlt h12) (hlt h23) (by linarith [Real.pi_pos])

/-- Seen from a point on the clockwise side of the ray of `L`, points moving out along the ray
turn clockwise. -/
theorem circleCyclic_ray_rev (L : Circle) {q : ℂ} (hq : across L q < 0) {t₁ t₂ t₃ : ℝ}
    (h12 : t₁ < t₂) (h23 : t₂ < t₃) (h1 : (t₁ : ℂ) * L - q ≠ 0) (h2 : (t₂ : ℂ) * L - q ≠ 0)
    (h3 : (t₃ : ℂ) * L - q ≠ 0) :
    CircleCyclic (unitOf _ h3) (unitOf _ h2) (unitOf _ h1) := by
  set c : ℂ := ((L⁻¹ : Circle) : ℂ) * q with hc
  have hcim : c.im < 0 := hq
  have hfac : ∀ t : ℝ, (t : ℂ) * L - q = (L : ℂ) * ((t : ℂ) - c) := by
    intro t
    rw [hc, mul_sub, ← mul_assoc, ← Circle.coe_mul, mul_inv_cancel, Circle.coe_one, one_mul,
      mul_comm]
  have hne : ∀ t : ℝ, (t : ℂ) - c ≠ 0 := by
    intro t h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hu : ∀ (t : ℝ) (h : (t : ℂ) * L - q ≠ 0),
      unitOf _ h = L * Circle.exp (Complex.arg ((t : ℂ) - c)) := by
    intro t h
    have h' : (L : ℂ) * ((t : ℂ) - c) ≠ 0 := by rw [← hfac]; exact h
    have e : unitOf _ h = unitOf _ h' := by congr 1 <;> simp [hfac]
    rw [e, unitOf_mul_circle L _ (hne t), unitOf_eq_exp_arg]
  rw [hu, hu, hu, circleCyclic_mul_left]
  have harg : ∀ t : ℝ, Complex.arg ((t : ℂ) - c) =
      Real.arccos ((t - c.re) / Real.sqrt ((t - c.re) ^ 2 + (-c.im) ^ 2)) := by
    intro t
    rw [Complex.arg_of_im_pos (by simp; linarith), norm_sub_real]
    simp
  have hmono := div_sqrt_strictMono (b := -c.im) (by linarith)
  have hmem : ∀ t : ℝ, (t - c.re) / Real.sqrt ((t - c.re) ^ 2 + (-c.im) ^ 2) ∈ Icc (-1 : ℝ) 1 := by
    intro t
    have hpos : 0 < Real.sqrt ((t - c.re) ^ 2 + (-c.im) ^ 2) :=
      Real.sqrt_pos.mpr (by nlinarith [sq_nonneg (t - c.re)])
    have habs : |t - c.re| ≤ Real.sqrt ((t - c.re) ^ 2 + (-c.im) ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by nlinarith)
    rw [mem_Icc, le_div_iff₀ hpos, div_le_iff₀ hpos]
    constructor <;> [linarith [neg_abs_le (t - c.re)]; linarith [le_abs_self (t - c.re)]]
  have hlt : ∀ {x y : ℝ}, x < y → Complex.arg ((y : ℂ) - c) < Complex.arg ((x : ℂ) - c) := by
    intro x y hxy
    rw [harg, harg]
    exact Real.strictAntiOn_arccos (hmem x) (hmem y) (hmono (by linarith))
  have hpos : 0 < Complex.arg ((t₃ : ℂ) - c) := by
    rcases (Complex.arg_nonneg_iff.mpr (by simp; linarith : 0 ≤ ((t₃ : ℂ) - c).im)).lt_or_eq
      with h | h
    · exact h
    · exfalso
      have := Complex.arg_eq_zero_iff.mp h.symm
      simp at this
      linarith [this.2]
  have hup := Complex.arg_le_pi ((t₁ : ℂ) - c)
  exact circleCyclic_exp_of_lt (hlt h23) (hlt h12) (by linarith [Real.pi_pos])

end GraphMinor.GM06
