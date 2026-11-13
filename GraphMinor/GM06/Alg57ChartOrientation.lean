module

public import GraphMinor.Surface.PlaneOrientation
public import GraphMinor.Surface.DiscTwist
import GraphMinor.GM19.Winding
import GraphMinor.GM19.Flower
import GraphMinor.Surface.Cap
import GraphMinor.Surface.EdgeLens
import Mathlib.Analysis.Convex.Gauge

/-!
# Orientation of convex pieces of a positive chart

Step 1 of the proof of Lemma 3 of our proof of VI (5.7) (outlined in `Alg57Algorithm.lean`)
compares the two sides of an edge at its two ends. We compare sides by the orientation
`planePos` of the plane, which nested discs share (`order_of_nested`).

Here a chart is an injective continuous map `χ` from the closed unit disc of `ℂ` to `ℂ`
whose boundary circle winds positively around `χ 0`. The main result is
`planePos_chart_convex`. For a compact convex set `K` in the closed unit disc with an interior
point `p`, the image `χ '' K` is a closed disc. Three of its boundary points are in positive
order exactly when the directions from `p` to their preimages are in counterclockwise order.

The proof moves the boundary of `χ '' K` by homotopies that keep off `χ p`: first along the
rays from `p` to a small round circle about `p`, then straight to the unit circle, and finally
the base point from `χ p` to `χ 0`. Winding numbers do not change along such homotopies
(`wind_eq_of_family`). The boundary of `K` is described through the gauge of `K - p`
(`exists_radial_of_convex`).
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Metric Topology GraphMinor.Surface

/-- Winding is unchanged along a family of loops that keeps off a moving point. -/
theorem wind_eq_of_family {F : ℝ → Circle → ℂ} (hF : Continuous fun q : ℝ × Circle => F q.1 q.2)
    {z : ℝ → ℂ} (hz : Continuous z) (hne : ∀ u w, F u w ≠ z u) (a b : ℝ) :
    wind (F a) (z a) = wind (F b) (z b) := by
  let H : ℝ → ℝ → ℂ := fun u t => F u (Circle.exp t) - z u
  have hH : Continuous fun q : ℝ × ℝ => H q.1 q.2 :=
    (hF.comp (continuous_fst.prodMk (Circle.exp.continuous.comp continuous_snd))).sub
      (hz.comp continuous_fst)
  have h0 : ∀ u t, H u t ≠ 0 := fun u t => sub_ne_zero.mpr (hne u _)
  have hper : ∀ u, Function.Periodic (H u) (2 * Real.pi) := fun u t => by
    simp only [H, exp_add_two_pi']
  have hv : ∀ t, ∃ t' ∈ Icc 0 (2 * Real.pi), ∀ u, H u t = H u t' := by
    intro t
    obtain ⟨t', ht', n, rfl⟩ := exists_mem_period t
    exact ⟨_, ht', fun u => ((hper u).sub_zsmul_eq n).symm⟩
  have hh := GM19.turn_eq_of_homotopy hH h0 isCompact_Icc hv (s := 0) (t := 2 * Real.pi)
    (fun u => by
      have hp := hper u 0
      rw [zero_add] at hp
      exact hp.symm) a b
  simpa only [wind, H] using hh

/-- The clamp of a real number to `[0, 1]`. -/
noncomputable def clampUnit (u : ℝ) : ℝ := max 0 (min u 1)

@[fun_prop]
theorem continuous_clampUnit : Continuous clampUnit := by
  unfold clampUnit; fun_prop

theorem clampUnit_mem (u : ℝ) : clampUnit u ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

@[simp] theorem clampUnit_zero : clampUnit 0 = 0 := by simp [clampUnit]

@[simp] theorem clampUnit_one : clampUnit 1 = 1 := by simp [clampUnit]

/-- Boundary of a compact convex set, seen from an interior point: a radial function. -/
theorem exists_radial_of_convex {K : Set ℂ} (hc : Convex ℝ K) (hb : Bornology.IsBounded K)
    (hcl : IsClosed K) {p : ℂ} (hp : p ∈ interior K) :
    ∃ ρ : Circle → ℝ, Continuous ρ ∧ (∀ w, 0 < ρ w) ∧
      (∀ w, p + (ρ w : ℂ) * w ∈ frontier K) ∧
      (∀ w (l : ℝ), 0 ≤ l → l ≤ ρ w → p + (l : ℂ) * w ∈ K) ∧
      ∀ q ∈ frontier K, ∃ hq : q - p ≠ 0,
        q = p + (ρ (unitOf (q - p) hq) : ℂ) * unitOf (q - p) hq := by
  let s : Set ℂ := (fun z => p + z) ⁻¹' K
  have hsc : Convex ℝ s := hc.translate_preimage_right p
  have hs0 : s ∈ 𝓝 (0 : ℂ) := by
    have : Continuous fun z : ℂ => p + z := by fun_prop
    exact this.continuousAt.preimage_mem_nhds (by simpa using mem_interior_iff_mem_nhds.mp hp)
  have hscl : IsClosed s := hcl.preimage (by fun_prop)
  have hsb : Bornology.IsBounded s := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hb
    refine (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mpr ⟨R + ‖p‖, fun z hz => ?_⟩
    have h1 := hR hz
    rw [mem_closedBall_zero_iff] at h1 ⊢
    calc ‖z‖ = ‖(p + z) - p‖ := by ring_nf
      _ ≤ ‖p + z‖ + ‖p‖ := norm_sub_le _ _
      _ ≤ R + ‖p‖ := by linarith
  have habs : Absorbent ℝ s := absorbent_nhds_zero hs0
  have hvb : Bornology.IsVonNBounded ℝ s := (NormedSpace.isVonNBounded_iff ℝ).mpr hsb
  have hgpos : ∀ z : ℂ, z ≠ 0 → 0 < gauge s z := fun z hz => (gauge_pos habs hvb).mpr hz
  have hgc : Continuous (gauge s) := continuous_gauge hsc hs0
  have hw0 : ∀ w : Circle, (w : ℂ) ≠ 0 := fun w => Circle.coe_ne_zero w
  let ρ : Circle → ℝ := fun w => (gauge s w)⁻¹
  have hρpos : ∀ w, 0 < ρ w := fun w => inv_pos.mpr (hgpos _ (hw0 w))
  have hgsmul : ∀ (l : ℝ) (z : ℂ), 0 ≤ l → gauge s ((l : ℂ) * z) = l * gauge s z := by
    intro l z hl
    rw [← Complex.real_smul, gauge_smul_of_nonneg hl, smul_eq_mul]
  have hfr : ∀ z, z ∈ frontier s ↔ p + z ∈ frontier K := by
    intro z
    have := (Homeomorph.addLeft p).preimage_frontier K
    change z ∈ frontier ((Homeomorph.addLeft p) ⁻¹' K) ↔ _
    rw [← this]
    rfl
  refine ⟨ρ, ?_, hρpos, ?_, ?_, ?_⟩
  · exact (hgc.comp continuous_subtype_val).inv₀ fun w => (hgpos _ (hw0 w)).ne'
  · intro w
    rw [← hfr, ← gauge_eq_one_iff_mem_frontier hsc hs0, hgsmul _ _ (hρpos w).le]
    exact inv_mul_cancel₀ (hgpos _ (hw0 w)).ne'
  · intro w l hl hlρ
    have hmem : (l : ℂ) * w ∈ closure s := by
      rw [← gauge_le_one_iff_mem_closure hsc hs0, hgsmul _ _ hl]
      calc l * gauge s w ≤ ρ w * gauge s w :=
            mul_le_mul_of_nonneg_right hlρ (gauge_nonneg _)
        _ = 1 := inv_mul_cancel₀ (hgpos _ (hw0 w)).ne'
    rw [hscl.closure_eq] at hmem
    exact hmem
  · intro q hq
    have hq0 : q - p ≠ 0 := by
      intro h
      have : q = p := sub_eq_zero.mp h
      rw [this] at hq
      exact hq.2 hp
    refine ⟨hq0, ?_⟩
    set w := unitOf (q - p) hq0
    have hqw : ((‖q - p‖ : ℝ) : ℂ) * w = q - p := norm_mul_unitOf _ hq0
    have hfs : q - p ∈ frontier s := (hfr _).mpr (by simpa using hq)
    have hg1 : gauge s (q - p) = 1 := (gauge_eq_one_iff_mem_frontier hsc hs0).mpr hfs
    rw [← hqw, hgsmul _ _ (norm_nonneg _)] at hg1
    have hρw : ρ w = ‖q - p‖ := by
      change (gauge s w)⁻¹ = _
      rw [inv_eq_of_mul_eq_one_left hg1]
    rw [hρw, hqw]
    ring

section Chart

variable {χ : ℂ → ℂ}

/-- The winding of the boundary circle is the same around the image of every interior point. -/
theorem wind_circle_eq_centre (hχ : Continuous χ) (hi : InjOn χ (closedBall 0 1)) {p : ℂ}
    (hp : p ∈ ball (0 : ℂ) 1) :
    wind (fun w : Circle => χ w) (χ p) = wind (fun w : Circle => χ w) (χ 0) := by
  have h := wind_eq_of_family (F := fun _ w => χ w) (by fun_prop)
    (z := fun u => χ ((clampUnit u : ℂ) * p)) (by fun_prop) ?_ 1 0
  · simpa using h
  · intro u w he
    have hp' : ‖p‖ < 1 := mem_ball_zero_iff.mp hp
    have hm : (clampUnit u : ℂ) * p ∈ closedBall (0 : ℂ) 1 := by
      rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (clampUnit_mem u).1]
      nlinarith [(clampUnit_mem u).2, norm_nonneg p]
    have hw : (w : ℂ) ∈ closedBall (0 : ℂ) 1 := by simp
    have := hi hw hm he
    have hn := congrArg norm this
    rw [Circle.norm_coe, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (clampUnit_mem u).1] at hn
    nlinarith [(clampUnit_mem u).2, norm_nonneg p]

/-- A small round circle about `p` winds around `χ p` as the boundary circle does. -/
theorem wind_round_eq_circle (hχ : Continuous χ) (hi : InjOn χ (closedBall 0 1)) {p : ℂ} {r : ℝ}
    (hr : 0 < r) (hsub : closedBall p r ⊆ closedBall 0 1) :
    wind (fun w : Circle => χ (p + (r : ℂ) * w)) (χ p) = wind (fun w : Circle => χ w) (χ p) := by
  have hpr : ‖p‖ + r ≤ 1 := by
    by_cases hp0 : p = 0
    · have h := hsub (show (r : ℂ) ∈ closedBall p r by
        rw [hp0, mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg hr.le])
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_of_nonneg hr.le] at h
      rw [hp0, norm_zero]; linarith
    · have hpn : 0 < ‖p‖ := norm_pos_iff.mpr hp0
      let q : ℂ := p + ((r / ‖p‖ : ℝ) : ℂ) * p
      have hq : q ∈ closedBall p r := by
        rw [mem_closedBall, dist_eq_norm]
        simp only [q, add_sub_cancel_left, norm_mul, Complex.norm_real]
        rw [Real.norm_of_nonneg (div_nonneg hr.le hpn.le), div_mul_cancel₀ _ hpn.ne']
      have h := hsub hq
      rw [mem_closedBall_zero_iff] at h
      have hq' : q = ((1 + r / ‖p‖ : ℝ) : ℂ) * p := by
        simp only [q]; push_cast; ring
      rw [hq', norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + r / ‖p‖)] at h
      have : (1 + r / ‖p‖) * ‖p‖ = ‖p‖ + r := by field_simp
      linarith
  have hp1 : ‖p‖ < 1 := by linarith
  let F : ℝ → Circle → ℂ := fun u w =>
    χ ((((1 - clampUnit u) : ℝ) : ℂ) * (p + (r : ℂ) * w) + (clampUnit u : ℂ) * w)
  have hF : Continuous fun q : ℝ × Circle => F q.1 q.2 := by
    have : Continuous fun q : ℝ × Circle =>
        (((1 - clampUnit q.1) : ℝ) : ℂ) * (p + (r : ℂ) * q.2) + (clampUnit q.1 : ℂ) * q.2 := by
      have := continuous_clampUnit
      fun_prop
    exact hχ.comp this
  have hne : ∀ u w, F u w ≠ χ p := by
    intro u w he
    set s := clampUnit u
    have hs := clampUnit_mem u
    have hmem : (((1 - s) : ℝ) : ℂ) * (p + (r : ℂ) * w) + (s : ℂ) * w ∈ closedBall (0 : ℂ) 1 := by
      rw [mem_closedBall_zero_iff]
      calc ‖(((1 - s) : ℝ) : ℂ) * (p + (r : ℂ) * w) + (s : ℂ) * w‖
          ≤ ‖(((1 - s) : ℝ) : ℂ) * (p + (r : ℂ) * w)‖ + ‖(s : ℂ) * w‖ := norm_add_le _ _
        _ ≤ (1 - s) * (‖p‖ + r) + s := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Circle.norm_coe,
            Real.norm_of_nonneg (sub_nonneg.mpr hs.2), Real.norm_of_nonneg hs.1, mul_one]
          gcongr
          · linarith [hs.2]
          · calc ‖p + (r : ℂ) * w‖ ≤ ‖p‖ + ‖(r : ℂ) * w‖ := norm_add_le _ _
              _ = ‖p‖ + r := by
                rw [norm_mul, Complex.norm_real, Circle.norm_coe, Real.norm_of_nonneg hr.le,
                  mul_one]
        _ ≤ 1 := by nlinarith [hs.1, hs.2]
    have hpm : p ∈ closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.mpr hp1.le
    have heq := hi hmem hpm he
    have h2 : ((((1 - s) * r + s : ℝ)) : ℂ) * w = (s : ℂ) * p := by
      push_cast at heq ⊢
      linear_combination heq
    have hn := congrArg norm h2
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Circle.norm_coe, mul_one,
      Real.norm_of_nonneg hs.1, Real.norm_of_nonneg (by nlinarith [hs.1, hs.2])] at hn
    have key : s * ‖p‖ < (1 - s) * r + s := by
      rcases eq_or_lt_of_le hs.1 with h0 | h0
      · nlinarith [h0, norm_nonneg p, hr]
      · have := mul_lt_mul_of_pos_left hp1 h0
        nlinarith [hs.2]
    linarith
  have h := wind_eq_of_family hF (z := fun _ => χ p) continuous_const hne 0 1
  simpa [F] using h

/-- Moving along the rays of a star-shaped boundary to a round circle keeps the winding. -/
theorem wind_star_eq_round (hχ : Continuous χ) (hi : InjOn χ (closedBall 0 1)) {p : ℂ}
    {ρ : Circle → ℝ} (hρc : Continuous ρ) (hρ : ∀ w, 0 < ρ w) {r : ℝ} (hr : 0 < r)
    (hmem : ∀ w (l : ℝ), min r (ρ w) ≤ l → l ≤ max r (ρ w) → p + (l : ℂ) * w ∈ closedBall 0 1)
    (hp : p ∈ closedBall (0 : ℂ) 1) :
    wind (fun w : Circle => χ (p + (ρ w : ℂ) * w)) (χ p) =
      wind (fun w : Circle => χ (p + (r : ℂ) * w)) (χ p) := by
  let lam : ℝ → Circle → ℝ := fun u w => (1 - clampUnit u) * ρ w + clampUnit u * r
  have hlam : ∀ u w, min r (ρ w) ≤ lam u w ∧ lam u w ≤ max r (ρ w) ∧ 0 < lam u w := by
    intro u w
    have hs := clampUnit_mem u
    refine ⟨?_, ?_, ?_⟩
    · have := min_le_left r (ρ w); have := min_le_right r (ρ w)
      simp only [lam]; nlinarith [hs.1, hs.2]
    · have := le_max_left r (ρ w); have := le_max_right r (ρ w)
      simp only [lam]; nlinarith [hs.1, hs.2]
    · simp only [lam]
      rcases eq_or_lt_of_le hs.1 with h0 | h0
      · rw [← h0]; simp [hρ w]
      · nlinarith [hρ w, hs.2]
  let F : ℝ → Circle → ℂ := fun u w => χ (p + (lam u w : ℂ) * w)
  have hF : Continuous fun q : ℝ × Circle => F q.1 q.2 := by
    have := continuous_clampUnit
    have : Continuous fun q : ℝ × Circle => p + (lam q.1 q.2 : ℂ) * q.2 := by
      simp only [lam]; fun_prop
    exact hχ.comp this
  have hne : ∀ u w, F u w ≠ χ p := by
    intro u w he
    obtain ⟨h1, h2, h3⟩ := hlam u w
    have heq := hi (hmem w _ h1 h2) hp he
    have : (lam u w : ℂ) * w = 0 := by linear_combination heq
    rcases mul_eq_zero.mp this with h | h
    · exact h3.ne' (by exact_mod_cast h)
    · exact Circle.coe_ne_zero w h
  have h := wind_eq_of_family hF (z := fun _ => χ p) continuous_const hne 0 1
  simpa [F, lam] using h

/-- **Convex pieces of a positive chart.** Let `χ` be injective and continuous on the closed
unit disc, with the boundary circle winding positively around `χ 0`. Let `K` be a compact convex
subset of the closed unit disc with an interior point `p`. Then `χ '' K` is a closed disc, and
three boundary points of `K` keep their counterclockwise order, seen from `p`, in `χ '' K`. -/
theorem planePos_chart_convex (hχ : Continuous χ) (hi : InjOn χ (closedBall 0 1))
    (hpos : 0 < wind (fun w : Circle => χ w) (χ 0)) {K : Set ℂ} (hc : Convex ℝ K)
    (hcl : IsClosed K) (hK : K ⊆ closedBall 0 1) {p : ℂ} (hp : p ∈ interior K) :
    IsClosedDisc (χ '' K) ∧ discBd (χ '' K) = χ '' frontier K ∧
    ∀ a ∈ frontier K, ∀ b ∈ frontier K, ∀ c ∈ frontier K, ∀ (ha : a - p ≠ 0) (hb : b - p ≠ 0)
      (hc' : c - p ≠ 0),
      (planePos (χ '' K) (χ a) (χ b) (χ c) ↔
        CircleCyclic (unitOf (a - p) ha) (unitOf (b - p) hb) (unitOf (c - p) hc')) := by
  have hbK : Bornology.IsBounded K := (isBounded_closedBall).subset hK
  obtain ⟨hKd, hKbd⟩ := isClosedDisc_of_convex hc ⟨p, hp⟩ hbK hcl
  have hiK : InjOn χ K := hi.mono hK
  obtain ⟨hD, hDbd⟩ := IsClosedDisc.image_injOn hKd hχ.continuousOn hiK
  rw [hKbd] at hDbd
  obtain ⟨ρ, hρc, hρ, hρfr, hρseg, hρrep⟩ := exists_radial_of_convex hc hbK hcl hp
  let φ : Circle → ℂ := fun w => χ (p + (ρ w : ℂ) * w)
  have hpK : p ∈ K := interior_subset hp
  have hfrK : frontier K ⊆ K := hcl.frontier_subset
  have hφc : Continuous φ := hχ.comp (by fun_prop)
  have hbase_inj : Function.Injective fun w : Circle => p + (ρ w : ℂ) * w := by
    intro w w' h
    have h' : (ρ w : ℂ) * w = (ρ w' : ℂ) * w' := add_left_cancel h
    have hn := congrArg norm h'
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Circle.norm_coe, Circle.norm_coe,
      Real.norm_of_nonneg (hρ w).le, Real.norm_of_nonneg (hρ w').le] at hn
    simp only [mul_one] at hn
    rw [hn] at h'
    exact Circle.ext (mul_left_cancel₀ (by exact_mod_cast (hρ w').ne') h')
  have hφi : Function.Injective φ := fun w w' h =>
    hbase_inj (hiK (hfrK (hρfr w)) (hfrK (hρfr w')) h)
  have hφr : range φ = discBd (χ '' K) := by
    rw [hDbd]
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨_, hρfr w, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨hq0, hqe⟩ := hρrep q hq
      exact ⟨unitOf (q - p) hq0, by simp only [φ]; rw [← hqe]⟩
  have hoff : ∀ w, φ w ≠ χ p := by
    intro w he
    have := hiK (hfrK (hρfr w)) hpK he
    have hz : (ρ w : ℂ) * w = 0 := by linear_combination this
    rcases mul_eq_zero.mp hz with h | h
    · exact (hρ w).ne' (by exact_mod_cast h)
    · exact Circle.coe_ne_zero w h
  have hpint : χ p ∈ discInt (χ '' K) := by
    refine ⟨⟨p, hpK, rfl⟩, ?_⟩
    rw [← hφr]
    rintro ⟨w, hw⟩
    exact hoff w hw
  obtain ⟨r, hr, hrK⟩ : ∃ r > 0, closedBall p r ⊆ K := by
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hp)
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hball⟩
  have hround : ∀ w : Circle, p + (r : ℂ) * w ∈ K := fun w => hrK (by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Circle.norm_coe, mul_one, Real.norm_of_nonneg hr.le])
  have hseg : ∀ w (l : ℝ), min r (ρ w) ≤ l → l ≤ max r (ρ w) → p + (l : ℂ) * w ∈ closedBall 0 1 := by
    intro w l h1 h2
    apply hK
    rcases le_total r (ρ w) with h | h
    · rw [min_eq_left h] at h1
      rw [max_eq_right h] at h2
      exact hρseg w l (hr.le.trans h1) h2
    · rw [min_eq_right h] at h1
      rw [max_eq_left h] at h2
      -- `l` lies between `ρ w` and `r`: a convex combination of two points of `K`
      have hl0 : 0 ≤ l := (hρ w).le.trans h1
      by_cases hlr : l ≤ ρ w
      · exact hρseg w l hl0 hlr
      · have hρr : ρ w < r := lt_of_lt_of_le (not_le.mp hlr) h2
        have hpt : p + (l : ℂ) * w ∈ closedBall p r := by
          rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
            Circle.norm_coe, mul_one, Real.norm_of_nonneg hl0]
          exact h2
        exact hrK hpt
  have hwind : 0 < wind φ (χ p) := by
    have hpb : p ∈ ball (0 : ℂ) 1 := by
      have := hrK (show p + (r : ℂ) ∈ closedBall p r by
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
          Real.norm_of_nonneg hr.le])
      have h1 := hK this
      rw [mem_closedBall_zero_iff] at h1
      rw [mem_ball_zero_iff]
      by_contra hp1
      push Not at hp1
      -- the point `p + r p/‖p‖` would leave the unit disc
      have hp0 : p ≠ 0 := by
        intro h; rw [h, norm_zero] at hp1; linarith
      have hpn : 0 < ‖p‖ := norm_pos_iff.mpr hp0
      have hq := hK (hrK (show p + ((r / ‖p‖ : ℝ) : ℂ) * p ∈ closedBall p r by
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (div_nonneg hr.le hpn.le), div_mul_cancel₀ _ hpn.ne']))
      rw [mem_closedBall_zero_iff] at hq
      have hq' : p + ((r / ‖p‖ : ℝ) : ℂ) * p = ((1 + r / ‖p‖ : ℝ) : ℂ) * p := by
        push_cast; ring
      rw [hq', norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + r / ‖p‖)] at hq
      have : (1 + r / ‖p‖) * ‖p‖ = ‖p‖ + r := by field_simp
      linarith
    have hsub : closedBall p r ⊆ closedBall 0 1 := fun z hz => hK (hrK hz)
    have e1 := wind_star_eq_round hχ hi hρc hρ hr hseg (hK hpK)
    have e2 := wind_round_eq_circle hχ hi hr hsub
    have e3 := wind_circle_eq_centre hχ hi hpb
    change 0 < wind (fun w : Circle => χ (p + (ρ w : ℂ) * w)) (χ p)
    rw [e1, e2, e3]
    exact hpos
  have hpos' : IsPosParam (χ '' K) φ := by
    rcases isPosParam_or_inv hD hφc hφi hφr with h | h
    · exact h
    · have h2 := h.2.2.2 _ hpint
      rw [wind_inv hφc hoff] at h2
      linarith
  refine ⟨hD, hDbd, fun a ha b hb c hc' ha0 hb0 hc0 => ?_⟩
  have hrep : ∀ q ∈ frontier K, ∀ hq0 : q - p ≠ 0, φ (unitOf (q - p) hq0) = χ q := by
    intro q hq hq0
    obtain ⟨hq1, hqe⟩ := hρrep q hq
    simp only [φ]
    rw [← hqe]
  rw [← hrep a ha ha0, ← hrep b hb hb0, ← hrep c hc' hc0]
  exact ⟨fun ⟨φ', _, _, _, hφ', h1, h2, h3, hcy⟩ =>
      order_of_nested hD hD subset_rfl hφ' hpos' hcy h1 h2 h3,
    fun h => ⟨φ, _, _, _, hpos', rfl, rfl, rfl, h⟩⟩

end Chart

end GraphMinor.GM06
