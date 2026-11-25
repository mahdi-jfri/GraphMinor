module

public import GraphMinor.GHR18.ParitySurgery

/-!
# Arc thickening and band-surgery along a multi-crossing arc (GHR18 Theorem 2.6, Step 2a)

This file develops the geometric engine for Step 2 of Geelen–Huynh–Richter (2018), Theorem 2.6:
given a proper 1-manifold `M` and a simple interior arc `γ_ext` connecting two distinct components
`C₁ ≠ C₂` of `M` while crossing `k` pairwise disjoint proper `I`-arcs `Q_{i_1}, ..., Q_{i_k}`
(all disjoint from `M.U`) transversely once each, we thicken `γ_ext` to an embedded interior
closed rectangle `Δ` whose left/right vertical sides lie on `C₁, C₂` and whose intersection with
each `Q_{i_r}` is a single vertical segment `{x_r} × [-η, η]`, and apply `rectangle_surgery`.

## Main results
1. `exists_disc_cross_straightener`: given a closed disc `E ⊆ ℂ` split by a horizontal chord
   `H = [a, b] × {0}` into `E₁, E₂` and two half-chords `F₁ ⊆ E₁`, `F₂ ⊆ E₂` meeting `H` at
   `x₀ ∈ (a, b)`, produces a homeomorphism `α : ℂ ≃ₜ ℂ` fixing `(discInt E)ᶜ ∪ H` pointwise such
   that `α '' (F₁ ∪ F₂)` is a straight vertical segment `{x₀} × [-η₀, η₀]` in a square around `x₀`.
2. `IsSimpleCrossing`: local `+`-crossing condition for `M.U` and `Q i`.
3. `RectCross`, `BandArcData`, and `band_surgery_along_arc`: executes `rectangle_surgery` along a
   transverse crossing arc `γ_ext`, strictly decreasing `M.Os.length` by `1`, preserving
   `w1Total AS` and `BdCohRel s t`, leaving `M.U ∩ Q j` and `IsSimpleCrossing` untouched outside
   `range idxs`, and creating `2` simple crossings on each `Q (idxs r)`.
-/

@[expose] public section

namespace GraphMinor.GHR18

open Set Metric Topology Complex GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM11

variable {S : Type} [TopologicalSpace S]

/-! ### Section 1: Pure 2D chord straightening inside a split closed disc -/

section ChordStraightener

/-- Any point inside an open ball contained in a set `E ⊆ ℂ` is an interior point of `E`. -/
private theorem isInteriorPoint_of_ball_subset {E : Set ℂ} {z : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hsub : ball z δ ⊆ E) (hz : z ∈ E) : IsInteriorPoint (⟨z, hz⟩ : E) := by
  refine ⟨Subtype.val ⁻¹' ball z δ, isOpen_ball.preimage continuous_subtype_val, mem_ball_self hδ, ?_⟩
  have hC_eq : (Subtype.val ⁻¹' ball z δ : Set E) ≃ₜ ball z δ :=
    { toFun := fun w => ⟨w.1.1, w.2⟩
      invFun := fun w => ⟨⟨w.1, hsub w.2⟩, w.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
      continuous_invFun := Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _ }
  obtain ⟨hball_eq⟩ := exists_homeomorph_ball z hδ
  exact ⟨hC_eq.trans hball_eq⟩

/-- Half-disc vertical chord builder: inside a closed disc `Ep ⊆ ℂ` whose boundary contains
`(x₀ : ℂ)` and `u ≠ (x₀ : ℂ)`, and which contains the open half-ball
`{z ∈ closedBall x₀ ρ | 0 < σ * z.im}` in its interior `discInt Ep`, builds a proper chord
`F'` of `Ep` from `(x₀ : ℂ)` to `u` that coincides with the vertical half-segment
`{x₀} × [0, σ * η]` inside `closedBall (x₀ : ℂ) η` for some `η > 0`. -/
private theorem exists_half_disc_vertical_chord {Ep : Set ℂ} (hE : IsClosedDisc Ep)
    {x₀ ρ σ : ℝ} (hρ : 0 < ρ) (hσ : σ = 1 ∨ σ = -1)
    {u : ℂ} (hx₀bd : (x₀ : ℂ) ∈ discBd Ep) (hubd : u ∈ discBd Ep) (hux : u ≠ (x₀ : ℂ))
    (hhalf : ∀ z ∈ closedBall (x₀ : ℂ) ρ, 0 < σ * z.im → z ∈ discInt Ep) :
    ∃ (F' : Set ℂ) (η : ℝ), 0 < η ∧ η ≤ ρ / 2 ∧
      F' ⊆ Ep ∧ IsLineWithEnds F' (x₀ : ℂ) u ∧ F' ∩ discBd Ep = {(x₀ : ℂ), u} ∧
      F' ∩ closedBall (x₀ : ℂ) η =
        {z : ℂ | z.re = x₀ ∧ 0 ≤ σ * z.im ∧ σ * z.im ≤ η} := by
  have hσ_sq : σ * σ = 1 := hσ.elim (fun h => by rw [h]; norm_num) (fun h => by rw [h]; norm_num)
  have hσ_ne : σ ≠ 0 := hσ.elim (fun h => by rw [h]; norm_num) (fun h => by rw [h]; norm_num)
  have hσ_abs : |σ| = 1 := hσ.elim (fun h => by rw [h]; norm_num) (fun h => by rw [h]; norm_num)
  let wp : ℂ := (x₀ : ℂ) + ((σ * (ρ / 2) : ℝ) : ℂ) * I
  let Vp : Set ℂ := {z : ℂ | z.re = x₀ ∧ 0 ≤ σ * z.im ∧ σ * z.im ≤ ρ / 2}
  have hV_sub_cb : Vp ⊆ closedBall (x₀ : ℂ) ρ := fun z hz => by
    rw [mem_closedBall, dist_eq_norm]
    have hsub : z - (x₀ : ℂ) = (z.im : ℂ) * I := Complex.ext (by simp [hz.1]) (by simp)
    rw [hsub, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have habs : |z.im| = σ * z.im := by
      calc |z.im| = |σ| * |z.im| := by rw [hσ_abs, one_mul]
        _ = |σ * z.im| := (abs_mul σ z.im).symm
        _ = σ * z.im := abs_of_nonneg hz.2.1
    linarith [hz.2.2]
  have hV_int : ∀ z ∈ Vp, z ≠ (x₀ : ℂ) → z ∈ discInt Ep := fun z hz hne => by
    refine hhalf z (hV_sub_cb hz) ?_
    refine lt_of_le_of_ne hz.2.1 fun h0 => hne (Complex.ext (by simpa using hz.1) ?_)
    have : z.im = 0 := (mul_eq_zero.mp h0.symm).resolve_left hσ_ne
    simpa using this
  have hwp_V : wp ∈ Vp := by
    refine ⟨by simp [wp], ?_, ?_⟩ <;> simp only [wp, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero, zero_add, add_zero]
    · rw [← mul_assoc, hσ_sq, one_mul]; linarith
    · rw [← mul_assoc, hσ_sq, one_mul]
  have hwp_ne : wp ≠ (x₀ : ℂ) := fun h => by
    have := congrArg Complex.im h
    simp only [wp, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero, zero_add, add_zero] at this
    exact (mul_ne_zero hσ_ne (half_pos hρ).ne') this
  have hwp_int : wp ∈ discInt Ep := hV_int wp hwp_V hwp_ne
  obtain ⟨h, g, c⟩ := hE.exists_isChart
  let zu : ℂ := h u
  let zw : ℂ := h wp
  have hzu_norm : ‖zu‖ = 1 := mem_sphere_zero_iff_norm.mp (c.bd ▸ ⟨u, hubd, rfl⟩)
  have hzw_norm : ‖zw‖ < 1 := by
    refine lt_of_le_of_ne (mem_closedBall_zero_iff.mp (c.hm hwp_int.1)) fun h1 => hwp_int.2 ?_
    obtain ⟨y, hybd, hy⟩ := (c.bd.symm ▸ mem_sphere_zero_iff_norm.mpr h1 : zw ∈ h '' discBd Ep)
    have := c.gh (GraphMinor.Surface.discBd_subset Ep hybd)
    rw [hy, c.gh hwp_int.1] at this
    exact this ▸ hybd
  have hzu_ne_zw : zu ≠ zw := fun h => by linarith [h ▸ hzu_norm]
  let seg : ℝ → ℂ := fun t => ((1 - t : ℝ) : ℂ) * zu + (t : ℂ) * zw
  let lam : ℝ → ℂ := fun t => g (seg t)
  have hseg_c : Continuous seg := by fun_prop
  have hseg_cb : ∀ t ∈ Icc (0 : ℝ) 1, seg t ∈ closedBall (0 : ℂ) 1 := fun t ht => by
    rw [mem_closedBall_zero_iff]
    calc ‖seg t‖ ≤ ‖((1 - t : ℝ) : ℂ) * zu‖ + ‖(t : ℂ) * zw‖ := norm_add_le _ _
      _ = (1 - t) * ‖zu‖ + t * ‖zw‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (by linarith [ht.2]), abs_of_nonneg ht.1]
      _ ≤ (1 - t) * 1 + t * 1 := by rw [hzu_norm]; nlinarith [ht.1, hzw_norm]
      _ = 1 := by ring
  have hseg_ball : ∀ t ∈ Ioc (0 : ℝ) 1, seg t ∈ ball (0 : ℂ) 1 := fun t ht => by
    rw [mem_ball_zero_iff]
    calc ‖seg t‖ ≤ ‖((1 - t : ℝ) : ℂ) * zu‖ + ‖(t : ℂ) * zw‖ := norm_add_le _ _
      _ = (1 - t) * ‖zu‖ + t * ‖zw‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (by linarith [ht.2]), abs_of_nonneg ht.1.le]
      _ < (1 - t) * 1 + t * 1 := by rw [hzu_norm]; nlinarith [ht.1, hzw_norm]
      _ = 1 := by ring
  have hseg_i : Function.Injective seg := fun t₁ t₂ he => by
    have h1 : ((t₁ - t₂ : ℝ) : ℂ) * (zw - zu) = 0 := by
      have : seg t₁ - seg t₂ = ((t₁ - t₂ : ℝ) : ℂ) * (zw - zu) := by dsimp only [seg]; push_cast; ring
      rw [← this, he, sub_self]
    rcases mul_eq_zero.mp h1 with h2 | h2
    · linarith [Complex.ofReal_eq_zero.mp h2]
    · exact (hzu_ne_zw (sub_eq_zero.mp h2).symm).elim
  have hlam_c : ContinuousOn lam (Icc 0 1) := c.gc.comp hseg_c.continuousOn hseg_cb
  have hlam_i : InjOn lam (Icc 0 1) := fun t₁ ht₁ t₂ ht₂ he =>
    hseg_i (by have := congrArg h he; rwa [c.hg (hseg_cb t₁ ht₁), c.hg (hseg_cb t₂ ht₂)] at this)
  have hlam_0 : lam 0 = u := by
    simp only [lam, seg, sub_zero, ofReal_one, one_mul, ofReal_zero, zero_mul, add_zero, zu]
    exact c.gh (GraphMinor.Surface.discBd_subset Ep hubd)
  have hlam_1 : lam 1 = wp := by
    simp only [lam, seg, sub_self, ofReal_zero, zero_mul, ofReal_one, one_mul, zero_add, zw]
    exact c.gh hwp_int.1
  have hlam_sub : ∀ t ∈ Icc (0 : ℝ) 1, lam t ∈ Ep := fun t ht => c.gm (hseg_cb t ht)
  have hlam_int : ∀ t ∈ Ioc (0 : ℝ) 1, lam t ∈ discInt Ep := fun t ht => by
    refine ⟨hlam_sub t ⟨ht.1.le, ht.2⟩, fun hbd => ?_⟩
    have h1 : seg t ∈ sphere (0 : ℂ) 1 := by
      have : h (lam t) ∈ sphere (0 : ℂ) 1 := c.bd ▸ ⟨lam t, hbd, rfl⟩
      rwa [c.hg (hseg_cb t ⟨ht.1.le, ht.2⟩)] at this
    exact (ne_of_lt (mem_ball_zero_iff.mp (hseg_ball t ht))) (mem_sphere_zero_iff_norm.mp h1)
  have hV_closed : IsClosed Vp :=
    (isClosed_eq continuous_re continuous_const).inter
      ((isClosed_le continuous_const (continuous_const.mul continuous_im)).inter
        (isClosed_le (continuous_const.mul continuous_im) continuous_const))
  let T : Set ℝ := Icc (0 : ℝ) 1 ∩ lam ⁻¹' Vp
  have hT_closed : IsClosed T := by
    rw [isClosed_iff_forall_filter]
    intro x F _ hFT hFx
    have hFT' : T ∈ F := Filter.le_principal_iff.mp hFT
    have hxIcc : x ∈ Icc (0 : ℝ) 1 := isClosed_Icc.mem_of_tendsto hFx (Filter.mem_of_superset hFT' fun _ h => h.1)
    have hlim : Filter.Tendsto lam F (𝓝 (lam x)) :=
      (hlam_c.continuousWithinAt hxIcc).tendsto.mono_left
        (le_inf hFx (Filter.le_principal_iff.mpr (Filter.mem_of_superset hFT' fun _ h => h.1)))
    exact ⟨hxIcc, hV_closed.mem_of_tendsto hlim (Filter.mem_of_superset hFT' fun _ h => h.2)⟩
  have h1T : (1 : ℝ) ∈ T := ⟨⟨zero_le_one, le_rfl⟩, show lam 1 ∈ Vp from hlam_1.symm ▸ hwp_V⟩
  have h0_notT : (0 : ℝ) ∉ T := fun h => (hV_int u (hlam_0 ▸ h.2) hux).2 hubd
  let t₀ : ℝ := sInf T
  have hT_bdd : BddBelow T := ⟨0, fun _ h => h.1.1⟩
  have ht₀_mem : t₀ ∈ T := hT_closed.csInf_mem ⟨1, h1T⟩ hT_bdd
  have ht₀_pos : 0 < t₀ := lt_of_le_of_ne ht₀_mem.1.1 (fun h => h0_notT (h ▸ ht₀_mem))
  have ht₀_le1 : t₀ ≤ 1 := ht₀_mem.1.2
  have hlam_t₀_int : lam t₀ ∈ discInt Ep := hlam_int t₀ ⟨ht₀_pos, ht₀_le1⟩
  have hlam_t₀_ne : lam t₀ ≠ (x₀ : ℂ) := fun h => hlam_t₀_int.2 (h ▸ hx₀bd)
  have hlam_t₀_re : (lam t₀).re = x₀ := ht₀_mem.2.1
  have hy₀_pos : 0 < σ * (lam t₀).im := lt_of_le_of_ne ht₀_mem.2.2.1 fun h0 =>
    hlam_t₀_ne (Complex.ext (by simpa using hlam_t₀_re) (by
      have : (lam t₀).im = 0 := (mul_eq_zero.mp h0.symm).resolve_left hσ_ne
      simpa using this))
  have hy₀_le : σ * (lam t₀).im ≤ ρ / 2 := ht₀_mem.2.2.2
  have hlam_off_V : ∀ t ∈ Ico (0 : ℝ) t₀, lam t ∉ Vp := fun t ht hV =>
    not_lt_of_ge (csInf_le hT_bdd ⟨⟨ht.1, ht.2.le.trans ht₀_le1⟩, hV⟩) ht.2
  let seg_v : ℝ → ℂ := fun r => (x₀ : ℂ) + ((r * (lam t₀).im : ℝ) : ℂ) * I
  let seg_lam : ℝ → ℂ := fun r => lam (lin t₀ 0 r)
  let γ : ℝ → ℂ := conc2 seg_v seg_lam
  have hv_c : ContinuousOn seg_v (Icc 0 1) := by fun_prop
  have hv_i : InjOn seg_v (Icc 0 1) := fun r₁ _ r₂ _ he => by
    have h1 := congrArg Complex.im he
    simp only [seg_v, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero, zero_add, add_zero] at h1
    have him_ne : (lam t₀).im ≠ 0 := fun h0 => by rw [h0, mul_zero] at hy₀_pos; exact lt_irrefl _ hy₀_pos
    exact mul_right_cancel₀ him_ne h1
  have hv_0 : seg_v 0 = (x₀ : ℂ) := by simp [seg_v]
  have hv_1 : seg_v 1 = lam t₀ := by apply Complex.ext <;> simp [seg_v, hlam_t₀_re]
  have hv_in_V : ∀ r ∈ Icc (0 : ℝ) 1, seg_v r ∈ Vp := fun r hr => by
    refine ⟨by simp [seg_v], ?_, ?_⟩ <;>
      simp only [seg_v, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero, zero_add, add_zero]
    · rw [show σ * (r * (lam t₀).im) = r * (σ * (lam t₀).im) by ring]; nlinarith [hr.1, hy₀_pos]
    · rw [show σ * (r * (lam t₀).im) = r * (σ * (lam t₀).im) by ring]; nlinarith [hr.2, hy₀_pos, hy₀_le]
  have hlin_maps : MapsTo (lin t₀ 0) (Icc 0 1) (Icc 0 1) := fun r hr => by
    simp only [lin, mem_Icc]; constructor <;> nlinarith [hr.1, hr.2, ht₀_pos, ht₀_le1]
  have hlin_inj : InjOn (lin t₀ 0) (Icc 0 1) := fun r₁ _ r₂ _ he => by
    simp only [lin] at he; nlinarith [ht₀_pos]
  have hsl_c : ContinuousOn seg_lam (Icc 0 1) :=
    hlam_c.comp (by unfold lin; fun_prop : ContinuousOn (lin t₀ 0) (Icc 0 1)) hlin_maps
  have hsl_i : InjOn seg_lam (Icc 0 1) := fun r₁ hr₁ r₂ hr₂ he =>
    hlin_inj hr₁ hr₂ (hlam_i (hlin_maps hr₁) (hlin_maps hr₂) he)
  have hsl_0 : seg_lam 0 = lam t₀ := by simp [seg_lam, lin_zero]
  have hsl_1 : seg_lam 1 = u := by simp [seg_lam, lin_one, hlam_0]
  have hγ_c : ContinuousOn γ (Icc 0 1) := continuousOn_conc2 hv_c hsl_c (hv_1.trans hsl_0.symm)
  have hγ_i : InjOn γ (Icc 0 1) := conc2_injOn_Icc hv_i hsl_i fun r₁ hr₁ r₂ hr₂ he => by
    rcases hr₂.1.eq_or_lt with rfl | hr₂pos
    · exact ⟨hv_i hr₁ ⟨zero_le_one, le_rfl⟩ (he.trans (hsl_0.trans hv_1.symm)), rfl⟩
    · have hlin_lt : lin t₀ 0 r₂ ∈ Ico (0 : ℝ) t₀ := by
        simp only [lin, mem_Ico]; exact ⟨by nlinarith [hr₂.2, ht₀_pos], by nlinarith [hr₂pos, ht₀_pos]⟩
      have he' : lam (lin t₀ 0 r₂) = seg_v r₁ := he.symm
      exact (hlam_off_V _ hlin_lt (he' ▸ hv_in_V r₁ hr₁)).elim
  have hγ_0 : γ 0 = (x₀ : ℂ) := (conc2_zero seg_v seg_lam).trans hv_0
  have hγ_1 : γ 1 = u := (conc2_one seg_v seg_lam).trans hsl_1
  have hγ_im : γ '' Icc 0 1 = seg_v '' Icc 0 1 ∪ seg_lam '' Icc 0 1 := conc2_image (hv_1.trans hsl_0.symm)
  have hγ_sub : γ '' Icc 0 1 ⊆ Ep := by
    rw [hγ_im]; rintro _ (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩)
    · by_cases hr0 : r = 0
      · rw [hr0, hv_0]; exact GraphMinor.Surface.discBd_subset Ep hx₀bd
      · exact (hV_int _ (hv_in_V r hr) (fun h => hr0 (hv_i hr ⟨le_rfl, zero_le_one⟩ (h.trans hv_0.symm)))).1
    · exact hlam_sub _ (hlin_maps hr)
  have hγ_bd : (γ '' Icc 0 1) ∩ discBd Ep = {(x₀ : ℂ), u} := by
    ext z; constructor
    · rintro ⟨hz, hzbd⟩; rw [hγ_im] at hz
      rcases hz with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
      · by_cases hr0 : r = 0
        · exact Or.inl (by rw [hr0, hv_0])
        · exact ((hV_int _ (hv_in_V r hr) (fun h => hr0 (hv_i hr ⟨le_rfl, zero_le_one⟩ (h.trans hv_0.symm)))).2 hzbd).elim
      · by_cases hr1 : r = 1
        · exact Or.inr (mem_singleton_iff.mpr (by rw [hr1, hsl_1]))
        · have hlt : 0 < lin t₀ 0 r := by simp only [lin]; nlinarith [lt_of_le_of_ne hr.2 hr1, ht₀_pos]
          exact ((hlam_int _ ⟨hlt, (hlin_maps hr).2⟩).2 hzbd).elim
    · rintro (rfl | rfl)
      · exact ⟨⟨0, ⟨le_rfl, zero_le_one⟩, hγ_0⟩, hx₀bd⟩
      · exact ⟨⟨1, ⟨zero_le_one, le_rfl⟩, hγ_1⟩, hubd⟩
  have hx₀_not_sl : (x₀ : ℂ) ∉ seg_lam '' Icc 0 1 := by
    rintro ⟨r, hr, he⟩
    by_cases hr1 : r = 1
    · rw [hr1, hsl_1] at he; exact hux he
    · have hlt : 0 < lin t₀ 0 r := by simp only [lin]; nlinarith [lt_of_le_of_ne hr.2 hr1, ht₀_pos]
      have he' : lam (lin t₀ 0 r) = (x₀ : ℂ) := he
      exact (hlam_int _ ⟨hlt, (hlin_maps hr).2⟩).2 (he' ▸ hx₀bd)
  have hsl_closed : IsClosed (seg_lam '' Icc 0 1) := (isCompact_Icc.image_of_continuousOn hsl_c).isClosed
  obtain ⟨η₁, hη₁, hball_disj⟩ := Metric.isOpen_iff.mp hsl_closed.isOpen_compl (x₀ : ℂ) hx₀_not_sl
  let η : ℝ := min (σ * (lam t₀).im) (min (η₁ / 2) (ρ / 2))
  have hη_pos : 0 < η := lt_min hy₀_pos (lt_min (half_pos hη₁) (half_pos hρ))
  have hη_le_y₀ : η ≤ σ * (lam t₀).im := min_le_left _ _
  have hη_lt_η₁ : η < η₁ := (min_le_right _ _).trans_lt ((min_le_left _ _).trans_lt (half_lt_self hη₁))
  have hη_le_ρ2 : η ≤ ρ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨γ '' Icc 0 1, η, hη_pos, hη_le_ρ2, hγ_sub, isLineWithEnds_of_param hγ_c hγ_i hγ_0 hγ_1 rfl, hγ_bd, ?_⟩
  ext z; constructor
  · rintro ⟨hzγ, hzcb⟩
    rw [hγ_im] at hzγ
    rcases hzγ with ⟨r, hr, rfl⟩ | hzsl
    · refine ⟨by simp [seg_v], (hv_in_V r hr).2.1, ?_⟩
      have hd : ‖seg_v r - (x₀ : ℂ)‖ ≤ η := by simpa [mem_closedBall, dist_eq_norm] using hzcb
      have hsub : seg_v r - (x₀ : ℂ) = ((r * (lam t₀).im : ℝ) : ℂ) * I := by simp [seg_v]
      rw [hsub, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at hd
      have hnonneg : 0 ≤ σ * (seg_v r).im := (hv_in_V r hr).2.1
      have him : (seg_v r).im = r * (lam t₀).im := by simp [seg_v]
      have habs : |r * (lam t₀).im| = σ * (seg_v r).im := by
        rw [← him]
        calc |(seg_v r).im| = |σ| * |(seg_v r).im| := by rw [hσ_abs, one_mul]
          _ = |σ * (seg_v r).im| := (abs_mul σ _).symm
          _ = σ * (seg_v r).im := abs_of_nonneg hnonneg
      linarith
    · exact (hball_disj (closedBall_subset_ball hη_lt_η₁ hzcb) hzsl).elim
  · rintro ⟨hzre, hz0, hzη⟩
    have hcb : z ∈ closedBall (x₀ : ℂ) η := by
      rw [mem_closedBall, dist_eq_norm]
      have hsub : z - (x₀ : ℂ) = (z.im : ℂ) * I := Complex.ext (by simp [hzre]) (by simp)
      rw [hsub, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      have habs : |z.im| = σ * z.im := by
        calc |z.im| = |σ| * |z.im| := by rw [hσ_abs, one_mul]
          _ = |σ * z.im| := (abs_mul σ _).symm
          _ = σ * z.im := abs_of_nonneg hz0
      linarith
    refine ⟨?_, hcb⟩
    rw [hγ_im]; left
    let r : ℝ := (σ * z.im) / (σ * (lam t₀).im)
    refine ⟨r, ⟨div_nonneg hz0 hy₀_pos.le, (div_le_one hy₀_pos).mpr (hzη.trans hη_le_y₀)⟩, ?_⟩
    apply Complex.ext
    · simp [seg_v, hzre]
    · simp only [seg_v, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero, zero_add, add_zero, r]
      have hden : (lam t₀).im ≠ 0 := fun h0 => by rw [h0, mul_zero] at hy₀_pos; exact lt_irrefl _ hy₀_pos
      have h1 : σ * z.im / (σ * (lam t₀).im) = z.im / (lam t₀).im := mul_div_mul_left _ _ hσ_ne
      rw [h1, div_mul_cancel₀ _ hden]

/-- **Split-disc cross straightener**: given a closed disc `E ⊆ ℂ` split by a horizontal chord
`H = [a, b] × {0}` (`a < x₀ < b`) into two closed discs `E₁, E₂`, and two half-chords `F₁ ⊆ E₁`,
`F₂ ⊆ E₂` meeting `H` at `(x₀ : ℂ)` and `discBd E` at `u, v`, produces `η₀ > 0` and
`α : ℂ ≃ₜ ℂ` fixing `(discInt E)ᶜ ∪ H` pointwise such that `α '' (F₁ ∪ F₂)` is the exact vertical
segment `{x₀} × [-η₀, η₀]` inside the square `[x₀ - η₀, x₀ + η₀] × [-η₀, η₀] ⊆ discInt E`. -/
theorem exists_disc_cross_straightener {E E₁ E₂ F₁ F₂ : Set ℂ} {a b x₀ : ℝ} {u v : ℂ}
    (hE : IsClosedDisc E) (hax : a < x₀) (hxb : x₀ < b)
    (hE₁ : IsClosedDisc E₁) (hE₂ : IsClosedDisc E₂)
    (hEu : E₁ ∪ E₂ = E) (hEi : E₁ ∩ E₂ = Icc a b ×ℂ ({0} : Set ℝ))
    (hHsub : Icc a b ×ℂ ({0} : Set ℝ) ⊆ E)
    (hHbd : (Icc a b ×ℂ ({0} : Set ℝ)) ∩ discBd E = {(a : ℂ), (b : ℂ)})
    (hF₁sub : F₁ ⊆ E₁) (hF₂sub : F₂ ⊆ E₂)
    (hF₁l : IsLineWithEnds F₁ (x₀ : ℂ) u) (hF₂l : IsLineWithEnds F₂ (x₀ : ℂ) v)
    (hF₁bd : F₁ ∩ discBd E₁ = {(x₀ : ℂ), u}) (hF₂bd : F₂ ∩ discBd E₂ = {(x₀ : ℂ), v})
    (hux : u ≠ (x₀ : ℂ)) (hvx : v ≠ (x₀ : ℂ)) :
    ∃ (η₀ : ℝ) (α : ℂ ≃ₜ ℂ), 0 < η₀ ∧
      Icc (x₀ - η₀) (x₀ + η₀) ×ℂ Icc (-η₀) η₀ ⊆ discInt E ∧
      (∀ z ∈ (discInt E)ᶜ, α z = z) ∧
      (∀ z ∈ Icc a b ×ℂ ({0} : Set ℝ), α z = z) ∧
      (α '' (F₁ ∪ F₂)) ∩ (Icc (x₀ - η₀) (x₀ + η₀) ×ℂ Icc (-η₀) η₀) =
        ({x₀} : Set ℝ) ×ℂ Icc (-η₀) η₀ := by
  let H : Set ℂ := Icc a b ×ℂ ({0} : Set ℝ)
  have hman : ∀ z : ℂ, IsManifoldPoint z := isManifoldPoint_complex
  have hx₀H : (x₀ : ℂ) ∈ H := Complex.mem_reProdIm.mpr ⟨⟨hax.le, hxb.le⟩, rfl⟩
  have hx₀_intE : (x₀ : ℂ) ∈ discInt E := by
    refine ⟨hHsub hx₀H, fun hbd => ?_⟩
    have hm : (x₀ : ℂ) ∈ ({(a : ℂ), (b : ℂ)} : Set ℂ) := hHbd ▸ ⟨hx₀H, hbd⟩
    rcases hm with h | h
    · exact hax.ne' (Complex.ofReal_injective h)
    · exact hxb.ne (Complex.ofReal_injective (mem_singleton_iff.mp h))
  have hdiscInt_open : IsOpen (discInt E) := isOpen_discInt hman hE
  obtain ⟨r₁, hr₁, hr₁sub⟩ := Metric.isOpen_iff.mp hdiscInt_open (x₀ : ℂ) hx₀_intE
  let ρ : ℝ := min (r₁ / 2) (min ((x₀ - a) / 2) ((b - x₀) / 2))
  have hρ : 0 < ρ := lt_min (half_pos hr₁) (lt_min (half_pos (by linarith)) (half_pos (by linarith)))
  have hcb_sub : closedBall (x₀ : ℂ) ρ ⊆ discInt E :=
    (closedBall_subset_ball ((min_le_left _ _).trans_lt (half_lt_self hr₁))).trans hr₁sub
  have hupper_conn : IsPreconnected {z ∈ closedBall (x₀ : ℂ) ρ | 0 < z.im} := by
    refine Convex.isPreconnected fun z hz w hw α β hα hβ hαβ => ?_
    refine ⟨(convex_closedBall (x₀ : ℂ) ρ) hz.1 hw.1 hα hβ hαβ, ?_⟩
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
    rcases hα.eq_or_lt with rfl | hαp
    · have : β = 1 := by linarith
      rw [this]; linarith [hw.2]
    · nlinarith [hz.2, hw.2, hβ]
  have hlower_conn : IsPreconnected {z ∈ closedBall (x₀ : ℂ) ρ | z.im < 0} := by
    refine Convex.isPreconnected fun z hz w hw α β hα hβ hαβ => ?_
    refine ⟨(convex_closedBall (x₀ : ℂ) ρ) hz.1 hw.1 hα hβ hαβ, ?_⟩
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
    rcases hα.eq_or_lt with rfl | hαp
    · have : β = 1 := by linarith
      rw [this]; linarith [hw.2]
    · nlinarith [hz.2, hw.2, hβ]
  have hE₁cl : IsClosed E₁ := hE₁.isCompact.isClosed
  have hE₂cl : IsClosed E₂ := hE₂.isCompact.isClosed
  have hside : ∀ {A : Set ℂ}, IsPreconnected A → A ⊆ closedBall (x₀ : ℂ) ρ → (∀ z ∈ A, z.im ≠ 0) →
      A ⊆ discInt E₁ ∨ A ⊆ discInt E₂ := fun {A} hAc hAsub hAim => by
    have hAcov : A ⊆ E₁ ∪ E₂ := hEu.symm ▸ hAsub.trans (hcb_sub.trans fun _ h => h.1)
    have hAdisj : A ∩ (E₁ ∩ E₂) = ∅ := by
      rw [eq_empty_iff_forall_notMem, hEi]; rintro z ⟨hzA, hzH⟩
      exact hAim z hzA (Complex.mem_reProdIm.mp hzH).2
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hAc E₁ E₂ hE₁cl hE₂cl hAcov hAdisj with h1 | h2
    · left; intro z hz
      refine ⟨h1 hz, fun hbd => ?_⟩
      have hznot2 : z ∉ E₂ := fun hz2 => by
        have hzH : z ∈ H := by dsimp only [H]; rw [← hEi]; exact ⟨h1 hz, hz2⟩
        exact hAim z hz (Complex.mem_reProdIm.mp hzH).2
      obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp (hdiscInt_open.sdiff hE₂cl) z ⟨hcb_sub (hAsub hz), hznot2⟩
      obtain ⟨⟨y, hyE⟩, hybd, hyval⟩ := hbd; dsimp only at hyval; subst hyval
      have hsub1 : ball y δ ⊆ E₁ := hδsub.trans fun w hw => (hEu ▸ hw.1.1).resolve_right hw.2
      exact hybd (isInteriorPoint_of_ball_subset hδ hsub1 hyE)
    · right; intro z hz
      refine ⟨h2 hz, fun hbd => ?_⟩
      have hznot1 : z ∉ E₁ := fun hz1 => by
        have hzH : z ∈ H := by dsimp only [H]; rw [← hEi]; exact ⟨hz1, h2 hz⟩
        exact hAim z hz (Complex.mem_reProdIm.mp hzH).2
      obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp (hdiscInt_open.sdiff hE₁cl) z ⟨hcb_sub (hAsub hz), hznot1⟩
      obtain ⟨⟨y, hyE⟩, hybd, hyval⟩ := hbd; dsimp only at hyval; subst hyval
      have hsub2 : ball y δ ⊆ E₂ := hδsub.trans fun w hw => (hEu ▸ hw.1.1).resolve_left hw.2
      exact hybd (isInteriorPoint_of_ball_subset hδ hsub2 hyE)
  have hup_side := hside hupper_conn (fun _ h => h.1) (fun _ h => h.2.ne')
  have hlo_side := hside hlower_conn (fun _ h => h.1) (fun _ h => h.2.ne)
  have hx₀_bd1 : (x₀ : ℂ) ∈ discBd E₁ := (hF₁bd ▸ Or.inl rfl : (x₀ : ℂ) ∈ F₁ ∩ discBd E₁).2
  have hx₀_bd2 : (x₀ : ℂ) ∈ discBd E₂ := (hF₂bd ▸ Or.inl rfl : (x₀ : ℂ) ∈ F₂ ∩ discBd E₂).2
  have hball_of_both : ∀ {E' : Set ℂ}, H ⊆ E' →
      {z ∈ closedBall (x₀ : ℂ) ρ | 0 < z.im} ⊆ discInt E' →
      {z ∈ closedBall (x₀ : ℂ) ρ | z.im < 0} ⊆ discInt E' →
      (x₀ : ℂ) ∉ discBd E' := fun {E'} hHE' h1 h2 hbd => by
    have hball_sub : ball (x₀ : ℂ) ρ ⊆ E' := fun z hz => by
      have hcb : z ∈ closedBall (x₀ : ℂ) ρ := ball_subset_closedBall hz
      rcases lt_trichotomy z.im 0 with hlt | heq | hgt
      · exact (h2 ⟨hcb, hlt⟩).1
      · have hre : |z.re - x₀| < ρ := by
          have hd : ‖z - (x₀ : ℂ)‖ < ρ := by simpa [mem_ball, dist_eq_norm] using hz
          exact (Complex.abs_re_le_norm (z - (x₀ : ℂ))).trans_lt (by simpa using hd)
        have hρ_le1 : ρ ≤ (x₀ - a) / 2 := (min_le_right _ _).trans (min_le_left _ _)
        have hρ_le2 : ρ ≤ (b - x₀) / 2 := (min_le_right _ _).trans (min_le_right _ _)
        exact hHE' (Complex.mem_reProdIm.mpr ⟨⟨by linarith [(abs_lt.mp hre).1], by linarith [(abs_lt.mp hre).2]⟩, heq⟩)
      · exact (h1 ⟨hcb, hgt⟩).1
    obtain ⟨⟨y, hyE⟩, hybd, hyval⟩ := hbd; dsimp only at hyval; subst hyval
    exact hybd (isInteriorPoint_of_ball_subset hρ hball_sub hyE)
  have hH_sub1 : H ⊆ E₁ := fun z hz => (hEi.symm ▸ hz : z ∈ E₁ ∩ E₂).1
  have hH_sub2 : H ⊆ E₂ := fun z hz => (hEi.symm ▸ hz : z ∈ E₁ ∩ E₂).2
  have hsigns : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      (∀ z ∈ closedBall (x₀ : ℂ) ρ, 0 < σ * z.im → z ∈ discInt E₁) ∧
      (∀ z ∈ closedBall (x₀ : ℂ) ρ, 0 < (-σ) * z.im → z ∈ discInt E₂) := by
    rcases hup_side with h1 | h1 <;> rcases hlo_side with h2 | h2
    · exact (hball_of_both hH_sub1 h1 h2 hx₀_bd1).elim
    · exact ⟨1, Or.inl rfl, fun z hz hpos => h1 ⟨hz, by linarith⟩, fun z hz hpos => h2 ⟨hz, by linarith⟩⟩
    · exact ⟨-1, Or.inr rfl, fun z hz hpos => h2 ⟨hz, by linarith⟩, fun z hz hpos => h1 ⟨hz, by linarith⟩⟩
    · exact (hball_of_both hH_sub2 h1 h2 hx₀_bd2).elim
  obtain ⟨σ, hσ, hhalf1, hhalf2⟩ := hsigns
  have hσneg : -σ = 1 ∨ -σ = -1 := hσ.elim (fun h => Or.inr (by linarith)) (fun h => Or.inl (by linarith))
  have hubd1 : u ∈ discBd E₁ := (hF₁bd ▸ Or.inr rfl : u ∈ F₁ ∩ discBd E₁).2
  have hvbd2 : v ∈ discBd E₂ := (hF₂bd ▸ Or.inr rfl : v ∈ F₂ ∩ discBd E₂).2
  obtain ⟨F₁', η₁, hη₁, hη₁le, hF₁'sub, hF₁'l, hF₁'bd, hF₁'cb⟩ :=
    exists_half_disc_vertical_chord hE₁ hρ hσ hx₀_bd1 hubd1 hux hhalf1
  obtain ⟨F₂', η₂, hη₂, hη₂le, hF₂'sub, hF₂'l, hF₂'bd, hF₂'cb⟩ :=
    exists_half_disc_vertical_chord hE₂ hρ hσneg hx₀_bd2 hvbd2 hvx hhalf2
  obtain ⟨α₁, hα₁F, hα₁fix⟩ := exists_chord_homeo hman hE₁ hF₁sub hF₁'sub hux.symm hF₁l hF₁'l hF₁bd hF₁'bd
  obtain ⟨α₂, hα₂F, hα₂fix⟩ := exists_chord_homeo hman hE₂ hF₂sub hF₂'sub hvx.symm hF₂l hF₂'l hF₂bd hF₂'bd
  have hE1_sub_E : E₁ ⊆ E := hEu ▸ subset_union_left
  have hE2_sub_E : E₂ ⊆ E := hEu ▸ subset_union_right
  -- Helper: any point in `E'₁ ∩ E'₂` where `E'₁ ∩ E'₂ = H` cannot lie in `discInt E'₁`!
  have hint_notH : ∀ {A B : Set ℂ}, IsClosedDisc A → IsClosedDisc B → A ∩ B = H →
      ∀ z ∈ discInt A, z ∉ H := fun {A B} hA hB hAB z hz hzH => by
    have hzB : z ∈ B := (hAB.symm ▸ hzH : z ∈ A ∩ B).2
    have hopA : IsOpen (discInt A) := isOpen_discInt hman hA
    obtain ⟨hB', gB', cB⟩ := hB.exists_isChart
    have hmemB : hB' z ∈ closedBall (0 : ℂ) 1 := cB.hm hzB
    have hlim : Filter.Tendsto (fun n : ℕ => gB' (((1 - 1 / ((n : ℝ) + 2) : ℝ) : ℂ) * hB' z)) Filter.atTop (𝓝 z) := by
      have h0 : gB' (hB' z) = z := cB.gh hzB
      conv_rhs => rw [← h0]
      refine (cB.gc.continuousWithinAt hmemB).tendsto.comp ?_
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ (Filter.Eventually.of_forall fun n => ?_)
      · have ht1 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) - 1 / ((n : ℝ) + 2)) Filter.atTop (𝓝 1) := by
          have ht0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (Filter.tendsto_add_atTop_nat 1)
          simpa using (tendsto_const_nhds.sub ht0).congr fun n => by simp; ring
        simpa using (Complex.continuous_ofReal.continuousAt.tendsto.comp ht1).mul tendsto_const_nhds (b := hB' z)
      · rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hpos : (0 : ℝ) ≤ 1 - 1 / ((n : ℝ) + 2) := by
          have : 1 / ((n : ℝ) + 2) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
          linarith
        rw [abs_of_nonneg hpos]
        have hlt : 1 - 1 / ((n : ℝ) + 2) ≤ 1 := by linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 2) by positivity]
        nlinarith [mem_closedBall_zero_iff.mp hmemB]
    obtain ⟨n, hn⟩ := (hlim.eventually (hopA.mem_nhds hz)).exists
    have hballn : ((1 - 1 / ((n : ℝ) + 2) : ℝ) : ℂ) * hB' z ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hpos : (0 : ℝ) ≤ 1 - 1 / ((n : ℝ) + 2) := by
        have : 1 / ((n : ℝ) + 2) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
        linarith
      rw [abs_of_nonneg hpos]
      have hlt : 1 - 1 / ((n : ℝ) + 2) < 1 := by linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 2) by positivity]
      nlinarith [mem_closedBall_zero_iff.mp hmemB, norm_nonneg (hB' z)]
    have hinB : gB' (((1 - 1 / ((n : ℝ) + 2) : ℝ) : ℂ) * hB' z) ∈ discInt B := by
      rw [cB.discInt_eq]; exact ⟨_, hballn, rfl⟩
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp (hopA.inter (isOpen_discInt hman hB)) _ ⟨hn, hinB⟩
    let p0 := gB' (((1 - 1 / ((n : ℝ) + 2) : ℝ) : ℂ) * hB' z)
    have hp0 : p0 ∈ H := hAB ▸ ⟨hn.1, hinB.1⟩
    have hp1 : p0 + ((ε / 2 : ℝ) : ℂ) * I ∈ H := by
      have hm := hεsub (show p0 + ((ε / 2 : ℝ) : ℂ) * I ∈ ball p0 ε by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
            Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]; linarith)
      exact hAB ▸ ⟨hm.1.1, hm.2.1⟩
    have him0 : p0.im = 0 := (Complex.mem_reProdIm.mp hp0).2
    have him1 : (p0 + ((ε / 2 : ℝ) : ℂ) * I).im = 0 := (Complex.mem_reProdIm.mp hp1).2
    simp only [add_im, mul_im, ofReal_re, ofReal_im, I_im, I_re, mul_one, mul_zero, add_zero, him0, zero_add] at him1
    linarith
  have hint1_notH : ∀ z ∈ discInt E₁, z ∉ H := hint_notH hE₁ hE₂ hEi
  have hint2_notH : ∀ z ∈ discInt E₂, z ∉ H := hint_notH hE₂ hE₁ (inter_comm E₂ E₁ ▸ hEi)
  have hint_sub : ∀ {A : Set ℂ}, IsClosedDisc A → A ⊆ E → discInt A ⊆ discInt E := fun {A} hA hAE z hz => by
    refine ⟨hAE hz.1, fun hbd => ?_⟩
    obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp (isOpen_discInt hman hA) z hz
    obtain ⟨⟨y, hyE⟩, hybd, hyval⟩ := hbd; dsimp only at hyval; subst hyval
    exact hybd (isInteriorPoint_of_ball_subset hδ (hδsub.trans fun _ h => hAE h.1) hyE)
  have hint1_sub : discInt E₁ ⊆ discInt E := hint_sub hE₁ hE1_sub_E
  have hint2_sub : discInt E₂ ⊆ discInt E := hint_sub hE₂ hE2_sub_E
  let α : ℂ ≃ₜ ℂ := α₁.trans α₂
  have hα_F1 : α '' F₁ = F₁' := by
    rw [show (α : ℂ → ℂ) = α₂ ∘ α₁ from rfl, image_comp, hα₁F]
    ext z; constructor
    · rintro ⟨w, hw, rfl⟩
      have hwnot2 : w ∉ discInt E₂ := fun hw2 => hint2_notH w hw2 (by dsimp only [H]; rw [← hEi]; exact ⟨hF₁'sub hw, hw2.1⟩)
      rwa [hα₂fix w hwnot2]
    · intro hz
      have hznot2 : z ∉ discInt E₂ := fun hz2 => hint2_notH z hz2 (by dsimp only [H]; rw [← hEi]; exact ⟨hF₁'sub hz, hz2.1⟩)
      exact ⟨z, hz, hα₂fix z hznot2⟩
  have hα_F2 : α '' F₂ = F₂' := by
    rw [show (α : ℂ → ℂ) = α₂ ∘ α₁ from rfl, image_comp]
    have h1 : α₁ '' F₂ = F₂ := by
      ext z; constructor
      · rintro ⟨w, hw, rfl⟩
        have hwnot1 : w ∉ discInt E₁ := fun hw1 => hint1_notH w hw1 (by dsimp only [H]; rw [← hEi]; exact ⟨hw1.1, hF₂sub hw⟩)
        rwa [hα₁fix w hwnot1]
      · intro hz
        have hznot1 : z ∉ discInt E₁ := fun hz1 => hint1_notH z hz1 (by dsimp only [H]; rw [← hEi]; exact ⟨hz1.1, hF₂sub hz⟩)
        exact ⟨z, hz, hα₁fix z hznot1⟩
    rw [h1, hα₂F]
  let η₀ : ℝ := min η₁ η₂ / 2
  have hη₀ : 0 < η₀ := half_pos (lt_min hη₁ hη₂)
  have hsq_in_cb : ∀ {η' : ℝ}, 0 < η' → η₀ ≤ η' / 2 →
      Icc (x₀ - η₀) (x₀ + η₀) ×ℂ Icc (-η₀) η₀ ⊆ closedBall (x₀ : ℂ) η' := fun {η'} _ hle z hz => by
    rw [Complex.mem_reProdIm] at hz; rw [mem_closedBall, dist_eq_norm]
    have hre : |z.re - x₀| ≤ η₀ := abs_le.mpr ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
    have him : |z.im| ≤ η₀ := abs_le.mpr hz.2
    have hsq : ‖z - (x₀ : ℂ)‖ ≤ |z.re - x₀| + |z.im| := by
      calc ‖z - (x₀ : ℂ)‖ = ‖((z.re - x₀ : ℝ) : ℂ) + (z.im : ℂ) * I‖ := by
            congr 1; apply Complex.ext <;> simp
        _ ≤ ‖((z.re - x₀ : ℝ) : ℂ)‖ + ‖(z.im : ℂ) * I‖ := norm_add_le _ _
        _ = |z.re - x₀| + |z.im| := by
            rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    linarith
  have hsq_cb1 : Icc (x₀ - η₀) (x₀ + η₀) ×ℂ Icc (-η₀) η₀ ⊆ closedBall (x₀ : ℂ) η₁ :=
    hsq_in_cb hη₁ (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  have hsq_cb2 : Icc (x₀ - η₀) (x₀ + η₀) ×ℂ Icc (-η₀) η₀ ⊆ closedBall (x₀ : ℂ) η₂ :=
    hsq_in_cb hη₂ (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
  refine ⟨η₀, α, hη₀, hsq_cb1.trans ((closedBall_subset_closedBall (hη₁le.trans (by linarith))).trans hcb_sub),
    fun z hz => by simp only [α, Homeomorph.trans_apply, hα₁fix z (fun h => hz (hint1_sub h)), hα₂fix z (fun h => hz (hint2_sub h))],
    fun z hz => by simp only [α, Homeomorph.trans_apply, hα₁fix z (fun h => hint1_notH z h hz), hα₂fix z (fun h => hint2_notH z h hz)], ?_⟩
  rw [image_union, hα_F1, hα_F2, union_inter_distrib_right]
  ext z; constructor
  · rintro (⟨hz1, hzsq⟩ | ⟨hz2, hzsq⟩)
    · have h1 : z ∈ F₁' ∩ closedBall (x₀ : ℂ) η₁ := ⟨hz1, hsq_cb1 hzsq⟩
      rw [hF₁'cb] at h1
      exact Complex.mem_reProdIm.mpr ⟨h1.1, (Complex.mem_reProdIm.mp hzsq).2⟩
    · have h2 : z ∈ F₂' ∩ closedBall (x₀ : ℂ) η₂ := ⟨hz2, hsq_cb2 hzsq⟩
      rw [hF₂'cb] at h2
      exact Complex.mem_reProdIm.mpr ⟨h2.1, (Complex.mem_reProdIm.mp hzsq).2⟩
  · intro hz
    rw [Complex.mem_reProdIm] at hz
    have hzre : z.re = x₀ := mem_singleton_iff.mp hz.1
    have hzsq : z ∈ Icc (x₀ - η₀) (x₀ + η₀) ×ℂ Icc (-η₀) η₀ :=
      Complex.mem_reProdIm.mpr ⟨⟨by linarith [hzre], by linarith [hzre]⟩, hz.2⟩
    have hσ_abs : |σ| = 1 := hσ.elim (fun h => by rw [h]; norm_num) (fun h => by rw [h]; norm_num)
    have hη₀_le1 : η₀ ≤ η₁ := by dsimp only [η₀]; linarith [min_le_left η₁ η₂, hη₁]
    have hη₀_le2 : η₀ ≤ η₂ := by dsimp only [η₀]; linarith [min_le_right η₁ η₂, hη₂]
    have habs_im : |σ * z.im| ≤ η₀ := by
      rw [abs_mul, hσ_abs, one_mul]; exact abs_le.mpr hz.2
    rcases le_total 0 (σ * z.im) with hge | hle
    · left
      have hm : z ∈ F₁' ∩ closedBall (x₀ : ℂ) η₁ :=
        hF₁'cb.symm ▸ ⟨hzre, hge, (le_abs_self _).trans (habs_im.trans hη₀_le1)⟩
      exact ⟨hm.1, hzsq⟩
    · right
      have hm : z ∈ F₂' ∩ closedBall (x₀ : ℂ) η₂ :=
        hF₂'cb.symm ▸ ⟨hzre, by linarith, by linarith [(abs_le.mp habs_im).1, hη₀_le2]⟩
      exact ⟨hm.1, hzsq⟩

/-- Compose a finite family of homeomorphisms `α : Fin N → ℂ ≃ₜ ℂ` with pairwise disjoint open
supports `U : Fin N → Set ℂ`: the composite fixes `(⋃ i, U i)ᶜ` pointwise, fixes any set fixed by
every `α i`, and equals `α i` on `U i`. -/
private theorem compose_disjoint_homeos :
    ∀ {N : ℕ} {U : Fin N → Set ℂ}, (Pairwise fun i j => Disjoint (U i) (U j)) →
      ∀ (α : Fin N → ℂ ≃ₜ ℂ), (∀ i, ∀ z ∈ (U i)ᶜ, α i z = z) →
      ∃ Φ : ℂ ≃ₜ ℂ,
        (∀ z, (∀ i, z ∉ U i) → Φ z = z) ∧
        (∀ z, (∀ i, α i z = z) → Φ z = z) ∧
        (∀ i, ∀ z ∈ U i, Φ z = α i z) ∧
        (∀ i, ∀ z ∈ U i, α i z ∈ U i) := by
  intro N
  induction N with
  | zero =>
    intro U _ α _
    exact ⟨Homeomorph.refl ℂ, fun _ _ => rfl, fun _ _ => rfl, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ N ih =>
    intro U hdisj α hfix
    have hpres : ∀ i, ∀ z ∈ U i, α i z ∈ U i := fun i z hz => by
      by_contra hnot
      have h1 : α i (α i z) = α i z := hfix i (α i z) hnot
      have h2 : α i z = z := (α i).injective h1
      exact hnot (h2.symm ▸ hz)
    let U' : Fin N → Set ℂ := fun i => U i.castSucc
    let α' : Fin N → ℂ ≃ₜ ℂ := fun i => α i.castSucc
    obtain ⟨Φ', hΦ'out, hΦ'fix, hΦ'in, -⟩ := ih (fun i j hij => hdisj (Fin.castSucc_injective N |>.ne hij)) α' (fun i => hfix i.castSucc)
    let Φ : ℂ ≃ₜ ℂ := Φ'.trans (α (Fin.last N))
    refine ⟨Φ, fun z hz => ?_, fun z hz => ?_, fun i z hz => ?_, hpres⟩
    · simp only [Φ, Homeomorph.trans_apply, hΦ'out z (fun i => hz i.castSucc), hfix (Fin.last N) z (hz (Fin.last N))]
    · simp only [Φ, Homeomorph.trans_apply, hΦ'fix z (fun i => hz i.castSucc), hz (Fin.last N)]
    · rcases Fin.lastCases (motive := fun i => i = Fin.last N ∨ ∃ j : Fin N, i = j.castSucc)
        (Or.inl rfl) (fun j => Or.inr ⟨j, rfl⟩) i with rfl | ⟨j, rfl⟩
      · have hnot' : ∀ j : Fin N, z ∉ U' j := fun j hj =>
          Set.disjoint_left.mp (hdisj (Fin.castSucc_lt_last j).ne) hj hz
        simp only [Φ, Homeomorph.trans_apply, hΦ'out z hnot']
      · have h1 : Φ' z = α' j z := hΦ'in j z hz
        have h2 : α' j z ∈ U' j := hpres j.castSucc z hz
        have hnotLast : α' j z ∉ U (Fin.last N) := fun hL =>
          Set.disjoint_left.mp (hdisj (Fin.castSucc_lt_last j).ne) h2 hL
        simp only [Φ, Homeomorph.trans_apply, h1, hfix (Fin.last N) _ hnotLast]; rfl

end ChordStraightener

/-! ### Section 2: Simple crossings, shrinkable rectangular crossing boxes, and band surgery -/

section BandSurgery

/-- Two subsets `A, B ⊆ S` have *simple interior crossings* if at every point `p ∈ A ∩ B` there is an
interior box chart `g : [-ε, ε]² → S` around `p` (`g 0 = p`) in which `A` is the horizontal axis
`[-ε, ε] × {0}` and `B` is the vertical axis `{0} × [-ε, ε]`. -/
def IsSimpleCrossing (A B : Set S) : Prop :=
  ∀ p ∈ A ∩ B, ∃ (g : ℂ → S) (ε : ℝ), 0 < ε ∧
    ContinuousOn g (Icc (-ε) ε ×ℂ Icc (-ε) ε) ∧
    InjOn g (Icc (-ε) ε ×ℂ Icc (-ε) ε) ∧
    IsOpen (g '' (Ioo (-ε) ε ×ℂ Ioo (-ε) ε)) ∧
    g '' (Icc (-ε) ε ×ℂ Icc (-ε) ε) ⊆ (bd S)ᶜ ∧
    g 0 = p ∧
    A ∩ g '' (Icc (-ε) ε ×ℂ Icc (-ε) ε) = g '' (Icc (-ε) ε ×ℂ ({0} : Set ℝ)) ∧
    B ∩ g '' (Icc (-ε) ε ×ℂ Icc (-ε) ε) = g '' (({0} : Set ℝ) ×ℂ Icc (-ε) ε)

/-- A transverse `ProperManifold` automatically has simple crossings with every `Q i`. -/
theorem ProperManifold.IsTransverse.isSimpleCrossing (hS : IsSurface S)
    {s t : S} {M : ProperManifold S s t} {m : ℕ} {Q : Fin m → Set S}
    {sb : StripBox S Q} {X : Fin m → Finset ℝ} (htr : M.IsTransverse sb X) (i : Fin m) :
    IsSimpleCrossing M.U (Q i) := by
  classical
  have : T2Space S := hS.2.1
  intro p hp
  rw [htr.inter_Q_eq i] at hp
  obtain ⟨x, hxX, rfl⟩ := hp
  have hxin := htr.2.1 i x hxX
  have hother : ∃ r₁ > 0, ∀ x' ∈ X i, x' ≠ x → r₁ < |x' - x| := by
    by_cases hempty : ((X i).erase x).Nonempty
    · let d : ℝ := (((X i).erase x).image fun x' => |x' - x|).min' (hempty.image fun x' => |x' - x|)
      have hd_pos : 0 < d := by
        obtain ⟨x', hx', hdx⟩ := Finset.mem_image.mp (Finset.min'_mem _ (hempty.image fun x' => |x' - x|))
        dsimp only [d]; rw [← hdx]; exact abs_pos.mpr (sub_ne_zero.mpr (Finset.ne_of_mem_erase hx'))
      refine ⟨d / 2, half_pos hd_pos, fun x' hx' hne => ?_⟩
      have hle : d ≤ |x' - x| := Finset.min'_le _ _ (Finset.mem_image.mpr ⟨x', Finset.mem_erase.mpr ⟨hne, hx'⟩, rfl⟩)
      linarith
    · exact ⟨1, one_pos, fun x' hx' hne => (hempty ⟨x', Finset.mem_erase.mpr ⟨hne, hx'⟩⟩).elim⟩
  obtain ⟨r₁, hr₁, hr₁_sep⟩ := hother
  let ε : ℝ := min (r₁ / 2) (min ((x - sb.a i) / 2) (min ((sb.b i - x) / 2) (sb.δ / 2)))
  have hε : 0 < ε := lt_min (half_pos hr₁) (lt_min (half_pos (by linarith [hxin.1]))
    (lt_min (half_pos (by linarith [hxin.2])) (half_pos sb.hδ)))
  let rot : ℂ → ℂ := fun w => (x : ℂ) - w * I
  let g : ℂ → S := fun w => sb.f i (rot w)
  have hrot_maps : MapsTo rot (Icc (-ε) ε ×ℂ Icc (-ε) ε) (sb.openRect i) := fun w hw => by
    rw [Complex.mem_reProdIm] at hw
    simp only [StripBox.openRect, Complex.mem_reProdIm, rot, sub_re, sub_im, ofReal_re, ofReal_im,
      mul_re, mul_im, I_re, I_im, mul_zero, mul_one]
    have hεa : ε ≤ (x - sb.a i) / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hεb : ε ≤ (sb.b i - x) / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hεδ : ε ≤ sb.δ / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    exact ⟨⟨by linarith [hw.2.1, hxin.1], by linarith [hw.2.2, hxin.2]⟩, ⟨by linarith [hw.1.2, sb.hδ], by linarith [hw.1.1, sb.hδ]⟩⟩
  have hrot_maps_rect : MapsTo rot (Icc (-ε) ε ×ℂ Icc (-ε) ε) (sb.rect i) :=
    hrot_maps.mono_right (fun z hz => by
      simp only [StripBox.openRect, StripBox.rect, Complex.mem_reProdIm] at hz ⊢
      exact ⟨Ioo_subset_Icc_self hz.1, Ioo_subset_Icc_self hz.2⟩)
  have hrot_inj : Function.Injective rot := fun w₁ w₂ he => by
    have : w₁ * I = w₂ * I := by linear_combination -he
    exact mul_right_cancel₀ Complex.I_ne_zero this
  have hrot_oo_open : IsOpen (rot '' (Ioo (-ε) ε ×ℂ Ioo (-ε) ε)) := by
    let hro : ℂ ≃ₜ ℂ :=
      { toFun := rot
        invFun := fun z => (z - (x : ℂ)) * I
        left_inv := fun w => by simp [rot, mul_assoc]
        right_inv := fun z => by simp [rot, mul_assoc]
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    exact hro.isOpenMap _ (isOpen_Ioo.reProdIm isOpen_Ioo)
  have hopen_im : IsOpen (g '' (Ioo (-ε) ε ×ℂ Ioo (-ε) ε)) := by
    have heq : g '' (Ioo (-ε) ε ×ℂ Ioo (-ε) ε) = sb.f i '' (rot '' (Ioo (-ε) ε ×ℂ Ioo (-ε) ε)) :=
      image_comp (sb.f i) rot (Ioo (-ε) ε ×ℂ Ioo (-ε) ε)
    rw [heq]
    have hsub_oo : rot '' (Ioo (-ε) ε ×ℂ Ioo (-ε) ε) ⊆ sb.rect i := by
      rintro _ ⟨w, hw, rfl⟩
      exact hrot_maps_rect (Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hw).1,
        Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hw).2⟩)
    exact isOpen_image_of_manifold hrot_oo_open ((sb.hfc i).mono hsub_oo) ((sb.hfi i).mono hsub_oo) (fun _ _ => hS.2.2 _)
  refine ⟨g, ε, hε, (sb.hfc i).comp (by fun_prop) hrot_maps_rect,
    fun w₁ hw₁ w₂ hw₂ he => hrot_inj (sb.hfi i (hrot_maps_rect hw₁) (hrot_maps_rect hw₂) he),
    hopen_im, (image_comp _ _ _ ▸ (image_mono (image_subset_iff.mpr hrot_maps_rect)).trans (sb.hint i)),
    by simp [g, rot], ?_, ?_⟩
  · ext y; constructor
    · rintro ⟨hyM, w, hw, rfl⟩
      have hbox : sb.f i (rot w) ∈ M.U ∩ sb.box i := ⟨hyM, rot w, hrot_maps_rect hw, rfl⟩
      rw [htr.2.2 i] at hbox
      obtain ⟨x', hx'X, w', hw', hfe⟩ := mem_iUnion₂.mp hbox
      rw [Complex.mem_reProdIm] at hw'
      have hw'R : w' ∈ sb.rect i := Complex.mem_reProdIm.mpr
        ⟨by rw [mem_singleton_iff.mp hw'.1]; exact Ioo_subset_Icc_self (htr.2.1 i x' hx'X), hw'.2⟩
      have hww' := sb.hfi i hw'R (hrot_maps_rect hw) hfe
      have hre : (rot w).re = x' := by rw [← hww', mem_singleton_iff.mp hw'.1]
      have hrot_re : (rot w).re = x + w.im := by simp [rot]
      have hxx' : x' = x := by
        by_contra hne
        have hlt := hr₁_sep x' hx'X hne
        have hεr : ε ≤ r₁ / 2 := min_le_left _ _
        have habs : |x' - x| ≤ ε := by
          rw [← hre, hrot_re, add_sub_cancel_left]; exact abs_le.mpr (Complex.mem_reProdIm.mp hw).2
        linarith
      exact ⟨w, Complex.mem_reProdIm.mpr ⟨(Complex.mem_reProdIm.mp hw).1, by
        rw [mem_singleton_iff]; linarith [hre, hrot_re, hxx']⟩, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      rw [Complex.mem_reProdIm] at hw
      have hw' : w ∈ Icc (-ε) ε ×ℂ Icc (-ε) ε := Complex.mem_reProdIm.mpr ⟨hw.1, by rw [mem_singleton_iff.mp hw.2]; exact ⟨by linarith, hε.le⟩⟩
      have hre : (rot w).re = x := by simp [rot, mem_singleton_iff.mp hw.2]
      have hM : sb.f i (rot w) ∈ M.U ∩ sb.box i := by
        rw [htr.2.2 i]
        exact mem_iUnion₂.mpr ⟨x, hxX, rot w, Complex.mem_reProdIm.mpr ⟨hre, (Complex.mem_reProdIm.mp (hrot_maps_rect hw')).2⟩, rfl⟩
      exact ⟨hM.1, w, hw', rfl⟩
  · ext y; constructor
    · rintro ⟨hyQ, w, hw, rfl⟩
      have him : (rot w).im = 0 := (sb.hQ_eq i (rot w) (hrot_maps_rect hw)).mp hyQ
      have hwre : w.re = 0 := by simp only [rot, sub_im, ofReal_im, mul_im, I_im, I_re, mul_one, mul_zero, add_zero, zero_sub, neg_eq_zero] at him; exact him
      exact ⟨w, Complex.mem_reProdIm.mpr ⟨hwre, (Complex.mem_reProdIm.mp hw).2⟩, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      rw [Complex.mem_reProdIm] at hw
      have hw' : w ∈ Icc (-ε) ε ×ℂ Icc (-ε) ε := Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hw.1]; exact ⟨by linarith, hε.le⟩, hw.2⟩
      have him : (rot w).im = 0 := by simp [rot, mem_singleton_iff.mp hw.1]
      exact ⟨(sb.hQ_eq i (rot w) (hrot_maps_rect hw')).mpr him, w, hw', rfl⟩

/-- Shrinkable rectangular crossing box: an embedded closed box `g '' ([-a, a] × [-b, b]) ⊆ (bd S)ᶜ`
where `A` is the vertical segment `{0} × [-b, b]` and `γ_ext '' [s, e]` is the 2-segment chord
`[wL, 0] ∪ [0, wR]` (`wL.re < 0 < wR.re`, `wL, wR ∈ frontier ([-a, a] × [-b, b])`). -/
structure RectCross (S : Type) [TopologicalSpace S] (γ_ext : ℝ → S) (A : Set S) where
  g : ℂ → S
  a : ℝ
  b : ℝ
  ha : 0 < a
  hb : 0 < b
  hgc : ContinuousOn g (Icc (-a) a ×ℂ Icc (-b) b)
  hgi : InjOn g (Icc (-a) a ×ℂ Icc (-b) b)
  hgint : g '' (Icc (-a) a ×ℂ Icc (-b) b) ⊆ (bd S)ᶜ
  hA_eq : A ∩ g '' (Icc (-a) a ×ℂ Icc (-b) b) = g '' (({0} : Set ℝ) ×ℂ Icc (-b) b)
  s : ℝ
  t_mid : ℝ
  e : ℝ
  hs0 : 0 < s
  hst : s < t_mid
  hte : t_mid < e
  he1 : e < 1
  wL : ℂ
  wR : ℂ
  hwL : wL ∈ frontier (Icc (-a) a ×ℂ Icc (-b) b)
  hwR : wR ∈ frontier (Icc (-a) a ×ℂ Icc (-b) b)
  hwL_re : wL.re < 0
  hwR_re : 0 < wR.re
  hγD : γ_ext '' Icc 0 1 ∩ g '' (Icc (-a) a ×ℂ Icc (-b) b) = γ_ext '' Icc s e
  hγ_L : ∀ r ∈ Icc (0 : ℝ) 1, γ_ext (lin s t_mid r) = g (((1 - r : ℝ) : ℂ) * wL)
  hγ_R : ∀ r ∈ Icc (0 : ℝ) 1, γ_ext (lin t_mid e r) = g ((r : ℂ) * wR)

namespace RectCross

variable {γ_ext : ℝ → S} {A : Set S}

/-- The closed box `g '' ([-a, a] × [-b, b])`. -/
def box (rc : RectCross S γ_ext A) : Set S :=
  rc.g '' (Icc (-rc.a) rc.a ×ℂ Icc (-rc.b) rc.b)

theorem mid_eq (rc : RectCross S γ_ext A) : γ_ext rc.t_mid = rc.g 0 := by
  have h := rc.hγ_R 0 ⟨le_rfl, zero_le_one⟩; simpa [lin_zero] using h

theorem s_eq (rc : RectCross S γ_ext A) : γ_ext rc.s = rc.g rc.wL := by
  have h := rc.hγ_L 0 ⟨le_rfl, zero_le_one⟩; simpa [lin_zero] using h

theorem e_eq (rc : RectCross S γ_ext A) : γ_ext rc.e = rc.g rc.wR := by
  have h := rc.hγ_R 1 ⟨zero_le_one, le_rfl⟩; simpa [lin_one] using h

/-- Uniformly scale a `RectCross` by `λ ∈ (0, 1]`, keeping the SAME midpoint `t_mid` and shrinking
the box `[-a, a] × [-b, b]` to `[-λa, λa] × [-λb, λb]`. -/
def shrink (rc : RectCross S γ_ext A) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    RectCross S γ_ext A :=
  let R := Icc (-rc.a) rc.a ×ℂ Icc (-rc.b) rc.b
  let R' := Icc (-(lam * rc.a)) (lam * rc.a) ×ℂ Icc (-(lam * rc.b)) (lam * rc.b)
  have hR'sub : R' ⊆ R := fun z hz => by
    rw [Complex.mem_reProdIm] at hz ⊢
    exact ⟨⟨by nlinarith [hz.1.1, rc.ha], by nlinarith [hz.1.2, rc.ha]⟩,
      ⟨by nlinarith [hz.2.1, rc.hb], by nlinarith [hz.2.2, rc.hb]⟩⟩
  have hfr_scale : ∀ {w : ℂ}, w ∈ frontier R → (lam : ℂ) * w ∈ frontier R' := fun {w} hw => by
    have hRcl : IsClosed R := isClosed_Icc.reProdIm isClosed_Icc
    have hwR := Complex.mem_reProdIm.mp (hRcl.frontier_subset hw)
    have hw_notint := hw.2
    rw [interior_reProdIm, interior_Icc, interior_Icc, Complex.mem_reProdIm] at hw_notint
    have hmem' : (lam : ℂ) * w ∈ R' := by
      rw [Complex.mem_reProdIm]; simp only [mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero]
      exact ⟨⟨by nlinarith [hwR.1.1, hlam0], by nlinarith [hwR.1.2, hlam0]⟩,
        ⟨by nlinarith [hwR.2.1, hlam0], by nlinarith [hwR.2.2, hlam0]⟩⟩
    refine ⟨subset_closure hmem', fun hint => hw_notint ?_⟩
    rw [interior_reProdIm, interior_Icc, interior_Icc, Complex.mem_reProdIm] at hint
    simp only [mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero] at hint
    exact ⟨⟨by nlinarith [hint.1.1, hlam0], by nlinarith [hint.1.2, hlam0]⟩,
      ⟨by nlinarith [hint.2.1, hlam0], by nlinarith [hint.2.2, hlam0]⟩⟩
  have hfr_scale_le : ∀ {w : ℂ} {c : ℝ}, w ∈ frontier R → 0 ≤ c → (c : ℂ) * w ∈ R' → c ≤ lam := fun {w c} hw hc0 hcR' => by
    by_contra hgt; push Not at hgt
    have hRcl : IsClosed R := isClosed_Icc.reProdIm isClosed_Icc
    have hwR := Complex.mem_reProdIm.mp (hRcl.frontier_subset hw)
    have hnotint := hw.2
    rw [interior_reProdIm, interior_Icc, interior_Icc, Complex.mem_reProdIm] at hnotint
    rw [Complex.mem_reProdIm] at hcR'
    simp only [mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero] at hcR'
    have hc_pos : 0 < c := hlam0.trans hgt
    exact hnotint ⟨⟨by nlinarith [hcR'.1.1, rc.ha], by nlinarith [hcR'.1.2, rc.ha]⟩,
      ⟨by nlinarith [hcR'.2.1, rc.hb], by nlinarith [hcR'.2.2, rc.hb]⟩⟩
  let s' := lin rc.s rc.t_mid (1 - lam)
  let e' := lin rc.t_mid rc.e lam
  have hs'0 : 0 < s' := by dsimp only [s', lin]; nlinarith [rc.hs0, rc.hst, hlam0, hlam1]
  have hs't : s' < rc.t_mid := by dsimp only [s', lin]; nlinarith [rc.hst, hlam0]
  have hte' : rc.t_mid < e' := by dsimp only [e', lin]; nlinarith [rc.hte, hlam0]
  have he'1 : e' < 1 := by dsimp only [e', lin]; nlinarith [rc.hte, rc.he1, hlam0, hlam1]
  have hγ_L' : ∀ r ∈ Icc (0 : ℝ) 1, γ_ext (lin s' rc.t_mid r) = rc.g (((1 - r : ℝ) : ℂ) * ((lam : ℂ) * rc.wL)) := fun r hr => by
    have hlin : lin s' rc.t_mid r = lin rc.s rc.t_mid (1 - lam + lam * r) := by dsimp only [s', lin]; ring
    have hr' : 1 - lam + lam * r ∈ Icc (0 : ℝ) 1 := ⟨by nlinarith [hr.1, hlam0, hlam1], by nlinarith [hr.2, hlam0]⟩
    rw [hlin, rc.hγ_L _ hr']; congr 1; push_cast; ring
  have hγ_R' : ∀ r ∈ Icc (0 : ℝ) 1, γ_ext (lin rc.t_mid e' r) = rc.g ((r : ℂ) * ((lam : ℂ) * rc.wR)) := fun r hr => by
    have hlin : lin rc.t_mid e' r = lin rc.t_mid rc.e (lam * r) := by dsimp only [e', lin]; ring
    have hr' : lam * r ∈ Icc (0 : ℝ) 1 := ⟨by nlinarith [hr.1, hlam0], by nlinarith [hr.2, hlam0, hlam1]⟩
    rw [hlin, rc.hγ_R _ hr']; congr 1; push_cast; ring
  have hA_eq' : A ∩ rc.g '' R' = rc.g '' (({0} : Set ℝ) ×ℂ Icc (-(lam * rc.b)) (lam * rc.b)) := by
    ext y; constructor
    · rintro ⟨hyA, z, hzR', rfl⟩
      have h1 : rc.g z ∈ A ∩ rc.g '' R := ⟨hyA, z, hR'sub hzR', rfl⟩
      rw [rc.hA_eq] at h1
      obtain ⟨w, hw, hfe⟩ := h1
      rw [Complex.mem_reProdIm] at hw
      have hwR : w ∈ R := Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hw.1]; exact ⟨by linarith [rc.ha], rc.ha.le⟩, hw.2⟩
      have hzw := rc.hgi (hR'sub hzR') hwR hfe.symm
      exact ⟨z, Complex.mem_reProdIm.mpr ⟨by rw [hzw]; exact hw.1, (Complex.mem_reProdIm.mp hzR').2⟩, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      rw [Complex.mem_reProdIm] at hz
      have hzR' : z ∈ R' := Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hz.1]; exact ⟨by nlinarith [rc.ha, hlam0], by nlinarith [rc.ha, hlam0]⟩, hz.2⟩
      have h1 : rc.g z ∈ A ∩ rc.g '' R := by
        rw [rc.hA_eq]; exact ⟨z, Complex.mem_reProdIm.mpr ⟨hz.1, (Complex.mem_reProdIm.mp (hR'sub hzR')).2⟩, rfl⟩
      exact ⟨h1.1, z, hzR', rfl⟩
  have hγD' : γ_ext '' Icc 0 1 ∩ rc.g '' R' = γ_ext '' Icc s' e' := by
    ext y; constructor
    · rintro ⟨hyγ, z, hzR', rfl⟩
      have h1 : rc.g z ∈ γ_ext '' Icc 0 1 ∩ rc.g '' R := ⟨hyγ, z, hR'sub hzR', rfl⟩
      rw [rc.hγD] at h1
      obtain ⟨τ, hτ, hτe⟩ := h1
      rcases le_total τ rc.t_mid with hle | hge
      · let r : ℝ := (τ - rc.s) / (rc.t_mid - rc.s)
        have hr : r ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg (by linarith [hτ.1]) (by linarith [rc.hst]),
          (div_le_one (by linarith [rc.hst])).mpr (by linarith)⟩
        have hτ_eq : lin rc.s rc.t_mid r = τ := by dsimp only [r, lin]; field_simp [show rc.t_mid - rc.s ≠ 0 by linarith [rc.hst]]; ring
        have hgw : rc.g (((1 - r : ℝ) : ℂ) * rc.wL) = rc.g z := by rw [← rc.hγ_L r hr, hτ_eq, hτe]
        have hwR : ((1 - r : ℝ) : ℂ) * rc.wL ∈ R := by
          have hwL := Complex.mem_reProdIm.mp ((isClosed_Icc.reProdIm isClosed_Icc).frontier_subset rc.hwL)
          rw [Complex.mem_reProdIm]; simp only [mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero]
          exact ⟨⟨by nlinarith [hwL.1.1, hr.1, hr.2, rc.ha], by nlinarith [hwL.1.2, hr.1, hr.2, rc.ha]⟩,
            ⟨by nlinarith [hwL.2.1, hr.1, hr.2, rc.hb], by nlinarith [hwL.2.2, hr.1, hr.2, rc.hb]⟩⟩
        have hzw := rc.hgi hwR (hR'sub hzR') hgw
        have h1r_le : 1 - r ≤ lam := hfr_scale_le rc.hwL (by linarith [hr.2]) (hzw ▸ hzR')
        have hs'le : s' ≤ τ := by
          rw [← hτ_eq]; dsimp only [s', lin]; nlinarith [rc.hst]
        exact ⟨τ, ⟨hs'le, hle.trans hte'.le⟩, hτe⟩
      · let r : ℝ := (τ - rc.t_mid) / (rc.e - rc.t_mid)
        have hr : r ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg (by linarith) (by linarith [rc.hte]),
          (div_le_one (by linarith [rc.hte])).mpr (by linarith [hτ.2])⟩
        have hτ_eq : lin rc.t_mid rc.e r = τ := by dsimp only [r, lin]; field_simp [show rc.e - rc.t_mid ≠ 0 by linarith [rc.hte]]; ring
        have hgw : rc.g ((r : ℂ) * rc.wR) = rc.g z := by rw [← rc.hγ_R r hr, hτ_eq, hτe]
        have hwR : (r : ℂ) * rc.wR ∈ R := by
          have hwR' := Complex.mem_reProdIm.mp ((isClosed_Icc.reProdIm isClosed_Icc).frontier_subset rc.hwR)
          rw [Complex.mem_reProdIm]; simp only [mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero]
          exact ⟨⟨by nlinarith [hwR'.1.1, hr.1, hr.2, rc.ha], by nlinarith [hwR'.1.2, hr.1, hr.2, rc.ha]⟩,
            ⟨by nlinarith [hwR'.2.1, hr.1, hr.2, rc.hb], by nlinarith [hwR'.2.2, hr.1, hr.2, rc.hb]⟩⟩
        have hzw := rc.hgi hwR (hR'sub hzR') hgw
        have hr_le : r ≤ lam := hfr_scale_le rc.hwR hr.1 (hzw ▸ hzR')
        have hle' : τ ≤ e' := by
          rw [← hτ_eq]; dsimp only [e', lin]; nlinarith [rc.hte]
        exact ⟨τ, ⟨hs't.le.trans hge, hle'⟩, hτe⟩
    · rintro ⟨τ, hτ, rfl⟩
      refine ⟨⟨τ, ⟨hs'0.le.trans hτ.1, hτ.2.trans he'1.le⟩, rfl⟩, ?_⟩
      rcases le_total τ rc.t_mid with hle | hge
      · let r : ℝ := (τ - s') / (rc.t_mid - s')
        have hr : r ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg (by linarith [hτ.1]) (by linarith [hs't]),
          (div_le_one (by linarith [hs't])).mpr (by linarith)⟩
        have hτ_eq : lin s' rc.t_mid r = τ := by dsimp only [r, lin]; field_simp [show rc.t_mid - s' ≠ 0 by linarith [hs't]]; ring
        rw [← hτ_eq, hγ_L' r hr]
        refine ⟨_, ?_, rfl⟩
        have hwL' := Complex.mem_reProdIm.mp ((isClosed_Icc.reProdIm isClosed_Icc).frontier_subset (hfr_scale rc.hwL))
        simp only [mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero] at hwL'
        have hla : 0 < lam * rc.a := mul_pos hlam0 rc.ha
        have hlb : 0 < lam * rc.b := mul_pos hlam0 rc.hb
        rw [Complex.mem_reProdIm]; simp only [mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero]
        exact ⟨⟨by nlinarith [hwL'.1.1, hr.1, hr.2, hla], by nlinarith [hwL'.1.2, hr.1, hr.2, hla]⟩,
          ⟨by nlinarith [hwL'.2.1, hr.1, hr.2, hlb], by nlinarith [hwL'.2.2, hr.1, hr.2, hlb]⟩⟩
      · let r : ℝ := (τ - rc.t_mid) / (e' - rc.t_mid)
        have hr : r ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg (by linarith) (by linarith [hte']),
          (div_le_one (by linarith [hte'])).mpr (by linarith [hτ.2])⟩
        have hτ_eq : lin rc.t_mid e' r = τ := by dsimp only [r, lin]; field_simp [show e' - rc.t_mid ≠ 0 by linarith [hte']]; ring
        rw [← hτ_eq, hγ_R' r hr]
        refine ⟨_, ?_, rfl⟩
        have hwR' := Complex.mem_reProdIm.mp ((isClosed_Icc.reProdIm isClosed_Icc).frontier_subset (hfr_scale rc.hwR))
        simp only [mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero] at hwR'
        have hla : 0 < lam * rc.a := mul_pos hlam0 rc.ha
        have hlb : 0 < lam * rc.b := mul_pos hlam0 rc.hb
        rw [Complex.mem_reProdIm]; simp only [mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero]
        exact ⟨⟨by nlinarith [hwR'.1.1, hr.1, hr.2, hla], by nlinarith [hwR'.1.2, hr.1, hr.2, hla]⟩,
          ⟨by nlinarith [hwR'.2.1, hr.1, hr.2, hlb], by nlinarith [hwR'.2.2, hr.1, hr.2, hlb]⟩⟩
  { g := rc.g, a := lam * rc.a, b := lam * rc.b,
    ha := mul_pos hlam0 rc.ha, hb := mul_pos hlam0 rc.hb,
    hgc := rc.hgc.mono hR'sub, hgi := rc.hgi.mono hR'sub,
    hgint := (image_mono hR'sub).trans rc.hgint, hA_eq := hA_eq',
    s := s', t_mid := rc.t_mid, e := e',
    hs0 := hs'0, hst := hs't, hte := hte', he1 := he'1,
    wL := (lam : ℂ) * rc.wL, wR := (lam : ℂ) * rc.wR,
    hwL := hfr_scale rc.hwL, hwR := hfr_scale rc.hwR,
    hwL_re := by simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]; nlinarith [hlam0, rc.hwL_re],
    hwR_re := by simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]; nlinarith [hlam0, rc.hwR_re],
    hγD := hγD', hγ_L := hγ_L', hγ_R := hγ_R' }

theorem shrink_box_subset (rc : RectCross S γ_ext A) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    (rc.shrink hlam0 hlam1).box ⊆ rc.box := by
  refine image_mono fun z hz => ?_
  rw [Complex.mem_reProdIm] at hz ⊢
  dsimp only [RectCross.shrink] at hz
  exact ⟨⟨by nlinarith [hz.1.1, rc.ha], by nlinarith [hz.1.2, rc.ha]⟩,
    ⟨by nlinarith [hz.2.1, rc.hb], by nlinarith [hz.2.2, rc.hb]⟩⟩

/-- Every `RectCross` whose box fits inside an open neighborhood `W` of `γ_ext rc.t_mid` can be
shrunk so its box lies completely in `W`. -/
theorem exists_shrink_subset (rc : RectCross S γ_ext A) {W : Set S} (hWo : IsOpen W)
    (hmem : γ_ext rc.t_mid ∈ W) :
    ∃ (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1), (rc.shrink h0 h1).box ⊆ W := by
  have h0R : (0 : ℂ) ∈ Icc (-rc.a) rc.a ×ℂ Icc (-rc.b) rc.b :=
    Complex.mem_reProdIm.mpr ⟨by simp [rc.ha.le], by simp [rc.hb.le]⟩
  have hpre : rc.g ⁻¹' W ∈ 𝓝[(Icc (-rc.a) rc.a ×ℂ Icc (-rc.b) rc.b)] (0 : ℂ) :=
    rc.hgc.continuousWithinAt h0R (hWo.mem_nhds (rc.mid_eq ▸ hmem))
  rw [Metric.mem_nhdsWithin_iff] at hpre
  obtain ⟨r, hr, hrsub⟩ := hpre
  let lam : ℝ := min 1 (r / (2 * (rc.a + rc.b)))
  have hlam0 : 0 < lam := lt_min one_pos (div_pos hr (by linarith [rc.ha, rc.hb]))
  have hlam1 : lam ≤ 1 := min_le_left _ _
  refine ⟨lam, hlam0, hlam1, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  dsimp only [RectCross.shrink] at hz
  have hzR : z ∈ Icc (-rc.a) rc.a ×ℂ Icc (-rc.b) rc.b := by
    rw [Complex.mem_reProdIm] at hz ⊢
    exact ⟨⟨by nlinarith [hz.1.1, rc.ha], by nlinarith [hz.1.2, rc.ha]⟩,
      ⟨by nlinarith [hz.2.1, rc.hb], by nlinarith [hz.2.2, rc.hb]⟩⟩
  have hball : z ∈ ball (0 : ℂ) r := by
    rw [mem_ball_zero_iff]
    rw [Complex.mem_reProdIm] at hz
    have hre : |z.re| ≤ lam * rc.a := abs_le.mpr hz.1
    have him : |z.im| ≤ lam * rc.b := abs_le.mpr hz.2
    have hnorm : ‖z‖ ≤ |z.re| + |z.im| := by
      calc ‖z‖ = ‖(z.re : ℂ) + (z.im : ℂ) * I‖ := by congr 1; apply Complex.ext <;> simp
        _ ≤ ‖(z.re : ℂ)‖ + ‖(z.im : ℂ) * I‖ := norm_add_le _ _
        _ = |z.re| + |z.im| := by simp [Complex.norm_real]
    have hlam_le : lam ≤ r / (2 * (rc.a + rc.b)) := min_le_right _ _
    have hmul : lam * (rc.a + rc.b) ≤ r / 2 := by
      calc lam * (rc.a + rc.b) ≤ (r / (2 * (rc.a + rc.b))) * (rc.a + rc.b) :=
            mul_le_mul_of_nonneg_right hlam_le (by linarith [rc.ha, rc.hb])
        _ = r / 2 := by field_simp [show rc.a + rc.b ≠ 0 by linarith [rc.ha, rc.hb]]
    linarith
  exact hrsub ⟨hball, hzR⟩

end RectCross

/-- Split a `RectCross` into two closed half-discs `D₁, D₂` and two half-chords `A₁, A₂` across
`γ_ext '' [rc.s, rc.e]`. -/
private theorem rectCross_split [T2Space S] {γ_ext : ℝ → S} {A : Set S}
    (hγc : ContinuousOn γ_ext (Icc 0 1)) (hγi : InjOn γ_ext (Icc 0 1))
    (rc : RectCross S γ_ext A) :
    ∃ (D₁ D₂ A₁ A₂ : Set S) (u v : S),
      IsClosedDisc rc.box ∧ IsClosedDisc D₁ ∧ IsClosedDisc D₂ ∧
      D₁ ∪ D₂ = rc.box ∧ D₁ ∩ D₂ = γ_ext '' Icc rc.s rc.e ∧
      (γ_ext '' Icc rc.s rc.e) ∩ discBd rc.box = {γ_ext rc.s, γ_ext rc.e} ∧
      A ∩ rc.box = A₁ ∪ A₂ ∧ A₁ ⊆ D₁ ∧ A₂ ⊆ D₂ ∧
      IsLineWithEnds A₁ (γ_ext rc.t_mid) u ∧ IsLineWithEnds A₂ (γ_ext rc.t_mid) v ∧
      A₁ ∩ discBd D₁ = {γ_ext rc.t_mid, u} ∧ A₂ ∩ discBd D₂ = {γ_ext rc.t_mid, v} ∧
      u ≠ γ_ext rc.t_mid ∧ v ≠ γ_ext rc.t_mid := by
  let R : Set ℂ := Icc (-rc.a) rc.a ×ℂ Icc (-rc.b) rc.b
  have hR_comp : IsCompact R := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨hR_disc, hR_bd⟩ := isClosedDisc_reProdIm_Icc (by linarith [rc.ha] : -rc.a < rc.a) (by linarith [rc.hb] : -rc.b < rc.b)
  obtain ⟨ginv, hginvc, hginvl⟩ := exists_inv_of_compactOn hR_comp rc.hgc rc.hgi
  have hD_pair := hR_disc.image rc.hgc hginvc hginvl
  have hD : IsClosedDisc rc.box := hD_pair.1
  have hR_closed : IsClosed R := isClosed_Icc.reProdIm isClosed_Icc
  have hR_fr_eq : discBd R = frontier R := by
    rw [hR_bd, hR_closed.frontier_eq, interior_reProdIm, interior_Icc, interior_Icc]
  have hD_bd : discBd rc.box = rc.g '' frontier R := by
    change discBd (rc.g '' R) = _; rw [hD_pair.2, hR_fr_eq]
  have hR_conv : Convex ℝ R := fun z hz w hw α β hα hβ hαβ => by
    rw [Complex.mem_reProdIm] at hz hw ⊢
    simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re, Complex.mul_im,
      ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero]
    have h1 := mul_le_mul_of_nonneg_left hz.1.1 hα
    have h2 := mul_le_mul_of_nonneg_left hw.1.1 hβ
    have h3 := mul_le_mul_of_nonneg_left hz.1.2 hα
    have h4 := mul_le_mul_of_nonneg_left hw.1.2 hβ
    have h5 := mul_le_mul_of_nonneg_left hz.2.1 hα
    have h6 := mul_le_mul_of_nonneg_left hw.2.1 hβ
    have h7 := mul_le_mul_of_nonneg_left hz.2.2 hα
    have h8 := mul_le_mul_of_nonneg_left hw.2.2 hβ
    have ha_sum : α * rc.a + β * rc.a = rc.a := by rw [← add_mul, hαβ, one_mul]
    have hb_sum : α * rc.b + β * rc.b = rc.b := by rw [← add_mul, hαβ, one_mul]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have h0R : (0 : ℂ) ∈ interior R := by
    rw [interior_reProdIm, interior_Icc, interior_Icc]
    exact Complex.mem_reProdIm.mpr ⟨by simp [rc.ha], by simp [rc.hb]⟩
  have hwL_R : rc.wL ∈ R := hR_closed.frontier_subset rc.hwL
  have hwR_R : rc.wR ∈ R := hR_closed.frontier_subset rc.hwR
  let segL : ℝ → ℂ := fun r => ((1 - r : ℝ) : ℂ) * rc.wL
  let segR : ℝ → ℂ := fun r => (r : ℂ) * rc.wR
  have hsegL_R : ∀ r ∈ Icc (0 : ℝ) 1, segL r ∈ R := fun r hr => by
    simpa [segL, smul_eq_mul] using hR_conv hwL_R (interior_subset h0R) (by linarith [hr.2] : (0 : ℝ) ≤ 1 - r) hr.1 (by ring)
  have hsegR_R : ∀ r ∈ Icc (0 : ℝ) 1, segR r ∈ R := fun r hr => by
    simpa [segR, smul_eq_mul] using hR_conv (interior_subset h0R) hwR_R (by linarith [hr.2] : (0 : ℝ) ≤ 1 - r) hr.1 (by ring)
  have hsegL_int : ∀ r ∈ Ioc (0 : ℝ) 1, segL r ∈ interior R := fun r hr => by
    rw [interior_reProdIm, interior_Icc, interior_Icc, Complex.mem_reProdIm]
    have hL := Complex.mem_reProdIm.mp hwL_R
    simp only [segL, mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero]
    exact ⟨⟨by nlinarith [hL.1.1, hr.1, hr.2, rc.ha], by nlinarith [hL.1.2, hr.1, hr.2, rc.ha]⟩,
      ⟨by nlinarith [hL.2.1, hr.1, hr.2, rc.hb], by nlinarith [hL.2.2, hr.1, hr.2, rc.hb]⟩⟩
  have hsegR_int : ∀ r ∈ Ico (0 : ℝ) 1, segR r ∈ interior R := fun r hr => by
    rw [interior_reProdIm, interior_Icc, interior_Icc, Complex.mem_reProdIm]
    have hR' := Complex.mem_reProdIm.mp hwR_R
    simp only [segR, mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero]
    exact ⟨⟨by nlinarith [hR'.1.1, hr.1, hr.2, rc.ha], by nlinarith [hR'.1.2, hr.1, hr.2, rc.ha]⟩,
      ⟨by nlinarith [hR'.2.1, hr.1, hr.2, rc.hb], by nlinarith [hR'.2.2, hr.1, hr.2, rc.hb]⟩⟩
  have hγ_segL : γ_ext '' Icc rc.s rc.t_mid = rc.g '' (segL '' Icc 0 1) := by
    rw [← subArc_image rc.hst.le]; ext y; constructor
    · rintro ⟨r, hr, rfl⟩; exact ⟨segL r, ⟨r, hr, rfl⟩, (rc.hγ_L r hr).symm⟩
    · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩; exact ⟨r, hr, rc.hγ_L r hr⟩
  have hγ_segR : γ_ext '' Icc rc.t_mid rc.e = rc.g '' (segR '' Icc 0 1) := by
    rw [← subArc_image rc.hte.le]; ext y; constructor
    · rintro ⟨r, hr, rfl⟩; exact ⟨segR r, ⟨r, hr, rfl⟩, (rc.hγ_R r hr).symm⟩
    · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩; exact ⟨r, hr, rc.hγ_R r hr⟩
  have hγ_se_eq : γ_ext '' Icc rc.s rc.e = rc.g '' (segL '' Icc 0 1 ∪ segR '' Icc 0 1) := by
    rw [← Icc_union_Icc_eq_Icc rc.hst.le rc.hte.le, image_union, hγ_segL, hγ_segR, image_union]
  have hγ_sub_D : γ_ext '' Icc rc.s rc.e ⊆ rc.box := by
    rw [hγ_se_eq]; exact image_mono (union_subset (image_subset_iff.mpr hsegL_R) (image_subset_iff.mpr hsegR_R))
  have hγ_bd : (γ_ext '' Icc rc.s rc.e) ∩ discBd rc.box = {γ_ext rc.s, γ_ext rc.e} := by
    rw [hγ_se_eq, hD_bd, rc.s_eq, rc.e_eq]
    ext y; constructor
    · rintro ⟨⟨z, hzL | hzR, rfl⟩, ⟨w, hwfr, hfe⟩⟩
      · obtain ⟨r, hr, rfl⟩ := hzL
        have hzw : segL r = w := rc.hgi (hsegL_R r hr) (hR_closed.frontier_subset hwfr) hfe.symm
        rcases hr.1.eq_or_lt with rfl | hr0
        · exact Or.inl (by simp [segL])
        · exact ((hzw ▸ hwfr).2 (hsegL_int r ⟨hr0, hr.2⟩)).elim
      · obtain ⟨r, hr, rfl⟩ := hzR
        have hzw : segR r = w := rc.hgi (hsegR_R r hr) (hR_closed.frontier_subset hwfr) hfe.symm
        rcases hr.2.eq_or_lt with rfl | hr1
        · exact Or.inr (by simp [segR])
        · exact ((hzw ▸ hwfr).2 (hsegR_int r ⟨hr.1, hr1⟩)).elim
    · rintro (rfl | rfl)
      · exact ⟨⟨rc.wL, Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [segL]⟩, rfl⟩, ⟨rc.wL, rc.hwL, rfl⟩⟩
      · exact ⟨⟨rc.wR, Or.inr ⟨1, ⟨zero_le_one, le_rfl⟩, by simp [segR]⟩, rfl⟩, ⟨rc.wR, rc.hwR, rfl⟩⟩
  have hse : rc.s < rc.e := rc.hst.trans rc.hte
  have hγ_se_l : IsLineWithEnds (γ_ext '' Icc rc.s rc.e) (γ_ext rc.s) (γ_ext rc.e) :=
    isLineWithEnds_of_param (continuousOn_subArc hse.le (hγc.mono (Icc_subset_Icc rc.hs0.le rc.he1.le)))
      (injOn_subArc hse (hγi.mono (Icc_subset_Icc rc.hs0.le rc.he1.le)))
      (subArc_zero γ_ext rc.s rc.e) (subArc_one γ_ext rc.s rc.e) (subArc_image hse.le)
  have hγ_ne : γ_ext rc.s ≠ γ_ext rc.e := fun h => hse.ne (hγi ⟨rc.hs0.le, hse.le.trans rc.he1.le⟩
    ⟨rc.hs0.le.trans hse.le, rc.he1.le⟩ h)
  obtain ⟨D₁, D₂, B₁, B₂, hB₁, hB₂, hBu, hBi, hD₁, hD₂, hDu, hDi, hbD₁, hbD₂, -, -⟩ :=
    disc_split hD hγ_sub_D hγ_ne hγ_se_l hγ_bd
  let u_top : S := rc.g ((rc.b : ℂ) * I)
  let u_bot : S := rc.g ((-(rc.b : ℝ) : ℂ) * I)
  let V_top : Set S := rc.g '' (({0} : Set ℝ) ×ℂ Icc 0 rc.b)
  let V_bot : Set S := rc.g '' (({0} : Set ℝ) ×ℂ Icc (-rc.b) 0)
  have htop_R : (rc.b : ℂ) * I ∈ R := Complex.mem_reProdIm.mpr ⟨by simp [rc.ha.le], by simp [rc.hb.le]⟩
  have hbot_R : (-(rc.b : ℝ) : ℂ) * I ∈ R := Complex.mem_reProdIm.mpr ⟨by simp [rc.ha.le], by simp [rc.hb.le]⟩
  have htop_fr : (rc.b : ℂ) * I ∈ frontier R := by
    refine ⟨subset_closure htop_R, fun hint => ?_⟩
    rw [interior_reProdIm, interior_Icc, interior_Icc] at hint
    have := (Complex.mem_reProdIm.mp hint).2.2; simp at this
  have hbot_fr : (-(rc.b : ℝ) : ℂ) * I ∈ frontier R := by
    refine ⟨subset_closure hbot_R, fun hint => ?_⟩
    rw [interior_reProdIm, interior_Icc, interior_Icc] at hint
    have := (Complex.mem_reProdIm.mp hint).2.1; simp at this
  have htop_bd : u_top ∈ discBd rc.box := hD_bd ▸ ⟨(rc.b : ℂ) * I, htop_fr, rfl⟩
  have hbot_bd : u_bot ∈ discBd rc.box := hD_bd ▸ ⟨(-(rc.b : ℝ) : ℂ) * I, hbot_fr, rfl⟩
  have htop_ne_s : u_top ≠ γ_ext rc.s := fun h => by
    have := congrArg Complex.re (rc.hgi htop_R hwL_R (h.trans rc.s_eq)); simp at this; linarith [rc.hwL_re]
  have htop_ne_e : u_top ≠ γ_ext rc.e := fun h => by
    have := congrArg Complex.re (rc.hgi htop_R hwR_R (h.trans rc.e_eq)); simp at this; linarith [rc.hwR_re]
  have hbot_ne_s : u_bot ≠ γ_ext rc.s := fun h => by
    have := congrArg Complex.re (rc.hgi hbot_R hwL_R (h.trans rc.s_eq)); simp at this; linarith [rc.hwL_re]
  have hbot_ne_e : u_bot ≠ γ_ext rc.e := fun h => by
    have := congrArg Complex.re (rc.hgi hbot_R hwR_R (h.trans rc.e_eq)); simp at this; linarith [rc.hwR_re]
  -- Any boundary arc `B ⊆ discBd rc.box` from `γ_ext s` to `γ_ext e` must contain `u_top` OR `u_bot` (by IVT on `Re ∘ ginv`):
  have hhit_tb : ∀ {B : Set S}, IsLineWithEnds B (γ_ext rc.s) (γ_ext rc.e) → B ⊆ discBd rc.box →
      u_top ∈ B ∨ u_bot ∈ B := fun {B} hBl hBsub => by
    obtain ⟨φ, hφ0, hφ1⟩ := hBl
    have hφ_R : ∀ t : unitInterval, ginv (φ t).1 ∈ frontier R ∧ rc.g (ginv (φ t).1) = (φ t).1 := fun t => by
      obtain ⟨z, hzfr, hze⟩ := hD_bd ▸ hBsub (φ t).2
      have hg1 : ginv (φ t).1 = z := by rw [← hze]; exact hginvl (hR_closed.frontier_subset hzfr)
      exact ⟨hg1 ▸ hzfr, by rw [hg1, hze]⟩
    have hre_c : Continuous fun t : unitInterval => (ginv (φ t).1).re :=
      continuous_re.comp (hginvc.comp_continuous (continuous_subtype_val.comp φ.continuous) fun t =>
        (hD_bd ▸ hBsub (φ t).2 |> fun ⟨z, hzfr, hze⟩ => ⟨z, hR_closed.frontier_subset hzfr, hze⟩))
    have hre0 : (ginv (φ 0).1).re = rc.wL.re := by rw [hφ0, rc.s_eq, hginvl hwL_R]
    have hre1 : (ginv (φ 1).1).re = rc.wR.re := by rw [hφ1, rc.e_eq, hginvl hwR_R]
    let fn : ℝ → ℝ := fun r => if hr : r ∈ Icc (0 : ℝ) 1 then (ginv (φ ⟨r, hr⟩).1).re else 0
    have hcont_Icc : ContinuousOn fn (Icc 0 1) := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact hre_c.congr fun r => by simp only [Set.domRestrict, fn, dite_eq_left r.2]
    have hfn0 : fn 0 = rc.wL.re := by simp [fn, hre0]
    have hfn1 : fn 1 = rc.wR.re := by simp [fn, hre1]
    obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc (zero_le_one (α := ℝ)) hcont_Icc
      (show (0 : ℝ) ∈ Icc (fn 0) (fn 1) from ⟨by linarith [hfn0, rc.hwL_re], by linarith [hfn1, rc.hwR_re]⟩)
    simp only [fn, dite_eq_left hr] at hr0
    let t : unitInterval := ⟨r, hr⟩
    have hfr := (hφ_R t).1
    have hnotint := hfr.2
    rw [interior_reProdIm, interior_Icc, interior_Icc, Complex.mem_reProdIm] at hnotint
    have him_not : (ginv (φ t).1).im ∉ Ioo (-rc.b) rc.b := fun h => hnotint ⟨by rw [hr0]; exact ⟨by linarith [rc.ha], rc.ha⟩, h⟩
    have him_icc := (Complex.mem_reProdIm.mp (hR_closed.frontier_subset hfr)).2
    rcases him_icc.1.eq_or_lt with h1 | h1
    · right
      have heq : (φ t).1 = u_bot := by rw [← (hφ_R t).2]; congr 1; apply Complex.ext <;> simp [t, hr0, h1.symm]
      exact heq ▸ (φ t).2
    · rcases him_icc.2.eq_or_lt with h2 | h2
      · left
        have heq : (φ t).1 = u_top := by rw [← (hφ_R t).2]; congr 1; apply Complex.ext <;> simp [t, hr0, h2]
        exact heq ▸ (φ t).2
      · exact (him_not ⟨h1, h2⟩).elim
  have hsep_B : ¬ (u_top ∈ B₁ ∧ u_bot ∈ B₁) ∧ ¬ (u_top ∈ B₂ ∧ u_bot ∈ B₂) := by
    constructor
    · rintro ⟨ht1, hb1⟩
      rcases hhit_tb hB₂ (hBu ▸ subset_union_right) with ht2 | hb2
      · rcases (hBi ▸ ⟨ht1, ht2⟩ : u_top ∈ ({γ_ext rc.s, γ_ext rc.e} : Set S)) with h | h
        · exact htop_ne_s h
        · exact htop_ne_e (mem_singleton_iff.mp h)
      · rcases (hBi ▸ ⟨hb1, hb2⟩ : u_bot ∈ ({γ_ext rc.s, γ_ext rc.e} : Set S)) with h | h
        · exact hbot_ne_s h
        · exact hbot_ne_e (mem_singleton_iff.mp h)
    · rintro ⟨ht2, hb2⟩
      rcases hhit_tb hB₁ (hBu ▸ subset_union_left) with ht1 | hb1
      · rcases (hBi ▸ ⟨ht1, ht2⟩ : u_top ∈ ({γ_ext rc.s, γ_ext rc.e} : Set S)) with h | h
        · exact htop_ne_s h
        · exact htop_ne_e (mem_singleton_iff.mp h)
      · rcases (hBi ▸ ⟨hb1, hb2⟩ : u_bot ∈ ({γ_ext rc.s, γ_ext rc.e} : Set S)) with h | h
        · exact hbot_ne_s h
        · exact hbot_ne_e (mem_singleton_iff.mp h)
  have hVt_sub_D : V_top ⊆ rc.box := image_mono fun z hz => by
    rw [Complex.mem_reProdIm] at hz ⊢
    exact ⟨by rw [mem_singleton_iff.mp hz.1]; exact ⟨by linarith [rc.ha], rc.ha.le⟩, ⟨by linarith [hz.2.1, rc.hb], hz.2.2⟩⟩
  have hVb_sub_D : V_bot ⊆ rc.box := image_mono fun z hz => by
    rw [Complex.mem_reProdIm] at hz ⊢
    exact ⟨by rw [mem_singleton_iff.mp hz.1]; exact ⟨by linarith [rc.ha], rc.ha.le⟩, ⟨hz.2.1, by linarith [hz.2.2, rc.hb]⟩⟩
  have hVt_inter_γ : V_top ∩ γ_ext '' Icc rc.s rc.e = {γ_ext rc.t_mid} := by
    rw [hγ_se_eq, rc.mid_eq]; ext y; constructor
    · rintro ⟨⟨z, hz, rfl⟩, ⟨w, ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩, hfe⟩⟩
      · have hzw := rc.hgi (by rw [Complex.mem_reProdIm] at hz; exact Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hz.1]; exact ⟨by linarith [rc.ha], rc.ha.le⟩, ⟨by linarith [hz.2.1, rc.hb], hz.2.2⟩⟩) (hsegL_R r hr) hfe.symm
        have hre := congrArg Complex.re hzw
        rw [mem_singleton_iff.mp (Complex.mem_reProdIm.mp hz).1] at hre
        simp only [segL, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] at hre
        have hr1 : r = 1 := by nlinarith [rc.hwL_re]
        rw [hzw, hr1]; simp [segL]
      · have hzw := rc.hgi (by rw [Complex.mem_reProdIm] at hz; exact Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hz.1]; exact ⟨by linarith [rc.ha], rc.ha.le⟩, ⟨by linarith [hz.2.1, rc.hb], hz.2.2⟩⟩) (hsegR_R r hr) hfe.symm
        have hre := congrArg Complex.re hzw
        rw [mem_singleton_iff.mp (Complex.mem_reProdIm.mp hz).1] at hre
        simp only [segR, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] at hre
        have hr0 : r = 0 := by nlinarith [rc.hwR_re]
        rw [hzw, hr0]; simp [segR]
    · rintro rfl
      exact ⟨⟨0, Complex.mem_reProdIm.mpr ⟨rfl, ⟨le_rfl, rc.hb.le⟩⟩, rfl⟩,
        ⟨0, Or.inl ⟨1, ⟨zero_le_one, le_rfl⟩, by simp [segL]⟩, rfl⟩⟩
  have hVb_inter_γ : V_bot ∩ γ_ext '' Icc rc.s rc.e = {γ_ext rc.t_mid} := by
    rw [hγ_se_eq, rc.mid_eq]; ext y; constructor
    · rintro ⟨⟨z, hz, rfl⟩, ⟨w, ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩, hfe⟩⟩
      · have hzw := rc.hgi (by rw [Complex.mem_reProdIm] at hz; exact Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hz.1]; exact ⟨by linarith [rc.ha], rc.ha.le⟩, ⟨hz.2.1, by linarith [hz.2.2, rc.hb]⟩⟩) (hsegL_R r hr) hfe.symm
        have hre := congrArg Complex.re hzw
        rw [mem_singleton_iff.mp (Complex.mem_reProdIm.mp hz).1] at hre
        simp only [segL, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] at hre
        have hr1 : r = 1 := by nlinarith [rc.hwL_re]
        rw [hzw, hr1]; simp [segL]
      · have hzw := rc.hgi (by rw [Complex.mem_reProdIm] at hz; exact Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hz.1]; exact ⟨by linarith [rc.ha], rc.ha.le⟩, ⟨hz.2.1, by linarith [hz.2.2, rc.hb]⟩⟩) (hsegR_R r hr) hfe.symm
        have hre := congrArg Complex.re hzw
        rw [mem_singleton_iff.mp (Complex.mem_reProdIm.mp hz).1] at hre
        simp only [segR, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] at hre
        have hr0 : r = 0 := by nlinarith [rc.hwR_re]
        rw [hzw, hr0]; simp [segR]
    · rintro rfl
      exact ⟨⟨0, Complex.mem_reProdIm.mpr ⟨rfl, by simp [rc.hb.le]⟩, rfl⟩,
        ⟨0, Or.inl ⟨1, ⟨zero_le_one, le_rfl⟩, by simp [segL]⟩, rfl⟩⟩
  have hVt_inter_bd : V_top ∩ discBd rc.box = {u_top} := by
    rw [hD_bd]; ext y; constructor
    · rintro ⟨⟨z, hz, rfl⟩, ⟨w, hwfr, hfe⟩⟩
      have hzw := rc.hgi (by rw [Complex.mem_reProdIm] at hz; exact Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hz.1]; exact ⟨by linarith [rc.ha], rc.ha.le⟩, ⟨by linarith [hz.2.1, rc.hb], hz.2.2⟩⟩) (hR_closed.frontier_subset hwfr) hfe.symm
      rw [Complex.mem_reProdIm] at hz
      have hre : z.re = 0 := mem_singleton_iff.mp hz.1
      have hnotint := (hzw ▸ hwfr).2
      rw [interior_reProdIm, interior_Icc, interior_Icc, Complex.mem_reProdIm] at hnotint
      have him : z.im = rc.b := by
        rcases hz.2.2.eq_or_lt with h | h; · exact h
        exact (hnotint ⟨by rw [hre]; exact ⟨by linarith [rc.ha], rc.ha⟩, ⟨by linarith [hz.2.1, rc.hb], h⟩⟩).elim
      exact congrArg rc.g (Complex.ext (by simp [hre]) (by simp [him]))
    · rintro rfl
      exact ⟨⟨(rc.b : ℂ) * I, Complex.mem_reProdIm.mpr ⟨by simp, by simp [rc.hb.le]⟩, rfl⟩, ⟨(rc.b : ℂ) * I, htop_fr, rfl⟩⟩
  have hVb_inter_bd : V_bot ∩ discBd rc.box = {u_bot} := by
    rw [hD_bd]; ext y; constructor
    · rintro ⟨⟨z, hz, rfl⟩, ⟨w, hwfr, hfe⟩⟩
      have hzw := rc.hgi (by rw [Complex.mem_reProdIm] at hz; exact Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hz.1]; exact ⟨by linarith [rc.ha], rc.ha.le⟩, ⟨hz.2.1, by linarith [hz.2.2, rc.hb]⟩⟩) (hR_closed.frontier_subset hwfr) hfe.symm
      rw [Complex.mem_reProdIm] at hz
      have hre : z.re = 0 := mem_singleton_iff.mp hz.1
      have hnotint := (hzw ▸ hwfr).2
      rw [interior_reProdIm, interior_Icc, interior_Icc, Complex.mem_reProdIm] at hnotint
      have him : z.im = -rc.b := by
        rcases hz.2.1.eq_or_lt with h | h; · exact h.symm
        exact (hnotint ⟨by rw [hre]; exact ⟨by linarith [rc.ha], rc.ha⟩, ⟨h, by linarith [hz.2.2, rc.hb]⟩⟩).elim
      exact congrArg rc.g (Complex.ext (by simp [hre]) (by simp [him]))
    · rintro rfl
      exact ⟨⟨(-(rc.b : ℝ) : ℂ) * I, Complex.mem_reProdIm.mpr ⟨by simp, by simp [rc.hb.le]⟩, rfl⟩, ⟨(-(rc.b : ℝ) : ℂ) * I, hbot_fr, rfl⟩⟩
  have hVt_line : IsLineWithEnds V_top (γ_ext rc.t_mid) u_top := by
    let p : ℝ → S := fun r => rc.g (((r * rc.b : ℝ) : ℂ) * I)
    have hpm : MapsTo (fun r : ℝ => ((r * rc.b : ℝ) : ℂ) * I) (Icc 0 1) R := fun r hr =>
      Complex.mem_reProdIm.mpr ⟨by simp [rc.ha.le], by simp; exact ⟨by nlinarith [hr.1, rc.hb], by nlinarith [hr.2, rc.hb]⟩⟩
    refine isLineWithEnds_of_param (rc.hgc.comp (by fun_prop) hpm)
      (fun r₁ hr₁ r₂ hr₂ he => by
        have := congrArg Complex.im (rc.hgi (hpm hr₁) (hpm hr₂) he)
        simp only [mul_im, ofReal_re, ofReal_im, I_im, I_re, mul_one, mul_zero, add_zero] at this
        exact mul_right_cancel₀ rc.hb.ne' this)
      (by simp [rc.mid_eq]) (by simp [u_top]) ?_
    ext y; constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨((r * rc.b : ℝ) : ℂ) * I, Complex.mem_reProdIm.mpr ⟨by simp, by simp; exact ⟨by nlinarith [hr.1, rc.hb], by nlinarith [hr.2, rc.hb]⟩⟩, rfl⟩
    · rintro ⟨z, hz, rfl⟩; rw [Complex.mem_reProdIm] at hz
      refine ⟨z.im / rc.b, ⟨div_nonneg hz.2.1 rc.hb.le, (div_le_one rc.hb).mpr hz.2.2⟩, congrArg rc.g (Complex.ext ?_ ?_)⟩
      · simp [mem_singleton_iff.mp hz.1]
      · simp [div_mul_cancel₀ _ rc.hb.ne']
  have hVb_line : IsLineWithEnds V_bot (γ_ext rc.t_mid) u_bot := by
    let p : ℝ → S := fun r => rc.g (((-(r * rc.b) : ℝ) : ℂ) * I)
    have hpm : MapsTo (fun r : ℝ => ((-(r * rc.b) : ℝ) : ℂ) * I) (Icc 0 1) R := fun r hr =>
      Complex.mem_reProdIm.mpr ⟨by simp [rc.ha.le], by simp; exact ⟨by nlinarith [hr.2, rc.hb], by nlinarith [hr.1, rc.hb]⟩⟩
    refine isLineWithEnds_of_param (rc.hgc.comp (by fun_prop) hpm)
      (fun r₁ hr₁ r₂ hr₂ he => by
        have := congrArg Complex.im (rc.hgi (hpm hr₁) (hpm hr₂) he)
        simp only [mul_im, ofReal_re, ofReal_im, I_im, I_re, mul_one, mul_zero, add_zero] at this
        nlinarith [rc.hb])
      (by simp [rc.mid_eq]) (by simp [u_bot]) ?_
    ext y; constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨((-(r * rc.b) : ℝ) : ℂ) * I, Complex.mem_reProdIm.mpr ⟨by simp, by simp; exact ⟨by nlinarith [hr.2, rc.hb], by nlinarith [hr.1, rc.hb]⟩⟩, rfl⟩
    · rintro ⟨z, hz, rfl⟩; rw [Complex.mem_reProdIm] at hz
      refine ⟨-z.im / rc.b, ⟨div_nonneg (by linarith [hz.2.2]) rc.hb.le, (div_le_one rc.hb).mpr (by linarith [hz.2.1])⟩, congrArg rc.g (Complex.ext ?_ ?_)⟩
      · simp [mem_singleton_iff.mp hz.1]
      · simp [div_mul_cancel₀ _ rc.hb.ne']
  have hV_side : ∀ {V : Set S} {u : S}, IsLineWithEnds V (γ_ext rc.t_mid) u → V ⊆ rc.box →
      V ∩ γ_ext '' Icc rc.s rc.e = {γ_ext rc.t_mid} → V ∩ discBd rc.box = {u} →
      (u ∈ B₁ → V ⊆ D₁ ∧ V ∩ discBd D₁ = {γ_ext rc.t_mid, u}) ∧
      (u ∈ B₂ → V ⊆ D₂ ∧ V ∩ discBd D₂ = {γ_ext rc.t_mid, u}) := fun {V u} hVl hVD hVγ hVbd => by
    have hpc : IsPreconnected (V \ {γ_ext rc.t_mid}) := by
      obtain ⟨φ, hφ0, -⟩ := hVl
      have h1 : V \ {γ_ext rc.t_mid} = (fun t : unitInterval => (φ t).1) '' Ioc 0 1 := by
        ext x; constructor
        · rintro ⟨hxV, hne⟩
          refine ⟨φ.symm ⟨x, hxV⟩, ⟨lt_of_le_of_ne unitInterval.nonneg' fun h0 => hne ?_, unitInterval.le_one'⟩,
            congrArg Subtype.val (φ.apply_symm_apply _)⟩
          have : (φ 0).1 = x := by rw [h0]; exact congrArg Subtype.val (φ.apply_symm_apply _)
          exact this.symm.trans hφ0
        · rintro ⟨t, ht, rfl⟩
          exact ⟨(φ t).2, fun h => ht.1.ne' (φ.injective (Subtype.ext (h.trans hφ0.symm)))⟩
      rw [h1]; exact isPreconnected_Ioc.image _ (continuous_subtype_val.comp φ.continuous).continuousOn
    have hdisj : (V \ {γ_ext rc.t_mid}) ∩ (D₁ ∩ D₂) = ∅ := by
      rw [eq_empty_iff_forall_notMem, hDi]; rintro x ⟨⟨hxV, hne⟩, hxγ⟩
      exact hne (hVγ ▸ ⟨hxV, hxγ⟩)
    have hsub_or := isPreconnected_iff_subset_of_disjoint_closed.mp hpc D₁ D₂ hD₁.isCompact.isClosed hD₂.isCompact.isClosed
      ((sdiff_subset.trans hVD).trans (hDu ▸ subset_rfl)) hdisj
    have hu_in_V : u ∈ V := by obtain ⟨φ, -, hφ1⟩ := hVl; exact hφ1 ▸ (φ 1).2
    have hmid_in_V : γ_ext rc.t_mid ∈ V := by obtain ⟨φ, hφ0, -⟩ := hVl; exact hφ0 ▸ (φ 0).2
    have hmid_in_γ : γ_ext rc.t_mid ∈ γ_ext '' Icc rc.s rc.e := ⟨rc.t_mid, ⟨rc.hst.le, rc.hte.le⟩, rfl⟩
    have hu_ne_mid : u ≠ γ_ext rc.t_mid := fun h => by
      have : γ_ext rc.t_mid ∈ ({γ_ext rc.s, γ_ext rc.e} : Set S) := hγ_bd ▸ ⟨hmid_in_γ, h ▸ (hVbd ▸ rfl : u ∈ V ∩ discBd rc.box).2⟩
      rcases this with h1 | h1
      · exact rc.hst.ne' (hγi ⟨rc.hs0.le.trans rc.hst.le, rc.hte.le.trans rc.he1.le⟩ ⟨rc.hs0.le, hse.le.trans rc.he1.le⟩ h1)
      · exact rc.hte.ne (hγi ⟨rc.hs0.le.trans rc.hst.le, rc.hte.le.trans rc.he1.le⟩ ⟨rc.hs0.le.trans hse.le, rc.he1.le⟩ (mem_singleton_iff.mp h1))
    constructor
    · intro huB1
      have hsub1 : V ⊆ D₁ := by
        rcases hsub_or with h1 | h2
        · intro x hx; by_cases hx0 : x = γ_ext rc.t_mid
          · rw [hx0]; exact (hDi.symm ▸ hmid_in_γ : γ_ext rc.t_mid ∈ D₁ ∩ D₂).1
          · exact h1 ⟨hx, hx0⟩
        · exfalso
          have huγ : u ∈ γ_ext '' Icc rc.s rc.e := hDi ▸ ⟨GraphMinor.Surface.discBd_subset D₁ (hbD₁ ▸ Or.inl huB1), h2 ⟨hu_in_V, hu_ne_mid⟩⟩
          exact hu_ne_mid (mem_singleton_iff.mp (hVγ ▸ (⟨hu_in_V, huγ⟩ : u ∈ V ∩ γ_ext '' Icc rc.s rc.e)))
      refine ⟨hsub1, ?_⟩
      ext x; constructor
      · rintro ⟨hxV, hxbd1⟩; rw [hbD₁] at hxbd1
        rcases hxbd1 with hxB1 | hxγ
        · exact Or.inr (hVbd ▸ (⟨hxV, hBu ▸ Or.inl hxB1⟩ : x ∈ V ∩ discBd rc.box))
        · exact Or.inl (mem_singleton_iff.mp (hVγ ▸ (⟨hxV, hxγ⟩ : x ∈ V ∩ γ_ext '' Icc rc.s rc.e)))
      · rintro (rfl | hx)
        · exact ⟨hmid_in_V, hbD₁ ▸ Or.inr hmid_in_γ⟩
        · rw [mem_singleton_iff.mp hx]; exact ⟨hu_in_V, hbD₁ ▸ Or.inl huB1⟩
    · intro huB2
      have hsub2 : V ⊆ D₂ := by
        rcases hsub_or with h1 | h2
        · exfalso
          have huγ : u ∈ γ_ext '' Icc rc.s rc.e := hDi ▸ ⟨h1 ⟨hu_in_V, hu_ne_mid⟩, GraphMinor.Surface.discBd_subset D₂ (hbD₂ ▸ Or.inl huB2)⟩
          exact hu_ne_mid (mem_singleton_iff.mp (hVγ ▸ (⟨hu_in_V, huγ⟩ : u ∈ V ∩ γ_ext '' Icc rc.s rc.e)))
        · intro x hx; by_cases hx0 : x = γ_ext rc.t_mid
          · rw [hx0]; exact (hDi.symm ▸ hmid_in_γ : γ_ext rc.t_mid ∈ D₁ ∩ D₂).2
          · exact h2 ⟨hx, hx0⟩
      refine ⟨hsub2, ?_⟩
      ext x; constructor
      · rintro ⟨hxV, hxbd2⟩; rw [hbD₂] at hxbd2
        rcases hxbd2 with hxB2 | hxγ
        · exact Or.inr (hVbd ▸ (⟨hxV, hBu ▸ Or.inr hxB2⟩ : x ∈ V ∩ discBd rc.box))
        · exact Or.inl (mem_singleton_iff.mp (hVγ ▸ (⟨hxV, hxγ⟩ : x ∈ V ∩ γ_ext '' Icc rc.s rc.e)))
      · rintro (rfl | hx)
        · exact ⟨hmid_in_V, hbD₂ ▸ Or.inr hmid_in_γ⟩
        · rw [mem_singleton_iff.mp hx]; exact ⟨hu_in_V, hbD₂ ▸ Or.inl huB2⟩
  have hA_split : A ∩ rc.box = V_top ∪ V_bot := by
    rw [RectCross.box, rc.hA_eq, ← image_union]; congr 1
    ext z; simp only [mem_union, Complex.mem_reProdIm, mem_singleton_iff, mem_Icc]
    constructor
    · rintro ⟨hre, h1, h2⟩; rcases le_total 0 z.im with h | h
      · exact Or.inl ⟨hre, h, h2⟩
      · exact Or.inr ⟨hre, h1, h⟩
    · rintro (⟨hre, h1, h2⟩ | ⟨hre, h1, h2⟩)
      · exact ⟨hre, by linarith, h2⟩
      · exact ⟨hre, h1, by linarith⟩
  have htop_ne_mid : u_top ≠ γ_ext rc.t_mid := fun h => by
    have := congrArg Complex.im (rc.hgi htop_R (interior_subset h0R) (h.trans rc.mid_eq)); simp at this; linarith [rc.hb]
  have hbot_ne_mid : u_bot ≠ γ_ext rc.t_mid := fun h => by
    have := congrArg Complex.im (rc.hgi hbot_R (interior_subset h0R) (h.trans rc.mid_eq)); simp at this; linarith [rc.hb]
  rcases (hBu.symm ▸ htop_bd : u_top ∈ B₁ ∪ B₂) with ht1 | ht2 <;>
  rcases (hBu.symm ▸ hbot_bd : u_bot ∈ B₁ ∪ B₂) with hb1 | hb2
  · exact (hsep_B.1 ⟨ht1, hb1⟩).elim
  · obtain ⟨h1sub, h1bd⟩ := (hV_side hVt_line hVt_sub_D hVt_inter_γ hVt_inter_bd).1 ht1
    obtain ⟨h2sub, h2bd⟩ := (hV_side hVb_line hVb_sub_D hVb_inter_γ hVb_inter_bd).2 hb2
    exact ⟨D₁, D₂, V_top, V_bot, u_top, u_bot, hD, hD₁, hD₂, hDu, hDi, hγ_bd, hA_split,
      h1sub, h2sub, hVt_line, hVb_line, h1bd, h2bd, htop_ne_mid, hbot_ne_mid⟩
  · obtain ⟨h1sub, h1bd⟩ := (hV_side hVb_line hVb_sub_D hVb_inter_γ hVb_inter_bd).1 hb1
    obtain ⟨h2sub, h2bd⟩ := (hV_side hVt_line hVt_sub_D hVt_inter_γ hVt_inter_bd).2 ht2
    exact ⟨D₁, D₂, V_bot, V_top, u_bot, u_top, hD, hD₁, hD₂, hDu, hDi, hγ_bd, hA_split.trans (union_comm _ _),
      h1sub, h2sub, hVb_line, hVt_line, h1bd, h2bd, hbot_ne_mid, htop_ne_mid⟩
  · exact (hsep_B.2 ⟨ht2, hb2⟩).elim

/-- **Band-surgery input data along a multi-crossing interior arc**:
An injective interior arc `γ_ext : [0, 1] → (bd S)ᶜ` connecting two distinct components of `M`
(crossed cleanly inside `rcL` and `rcR`) while crossing `k` distinct `Q (idxs r)` (`r : Fin k`, all
disjoint from `M.U`) cleanly inside pairwise disjoint `RectCross`es `rcM r`, with `γ_ext '' [tL, tR]`
otherwise disjoint from `M.U ∪ ⋃ Q`. -/
structure BandArcData (S : Type) [TopologicalSpace S] {s t : S} (M : ProperManifold S s t)
    {m : ℕ} (Q : Fin m → Set S) (k : ℕ) where
  γ_ext : ℝ → S
  idxs : Fin k → Fin m
  hidxs_inj : Function.Injective idxs
  hidxs_disj : ∀ r : Fin k, Disjoint M.U (Q (idxs r))
  hγc : ContinuousOn γ_ext (Icc 0 1)
  hγi : InjOn γ_ext (Icc 0 1)
  hγint : γ_ext '' Icc 0 1 ⊆ (bd S)ᶜ
  rcL : RectCross S γ_ext M.U
  rcR : RectCross S γ_ext M.U
  rcM : ∀ r : Fin k, RectCross S γ_ext (Q (idxs r))
  hL_lt_R : rcL.e < rcR.s
  hM_order : ∀ r : Fin k, rcL.e < (rcM r).s ∧ (rcM r).e < rcR.s
  hM_disj : ∀ r₁ r₂ : Fin k, r₁ ≠ r₂ → Disjoint (rcM r₁).box (rcM r₂).box
  hL_disj_R : Disjoint rcL.box rcR.box
  hL_disj_M : ∀ r : Fin k, Disjoint rcL.box (rcM r).box
  hR_disj_M : ∀ r : Fin k, Disjoint rcR.box (rcM r).box
  hL_disj_Q : ∀ j : Fin m, Disjoint rcL.box (Q j)
  hR_disj_Q : ∀ j : Fin m, Disjoint rcR.box (Q j)
  hM_disj_M : ∀ r : Fin k, Disjoint (rcM r).box M.U
  hM_disj_Q : ∀ r : Fin k, ∀ j : Fin m, j ≠ idxs r → Disjoint (rcM r).box (Q j)
  hγ_clean_M : ∀ r ∈ Icc rcL.t_mid rcR.t_mid, γ_ext r ∈ M.U → r = rcL.t_mid ∨ r = rcR.t_mid
  hγ_clean_Q : ∀ r ∈ Icc rcL.t_mid rcR.t_mid, ∀ j : Fin m, γ_ext r ∈ Q j →
    ∃ q : Fin k, j = idxs q ∧ r = (rcM q).t_mid
  hdiff_comp : ¬ (γ_ext rcL.t_mid ∈ M.P₀ ∧ γ_ext rcR.t_mid ∈ M.P₀) ∧
    ∀ a ∈ M.Os, ¬ (γ_ext rcL.t_mid ∈ a.O ∧ γ_ext rcR.t_mid ∈ a.O)

/-- Pull a single `RectCross S γ_ext A` (whose box lies in `K '' O`) back into a strip chart
`(O, K, θ)` of `γ_ext` and straighten its chord `A` via `exists_disc_cross_straightener`. -/
private theorem rectCross_straighten_in_strip [T2Space S] {γ_ext : ℝ → S} {A : Set S}
    (hγc : ContinuousOn γ_ext (Icc 0 1)) (hγi : InjOn γ_ext (Icc 0 1))
    {O : Set ℂ} {K : ℂ → S} {θ : unitInterval → ℝ}
    (hOo : IsOpen O) (hKc : ContinuousOn K O) (hKi : InjOn K O)
    (hKopen : ∀ W, IsOpen W → W ⊆ O → IsOpen (K '' W))
    (hθc : Continuous θ) (hθm : StrictMono θ)
    (hθ_in_O : ∀ r : unitInterval, (θ r : ℂ) ∈ O ∧ K (θ r) = γ_ext r.1)
    (rc : RectCross S γ_ext A) (hbox_in_KO : rc.box ⊆ K '' O) :
    ∃ (E : Set ℂ) (a_i b_i x_i η_i : ℝ) (α_i : ℂ ≃ₜ ℂ),
      IsClosedDisc E ∧ E ⊆ O ∧ K '' E = rc.box ∧
      a_i = θ ⟨rc.s, rc.hs0.le, (rc.hst.trans rc.hte).le.trans rc.he1.le⟩ ∧
      b_i = θ ⟨rc.e, rc.hs0.le.trans (rc.hst.trans rc.hte).le, rc.he1.le⟩ ∧
      x_i = θ ⟨rc.t_mid, rc.hs0.le.trans rc.hst.le, rc.hte.le.trans rc.he1.le⟩ ∧
      a_i < x_i ∧ x_i < b_i ∧ 0 < η_i ∧
      Icc (x_i - η_i) (x_i + η_i) ×ℂ Icc (-η_i) η_i ⊆ discInt E ∧
      (∀ z ∈ (discInt E)ᶜ, α_i z = z) ∧
      (∀ z ∈ Icc a_i b_i ×ℂ ({0} : Set ℝ), α_i z = z) ∧
      (α_i '' (E ∩ K ⁻¹' A)) ∩ (Icc (x_i - η_i) (x_i + η_i) ×ℂ Icc (-η_i) η_i) =
        ({x_i} : Set ℝ) ×ℂ Icc (-η_i) η_i := by
  classical
  obtain ⟨D₁, D₂, A₁, A₂, u, v, hD, hD₁, hD₂, hDu, hDi, hγbd, hAeq, hA₁sub, hA₂sub,
    hA₁l, hA₂l, hA₁bd, hA₂bd, hux, hvx⟩ := rectCross_split hγc hγi rc
  let E : Set ℂ := O ∩ K ⁻¹' rc.box
  have hKE : K '' E = rc.box := by
    ext y; constructor
    · rintro ⟨z, hz, rfl⟩; exact hz.2
    · intro hy; obtain ⟨z, hzO, rfl⟩ := hbox_in_KO hy; exact ⟨z, ⟨hzO, hy⟩, rfl⟩
  have hE_sub_O : E ⊆ O := inter_subset_left
  let Kinv : S → ℂ := fun y => if hy : y ∈ K '' O then Classical.choose hy else 0
  have hKinv_O : ∀ y ∈ K '' O, Kinv y ∈ O ∧ K (Kinv y) = y := fun y hy => by
    simp only [Kinv, dite_eq_left hy]; exact Classical.choose_spec hy
  have hKinv_left : LeftInvOn Kinv K O := fun z hzO =>
    hKi (hKinv_O (K z) ⟨z, hzO, rfl⟩).1 hzO (hKinv_O (K z) ⟨z, hzO, rfl⟩).2
  have hKinv_c : ContinuousOn Kinv (K '' O) := by
    rw [_root_.continuousOn_iff]
    intro y hy W hWo hWy
    have hKW'o : IsOpen (K '' (W ∩ O)) := hKopen (W ∩ O) (hWo.inter hOo) inter_subset_right
    refine ⟨K '' (W ∩ O), hKW'o, ⟨Kinv y, ⟨hWy, (hKinv_O y hy).1⟩, (hKinv_O y hy).2⟩, ?_⟩
    rintro y' ⟨⟨z, ⟨hzW, hzO⟩, rfl⟩, -⟩
    rwa [mem_preimage, hKinv_left hzO]
  have hKinv_E : Kinv '' rc.box = E := by
    rw [← hKE]; ext z; constructor
    · rintro ⟨_, ⟨w, hwE, rfl⟩, rfl⟩; rwa [hKinv_left (hE_sub_O hwE)]
    · intro hzE; exact ⟨K z, ⟨z, hzE, rfl⟩, hKinv_left (hE_sub_O hzE)⟩
  have hKinv_inj : InjOn Kinv (K '' O) := fun y₁ hy₁ y₂ hy₂ he => by
    rw [← (hKinv_O y₁ hy₁).2, ← (hKinv_O y₂ hy₂).2, he]
  have hE_pair := hD.image (hKinv_c.mono hbox_in_KO) (hKc.mono (hKinv_E ▸ hE_sub_O))
    (fun y hy => (hKinv_O y (hbox_in_KO hy)).2)
  rw [hKinv_E] at hE_pair
  let E₁ := Kinv '' D₁; let E₂ := Kinv '' D₂
  let F₁ := Kinv '' A₁; let F₂ := Kinv '' A₂
  have hD1_sub : D₁ ⊆ rc.box := hDu ▸ subset_union_left
  have hD2_sub : D₂ ⊆ rc.box := hDu ▸ subset_union_right
  have hE₁_pair := hD₁.image (hKinv_c.mono (hD1_sub.trans hbox_in_KO))
    (hKc.mono ((image_mono hD1_sub).trans (hKinv_E ▸ hE_sub_O))) (fun y hy => (hKinv_O y (hbox_in_KO (hD1_sub hy))).2)
  have hE₂_pair := hD₂.image (hKinv_c.mono (hD2_sub.trans hbox_in_KO))
    (hKc.mono ((image_mono hD2_sub).trans (hKinv_E ▸ hE_sub_O))) (fun y hy => (hKinv_O y (hbox_in_KO (hD2_sub hy))).2)
  have hEu : E₁ ∪ E₂ = E := by rw [← image_union, hDu, hKinv_E]
  let ts : unitInterval := ⟨rc.s, rc.hs0.le, (rc.hst.trans rc.hte).le.trans rc.he1.le⟩
  let tm : unitInterval := ⟨rc.t_mid, rc.hs0.le.trans rc.hst.le, rc.hte.le.trans rc.he1.le⟩
  let te : unitInterval := ⟨rc.e, rc.hs0.le.trans (rc.hst.trans rc.hte).le, rc.he1.le⟩
  have ha_lt_x : θ ts < θ tm := hθm rc.hst
  have hx_lt_b : θ tm < θ te := hθm rc.hte
  have hH_eq : Kinv '' (γ_ext '' Icc rc.s rc.e) = Icc (θ ts) (θ te) ×ℂ ({0} : Set ℝ) := by
    ext z; constructor
    · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
      let tr : unitInterval := ⟨r, rc.hs0.le.trans hr.1, hr.2.trans rc.he1.le⟩
      have htr_K : γ_ext r = K (θ tr) := (hθ_in_O tr).2.symm
      rw [htr_K, hKinv_left (hθ_in_O tr).1]
      exact Complex.mem_reProdIm.mpr ⟨⟨hθm.monotone (show ts ≤ tr from hr.1), hθm.monotone (show tr ≤ te from hr.2)⟩, rfl⟩
    · intro hz; rw [Complex.mem_reProdIm] at hz
      have hzim : z.im = 0 := mem_singleton_iff.mp hz.2
      let fn : ℝ → ℝ := fun r => if hr : r ∈ Icc (0 : ℝ) 1 then θ ⟨r, hr⟩ else 0
      have hfn_c : ContinuousOn fn (Icc rc.s rc.e) :=
        (by rw [continuousOn_iff_continuous_domRestrict]
            exact hθc.congr fun r => by simp only [Set.domRestrict, fn, dite_eq_left r.2] : ContinuousOn fn (Icc 0 1)).mono
          (Icc_subset_Icc rc.hs0.le rc.he1.le)
      have hfns : fn rc.s = θ ts := by simp only [fn, dite_eq_left (show rc.s ∈ Icc (0 : ℝ) 1 from ts.2)]; rfl
      have hfne : fn rc.e = θ te := by simp only [fn, dite_eq_left (show rc.e ∈ Icc (0 : ℝ) 1 from te.2)]; rfl
      obtain ⟨r, hr, hreq⟩ := intermediate_value_Icc (rc.hst.trans rc.hte).le hfn_c
        (show z.re ∈ Icc (fn rc.s) (fn rc.e) from by rw [hfns, hfne]; exact hz.1)
      have hr01 : r ∈ Icc (0 : ℝ) 1 := ⟨rc.hs0.le.trans hr.1, hr.2.trans rc.he1.le⟩
      simp only [fn, dite_eq_left hr01] at hreq
      let tr : unitInterval := ⟨r, hr01⟩
      have hz_eq : z = (θ tr : ℂ) := Complex.ext (by simpa [tr] using hreq.symm) (by simp [hzim])
      refine ⟨γ_ext r, ⟨r, hr, rfl⟩, ?_⟩
      rw [(hθ_in_O tr).2.symm, hKinv_left (hθ_in_O tr).1, hz_eq]
  have hEi : E₁ ∩ E₂ = Icc (θ ts) (θ te) ×ℂ ({0} : Set ℝ) := by
    rw [← hH_eq, ← hDi]
    exact (hKinv_inj.image_inter (hD1_sub.trans hbox_in_KO) (hD2_sub.trans hbox_in_KO)).symm
  have hHsub : Icc (θ ts) (θ te) ×ℂ ({0} : Set ℝ) ⊆ E := by rw [← hEi]; exact inter_subset_left.trans (hEu ▸ subset_union_left)
  have hHbd : (Icc (θ ts) (θ te) ×ℂ ({0} : Set ℝ)) ∩ discBd E = {(θ ts : ℂ), (θ te : ℂ)} := by
    rw [← hH_eq, hE_pair.2]
    have hγ_sub_KO : γ_ext '' Icc rc.s rc.e ⊆ K '' O := (hDi ▸ inter_subset_left.trans hD1_sub).trans hbox_in_KO
    have hbd_sub_KO : discBd rc.box ⊆ K '' O := (GraphMinor.Surface.discBd_subset _).trans hbox_in_KO
    rw [← hKinv_inj.image_inter hγ_sub_KO hbd_sub_KO, hγbd, image_pair]
    change ({Kinv (γ_ext ts.1), Kinv (γ_ext te.1)} : Set ℂ) = _
    rw [(hθ_in_O ts).2.symm, (hθ_in_O te).2.symm, hKinv_left (hθ_in_O ts).1, hKinv_left (hθ_in_O te).1]
  have hline_pull : ∀ {L : Set S} {p q : S}, L ⊆ rc.box → IsLineWithEnds L p q →
      IsLineWithEnds (Kinv '' L) (Kinv p) (Kinv q) := fun {L p q} hL hLl => by
    obtain ⟨φ, hφ0, hφ1⟩ := hLl
    have hpc : ContinuousOn (fun r : ℝ => if hr : r ∈ Icc (0 : ℝ) 1 then Kinv (φ ⟨r, hr⟩).1 else 0) (Icc 0 1) := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact ((hKinv_c.mono (hL.trans hbox_in_KO)).comp_continuous
        (continuous_subtype_val.comp φ.continuous) (fun t => (φ t).2)).congr fun t => by
          simp only [Set.domRestrict, Function.comp, dite_eq_left t.2]
    have hpi : InjOn (fun r : ℝ => if hr : r ∈ Icc (0 : ℝ) 1 then Kinv (φ ⟨r, hr⟩).1 else 0) (Icc 0 1) := by
      intro r₁ hr₁ r₂ hr₂ he
      simp only [dite_eq_left hr₁, dite_eq_left hr₂] at he
      have := hKinv_inj (hbox_in_KO (hL (φ ⟨r₁, hr₁⟩).2)) (hbox_in_KO (hL (φ ⟨r₂, hr₂⟩).2)) he
      exact congrArg Subtype.val (φ.injective (Subtype.ext this))
    refine isLineWithEnds_of_param hpc hpi (by simp [hφ0]) (by simp [hφ1]) ?_
    ext z; constructor
    · rintro ⟨r, hr, rfl⟩; simp only [dite_eq_left hr]; exact ⟨(φ ⟨r, hr⟩).1, (φ ⟨r, hr⟩).2, rfl⟩
    · rintro ⟨y, hyL, rfl⟩
      let t := φ.symm ⟨y, hyL⟩
      refine ⟨t.1, t.2, ?_⟩; simp only [dite_eq_left t.2]
      have : (φ t).1 = y := congrArg Subtype.val (φ.apply_symm_apply _)
      rw [this]
  have hKinv_tm : Kinv (γ_ext rc.t_mid) = (θ tm : ℂ) := by
    change Kinv (γ_ext tm.1) = _; rw [(hθ_in_O tm).2.symm, hKinv_left (hθ_in_O tm).1]
  have hF₁l : IsLineWithEnds F₁ (θ tm : ℂ) (Kinv u) := hKinv_tm ▸ hline_pull (hA₁sub.trans hD1_sub) hA₁l
  have hF₂l : IsLineWithEnds F₂ (θ tm : ℂ) (Kinv v) := hKinv_tm ▸ hline_pull (hA₂sub.trans hD2_sub) hA₂l
  have hF₁bd : F₁ ∩ discBd E₁ = {(θ tm : ℂ), Kinv u} := by
    rw [hE₁_pair.2, ← hKinv_inj.image_inter (hA₁sub.trans (hD1_sub.trans hbox_in_KO)) ((GraphMinor.Surface.discBd_subset D₁).trans (hD1_sub.trans hbox_in_KO)),
      hA₁bd, image_pair, hKinv_tm]
  have hF₂bd : F₂ ∩ discBd E₂ = {(θ tm : ℂ), Kinv v} := by
    rw [hE₂_pair.2, ← hKinv_inj.image_inter (hA₂sub.trans (hD2_sub.trans hbox_in_KO)) ((GraphMinor.Surface.discBd_subset D₂).trans (hD2_sub.trans hbox_in_KO)),
      hA₂bd, image_pair, hKinv_tm]
  have hu_in_KO : u ∈ K '' O := hbox_in_KO (hD1_sub (GraphMinor.Surface.discBd_subset D₁ (hA₁bd ▸ Or.inr rfl : u ∈ A₁ ∩ discBd D₁).2))
  have hv_in_KO : v ∈ K '' O := hbox_in_KO (hD2_sub (GraphMinor.Surface.discBd_subset D₂ (hA₂bd ▸ Or.inr rfl : v ∈ A₂ ∩ discBd D₂).2))
  have htm_in_KO : γ_ext rc.t_mid ∈ K '' O := ⟨θ tm, (hθ_in_O tm).1, (hθ_in_O tm).2⟩
  have hux' : Kinv u ≠ (θ tm : ℂ) := fun h => hux (hKinv_inj hu_in_KO htm_in_KO (h.trans hKinv_tm.symm))
  have hvx' : Kinv v ≠ (θ tm : ℂ) := fun h => hvx (hKinv_inj hv_in_KO htm_in_KO (h.trans hKinv_tm.symm))
  obtain ⟨η_i, α_i, hη_i, hsq_i, hfix_out, hfix_H, hα_sq⟩ :=
    exists_disc_cross_straightener hE_pair.1 ha_lt_x hx_lt_b hE₁_pair.1 hE₂_pair.1 hEu hEi hHsub hHbd
      (image_mono hA₁sub) (image_mono hA₂sub) hF₁l hF₂l hF₁bd hF₂bd hux' hvx'
  have hF12_eq : F₁ ∪ F₂ = E ∩ K ⁻¹' A := by
    rw [← image_union, ← hAeq]; ext z; constructor
    · rintro ⟨y, ⟨hyA, hybox⟩, rfl⟩
      have hzO := (hKinv_O y (hbox_in_KO hybox)).1
      have hKy := (hKinv_O y (hbox_in_KO hybox)).2
      exact ⟨⟨hzO, by rwa [mem_preimage, hKy]⟩, by rwa [mem_preimage, hKy]⟩
    · rintro ⟨⟨hzO, hzbox⟩, hzA⟩
      exact ⟨K z, ⟨hzA, hzbox⟩, hKinv_left hzO⟩
  exact ⟨E, θ ts, θ te, θ tm, η_i, α_i, hE_pair.1, hE_sub_O, hKE, rfl, rfl, rfl,
    ha_lt_x, hx_lt_b, hη_i, hsq_i, hfix_out, hfix_H, hF12_eq ▸ hα_sq⟩

/-- **Master multi-crossing band surgery theorem**:
Given `data : BandArcData S M Q k`, thickens `data.γ_ext` into an interior closed rectangle
`Δ ⊆ (bd S)ᶜ` aligned with every crossing box `rcL, rcM r, rcR`, and applies `rectangle_surgery`
to obtain a new `ProperManifold` `M'` with:
1. `M'.Os.length + 1 = M.Os.length` (strictly fewer `O`-arcs!),
2. `M'.w1Total AS = M.w1Total AS` and `BdCohRel s t ωM' ωM`,
3. For every `j ∉ range data.idxs`: `M'.U ∩ Q j = M.U ∩ Q j`, and `IsSimpleCrossing M.U (Q j) → IsSimpleCrossing M'.U (Q j)`,
4. For every `r : Fin k`: `(M'.U ∩ Q (data.idxs r)).Nonempty ∧ (M'.U ∩ Q (data.idxs r)).Finite ∧ (M'.U ∩ Q (data.idxs r)).ncard ≤ 2 ∧ IsSimpleCrossing M'.U (Q (data.idxs r))`! -/
theorem band_surgery_along_arc [ConnectedSpace S] (hS : IsSurface S) (AS : SurfAtlas S)
    {s t : S} (hst : s ≠ t) {m : ℕ} {Q : Fin m → Set S}
    (hQclosed : ∀ j, IsClosed (Q j))
    (M : ProperManifold S s t) {k : ℕ} (data : BandArcData S M Q k) :
    ∃ M' : ProperManifold S s t,
      M'.Os.length + 1 = M.Os.length ∧
      M'.w1Total AS = M.w1Total AS ∧
      (∀ ωM ωM', IsCrossingCocycle M.U ωM → IsCrossingCocycle M'.U ωM' → BdCohRel s t ωM' ωM) ∧
      (∀ j : Fin m, j ∉ range data.idxs →
        M'.U ∩ Q j = M.U ∩ Q j ∧ (IsSimpleCrossing M.U (Q j) → IsSimpleCrossing M'.U (Q j))) ∧
      (∀ r : Fin k,
        (M'.U ∩ Q (data.idxs r)).Nonempty ∧
        (M'.U ∩ Q (data.idxs r)).Finite ∧
        (M'.U ∩ Q (data.idxs r)).ncard ≤ 2 ∧
        IsSimpleCrossing M'.U (Q (data.idxs r))) := by
  classical
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  -- Step 1: Cap `S` to a closed surface `T` and build a single strip chart `(O, K, θ)` for `data.γ_ext` into `(bd S)ᶜ`:
  obtain ⟨T, _, j, Kcap, hT, hj, hKcap, hcov, hinter, -⟩ := exists_capAll S hS
  have : T2Space T := hT.2.1
  have hji := hj.injective
  let a_ext : unitInterval → S := fun r => data.γ_ext r.1
  have ha_arc : IsArcMap a_ext := ⟨continuousOn_iff_continuous_domRestrict.mp data.hγc,
    fun r₁ r₂ he => Subtype.ext (data.hγi r₁.2 r₂.2 he)⟩
  obtain ⟨O₀, K₀, θ, hK₀, hθc, hθm, hθ⟩ :=
    exists_stripChart_of_arc hT ⟨hj.continuous.comp ha_arc.1, hji.comp ha_arc.2⟩
  have hjint_open : IsOpen (j '' (bd S)ᶜ) := by
    have heq : j '' (bd S)ᶜ = Kcapᶜ := by
      ext y; constructor
      · rintro ⟨x, hx, rfl⟩ hyK
        have : j x ∈ j '' bd S := hinter ▸ ⟨⟨x, rfl⟩, hyK⟩
        obtain ⟨x', hx', he⟩ := this; exact hx (hji he ▸ hx')
      · intro hyK
        have hyr : y ∈ range j := (Set.ext_iff.mp hcov y).mpr (mem_univ y) |>.resolve_right hyK
        obtain ⟨x, rfl⟩ := hyr
        exact ⟨x, fun hx => hyK (hinter.symm ▸ ⟨x, hx, rfl⟩ : j x ∈ range j ∩ Kcap).2, rfl⟩
    rw [heq]; exact hKcap.isOpen_compl
  let O : Set ℂ := O₀ ∩ K₀ ⁻¹' (j '' (bd S)ᶜ)
  have hOo : IsOpen O := by
    rw [isOpen_iff_mem_nhds]; intro z ⟨hz0, hz1⟩
    have h1 := hK₀.hc.continuousWithinAt hz0 (hjint_open.mem_nhds hz1)
    rw [nhdsWithin_eq_nhds.mpr (hK₀.isOpen.mem_nhds hz0)] at h1
    exact Filter.inter_mem (hK₀.isOpen.mem_nhds hz0) h1
  let K : ℂ → S := fun z => if hz : K₀ z ∈ range j then Classical.choose hz else s
  have hjK : ∀ z ∈ O, j (K z) = K₀ z := fun z hz => by
    have hr : K₀ z ∈ range j := by obtain ⟨x, -, hx⟩ := hz.2; exact ⟨x, hx⟩
    simp only [K, dite_eq_left hr]; exact Classical.choose_spec hr
  have hK_int : ∀ z ∈ O, K z ∈ (bd S)ᶜ := fun z hz => by
    obtain ⟨x, hx, hxe⟩ := hz.2
    exact (hji ((hjK z hz).trans hxe.symm)) ▸ hx
  have hKc : ContinuousOn K O := by
    rw [continuousOn_iff_continuous_domRestrict, hj.continuous_iff]
    exact (hK₀.hc.mono inter_subset_left).domRestrict.congr fun z => (hjK z.1 z.2).symm
  have hKi : InjOn K O := fun z₁ hz₁ z₂ hz₂ he =>
    hK₀.hi hz₁.1 hz₂.1 (by rw [← hjK z₁ hz₁, ← hjK z₂ hz₂, he])
  have hKopen : ∀ W, IsOpen W → W ⊆ O → IsOpen (K '' W) := fun W hWo hWO =>
    isOpen_image_of_manifold hWo (hKc.mono hWO) (hKi.mono hWO) (fun _ _ => hS.2.2 _)
  have hKO_open : IsOpen (K '' O) := hKopen O hOo subset_rfl
  have hθ_in_O : ∀ r : unitInterval, (θ r : ℂ) ∈ O ∧ K (θ r) = data.γ_ext r.1 := fun r => by
    have h1 := hθ r
    have hm : K₀ (θ r) ∈ j '' (bd S)ᶜ := h1.2.symm ▸ ⟨data.γ_ext r.1, data.hγint ⟨r.1, r.2, rfl⟩, rfl⟩
    refine ⟨⟨h1.1, hm⟩, hji ((hjK _ ⟨h1.1, hm⟩).trans h1.2)⟩
  -- Step 2: Independently shrink `rcL`, `rcR`, and each `rcM r` into `K '' O` and straighten each!
  let tL_u : unitInterval := ⟨data.rcL.t_mid, data.rcL.hs0.le.trans data.rcL.hst.le, data.rcL.hte.le.trans data.rcL.he1.le⟩
  let tR_u : unitInterval := ⟨data.rcR.t_mid, data.rcR.hs0.le.trans data.rcR.hst.le, data.rcR.hte.le.trans data.rcR.he1.le⟩
  let tM_u : Fin k → unitInterval := fun r =>
    ⟨(data.rcM r).t_mid, (data.rcM r).hs0.le.trans (data.rcM r).hst.le, (data.rcM r).hte.le.trans (data.rcM r).he1.le⟩
  obtain ⟨lamL, hlamL0, hlamL1, hboxL_KO⟩ := data.rcL.exists_shrink_subset hKO_open ⟨θ tL_u, (hθ_in_O tL_u).1, (hθ_in_O tL_u).2⟩
  obtain ⟨lamR, hlamR0, hlamR1, hboxR_KO⟩ := data.rcR.exists_shrink_subset hKO_open ⟨θ tR_u, (hθ_in_O tR_u).1, (hθ_in_O tR_u).2⟩
  have hM_shrink : ∀ r : Fin k, ∃ (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1), ((data.rcM r).shrink h0 h1).box ⊆ K '' O := fun r =>
    (data.rcM r).exists_shrink_subset hKO_open ⟨θ (tM_u r), (hθ_in_O (tM_u r)).1, (hθ_in_O (tM_u r)).2⟩
  choose lamM hlamM0 hlamM1 hboxM_KO using hM_shrink
  let rcL := data.rcL.shrink hlamL0 hlamL1
  let rcR := data.rcR.shrink hlamR0 hlamR1
  let rcM : ∀ r : Fin k, RectCross S data.γ_ext (Q (data.idxs r)) := fun r => (data.rcM r).shrink (hlamM0 r) (hlamM1 r)
  have hrcL_sub : rcL.box ⊆ data.rcL.box := data.rcL.shrink_box_subset hlamL0 hlamL1
  have hrcR_sub : rcR.box ⊆ data.rcR.box := data.rcR.shrink_box_subset hlamR0 hlamR1
  have hrcM_sub : ∀ r : Fin k, (rcM r).box ⊆ (data.rcM r).box := fun r => (data.rcM r).shrink_box_subset (hlamM0 r) (hlamM1 r)
  obtain ⟨EL, aL, bL, xL, ηL, αL, -, hEL_O, hKEL, haL_eq, hbL_eq, hxL_eq, -, -, hηL_pos, hsqL_sub, hαL_out, hαL_H, hαL_sq⟩ :=
    rectCross_straighten_in_strip data.hγc data.hγi hOo hKc hKi hKopen hθc hθm hθ_in_O rcL hboxL_KO
  obtain ⟨ER, aR, bR, xR, ηR, αR, -, hER_O, hKER, haR_eq, hbR_eq, hxR_eq, -, -, hηR_pos, hsqR_sub, hαR_out, hαR_H, hαR_sq⟩ :=
    rectCross_straighten_in_strip data.hγc data.hγi hOo hKc hKi hKopen hθc hθm hθ_in_O rcR hboxR_KO
  have hM_str : ∀ r : Fin k, ∃ (E : Set ℂ) (a_i b_i x_i η_i : ℝ) (α_i : ℂ ≃ₜ ℂ),
      IsClosedDisc E ∧ E ⊆ O ∧ K '' E = (rcM r).box ∧
      a_i = θ ⟨(rcM r).s, (rcM r).hs0.le, ((rcM r).hst.trans (rcM r).hte).le.trans (rcM r).he1.le⟩ ∧
      b_i = θ ⟨(rcM r).e, (rcM r).hs0.le.trans ((rcM r).hst.trans (rcM r).hte).le, (rcM r).he1.le⟩ ∧
      x_i = θ ⟨(rcM r).t_mid, (rcM r).hs0.le.trans (rcM r).hst.le, (rcM r).hte.le.trans (rcM r).he1.le⟩ ∧
      a_i < x_i ∧ x_i < b_i ∧ 0 < η_i ∧
      Icc (x_i - η_i) (x_i + η_i) ×ℂ Icc (-η_i) η_i ⊆ discInt E ∧
      (∀ z ∈ (discInt E)ᶜ, α_i z = z) ∧
      (∀ z ∈ Icc a_i b_i ×ℂ ({0} : Set ℝ), α_i z = z) ∧
      (α_i '' (E ∩ K ⁻¹' Q (data.idxs r))) ∩ (Icc (x_i - η_i) (x_i + η_i) ×ℂ Icc (-η_i) η_i) =
        ({x_i} : Set ℝ) ×ℂ Icc (-η_i) η_i := fun r =>
    rectCross_straighten_in_strip data.hγc data.hγi hOo hKc hKi hKopen hθc hθm hθ_in_O (rcM r) (hboxM_KO r)
  choose EM aM bM xM ηM αM _ hEM_O hKEM haM_eq hbM_eq hxM_eq _ _ hηM_pos hsqM_sub hαM_out hαM_H hαM_sq using hM_str
  -- Step 3: Pack the `N = k + 2` non-dependent pieces into `Fin (k + 2)` and compose `α_i`:
  let N : ℕ := k + 2
  let iL : Fin N := ⟨0, by omega⟩
  let iR : Fin N := ⟨k + 1, by omega⟩
  let iM : Fin k → Fin N := fun r => ⟨r.1 + 1, by omega⟩
  let E : Fin N → Set ℂ := fun i =>
    if h0 : i.1 = 0 then EL else if hk : i.1 = k + 1 then ER else EM ⟨i.1 - 1, by omega⟩
  let x_i : Fin N → ℝ := fun i =>
    if h0 : i.1 = 0 then xL else if hk : i.1 = k + 1 then xR else xM ⟨i.1 - 1, by omega⟩
  let η_i : Fin N → ℝ := fun i =>
    if h0 : i.1 = 0 then ηL else if hk : i.1 = k + 1 then ηR else ηM ⟨i.1 - 1, by omega⟩
  let α_i : Fin N → ℂ ≃ₜ ℂ := fun i =>
    if h0 : i.1 = 0 then αL else if hk : i.1 = k + 1 then αR else αM ⟨i.1 - 1, by omega⟩
  have hEL_eq : E iL = EL := by simp [E, iL]
  have hER_eq : E iR = ER := by simp [E, iR]
  have hEM_eq : ∀ r : Fin k, E (iM r) = EM r := fun r => by simp [E, iM, r.2.ne]
  have hαL_eq : α_i iL = αL := by simp [α_i, iL]
  have hαR_eq : α_i iR = αR := by simp [α_i, iR]
  have hαM_eq : ∀ r : Fin k, α_i (iM r) = αM r := fun r => by simp [α_i, iM, r.2.ne]
  have hηL_eq : η_i iL = ηL := by simp [η_i, iL]
  have hηR_eq : η_i iR = ηR := by simp [η_i, iR]
  have hηM_eq : ∀ r : Fin k, η_i (iM r) = ηM r := fun r => by simp [η_i, iM, r.2.ne]
  have hxL_i : x_i iL = xL := by simp [x_i, iL]
  have hxR_i : x_i iR = xR := by simp [x_i, iR]
  have hxM_i : ∀ r : Fin k, x_i (iM r) = xM r := fun r => by simp [x_i, iM, r.2.ne]
  have hfin_cases : ∀ (P : Fin N → Prop), P iL → P iR → (∀ r : Fin k, P (iM r)) → ∀ i : Fin N, P i := by
    intro P hL hR hM i
    by_cases h0 : i.1 = 0
    · exact (Fin.ext h0 : i = iL) ▸ hL
    · by_cases hk : i.1 = k + 1
      · exact (Fin.ext hk : i = iR) ▸ hR
      · exact (Fin.ext (by dsimp [iM]; omega) : i = iM ⟨i.1 - 1, by omega⟩) ▸ hM ⟨i.1 - 1, by omega⟩
  have hE_sub_O : ∀ i : Fin N, E i ⊆ O := hfin_cases _ (hEL_eq ▸ hEL_O) (hER_eq ▸ hER_O) (fun r => hEM_eq r ▸ hEM_O r)
  have hη_pos : ∀ i : Fin N, 0 < η_i i := hfin_cases _ (hηL_eq ▸ hηL_pos) (hηR_eq ▸ hηR_pos) (fun r => hηM_eq r ▸ hηM_pos r)
  have hα_out : ∀ i : Fin N, ∀ z ∈ (discInt (E i))ᶜ, α_i i z = z :=
    hfin_cases _ (by rw [hEL_eq, hαL_eq]; exact hαL_out) (by rw [hER_eq, hαR_eq]; exact hαR_out)
      (fun r => by rw [hEM_eq r, hαM_eq r]; exact hαM_out r)
  have hsq_sub : ∀ i : Fin N, Icc (x_i i - η_i i) (x_i i + η_i i) ×ℂ Icc (-η_i i) (η_i i) ⊆ discInt (E i) :=
    hfin_cases _ (by rw [hEL_eq, hxL_i, hηL_eq]; exact hsqL_sub) (by rw [hER_eq, hxR_i, hηR_eq]; exact hsqR_sub)
      (fun r => by rw [hEM_eq r, hxM_i r, hηM_eq r]; exact hsqM_sub r)
  have hE_disj : Pairwise fun i₁ i₂ : Fin N => Disjoint (E i₁) (E i₂) := by
    have hKE_disj : ∀ {A₁ A₂ : Set ℂ}, K '' A₁ ⊆ data.rcL.box ∨ K '' A₁ ⊆ data.rcR.box ∨ (∃ r, K '' A₁ ⊆ (data.rcM r).box) →
        Disjoint (K '' A₁) (K '' A₂) → Disjoint A₁ A₂ := fun _ hD => by
      rw [Set.disjoint_left]; intro z h1 h2; exact Set.disjoint_left.mp hD ⟨z, h1, rfl⟩ ⟨z, h2, rfl⟩
    intro i₁ i₂ hne
    refine Set.disjoint_left.mpr fun z h1 h2 => ?_
    have hk1 : K z ∈ K '' E i₁ := ⟨z, h1, rfl⟩
    have hk2 : K z ∈ K '' E i₂ := ⟨z, h2, rfl⟩
    revert i₁ i₂
    refine hfin_cases _ ?_ ?_ ?_
    · refine hfin_cases _ (fun h => (h rfl).elim) (fun _ _ _ hk1 hk2 => ?_) (fun r _ _ _ hk1 hk2 => ?_)
      · rw [hEL_eq, hKEL] at hk1; rw [hER_eq, hKER] at hk2
        exact Set.disjoint_left.mp data.hL_disj_R (hrcL_sub hk1) (hrcR_sub hk2)
      · rw [hEL_eq, hKEL] at hk1; rw [hEM_eq r, hKEM r] at hk2
        exact Set.disjoint_left.mp (data.hL_disj_M r) (hrcL_sub hk1) (hrcM_sub r hk2)
    · refine hfin_cases _ (fun _ _ _ hk1 hk2 => ?_) (fun h => (h rfl).elim) (fun r _ _ _ hk1 hk2 => ?_)
      · rw [hER_eq, hKER] at hk1; rw [hEL_eq, hKEL] at hk2
        exact Set.disjoint_left.mp data.hL_disj_R (hrcL_sub hk2) (hrcR_sub hk1)
      · rw [hER_eq, hKER] at hk1; rw [hEM_eq r, hKEM r] at hk2
        exact Set.disjoint_left.mp (data.hR_disj_M r) (hrcR_sub hk1) (hrcM_sub r hk2)
    · intro r₁; refine hfin_cases _ (fun _ _ _ hk1 hk2 => ?_) (fun _ _ _ hk1 hk2 => ?_) (fun r₂ hne _ _ hk1 hk2 => ?_)
      · rw [hEM_eq r₁, hKEM r₁] at hk1; rw [hEL_eq, hKEL] at hk2
        exact Set.disjoint_left.mp (data.hL_disj_M r₁) (hrcL_sub hk2) (hrcM_sub r₁ hk1)
      · rw [hEM_eq r₁, hKEM r₁] at hk1; rw [hER_eq, hKER] at hk2
        exact Set.disjoint_left.mp (data.hR_disj_M r₁) (hrcR_sub hk2) (hrcM_sub r₁ hk1)
      · rw [hEM_eq r₁, hKEM r₁] at hk1; rw [hEM_eq r₂, hKEM r₂] at hk2
        have hrne : r₁ ≠ r₂ := fun h => hne (by rw [h])
        exact Set.disjoint_left.mp (data.hM_disj r₁ r₂ hrne) (hrcM_sub r₁ hk1) (hrcM_sub r₂ hk2)
  have hdiscInt_disj : Pairwise fun i₁ i₂ : Fin N => Disjoint (discInt (E i₁)) (discInt (E i₂)) :=
    fun i₁ i₂ hne => (hE_disj hne).mono (fun _ h => h.1) (fun _ h => h.1)
  obtain ⟨Φ, hΦ_out, _, hΦ_in, hα_pres⟩ := compose_disjoint_homeos hdiscInt_disj α_i hα_out
  have hΦ_symm_O : ∀ z ∈ O, Φ.symm z ∈ O := fun z hzO => by
    by_cases hin : ∃ i, z ∈ discInt (E i)
    · obtain ⟨i, hi⟩ := hin
      have hw : Φ.symm z ∈ discInt (E i) := by
        by_contra hnot
        have : Φ (Φ.symm z) ∉ discInt (E i) := by
          by_cases hin2 : ∃ j, Φ.symm z ∈ discInt (E j)
          · obtain ⟨j, hj⟩ := hin2
            have hji : j ≠ i := fun h => hnot (h ▸ hj)
            rw [hΦ_in j _ hj]
            exact Set.disjoint_left.mp (hdiscInt_disj hji) (hα_pres j _ hj)
          · push Not at hin2; rwa [hΦ_out _ hin2]
        exact this (by rwa [Φ.apply_symm_apply])
      exact hE_sub_O i hw.1
    · push Not at hin
      have h1 : Φ z = z := hΦ_out z hin
      have h2 : Φ.symm z = z := Φ.symm_apply_eq.mpr h1.symm
      rwa [h2]
  have hΦ_fix_real : ∀ r : unitInterval, Φ (θ r : ℂ) = (θ r : ℂ) := fun r => by
    by_cases hin : ∃ i, (θ r : ℂ) ∈ discInt (E i)
    · obtain ⟨i, hi⟩ := hin
      rw [hΦ_in i _ hi]
      have hcase : ∀ {A' : Set S} (rc' : RectCross S data.γ_ext A') {E' : Set ℂ} {a' b' : ℝ} {α' : ℂ ≃ₜ ℂ},
          K '' E' = rc'.box →
          a' = θ ⟨rc'.s, rc'.hs0.le, (rc'.hst.trans rc'.hte).le.trans rc'.he1.le⟩ →
          b' = θ ⟨rc'.e, rc'.hs0.le.trans (rc'.hst.trans rc'.hte).le, rc'.he1.le⟩ →
          (∀ z ∈ Icc a' b' ×ℂ ({0} : Set ℝ), α' z = z) →
          (θ r : ℂ) ∈ discInt E' → α' (θ r : ℂ) = (θ r : ℂ) := by
        intro A' rc' E' a' b' α' hKE' ha' hb' hαH' hmem
        have hmemD : data.γ_ext r.1 ∈ rc'.box := by rw [← (hθ_in_O r).2, ← hKE']; exact ⟨(θ r : ℂ), hmem.1, rfl⟩
        have hmγ : data.γ_ext r.1 ∈ data.γ_ext '' Icc rc'.s rc'.e := by
          rw [← rc'.hγD]; exact ⟨⟨r.1, r.2, rfl⟩, hmemD⟩
        obtain ⟨r', hr', hre⟩ := hmγ
        have hrr' : r.1 = r' := data.hγi r.2 ⟨rc'.hs0.le.trans hr'.1, hr'.2.trans rc'.he1.le⟩ hre.symm
        refine hαH' (θ r : ℂ) ?_
        rw [ha', hb', Complex.mem_reProdIm]
        exact ⟨⟨hθm.monotone (show rc'.s ≤ r.1 from hrr' ▸ hr'.1), hθm.monotone (show r.1 ≤ rc'.e from hrr' ▸ hr'.2)⟩, rfl⟩
      revert i
      refine hfin_cases _ (fun hi => ?_) (fun hi => ?_) (fun q hi => ?_)
      · rw [hαL_eq]; exact hcase rcL hKEL haL_eq hbL_eq hαL_H (hEL_eq ▸ hi)
      · rw [hαR_eq]; exact hcase rcR hKER haR_eq hbR_eq hαR_H (hER_eq ▸ hi)
      · rw [hαM_eq q]; exact hcase (rcM q) (hKEM q) (haM_eq q) (hbM_eq q) (hαM_H q) (hEM_eq q ▸ hi)
    · push Not at hin; exact hΦ_out _ hin
  have hΦ_symm_fix_real : ∀ r : unitInterval, Φ.symm (θ r : ℂ) = (θ r : ℂ) := fun r =>
    Φ.symm_apply_eq.mpr (hΦ_fix_real r).symm
  let f : ℂ → S := fun z => K (Φ.symm z)
  have hfc_O : ContinuousOn f O := hKc.comp Φ.symm.continuous.continuousOn hΦ_symm_O
  have hfi_O : InjOn f O := fun z₁ hz₁ z₂ hz₂ he => Φ.symm.injective (hKi (hΦ_symm_O z₁ hz₁) (hΦ_symm_O z₂ hz₂) he)
  -- Order of `xL < xM r < xR`:
  have hL_lt_R_t : tL_u < tR_u := show data.rcL.t_mid < data.rcR.t_mid by linarith [data.rcL.hte, data.hL_lt_R, data.rcR.hst]
  have hxL_val : xL = θ tL_u := hxL_eq
  have hxR_val : xR = θ tR_u := hxR_eq
  have hxM_val : ∀ r : Fin k, xM r = θ (tM_u r) := hxM_eq
  have hL_lt_R_x : xL < xR := by rw [hxL_val, hxR_val]; exact hθm hL_lt_R_t
  have hM_between_x : ∀ r : Fin k, xL < xM r ∧ xM r < xR := fun r => by
    rw [hxL_val, hxM_val r, hxR_val]
    exact ⟨hθm (show data.rcL.t_mid < (data.rcM r).t_mid by linarith [data.rcL.hte, (data.hM_order r).1, (data.rcM r).hst]),
      hθm (show (data.rcM r).t_mid < data.rcR.t_mid by linarith [(data.rcM r).hte, (data.hM_order r).2, data.rcR.hst])⟩
  -- Local behavior of `f` inside each square `Ssq i`:
  let Ssq : Fin N → Set ℂ := fun i => Icc (x_i i - η_i i) (x_i i + η_i i) ×ℂ Icc (-η_i i) (η_i i)
  let Osq : Fin N → Set ℂ := fun i => Ioo (x_i i - η_i i) (x_i i + η_i i) ×ℂ Ioo (-η_i i) (η_i i)
  have hΦ_symm_in : ∀ (i : Fin N) (z : ℂ), z ∈ discInt (E i) → Φ.symm z = (α_i i).symm z ∧ (α_i i).symm z ∈ discInt (E i) := fun i z hz => by
    have h1 : (α_i i).symm z ∈ discInt (E i) := by
      by_contra hnot
      have h2 : α_i i ((α_i i).symm z) = (α_i i).symm z := hα_out i _ hnot
      rw [(α_i i).apply_symm_apply] at h2; exact hnot (h2 ▸ hz)
    have h2 : Φ ((α_i i).symm z) = z := by rw [hΦ_in i _ h1, (α_i i).apply_symm_apply]
    exact ⟨Φ.symm_apply_eq.mpr h2.symm, h1⟩
  have hf_Ssq_in : ∀ (i : Fin N) (z : ℂ), z ∈ Ssq i → f z ∈ K '' E i := fun i z hz => by
    obtain ⟨h1, h2⟩ := hΦ_symm_in i z (hsq_sub i hz)
    exact ⟨Φ.symm z, h1 ▸ h2.1, rfl⟩
  have hf_Ssq_target_gen : ∀ {i : Fin N} {A' : Set S},
      (α_i i '' (E i ∩ K ⁻¹' A')) ∩ Ssq i = ({x_i i} : Set ℝ) ×ℂ Icc (-η_i i) (η_i i) →
      ∀ z ∈ Ssq i, f z ∈ A' ↔ z.re = x_i i := fun {i A'} hsqA z hz => by
    obtain ⟨hαs, hsym_int⟩ := hΦ_symm_in i z (hsq_sub i hz)
    constructor
    · intro hfA
      have hm : z ∈ (α_i i '' (E i ∩ K ⁻¹' A')) ∩ Ssq i :=
        ⟨⟨(α_i i).symm z, ⟨hsym_int.1, by rwa [mem_preimage, ← hαs]⟩, (α_i i).apply_symm_apply z⟩, hz⟩
      rw [hsqA] at hm; exact mem_singleton_iff.mp (Complex.mem_reProdIm.mp hm).1
    · intro hre
      have hm : z ∈ ({x_i i} : Set ℝ) ×ℂ Icc (-η_i i) (η_i i) :=
        Complex.mem_reProdIm.mpr ⟨hre, (Complex.mem_reProdIm.mp hz).2⟩
      rw [← hsqA] at hm
      obtain ⟨w, ⟨_, hwA⟩, hwe⟩ := hm.1
      have : w = (α_i i).symm z := by rw [← hwe, (α_i i).symm_apply_apply]
      dsimp only [f]; rw [hαs, ← this]; exact hwA
  have hf_Ssq_L : ∀ z ∈ Ssq iL, f z ∈ M.U ↔ z.re = xL := fun z hz => by
    have h := hf_Ssq_target_gen (i := iL) (A' := M.U) (by simp only [Ssq, hEL_eq, hαL_eq, hxL_i, hηL_eq]; exact hαL_sq) z hz
    simpa [hxL_i] using h
  have hf_Ssq_R : ∀ z ∈ Ssq iR, f z ∈ M.U ↔ z.re = xR := fun z hz => by
    have h := hf_Ssq_target_gen (i := iR) (A' := M.U) (by simp only [Ssq, hER_eq, hαR_eq, hxR_i, hηR_eq]; exact hαR_sq) z hz
    simpa [hxR_i] using h
  have hf_Ssq_M : ∀ (r : Fin k) (z : ℂ), z ∈ Ssq (iM r) → (f z ∈ Q (data.idxs r) ↔ z.re = xM r) := fun r z hz => by
    have h := hf_Ssq_target_gen (i := iM r) (A' := Q (data.idxs r))
      (by simp only [Ssq, hEM_eq r, hαM_eq r, hxM_i r, hηM_eq r]; exact hαM_sq r) z hz
    simpa [hxM_i r] using h
  -- Step 4: Find `η > 0` separating `Icc xL xR ×ℂ Icc (-η) η \ ⋃ Osq` from `X_all := M.U ∪ ⋃ Q`:
  let X_all : Set S := M.U ∪ ⋃ j : Fin m, Q j
  have hX_closed : IsClosed X_all := M.isClosed_U.union (isClosed_iUnion_of_finite hQclosed)
  have hθ_inv_seg : ∀ x ∈ Icc xL xR, ∃ r : unitInterval, r.1 ∈ Icc data.rcL.t_mid data.rcR.t_mid ∧ θ r = x := fun x hx => by
    let fn : ℝ → ℝ := fun r => if hr : r ∈ Icc (0 : ℝ) 1 then θ ⟨r, hr⟩ else 0
    have hfn_c : ContinuousOn fn (Icc tL_u.1 tR_u.1) :=
      (by rw [continuousOn_iff_continuous_domRestrict]
          exact hθc.congr fun r => by simp only [Set.domRestrict, fn, dite_eq_left r.2] : ContinuousOn fn (Icc 0 1)).mono
        (Icc_subset_Icc tL_u.2.1 tR_u.2.2)
    have hfnL : fn tL_u.1 = xL := by simp only [fn, dite_eq_left tL_u.2]; exact hxL_val.symm
    have hfnR : fn tR_u.1 = xR := by simp only [fn, dite_eq_left tR_u.2]; exact hxR_val.symm
    obtain ⟨r, hr, hreq⟩ := intermediate_value_Icc (show tL_u.1 ≤ tR_u.1 from hL_lt_R_t.le) hfn_c
      (show x ∈ Icc (fn tL_u.1) (fn tR_u.1) from by rw [hfnL, hfnR]; exact hx)
    have hr01 : r ∈ Icc (0 : ℝ) 1 := ⟨tL_u.2.1.trans hr.1, hr.2.trans tR_u.2.2⟩
    simp only [fn, dite_eq_left hr01] at hreq
    exact ⟨⟨r, hr01⟩, hr, hreq⟩
  have hseg_in_O : Icc xL xR ×ℂ ({0} : Set ℝ) ⊆ O := fun z hz => by
    rw [Complex.mem_reProdIm] at hz
    obtain ⟨r, -, hreq⟩ := hθ_inv_seg z.re hz.1
    have hz_eq : z = (θ r : ℂ) := Complex.ext hreq.symm (by simp [mem_singleton_iff.mp hz.2])
    rw [hz_eq]; exact (hθ_in_O r).1
  have hηO_ex : ∃ η_O > 0, Icc xL xR ×ℂ Icc (-η_O) η_O ⊆ O := by
    obtain ⟨ε, hε, hεsub⟩ := (isCompact_Icc.reProdIm isCompact_singleton).exists_thickening_subset_open hOo hseg_in_O
    refine ⟨ε / 2, half_pos hε, fun z hz => hεsub ?_⟩
    rw [Complex.mem_reProdIm] at hz; rw [Metric.mem_thickening_iff]
    refine ⟨(z.re : ℂ), Complex.mem_reProdIm.mpr ⟨hz.1, rfl⟩, ?_⟩
    rw [dist_eq_norm]
    have hsub : z - (z.re : ℂ) = (z.im : ℂ) * I := Complex.ext (by simp) (by simp)
    rw [hsub, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    linarith [abs_le.mpr hz.2]
  obtain ⟨η_O, hηO, hRO_sub⟩ := hηO_ex
  let J : Set ℂ := (Icc xL xR ×ℂ ({0} : Set ℝ)) \ ⋃ i : Fin N, Osq i
  have hJ_comp : IsCompact J :=
    (isCompact_Icc.reProdIm isCompact_singleton).diff (isOpen_iUnion fun i => isOpen_Ioo.reProdIm isOpen_Ioo)
  have hJ_disj_X : ∀ z ∈ J, f z ∉ X_all := fun z hz hfX => by
    have hzseg := Complex.mem_reProdIm.mp hz.1
    have hzim : z.im = 0 := mem_singleton_iff.mp hzseg.2
    obtain ⟨r, hr, hreq⟩ := hθ_inv_seg z.re hzseg.1
    have hz_eq : z = (θ r : ℂ) := Complex.ext hreq.symm (by simp [hzim])
    have hfz : f z = data.γ_ext r.1 := by dsimp only [f]; rw [hz_eq, hΦ_symm_fix_real, (hθ_in_O r).2]
    have hnot_x : ∀ i : Fin N, z.re ≠ x_i i := fun i hxi => hz.2 (mem_iUnion.mpr ⟨i,
      Complex.mem_reProdIm.mpr ⟨⟨by linarith [hη_pos i], by linarith [hη_pos i]⟩,
        ⟨by linarith [hη_pos i, hzim], by linarith [hη_pos i, hzim]⟩⟩⟩)
    rw [hfz] at hfX
    rcases hfX with hM | hQ
    · rcases data.hγ_clean_M r.1 hr hM with hL | hR
      · apply hnot_x iL; rw [hxL_i, hxL_val, ← hreq]; exact congrArg θ (Subtype.ext hL)
      · apply hnot_x iR; rw [hxR_i, hxR_val, ← hreq]; exact congrArg θ (Subtype.ext hR)
    · obtain ⟨j0, hj0⟩ := mem_iUnion.mp hQ
      obtain ⟨q, -, hq⟩ := data.hγ_clean_Q r.1 hr j0 hj0
      apply hnot_x (iM q); rw [hxM_i q, hxM_val q, ← hreq]; exact congrArg θ (Subtype.ext hq)
  have hO_offX_open : IsOpen (O ∩ f ⁻¹' X_allᶜ) := by
    rw [isOpen_iff_mem_nhds]; intro z ⟨hzO, hzX⟩
    have h1 := hfc_O.continuousWithinAt hzO (hX_closed.isOpen_compl.mem_nhds hzX)
    rw [nhdsWithin_eq_nhds.mpr (hOo.mem_nhds hzO)] at h1
    exact Filter.inter_mem (hOo.mem_nhds hzO) h1
  obtain ⟨η_J, hηJ, hηJ_sub⟩ := hJ_comp.exists_thickening_subset_open hO_offX_open
    (fun z hz => ⟨(sdiff_subset.trans hseg_in_O) hz, hJ_disj_X z hz⟩)
  let η_min : ℝ := (Finset.univ.image η_i).min' (Finset.univ_nonempty.image η_i)
  have hη_min_pos : 0 < η_min := by
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp (Finset.min'_mem _ (Finset.univ_nonempty.image η_i))
    have heq : η_min = η_i i := hi.symm
    rw [heq]; exact hη_pos i
  have hη_min_le : ∀ i : Fin N, η_min ≤ η_i i := fun i =>
    Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  let η : ℝ := min (η_O / 2) (min (η_J / 2) (η_min / 2))
  have hη_pos : 0 < η := lt_min (half_pos hηO) (lt_min (half_pos hηJ) (half_pos hη_min_pos))
  have hη_le_O : η ≤ η_O := (min_le_left _ _).trans (by linarith)
  have hη_lt_J : η < η_J := (min_le_right _ _).trans_lt ((min_le_left _ _).trans_lt (half_lt_self hηJ))
  have hη_le_half : ∀ i : Fin N, η ≤ η_i i / 2 := fun i =>
    (min_le_right _ _).trans ((min_le_right _ _).trans (div_le_div_of_nonneg_right (hη_min_le i) (by norm_num)))
  -- Step 5: Compute exact intersections of `Δ := f '' (Icc xL xR ×ℂ Icc (-η) η)` with `M.U` and every `Q j`:
  let Rη : Set ℂ := Icc xL xR ×ℂ Icc (-η) η
  have hRη_sub_O : Rη ⊆ O := fun z hz => hRO_sub (by
    rw [Complex.mem_reProdIm] at hz ⊢
    exact ⟨hz.1, ⟨by linarith [hz.2.1, hη_le_O], by linarith [hz.2.2, hη_le_O]⟩⟩)
  let Δ : Set S := f '' Rη
  have hΔint : Δ ⊆ (bd S)ᶜ := by rintro _ ⟨z, hz, rfl⟩; exact hK_int _ (hΦ_symm_O z (hRη_sub_O hz))
  have hRη_X_in_Ssq : ∀ z ∈ Rη, f z ∈ X_all → ∃ i : Fin N, z ∈ Ssq i := fun z hz hfX => by
    by_contra hnot; push Not at hnot
    have hz_not_Osq : (z.re : ℂ) ∉ ⋃ i : Fin N, Osq i := fun hm => by
      obtain ⟨i, hi⟩ := mem_iUnion.mp hm; rw [Complex.mem_reProdIm] at hi
      have h1 := Complex.mem_reProdIm.mp hz
      exact hnot i (Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (by simpa using hi.1),
        ⟨by linarith [h1.2.1, hη_le_half i, hη_pos], by linarith [h1.2.2, hη_le_half i, hη_pos]⟩⟩)
    have hzre_J : (z.re : ℂ) ∈ J := ⟨Complex.mem_reProdIm.mpr ⟨(Complex.mem_reProdIm.mp hz).1, rfl⟩, hz_not_Osq⟩
    have hz_thick : z ∈ Metric.thickening η_J J := by
      rw [Metric.mem_thickening_iff]; refine ⟨(z.re : ℂ), hzre_J, ?_⟩
      rw [dist_eq_norm]
      have hsub : z - (z.re : ℂ) = (z.im : ℂ) * I := Complex.ext (by simp) (by simp)
      rw [hsub, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact (abs_le.mpr (Complex.mem_reProdIm.mp hz).2).trans_lt hη_lt_J
    exact (hηJ_sub hz_thick).2 hfX
  have hMΔ : M.U ∩ Δ = f '' (({xL} : Set ℝ) ×ℂ Icc (-η) η) ∪ f '' (({xR} : Set ℝ) ×ℂ Icc (-η) η) := by
    ext y; constructor
    · rintro ⟨hyM, z, hzR, rfl⟩
      obtain ⟨i, hzi⟩ := hRη_X_in_Ssq z hzR (Or.inl hyM)
      revert i
      refine hfin_cases _ (fun hzi => ?_) (fun hzi => ?_) (fun r hzi => ?_)
      · exact Or.inl ⟨z, Complex.mem_reProdIm.mpr ⟨(hf_Ssq_L z hzi).mp hyM, (Complex.mem_reProdIm.mp hzR).2⟩, rfl⟩
      · exact Or.inr ⟨z, Complex.mem_reProdIm.mpr ⟨(hf_Ssq_R z hzi).mp hyM, (Complex.mem_reProdIm.mp hzR).2⟩, rfl⟩
      · exfalso
        have hbox : f z ∈ (data.rcM r).box := hrcM_sub r (hKEM r ▸ hEM_eq r ▸ hf_Ssq_in (iM r) z hzi)
        exact Set.disjoint_left.mp (data.hM_disj_M r) hbox hyM
    · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
      · rw [Complex.mem_reProdIm] at hz
        have hzR : z ∈ Rη := Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hz.1]; exact ⟨le_rfl, hL_lt_R_x.le⟩, hz.2⟩
        have hzS : z ∈ Ssq iL := Complex.mem_reProdIm.mpr
          ⟨by rw [hxL_i, hηL_eq, mem_singleton_iff.mp hz.1]; exact ⟨by linarith [hηL_pos], by linarith [hηL_pos]⟩,
           by rw [hηL_eq]; exact ⟨by linarith [hz.2.1, hη_le_half iL, hηL_eq, hη_pos], by linarith [hz.2.2, hη_le_half iL, hηL_eq, hη_pos]⟩⟩
        exact ⟨(hf_Ssq_L z hzS).mpr (mem_singleton_iff.mp hz.1), z, hzR, rfl⟩
      · rw [Complex.mem_reProdIm] at hz
        have hzR : z ∈ Rη := Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hz.1]; exact ⟨hL_lt_R_x.le, le_rfl⟩, hz.2⟩
        have hzS : z ∈ Ssq iR := Complex.mem_reProdIm.mpr
          ⟨by rw [hxR_i, hηR_eq, mem_singleton_iff.mp hz.1]; exact ⟨by linarith [hηR_pos], by linarith [hηR_pos]⟩,
           by rw [hηR_eq]; exact ⟨by linarith [hz.2.1, hη_le_half iR, hηR_eq, hη_pos], by linarith [hz.2.2, hη_le_half iR, hηR_eq, hη_pos]⟩⟩
        exact ⟨(hf_Ssq_R z hzS).mpr (mem_singleton_iff.mp hz.1), z, hzR, rfl⟩
  -- Step 6: Apply `rectangle_surgery`!
  have hfL_eq : f (xL : ℂ) = data.γ_ext data.rcL.t_mid := by
    dsimp only [f]; rw [hxL_val, hΦ_symm_fix_real tL_u, (hθ_in_O tL_u).2]
  have hfR_eq : f (xR : ℂ) = data.γ_ext data.rcR.t_mid := by
    dsimp only [f]; rw [hxR_val, hΦ_symm_fix_real tR_u, (hθ_in_O tR_u).2]
  obtain ⟨M', hagree, hM'Δ, hw1, hcoh, hlen_of⟩ :=
    rectangle_surgery hS AS hst M hL_lt_R_x hη_pos (hfc_O.mono hRη_sub_O) (hfi_O.mono hRη_sub_O) hΔint hMΔ
  have hlen : M'.Os.length + 1 = M.Os.length := hlen_of (by rw [hfL_eq, hfR_eq]; exact data.hdiff_comp)
  -- Step 7: Check `Q j ∩ Δ`:
  have hQ_disj_Δ : ∀ j : Fin m, j ∉ range data.idxs → Disjoint Δ (Q j) := fun j hj => by
    rw [Set.disjoint_left]; rintro _ ⟨z, hzR, rfl⟩ hQj
    obtain ⟨i, hzi⟩ := hRη_X_in_Ssq z hzR (Or.inr (mem_iUnion.mpr ⟨j, hQj⟩))
    revert i
    refine hfin_cases _ (fun hzi => ?_) (fun hzi => ?_) (fun r hzi => ?_)
    · exact Set.disjoint_left.mp (data.hL_disj_Q j) (hrcL_sub (hKEL ▸ hEL_eq ▸ hf_Ssq_in iL z hzi)) hQj
    · exact Set.disjoint_left.mp (data.hR_disj_Q j) (hrcR_sub (hKER ▸ hER_eq ▸ hf_Ssq_in iR z hzi)) hQj
    · exact Set.disjoint_left.mp (data.hM_disj_Q r j fun heq => hj ⟨r, heq.symm⟩)
        (hrcM_sub r (hKEM r ▸ hEM_eq r ▸ hf_Ssq_in (iM r) z hzi)) hQj
  have hQ_inter_Δ : ∀ r : Fin k, Q (data.idxs r) ∩ Δ = f '' (({xM r} : Set ℝ) ×ℂ Icc (-η) η) := fun r => by
    ext y; constructor
    · rintro ⟨hyQ, z, hzR, rfl⟩
      obtain ⟨i, hzi⟩ := hRη_X_in_Ssq z hzR (Or.inr (mem_iUnion.mpr ⟨data.idxs r, hyQ⟩))
      revert i
      refine hfin_cases _ (fun hzi => ?_) (fun hzi => ?_) (fun q hzi => ?_)
      · exact (Set.disjoint_left.mp (data.hL_disj_Q (data.idxs r)) (hrcL_sub (hKEL ▸ hEL_eq ▸ hf_Ssq_in iL z hzi)) hyQ).elim
      · exact (Set.disjoint_left.mp (data.hR_disj_Q (data.idxs r)) (hrcR_sub (hKER ▸ hER_eq ▸ hf_Ssq_in iR z hzi)) hyQ).elim
      · have hqr_eq : data.idxs q = data.idxs r := by
          by_contra hne
          exact Set.disjoint_left.mp (data.hM_disj_Q q (data.idxs r) (Ne.symm hne))
            (hrcM_sub q (hKEM q ▸ hEM_eq q ▸ hf_Ssq_in (iM q) z hzi)) hyQ
        have hqr : q = r := data.hidxs_inj hqr_eq
        subst hqr
        exact ⟨z, Complex.mem_reProdIm.mpr ⟨(hf_Ssq_M q z hzi).mp hyQ, (Complex.mem_reProdIm.mp hzR).2⟩, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      rw [Complex.mem_reProdIm] at hz
      have hbet := hM_between_x r
      have hzR : z ∈ Rη := Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hz.1]; exact ⟨hbet.1.le, hbet.2.le⟩, hz.2⟩
      have hzS : z ∈ Ssq (iM r) := Complex.mem_reProdIm.mpr
        ⟨by rw [hxM_i r, hηM_eq r, mem_singleton_iff.mp hz.1]; exact ⟨by linarith [hηM_pos r], by linarith [hηM_pos r]⟩,
         by rw [hηM_eq r]; exact ⟨by linarith [hz.2.1, hη_le_half (iM r), hηM_eq r, hη_pos], by linarith [hz.2.2, hη_le_half (iM r), hηM_eq r, hη_pos]⟩⟩
      exact ⟨(hf_Ssq_M r z hzS).mpr (mem_singleton_iff.mp hz.1), z, hzR, rfl⟩
  -- Step 8: Assemble all conclusions!
  refine ⟨M', hlen, hw1, hcoh, fun j hj => ?_, fun r => ?_⟩
  · have hdisj := hQ_disj_Δ j hj
    have hinter_eq : M'.U ∩ Q j = M.U ∩ Q j := by
      ext y; constructor
      · rintro ⟨hyM', hyQ⟩; exact ⟨(show y ∈ M.U \ Δ from hagree ▸ ⟨hyM', fun h => Set.disjoint_left.mp hdisj h hyQ⟩).1, hyQ⟩
      · rintro ⟨hyM, hyQ⟩; exact ⟨(show y ∈ M'.U \ Δ from hagree.symm ▸ ⟨hyM, fun h => Set.disjoint_left.mp hdisj h hyQ⟩).1, hyQ⟩
    refine ⟨hinter_eq, fun hsc p hp => ?_⟩
    rw [hinter_eq] at hp
    obtain ⟨g, ε, hε, hgc, hgi, _, hgint, hg0, hMbox, hQbox⟩ := hsc p hp
    have hΔ_closed : IsClosed Δ := ((isCompact_Icc.reProdIm isCompact_Icc).image_of_continuousOn (hfc_O.mono hRη_sub_O)).isClosed
    have hp_notΔ : p ∉ Δ := fun h => Set.disjoint_left.mp hdisj h hp.2
    have h0sq : (0 : ℂ) ∈ Icc (-ε) ε ×ℂ Icc (-ε) ε := Complex.mem_reProdIm.mpr ⟨by simp [hε.le], by simp [hε.le]⟩
    have hpre : g ⁻¹' Δᶜ ∈ 𝓝[Icc (-ε) ε ×ℂ Icc (-ε) ε] (0 : ℂ) :=
      hgc.continuousWithinAt h0sq (hΔ_closed.isOpen_compl.mem_nhds (hg0.symm ▸ hp_notΔ))
    rw [Metric.mem_nhdsWithin_iff] at hpre
    obtain ⟨r₁, hr₁, hr₁sub⟩ := hpre
    let ε' : ℝ := min ε (r₁ / 4)
    have hε' : 0 < ε' := lt_min hε (div_pos hr₁ (by norm_num))
    have hε'le : ε' ≤ ε := min_le_left _ _
    have hsub_sq : Icc (-ε') ε' ×ℂ Icc (-ε') ε' ⊆ Icc (-ε) ε ×ℂ Icc (-ε) ε := fun w hw => by
      rw [Complex.mem_reProdIm] at hw ⊢
      exact ⟨⟨by linarith [hw.1.1], by linarith [hw.1.2]⟩, ⟨by linarith [hw.2.1], by linarith [hw.2.2]⟩⟩
    have hdisj_box : Disjoint (g '' (Icc (-ε') ε' ×ℂ Icc (-ε') ε')) Δ := by
      rw [Set.disjoint_left]; rintro _ ⟨w, hw, rfl⟩
      have hball : w ∈ ball (0 : ℂ) r₁ := by
        rw [mem_ball_zero_iff]; rw [Complex.mem_reProdIm] at hw
        have hnorm : ‖w‖ ≤ |w.re| + |w.im| := by
          calc ‖w‖ = ‖(w.re : ℂ) + (w.im : ℂ) * I‖ := by congr 1; apply Complex.ext <;> simp
            _ ≤ ‖(w.re : ℂ)‖ + ‖(w.im : ℂ) * I‖ := norm_add_le _ _
            _ = |w.re| + |w.im| := by rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
        have hle4 : ε' ≤ r₁ / 4 := min_le_right _ _
        linarith [abs_le.mpr hw.1, abs_le.mpr hw.2]
      exact hr₁sub ⟨hball, hsub_sq hw⟩
    refine ⟨g, ε', hε', hgc.mono hsub_sq, hgi.mono hsub_sq,
      isOpen_image_of_manifold (isOpen_Ioo.reProdIm isOpen_Ioo)
        (hgc.mono fun w hw => hsub_sq (Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hw).1,
          Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hw).2⟩))
        (hgi.mono fun w hw => hsub_sq (Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hw).1,
          Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hw).2⟩))
        (fun _ _ => hS.2.2 _),
      (image_mono hsub_sq).trans hgint, hg0, ?_, ?_⟩
    · ext y; constructor
      · rintro ⟨hyM', w, hw, rfl⟩
        have hyM : g w ∈ M.U := (show g w ∈ M.U \ Δ from hagree ▸ ⟨hyM', Set.disjoint_left.mp hdisj_box ⟨w, hw, rfl⟩⟩).1
        have h1 : g w ∈ M.U ∩ g '' (Icc (-ε) ε ×ℂ Icc (-ε) ε) := ⟨hyM, w, hsub_sq hw, rfl⟩
        rw [hMbox] at h1
        obtain ⟨w', hw', hfe⟩ := h1
        rw [Complex.mem_reProdIm] at hw'
        have hw'sq : w' ∈ Icc (-ε) ε ×ℂ Icc (-ε) ε := Complex.mem_reProdIm.mpr ⟨hw'.1, by rw [mem_singleton_iff.mp hw'.2]; exact ⟨by linarith, hε.le⟩⟩
        have hww' := hgi (hsub_sq hw) hw'sq hfe.symm
        exact ⟨w, Complex.mem_reProdIm.mpr ⟨(Complex.mem_reProdIm.mp hw).1, by rw [hww']; exact hw'.2⟩, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        rw [Complex.mem_reProdIm] at hw
        have hwsq : w ∈ Icc (-ε') ε' ×ℂ Icc (-ε') ε' := Complex.mem_reProdIm.mpr ⟨hw.1, by rw [mem_singleton_iff.mp hw.2]; exact ⟨by linarith, hε'.le⟩⟩
        have hyM : g w ∈ M.U := (show g w ∈ M.U ∩ g '' (Icc (-ε) ε ×ℂ Icc (-ε) ε) by
          rw [hMbox]; exact ⟨w, Complex.mem_reProdIm.mpr ⟨(Complex.mem_reProdIm.mp (hsub_sq hwsq)).1, hw.2⟩, rfl⟩).1
        exact ⟨(show g w ∈ M'.U \ Δ from hagree.symm ▸ ⟨hyM, Set.disjoint_left.mp hdisj_box ⟨w, hwsq, rfl⟩⟩).1, w, hwsq, rfl⟩
    · ext y; constructor
      · rintro ⟨hyQ, w, hw, rfl⟩
        have h1 : g w ∈ Q j ∩ g '' (Icc (-ε) ε ×ℂ Icc (-ε) ε) := ⟨hyQ, w, hsub_sq hw, rfl⟩
        rw [hQbox] at h1
        obtain ⟨w', hw', hfe⟩ := h1
        rw [Complex.mem_reProdIm] at hw'
        have hw'sq : w' ∈ Icc (-ε) ε ×ℂ Icc (-ε) ε := Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hw'.1]; exact ⟨by linarith, hε.le⟩, hw'.2⟩
        have hww' := hgi (hsub_sq hw) hw'sq hfe.symm
        exact ⟨w, Complex.mem_reProdIm.mpr ⟨by rw [hww']; exact hw'.1, (Complex.mem_reProdIm.mp hw).2⟩, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        rw [Complex.mem_reProdIm] at hw
        have hwsq : w ∈ Icc (-ε') ε' ×ℂ Icc (-ε') ε' := Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hw.1]; exact ⟨by linarith, hε'.le⟩, hw.2⟩
        have hyQ : g w ∈ Q j := (show g w ∈ Q j ∩ g '' (Icc (-ε) ε ×ℂ Icc (-ε) ε) by
          rw [hQbox]; exact ⟨w, Complex.mem_reProdIm.mpr ⟨hw.1, (Complex.mem_reProdIm.mp (hsub_sq hwsq)).2⟩, rfl⟩).1
        exact ⟨hyQ, w, hwsq, rfl⟩
  · let p_top : S := f ((xM r : ℂ) + (η : ℂ) * I)
    let p_bot : S := f ((xM r : ℂ) + (-(η : ℝ) : ℂ) * I)
    have hbet := hM_between_x r
    have hpair : M'.U ∩ Q (data.idxs r) = {p_top, p_bot} := by
      ext y; constructor
      · rintro ⟨hyM', hyQ⟩
        have hyΔ : y ∈ Δ := by
          by_contra hnot
          exact Set.disjoint_left.mp (data.hidxs_disj r) (show y ∈ M.U \ Δ from hagree ▸ ⟨hyM', hnot⟩).1 hyQ
        have h1 : y ∈ M'.U ∩ Δ := ⟨hyM', hyΔ⟩; rw [hM'Δ] at h1
        have h2 : y ∈ Q (data.idxs r) ∩ Δ := ⟨hyQ, hyΔ⟩; rw [hQ_inter_Δ r] at h2
        obtain ⟨z, hz, rfl⟩ := h2; rw [Complex.mem_reProdIm] at hz
        have hzR : z ∈ Rη := Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hz.1]; exact ⟨hbet.1.le, hbet.2.le⟩, hz.2⟩
        rcases h1 with ⟨w, hw, hfe⟩ | ⟨w, hw, hfe⟩
        · rw [Complex.mem_reProdIm] at hw
          have hwR : w ∈ Rη := Complex.mem_reProdIm.mpr ⟨hw.1, by rw [mem_singleton_iff.mp hw.2]; exact ⟨by linarith, le_rfl⟩⟩
          have hzw := hfi_O (hRη_sub_O hzR) (hRη_sub_O hwR) hfe.symm
          exact Or.inl (congrArg f (Complex.ext (by simp [mem_singleton_iff.mp hz.1]) (by simp [hzw, mem_singleton_iff.mp hw.2])))
        · rw [Complex.mem_reProdIm] at hw
          have hwR : w ∈ Rη := Complex.mem_reProdIm.mpr ⟨hw.1, by rw [mem_singleton_iff.mp hw.2]; exact ⟨le_rfl, by linarith⟩⟩
          have hzw := hfi_O (hRη_sub_O hzR) (hRη_sub_O hwR) hfe.symm
          exact Or.inr (congrArg f (Complex.ext (by simp [mem_singleton_iff.mp hz.1]) (by simp [hzw, mem_singleton_iff.mp hw.2])))
      · rintro (rfl | rfl)
        · have hzT : (xM r : ℂ) + (η : ℂ) * I ∈ Icc xL xR ×ℂ ({η} : Set ℝ) :=
            Complex.mem_reProdIm.mpr ⟨by simp [hbet.1.le, hbet.2.le], by simp⟩
          have hzV : (xM r : ℂ) + (η : ℂ) * I ∈ ({xM r} : Set ℝ) ×ℂ Icc (-η) η :=
            Complex.mem_reProdIm.mpr ⟨by simp, by simp; linarith⟩
          exact ⟨(hM'Δ.symm ▸ Or.inl ⟨_, hzT, rfl⟩ : p_top ∈ M'.U ∩ Δ).1,
            ((hQ_inter_Δ r).symm ▸ ⟨_, hzV, rfl⟩ : p_top ∈ Q (data.idxs r) ∩ Δ).1⟩
        · have hzB : (xM r : ℂ) + (-(η : ℝ) : ℂ) * I ∈ Icc xL xR ×ℂ ({-η} : Set ℝ) :=
            Complex.mem_reProdIm.mpr ⟨by simp [hbet.1.le, hbet.2.le], by simp⟩
          have hzV : (xM r : ℂ) + (-(η : ℝ) : ℂ) * I ∈ ({xM r} : Set ℝ) ×ℂ Icc (-η) η :=
            Complex.mem_reProdIm.mpr ⟨by simp, by simp; linarith⟩
          exact ⟨(hM'Δ.symm ▸ Or.inr ⟨_, hzB, rfl⟩ : p_bot ∈ M'.U ∩ Δ).1,
            ((hQ_inter_Δ r).symm ▸ ⟨_, hzV, rfl⟩ : p_bot ∈ Q (data.idxs r) ∩ Δ).1⟩
    refine ⟨hpair ▸ ⟨p_top, Or.inl rfl⟩, hpair ▸ (finite_singleton p_bot).insert p_top, ?_, ?_⟩
    · rw [hpair]; exact (Set.ncard_insert_le p_top {p_bot}).trans (by simp)
    · intro p hp; rw [hpair] at hp
      have hbuild_cross : ∀ (σ : ℝ), (σ = 1 ∨ σ = -1) → p = f ((xM r : ℂ) + ((σ * η : ℝ) : ℂ) * I) →
          ∃ (g : ℂ → S) (ε : ℝ), 0 < ε ∧
            ContinuousOn g (Icc (-ε) ε ×ℂ Icc (-ε) ε) ∧ InjOn g (Icc (-ε) ε ×ℂ Icc (-ε) ε) ∧
            IsOpen (g '' (Ioo (-ε) ε ×ℂ Ioo (-ε) ε)) ∧ g '' (Icc (-ε) ε ×ℂ Icc (-ε) ε) ⊆ (bd S)ᶜ ∧
            g 0 = p ∧
            M'.U ∩ g '' (Icc (-ε) ε ×ℂ Icc (-ε) ε) = g '' (Icc (-ε) ε ×ℂ ({0} : Set ℝ)) ∧
            Q (data.idxs r) ∩ g '' (Icc (-ε) ε ×ℂ Icc (-ε) ε) = g '' (({0} : Set ℝ) ×ℂ Icc (-ε) ε) := by
        intro σ hσ hp_eq
        let z0 : ℂ := (xM r : ℂ) + ((σ * η : ℝ) : ℂ) * I
        let ε : ℝ := min (η / 2) (min ((xM r - xL) / 2) ((xR - xM r) / 2))
        have hε : 0 < ε := lt_min (half_pos hη_pos) (lt_min (half_pos (by linarith [hbet.1])) (half_pos (by linarith [hbet.2])))
        have hε_η : ε ≤ η / 2 := min_le_left _ _
        have hε_L : ε ≤ (xM r - xL) / 2 := (min_le_right _ _).trans (min_le_left _ _)
        have hε_R : ε ≤ (xR - xM r) / 2 := (min_le_right _ _).trans (min_le_right _ _)
        let tr : ℂ → ℂ := fun w => z0 + w
        let g : ℂ → S := fun w => f (tr w)
        have htr_Ssq : MapsTo tr (Icc (-ε) ε ×ℂ Icc (-ε) ε) (Ssq (iM r)) := fun w hw => by
          rw [Complex.mem_reProdIm] at hw ⊢
          have hσ_abs : |σ| = 1 := hσ.elim (fun h => by rw [h]; norm_num) (fun h => by rw [h]; norm_num)
          have hση : |σ * η| = η := by rw [abs_mul, hσ_abs, one_mul, abs_of_pos hη_pos]
          have hση_b := abs_le.mp hση.le
          have hhalf := hη_le_half (iM r)
          simp only [tr, z0, hxM_i r, hηM_eq r, add_re, add_im, ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im, mul_zero, mul_one, sub_zero, add_zero] at hhalf ⊢
          exact ⟨⟨by linarith [hw.1.1, hε_η, hhalf], by linarith [hw.1.2, hε_η, hhalf]⟩,
            ⟨by linarith [hw.2.1, hση_b.1, hε_η, hhalf], by linarith [hw.2.2, hση_b.2, hε_η, hhalf]⟩⟩
        have htr_O : MapsTo tr (Icc (-ε) ε ×ℂ Icc (-ε) ε) O :=
          htr_Ssq.mono_right ((hsq_sub (iM r)).trans fun _ h => hE_sub_O (iM r) h.1)
        have htr_inj : Function.Injective tr := fun _ _ h => add_left_cancel h
        have htr_oo_open : IsOpen (tr '' (Ioo (-ε) ε ×ℂ Ioo (-ε) ε)) :=
          (Homeomorph.addLeft z0).isOpenMap _ (isOpen_Ioo.reProdIm isOpen_Ioo)
        have hopen_im : IsOpen (g '' (Ioo (-ε) ε ×ℂ Ioo (-ε) ε)) := by
          have heq : g '' (Ioo (-ε) ε ×ℂ Ioo (-ε) ε) = f '' (tr '' (Ioo (-ε) ε ×ℂ Ioo (-ε) ε)) :=
            image_comp f tr (Ioo (-ε) ε ×ℂ Ioo (-ε) ε)
          rw [heq]
          have hsub_oo : tr '' (Ioo (-ε) ε ×ℂ Ioo (-ε) ε) ⊆ O := by
            rintro _ ⟨w, hw, rfl⟩
            exact htr_O (Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hw).1,
              Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hw).2⟩)
          exact isOpen_image_of_manifold htr_oo_open (hfc_O.mono hsub_oo) (hfi_O.mono hsub_oo) (fun _ _ => hS.2.2 _)
        have hbox_disj_M : Disjoint (g '' (Icc (-ε) ε ×ℂ Icc (-ε) ε)) M.U := by
          rw [Set.disjoint_left]; rintro _ ⟨w, hw, rfl⟩ hwM
          exact Set.disjoint_left.mp (data.hM_disj_M r)
            (hrcM_sub r (hKEM r ▸ hEM_eq r ▸ hf_Ssq_in (iM r) (tr w) (htr_Ssq hw))) hwM
        refine ⟨g, ε, hε, hfc_O.comp (by fun_prop) htr_O,
          fun w₁ hw₁ w₂ hw₂ he => htr_inj (hfi_O (htr_O hw₁) (htr_O hw₂) he),
          hopen_im, by rintro _ ⟨w, hw, rfl⟩; exact hK_int _ (hΦ_symm_O _ (htr_O hw)),
          by simp [g, tr, hp_eq, z0], ?_, ?_⟩
        · ext y; constructor
          · rintro ⟨hyM', w, hw, rfl⟩
            have hyΔ : f (tr w) ∈ Δ := by
              by_contra hnot
              exact Set.disjoint_left.mp hbox_disj_M ⟨w, hw, rfl⟩ (show f (tr w) ∈ M.U \ Δ from hagree ▸ ⟨hyM', hnot⟩).1
            have h1 : f (tr w) ∈ M'.U ∩ Δ := ⟨hyM', hyΔ⟩; rw [hM'Δ] at h1
            have htr_im : (tr w).im = σ * η + w.im := by simp [tr, z0]
            have hw_im := (Complex.mem_reProdIm.mp hw).2
            rcases h1 with ⟨w', hw', hfe⟩ | ⟨w', hw', hfe⟩
            · rw [Complex.mem_reProdIm] at hw'
              have hw'R : w' ∈ Rη := Complex.mem_reProdIm.mpr ⟨hw'.1, by rw [mem_singleton_iff.mp hw'.2]; exact ⟨by linarith, le_rfl⟩⟩
              have hww' := hfi_O (htr_O hw) (hRη_sub_O hw'R) hfe.symm
              have him : σ * η + w.im = η := by rw [← htr_im, hww', mem_singleton_iff.mp hw'.2]
              rcases hσ with rfl | rfl
              · exact ⟨w, Complex.mem_reProdIm.mpr ⟨(Complex.mem_reProdIm.mp hw).1, by rw [mem_singleton_iff]; linarith⟩, rfl⟩
              · linarith [hw_im.2, hε_η]
            · rw [Complex.mem_reProdIm] at hw'
              have hw'R : w' ∈ Rη := Complex.mem_reProdIm.mpr ⟨hw'.1, by rw [mem_singleton_iff.mp hw'.2]; exact ⟨le_rfl, by linarith⟩⟩
              have hww' := hfi_O (htr_O hw) (hRη_sub_O hw'R) hfe.symm
              have him : σ * η + w.im = -η := by rw [← htr_im, hww', mem_singleton_iff.mp hw'.2]
              rcases hσ with rfl | rfl
              · linarith [hw_im.1, hε_η]
              · exact ⟨w, Complex.mem_reProdIm.mpr ⟨(Complex.mem_reProdIm.mp hw).1, by rw [mem_singleton_iff]; linarith⟩, rfl⟩
          · rintro ⟨w, hw, rfl⟩
            rw [Complex.mem_reProdIm] at hw
            have hwsq : w ∈ Icc (-ε) ε ×ℂ Icc (-ε) ε := Complex.mem_reProdIm.mpr ⟨hw.1, by rw [mem_singleton_iff.mp hw.2]; exact ⟨by linarith, hε.le⟩⟩
            have hre_in : (tr w).re ∈ Icc xL xR := by
              simp only [tr, z0, add_re, ofReal_re, mul_re, I_re, I_im, mul_zero, ofReal_im, mul_one, sub_zero, add_zero]
              exact ⟨by linarith [hw.1.1, hε_L], by linarith [hw.1.2, hε_R]⟩
            have him_eq : (tr w).im = σ * η := by
              simp only [tr, z0, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero, zero_add, add_zero, mem_singleton_iff.mp hw.2]
            have hM' : f (tr w) ∈ M'.U := by
              rcases hσ with rfl | rfl
              · exact (hM'Δ.symm ▸ Or.inl ⟨tr w, Complex.mem_reProdIm.mpr ⟨hre_in, by simp [him_eq]⟩, rfl⟩ : f (tr w) ∈ M'.U ∩ Δ).1
              · exact (hM'Δ.symm ▸ Or.inr ⟨tr w, Complex.mem_reProdIm.mpr ⟨hre_in, by simp [him_eq]⟩, rfl⟩ : f (tr w) ∈ M'.U ∩ Δ).1
            exact ⟨hM', w, hwsq, rfl⟩
        · ext y; constructor
          · rintro ⟨hyQ, w, hw, rfl⟩
            have hre : (tr w).re = xM r := (hf_Ssq_M r (tr w) (htr_Ssq hw)).mp hyQ
            have hwre : w.re = 0 := by
              simp only [tr, z0, add_re, ofReal_re, mul_re, I_re, I_im, mul_zero, ofReal_im, mul_one, sub_zero, add_zero] at hre
              linarith
            exact ⟨w, Complex.mem_reProdIm.mpr ⟨hwre, (Complex.mem_reProdIm.mp hw).2⟩, rfl⟩
          · rintro ⟨w, hw, rfl⟩
            rw [Complex.mem_reProdIm] at hw
            have hwsq : w ∈ Icc (-ε) ε ×ℂ Icc (-ε) ε := Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hw.1]; exact ⟨by linarith, hε.le⟩, hw.2⟩
            have hre : (tr w).re = xM r := by
              simp only [tr, z0, add_re, ofReal_re, mul_re, I_re, I_im, mul_zero, ofReal_im, mul_one, sub_zero, add_zero, mem_singleton_iff.mp hw.1]
            exact ⟨(hf_Ssq_M r (tr w) (htr_Ssq hwsq)).mpr hre, w, hwsq, rfl⟩
      rcases hp with rfl | hp'
      · exact hbuild_cross 1 (Or.inl rfl) (by simp [p_top])
      · rw [mem_singleton_iff] at hp'; subst hp'
        exact hbuild_cross (-1) (Or.inr rfl) (by simp [p_bot, neg_mul])

end BandSurgery

end GraphMinor.GHR18
