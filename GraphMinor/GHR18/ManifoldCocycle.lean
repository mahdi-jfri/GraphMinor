module

public import GraphMinor.GHR18.ArcTypeHelpers
public import GraphMinor.Surface.Collar
public import GraphMinor.Surface.PushOff
public import GraphMinor.GM07.StarDisc

/-!
# Crossing cocycles for proper 1-manifolds and disc-surgery invariance

This file develops the homological and `w₁` invariance tools needed for GHR18 Theorem 2.6
(`Surgery.lean`):

1. **Ball potentials and `w₁` invariance**:
   - `exists_potential_on_ball`: any local cocycle `ω` on a space `S` is a coboundary `δ h` on any
     open set `U ≃ₜ ball (0 : ℂ) 1`;
   - `cocInt_eq_sub_of_subset_ball`: for any path `γ` in `U`, `cocInt ω γ = h (γ 1) - h (γ 0)`;
   - `cocInt_eq_of_same_ends_in_disc`: any two paths in a closed disc `Δ ⊆ (bd S)ᶜ` with the same
     endpoints have equal `cocInt ω`;
   - `bdCohRel_of_zero_outside_disc`: a `ZMod 2` local cocycle vanishing locally outside an interior
     closed disc `Δ ⊆ (bd S)ᶜ` is a coboundary `δ h` with `h = 0` on `bd S`.

2. **Crossing cocycles for proper 1-manifolds**:
   - `HasLocalTwoSides` and `IsCrossingCocycle`: local characterization of a `ZMod 2` crossing
     cocycle along a closed 1-manifold `M ⊆ S`;
   - `bdCohRel_of_agree_outside_disc`: if two closed sets `M₁, M₂` with `M₁ ∩ bd S = {s, t}` and
     `M₂ ∩ bd S = {s, t}` agree outside an interior closed disc `Δ ⊆ (bd S)ᶜ`, then any crossing
     cocycles `ω₁, ω₂` for `M₁, M₂` satisfy `BdCohRel s t ω₁ ω₂`;
   - `isCrossingCocycle_union`: crossing cocycle for a disjoint union;
   - `arcCocycle_isCrossingCocycle`: `arcCocycle` of a proper `I`-arc is a crossing cocycle;
   - `exists_oArcCocycle`: every interior `O`-arc `O ⊆ (bd S)ᶜ` (1-sided or 2-sided) admits a
     crossing cocycle and has local two sides.
-/

@[expose] public section

namespace GraphMinor.GHR18

open Set Topology Function Metric Complex GraphMinor.Surface

universe u

/-! ### Section 1: Connectivity of an open complex annulus -/

/-- The open complex annulus `{z : ℂ | r < ‖z‖ ∧ ‖z‖ < 1}` (`0 < r < 1`) is preconnected. -/
theorem isPreconnected_annulus {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    IsPreconnected (ball (0 : ℂ) 1 \ closedBall (0 : ℂ) r) := by
  set A : Set ℂ := ball (0 : ℂ) 1 \ closedBall (0 : ℂ) r
  set ρ : ℝ := (r + 1) / 2
  have hρ_gt : r < ρ := by simp only [ρ]; linarith
  have hρ_lt : ρ < 1 := by simp only [ρ]; linarith
  have hρ_pos : 0 < ρ := hr0.trans hρ_gt
  have hbase : (ρ : ℂ) ∈ A := by
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ_pos]; exact hρ_lt
    · rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ_pos]; linarith
  have hjoin : ∀ z ∈ A, JoinedIn A z (ρ : ℂ) := by
    intro z hz
    have hz_lt : ‖z‖ < 1 := mem_ball_zero_iff.mp hz.1
    have hz_gt : r < ‖z‖ := not_le.mp (by simpa [mem_closedBall_zero_iff] using hz.2)
    have hz_pos : 0 < ‖z‖ := hr0.trans hz_gt
    let w : ℂ := ((ρ / ‖z‖ : ℝ) : ℂ) * z
    have hw_norm : ‖w‖ = ρ := by
      simp only [w, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hρ_pos hz_pos)]
      field_simp [hz_pos.ne']
    have hj1 : JoinedIn A z w := by
      let γ : unitInterval → ℂ := fun t => (((1 - t.1 + t.1 * (ρ / ‖z‖) : ℝ) : ℂ)) * z
      refine ⟨⟨⟨γ, by unfold γ; fun_prop⟩, by simp [γ], by simp [γ, w]⟩, fun t => ?_⟩
      have hscale_pos : 0 < 1 - t.1 + t.1 * (ρ / ‖z‖) := by
        have h1 : 0 ≤ 1 - t.1 := sub_nonneg.mpr t.2.2
        have h3 : 0 < ρ / ‖z‖ := div_pos hρ_pos hz_pos
        rcases eq_or_lt_of_le t.2.1 with ht0 | htpos
        · rw [← ht0]; norm_num
        · nlinarith
      have hnorm : ‖γ t‖ = (1 - t.1) * ‖z‖ + t.1 * ρ := by
        simp only [γ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hscale_pos]
        field_simp [hz_pos.ne']
      refine ⟨?_, ?_⟩
      · rw [mem_ball_zero_iff]; change ‖γ t‖ < 1; rw [hnorm]
        have hpos : 0 < (1 - t.1) * (1 - ‖z‖) + t.1 * (1 - ρ) := by
          rcases eq_or_lt_of_le t.2.1 with ht0 | htpos
          · rw [← ht0]; linarith
          · nlinarith [t.2.2, hz_lt, hρ_lt]
        linarith
      · rw [mem_closedBall_zero_iff]; change ¬ ‖γ t‖ ≤ r; rw [hnorm]
        have hpos : 0 < (1 - t.1) * (‖z‖ - r) + t.1 * (ρ - r) := by
          rcases eq_or_lt_of_le t.2.1 with ht0 | htpos
          · rw [← ht0]; linarith
          · nlinarith [t.2.2, hz_gt, hρ_gt]
        linarith
    have hj2 : JoinedIn A w (ρ : ℂ) := by
      set θ : ℝ := Complex.arg w
      have hw_eq : w = (ρ : ℂ) * Complex.exp ((θ : ℂ) * I) := by
        have h := Complex.norm_mul_exp_arg_mul_I w
        rw [hw_norm] at h; exact h.symm
      let γ : unitInterval → ℂ := fun t => (ρ : ℂ) * Complex.exp ((((1 - t.1) * θ : ℝ) : ℂ) * I)
      refine ⟨⟨⟨γ, by unfold γ; fun_prop⟩, ?_, ?_⟩, fun t => ?_⟩
      · simp [γ, hw_eq]
      · simp [γ]
      · have hn : ‖γ t‖ = ρ := by
          simp only [γ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ_pos,
            Complex.norm_exp_ofReal_mul_I, mul_one]
        refine ⟨?_, ?_⟩
        · rw [mem_ball_zero_iff]; change ‖γ t‖ < 1; rw [hn]; exact hρ_lt
        · rw [mem_closedBall_zero_iff]; change ¬ ‖γ t‖ ≤ r; rw [hn]; linarith
    exact hj1.trans hj2
  exact (IsPathConnected.isConnected ⟨(ρ : ℂ), hbase, fun z hz => (hjoin z hz).symm⟩).isPreconnected

/-! ### Section 2: Potentials on open balls and disc coboundary invariance -/

section BallPotential

variable {S : Type u} [TopologicalSpace S]

/-- Extract a homeomorphism `ball (0 : ℂ) 1 ≃ₜ discInt Δ'` from `IsClosedDisc Δ'`. -/
noncomputable def discIntHomeo {Δ' : Set S} (hΔ' : IsClosedDisc Δ') :
    ball (0 : ℂ) 1 ≃ₜ discInt Δ' := by
  classical
  let h := hΔ'.exists_isChart.choose
  let g := hΔ'.exists_isChart.choose_spec.choose
  have c : IsChart Δ' h g := hΔ'.exists_isChart.choose_spec.choose_spec
  have hgm : ∀ p : ball (0 : ℂ) 1, g p.1 ∈ discInt Δ' := fun p => by
    rw [c.discInt_eq]; exact ⟨p.1, p.2, rfl⟩
  have hhm : ∀ x : discInt Δ', h x.1 ∈ ball (0 : ℂ) 1 := fun x => by
    have hx : x.1 ∈ g '' ball (0 : ℂ) 1 := c.discInt_eq ▸ x.2
    obtain ⟨p, hp, hpe⟩ := hx
    rw [← hpe, c.hg (ball_subset_closedBall hp)]; exact hp
  exact
    { toFun := fun p => ⟨g p.1, hgm p⟩
      invFun := fun x => ⟨h x.1, hhm x⟩
      left_inv := fun p => Subtype.ext (c.hg (ball_subset_closedBall p.2))
      right_inv := fun x => Subtype.ext (c.gh x.2.1)
      continuous_toFun := Continuous.subtype_mk
        ((c.gc.mono ball_subset_closedBall).comp_continuous continuous_subtype_val fun p => p.2) hgm
      continuous_invFun := Continuous.subtype_mk
        (c.hc.comp_continuous continuous_subtype_val fun x => x.2.1) hhm }

/-- On an open ball `U ≃ₜ ball (0 : ℂ) 1`, any local cocycle `ω : S → S → A` is locally a
coboundary `ω x y = h y - h x`. -/
theorem exists_potential_on_ball {A : Type} [AddCommGroup A] {ω : S → S → A} (hω : IsCoc ω)
    {U : Set S} (hUo : IsOpen U) (e : ball (0 : ℂ) 1 ≃ₜ U) :
    ∃ (h : S → A) (N : Set (S × S)),
      (∀ z ∈ U, N ∈ 𝓝 (z, z)) ∧
      ∀ x ∈ U, ∀ y ∈ U, (x, y) ∈ N → ω x y = h y - h x := by
  classical
  obtain ⟨N₀, hN₀, hc₀⟩ := hω
  have hrad_mem : ∀ (p : ball (0 : ℂ) 1) (t : ℝ), t ∈ Icc (0 : ℝ) 1 → ((t : ℂ) * p.1) ∈ ball (0 : ℂ) 1 := by
    intro p t ht
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    have hp : ‖p.1‖ < 1 := mem_ball_zero_iff.mp p.2
    nlinarith [ht.2, norm_nonneg p.1]
  let cl : ℝ → ℝ := fun t => max 0 (min t 1)
  have hcl_mem : ∀ t : ℝ, cl t ∈ Icc (0 : ℝ) 1 := fun t => ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  have hcl_c : Continuous cl := continuous_const.max (continuous_id.min continuous_const)
  have hcl_eq : ∀ {t : ℝ}, t ∈ Icc (0 : ℝ) 1 → cl t = t := fun ht => by
    simp only [cl, min_eq_left ht.2, max_eq_right ht.1]
  let rad : ball (0 : ℂ) 1 → ℝ → S := fun p t => (e ⟨(cl t : ℂ) * p.1, hrad_mem p _ (hcl_mem t)⟩).1
  have hrad_c : ∀ p : ball (0 : ℂ) 1, Continuous (rad p) := fun p =>
    continuous_subtype_val.comp (e.continuous.comp (Continuous.subtype_mk
      ((Complex.continuous_ofReal.comp hcl_c).mul continuous_const) fun t => hrad_mem p _ (hcl_mem t)))
  let h : S → A := fun x => if hx : x ∈ U then cocInt ω (rad (e.symm ⟨x, hx⟩)) else 0
  have hball : ∀ z : U, ∃ r : ℝ, 0 < r ∧ ball (e.symm z).1 r ⊆ ball (0 : ℂ) 1 ∧
      ∀ p q : ball (0 : ℂ) 1, p.1 ∈ ball (e.symm z).1 r → q.1 ∈ ball (e.symm z).1 r → ((e p).1, (e q).1) ∈ N₀ := by
    intro z
    have hcont : Continuous (fun pq : ball (0 : ℂ) 1 × ball (0 : ℂ) 1 => ((e pq.1).1, (e pq.2).1)) :=
      (continuous_subtype_val.comp (e.continuous.comp continuous_fst)).prodMk
        (continuous_subtype_val.comp (e.continuous.comp continuous_snd))
    have hnhd : (fun pq : ball (0 : ℂ) 1 × ball (0 : ℂ) 1 => ((e pq.1).1, (e pq.2).1)) ⁻¹' N₀ ∈
        𝓝 (e.symm z, e.symm z) := by
      refine hcont.continuousAt.preimage_mem_nhds ?_
      simpa only [e.apply_symm_apply] using hN₀ z.1
    rw [nhds_prod_eq, Filter.mem_prod_iff] at hnhd
    obtain ⟨V₁, hV₁, V₂, hV₂, hVsub⟩ := hnhd
    have hV : V₁ ∩ V₂ ∈ 𝓝 (e.symm z) := Filter.inter_mem hV₁ hV₂
    rw [Metric.mem_nhds_iff] at hV
    obtain ⟨r₁, hr₁, hr₁sub⟩ := hV
    have hopen : ball (0 : ℂ) 1 ∈ 𝓝 (e.symm z).1 := isOpen_ball.mem_nhds (e.symm z).2
    rw [Metric.mem_nhds_iff] at hopen
    obtain ⟨r₂, hr₂, hr₂sub⟩ := hopen
    refine ⟨min r₁ r₂, lt_min hr₁ hr₂, (ball_subset_ball (min_le_right _ _)).trans hr₂sub, fun p q hp hq => ?_⟩
    have hp1 : p ∈ ball (e.symm z) r₁ := show dist p.1 (e.symm z).1 < r₁ from lt_of_lt_of_le hp (min_le_left _ _)
    have hq1 : q ∈ ball (e.symm z) r₁ := show dist q.1 (e.symm z).1 < r₁ from lt_of_lt_of_le hq (min_le_left _ _)
    exact hVsub (show (p, q) ∈ V₁ ×ˢ V₂ from ⟨(hr₁sub hp1).1, (hr₁sub hq1).2⟩)
  choose r hr_pos hr_sub hr_N using hball
  let V : U → Set S := fun z => Subtype.val '' (e '' {p : ball (0 : ℂ) 1 | p.1 ∈ ball (e.symm z).1 (r z)})
  have hVo : ∀ z : U, IsOpen (V z) := fun z => by
    have hop_b : IsOpen {p : ball (0 : ℂ) 1 | p.1 ∈ ball (e.symm z).1 (r z)} :=
      isOpen_ball.preimage continuous_subtype_val
    exact hUo.isOpenMap_subtype_val _ (e.isOpenMap _ hop_b)
  have hzV : ∀ z : U, z.1 ∈ V z := fun z =>
    ⟨z, ⟨e.symm z, mem_ball_self (hr_pos z), e.apply_symm_apply z⟩, rfl⟩
  let N : Set (S × S) := ⋃ z : U, V z ×ˢ V z
  refine ⟨h, N, fun z hz => ?_, fun x hx y hy hxy => ?_⟩
  · refine Filter.mem_of_superset ((hVo ⟨z, hz⟩).prod (hVo ⟨z, hz⟩) |>.mem_nhds ⟨hzV ⟨z, hz⟩, hzV ⟨z, hz⟩⟩) ?_
    exact subset_iUnion (fun w : U => V w ×ˢ V w) ⟨z, hz⟩
  · obtain ⟨z, hxV, hyV⟩ := mem_iUnion.mp hxy
    obtain ⟨xU, ⟨p, hp, hpe⟩, hxe⟩ := hxV
    obtain ⟨yU, ⟨q, hq, hqe⟩, hye⟩ := hyV
    have hx_eq : x = (e p).1 := hxe.symm.trans (congrArg Subtype.val hpe.symm)
    have hy_eq : y = (e q).1 := hye.symm.trans (congrArg Subtype.val hqe.symm)
    have hp_symm : e.symm ⟨x, hx⟩ = p := by
      apply e.injective; apply Subtype.ext; rw [e.apply_symm_apply]; exact hx_eq
    have hq_symm : e.symm ⟨y, hy⟩ = q := by
      apply e.injective; apply Subtype.ext; rw [e.apply_symm_apply]; exact hy_eq
    have hseg_mem : ∀ t : ℝ, ((1 - cl t : ℝ) : ℂ) * p.1 + (cl t : ℂ) * q.1 ∈ ball (e.symm z).1 (r z) := fun t => by
      have ht := hcl_mem t
      have := (convex_ball (e.symm z).1 (r z)) hp hq (sub_nonneg.mpr ht.2) ht.1 (by ring)
      simpa [Complex.real_smul] using this
    let seg : ℝ → S := fun t => (e ⟨((1 - cl t : ℝ) : ℂ) * p.1 + (cl t : ℂ) * q.1, hr_sub z (hseg_mem t)⟩).1
    have hseg_c : Continuous seg :=
      continuous_subtype_val.comp (e.continuous.comp (Continuous.subtype_mk
        (((Complex.continuous_ofReal.comp (continuous_const.sub hcl_c)).mul continuous_const).add
          ((Complex.continuous_ofReal.comp hcl_c).mul continuous_const))
        fun t => hr_sub z (hseg_mem t)))
    have hseg_int : cocInt ω seg = ω x y := by
      obtain ⟨n, hn_pos, hn⟩ := cocInt_eq_sum hN₀ hc₀ hseg_c.continuousOn
      rw [hn n le_rfl]
      have hall : ∀ a b : ℝ, (seg a, seg b) ∈ N₀ := fun a b => hr_N z _ _ (hseg_mem a) (hseg_mem b)
      have htele : cocSum ω seg n = ω (seg 0) (seg 1) := by
        unfold cocSum
        have hstep : ∀ k : ℕ, (∑ i ∈ Finset.range k, ω (seg ((i : ℝ) / n)) (seg (((i + 1 : ℕ) : ℝ) / n))) =
            ω (seg 0) (seg ((k : ℝ) / n)) := by
          intro k; induction k with
          | zero =>
            simp only [Finset.sum_range_zero, Nat.cast_zero, zero_div]
            have h0 := hc₀ (seg 0) (seg 0) (seg 0) (hall 0 0) (hall 0 0) (hall 0 0)
            exact (add_left_cancel (h0.trans (add_zero _).symm)).symm
          | succ k ih =>
            rw [Finset.sum_range_succ, ih]
            exact hc₀ _ _ _ (hall _ _) (hall _ _) (hall _ _)
        rw [hstep n, div_self (Nat.cast_ne_zero.mpr hn_pos.ne')]
      rw [htele]
      have h0 : seg 0 = x := by
        simp only [seg, hcl_eq ⟨le_rfl, zero_le_one⟩, sub_zero, ofReal_one, one_mul, ofReal_zero, zero_mul, add_zero]
        exact hx_eq.symm
      have h1 : seg 1 = y := by
        simp only [seg, hcl_eq ⟨zero_le_one, le_rfl⟩, sub_self, ofReal_zero, zero_mul, ofReal_one, one_mul, zero_add]
        exact hy_eq.symm
      rw [h0, h1]
    let α₁ : ℝ → ℂ := fun t =>
      if t ≤ 1 / 2 then (cl (2 * t) : ℂ) * p.1
      else ((1 - cl (2 * t - 1) : ℝ) : ℂ) * p.1 + (cl (2 * t - 1) : ℂ) * q.1
    have hα₁_mem : ∀ t : ℝ, α₁ t ∈ ball (0 : ℂ) 1 := fun t => by
      dsimp only [α₁]; split_ifs
      · exact hrad_mem p _ (hcl_mem _)
      · exact hr_sub z (hseg_mem _)
    have hα₁_c : Continuous α₁ := by
      refine continuous_if_le continuous_id continuous_const
        ((Complex.continuous_ofReal.comp (hcl_c.comp (continuous_const.mul continuous_id))).mul continuous_const).continuousOn
        ((((Complex.continuous_ofReal.comp (continuous_const.sub (hcl_c.comp ((continuous_const.mul continuous_id).sub continuous_const)))).mul continuous_const).add
          ((Complex.continuous_ofReal.comp (hcl_c.comp ((continuous_const.mul continuous_id).sub continuous_const))).mul continuous_const))).continuousOn
        fun t ht => ?_
      have h2t : 2 * t = 1 := by linarith
      have h2t1 : 2 * t - 1 = 0 := by linarith
      rw [h2t1, h2t, hcl_eq ⟨zero_le_one, le_rfl⟩, hcl_eq ⟨le_rfl, zero_le_one⟩]
      simp
    let H : ℝ → ℝ → S := fun s t =>
      (e ⟨((1 - cl s : ℝ) : ℂ) * α₁ t + (cl s : ℂ) * ((cl t : ℂ) * q.1), by
        have hs := hcl_mem s
        have := (convex_ball (0 : ℂ) 1) (hα₁_mem t) (hrad_mem q _ (hcl_mem t)) (sub_nonneg.mpr hs.2) hs.1 (by ring)
        simpa [Complex.real_smul] using this⟩).1
    have hHc : Continuous (fun st : ℝ × ℝ => H st.1 st.2) :=
      continuous_subtype_val.comp (e.continuous.comp (Continuous.subtype_mk
        (((Complex.continuous_ofReal.comp (continuous_const.sub (hcl_c.comp continuous_fst))).mul (hα₁_c.comp continuous_snd)).add
          ((Complex.continuous_ofReal.comp (hcl_c.comp continuous_fst)).mul ((Complex.continuous_ofReal.comp (hcl_c.comp continuous_snd)).mul continuous_const)))
        fun st => by
          have hs := hcl_mem st.1
          have := (convex_ball (0 : ℂ) 1) (hα₁_mem st.2) (hrad_mem q _ (hcl_mem st.2)) (sub_nonneg.mpr hs.2) hs.1 (by ring)
          simpa [Complex.real_smul] using this))
    have hα₁0 : α₁ 0 = 0 := by simp [α₁, hcl_eq ⟨le_rfl, zero_le_one⟩]
    have hα₁1 : α₁ 1 = q.1 := by
      unfold α₁
      rw [ite_eq_right (by norm_num : ¬ (1 : ℝ) ≤ 1 / 2)]
      norm_num
      rw [hcl_eq ⟨zero_le_one, le_rfl⟩]
      simp
    have hH0 : ∀ s ∈ Icc (0 : ℝ) 1, H s 0 = H 0 0 := fun s _ => by
      simp only [H, hα₁0, hcl_eq ⟨le_rfl, zero_le_one⟩, ofReal_zero, zero_mul, mul_zero, add_zero]
    have hH1 : ∀ s ∈ Icc (0 : ℝ) 1, H s 1 = H 0 1 := fun s _ => by
      simp only [H, hα₁1, hcl_eq ⟨zero_le_one, le_rfl⟩, ofReal_one, one_mul]
      apply congrArg Subtype.val
      apply congrArg e
      apply Subtype.ext
      change ((1 - cl s : ℝ) : ℂ) * q.1 + (cl s : ℂ) * q.1 =
        ((1 - cl 0 : ℝ) : ℂ) * q.1 + (cl 0 : ℂ) * q.1
      rw [hcl_eq ⟨le_rfl, zero_le_one⟩]; push_cast; ring
    have hhom := cocInt_homotopy ⟨N₀, hN₀, hc₀⟩ hHc.continuousOn hH0 hH1
    have hradp_end : rad p 1 = seg 0 := by
      simp only [rad, seg, hcl_eq ⟨zero_le_one, le_rfl⟩, hcl_eq ⟨le_rfl, zero_le_one⟩, sub_zero,
        ofReal_one, one_mul, ofReal_zero, zero_mul, add_zero]
    have hH0_eq : ∀ t ∈ Icc (0 : ℝ) 1, H 0 t = conc2 (rad p) seg t := fun t _ => by
      simp only [H, hcl_eq ⟨le_rfl, zero_le_one⟩, sub_zero, ofReal_one, one_mul, ofReal_zero, zero_mul, add_zero, conc2, α₁]
      split_ifs <;> rfl
    have hH1_eq : ∀ t ∈ Icc (0 : ℝ) 1, H 1 t = rad q t := fun t _ => by
      simp only [H, hcl_eq ⟨zero_le_one, le_rfl⟩, sub_self, ofReal_zero, zero_mul, ofReal_one, one_mul, zero_add, rad]
    have h0c : ContinuousOn (H 0) (Icc 0 1) := (hHc.comp (continuous_const.prodMk continuous_id)).continuousOn
    have h1c : ContinuousOn (H 1) (Icc 0 1) := (hHc.comp (continuous_const.prodMk continuous_id)).continuousOn
    have hconc_eq : cocInt ω (conc2 (rad p) seg) = cocInt ω (rad q) := by
      have hc1 := cocInt_congr ⟨N₀, hN₀, hc₀⟩ h0c (continuousOn_conc2 (hrad_c p).continuousOn hseg_c.continuousOn hradp_end) hH0_eq
      have hc2 := cocInt_congr ⟨N₀, hN₀, hc₀⟩ h1c (hrad_c q).continuousOn hH1_eq
      exact hc1.symm.trans (hhom.trans hc2)
    have hadd := cocInt_conc2 ⟨N₀, hN₀, hc₀⟩ (hrad_c p).continuousOn hseg_c.continuousOn hradp_end
    have hhx : h x = cocInt ω (rad p) := by simp only [h, dite_eq_left hx, hp_symm]
    have hhy : h y = cocInt ω (rad q) := by simp only [h, dite_eq_left hy, hq_symm]
    rw [hhx, hhy, ← hconc_eq, hadd, hseg_int]; abel

/-- For any curve `γ` staying inside `U`, its `cocInt` equals the endpoint difference of any local
potential `h` on `U`. -/
theorem cocInt_eq_sub_of_subset_ball {A : Type} [AddCommGroup A] {ω : S → S → A} (hω : IsCoc ω)
    {U : Set S} {h : S → A} {N : Set (S × S)}
    (hN : ∀ z ∈ U, N ∈ 𝓝 (z, z)) (hpot : ∀ x ∈ U, ∀ y ∈ U, (x, y) ∈ N → ω x y = h y - h x)
    {γ : ℝ → S} (hγ : ContinuousOn γ (Icc 0 1)) (hγU : γ '' Icc 0 1 ⊆ U) :
    cocInt ω γ = h (γ 1) - h (γ 0) := by
  classical
  have hne : U.Nonempty := ⟨γ 0, hγU ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩⟩
  let u₀ : U := ⟨hne.some, hne.some_mem⟩
  let γU : ℝ → U := fun t => if ht : t ∈ Icc (0 : ℝ) 1 then ⟨γ t, hγU ⟨t, ht, rfl⟩⟩ else u₀
  have hγU_c : ContinuousOn γU (Icc 0 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine (Continuous.subtype_mk (f := fun t : Icc (0 : ℝ) 1 => γ t.1)
      (continuousOn_iff_continuous_domRestrict.mp hγ) (fun t => hγU ⟨t.1, t.2, rfl⟩)).congr fun t => ?_
    simp only [Set.domRestrict, γU, dite_eq_left t.2]
  have hγU_val : ∀ t ∈ Icc (0 : ℝ) 1, (γU t).1 = γ t := fun t ht => by simp only [γU, dite_eq_left ht]
  let ωU : U → U → A := pbk Subtype.val ω
  let NU : Set (U × U) := (fun p : U × U => (p.1.1, p.2.1)) ⁻¹' N
  have hNU : NearDiag NU := fun z =>
    ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)).continuousAt.preimage_mem_nhds
      (hN z.1 z.2)
  have hωU_pot : ∀ x y : U, (x, y) ∈ NU → ωU x y = h y.1 - h x.1 := fun x y hxy => hpot x.1 x.2 y.1 y.2 hxy
  have h1 : cocInt ωU γU = h (γU 1).1 - h (γU 0).1 := cocInt_coboundary hNU hωU_pot hγU_c
  rw [hγU_val 1 ⟨zero_le_one, le_rfl⟩, hγU_val 0 ⟨le_rfl, zero_le_one⟩] at h1
  have h2 : cocInt ωU γU = cocInt ω γ := by
    obtain ⟨N₀, hN₀, hc₀⟩ := hω
    let N₀U : Set (U × U) := (fun p : U × U => (p.1.1, p.2.1)) ⁻¹' N₀
    have hN₀U : NearDiag N₀U := fun z =>
      ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)).continuousAt.preimage_mem_nhds
        (hN₀ z.1)
    obtain ⟨n₁, hn₁, hsum₁⟩ := cocInt_eq_sum (φ := ωU) hN₀U (fun x y z h1 h2 h3 => hc₀ _ _ _ h1 h2 h3) hγU_c
    obtain ⟨n₂, hn₂, hsum₂⟩ := cocInt_eq_sum hN₀ hc₀ hγ
    set n := max n₁ n₂
    have hn_pos : 0 < n := lt_of_lt_of_le hn₁ (le_max_left _ _)
    have hn_r : (0 : ℝ) < n := by exact_mod_cast hn_pos
    rw [hsum₁ n (le_max_left _ _), hsum₂ n (le_max_right _ _)]
    unfold cocSum ωU pbk
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < n := Finset.mem_range.mp hk
    have ha : (k : ℝ) / n ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (Nat.cast_nonneg _) hn_r.le, (div_le_one hn_r).mpr (by exact_mod_cast hk'.le)⟩
    have hb : ((k + 1 : ℕ) : ℝ) / n ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (Nat.cast_nonneg _) hn_r.le, (div_le_one hn_r).mpr (by exact_mod_cast hk')⟩
    rw [hγU_val _ ha, hγU_val _ hb]
  exact h2.symm.trans h1

/-- Any two continuous paths inside a closed disc `Δ ⊆ (bd S)ᶜ` of a surface `S` with the same
endpoints have equal `cocInt ω` for any local cocycle `ω`. -/
theorem cocInt_eq_of_same_ends_in_disc {A : Type} [AddCommGroup A] (hS : IsSurface S)
    {ω : S → S → A} (hω : IsCoc ω) {Δ : Set S} (hΔ : IsClosedDisc Δ) (hΔ_int : Δ ⊆ (bd S)ᶜ)
    {γ₁ γ₂ : ℝ → S} (hγ₁ : ContinuousOn γ₁ (Icc 0 1)) (hγ₂ : ContinuousOn γ₂ (Icc 0 1))
    (hsub₁ : γ₁ '' Icc 0 1 ⊆ Δ) (hsub₂ : γ₂ '' Icc 0 1 ⊆ Δ)
    (h0 : γ₁ 0 = γ₂ 0) (h1 : γ₁ 1 = γ₂ 1) :
    cocInt ω γ₁ = cocInt ω γ₂ := by
  have : T2Space S := hS.2.1
  have hint : ∀ x ∈ discBd Δ, IsInteriorPoint x := fun x hx =>
    not_not.mp (hΔ_int (discBd_subset Δ hx))
  obtain ⟨Δ', hΔ', hsub', -⟩ :=
    exists_disc_around hS.2.2 hΔ hint (isClosed_bd S).isOpen_compl (fun x hx => hΔ_int (discBd_subset Δ hx))
  have hUo : IsOpen (discInt Δ') := hΔ'.isOpen_discInt hS.2.2
  obtain ⟨h, N, hN, hpot⟩ := exists_potential_on_ball hω hUo (discIntHomeo hΔ')
  have h1' := cocInt_eq_sub_of_subset_ball hω hN hpot hγ₁ (hsub₁.trans hsub')
  have h2' := cocInt_eq_sub_of_subset_ball hω hN hpot hγ₂ (hsub₂.trans hsub')
  rw [h1', h2', h0, h1]

/-- A `ZMod 2` local cocycle on a surface `S` that vanishes locally outside a closed disc
`Δ ⊆ (bd S)ᶜ` is a coboundary `δ h` with `h = 0` on `bd S`. -/
theorem coboundary_of_zero_outside_disc (hS : IsSurface S) {η : S → S → ZMod 2} (hη : IsCoc η)
    {Δ : Set S} (hΔ : IsClosedDisc Δ) (hΔ_int : Δ ⊆ (bd S)ᶜ)
    (hzero : ∀ z ∉ Δ, ∃ W : Set S, IsOpen W ∧ z ∈ W ∧ ∀ x ∈ W, ∀ y ∈ W, η x y = 0) :
    ∃ h : S → ZMod 2, (∀ x ∈ bd S, h x = 0) ∧
      ∃ N : Set (S × S), NearDiag N ∧ ∀ x y, (x, y) ∈ N → η x y = h y - h x := by
  classical
  have : T2Space S := hS.2.1
  have hint : ∀ x ∈ discBd Δ, IsInteriorPoint x := fun x hx =>
    not_not.mp (hΔ_int (discBd_subset Δ hx))
  obtain ⟨Δ', hΔ', hsub', hΔ'sub⟩ :=
    exists_disc_around hS.2.2 hΔ hint (isClosed_bd S).isOpen_compl (fun x hx => hΔ_int (discBd_subset Δ hx))
  have hΔ'_int : Δ' ⊆ (bd S)ᶜ := hΔ'sub.trans (union_subset hΔ_int Subset.rfl)
  set U : Set S := discInt Δ'
  have hUo : IsOpen U := hΔ'.isOpen_discInt hS.2.2
  have hU_int : U ⊆ (bd S)ᶜ := fun x hx => hΔ'_int hx.1
  let e : ball (0 : ℂ) 1 ≃ₜ U := discIntHomeo hΔ'
  -- Bound `e.symm '' Δ` inside `closedBall (0 : ℂ) r` for some `0 < r < 1`:
  let K : Set ℂ := Subtype.val '' (e.symm '' (Subtype.val ⁻¹' Δ))
  have hK_cpt : IsCompact K := by
    have hΔ_cpt_U : IsCompact (Subtype.val ⁻¹' Δ : Set U) := by
      have h1 : IsCompact Δ := hΔ.isCompact
      have h2 : Subtype.val '' (Subtype.val ⁻¹' Δ : Set U) = Δ := by
        ext x; simp only [mem_image, mem_preimage, Subtype.exists, exists_and_right, exists_eq_right]
        exact ⟨fun ⟨_, hx⟩ => hx, fun hx => ⟨hsub' hx, hx⟩⟩
      exact (Topology.IsInducing.subtypeVal.isCompact_iff).mpr (h2.symm ▸ h1)
    exact (hΔ_cpt_U.image e.symm.continuous).image continuous_subtype_val
  have hK_sub : K ⊆ ball (0 : ℂ) 1 := by
    rintro _ ⟨p, -, rfl⟩; exact p.2
  have hex_r : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ K ⊆ closedBall (0 : ℂ) r := by
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · exact ⟨1 / 2, by norm_num, by norm_num, by rw [hKe]; exact empty_subset _⟩
    · obtain ⟨z₀, hz₀K, hz₀max⟩ := hK_cpt.exists_isMaxOn hKne continuous_norm.continuousOn
      have hlt : ‖z₀‖ < 1 := mem_ball_zero_iff.mp (hK_sub hz₀K)
      set r := max (1 / 2) ((‖z₀‖ + 1) / 2)
      refine ⟨r, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (le_max_left _ _),
        max_lt (by norm_num) (by linarith), fun z hz => ?_⟩
      rw [mem_closedBall_zero_iff]
      have h1 : ‖z‖ ≤ ‖z₀‖ := hz₀max hz
      exact h1.trans ((by linarith : ‖z₀‖ ≤ (‖z₀‖ + 1) / 2).trans (le_max_right _ _))
  obtain ⟨r, hr0, hr1, hKr⟩ := hex_r
  let D : Set S := Subtype.val '' (e '' {p : ball (0 : ℂ) 1 | p.1 ∈ closedBall (0 : ℂ) r})
  have hΔD : Δ ⊆ D := fun x hx => by
    have hxU : x ∈ U := hsub' hx
    refine ⟨⟨x, hxU⟩, ⟨e.symm ⟨x, hxU⟩, ?_, e.apply_symm_apply _⟩, rfl⟩
    exact hKr ⟨e.symm ⟨x, hxU⟩, ⟨⟨x, hxU⟩, hx, rfl⟩, rfl⟩
  have hDU : D ⊆ U := by rintro _ ⟨u, -, rfl⟩; exact u.2
  have hDc : IsClosed D := by
    have hball_cpt : IsCompact {p : ball (0 : ℂ) 1 | p.1 ∈ closedBall (0 : ℂ) r} := by
      rw [Topology.IsInducing.subtypeVal.isCompact_iff]
      have heq : Subtype.val '' {p : ball (0 : ℂ) 1 | p.1 ∈ closedBall (0 : ℂ) r} = closedBall (0 : ℂ) r := by
        ext z; simp only [mem_image, mem_ofPred_eq, Subtype.exists, exists_and_right, exists_eq_right]
        exact ⟨fun ⟨_, hz⟩ => hz, fun hz => ⟨closedBall_subset_ball hr1 hz, hz⟩⟩
      rw [heq]; exact isCompact_closedBall _ _
    exact ((hball_cpt.image e.continuous).image continuous_subtype_val).isClosed
  -- `U \ D` is preconnected (homeomorphic to the annulus `ball 0 1 \ closedBall 0 r`):
  have hUD_conn : IsPreconnected (U \ D) := by
    have him : (fun p : ball (0 : ℂ) 1 => (e p).1) '' {p : ball (0 : ℂ) 1 | p.1 ∈ ball (0 : ℂ) 1 \ closedBall (0 : ℂ) r} = U \ D := by
      ext x; constructor
      · rintro ⟨p, hp, rfl⟩
        refine ⟨(e p).2, ?_⟩
        rintro ⟨u, ⟨q, hq, hqu⟩, hux⟩
        have hpq : p = q := e.injective (Subtype.ext (hqu.symm ▸ hux.symm))
        exact hp.2 (hpq ▸ hq)
      · rintro ⟨hxU, hxD⟩
        refine ⟨e.symm ⟨x, hxU⟩, ⟨(e.symm ⟨x, hxU⟩).2, fun hcr => hxD ⟨⟨x, hxU⟩, ⟨e.symm ⟨x, hxU⟩, hcr, e.apply_symm_apply _⟩, rfl⟩⟩, ?_⟩
        simp
    have hann : IsPreconnected {p : ball (0 : ℂ) 1 | p.1 ∈ ball (0 : ℂ) 1 \ closedBall (0 : ℂ) r} := by
      have h1 := isPreconnected_annulus hr0 hr1
      refine (Topology.IsInducing.subtypeVal.isPreconnected_image (s := {p : ball (0 : ℂ) 1 | p.1 ∈ ball (0 : ℂ) 1 \ closedBall (0 : ℂ) r})).mp ?_
      have heq : Subtype.val '' {p : ball (0 : ℂ) 1 | p.1 ∈ ball (0 : ℂ) 1 \ closedBall (0 : ℂ) r} = ball (0 : ℂ) 1 \ closedBall (0 : ℂ) r := by
        ext z; simp only [mem_image, mem_ofPred_eq, Subtype.exists, exists_and_right, exists_eq_right]
        exact ⟨fun ⟨_, hz⟩ => hz, fun hz => ⟨hz.1, hz⟩⟩
      rw [heq]; exact h1
    rw [← him]
    exact hann.image _ (continuous_subtype_val.comp e.continuous).continuousOn
  have hUD_ne : (U \ D).Nonempty := by
    set ρ : ℝ := (r + 1) / 2
    have hρ0 : 0 < ρ := by simp only [ρ]; linarith
    have hρ1 : ρ < 1 := by simp only [ρ]; linarith
    have hρb : (ρ : ℂ) ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0]; exact hρ1
    refine ⟨(e ⟨(ρ : ℂ), hρb⟩).1, (e _).2, ?_⟩
    rintro ⟨u, ⟨q, hq, hqu⟩, hux⟩
    have hEq : (⟨(ρ : ℂ), hρb⟩ : ball (0 : ℂ) 1) = q := e.injective (Subtype.ext (hqu.symm ▸ hux.symm))
    have hEq_val : (ρ : ℂ) = q.1 := congrArg Subtype.val hEq
    have hle : ‖(ρ : ℂ)‖ ≤ r := mem_closedBall_zero_iff.mp (hEq_val.symm ▸ hq)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0] at hle
    simp only [ρ] at hle; linarith
  -- Potential `h` on `U` from `exists_potential_on_ball`:
  obtain ⟨h, NU, hNU, hpot⟩ := exists_potential_on_ball hη hUo e
  -- `h` is locally constant on `U \ D`:
  have hlc : IsLocallyConstant (fun x : (U \ D : Set S) => h x.1) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨z, hzU, hzD⟩
    have hzΔ : z ∉ Δ := fun h' => hzD (hΔD h')
    obtain ⟨W, hWo, hzW, hWz⟩ := hzero z hzΔ
    obtain ⟨V₁, hV₁, V₂, hV₂, hVsub⟩ := mem_nhds_prod_iff.mp (hNU z hzU)
    have hnhd : Subtype.val ⁻¹' (W ∩ V₁ ∩ V₂ ∩ U) ∈ 𝓝 (⟨z, hzU, hzD⟩ : (U \ D : Set S)) :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds
        (Filter.inter_mem (Filter.inter_mem (Filter.inter_mem (hWo.mem_nhds hzW) hV₁) hV₂) (hUo.mem_nhds hzU))
    refine Filter.mem_of_superset hnhd fun y hy => ?_
    have h1 := hpot z hzU y.1 hy.2 (hVsub ⟨mem_of_mem_nhds hV₁, hy.1.2⟩)
    have h2 := hWz z hzW y.1 hy.1.1.1
    rw [h2] at h1
    exact (sub_eq_zero.mp h1.symm)
  obtain ⟨x₀, hx₀⟩ := hUD_ne
  set c₀ : ZMod 2 := h x₀
  have hconst : ∀ x ∈ U \ D, h x = c₀ := fun x hx => by
    have : PreconnectedSpace (U \ D : Set S) := isPreconnected_iff_preconnectedSpace.mp hUD_conn
    exact hlc.apply_eq_of_isPreconnected isPreconnected_univ (mem_univ ⟨x, hx⟩) (mem_univ ⟨x₀, hx₀⟩)
  let h' : S → ZMod 2 := fun x => if x ∈ U then h x - c₀ else 0
  have hh'_zero : ∀ x ∉ D, h' x = 0 := fun x hxD => by
    by_cases hxU : x ∈ U
    · simp only [h', ite_eq_left hxU, hconst x ⟨hxU, hxD⟩, sub_self]
    · simp only [h', ite_eq_right hxU]
  -- Assemble `NearDiag N`:
  let N_out : Set (S × S) := ⋃ (z : S) (hz : z ∉ Δ), (hzero z hz).choose ×ˢ (hzero z hz).choose
  let N : Set (S × S) := (NU ∩ (U ×ˢ U)) ∪ (N_out ∩ (Dᶜ ×ˢ Dᶜ))
  refine ⟨h', fun x hx => hh'_zero x fun hxD => hU_int (hDU hxD) hx, N, fun z => ?_, fun x y hxy => ?_⟩
  · by_cases hzU : z ∈ U
    · exact Filter.mem_of_superset (Filter.inter_mem (hNU z hzU) ((hUo.prod hUo).mem_nhds ⟨hzU, hzU⟩)) subset_union_left
    · have hzD : z ∉ D := fun h' => hzU (hDU h')
      have hzΔ : z ∉ Δ := fun h' => hzD (hΔD h')
      have hspec := (hzero z hzΔ).choose_spec
      refine Filter.mem_of_superset
        (Filter.inter_mem ((hspec.1.prod hspec.1).mem_nhds ⟨hspec.2.1, hspec.2.1⟩)
          ((hDc.isOpen_compl.prod hDc.isOpen_compl).mem_nhds ⟨hzD, hzD⟩))
        (fun p hp => Or.inr ⟨mem_iUnion₂.mpr ⟨z, hzΔ, hp.1⟩, hp.2⟩)
  · rcases hxy with ⟨h1, hxU, hyU⟩ | ⟨h1, hxD, hyD⟩
    · simp only [h', ite_eq_left hxU, ite_eq_left hyU]
      rw [hpot x hxU y hyU h1]; ring
    · obtain ⟨z, hzΔ, hxW, hyW⟩ := mem_iUnion₂.mp h1
      rw [hh'_zero x hxD, hh'_zero y hyD, sub_self]
      exact (hzero z hzΔ).choose_spec.2.2 x hxW y hyW

end BallPotential

/-! ### Section 3: Crossing cocycles and invariance under interior disc replacement -/

section CrossingCocycle

variable {S : Type u} [TopologicalSpace S]

/-- `M` locally splits small neighborhoods of `z` into two disjoint nonempty connected open sides. -/
def HasLocalTwoSides (M : Set S) (z : S) : Prop :=
  ∀ V : Set S, IsOpen V → z ∈ V →
    ∃ U A B : Set S, IsOpen U ∧ z ∈ U ∧ U ⊆ V ∧
      U \ M = A ∪ B ∧ Disjoint A B ∧ IsOpen A ∧ IsOpen B ∧
      IsPreconnected A ∧ IsPreconnected B ∧ A.Nonempty ∧ B.Nonempty

/-- A `ZMod 2` local cocycle `ω` is a *crossing cocycle* for a closed set `M ⊆ S` if it vanishes
locally off `M` and near every `z ∈ M` is given by `δ f` for a function `f : S → ZMod 2` taking
distinct constant values on the two local sides of `M`. -/
def IsCrossingCocycle (M : Set S) (ω : S → S → ZMod 2) : Prop :=
  IsCoc ω ∧
  (∀ z ∉ M, ∃ W : Set S, IsOpen W ∧ z ∈ W ∧ ∀ x ∈ W, ∀ y ∈ W, ω x y = 0) ∧
  (∀ z ∈ M, ∃ W A B : Set S, IsOpen W ∧ z ∈ W ∧
    W \ M = A ∪ B ∧ Disjoint A B ∧ IsOpen A ∧ IsOpen B ∧
    (∀ U : Set S, IsOpen U → z ∈ U → (U ∩ A).Nonempty ∧ (U ∩ B).Nonempty) ∧
    ∃ f : S → ZMod 2, (∀ x ∈ W, ∀ y ∈ W, ω x y = f y - f x) ∧
      (∀ x ∈ A, ∀ y ∈ A, f x = f y) ∧ (∀ x ∈ B, ∀ y ∈ B, f x = f y) ∧
      (∀ x ∈ A, ∀ y ∈ B, f x ≠ f y))

omit [TopologicalSpace S] in
/-- Helper: if two `ZMod 2` functions each take opposite constant values on two sides `A, B`, then
their difference is constant across `A ∪ B`. -/
theorem zmod2_diff_const_of_two_sides {A B : Set S} {f₁ f₂ : S → ZMod 2}
    (h1A : ∀ x ∈ A, ∀ y ∈ A, f₁ x = f₁ y) (h1B : ∀ x ∈ B, ∀ y ∈ B, f₁ x = f₁ y)
    (h1AB : ∀ x ∈ A, ∀ y ∈ B, f₁ x ≠ f₁ y)
    (h2A : ∀ x ∈ A, ∀ y ∈ A, f₂ x = f₂ y) (h2B : ∀ x ∈ B, ∀ y ∈ B, f₂ x = f₂ y)
    (h2AB : ∀ x ∈ A, ∀ y ∈ B, f₂ x ≠ f₂ y) :
    ∀ x ∈ A ∪ B, ∀ y ∈ A ∪ B, f₁ x - f₂ x = f₁ y - f₂ y := by
  have hne_z2 : ∀ a b : ZMod 2, a ≠ b → b = a + 1 := by decide
  intro x hx y hy
  rcases hx with hxA | hxB <;> rcases hy with hyA | hyB
  · rw [h1A x hxA y hyA, h2A x hxA y hyA]
  · rw [hne_z2 _ _ (h1AB x hxA y hyB), hne_z2 _ _ (h2AB x hxA y hyB)]; ring
  · rw [hne_z2 _ _ (h1AB y hyA x hxB), hne_z2 _ _ (h2AB y hyA x hxB)]; ring
  · rw [h1B x hxB y hyB, h2B x hxB y hyB]

/-- **Master Disc-Surgery Cohomology Invariance Theorem**:
If two closed sets `M₁, M₂ ⊆ S` with `M₁ ∩ bd S = {s, t}` and `M₂ ∩ bd S = {s, t}` agree outside an
interior closed disc `Δ ⊆ (bd S)ᶜ`, `M₁` has local two sides at every point of `M₁ \ Δ`, and `ω₁, ω₂`
are crossing cocycles for `M₁, M₂`, then `BdCohRel s t ω₁ ω₂`. -/
theorem bdCohRel_of_agree_outside_disc (hS : IsSurface S) {s t : S}
    {M₁ M₂ Δ : Set S} (hM₁ : IsClosed M₁) (hΔ : IsClosedDisc Δ) (hΔ_int : Δ ⊆ (bd S)ᶜ)
    (hb₁ : M₁ ∩ bd S = {s, t}) (hagree : M₁ \ Δ = M₂ \ Δ)
    (htwo : ∀ z ∈ M₁ \ Δ, HasLocalTwoSides M₁ z)
    {ω₁ ω₂ : S → S → ZMod 2} (hω₁ : IsCrossingCocycle M₁ ω₁) (hω₂ : IsCrossingCocycle M₂ ω₂) :
    BdCohRel s t ω₁ ω₂ := by
  classical
  have : T2Space S := hS.2.1
  have hΔc : IsClosed Δ := hΔ.isClosed
  -- For every `z ∈ M₁ \ Δ`, find an open `U ⊆ Δᶜ` on which `ω₁ - ω₂ = δ(f₁ - f₂)` and `f₁ - f₂` is constant on `U \ M₁`:
  have hloc : ∀ z ∈ M₁ \ Δ, ∃ (U : Set S) (f₁ f₂ : S → ZMod 2) (c : ZMod 2),
      IsOpen U ∧ z ∈ U ∧ U ⊆ Δᶜ ∧ (U \ M₁).Nonempty ∧
      (∀ x ∈ U, ∀ y ∈ U, ω₁ x y = f₁ y - f₁ x) ∧
      (∀ x ∈ U, ∀ y ∈ U, ω₂ x y = f₂ y - f₂ x) ∧
      (∀ x ∈ U \ M₁, f₁ x - f₂ x = c) := by
    intro z hz
    have hzM₂ : z ∈ M₂ := (hagree ▸ hz).1
    obtain ⟨W₁, A₁, B₁, hW₁o, hzW₁, hW₁s, hAB₁, hA₁o, hB₁o, hAB₁_near, f₁, hf₁ω, hf₁A, hf₁B, hf₁AB⟩ := hω₁.2.2 z hz.1
    obtain ⟨W₂, A₂, B₂, hW₂o, hzW₂, hW₂s, hAB₂, hA₂o, hB₂o, hAB₂_near, f₂, hf₂ω, hf₂A, hf₂B, hf₂AB⟩ := hω₂.2.2 z hzM₂
    have hV : IsOpen (W₁ ∩ W₂ ∩ Δᶜ) := (hW₁o.inter hW₂o).inter hΔc.isOpen_compl
    obtain ⟨U, UA, UB, hUo, hzU, hUV, hUs, hUdj, hUAo, hUBo, hUAc, hUBc, hUAne, hUBne⟩ :=
      htwo z hz _ hV ⟨⟨hzW₁, hzW₂⟩, hz.2⟩
    have hUΔ : U ⊆ Δᶜ := fun x hx => (hUV hx).2
    have hUM_eq : U \ M₁ = U \ M₂ := by
      ext x; simp only [mem_sdiff]
      exact ⟨fun ⟨hxU, hx1⟩ => ⟨hxU, fun hx2 => hx1 (show x ∈ M₁ \ Δ from hagree.symm ▸ ⟨hx2, hUΔ hxU⟩).1⟩,
             fun ⟨hxU, hx2⟩ => ⟨hxU, fun hx1 => hx2 (show x ∈ M₂ \ Δ from hagree ▸ ⟨hx1, hUΔ hxU⟩).1⟩⟩
    have hside_split : ∀ {A B : Set S} {f : S → ZMod 2},
        IsOpen A → IsOpen B → Disjoint A B → U \ M₁ ⊆ A ∪ B →
        (∀ x ∈ U, x ∈ A ∪ B → x ∉ M₁) → (U ∩ A).Nonempty → (U ∩ B).Nonempty →
        (∀ x ∈ A, ∀ y ∈ A, f x = f y) → (∀ x ∈ B, ∀ y ∈ B, f x = f y) → (∀ x ∈ A, ∀ y ∈ B, f x ≠ f y) →
        (∀ x ∈ UA, ∀ y ∈ UA, f x = f y) ∧ (∀ x ∈ UB, ∀ y ∈ UB, f x = f y) ∧ (∀ x ∈ UA, ∀ y ∈ UB, f x ≠ f y) := by
      intro A B f hAo hBo hABd hsub hABnM hneA hneB hfA hfB hfAB
      have hUA_sub : UA ⊆ A ∪ B := (hUs ▸ subset_union_left).trans hsub
      have hUB_sub : UB ⊆ A ∪ B := (hUs ▸ subset_union_right).trans hsub
      have hU_sub : ∀ X, IsPreconnected X → X ⊆ A ∪ B → X ⊆ A ∨ X ⊆ B := fun X hXc hXsub => by
        by_contra hnot; push Not at hnot
        obtain ⟨a, haX, haA⟩ := Set.not_subset.mp hnot.1
        obtain ⟨b, hbX, hbB⟩ := Set.not_subset.mp hnot.2
        have haB : a ∈ B := (hXsub haX).resolve_left haA
        have hbA : b ∈ A := (hXsub hbX).resolve_right hbB
        obtain ⟨w, -, hwA, hwB⟩ := hXc A B hAo hBo hXsub ⟨b, hbX, hbA⟩ ⟨a, haX, haB⟩
        exact Set.disjoint_left.mp hABd hwA hwB
      rcases hU_sub UA hUAc hUA_sub with h1 | h1 <;> rcases hU_sub UB hUBc hUB_sub with h2 | h2
      · exfalso
        obtain ⟨b, hbU, hbB⟩ := hneB
        have hbM : b ∉ M₁ := hABnM b hbU (Or.inr hbB)
        have hbAB : b ∈ UA ∪ UB := hUs ▸ (⟨hbU, hbM⟩ : b ∈ U \ M₁)
        have hbA : b ∈ A := hbAB.elim (fun h => h1 h) (fun h => h2 h)
        exact Set.disjoint_left.mp hABd hbA hbB
      · exact ⟨fun x hx y hy => hfA x (h1 hx) y (h1 hy),
               fun x hx y hy => hfB x (h2 hx) y (h2 hy),
               fun x hx y hy => hfAB x (h1 hx) y (h2 hy)⟩
      · exact ⟨fun x hx y hy => hfB x (h1 hx) y (h1 hy),
               fun x hx y hy => hfA x (h2 hx) y (h2 hy),
               fun x hx y hy => (hfAB y (h2 hy) x (h1 hx)).symm⟩
      · exfalso
        obtain ⟨a, haU, haA⟩ := hneA
        have haM : a ∉ M₁ := hABnM a haU (Or.inl haA)
        have haAB : a ∈ UA ∪ UB := hUs ▸ (⟨haU, haM⟩ : a ∈ U \ M₁)
        have haB : a ∈ B := haAB.elim (fun h => h1 h) (fun h => h2 h)
        exact Set.disjoint_left.mp hABd haA haB
    have h1s := hside_split hA₁o hB₁o hAB₁
      (fun x hx => hW₁s ▸ ⟨(hUV hx.1).1.1, hx.2⟩)
      (fun x _ hx => (hW₁s.symm ▸ hx).2)
      (hAB₁_near U hUo hzU).1 (hAB₁_near U hUo hzU).2 hf₁A hf₁B hf₁AB
    have h2s := hside_split hA₂o hB₂o hAB₂
      (fun x hx => hW₂s ▸ ⟨(hUV hx.1).1.2, (hUM_eq ▸ hx).2⟩)
      (fun x hxU hx hxM₁ => (hW₂s.symm ▸ hx).2 (show x ∈ M₂ \ Δ from hagree ▸ ⟨hxM₁, hUΔ hxU⟩).1)
      (hAB₂_near U hUo hzU).1 (hAB₂_near U hUo hzU).2 hf₂A hf₂B hf₂AB
    have hconst := zmod2_diff_const_of_two_sides h1s.1 h1s.2.1 h1s.2.2 h2s.1 h2s.2.1 h2s.2.2
    obtain ⟨p₀, hp₀A⟩ := hUAne
    refine ⟨U, f₁, f₂, f₁ p₀ - f₂ p₀, hUo, hzU, hUΔ, ⟨p₀, hUs.symm ▸ Or.inl hp₀A⟩,
      fun x hx y hy => hf₁ω x (hUV hx).1.1 y (hUV hy).1.1,
      fun x hx y hy => hf₂ω x (hUV hx).1.2 y (hUV hy).1.2,
      fun x hx => hconst x (hUs ▸ hx) p₀ (Or.inl hp₀A)⟩
  -- Define `g : S → ZMod 2` supported on `M₁ \ Δ`:
  let g : S → ZMod 2 := fun x =>
    if hx : x ∈ M₁ \ Δ then
      let p := (hloc x hx).choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.1.some
      ω₁ p x - ω₂ p x
    else 0
  have hg_bd : ∀ x ∈ bd S \ {s, t}, g x = 0 := fun x hx => by
    refine dite_eq_right fun hxM => ?_
    exact hx.2 (hb₁ ▸ ⟨hxM.1, hx.1⟩)
  -- Check `η x y := (ω₁ x y - ω₂ x y) - (g y - g x)` is `IsCoc` and vanishes locally on `Δᶜ`:
  let η : S → S → ZMod 2 := fun x y => (ω₁ x y - ω₂ x y) - (g y - g x)
  have hη_coc : IsCoc η := by
    obtain ⟨N₁, hN₁, hc₁⟩ := hω₁.1
    obtain ⟨N₂, hN₂, hc₂⟩ := hω₂.1
    refine ⟨N₁ ∩ N₂, fun z => Filter.inter_mem (hN₁ z) (hN₂ z), fun x y z h1 h2 h3 => ?_⟩
    have e1 := hc₁ x y z h1.1 h2.1 h3.1
    have e2 := hc₂ x y z h1.2 h2.2 h3.2
    simp only [η]; linear_combination e1 - e2
  have hη_zero : ∀ z ∉ Δ, ∃ W : Set S, IsOpen W ∧ z ∈ W ∧ ∀ x ∈ W, ∀ y ∈ W, η x y = 0 := by
    intro z hzΔ
    by_cases hzM : z ∈ M₁
    · obtain ⟨U, f₁, f₂, c, hUo, hzU, hUΔ, hUne, hf₁ω, hf₂ω, hc⟩ := hloc z ⟨hzM, hzΔ⟩
      refine ⟨U, hUo, hzU, fun x hx y hy => ?_⟩
      -- Show `g w = (f₁ w - f₂ w) - c` for all `w ∈ U`:
      have hg_eq : ∀ w ∈ U, g w = (f₁ w - f₂ w) - c := fun w hwU => by
        by_cases hwM : w ∈ M₁
        · have hw : w ∈ M₁ \ Δ := ⟨hwM, hUΔ hwU⟩
          have hsp := (hloc w hw).choose_spec.choose_spec.choose_spec.choose_spec
          let Uw := (hloc w hw).choose
          let f₁w := (hloc w hw).choose_spec.choose
          let f₂w := (hloc w hw).choose_spec.choose_spec.choose
          let cw := (hloc w hw).choose_spec.choose_spec.choose_spec.choose
          let pw := hsp.2.2.2.1.some
          have hpw : pw ∈ Uw \ M₁ := hsp.2.2.2.1.some_mem
          -- Pick a point `q ∈ (U ∩ Uw) \ M₁` to relate `c` and `cw`:
          obtain ⟨q, hqU, hqUw, hqM⟩ : ∃ q, q ∈ U ∧ q ∈ Uw ∧ q ∉ M₁ := by
            have hUo' : IsOpen (U ∩ Uw) := hUo.inter hsp.1
            obtain ⟨W₁, A₁, B₁, _, _, hW₁s, _, _, _, hAB₁_near, -⟩ := hω₁.2.2 w hwM
            obtain ⟨q, ⟨hq1, hq2⟩, hqA⟩ := (hAB₁_near (U ∩ Uw) hUo' ⟨hwU, hsp.2.1⟩).1
            exact ⟨q, hq1, hq2, (show q ∈ W₁ \ M₁ from hW₁s.symm ▸ Or.inl hqA).2⟩
          have hgval : g w = ω₁ pw w - ω₂ pw w := dite_eq_left hw
          have hpw_eq : ω₁ pw w - ω₂ pw w = (f₁w w - f₂w w) - cw := by
            have e1 : ω₁ pw w = f₁w w - f₁w pw := hsp.2.2.2.2.1 pw hpw.1 w hsp.2.1
            have e2 : ω₂ pw w = f₂w w - f₂w pw := hsp.2.2.2.2.2.1 pw hpw.1 w hsp.2.1
            have e3 : f₁w pw - f₂w pw = cw := hsp.2.2.2.2.2.2 pw hpw
            linear_combination e1 - e2 - e3
          have hq_eq : (f₁w w - f₂w w) - cw = ω₁ q w - ω₂ q w := by
            have e1 : ω₁ q w = f₁w w - f₁w q := hsp.2.2.2.2.1 q hqUw w hsp.2.1
            have e2 : ω₂ q w = f₂w w - f₂w q := hsp.2.2.2.2.2.1 q hqUw w hsp.2.1
            have e3 : f₁w q - f₂w q = cw := hsp.2.2.2.2.2.2 q ⟨hqUw, hqM⟩
            linear_combination -e1 + e2 + e3
          have hq_eq2 : ω₁ q w - ω₂ q w = (f₁ w - f₂ w) - c := by
            have e1 := hf₁ω q hqU w hwU
            have e2 := hf₂ω q hqU w hwU
            have e3 := hc q ⟨hqU, hqM⟩
            linear_combination e1 - e2 - e3
          exact hgval.trans (hpw_eq.trans (hq_eq.trans hq_eq2))
        · have hg0 : g w = 0 := dite_eq_right fun h => hwM h.1
          rw [hg0, hc w ⟨hwU, hwM⟩, sub_self]
      simp only [η, hf₁ω x hx y hy, hf₂ω x hx y hy, hg_eq x hx, hg_eq y hy]; ring
    · have hzM₂ : z ∉ M₂ := fun h => hzM (show z ∈ M₁ \ Δ from hagree.symm ▸ ⟨h, hzΔ⟩).1
      obtain ⟨W₁, hW₁o, hzW₁, hW₁⟩ := hω₁.2.1 z hzM
      obtain ⟨W₂, hW₂o, hzW₂, hW₂⟩ := hω₂.2.1 z hzM₂
      refine ⟨W₁ ∩ W₂ ∩ M₁ᶜ ∩ Δᶜ, ((hW₁o.inter hW₂o).inter hM₁.isOpen_compl).inter hΔc.isOpen_compl,
        ⟨⟨⟨hzW₁, hzW₂⟩, hzM⟩, hzΔ⟩, fun x hx y hy => ?_⟩
      have hgx : g x = 0 := dite_eq_right fun h => hx.1.2 h.1
      have hgy : g y = 0 := dite_eq_right fun h => hy.1.2 h.1
      simp only [η, hW₁ x hx.1.1.1 y hy.1.1.1, hW₂ x hx.1.1.2 y hy.1.1.2, hgx, hgy, sub_self]
  obtain ⟨h', hh'_bd, N, hN, hη_eq⟩ := coboundary_of_zero_outside_disc hS hη_coc hΔ hΔ_int hη_zero
  refine ⟨fun x => g x + h' x, fun x hx => by simp [hg_bd x hx, hh'_bd x hx.1], N, hN, fun x y hxy => ?_⟩
  have e := hη_eq x y hxy
  simp only [η] at e
  linear_combination e

/-- Crossing cocycle for a disjoint union of two closed sets. -/
theorem isCrossingCocycle_union {M₁ M₂ : Set S} (hM₁ : IsClosed M₁) (hM₂ : IsClosed M₂)
    (hdisj : Disjoint M₁ M₂) {ω₁ ω₂ : S → S → ZMod 2}
    (h₁ : IsCrossingCocycle M₁ ω₁) (h₂ : IsCrossingCocycle M₂ ω₂) :
    IsCrossingCocycle (M₁ ∪ M₂) (fun x y => ω₁ x y + ω₂ x y) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨N₁, hN₁, hc₁⟩ := h₁.1
    obtain ⟨N₂, hN₂, hc₂⟩ := h₂.1
    refine ⟨N₁ ∩ N₂, fun z => Filter.inter_mem (hN₁ z) (hN₂ z), fun x y z h1 h2 h3 => ?_⟩
    have e1 := hc₁ x y z h1.1 h2.1 h3.1
    have e2 := hc₂ x y z h1.2 h2.2 h3.2
    linear_combination e1 + e2
  · intro z hz
    obtain ⟨W₁, hW₁o, hzW₁, hW₁⟩ := h₁.2.1 z (fun h => hz (Or.inl h))
    obtain ⟨W₂, hW₂o, hzW₂, hW₂⟩ := h₂.2.1 z (fun h => hz (Or.inr h))
    exact ⟨W₁ ∩ W₂, hW₁o.inter hW₂o, ⟨hzW₁, hzW₂⟩, fun x hx y hy => by dsimp only; rw [hW₁ x hx.1 y hy.1, hW₂ x hx.2 y hy.2, add_zero]⟩
  · intro z hz
    rcases hz with hz₁ | hz₂
    · have hz₂ : z ∉ M₂ := Set.disjoint_left.mp hdisj hz₁
      obtain ⟨W₁, A₁, B₁, hW₁o, hzW₁, hW₁s, hAB₁, hA₁o, hB₁o, hAB₁_near, f₁, hf₁ω, hf₁A, hf₁B, hf₁AB⟩ := h₁.2.2 z hz₁
      obtain ⟨W₂, hW₂o, hzW₂, hW₂⟩ := h₂.2.1 z hz₂
      let W := W₁ ∩ W₂ ∩ M₂ᶜ
      have hWo : IsOpen W := (hW₁o.inter hW₂o).inter hM₂.isOpen_compl
      refine ⟨W, A₁ ∩ W, B₁ ∩ W, hWo, ⟨⟨hzW₁, hzW₂⟩, hz₂⟩, ?_, hAB₁.mono inter_subset_left inter_subset_left,
        hA₁o.inter hWo, hB₁o.inter hWo, fun U hUo hzU => ?_,
        f₁, fun x hx y hy => by dsimp only; rw [hf₁ω x hx.1.1 y hy.1.1, hW₂ x hx.1.2 y hy.1.2, add_zero],
        fun x hx y hy => hf₁A x hx.1 y hy.1, fun x hx y hy => hf₁B x hx.1 y hy.1, fun x hx y hy => hf₁AB x hx.1 y hy.1⟩
      · ext x; constructor
        · rintro ⟨hxW, hxM⟩
          have hxAB : x ∈ A₁ ∪ B₁ := hW₁s ▸ ⟨hxW.1.1, fun h => hxM (Or.inl h)⟩
          exact hxAB.elim (fun h => Or.inl ⟨h, hxW⟩) (fun h => Or.inr ⟨h, hxW⟩)
        · rintro (⟨hxA, hxW⟩ | ⟨hxB, hxW⟩)
          · exact ⟨hxW, fun h => h.elim (show x ∈ W₁ \ M₁ from hW₁s.symm ▸ Or.inl hxA).2 hxW.2⟩
          · exact ⟨hxW, fun h => h.elim (show x ∈ W₁ \ M₁ from hW₁s.symm ▸ Or.inr hxB).2 hxW.2⟩
      · obtain ⟨⟨a, ⟨haU, haW⟩, haA⟩, ⟨b, ⟨hbU, hbW⟩, hbB⟩⟩ := hAB₁_near (U ∩ W) (hUo.inter hWo) ⟨hzU, ⟨⟨hzW₁, hzW₂⟩, hz₂⟩⟩
        exact ⟨⟨a, haU, haA, haW⟩, ⟨b, hbU, hbB, hbW⟩⟩
    · have hz₁ : z ∉ M₁ := Set.disjoint_right.mp hdisj hz₂
      obtain ⟨W₂, A₂, B₂, hW₂o, hzW₂, hW₂s, hAB₂, hA₂o, hB₂o, hAB₂_near, f₂, hf₂ω, hf₂A, hf₂B, hf₂AB⟩ := h₂.2.2 z hz₂
      obtain ⟨W₁, hW₁o, hzW₁, hW₁⟩ := h₁.2.1 z hz₁
      let W := W₁ ∩ W₂ ∩ M₁ᶜ
      have hWo : IsOpen W := (hW₁o.inter hW₂o).inter hM₁.isOpen_compl
      refine ⟨W, A₂ ∩ W, B₂ ∩ W, hWo, ⟨⟨hzW₁, hzW₂⟩, hz₁⟩, ?_, hAB₂.mono inter_subset_left inter_subset_left,
        hA₂o.inter hWo, hB₂o.inter hWo, fun U hUo hzU => ?_,
        f₂, fun x hx y hy => by dsimp only; rw [hW₁ x hx.1.1 y hy.1.1, hf₂ω x hx.1.2 y hy.1.2, zero_add],
        fun x hx y hy => hf₂A x hx.1 y hy.1, fun x hx y hy => hf₂B x hx.1 y hy.1, fun x hx y hy => hf₂AB x hx.1 y hy.1⟩
      · ext x; constructor
        · rintro ⟨hxW, hxM⟩
          have hxAB : x ∈ A₂ ∪ B₂ := hW₂s ▸ ⟨hxW.1.2, fun h => hxM (Or.inr h)⟩
          exact hxAB.elim (fun h => Or.inl ⟨h, hxW⟩) (fun h => Or.inr ⟨h, hxW⟩)
        · rintro (⟨hxA, hxW⟩ | ⟨hxB, hxW⟩)
          · exact ⟨hxW, fun h => h.elim hxW.2 (show x ∈ W₂ \ M₂ from hW₂s.symm ▸ Or.inl hxA).2⟩
          · exact ⟨hxW, fun h => h.elim hxW.2 (show x ∈ W₂ \ M₂ from hW₂s.symm ▸ Or.inr hxB).2⟩
      · obtain ⟨⟨a, ⟨haU, haW⟩, haA⟩, ⟨b, ⟨hbU, hbW⟩, hbB⟩⟩ := hAB₂_near (U ∩ W) (hUo.inter hWo) ⟨hzU, ⟨⟨hzW₁, hzW₂⟩, hz₁⟩⟩
        exact ⟨⟨a, haU, haA, haW⟩, ⟨b, hbU, hbB, hbW⟩⟩

/-- Helper: for any cutting data `(Y, ψ, X, X', V_X, V_X')` of a proper `I`-arc `F`,
`cutCocycle ψ V_X V_X' X` is a crossing cocycle and every `z ∈ F` has local two sides. -/
private theorem cutCocycle_isCrossingCocycle {Y : Type u} [TopologicalSpace Y] [T2Space Y]
    (hS : IsSurface S) {F : Set S} {s t : S} (hl : IsLineWithEnds F s t)
    {ψ : Y → S} {X X' V_X V_X' : Set Y}
    (hY_s : IsSurface Y) (hψ : IsCutting ψ F) (hP : LiftPair ψ F s t X X')
    (hVXo : IsOpen V_X) (hVX'o : IsOpen V_X') (hXV : X ⊆ V_X) (hX'V' : X' ⊆ V_X')
    (hdisj_cl : Disjoint (closure V_X) (closure V_X')) :
    IsCrossingCocycle F (cutCocycle ψ V_X V_X' X) ∧ ∀ z ∈ F, HasLocalTwoSides F z := by
  classical
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have : CompactSpace Y := hY_s.1
  have hF : IsClosed F := hl.isCompact.isClosed
  have hdisj_V : Disjoint V_X V_X' := hdisj_cl.mono subset_closure subset_closure
  obtain ⟨_, _, _, _, l1, l2, hdX, hun, -⟩ := id hP
  have hleft : ∀ {y}, y ∈ X → ψ y ∈ F := fun {y} h => (hun ▸ Or.inl h : y ∈ ψ ⁻¹' F)
  have hright : ∀ {y}, y ∈ X' → ψ y ∈ F := fun {y} h => (hun ▸ Or.inr h : y ∈ ψ ⁻¹' F)
  have hW_open : IsOpen (cutNbhd ψ V_X V_X') := isOpen_cutNbhd hψ hVXo hVX'o
  have hF_sub : F ⊆ cutNbhd ψ V_X V_X' := subset_cutNbhd hun hXV hX'V'
  have hcl_Y : IsClosedMap ψ := hψ.1.isClosedMap
  let A : Set S := ψ '' (V_X \ X) ∩ cutNbhd ψ V_X V_X'
  let B : Set S := ψ '' (V_X' \ X') ∩ cutNbhd ψ V_X V_X'
  have hopen_img : ∀ {O : Set Y}, IsOpen O → Disjoint O (ψ ⁻¹' F) → IsOpen (ψ '' O) := by
    intro O hOo hOdis
    have hclO : IsClosed (ψ '' Oᶜ) := hcl_Y _ hOo.isClosed_compl
    have heq : (ψ '' O)ᶜ = ψ '' Oᶜ := by
      ext x; constructor
      · intro hx; obtain ⟨y, rfl⟩ := hψ.2.1 x
        exact ⟨y, fun hyO => hx ⟨y, hyO, rfl⟩, rfl⟩
      · rintro ⟨y, hyOc, rfl⟩ ⟨w, hwO, hwe⟩
        have hwF : ψ w ∉ F := Set.disjoint_left.mp hOdis hwO
        have hyF : ψ y ∉ F := by rwa [← hwe]
        exact hyOc ((hψ.2.2.1 hwF hyF hwe) ▸ hwO)
    rw [← isClosed_compl_iff, heq]; exact hclO
  have hVX_disj : Disjoint (V_X \ X) (ψ ⁻¹' F) := by
    rw [Set.disjoint_left]; intro y hy hyF
    rcases (hun.symm ▸ hyF : y ∈ X ∪ X') with h | h
    · exact hy.2 h
    · exact Set.disjoint_left.mp hdisj_V hy.1 (hX'V' h)
  have hVX'_disj : Disjoint (V_X' \ X') (ψ ⁻¹' F) := by
    rw [Set.disjoint_left]; intro y hy hyF
    rcases (hun.symm ▸ hyF : y ∈ X ∪ X') with h | h
    · exact Set.disjoint_left.mp hdisj_V (hXV h) hy.1
    · exact hy.2 h
  have hXc : IsClosed X := l1.isCompact.isClosed
  have hX'c : IsClosed X' := l2.isCompact.isClosed
  have hAo : IsOpen A := (hopen_img (hVXo.sdiff hXc) hVX_disj).inter hW_open
  have hBo : IsOpen B := (hopen_img (hVX'o.sdiff hX'c) hVX'_disj).inter hW_open
  have hAB_disj : Disjoint A B := by
    rw [Set.disjoint_left]; rintro x ⟨⟨y₁, hy₁, rfl⟩, -⟩ ⟨⟨y₂, hy₂, hye⟩, -⟩
    have h1 : ψ y₁ ∉ F := Set.disjoint_left.mp hVX_disj hy₁
    have h2 : ψ y₂ ∉ F := Set.disjoint_left.mp hVX'_disj hy₂
    have hy : y₂ = y₁ := hψ.2.2.1 h2 h1 hye
    exact Set.disjoint_left.mp hdisj_V hy₁.1 (hy ▸ hy₂.1)
  have hW_split : cutNbhd ψ V_X V_X' \ F = A ∪ B := by
    ext x; constructor
    · rintro ⟨hxW, hxF⟩
      obtain ⟨y, rfl⟩ := hψ.2.1 x
      have hy : y ∈ V_X ∪ V_X' := preimage_cutNbhd_subset hxW
      rcases hy with hyV | hyV'
      · exact Or.inl ⟨⟨y, ⟨hyV, fun hyX => hxF (hleft hyX)⟩, rfl⟩, hxW⟩
      · exact Or.inr ⟨⟨y, ⟨hyV', fun hyX' => hxF (hright hyX')⟩, rfl⟩, hxW⟩
    · rintro (⟨⟨y, hy, rfl⟩, hxW⟩ | ⟨⟨y, hy, rfl⟩, hxW⟩)
      · exact ⟨hxW, Set.disjoint_left.mp hVX_disj hy⟩
      · exact ⟨hxW, Set.disjoint_left.mp hVX'_disj hy⟩
  have hAB_near : ∀ z ∈ F, ∀ U : Set S, IsOpen U → z ∈ U → (U ∩ A).Nonempty ∧ (U ∩ B).Nonempty := by
    intro z hz U hUo hzU
    obtain ⟨a, ξ, η, L, -, -, himξ, himη, -, -⟩ := exists_arcLift hP hψ
    obtain ⟨u, hu, rfl⟩ := (L.img ▸ hz : z ∈ a '' Icc 0 1)
    have hy₁X : ξ u ∈ X := himξ ▸ ⟨u, hu, rfl⟩
    have hy₂X' : η u ∈ X' := himη ▸ ⟨u, hu, rfl⟩
    have hdense := dense_cut_compl hY_s hψ
    have hO1 : IsOpen (V_X ∩ ψ ⁻¹' (U ∩ cutNbhd ψ V_X V_X')) :=
      hVXo.inter ((hUo.inter hW_open).preimage hψ.1)
    have hO2 : IsOpen (V_X' ∩ ψ ⁻¹' (U ∩ cutNbhd ψ V_X V_X')) :=
      hVX'o.inter ((hUo.inter hW_open).preimage hψ.1)
    obtain ⟨w₁, hw₁O, hw₁F⟩ := hdense.inter_open_nonempty _ hO1
      ⟨ξ u, hXV hy₁X, by rw [mem_preimage, L.hξ u hu]; exact ⟨hzU, hF_sub hz⟩⟩
    obtain ⟨w₂, hw₂O, hw₂F⟩ := hdense.inter_open_nonempty _ hO2
      ⟨η u, hX'V' hy₂X', by rw [mem_preimage, L.hη u hu]; exact ⟨hzU, hF_sub hz⟩⟩
    refine ⟨⟨ψ w₁, hw₁O.2.1, ⟨w₁, ⟨hw₁O.1, fun h => hw₁F (hleft h)⟩, rfl⟩, hw₁O.2.2⟩,
            ⟨ψ w₂, hw₂O.2.1, ⟨w₂, ⟨hw₂O.1, fun h => hw₂F (hright h)⟩, rfl⟩, hw₂O.2.2⟩⟩
  have hcross : IsCrossingCocycle F (cutCocycle ψ V_X V_X' X) := by
    refine ⟨isCoc_cutCocycle hψ hF hun hVXo hVX'o hXV hX'V' hdisj_cl, ?_, ?_⟩
    · intro z hz
      obtain ⟨W, hWo, hzW, -, hWz⟩ := cutCocycle_zero_off hψ hF hun hdisj_cl z hz
      exact ⟨W, hWo, hzW, hWz⟩
    · intro z hz
      refine ⟨cutNbhd ψ V_X V_X', A, B, hW_open, hF_sub hz, hW_split, hAB_disj, hAo, hBo, hAB_near z hz,
        cutSide ψ V_X X, fun x hx y hy => ?_, fun x hx y hy => ?_, fun x hx y hy => ?_, fun x hx y hy => ?_⟩
      · unfold cutCocycle; exact ite_eq_left ⟨hx, hy⟩
      · obtain ⟨⟨y₁, hy₁, rfl⟩, -⟩ := hx; obtain ⟨⟨y₂, hy₂, rfl⟩, -⟩ := hy
        rw [cutSide_of_mem_VX hy₁, cutSide_of_mem_VX hy₂]
      · obtain ⟨⟨y₁, hy₁, rfl⟩, -⟩ := hx; obtain ⟨⟨y₂, hy₂, rfl⟩, -⟩ := hy
        rw [cutSide_of_mem_VX' hψ hun hdisj_V hX'V' hy₁.1, cutSide_of_mem_VX' hψ hun hdisj_V hX'V' hy₂.1]
      · obtain ⟨⟨y₁, hy₁, rfl⟩, -⟩ := hx; obtain ⟨⟨y₂, hy₂, rfl⟩, -⟩ := hy
        rw [cutSide_of_mem_VX hy₁, cutSide_of_mem_VX' hψ hun hdisj_V hX'V' hy₂.1]
        decide
  have htwo : ∀ z ∈ F, HasLocalTwoSides F z := by
    intro z hz V hVo hzV
    obtain ⟨a, ξ, η, L, -, -, himξ, himη, -, -⟩ := exists_arcLift hP hψ
    obtain ⟨u, hu, rfl⟩ := (L.img ▸ hz : z ∈ a '' Icc 0 1)
    set y₁ := ξ u; set y₂ := η u
    have hy₁X : y₁ ∈ X := himξ ▸ ⟨u, hu, rfl⟩
    have hy₂X' : y₂ ∈ X' := himη ▸ ⟨u, hu, rfl⟩
    have hy₁ψ : ψ y₁ = a u := L.hξ u hu
    have hy₂ψ : ψ y₂ = a u := L.hη u hu
    have hhalf_conn : ∀ (y : Y) (W : Set Y), IsOpen W → y ∈ W → y ∈ bd Y →
        ∃ O : Set Y, IsOpen O ∧ y ∈ O ∧ O ⊆ W ∧
          IsPreconnected (O \ bd Y) ∧ (O \ bd Y).Nonempty ∧ O ⊆ closure (O \ bd Y) := by
      intro y W hWo hyW hybd
      obtain ⟨c, hyc⟩ := exists_surfChart (hY_s.2.2 y)
      have hre0 : (c.j y).re = 0 := (c.mem_bd_iff hyc).mp hybd
      have hjyO : c.j y ∈ c.O := (c.hm hyc).1
      have hW_sub_open : IsOpen ((fun p : (c.O ∩ halfPlane : Set ℂ) => c.k p.1) ⁻¹' (c.U ∩ W)) :=
        (c.hU.inter hWo).preimage (continuousOn_iff_continuous_domRestrict.mp c.hk)
      have hp0 : (⟨c.j y, c.hm hyc⟩ : (c.O ∩ halfPlane : Set ℂ)) ∈
          (fun p : (c.O ∩ halfPlane : Set ℂ) => c.k p.1) ⁻¹' (c.U ∩ W) := by
        show c.k (c.j y) ∈ c.U ∩ W; rw [c.hl hyc]; exact ⟨hyc, hyW⟩
      rw [Metric.isOpen_iff] at hW_sub_open
      obtain ⟨r₁, hr₁, hr₁sub⟩ := hW_sub_open _ hp0
      obtain ⟨r₂, hr₂, hr₂sub⟩ := Metric.isOpen_iff.mp c.hO _ hjyO
      set r := min r₁ r₂
      have hr : 0 < r := lt_min hr₁ hr₂
      let O : Set Y := c.U ∩ c.j ⁻¹' ball (c.j y) r
      have hOo : IsOpen O := c.hj.isOpen_inter_preimage c.hU isOpen_ball
      have hyO : y ∈ O := ⟨hyc, mem_ball_self hr⟩
      have hOW : O ⊆ W := fun w hw => by
        have hw1 : c.j w ∈ c.O ∩ halfPlane := c.hm hw.1
        have hdist : dist (⟨c.j w, hw1⟩ : (c.O ∩ halfPlane : Set ℂ)) ⟨c.j y, c.hm hyc⟩ < r₁ :=
          lt_of_lt_of_le (mem_ball.mp hw.2) (min_le_left _ _)
        have hmem := hr₁sub hdist
        show w ∈ W
        rw [← c.hl hw.1]; exact hmem.2
      have hO_eq : O \ bd Y = c.k '' (ball (c.j y) r ∩ {w : ℂ | 0 < w.re}) := by
        ext w; constructor
        · rintro ⟨⟨hwU, hwb⟩, hwbd⟩
          refine ⟨c.j w, ⟨hwb, (c.not_mem_bd_iff hwU).mp hwbd⟩, c.hl hwU⟩
        · rintro ⟨z, ⟨hzb, hzpos⟩, rfl⟩
          have hzO : z ∈ c.O := hr₂sub (mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hzb) (min_le_right _ _)))
          have hzh : z ∈ c.O ∩ halfPlane := ⟨hzO, show z ∈ halfPlane from le_of_lt (show 0 < z.re from hzpos)⟩
          have hkzU : c.k z ∈ c.U := c.hk' hzh
          refine ⟨⟨hkzU, by rw [mem_preimage, c.hr hzh]; exact hzb⟩, ?_⟩
          rw [c.not_mem_bd_iff hkzU, c.hr hzh]; exact hzpos
      have hconv : Convex ℝ (ball (c.j y) r ∩ {w : ℂ | 0 < w.re}) :=
        (convex_ball _ _).inter (convex_halfSpace_re_gt 0)
      have hpc : IsPreconnected (O \ bd Y) := by
        rw [hO_eq]
        exact hconv.isPreconnected.image c.k (c.hk.mono fun z hz =>
          ⟨hr₂sub (mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hz.1) (min_le_right _ _))),
            show z ∈ halfPlane from le_of_lt (show 0 < z.re from hz.2)⟩)
      have hne_pt : c.j y + ((r / 2 : ℝ) : ℂ) ∈ ball (c.j y) r ∩ {w : ℂ | 0 < w.re} := by
        refine ⟨?_, ?_⟩
        · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr)]; linarith
        · simp [hre0, half_pos hr]
      have hne' : (O \ bd Y).Nonempty := by rw [hO_eq]; exact ⟨c.k (c.j y + ((r / 2 : ℝ) : ℂ)), _, hne_pt, rfl⟩
      have hcl : O ⊆ closure (O \ bd Y) := fun w hw => by
        rw [_root_.mem_closure_iff]
        intro G hGo hwG
        have hw1 : c.j w ∈ c.O ∩ halfPlane := c.hm hw.1
        have hopenG : IsOpen ((fun p : (c.O ∩ halfPlane : Set ℂ) => c.k p.1) ⁻¹' G) :=
          hGo.preimage (continuousOn_iff_continuous_domRestrict.mp c.hk)
        have hpw : (⟨c.j w, hw1⟩ : (c.O ∩ halfPlane : Set ℂ)) ∈
            (fun p : (c.O ∩ halfPlane : Set ℂ) => c.k p.1) ⁻¹' G := by
          show c.k (c.j w) ∈ G; rwa [c.hl hw.1]
        obtain ⟨δ₁, hδ₁, hδ₁sub⟩ := Metric.isOpen_iff.mp hopenG _ hpw
        obtain ⟨δ₂, hδ₂, hδ₂sub⟩ := Metric.isOpen_iff.mp isOpen_ball _ hw.2
        set ε := min δ₁ δ₂ / 2
        have hε : 0 < ε := half_pos (lt_min hδ₁ hδ₂)
        let z' : ℂ := c.j w + (ε : ℂ)
        have hz'b : z' ∈ ball (c.j y) r := hδ₂sub (by
          rw [mem_ball, dist_eq_norm, show z' - c.j w = (ε : ℂ) by simp [z'],
              Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
          exact (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)).trans_lt (half_lt_self hδ₂))
        have hwre : 0 ≤ (c.j w).re := hw1.2
        have hz'pos : 0 < z'.re := by simp only [z', add_re, ofReal_re]; linarith
        have hz'O : z' ∈ c.O := hr₂sub (mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hz'b) (min_le_right _ _)))
        have hz'h : z' ∈ c.O ∩ halfPlane := ⟨hz'O, show z' ∈ halfPlane from le_of_lt hz'pos⟩
        have hz'G : c.k z' ∈ G := hδ₁sub (a := ⟨z', hz'h⟩) (by
          rw [mem_ball]; show dist z' (c.j w) < δ₁
          rw [dist_eq_norm, show z' - c.j w = (ε : ℂ) by simp [z'],
              Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
          exact (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)).trans_lt (half_lt_self hδ₁))
        exact ⟨c.k z', hz'G, by rw [hO_eq]; exact ⟨z', ⟨hz'b, hz'pos⟩, rfl⟩⟩
      exact ⟨O, hOo, hyO, hOW, hpc, hne', hcl⟩
    have hy₁_bd : y₁ ∈ bd Y := hψ.2.2.2.2 (hleft hy₁X)
    have hy₂_bd : y₂ ∈ bd Y := hψ.2.2.2.2 (hright hy₂X')
    have hy₁_in : y₁ ∈ V_X ∩ ψ ⁻¹' V := ⟨hXV hy₁X, show ψ y₁ ∈ V by rw [hy₁ψ]; exact hzV⟩
    have hy₂_in : y₂ ∈ V_X' ∩ ψ ⁻¹' V := ⟨hX'V' hy₂X', show ψ y₂ ∈ V by rw [hy₂ψ]; exact hzV⟩
    obtain ⟨O₁, hO₁o, hy₁O₁, hO₁sub, hO₁pc, hO₁ne, hO₁cl⟩ :=
      hhalf_conn y₁ (V_X ∩ ψ ⁻¹' V) (hVXo.inter (hVo.preimage hψ.1)) hy₁_in hy₁_bd
    obtain ⟨O₂, hO₂o, hy₂O₂, hO₂sub, hO₂pc, hO₂ne, hO₂cl⟩ :=
      hhalf_conn y₂ (V_X' ∩ ψ ⁻¹' V) (hVX'o.inter (hVo.preimage hψ.1)) hy₂_in hy₂_bd
    have hO₁_disj : Disjoint (O₁ \ X) (ψ ⁻¹' F) :=
      hVX_disj.mono (show O₁ \ X ⊆ V_X \ X from fun w hw => ⟨(hO₁sub hw.1).1, hw.2⟩) Subset.rfl
    have hO₂_disj : Disjoint (O₂ \ X') (ψ ⁻¹' F) :=
      hVX'_disj.mono (show O₂ \ X' ⊆ V_X' \ X' from fun w hw => ⟨(hO₂sub hw.1).1, hw.2⟩) Subset.rfl
    have hO₁_pc : IsPreconnected (O₁ \ X) :=
      hO₁pc.subset_closure (fun w hw => ⟨hw.1, fun hwX => hw.2 (hψ.2.2.2.2 (hleft hwX))⟩)
        (fun w hw => hO₁cl hw.1)
    have hO₂_pc : IsPreconnected (O₂ \ X') :=
      hO₂pc.subset_closure (fun w hw => ⟨hw.1, fun hwX' => hw.2 (hψ.2.2.2.2 (hright hwX'))⟩)
        (fun w hw => hO₂cl hw.1)
    have hO₁_ne : (O₁ \ X).Nonempty := hO₁ne.mono fun w hw => ⟨hw.1, fun hwX => hw.2 (hψ.2.2.2.2 (hleft hwX))⟩
    have hO₂_ne : (O₂ \ X').Nonempty := hO₂ne.mono fun w hw => ⟨hw.1, fun hwX' => hw.2 (hψ.2.2.2.2 (hright hwX'))⟩
    let U : Set S := cutNbhd ψ O₁ O₂ ∩ V
    have hUo : IsOpen U := (isOpen_cutNbhd hψ hO₁o hO₂o).inter hVo
    have hzU : a u ∈ U := by
      refine ⟨?_, hzV⟩
      rintro ⟨w, hwc, hwe⟩
      have hwF : w ∈ ψ ⁻¹' F := by rw [mem_preimage, hwe]; exact L.img ▸ ⟨u, hu, rfl⟩
      rcases (hun.symm ▸ hwF : w ∈ X ∪ X') with hwX | hwX'
      · have hwu : w = y₁ := by
          by_contra hne'
          rcases L.fib w y₁ (hwe.trans hy₁ψ.symm) hne' with ⟨v, hv, ⟨rfl, hy1⟩ | ⟨hy1, rfl⟩⟩
          · exact Set.disjoint_left.mp hdX hy₁X (hy1 ▸ (himη ▸ ⟨v, hv, rfl⟩))
          · exact Set.disjoint_left.mp hdX hwX (himη ▸ ⟨v, hv, rfl⟩)
        exact hwc (Or.inl (hwu ▸ hy₁O₁))
      · have hwu : w = y₂ := by
          by_contra hne'
          rcases L.fib w y₂ (hwe.trans hy₂ψ.symm) hne' with ⟨v, hv, ⟨rfl, hy2⟩ | ⟨hy2, rfl⟩⟩
          · exact Set.disjoint_left.mp hdX (himξ ▸ ⟨v, hv, rfl⟩) hwX'
          · exact Set.disjoint_left.mp hdX (hy2 ▸ (himξ ▸ ⟨v, hv, rfl⟩)) hy₂X'
        exact hwc (Or.inr (hwu ▸ hy₂O₂))
    refine ⟨U, ψ '' (O₁ \ X), ψ '' (O₂ \ X'), hUo, hzU, inter_subset_right, ?_, ?_,
      hopen_img (hO₁o.sdiff hXc) hO₁_disj, hopen_img (hO₂o.sdiff hX'c) hO₂_disj,
      hO₁_pc.image ψ hψ.1.continuousOn, hO₂_pc.image ψ hψ.1.continuousOn, hO₁_ne.image ψ, hO₂_ne.image ψ⟩
    · ext x; constructor
      · rintro ⟨⟨hxC, -⟩, hxF⟩
        obtain ⟨w, rfl⟩ := hψ.2.1 x
        rcases preimage_cutNbhd_subset hxC with hw1 | hw2
        · exact Or.inl ⟨w, ⟨hw1, fun h => hxF (hleft h)⟩, rfl⟩
        · exact Or.inr ⟨w, ⟨hw2, fun h => hxF (hright h)⟩, rfl⟩
      · rintro (⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩)
        · have hwF : ψ w ∉ F := Set.disjoint_left.mp hO₁_disj hw
          refine ⟨⟨?_, (hO₁sub hw.1).2⟩, hwF⟩
          rintro ⟨w', hw'c, hwe⟩
          have hw'F : ψ w' ∉ F := by rwa [hwe]
          exact hw'c (Or.inl ((hψ.2.2.1 hw'F hwF hwe) ▸ hw.1))
        · have hwF : ψ w ∉ F := Set.disjoint_left.mp hO₂_disj hw
          refine ⟨⟨?_, (hO₂sub hw.1).2⟩, hwF⟩
          rintro ⟨w', hw'c, hwe⟩
          have hw'F : ψ w' ∉ F := by rwa [hwe]
          exact hw'c (Or.inr ((hψ.2.2.1 hw'F hwF hwe) ▸ hw.1))
    · rw [Set.disjoint_left]; rintro x ⟨w₁, hw₁, rfl⟩ ⟨w₂, hw₂, hwe⟩
      have h1 : ψ w₁ ∉ F := Set.disjoint_left.mp hO₁_disj hw₁
      have h2 : ψ w₂ ∉ F := Set.disjoint_left.mp hO₂_disj hw₂
      exact Set.disjoint_left.mp hdisj_V (hO₁sub hw₁.1).1 ((hψ.2.2.1 h2 h1 hwe) ▸ (hO₂sub hw₂.1).1)
  exact ⟨hcross, htwo⟩

/-- Every point of a proper `I`-arc `F` in a surface `S` has local two sides, and `arcCocycle F`
is a crossing cocycle for `F`. -/
theorem arcCocycle_isCrossingCocycle [ConnectedSpace S] (hS : IsSurface S) {F : Set S} {s t : S} (hne : s ≠ t)
    (hb : F ∩ bd S = {s, t}) (hl : IsLineWithEnds F s t) :
    IsCrossingCocycle F (arcCocycle hS hne hb hl) ∧ ∀ z ∈ F, HasLocalTwoSides F z := by
  unfold arcCocycle
  set d := exists_cut_cocycle_data hS hne hb hl
  let _ := d.choose_spec.choose
  let _ := d.choose_spec.choose_spec.choose
  obtain ⟨hY_s, hψ, hP, hVXo, hVX'o, hXV, hX'V', hdisj_cl⟩ :=
    d.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
  exact cutCocycle_isCrossingCocycle hS hl hY_s hψ hP hVXo hVX'o hXV hX'V' hdisj_cl

end CrossingCocycle

/-! ### Section 4: Crossing cocycle for an interior `O`-arc (1-sided or 2-sided) -/

section OArcCocycle

variable {S : Type} [TopologicalSpace S]

/-- Helper: in a strip chart over an open subset `V ⊆ j ⁻¹' (Ks '' R)`, every open neighborhood `U`
of `z ∈ V` (with `z_coord z` real) contains points of `V` with positive and negative imaginary coordinate. -/
private theorem strip_near_sides {T : Type} [TopologicalSpace T] {j : S → T} {K : Set T}
    (hj : IsClosedEmbedding j) (hK : IsClosed K) (hcov : range j ∪ K = univ)
    {Os R Rbig : Set ℂ} {Ks : ℂ → T} (hKs : StripChart Os Ks)
    (hRo : IsOpen R) (hRsub : closure R ⊆ Rbig) (hRbigOs : Rbig ⊆ Os)
    {zc : S → ℂ} (hzc : ∀ {w : ℂ} {x : S}, w ∈ Rbig → Ks w = j x → zc x = w)
    {V : Set S} (hVo : IsOpen V) {z : S} (hzV : z ∈ V) (hzK : j z ∉ K)
    (hzR : zc z ∈ R) (hze : Ks (zc z) = j z) (hz0 : (zc z).im = 0)
    {U : Set S} (hUo : IsOpen U) (hzU : z ∈ U) :
    (U ∩ (V ∩ {x : S | 0 < (zc x).im})).Nonempty ∧
    (U ∩ (V ∩ {x : S | (zc x).im < 0})).Nonempty := by
  have hU' : IsOpen (j '' (U ∩ V) ∩ Kᶜ) := by
    obtain ⟨W, hWo, hWU⟩ := hj.isInducing.isOpen_iff.mp (hUo.inter hVo)
    have heq : j '' (U ∩ V) ∩ Kᶜ = W ∩ Kᶜ := by
      ext y; constructor
      · rintro ⟨⟨x, hxU, rfl⟩, hyK⟩; exact ⟨(Set.ext_iff.mp hWU x).mpr hxU, hyK⟩
      · rintro ⟨hyW, hyK⟩
        obtain ⟨x, rfl⟩ := (hcov ▸ mem_univ y).resolve_right hyK
        exact ⟨⟨x, (Set.ext_iff.mp hWU x).mp hyW, rfl⟩, hyK⟩
    rw [heq]; exact hWo.inter hK.isOpen_compl
  have hpre : IsOpen (R ∩ Ks ⁻¹' (j '' (U ∩ V) ∩ Kᶜ)) :=
    (hKs.hc.mono (subset_closure.trans (hRsub.trans hRbigOs))).isOpen_inter_preimage hRo hU'
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hpre (zc z)
    ⟨hzR, by rw [mem_preimage, hze]; exact ⟨⟨z, ⟨hzU, hzV⟩, rfl⟩, hzK⟩⟩
  have hmk : ∀ σ : ℝ, σ = 1 ∨ σ = -1 → ∃ x ∈ U ∩ V, zc x = zc z + ((σ * (r / 2) : ℝ) : ℂ) * I := by
    intro σ hσ
    let w' := zc z + ((σ * (r / 2) : ℝ) : ℂ) * I
    have hw'b : w' ∈ ball (zc z) r := by
      have hsub : w' - zc z = ((σ * (r / 2) : ℝ) : ℂ) * I := add_sub_cancel_left _ _
      rw [mem_ball, dist_eq_norm, hsub, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      rcases hσ with rfl | rfl
      · rw [one_mul, abs_of_pos (half_pos hr)]; exact half_lt_self hr
      · rw [neg_one_mul, abs_neg, abs_of_pos (half_pos hr)]; exact half_lt_self hr
    obtain ⟨hw'R, ⟨x, hxU, hxe⟩, -⟩ := hrsub hw'b
    exact ⟨x, hxU, hzc (hRsub (subset_closure hw'R)) hxe.symm⟩
  obtain ⟨x₁, ⟨hx₁U, hx₁V⟩, hx₁z⟩ := hmk 1 (Or.inl rfl)
  obtain ⟨x₂, ⟨hx₂U, hx₂V⟩, hx₂z⟩ := hmk (-1) (Or.inr rfl)
  have hx₁im : 0 < (zc x₁).im := by
    rw [hx₁z, add_im, hz0, zero_add, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero, one_mul]
    exact half_pos hr
  have hx₂im : (zc x₂).im < 0 := by
    rw [hx₂z, add_im, hz0, zero_add, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero, neg_one_mul]
    exact neg_lt_zero.mpr (half_pos hr)
  exact ⟨⟨x₁, hx₁U, hx₁V, hx₁im⟩, ⟨x₂, hx₂U, hx₂V, hx₂im⟩⟩

/-- Every interior `O`-arc `O ⊆ (bd S)ᶜ` in a surface `S` (whether 1-sided or 2-sided) admits a
`ZMod 2` crossing cocycle and has local two sides at every point. -/
theorem exists_oArcCocycle (hS : IsSurface S) {O : Set S} (hO : IsOArc O) (hO_int : O ⊆ (bd S)ᶜ) :
    (∃ ω : S → S → ZMod 2, IsCrossingCocycle O ω) ∧ ∀ z ∈ O, HasLocalTwoSides O z := by
  classical
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have hOc : IsClosed O := hO.isCompact.isClosed
  obtain ⟨φ⟩ := id hO
  obtain ⟨T, _, j, K, hT, hj, hK, hcov, hinter, -⟩ := exists_capAll S hS
  have : T2Space T := hT.2.1
  have hji := hj.injective
  have hO_notK : ∀ x ∈ O, j x ∉ K := fun x hx hK' =>
    hO_int hx (by
      have h1 : j x ∈ range j ∩ K := ⟨⟨x, rfl⟩, hK'⟩
      rw [hinter] at h1; obtain ⟨y, hy, he⟩ := h1; exact hji he ▸ hy)
  -- Cover `O` by two overlapping `I`-arcs `a₁` (`[-1/8, 5/8]`) and `a₂` (`[3/8, 9/8]`):
  let a₁ : unitInterval → T := fun u => j (φ (ee (lin (-1 / 8) (5 / 8) u.1))).1
  let a₂ : unitInterval → T := fun u => j (φ (ee (lin (3 / 8) (9 / 8) u.1))).1
  have ha_arc : ∀ (p q : ℝ), p < q → q - p < 1 →
      IsArcMap (fun u : unitInterval => j (φ (ee (lin p q u.1))).1) := by
    intro p q hpq hsp
    refine ⟨hj.continuous.comp (continuous_subtype_val.comp (φ.continuous.comp
      (continuous_ee.comp ((continuousOn_lin p q).comp_continuous continuous_subtype_val fun u => u.2)))),
      fun u v he => ?_⟩
    have hee := φ.injective (Subtype.ext (hji he))
    obtain ⟨k, hk⟩ := ee_eq_iff.mp hee
    have hlu : lin p q u.1 ∈ Icc p q := ⟨by simp [lin]; nlinarith [u.2.1, hpq], by simp [lin]; nlinarith [u.2.2, hpq]⟩
    have hlv : lin p q v.1 ∈ Icc p q := ⟨by simp [lin]; nlinarith [v.2.1, hpq], by simp [lin]; nlinarith [v.2.2, hpq]⟩
    have hklt : |(k : ℝ)| < 1 := by rw [abs_lt]; exact ⟨by linarith [hlu.1, hlv.2], by linarith [hlu.2, hlv.1]⟩
    have hk0 : k = 0 := by have := abs_lt.mp (show |k| < 1 by exact_mod_cast hklt); omega
    subst hk0; simp only [Int.cast_zero, add_zero, lin] at hk
    apply Subtype.ext; nlinarith [hpq]
  have ha₁ : IsArcMap a₁ := ha_arc (-1 / 8) (5 / 8) (by norm_num) (by norm_num)
  have ha₂ : IsArcMap a₂ := ha_arc (3 / 8) (9 / 8) (by norm_num) (by norm_num)
  obtain ⟨O₁, K₁, θ₁, hK₁, hθ₁c, hθ₁m, hθ₁⟩ := GM07.exists_stripChart_of_arc hT ha₁
  obtain ⟨O₂, K₂, θ₂, hK₂, hθ₂c, hθ₂m, hθ₂⟩ := GM07.exists_stripChart_of_arc hT ha₂
  -- Helper: shrink a strip chart around `a` to a closed rectangle `[θ(1/24), θ(23/24)] × [-ε, ε]`
  -- whose image misses `K` and meets `j '' O` ONLY along `Im = 0`:
  have hrect_of : ∀ (p q : ℝ) (hpq : p < q) (hsp : q - p < 1)
      (Os : Set ℂ) (Ks : ℂ → T) (θ : unitInterval → ℝ),
      StripChart Os Ks → Continuous θ → StrictMono θ →
      (∀ t : unitInterval, (θ t : ℂ) ∈ Os ∧ Ks (θ t) = j (φ (ee (lin p q t.1))).1) →
      ∃ ε : ℝ, 0 < ε ∧
        (Icc (θ ⟨1 / 24, by norm_num, by norm_num⟩) (θ ⟨23 / 24, by norm_num, by norm_num⟩) ×ℂ Icc (-ε) ε) ⊆ Os ∧
        (Ks '' (Icc (θ ⟨1 / 24, by norm_num, by norm_num⟩) (θ ⟨23 / 24, by norm_num, by norm_num⟩) ×ℂ Icc (-ε) ε) ⊆ Kᶜ) ∧
        (∀ z ∈ Icc (θ ⟨1 / 24, by norm_num, by norm_num⟩) (θ ⟨23 / 24, by norm_num, by norm_num⟩) ×ℂ Icc (-ε) ε,
          Ks z ∈ j '' O ↔ z.im = 0) := by
    intro p q hpq hsp Os Ks θ hKs hθc hθm hθ
    set α : ℝ := θ ⟨1 / 24, by norm_num, by norm_num⟩
    set β : ℝ := θ ⟨23 / 24, by norm_num, by norm_num⟩
    let O_far : Set T := (fun t : ℝ => j (φ (ee t)).1) '' Icc (lin p q (47 / 48)) (lin p q (1 / 48) + 1)
    have hOfar_c : IsClosed O_far :=
      (isCompact_Icc.image (hj.continuous.comp (continuous_subtype_val.comp (φ.continuous.comp continuous_ee)))).isClosed
    have hseg_in : ∀ x ∈ Icc α β, (x : ℂ) ∈ Os ∧ Ks (x : ℂ) ∈ (K ∪ O_far)ᶜ := by
      intro x hx
      obtain ⟨t, ht⟩ := intermediate_value_univ ⟨1 / 24, by norm_num, by norm_num⟩ ⟨23 / 24, by norm_num, by norm_num⟩ hθc hx
      have ht_lo : (1 / 24 : ℝ) ≤ t.1 := by
        by_contra hlt; push Not at hlt
        exact not_lt.mpr hx.1 (ht ▸ hθm (show t < ⟨1 / 24, by norm_num, by norm_num⟩ from hlt))
      have ht_hi : t.1 ≤ 23 / 24 := by
        by_contra hgt; push Not at hgt
        exact not_lt.mpr hx.2 (ht ▸ hθm (show ⟨23 / 24, by norm_num, by norm_num⟩ < t from hgt))
      rw [← ht]
      refine ⟨(hθ t).1, ?_⟩
      rw [(hθ t).2]; rintro (hK' | ⟨r, hr, hre⟩)
      · exact hO_notK _ (φ _).2 hK'
      · have hee := φ.injective (Subtype.ext (hji hre))
        have hlt1 : lin p q (1 / 48) < lin p q t.1 := by simp only [lin]; nlinarith [hpq, ht_lo]
        have hlt2 : lin p q t.1 < lin p q (47 / 48) := by simp only [lin]; nlinarith [hpq, ht_hi]
        have hlt3 : lin p q (1 / 48) + 1 < lin p q t.1 + 1 := by linarith
        exact ee_ne (by linarith [hr.1]) (by linarith [hr.2]) hee.symm
    let Ω : Set ℂ := Os ∩ Ks ⁻¹' (K ∪ O_far)ᶜ
    have hΩo : IsOpen Ω := hKs.hc.isOpen_inter_preimage hKs.isOpen (hK.union hOfar_c).isOpen_compl
    have hseg_sub : (Icc α β ×ℂ ({0} : Set ℝ)) ⊆ Ω := by
      rintro z hz; rw [Complex.mem_reProdIm] at hz
      have hze : z = (z.re : ℂ) := Complex.ext rfl (by simpa using hz.2)
      rw [hze]; exact hseg_in z.re hz.1
    have hseg_cpt : IsCompact (Icc α β ×ℂ ({0} : Set ℝ)) := isCompact_Icc.reProdIm isCompact_singleton
    obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric hseg_cpt (c := fun _ : Unit => Ω)
      (fun _ => hΩo) (fun z hz => mem_iUnion.mpr ⟨(), hseg_sub hz⟩)
    have hRΩ : (Icc α β ×ℂ Icc (-(δ / 2)) (δ / 2)) ⊆ Ω := fun z hz => by
      rw [Complex.mem_reProdIm] at hz
      obtain ⟨_, hsub⟩ := hleb (z.re : ℂ) (Complex.mem_reProdIm.mpr ⟨hz.1, by simp⟩)
      refine hsub ?_
      rw [mem_ball, dist_eq_norm, show z - (z.re : ℂ) = (z.im : ℂ) * I from Complex.ext (by simp) (by simp),
          norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      have : |z.im| ≤ δ / 2 := abs_le.mpr hz.2
      linarith
    refine ⟨δ / 2, half_pos hδ, fun z hz => (hRΩ hz).1, by rintro _ ⟨z, hz, rfl⟩; exact fun hK' => (hRΩ hz).2 (Or.inl hK'), fun z hz => ?_⟩
    rw [Complex.mem_reProdIm] at hz
    constructor
    · intro hKzO
      obtain ⟨x, hxO, hxe⟩ := hKzO
      obtain ⟨r₀, -, hr₀e⟩ := exists_param (φ.symm ⟨x, hxO⟩)
      have hx_eq : x = (φ (ee r₀)).1 := by rw [hr₀e]; simp
      set r := lin p q (1 / 48) + Int.fract (r₀ - lin p q (1 / 48))
      have hree : ee r = ee r₀ := ee_eq_iff.mpr ⟨-⌊r₀ - lin p q (1 / 48)⌋, by simp only [r, Int.cast_neg]; linarith [Int.floor_add_fract (r₀ - lin p q (1 / 48))]⟩
      have hr_lo : lin p q (1 / 48) ≤ r := by simp only [r]; linarith [Int.fract_nonneg (r₀ - lin p q (1 / 48))]
      have hr_hi : r < lin p q (1 / 48) + 1 := by simp only [r]; linarith [Int.fract_lt_one (r₀ - lin p q (1 / 48))]
      have hr_lt : r < lin p q (47 / 48) := by
        by_contra hge; push Not at hge
        exact (hRΩ (Complex.mem_reProdIm.mpr hz)).2 (Or.inr ⟨r, ⟨hge, hr_hi.le⟩, by dsimp only; rw [hree, ← hx_eq, hxe]⟩)
      let t_val : ℝ := (r - p) / (q - p)
      have ht_mem : t_val ∈ Icc (0 : ℝ) 1 := by
        have hp_le : p ≤ r := by have : p < lin p q (1 / 48) := by simp [lin]; nlinarith [hpq]
                                 linarith
        have hq_ge : r ≤ q := by have : lin p q (47 / 48) < q := by simp [lin]; nlinarith [hpq]
                                 linarith
        exact ⟨div_nonneg (by linarith) (by linarith), (div_le_one (by linarith)).mpr (by linarith)⟩
      let t : unitInterval := ⟨t_val, ht_mem⟩
      have hlin_t : lin p q t.1 = r := by simp only [lin, t, t_val]; field_simp [show q - p ≠ 0 by linarith]; ring
      have hKeq : Ks z = Ks (θ t : ℂ) := by rw [(hθ t).2, hlin_t, hree, ← hx_eq, hxe]
      have hz_eq : z = (θ t : ℂ) := hKs.hi (hRΩ (Complex.mem_reProdIm.mpr hz)).1 (hθ t).1 hKeq
      rw [hz_eq]; simp
    · intro him0
      obtain ⟨t, ht⟩ := intermediate_value_univ ⟨1 / 24, by norm_num, by norm_num⟩ ⟨23 / 24, by norm_num, by norm_num⟩ hθc hz.1
      have hze : z = (θ t : ℂ) := Complex.ext (by simp [ht]) (by simp [him0])
      rw [hze, (hθ t).2]; exact ⟨_, (φ _).2, rfl⟩
  obtain ⟨ε₁, hε₁, hR₁Os, hR₁K, hR₁O⟩ := hrect_of (-1 / 8) (5 / 8) (by norm_num) (by norm_num) O₁ K₁ θ₁ hK₁ hθ₁c hθ₁m hθ₁
  obtain ⟨ε₂, hε₂, hR₂Os, hR₂K, hR₂O⟩ := hrect_of (3 / 8) (9 / 8) (by norm_num) (by norm_num) O₂ K₂ θ₂ hK₂ hθ₂c hθ₂m hθ₂
  have hO_cov : ∀ z ∈ O,
      (∃ u ∈ Ioo (1 / 12 : ℝ) (11 / 12), z = (φ (ee (lin (-1 / 8) (5 / 8) u))).1) ∨
      (∃ u ∈ Ioo (1 / 12 : ℝ) (11 / 12), z = (φ (ee (lin (3 / 8) (9 / 8) u))).1) := by
    intro z hz
    obtain ⟨r, hr, hre⟩ := exists_param (φ.symm ⟨z, hz⟩)
    have hze : z = (φ (ee r)).1 := by rw [hre]; simp
    by_cases hhalf : r < 1 / 2
    · refine Or.inl ⟨(r + 1 / 8) / (3 / 4), ⟨by linarith [hr.1], by linarith⟩, ?_⟩
      rw [hze]; congr 3; simp only [lin]; ring
    · push Not at hhalf
      refine Or.inr ⟨(r - 3 / 8) / (3 / 4), ⟨by linarith, by linarith [hr.2]⟩, ?_⟩
      rw [hze]; congr 3; simp only [lin]; ring
  have htwo : ∀ z ∈ O, HasLocalTwoSides O z := by
    intro z hz V hVo hzV
    have hfrom_chart : ∀ (p q : ℝ) (Os : Set ℂ) (Ks : ℂ → T) (θ : unitInterval → ℝ) (ε : ℝ),
        0 < ε → StripChart Os Ks → StrictMono θ →
        (∀ t : unitInterval, (θ t : ℂ) ∈ Os ∧ Ks (θ t) = j (φ (ee (lin p q t.1))).1) →
        (Icc (θ ⟨1 / 24, by norm_num, by norm_num⟩) (θ ⟨23 / 24, by norm_num, by norm_num⟩) ×ℂ Icc (-ε) ε) ⊆ Os →
        (∀ w ∈ Icc (θ ⟨1 / 24, by norm_num, by norm_num⟩) (θ ⟨23 / 24, by norm_num, by norm_num⟩) ×ℂ Icc (-ε) ε,
          Ks w ∈ j '' O ↔ w.im = 0) →
        (∃ u ∈ Ioo (1 / 12 : ℝ) (11 / 12), z = (φ (ee (lin p q u))).1) →
        ∃ U A B : Set S, IsOpen U ∧ z ∈ U ∧ U ⊆ V ∧ U \ O = A ∪ B ∧ Disjoint A B ∧
          IsOpen A ∧ IsOpen B ∧ IsPreconnected A ∧ IsPreconnected B ∧ A.Nonempty ∧ B.Nonempty := by
      intro p q Os Ks θ ε hε hKs hθm hθ hROs hRO ⟨u, hu, hzu⟩
      let tu : unitInterval := ⟨u, by linarith [hu.1], by linarith [hu.2]⟩
      set x₀ := θ tu
      have hx₀_lo : θ ⟨1 / 24, by norm_num, by norm_num⟩ < x₀ := hθm (show (⟨1 / 24, by norm_num, by norm_num⟩ : unitInterval) < tu by change (1 / 24 : ℝ) < u; linarith [hu.1])
      have hx₀_hi : x₀ < θ ⟨23 / 24, by norm_num, by norm_num⟩ := hθm (show tu < (⟨23 / 24, by norm_num, by norm_num⟩ : unitInterval) by change u < 23 / 24; linarith [hu.2])
      have hRopen : IsOpen (Ioo (θ ⟨1 / 24, by norm_num, by norm_num⟩) (θ ⟨23 / 24, by norm_num, by norm_num⟩) ×ℂ Ioo (-ε) ε) :=
        isOpen_Ioo.reProdIm isOpen_Ioo
      have hRsub : (Ioo (θ ⟨1 / 24, by norm_num, by norm_num⟩) (θ ⟨23 / 24, by norm_num, by norm_num⟩) ×ℂ Ioo (-ε) ε) ⊆
          (Icc (θ ⟨1 / 24, by norm_num, by norm_num⟩) (θ ⟨23 / 24, by norm_num, by norm_num⟩) ×ℂ Icc (-ε) ε) :=
        fun w hw => Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hw).1, Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hw).2⟩
      have hjVo : IsOpen (j '' V ∩ Kᶜ) := by
        obtain ⟨W, hWo, hWV⟩ := hj.isInducing.isOpen_iff.mp hVo
        have heq : j '' V ∩ Kᶜ = W ∩ Kᶜ := by
          ext y; constructor
          · rintro ⟨⟨x, hxV, rfl⟩, hyK⟩; exact ⟨(Set.ext_iff.mp hWV x).mpr hxV, hyK⟩
          · rintro ⟨hyW, hyK⟩
            obtain ⟨x, rfl⟩ := (hcov ▸ mem_univ y).resolve_right hyK
            exact ⟨⟨x, (Set.ext_iff.mp hWV x).mp hyW, rfl⟩, hyK⟩
        rw [heq]; exact hWo.inter hK.isOpen_compl
      have hpre_o : IsOpen ((Ioo (θ ⟨1 / 24, by norm_num, by norm_num⟩) (θ ⟨23 / 24, by norm_num, by norm_num⟩) ×ℂ Ioo (-ε) ε) ∩ Ks ⁻¹' (j '' V ∩ Kᶜ)) :=
        (hKs.hc.mono (hRsub.trans hROs)).isOpen_inter_preimage hRopen hjVo
      have hx₀_mem : (x₀ : ℂ) ∈ (Ioo (θ ⟨1 / 24, by norm_num, by norm_num⟩) (θ ⟨23 / 24, by norm_num, by norm_num⟩) ×ℂ Ioo (-ε) ε) ∩ Ks ⁻¹' (j '' V ∩ Kᶜ) := by
        refine ⟨Complex.mem_reProdIm.mpr ⟨⟨hx₀_lo, hx₀_hi⟩, by simp [hε]⟩, ?_⟩
        rw [mem_preimage, (hθ tu).2, ← hzu]; exact ⟨⟨z, hzV, rfl⟩, hO_notK z hz⟩
      obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp hpre_o _ hx₀_mem
      have hB_in_R : ball (x₀ : ℂ) δ ⊆ Icc (θ ⟨1 / 24, by norm_num, by norm_num⟩) (θ ⟨23 / 24, by norm_num, by norm_num⟩) ×ℂ Icc (-ε) ε :=
        fun w hw => hRsub (hδsub hw).1
      let U : Set S := j ⁻¹' (Ks '' ball (x₀ : ℂ) δ)
      let A : Set S := j ⁻¹' (Ks '' (ball (x₀ : ℂ) δ ∩ {w : ℂ | 0 < w.im}))
      let B : Set S := j ⁻¹' (Ks '' (ball (x₀ : ℂ) δ ∩ {w : ℂ | w.im < 0}))
      have hUo : IsOpen U := (hKs.ho _ isOpen_ball (hB_in_R.trans hROs)).preimage hj.continuous
      have hAo : IsOpen A := (hKs.ho _ (isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)) (inter_subset_left.trans (hB_in_R.trans hROs))).preimage hj.continuous
      have hBo : IsOpen B := (hKs.ho _ (isOpen_ball.inter (isOpen_lt Complex.continuous_im continuous_const)) (inter_subset_left.trans (hB_in_R.trans hROs))).preimage hj.continuous
      have hK_range : ∀ w ∈ ball (x₀ : ℂ) δ, ∃ x : S, j x = Ks w := fun w hw => by
        obtain ⟨x, -, hxe⟩ := (hδsub hw).2.1; exact ⟨x, hxe⟩
      refine ⟨U, A, B, hUo, ⟨(x₀ : ℂ), mem_ball_self hδ, by rw [(hθ tu).2, ← hzu]⟩,
        fun x ⟨w, hw, hwe⟩ => by obtain ⟨x', hx'V, hx'e⟩ := (hδsub hw).2.1; exact hji (hx'e.trans hwe) ▸ hx'V,
        ?_, ?_, hAo, hBo, ?_, ?_, ?_, ?_⟩
      · ext x; constructor
        · rintro ⟨⟨w, hw, hwe⟩, hxO⟩
          have him0 : w.im ≠ 0 := fun h0 => hxO (by
            obtain ⟨y, hyO, hye⟩ := (hRO w (hB_in_R hw)).mpr h0; exact hji (hye.trans hwe) ▸ hyO)
          rcases lt_or_gt_of_ne him0 with hlt | hgt
          · exact Or.inr ⟨w, ⟨hw, hlt⟩, hwe⟩
          · exact Or.inl ⟨w, ⟨hw, hgt⟩, hwe⟩
        · rintro (⟨w, ⟨hw, hgt⟩, hwe⟩ | ⟨w, ⟨hw, hlt⟩, hwe⟩)
          · exact ⟨⟨w, hw, hwe⟩, fun hxO => hgt.ne' ((hRO w (hB_in_R hw)).mp ⟨x, hxO, hwe.symm⟩)⟩
          · exact ⟨⟨w, hw, hwe⟩, fun hxO => hlt.ne ((hRO w (hB_in_R hw)).mp ⟨x, hxO, hwe.symm⟩)⟩
      · rw [Set.disjoint_left]; rintro x ⟨w₁, ⟨hw₁, h1⟩, he₁⟩ ⟨w₂, ⟨hw₂, h2⟩, he₂⟩
        have hw := hKs.hi (hROs (hB_in_R hw₁)) (hROs (hB_in_R hw₂)) (he₁.trans he₂.symm)
        rw [hw] at h1
        exact (lt_asymm (show 0 < w₂.im from h1) (show w₂.im < 0 from h2)).elim
      · have hpc : IsPreconnected (Ks '' (ball (x₀ : ℂ) δ ∩ {w : ℂ | 0 < w.im})) :=
          ((convex_ball _ _).inter (convex_halfSpace_im_gt 0)).isPreconnected.image Ks
            (hKs.hc.mono (inter_subset_left.trans (hB_in_R.trans hROs)))
        have him : j '' A = Ks '' (ball (x₀ : ℂ) δ ∩ {w : ℂ | 0 < w.im}) := by
          ext y; constructor
          · rintro ⟨x, hx, rfl⟩; exact hx
          · rintro ⟨w, hw, rfl⟩; obtain ⟨x, hx⟩ := hK_range w hw.1; exact ⟨x, ⟨w, hw, hx.symm⟩, hx⟩
        exact (hj.isInducing.isPreconnected_image (s := A)).mp (him.symm ▸ hpc)
      · have hpc : IsPreconnected (Ks '' (ball (x₀ : ℂ) δ ∩ {w : ℂ | w.im < 0})) :=
          ((convex_ball _ _).inter (convex_halfSpace_im_lt 0)).isPreconnected.image Ks
            (hKs.hc.mono (inter_subset_left.trans (hB_in_R.trans hROs)))
        have him : j '' B = Ks '' (ball (x₀ : ℂ) δ ∩ {w : ℂ | w.im < 0}) := by
          ext y; constructor
          · rintro ⟨x, hx, rfl⟩; exact hx
          · rintro ⟨w, hw, rfl⟩; obtain ⟨x, hx⟩ := hK_range w hw.1; exact ⟨x, ⟨w, hw, hx.symm⟩, hx⟩
        exact (hj.isInducing.isPreconnected_image (s := B)).mp (him.symm ▸ hpc)
      · have hw : (x₀ : ℂ) + ((δ / 2 : ℝ) : ℂ) * I ∈ ball (x₀ : ℂ) δ ∩ {w : ℂ | 0 < w.im} := by
          refine ⟨?_, ?_⟩
          · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
                Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hδ)]; linarith
          · simp [half_pos hδ]
        obtain ⟨x, hx⟩ := hK_range _ hw.1; exact ⟨x, _, hw, hx.symm⟩
      · have hw : (x₀ : ℂ) - ((δ / 2 : ℝ) : ℂ) * I ∈ ball (x₀ : ℂ) δ ∩ {w : ℂ | w.im < 0} := by
          refine ⟨?_, ?_⟩
          · rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one,
                Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hδ)]; linarith
          · simp [half_pos hδ]
        obtain ⟨x, hx⟩ := hK_range _ hw.1; exact ⟨x, _, hw, hx.symm⟩
    rcases hO_cov z hz with h1 | h2
    · exact hfrom_chart (-1 / 8) (5 / 8) O₁ K₁ θ₁ ε₁ hε₁ hK₁ hθ₁m hθ₁ hR₁Os hR₁O h1
    · exact hfrom_chart (3 / 8) (9 / 8) O₂ K₂ θ₂ ε₂ hε₂ hK₂ hθ₂m hθ₂ hR₂Os hR₂O h2
  -- Construct the `ZMod 2` crossing cocycle `ω` for `O` using the two shrunk open rectangles:
  let R₁big : Set ℂ := Icc (θ₁ ⟨1 / 24, by norm_num, by norm_num⟩) (θ₁ ⟨23 / 24, by norm_num, by norm_num⟩) ×ℂ Icc (-ε₁) ε₁
  let R₂big : Set ℂ := Icc (θ₂ ⟨1 / 24, by norm_num, by norm_num⟩) (θ₂ ⟨23 / 24, by norm_num, by norm_num⟩) ×ℂ Icc (-ε₂) ε₂
  let R₁ : Set ℂ := Ioo (θ₁ ⟨1 / 12, by norm_num, by norm_num⟩) (θ₁ ⟨11 / 12, by norm_num, by norm_num⟩) ×ℂ Ioo (-(ε₁ / 2)) (ε₁ / 2)
  let R₂ : Set ℂ := Ioo (θ₂ ⟨1 / 12, by norm_num, by norm_num⟩) (θ₂ ⟨11 / 12, by norm_num, by norm_num⟩) ×ℂ Ioo (-(ε₂ / 2)) (ε₂ / 2)
  have hR₁_sub_big : closure R₁ ⊆ R₁big := by
    have h1 : R₁ ⊆ Icc (θ₁ ⟨1 / 12, by norm_num, by norm_num⟩) (θ₁ ⟨11 / 12, by norm_num, by norm_num⟩) ×ℂ Icc (-(ε₁ / 2)) (ε₁ / 2) :=
      fun z hz => Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hz).1, Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hz).2⟩
    have h2 : Icc (θ₁ ⟨1 / 12, by norm_num, by norm_num⟩) (θ₁ ⟨11 / 12, by norm_num, by norm_num⟩) ×ℂ Icc (-(ε₁ / 2)) (ε₁ / 2) ⊆ R₁big := by
      intro z hz; rw [Complex.mem_reProdIm] at hz ⊢
      have hlo : θ₁ ⟨1 / 24, by norm_num, by norm_num⟩ ≤ θ₁ ⟨1 / 12, by norm_num, by norm_num⟩ :=
        hθ₁m.monotone (by show (1 / 24 : ℝ) ≤ 1 / 12; norm_num)
      have hhi : θ₁ ⟨11 / 12, by norm_num, by norm_num⟩ ≤ θ₁ ⟨23 / 24, by norm_num, by norm_num⟩ :=
        hθ₁m.monotone (by show (11 / 12 : ℝ) ≤ 23 / 24; norm_num)
      exact ⟨⟨hlo.trans hz.1.1, hz.1.2.trans hhi⟩, ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩
    exact (closure_minimal (h1.trans h2) (isClosed_Icc.reProdIm isClosed_Icc))
  have hR₂_sub_big : closure R₂ ⊆ R₂big := by
    have h1 : R₂ ⊆ Icc (θ₂ ⟨1 / 12, by norm_num, by norm_num⟩) (θ₂ ⟨11 / 12, by norm_num, by norm_num⟩) ×ℂ Icc (-(ε₂ / 2)) (ε₂ / 2) :=
      fun z hz => Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hz).1, Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hz).2⟩
    have h2 : Icc (θ₂ ⟨1 / 12, by norm_num, by norm_num⟩) (θ₂ ⟨11 / 12, by norm_num, by norm_num⟩) ×ℂ Icc (-(ε₂ / 2)) (ε₂ / 2) ⊆ R₂big := by
      intro z hz; rw [Complex.mem_reProdIm] at hz ⊢
      have hlo : θ₂ ⟨1 / 24, by norm_num, by norm_num⟩ ≤ θ₂ ⟨1 / 12, by norm_num, by norm_num⟩ :=
        hθ₂m.monotone (by show (1 / 24 : ℝ) ≤ 1 / 12; norm_num)
      have hhi : θ₂ ⟨11 / 12, by norm_num, by norm_num⟩ ≤ θ₂ ⟨23 / 24, by norm_num, by norm_num⟩ :=
        hθ₂m.monotone (by show (11 / 12 : ℝ) ≤ 23 / 24; norm_num)
      exact ⟨⟨hlo.trans hz.1.1, hz.1.2.trans hhi⟩, ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩
    exact closure_minimal (h1.trans h2) (isClosed_Icc.reProdIm isClosed_Icc)
  have hR₁o : IsOpen R₁ := isOpen_Ioo.reProdIm isOpen_Ioo
  have hR₂o : IsOpen R₂ := isOpen_Ioo.reProdIm isOpen_Ioo
  let W₁ : Set S := j ⁻¹' (K₁ '' R₁)
  let W₂ : Set S := j ⁻¹' (K₂ '' R₂)
  have hW₁o : IsOpen W₁ := (hK₁.ho _ hR₁o (subset_closure.trans (hR₁_sub_big.trans hR₁Os))).preimage hj.continuous
  have hW₂o : IsOpen W₂ := (hK₂.ho _ hR₂o (subset_closure.trans (hR₂_sub_big.trans hR₂Os))).preimage hj.continuous
  have hcov_W : ∀ z ∈ O, z ∈ W₁ ∨ z ∈ W₂ := fun z hzO => by
    rcases hO_cov z hzO with ⟨u, hu, hzu⟩ | ⟨u, hu, hzu⟩
    · left
      let tu : unitInterval := ⟨u, by linarith [hu.1], by linarith [hu.2]⟩
      have ht_lo : (⟨1 / 12, by norm_num, by norm_num⟩ : unitInterval) < tu := hu.1
      have ht_hi : tu < (⟨11 / 12, by norm_num, by norm_num⟩ : unitInterval) := hu.2
      have him0 : (0 : ℝ) ∈ Ioo (-(ε₁ / 2)) (ε₁ / 2) := ⟨by linarith [half_pos hε₁], half_pos hε₁⟩
      exact ⟨(θ₁ tu : ℂ), Complex.mem_reProdIm.mpr ⟨⟨hθ₁m ht_lo, hθ₁m ht_hi⟩, him0⟩,
        ((hθ₁ tu).2).trans (congrArg j hzu.symm)⟩
    · right
      let tu : unitInterval := ⟨u, by linarith [hu.1], by linarith [hu.2]⟩
      have ht_lo : (⟨1 / 12, by norm_num, by norm_num⟩ : unitInterval) < tu := hu.1
      have ht_hi : tu < (⟨11 / 12, by norm_num, by norm_num⟩ : unitInterval) := hu.2
      have him0 : (0 : ℝ) ∈ Ioo (-(ε₂ / 2)) (ε₂ / 2) := ⟨by linarith [half_pos hε₂], half_pos hε₂⟩
      exact ⟨(θ₂ tu : ℂ), Complex.mem_reProdIm.mpr ⟨⟨hθ₂m ht_lo, hθ₂m ht_hi⟩, him0⟩,
        ((hθ₂ tu).2).trans (congrArg j hzu.symm)⟩
  -- Inverse coordinates `z₁ : S → ℂ` on `K₁ '' R₁big` and `z₂ : S → ℂ` on `K₂ '' R₂big`:
  let z₁ : S → ℂ := fun x => if h : ∃ w ∈ R₁big, K₁ w = j x then h.choose else 0
  let z₂ : S → ℂ := fun x => if h : ∃ w ∈ R₂big, K₂ w = j x then h.choose else 0
  have hz₁_eq : ∀ {w : ℂ} {x : S}, w ∈ R₁big → K₁ w = j x → z₁ x = w := fun {w x} hw he => by
    have hex : ∃ u ∈ R₁big, K₁ u = j x := ⟨w, hw, he⟩
    simp only [z₁, dite_eq_left hex]
    exact hK₁.hi (hR₁Os hex.choose_spec.1) (hR₁Os hw) (hex.choose_spec.2.trans he.symm)
  have hz₂_eq : ∀ {w : ℂ} {x : S}, w ∈ R₂big → K₂ w = j x → z₂ x = w := fun {w x} hw he => by
    have hex : ∃ u ∈ R₂big, K₂ u = j x := ⟨w, hw, he⟩
    simp only [z₂, dite_eq_left hex]
    exact hK₂.hi (hR₂Os hex.choose_spec.1) (hR₂Os hw) (hex.choose_spec.2.trans he.symm)
  have hW₁_pos : ∀ {x : S}, x ∈ W₁ → z₁ x ∈ R₁ ∧ K₁ (z₁ x) = j x := fun ⟨w, hw, hwe⟩ => by
    rw [hz₁_eq (hR₁_sub_big (subset_closure hw)) hwe]; exact ⟨hw, hwe⟩
  have hW₂_pos : ∀ {x : S}, x ∈ W₂ → z₂ x ∈ R₂ ∧ K₂ (z₂ x) = j x := fun ⟨w, hw, hwe⟩ => by
    rw [hz₂_eq (hR₂_sub_big (subset_closure hw)) hwe]; exact ⟨hw, hwe⟩
  -- For any `x ∈ O` with `j x ∈ K₁ '' R₁big ∩ K₂ '' R₂big`, `sameAt x` tests whether upper half-plane of `K₁` hits upper half-plane of `K₂`:
  let sameAt : S → Prop := fun x =>
    ∃ r > 0, ∀ w ∈ ball (z₁ x) r, w.im > 0 → ∃ w₂ ∈ R₂big, K₂ w₂ = K₁ w ∧ w₂.im > 0
  -- Key local compatibility lemma on any `x ∈ O` with `j x ∈ K₁ '' (int R₁big) ∩ K₂ '' (int R₂big)` (in particular on `closure W₁ ∩ W₂ ∩ O`!):
  have hR₁int : IsOpen (Ioo (θ₁ ⟨1 / 24, by norm_num, by norm_num⟩) (θ₁ ⟨23 / 24, by norm_num, by norm_num⟩) ×ℂ Ioo (-ε₁) ε₁) :=
    isOpen_Ioo.reProdIm isOpen_Ioo
  have hR₂int : IsOpen (Ioo (θ₂ ⟨1 / 24, by norm_num, by norm_num⟩) (θ₂ ⟨23 / 24, by norm_num, by norm_num⟩) ×ℂ Ioo (-ε₂) ε₂) :=
    isOpen_Ioo.reProdIm isOpen_Ioo
  have hclR₁_int : closure R₁ ⊆ Ioo (θ₁ ⟨1 / 24, by norm_num, by norm_num⟩) (θ₁ ⟨23 / 24, by norm_num, by norm_num⟩) ×ℂ Ioo (-ε₁) ε₁ := by
    have h1 : R₁ ⊆ Icc (θ₁ ⟨1 / 12, by norm_num, by norm_num⟩) (θ₁ ⟨11 / 12, by norm_num, by norm_num⟩) ×ℂ Icc (-(ε₁ / 2)) (ε₁ / 2) :=
      fun z hz => Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hz).1, Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hz).2⟩
    refine (closure_minimal h1 (isClosed_Icc.reProdIm isClosed_Icc)).trans fun z hz => ?_
    rw [Complex.mem_reProdIm] at hz ⊢
    have hlo : θ₁ ⟨1 / 24, by norm_num, by norm_num⟩ < θ₁ ⟨1 / 12, by norm_num, by norm_num⟩ :=
      hθ₁m (by show (1 / 24 : ℝ) < 1 / 12; norm_num)
    have hhi : θ₁ ⟨11 / 12, by norm_num, by norm_num⟩ < θ₁ ⟨23 / 24, by norm_num, by norm_num⟩ :=
      hθ₁m (by show (11 / 12 : ℝ) < 23 / 24; norm_num)
    exact ⟨⟨hlo.trans_le hz.1.1, hz.1.2.trans_lt hhi⟩, ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩
  have hclR₂_int : closure R₂ ⊆ Ioo (θ₂ ⟨1 / 24, by norm_num, by norm_num⟩) (θ₂ ⟨23 / 24, by norm_num, by norm_num⟩) ×ℂ Ioo (-ε₂) ε₂ := by
    have h1 : R₂ ⊆ Icc (θ₂ ⟨1 / 12, by norm_num, by norm_num⟩) (θ₂ ⟨11 / 12, by norm_num, by norm_num⟩) ×ℂ Icc (-(ε₂ / 2)) (ε₂ / 2) :=
      fun z hz => Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hz).1, Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hz).2⟩
    refine (closure_minimal h1 (isClosed_Icc.reProdIm isClosed_Icc)).trans fun z hz => ?_
    rw [Complex.mem_reProdIm] at hz ⊢
    have hlo : θ₂ ⟨1 / 24, by norm_num, by norm_num⟩ < θ₂ ⟨1 / 12, by norm_num, by norm_num⟩ :=
      hθ₂m (by show (1 / 24 : ℝ) < 1 / 12; norm_num)
    have hhi : θ₂ ⟨11 / 12, by norm_num, by norm_num⟩ < θ₂ ⟨23 / 24, by norm_num, by norm_num⟩ :=
      hθ₂m (by show (11 / 12 : ℝ) < 23 / 24; norm_num)
    exact ⟨⟨hlo.trans_le hz.1.1, hz.1.2.trans_lt hhi⟩, ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩
  let f₂ : S → ZMod 2 := fun x => if 0 < (z₂ x).im then 1 else 0
  let f₁ : S → ZMod 2 := fun x =>
    if x ∈ O then (if sameAt x then 0 else 1) else if 0 < (z₁ x).im then 1 else 0
  let ω : S → S → ZMod 2 := fun x y =>
    if x ∈ W₁ ∧ y ∈ W₁ then f₁ y - f₁ x
    else if x ∈ W₂ ∧ y ∈ W₂ then f₂ y - f₂ x
    else 0
  -- Key transition lemma: near any `x₀ ∈ O` with `z₁ x₀ ∈ int R₁big` and `z₂ x₀ ∈ int R₂big`, `f₁ - f₂` is CONSTANT!
  have htrans : ∀ x₀ ∈ O, (∃ w₁ ∈ Ioo (θ₁ ⟨1 / 24, by norm_num, by norm_num⟩) (θ₁ ⟨23 / 24, by norm_num, by norm_num⟩) ×ℂ Ioo (-ε₁) ε₁, K₁ w₁ = j x₀) →
      (∃ w₂ ∈ Ioo (θ₂ ⟨1 / 24, by norm_num, by norm_num⟩) (θ₂ ⟨23 / 24, by norm_num, by norm_num⟩) ×ℂ Ioo (-ε₂) ε₂, K₂ w₂ = j x₀) →
      ∃ U : Set S, IsOpen U ∧ x₀ ∈ U ∧ ∃ c : ZMod 2, ∀ x ∈ U, f₁ x - f₂ x = c := by
    intro x₀ hx₀ ⟨w₁, hw₁i, hw₁e⟩ ⟨w₂, hw₂i, hw₂e⟩
    have hw₁b : w₁ ∈ R₁big := Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hw₁i).1, Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hw₁i).2⟩
    have hw₂b : w₂ ∈ R₂big := Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hw₂i).1, Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hw₂i).2⟩
    have hw₁0 : w₁.im = 0 := (hR₁O w₁ hw₁b).mp ⟨x₀, hx₀, hw₁e.symm⟩
    have hK₂int_o : IsOpen (K₂ '' (Ioo (θ₂ ⟨1 / 24, by norm_num, by norm_num⟩) (θ₂ ⟨23 / 24, by norm_num, by norm_num⟩) ×ℂ Ioo (-ε₂) ε₂)) :=
      hK₂.ho _ hR₂int (fun z hz => hR₂Os (Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hz).1, Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hz).2⟩))
    have hpre_o : IsOpen ((Ioo (θ₁ ⟨1 / 24, by norm_num, by norm_num⟩) (θ₁ ⟨23 / 24, by norm_num, by norm_num⟩) ×ℂ Ioo (-ε₁) ε₁) ∩
        K₁ ⁻¹' (K₂ '' (Ioo (θ₂ ⟨1 / 24, by norm_num, by norm_num⟩) (θ₂ ⟨23 / 24, by norm_num, by norm_num⟩) ×ℂ Ioo (-ε₂) ε₂))) :=
      (hK₁.hc.mono fun z hz => hR₁Os (Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hz).1, Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hz).2⟩)).isOpen_inter_preimage hR₁int hK₂int_o
    obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp hpre_o w₁ ⟨hw₁i, w₂, hw₂i, hw₂e.trans hw₁e.symm⟩
    have hB_big : ∀ w ∈ ball w₁ δ, w ∈ R₁big ∧ ∃ u₂ ∈ R₂big, K₂ u₂ = K₁ w := fun w hw => by
      have h1 := hδsub hw
      obtain ⟨u₂, hu₂, hu₂e⟩ := h1.2
      exact ⟨Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp h1.1).1, Ioo_subset_Icc_self (Complex.mem_reProdIm.mp h1.1).2⟩,
        u₂, Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hu₂).1, Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hu₂).2⟩, hu₂e⟩
    -- Partition `ball w₁ δ ∩ {im > 0}` by sign of `u₂.im` (two disjoint open sets!):
    let Up : Set ℂ := ball w₁ δ ∩ {w : ℂ | 0 < w.im}
    let Dn : Set ℂ := ball w₁ δ ∩ {w : ℂ | w.im < 0}
    have hUp_pc : IsPreconnected Up := ((convex_ball _ _).inter (convex_halfSpace_im_gt 0)).isPreconnected
    have hDn_pc : IsPreconnected Dn := ((convex_ball _ _).inter (convex_halfSpace_im_lt 0)).isPreconnected
    have hUp_ne : Up.Nonempty := ⟨w₁ + ((δ / 2 : ℝ) : ℂ) * I, by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hδ)]; linarith, by simp [hw₁0, half_pos hδ]⟩
    have hDn_ne : Dn.Nonempty := ⟨w₁ - ((δ / 2 : ℝ) : ℂ) * I, by
      rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hδ)]; linarith, by simp [hw₁0, half_pos hδ]⟩
    let Qpos : Set ℂ := K₁ ⁻¹' (K₂ '' (Ioo (θ₂ ⟨1 / 24, by norm_num, by norm_num⟩) (θ₂ ⟨23 / 24, by norm_num, by norm_num⟩) ×ℂ Ioo 0 ε₂))
    let Qneg : Set ℂ := K₁ ⁻¹' (K₂ '' (Ioo (θ₂ ⟨1 / 24, by norm_num, by norm_num⟩) (θ₂ ⟨23 / 24, by norm_num, by norm_num⟩) ×ℂ Ioo (-ε₂) 0))
    have hQpos_o : IsOpen (ball w₁ δ ∩ Qpos) := (hK₁.hc.mono fun w hw => hR₁Os (hB_big w hw).1).isOpen_inter_preimage isOpen_ball
      (hK₂.ho _ (isOpen_Ioo.reProdIm isOpen_Ioo) fun u hu => hR₂Os (Complex.mem_reProdIm.mpr
        ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hu).1, ⟨by linarith [(Complex.mem_reProdIm.mp hu).2.1], (Complex.mem_reProdIm.mp hu).2.2.le⟩⟩))
    have hQneg_o : IsOpen (ball w₁ δ ∩ Qneg) := (hK₁.hc.mono fun w hw => hR₁Os (hB_big w hw).1).isOpen_inter_preimage isOpen_ball
      (hK₂.ho _ (isOpen_Ioo.reProdIm isOpen_Ioo) fun u hu => hR₂Os (Complex.mem_reProdIm.mpr
        ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hu).1, ⟨(Complex.mem_reProdIm.mp hu).2.1.le, by linarith [(Complex.mem_reProdIm.mp hu).2.2]⟩⟩))
    have hQ_disj : Disjoint Qpos Qneg := by
      rw [Set.disjoint_left]; rintro w ⟨u₁, hu₁, he₁⟩ ⟨u₂, hu₂, he₂⟩
      have hu₁b : u₁ ∈ R₂big := Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hu₁).1,
        ⟨by linarith [(Complex.mem_reProdIm.mp hu₁).2.1], (Complex.mem_reProdIm.mp hu₁).2.2.le⟩⟩
      have hu₂b : u₂ ∈ R₂big := Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hu₂).1,
        ⟨(Complex.mem_reProdIm.mp hu₂).2.1.le, by linarith [(Complex.mem_reProdIm.mp hu₂).2.2]⟩⟩
      have heq := hK₂.hi (hR₂Os hu₁b) (hR₂Os hu₂b) (he₁.trans he₂.symm)
      rw [heq] at hu₁; linarith [(Complex.mem_reProdIm.mp hu₁).2.1, (Complex.mem_reProdIm.mp hu₂).2.2]
    have hside_const : ∀ X, IsPreconnected X → X ⊆ ball w₁ δ → (∀ w ∈ X, w.im ≠ 0) →
        X ⊆ Qpos ∨ X ⊆ Qneg := fun X hXc hXB hX0 => by
      have hcov' : X ⊆ (ball w₁ δ ∩ Qpos) ∪ (ball w₁ δ ∩ Qneg) := fun w hw => by
        obtain ⟨u₂, hu₂, hu₂e⟩ := (hδsub (hXB hw)).2
        have hu₂b : u₂ ∈ R₂big := Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hu₂).1, Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hu₂).2⟩
        have hu₂0 : u₂.im ≠ 0 := fun h0 => hX0 w hw ((hR₁O w (hB_big w (hXB hw)).1).mp (hu₂e ▸ (hR₂O u₂ hu₂b).mpr h0))
        rcases lt_or_gt_of_ne hu₂0 with hlt | hgt
        · exact Or.inr ⟨hXB hw, u₂, Complex.mem_reProdIm.mpr ⟨(Complex.mem_reProdIm.mp hu₂).1, (Complex.mem_reProdIm.mp hu₂).2.1, hlt⟩, hu₂e⟩
        · exact Or.inl ⟨hXB hw, u₂, Complex.mem_reProdIm.mpr ⟨(Complex.mem_reProdIm.mp hu₂).1, hgt, (Complex.mem_reProdIm.mp hu₂).2.2⟩, hu₂e⟩
      by_contra hnot; push Not at hnot
      obtain ⟨a, haX, haP⟩ := Set.not_subset.mp hnot.1
      obtain ⟨b, hbX, hbN⟩ := Set.not_subset.mp hnot.2
      have haN : a ∈ ball w₁ δ ∩ Qneg := (hcov' haX).resolve_left fun h => haP h.2
      have hbP : b ∈ ball w₁ δ ∩ Qpos := (hcov' hbX).resolve_right fun h => hbN h.2
      obtain ⟨w, -, hwP, hwN⟩ := hXc _ _ hQpos_o hQneg_o hcov' ⟨b, hbX, hbP⟩ ⟨a, haX, haN⟩
      exact Set.disjoint_left.mp hQ_disj hwP.2 hwN.2
    -- Also `Up` and `Dn` cannot map to the SAME side of `K₂`!
    have hnot_same : ¬ (Up ⊆ Qpos ∧ Dn ⊆ Qpos) ∧ ¬ (Up ⊆ Qneg ∧ Dn ⊆ Qneg) := by
      have hK₁_open : IsOpen (K₁ '' ball w₁ δ) := hK₁.ho _ isOpen_ball (fun w hw => hR₁Os (hB_big w hw).1)
      have hpre2 : IsOpen (O₂ ∩ K₂ ⁻¹' (K₁ '' ball w₁ δ)) := hK₂.hc.isOpen_inter_preimage hK₂.isOpen hK₁_open
      obtain ⟨r₂, hr₂, hr₂sub⟩ := Metric.isOpen_iff.mp hpre2 w₂ ⟨hR₂Os hw₂b, w₁, mem_ball_self hδ, hw₁e.trans hw₂e.symm⟩
      have hw₂0 : w₂.im = 0 := (hR₂O w₂ hw₂b).mp ⟨x₀, hx₀, hw₂e.symm⟩
      have hB2_in : ∃ r₂' > 0, r₂' ≤ r₂ ∧ ball w₂ r₂' ⊆ Ioo (θ₂ ⟨1 / 24, by norm_num, by norm_num⟩) (θ₂ ⟨23 / 24, by norm_num, by norm_num⟩) ×ℂ Ioo (-ε₂) ε₂ := by
        obtain ⟨r, hr, hrs⟩ := Metric.isOpen_iff.mp hR₂int w₂ hw₂i
        exact ⟨min r r₂, lt_min hr hr₂, min_le_right _ _, (ball_subset_ball (min_le_left _ _)).trans hrs⟩
      obtain ⟨r₂', hr₂', hr₂'le, hB2sub⟩ := hB2_in
      constructor
      · rintro ⟨hUpP, hDnP⟩
        let u := w₂ - ((r₂' / 2 : ℝ) : ℂ) * I
        have huB : u ∈ ball w₂ r₂' := by
          rw [mem_ball, dist_eq_norm, show u - w₂ = -(((r₂' / 2 : ℝ) : ℂ) * I) by simp [u],
              norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr₂')]; linarith
        have hu_im : u.im < 0 := by simp [u, hw₂0, half_pos hr₂']
        obtain ⟨w, hwB, hwe⟩ := (hr₂sub (lt_of_lt_of_le huB hr₂'le)).2
        have hu_int := hB2sub huB
        have hub : u ∈ R₂big := Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hu_int).1, Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hu_int).2⟩
        have hwQ : w ∈ Qneg := ⟨u, Complex.mem_reProdIm.mpr ⟨(Complex.mem_reProdIm.mp hu_int).1, (Complex.mem_reProdIm.mp hu_int).2.1, hu_im⟩, hwe.symm⟩
        have hw0 : w.im ≠ 0 := fun h0 => hu_im.ne ((hR₂O u hub).mp (hwe ▸ (hR₁O w (hB_big w hwB).1).mpr h0))
        rcases lt_or_gt_of_ne hw0 with hlt | hgt
        · exact Set.disjoint_left.mp hQ_disj (hDnP ⟨hwB, hlt⟩) hwQ
        · exact Set.disjoint_left.mp hQ_disj (hUpP ⟨hwB, hgt⟩) hwQ
      · rintro ⟨hUpN, hDnN⟩
        let u := w₂ + ((r₂' / 2 : ℝ) : ℂ) * I
        have huB : u ∈ ball w₂ r₂' := by
          rw [mem_ball, dist_eq_norm, show u - w₂ = ((r₂' / 2 : ℝ) : ℂ) * I by simp [u],
              norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr₂')]; linarith
        have hu_im : 0 < u.im := by simp [u, hw₂0, half_pos hr₂']
        obtain ⟨w, hwB, hwe⟩ := (hr₂sub (lt_of_lt_of_le huB hr₂'le)).2
        have hu_int := hB2sub huB
        have hub : u ∈ R₂big := Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hu_int).1, Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hu_int).2⟩
        have hwQ : w ∈ Qpos := ⟨u, Complex.mem_reProdIm.mpr ⟨(Complex.mem_reProdIm.mp hu_int).1, hu_im, (Complex.mem_reProdIm.mp hu_int).2.2⟩, hwe.symm⟩
        have hw0 : w.im ≠ 0 := fun h0 => hu_im.ne' ((hR₂O u hub).mp (hwe ▸ (hR₁O w (hB_big w hwB).1).mpr h0))
        rcases lt_or_gt_of_ne hw0 with hlt | hgt
        · exact Set.disjoint_left.mp hQ_disj hwQ (hDnN ⟨hwB, hlt⟩)
        · exact Set.disjoint_left.mp hQ_disj hwQ (hUpN ⟨hwB, hgt⟩)
    let U : Set S := j ⁻¹' (K₁ '' ball w₁ δ)
    have hUo : IsOpen U := (hK₁.ho _ isOpen_ball (fun w hw => hR₁Os (hB_big w hw).1)).preimage hj.continuous
    have hx₀U : x₀ ∈ U := ⟨w₁, mem_ball_self hδ, hw₁e⟩
    have hUp_or := hside_const Up hUp_pc inter_subset_left (fun _ hw => hw.2.ne')
    have hDn_or := hside_const Dn hDn_pc inter_subset_left (fun _ hw => hw.2.ne)
    rcases hUp_or with hUpP | hUpN
    · have hDnN : Dn ⊆ Qneg := hDn_or.resolve_left (fun h => hnot_same.1 ⟨hUpP, h⟩)
      refine ⟨U, hUo, hx₀U, 0, fun x ⟨w, hw, hwe⟩ => ?_⟩
      have hz1 : z₁ x = w := hz₁_eq (hB_big w hw).1 hwe
      obtain ⟨u₂, hu₂b, hu₂e⟩ := (hB_big w hw).2
      have hz2 : z₂ x = u₂ := hz₂_eq hu₂b (hu₂e.trans hwe)
      by_cases hxO : x ∈ O
      · have hw0 : w.im = 0 := (hR₁O w (hB_big w hw).1).mp ⟨x, hxO, hwe.symm⟩
        have hu20 : u₂.im = 0 := (hR₂O u₂ hu₂b).mp ⟨x, hxO, (hu₂e.trans hwe).symm⟩
        have hsame : sameAt x := by
          obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp isOpen_ball w hw
          refine ⟨r, hr, fun v hv hvim => ?_⟩
          have hvB : v ∈ ball w₁ δ := hrsub (hz1 ▸ hv)
          obtain ⟨v₂, hv₂, hv₂e⟩ := hUpP ⟨hvB, hvim⟩
          exact ⟨v₂, Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hv₂).1,
            ⟨by linarith [(Complex.mem_reProdIm.mp hv₂).2.1], (Complex.mem_reProdIm.mp hv₂).2.2.le⟩⟩,
            hv₂e, (Complex.mem_reProdIm.mp hv₂).2.1⟩
        simp [f₁, f₂, hxO, hsame, hz2, hu20]
      · have hw0 : w.im ≠ 0 := fun h0 => hxO (by obtain ⟨y, hyO, hye⟩ := (hR₁O w (hB_big w hw).1).mpr h0; exact hji (hye.trans hwe) ▸ hyO)
        rcases lt_or_gt_of_ne hw0 with hlt | hgt
        · obtain ⟨v₂, hv₂, hv₂e⟩ := hDnN ⟨hw, hlt⟩
          have hv2b : v₂ ∈ R₂big := Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hv₂).1,
            ⟨(Complex.mem_reProdIm.mp hv₂).2.1.le, by linarith [(Complex.mem_reProdIm.mp hv₂).2.2]⟩⟩
          have hz2' : z₂ x = v₂ := hz₂_eq hv2b (hv₂e.trans hwe)
          have hnot1 : ¬ 0 < (z₁ x).im := by rw [hz1]; linarith
          have hnot2 : ¬ 0 < (z₂ x).im := by rw [hz2']; linarith [(Complex.mem_reProdIm.mp hv₂).2.2]
          simp [f₁, f₂, hxO, hnot1, hnot2]
        · obtain ⟨v₂, hv₂, hv₂e⟩ := hUpP ⟨hw, hgt⟩
          have hv2b : v₂ ∈ R₂big := Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hv₂).1,
            ⟨by linarith [(Complex.mem_reProdIm.mp hv₂).2.1], (Complex.mem_reProdIm.mp hv₂).2.2.le⟩⟩
          have hz2' : z₂ x = v₂ := hz₂_eq hv2b (hv₂e.trans hwe)
          have hpos1 : 0 < (z₁ x).im := by rw [hz1]; exact hgt
          have hpos2 : 0 < (z₂ x).im := by rw [hz2']; exact (Complex.mem_reProdIm.mp hv₂).2.1
          simp [f₁, f₂, hxO, hpos1, hpos2]
    · have hDnP : Dn ⊆ Qpos := hDn_or.resolve_right (fun h => hnot_same.2 ⟨hUpN, h⟩)
      refine ⟨U, hUo, hx₀U, 1, fun x ⟨w, hw, hwe⟩ => ?_⟩
      have hz1 : z₁ x = w := hz₁_eq (hB_big w hw).1 hwe
      obtain ⟨u₂, hu₂b, hu₂e⟩ := (hB_big w hw).2
      have hz2 : z₂ x = u₂ := hz₂_eq hu₂b (hu₂e.trans hwe)
      by_cases hxO : x ∈ O
      · have hw0 : w.im = 0 := (hR₁O w (hB_big w hw).1).mp ⟨x, hxO, hwe.symm⟩
        have hu20 : u₂.im = 0 := (hR₂O u₂ hu₂b).mp ⟨x, hxO, (hu₂e.trans hwe).symm⟩
        have hnsame : ¬ sameAt x := fun ⟨r, hr, hru⟩ => by
          obtain ⟨r', hr', hr'sub⟩ := Metric.isOpen_iff.mp isOpen_ball w hw
          set ρ := min r r' / 2
          have hρ : 0 < ρ := half_pos (lt_min hr hr')
          let v := w + (ρ : ℂ) * I
          have hv_ball : v ∈ ball w r' := by
            rw [mem_ball, dist_eq_norm, show v - w = (ρ : ℂ) * I by simp [v], norm_mul, Complex.norm_I, mul_one,
                Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
            exact (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)).trans_lt (half_lt_self hr')
          have hv_r : v ∈ ball (z₁ x) r := by
            rw [hz1, mem_ball, dist_eq_norm, show v - w = (ρ : ℂ) * I by simp [v], norm_mul, Complex.norm_I, mul_one,
                Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
            exact (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)).trans_lt (half_lt_self hr)
          have hvim : 0 < v.im := by simp [v, hw0, hρ]
          obtain ⟨v₂, hv₂b, hv₂e, hv₂pos⟩ := hru v hv_r hvim
          obtain ⟨v₂', hv₂', hv₂'e⟩ := hUpN ⟨hr'sub hv_ball, hvim⟩
          have hv₂'b : v₂' ∈ R₂big := Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hv₂').1,
            ⟨(Complex.mem_reProdIm.mp hv₂').2.1.le, by linarith [(Complex.mem_reProdIm.mp hv₂').2.2]⟩⟩
          have heq := hK₂.hi (hR₂Os hv₂b) (hR₂Os hv₂'b) (hv₂e.trans hv₂'e.symm)
          rw [heq] at hv₂pos; linarith [(Complex.mem_reProdIm.mp hv₂').2.2]
        simp [f₁, f₂, hxO, hnsame, hz2, hu20]
      · have hw0 : w.im ≠ 0 := fun h0 => hxO (by obtain ⟨y, hyO, hye⟩ := (hR₁O w (hB_big w hw).1).mpr h0; exact hji (hye.trans hwe) ▸ hyO)
        rcases lt_or_gt_of_ne hw0 with hlt | hgt
        · obtain ⟨v₂, hv₂, hv₂e⟩ := hDnP ⟨hw, hlt⟩
          have hv2b : v₂ ∈ R₂big := Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hv₂).1,
            ⟨by linarith [(Complex.mem_reProdIm.mp hv₂).2.1], (Complex.mem_reProdIm.mp hv₂).2.2.le⟩⟩
          have hz2' : z₂ x = v₂ := hz₂_eq hv2b (hv₂e.trans hwe)
          have hnot1 : ¬ 0 < (z₁ x).im := by rw [hz1]; linarith
          have hpos2 : 0 < (z₂ x).im := by rw [hz2']; exact (Complex.mem_reProdIm.mp hv₂).2.1
          simp [f₁, f₂, hxO, hnot1, hpos2]
        · obtain ⟨v₂, hv₂, hv₂e⟩ := hUpN ⟨hw, hgt⟩
          have hv2b : v₂ ∈ R₂big := Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hv₂).1,
            ⟨(Complex.mem_reProdIm.mp hv₂).2.1.le, by linarith [(Complex.mem_reProdIm.mp hv₂).2.2]⟩⟩
          have hz2' : z₂ x = v₂ := hz₂_eq hv2b (hv₂e.trans hwe)
          have hpos1 : 0 < (z₁ x).im := by rw [hz1]; exact hgt
          have hnot2 : ¬ 0 < (z₂ x).im := by rw [hz2']; linarith [(Complex.mem_reProdIm.mp hv₂).2.2]
          simp [f₁, f₂, hxO, hpos1, hnot2]
  -- Now verify `ω` vanishes locally off `O`:
  have hω_off : ∀ z ∉ O, ∃ U : Set S, IsOpen U ∧ z ∈ U ∧ ∀ x ∈ U, ∀ y ∈ U, ω x y = 0 := by
    intro z hzO
    -- For `k ∈ {1, 2}`, the upper half `K_k '' (closure R_k ∩ {im ≥ 0})` and lower half `K_k '' (closure R_k ∩ {im ≤ 0})`
    -- are compact sets intersecting inside `j '' O`, so `j z` misses at least one of them!
    have hhalf_miss : ∀ (Ks : ℂ → T) (Rs Rbig Os : Set ℂ),
        StripChart Os Ks → closure Rs ⊆ Rbig → Rbig ⊆ Os →
        (∀ w ∈ Rbig, Ks w ∈ j '' O ↔ w.im = 0) → IsCompact (closure Rs) →
        ∃ V : Set S, IsOpen V ∧ z ∈ V ∧
          ((∀ x ∈ V, ∀ w ∈ Rs, Ks w = j x → 0 < w.im) ∨ (∀ x ∈ V, ∀ w ∈ Rs, Ks w = j x → w.im < 0)) := by
      intro Ks Rs Rbig Os hKs hcl hbig hRO hcl_cpt
      let Cpos : Set T := Ks '' (closure Rs ∩ {w : ℂ | 0 ≤ w.im})
      let Cneg : Set T := Ks '' (closure Rs ∩ {w : ℂ | w.im ≤ 0})
      have hCpos_c : IsClosed Cpos :=
        ((hcl_cpt.inter_right (isClosed_le continuous_const Complex.continuous_im)).image_of_continuousOn
          (hKs.hc.mono (inter_subset_left.trans (hcl.trans hbig)))).isClosed
      have hCneg_c : IsClosed Cneg :=
        ((hcl_cpt.inter_right (isClosed_le Complex.continuous_im continuous_const)).image_of_continuousOn
          (hKs.hc.mono (inter_subset_left.trans (hcl.trans hbig)))).isClosed
      have hnot_both : ¬ (j z ∈ Cpos ∧ j z ∈ Cneg) := by
        rintro ⟨⟨w₁, ⟨hw₁c, hw₁p⟩, he₁⟩, ⟨w₂, ⟨hw₂c, hw₂n⟩, he₂⟩⟩
        have hw := hKs.hi (hbig (hcl hw₁c)) (hbig (hcl hw₂c)) (he₁.trans he₂.symm)
        have h0 : w₁.im = 0 := le_antisymm (hw ▸ hw₂n) hw₁p
        obtain ⟨y, hyO, hye⟩ := (hRO w₁ (hcl hw₁c)).mpr h0
        exact hzO (hji (hye.trans he₁) ▸ hyO)
      by_cases hp : j z ∈ Cpos
      · have hn : j z ∉ Cneg := fun h => hnot_both ⟨hp, h⟩
        refine ⟨j ⁻¹' Cnegᶜ, hCneg_c.isOpen_compl.preimage hj.continuous, hn, Or.inl fun x hx w hw hwe => ?_⟩
        by_contra hle; push Not at hle
        exact hx ⟨w, ⟨subset_closure hw, hle⟩, hwe⟩
      · refine ⟨j ⁻¹' Cposᶜ, hCpos_c.isOpen_compl.preimage hj.continuous, hp, Or.inr fun x hx w hw hwe => ?_⟩
        by_contra hge; push Not at hge
        exact hx ⟨w, ⟨subset_closure hw, hge⟩, hwe⟩
    have hclR₁_cpt : IsCompact (closure R₁) :=
      (isCompact_Icc.reProdIm isCompact_Icc).of_isClosed_subset isClosed_closure hR₁_sub_big
    have hclR₂_cpt : IsCompact (closure R₂) :=
      (isCompact_Icc.reProdIm isCompact_Icc).of_isClosed_subset isClosed_closure hR₂_sub_big
    obtain ⟨V₁, hV₁o, hzV₁, hV₁s⟩ := hhalf_miss K₁ R₁ R₁big O₁ hK₁ hR₁_sub_big hR₁Os hR₁O hclR₁_cpt
    obtain ⟨V₂, hV₂o, hzV₂, hV₂s⟩ := hhalf_miss K₂ R₂ R₂big O₂ hK₂ hR₂_sub_big hR₂Os hR₂O hclR₂_cpt
    refine ⟨V₁ ∩ V₂ ∩ Oᶜ, (hV₁o.inter hV₂o).inter hOc.isOpen_compl, ⟨⟨hzV₁, hzV₂⟩, hzO⟩, fun x hx y hy => ?_⟩
    unfold ω
    split_ifs with h1 h2
    · rcases hV₁s with hpos | hneg
      · have hx1 := hpos x hx.1.1 _ (hW₁_pos h1.1).1 (hW₁_pos h1.1).2
        have hy1 := hpos y hy.1.1 _ (hW₁_pos h1.2).1 (hW₁_pos h1.2).2
        simp only [f₁, ite_eq_right hx.2, ite_eq_right hy.2, ite_eq_left hx1, ite_eq_left hy1, sub_self]
      · have hx1 : ¬ 0 < (z₁ x).im := not_lt.mpr (hneg x hx.1.1 _ (hW₁_pos h1.1).1 (hW₁_pos h1.1).2).le
        have hy1 : ¬ 0 < (z₁ y).im := not_lt.mpr (hneg y hy.1.1 _ (hW₁_pos h1.2).1 (hW₁_pos h1.2).2).le
        simp only [f₁, ite_eq_right hx.2, ite_eq_right hy.2, ite_eq_right hx1, ite_eq_right hy1, sub_self]
    · rcases hV₂s with hpos | hneg
      · have hx2 := hpos x hx.1.2 _ (hW₂_pos h2.1).1 (hW₂_pos h2.1).2
        have hy2 := hpos y hy.1.2 _ (hW₂_pos h2.2).1 (hW₂_pos h2.2).2
        simp only [f₂, ite_eq_left hx2, ite_eq_left hy2, sub_self]
      · have hx2 : ¬ 0 < (z₂ x).im := not_lt.mpr (hneg x hx.1.2 _ (hW₂_pos h2.1).1 (hW₂_pos h2.1).2).le
        have hy2 : ¬ 0 < (z₂ y).im := not_lt.mpr (hneg y hy.1.2 _ (hW₂_pos h2.2).1 (hW₂_pos h2.2).2).le
        simp only [f₂, ite_eq_right hx2, ite_eq_right hy2, sub_self]
    · rfl
  -- Verify `ω` is locally a coboundary at EVERY `z ∈ S` (giving `IsCoc ω` immediately!):
  have hω_loc : ∀ z : S, ∃ (U : Set S) (g : S → ZMod 2), IsOpen U ∧ z ∈ U ∧ ∀ x ∈ U, ∀ y ∈ U, ω x y = g y - g x := by
    intro z
    by_cases hzO : z ∈ O
    · by_cases hz1 : z ∈ W₁
      · exact ⟨W₁, f₁, hW₁o, hz1, fun x hx y hy => by unfold ω; rw [ite_eq_left ⟨hx, hy⟩]⟩
      · have hz2 : z ∈ W₂ := (hcov_W z hzO).resolve_left hz1
        have hcl_c : IsClosed (K₁ '' closure R₁) :=
          (((isCompact_Icc.reProdIm isCompact_Icc).of_isClosed_subset isClosed_closure hR₁_sub_big).image_of_continuousOn
            (hK₁.hc.mono (hR₁_sub_big.trans hR₁Os))).isClosed
        by_cases hcl1 : j z ∈ K₁ '' closure R₁
        · obtain ⟨w₁, hw₁c, hw₁e⟩ := hcl1
          have ⟨w₂, hw₂, hw₂e⟩ := hz2
          obtain ⟨U₀, hU₀o, hzU₀, c, hU₀c⟩ := htrans z hzO ⟨w₁, hclR₁_int hw₁c, hw₁e⟩ ⟨w₂, hclR₂_int (subset_closure hw₂), hw₂e⟩
          refine ⟨U₀ ∩ W₂, f₂, hU₀o.inter hW₂o, ⟨hzU₀, hz2⟩, fun x hx y hy => ?_⟩
          unfold ω; split_ifs with h1 h2
          · have e1 := hU₀c x hx.1; have e2 := hU₀c y hy.1; linear_combination e2 - e1
          · rfl
          · exact absurd ⟨hx.2, hy.2⟩ h2
        · refine ⟨W₂ ∩ j ⁻¹' (K₁ '' closure R₁)ᶜ, f₂, hW₂o.inter (hcl_c.isOpen_compl.preimage hj.continuous), ⟨hz2, hcl1⟩,
            fun x hx y hy => ?_⟩
          have hx1 : x ∉ W₁ := fun ⟨w, hw, hwe⟩ => hx.2 ⟨w, subset_closure hw, hwe⟩
          unfold ω; rw [ite_eq_right (fun h => hx1 h.1), ite_eq_left ⟨hx.1, hy.1⟩]
    · obtain ⟨U, hUo, hzU, hU0⟩ := hω_off z hzO
      exact ⟨U, fun _ => 0, hUo, hzU, fun x hx y hy => by rw [hU0 x hx y hy, sub_self]⟩
  have hcoc : IsCoc ω := by
    have hshr : ∀ z : S, ∃ V : Set S, IsOpen V ∧ z ∈ V ∧ closure V ⊆ (hω_loc z).choose := fun z => by
      obtain ⟨V, hVo, hsubV, hclV⟩ := exists_open_closure_subset isClosed_singleton (hω_loc z).choose_spec.choose_spec.1
        (singleton_subset_iff.mpr (hω_loc z).choose_spec.choose_spec.2.1)
      exact ⟨V, hVo, singleton_subset_iff.mp hsubV, hclV⟩
    choose V hVo hzV hVcl using hshr
    obtain ⟨F, hFcov⟩ := isCompact_univ.elim_finite_subcover V hVo (fun x _ => mem_iUnion.mpr ⟨x, hzV x⟩)
    let N : Set (S × S) := ⋂ z ∈ F, (((hω_loc z).choose ×ˢ (hω_loc z).choose) ∪ ((closure (V z))ᶜ ×ˢ (closure (V z))ᶜ))
    refine ⟨N, fun q => ?_, fun x y w h1 h2 h3 => ?_⟩
    · rw [Filter.biInter_finset_mem]
      intro z _
      by_cases hq : q ∈ closure (V z)
      · have hqU : q ∈ (hω_loc z).choose := hVcl z hq
        have hUo : IsOpen (hω_loc z).choose := (hω_loc z).choose_spec.choose_spec.1
        exact Filter.mem_of_superset ((hUo.prod hUo).mem_nhds ⟨hqU, hqU⟩) subset_union_left
      · exact Filter.mem_of_superset ((isClosed_closure.isOpen_compl.prod isClosed_closure.isOpen_compl).mem_nhds ⟨hq, hq⟩) subset_union_right
    · obtain ⟨_, ⟨z, rfl⟩, ⟨_, ⟨hzF, rfl⟩, hyV⟩⟩ := hFcov (mem_univ y)
      have hycl : y ∈ closure (V z) := subset_closure hyV
      have h1z : (x, y) ∈ (hω_loc z).choose ×ˢ (hω_loc z).choose :=
        (mem_iInter₂.mp h1 z hzF).resolve_right fun h => h.2 hycl
      have h2z : (y, w) ∈ (hω_loc z).choose ×ˢ (hω_loc z).choose :=
        (mem_iInter₂.mp h2 z hzF).resolve_right fun h => h.1 hycl
      have hg := (hω_loc z).choose_spec.choose_spec.2.2
      rw [hg x h1z.1 y h1z.2, hg y h2z.1 w h2z.2, hg x h1z.1 w h2z.2]; ring
  refine ⟨⟨ω, hcoc, hω_off, fun z hzO => ?_⟩, htwo⟩
  by_cases hz1 : z ∈ W₁
  · let A : Set S := W₁ ∩ {x : S | 0 < (z₁ x).im}
    let B : Set S := W₁ ∩ {x : S | (z₁ x).im < 0}
    have hA_eq : A = j ⁻¹' (K₁ '' (R₁ ∩ {w : ℂ | 0 < w.im})) := by
      ext x; constructor
      · rintro ⟨hx1, hpos⟩; obtain ⟨hw, hwe⟩ := hW₁_pos hx1; exact ⟨z₁ x, ⟨hw, hpos⟩, hwe⟩
      · rintro ⟨w, ⟨hw, hpos⟩, hwe⟩
        have hx1 : x ∈ W₁ := ⟨w, hw, hwe⟩
        exact ⟨hx1, show 0 < (z₁ x).im by rw [hz₁_eq (hR₁_sub_big (subset_closure hw)) hwe]; exact hpos⟩
    have hB_eq : B = j ⁻¹' (K₁ '' (R₁ ∩ {w : ℂ | w.im < 0})) := by
      ext x; constructor
      · rintro ⟨hx1, hneg⟩; obtain ⟨hw, hwe⟩ := hW₁_pos hx1; exact ⟨z₁ x, ⟨hw, hneg⟩, hwe⟩
      · rintro ⟨w, ⟨hw, hneg⟩, hwe⟩
        have hx1 : x ∈ W₁ := ⟨w, hw, hwe⟩
        exact ⟨hx1, show (z₁ x).im < 0 by rw [hz₁_eq (hR₁_sub_big (subset_closure hw)) hwe]; exact hneg⟩
    have hAo : IsOpen A := by
      rw [hA_eq]; exact (hK₁.ho _ (hR₁o.inter (isOpen_lt continuous_const Complex.continuous_im))
        (inter_subset_left.trans (subset_closure.trans (hR₁_sub_big.trans hR₁Os)))).preimage hj.continuous
    have hBo : IsOpen B := by
      rw [hB_eq]; exact (hK₁.ho _ (hR₁o.inter (isOpen_lt Complex.continuous_im continuous_const))
        (inter_subset_left.trans (subset_closure.trans (hR₁_sub_big.trans hR₁Os)))).preimage hj.continuous
    have hsplit : W₁ \ O = A ∪ B := by
      ext x; constructor
      · rintro ⟨hx1, hxO⟩
        obtain ⟨hw, hwe⟩ := hW₁_pos hx1
        have hne0 : (z₁ x).im ≠ 0 := fun h0 => hxO (by
          obtain ⟨y, hyO, hye⟩ := (hR₁O _ (hR₁_sub_big (subset_closure hw))).mpr h0; exact hji (hye.trans hwe) ▸ hyO)
        rcases lt_or_gt_of_ne hne0 with hlt | hgt
        · exact Or.inr ⟨hx1, hlt⟩
        · exact Or.inl ⟨hx1, hgt⟩
      · rintro (⟨hx1, hgt⟩ | ⟨hx1, hlt⟩)
        · obtain ⟨hw, hwe⟩ := hW₁_pos hx1
          exact ⟨hx1, fun hxO => hgt.ne' ((hR₁O _ (hR₁_sub_big (subset_closure hw))).mp ⟨x, hxO, hwe.symm⟩)⟩
        · obtain ⟨hw, hwe⟩ := hW₁_pos hx1
          exact ⟨hx1, fun hxO => hlt.ne ((hR₁O _ (hR₁_sub_big (subset_closure hw))).mp ⟨x, hxO, hwe.symm⟩)⟩
    have hnear : ∀ U : Set S, IsOpen U → z ∈ U → (U ∩ A).Nonempty ∧ (U ∩ B).Nonempty := fun U hUo hzU => by
      obtain ⟨hw, hwe⟩ := hW₁_pos hz1
      exact strip_near_sides hj hK hcov hK₁ hR₁o hR₁_sub_big hR₁Os hz₁_eq hW₁o hz1 (hO_notK z hzO) hw hwe
        ((hR₁O _ (hR₁_sub_big (subset_closure hw))).mp ⟨z, hzO, hwe.symm⟩) hUo hzU
    refine ⟨W₁, A, B, hW₁o, hz1, hsplit, by rw [Set.disjoint_left]; rintro x ⟨-, h1⟩ ⟨-, h2⟩; change 0 < (z₁ x).im at h1; change (z₁ x).im < 0 at h2; linarith,
      hAo, hBo, hnear, f₁, fun x hx y hy => by unfold ω; rw [ite_eq_left ⟨hx, hy⟩],
      fun x hx y hy => by
        have hxO : x ∉ O := (show x ∈ W₁ \ O from hsplit.symm ▸ Or.inl hx).2
        have hyO : y ∉ O := (show y ∈ W₁ \ O from hsplit.symm ▸ Or.inl hy).2
        simp only [f₁, ite_eq_right hxO, ite_eq_right hyO, ite_eq_left (show 0 < (z₁ x).im from hx.2), ite_eq_left (show 0 < (z₁ y).im from hy.2)],
      fun x hx y hy => by
        have hxO : x ∉ O := (show x ∈ W₁ \ O from hsplit.symm ▸ Or.inr hx).2
        have hyO : y ∉ O := (show y ∈ W₁ \ O from hsplit.symm ▸ Or.inr hy).2
        have h1 : ¬ 0 < (z₁ x).im := not_lt.mpr (show (z₁ x).im < 0 from hx.2).le
        have h2 : ¬ 0 < (z₁ y).im := not_lt.mpr (show (z₁ y).im < 0 from hy.2).le
        simp only [f₁, ite_eq_right hxO, ite_eq_right hyO, ite_eq_right h1, ite_eq_right h2],
      fun x hx y hy => by
        have hxO : x ∉ O := (show x ∈ W₁ \ O from hsplit.symm ▸ Or.inl hx).2
        have hyO : y ∉ O := (show y ∈ W₁ \ O from hsplit.symm ▸ Or.inr hy).2
        have h2 : ¬ 0 < (z₁ y).im := not_lt.mpr (show (z₁ y).im < 0 from hy.2).le
        simp only [f₁, ite_eq_right hxO, ite_eq_right hyO, ite_eq_left (show 0 < (z₁ x).im from hx.2), ite_eq_right h2]; decide⟩
  · have hz2 : z ∈ W₂ := (hcov_W z hzO).resolve_left hz1
    have hU2_ex : ∃ U₂ : Set S, IsOpen U₂ ∧ z ∈ U₂ ∧ U₂ ⊆ W₂ ∧ ∀ x ∈ U₂, ∀ y ∈ U₂, ω x y = f₂ y - f₂ x := by
      have hcl_c : IsClosed (K₁ '' closure R₁) :=
        (((isCompact_Icc.reProdIm isCompact_Icc).of_isClosed_subset isClosed_closure hR₁_sub_big).image_of_continuousOn
          (hK₁.hc.mono (hR₁_sub_big.trans hR₁Os))).isClosed
      by_cases hcl1 : j z ∈ K₁ '' closure R₁
      · obtain ⟨w₁, hw₁c, hw₁e⟩ := hcl1
        have ⟨w₂, hw₂, hw₂e⟩ := hz2
        obtain ⟨U₀, hU₀o, hzU₀, c, hU₀c⟩ := htrans z hzO ⟨w₁, hclR₁_int hw₁c, hw₁e⟩ ⟨w₂, hclR₂_int (subset_closure hw₂), hw₂e⟩
        refine ⟨U₀ ∩ W₂, hU₀o.inter hW₂o, ⟨hzU₀, hz2⟩, inter_subset_right, fun x hx y hy => ?_⟩
        unfold ω; split_ifs with h1 h2
        · have e1 := hU₀c x hx.1; have e2 := hU₀c y hy.1; linear_combination e2 - e1
        · rfl
        · exact absurd ⟨hx.2, hy.2⟩ h2
      · refine ⟨W₂ ∩ j ⁻¹' (K₁ '' closure R₁)ᶜ, hW₂o.inter (hcl_c.isOpen_compl.preimage hj.continuous), ⟨hz2, hcl1⟩,
          inter_subset_left, fun x hx y hy => ?_⟩
        have hx1 : x ∉ W₁ := fun ⟨w, hw, hwe⟩ => hx.2 ⟨w, subset_closure hw, hwe⟩
        unfold ω; rw [ite_eq_right (fun h => hx1 h.1), ite_eq_left ⟨hx.1, hy.1⟩]
    obtain ⟨U₂, hU₂o, hzU₂, hU₂sub, hU₂ω⟩ := hU2_ex
    let A : Set S := U₂ ∩ {x : S | 0 < (z₂ x).im}
    let B : Set S := U₂ ∩ {x : S | (z₂ x).im < 0}
    have hA_eq : A = U₂ ∩ j ⁻¹' (K₂ '' (R₂ ∩ {w : ℂ | 0 < w.im})) := by
      ext x; constructor
      · rintro ⟨hx2, hpos⟩; obtain ⟨hw, hwe⟩ := hW₂_pos (hU₂sub hx2); exact ⟨hx2, z₂ x, ⟨hw, hpos⟩, hwe⟩
      · rintro ⟨hx2, w, ⟨hw, hpos⟩, hwe⟩
        exact ⟨hx2, show 0 < (z₂ x).im by rw [hz₂_eq (hR₂_sub_big (subset_closure hw)) hwe]; exact hpos⟩
    have hB_eq : B = U₂ ∩ j ⁻¹' (K₂ '' (R₂ ∩ {w : ℂ | w.im < 0})) := by
      ext x; constructor
      · rintro ⟨hx2, hneg⟩; obtain ⟨hw, hwe⟩ := hW₂_pos (hU₂sub hx2); exact ⟨hx2, z₂ x, ⟨hw, hneg⟩, hwe⟩
      · rintro ⟨hx2, w, ⟨hw, hneg⟩, hwe⟩
        exact ⟨hx2, show (z₂ x).im < 0 by rw [hz₂_eq (hR₂_sub_big (subset_closure hw)) hwe]; exact hneg⟩
    have hAo : IsOpen A := by
      rw [hA_eq]; exact hU₂o.inter ((hK₂.ho _ (hR₂o.inter (isOpen_lt continuous_const Complex.continuous_im))
        (inter_subset_left.trans (subset_closure.trans (hR₂_sub_big.trans hR₂Os)))).preimage hj.continuous)
    have hBo : IsOpen B := by
      rw [hB_eq]; exact hU₂o.inter ((hK₂.ho _ (hR₂o.inter (isOpen_lt Complex.continuous_im continuous_const))
        (inter_subset_left.trans (subset_closure.trans (hR₂_sub_big.trans hR₂Os)))).preimage hj.continuous)
    have hsplit : U₂ \ O = A ∪ B := by
      ext x; constructor
      · rintro ⟨hx2, hxO⟩
        obtain ⟨hw, hwe⟩ := hW₂_pos (hU₂sub hx2)
        have hne0 : (z₂ x).im ≠ 0 := fun h0 => hxO (by
          obtain ⟨y, hyO, hye⟩ := (hR₂O _ (hR₂_sub_big (subset_closure hw))).mpr h0; exact hji (hye.trans hwe) ▸ hyO)
        rcases lt_or_gt_of_ne hne0 with hlt | hgt
        · exact Or.inr ⟨hx2, hlt⟩
        · exact Or.inl ⟨hx2, hgt⟩
      · rintro (⟨hx2, hgt⟩ | ⟨hx2, hlt⟩)
        · obtain ⟨hw, hwe⟩ := hW₂_pos (hU₂sub hx2)
          exact ⟨hx2, fun hxO => hgt.ne' ((hR₂O _ (hR₂_sub_big (subset_closure hw))).mp ⟨x, hxO, hwe.symm⟩)⟩
        · obtain ⟨hw, hwe⟩ := hW₂_pos (hU₂sub hx2)
          exact ⟨hx2, fun hxO => hlt.ne ((hR₂O _ (hR₂_sub_big (subset_closure hw))).mp ⟨x, hxO, hwe.symm⟩)⟩
    have hnear : ∀ U : Set S, IsOpen U → z ∈ U → (U ∩ A).Nonempty ∧ (U ∩ B).Nonempty := fun U hUo hzU => by
      obtain ⟨hw, hwe⟩ := hW₂_pos hz2
      exact strip_near_sides hj hK hcov hK₂ hR₂o hR₂_sub_big hR₂Os hz₂_eq hU₂o hzU₂ (hO_notK z hzO) hw hwe
        ((hR₂O _ (hR₂_sub_big (subset_closure hw))).mp ⟨z, hzO, hwe.symm⟩) hUo hzU
    refine ⟨U₂, A, B, hU₂o, hzU₂, hsplit, by rw [Set.disjoint_left]; rintro x ⟨-, h1⟩ ⟨-, h2⟩; change 0 < (z₂ x).im at h1; change (z₂ x).im < 0 at h2; linarith,
      hAo, hBo, hnear, f₂, hU₂ω,
      fun x hx y hy => by simp only [f₂, ite_eq_left (show 0 < (z₂ x).im from hx.2), ite_eq_left (show 0 < (z₂ y).im from hy.2)],
      fun x hx y hy => by
        have h1 : ¬ 0 < (z₂ x).im := not_lt.mpr (show (z₂ x).im < 0 from hx.2).le
        have h2 : ¬ 0 < (z₂ y).im := not_lt.mpr (show (z₂ y).im < 0 from hy.2).le
        simp only [f₂, ite_eq_right h1, ite_eq_right h2],
      fun x hx y hy => by
        have h2 : ¬ 0 < (z₂ y).im := not_lt.mpr (show (z₂ y).im < 0 from hy.2).le
        simp only [f₂, ite_eq_left (show 0 < (z₂ x).im from hx.2), ite_eq_right h2]; decide⟩

end OArcCocycle

end GraphMinor.GHR18


