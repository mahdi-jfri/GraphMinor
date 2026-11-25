module

public import GraphMinor.GHR18.ArcCutStruct
public import GraphMinor.Surface.CuffHomeo
public import GraphMinor.Surface.CutParallel

/-!
# Helper lemmas for arc parallelism (`ArcType.lean`)

This file collects the modular building blocks for `parallel_of_cocycle_eq`:
- Path-independence of `cocInt` along an `I`-arc (`cocInt_congr`, `cocInt_eq_of_arc_eq`);
- Circle-homeomorphism lifting and orientation preservation from local monotonicity
  (`preservesCircleOrientation_refl`, `circle_lift_of_orient`, `local_dir_eq_on_interval`,
  `local_dir_eq_on_untouched`, `gap_dir_eq`, `preservesCircleOrientation_of_local_dirs`);
- Combined cuff-matching and arbitrary-direction arc alignment (`exists_homeo_match_cuffs`,
  `exists_align_one_arc_any`, `exists_align_two_arcs_any`);
- Cut-cuff gap structure for the three geometric cases (`gap_into_G_of_hit`, `onesided_cuff_info`,
  `twosided_cuff_info`, `diff_cuff_info`).
-/

@[expose] public section

namespace GraphMinor.GHR18

open Set Topology Function Metric GraphMinor.Surface

universe u

/-! ### Tiny Bool / `ZMod 2` helpers -/

theorem bool_beq_of_zmod2_sub_eq {a b c d : Bool}
    (h : (if a then (0 : ZMod 2) else 1) - (if b then 0 else 1) =
         (if c then (0 : ZMod 2) else 1) - (if d then 0 else 1)) :
    (a == b) = (c == d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

theorem bool_not_eq_beq_of_zmod2 {Δ : ZMod 2} {d d' : Bool}
    (h : (if d then (0 : ZMod 2) else 1) - (if d' then 0 else 1) = Δ) :
    (!decide (Δ ≠ 0)) = (d == d') := by
  subst h; cases d <;> cases d' <;> decide

theorem strictMono_flip_dir {f : ℝ → ℝ} {s : Set ℝ} {fl d d' : Bool}
    (hfl : (!fl) = (d == d'))
    (hf : if d then StrictMonoOn f s else StrictAntiOn f s) :
    if d' then StrictMonoOn (fun u => if fl then -f u else f u) s
    else StrictAntiOn (fun u => if fl then -f u else f u) s := by
  cases fl <;> cases d <;> cases d' <;> simp at hfl hf ⊢
  · exact hf
  · exact hf
  · exact fun a ha b hb h => neg_lt_neg (hf ha hb h)
  · exact fun a ha b hb h => neg_lt_neg (hf ha hb h)

theorem preservesCircleOrientation_refl : PreservesCircleOrientation (Homeomorph.refl Circle) :=
  ⟨id, continuous_id, strictMono_id, fun _ => rfl⟩

/-- Lift a circle homeomorphism with known orientation bit `pres : Bool` to a continuous strictly
monotone real map `l : ℝ → ℝ` satisfying `k (ee r) = ee (l r)` and `l (r + 1) = l r ± 1`. -/
theorem circle_lift_of_orient {k : Circle ≃ₜ Circle} (pres : Bool)
    (hk : if pres then PreservesCircleOrientation k
      else PreservesCircleOrientation ((Homeomorph.inv Circle).trans k)) :
    ∃ l : ℝ → ℝ, Continuous l ∧ (if pres then StrictMono l else StrictAnti l) ∧
      (∀ r : ℝ, k (ee r) = ee (l r)) ∧
      (∀ r : ℝ, l (r + 1) = l r + if pres then 1 else -1) := by
  have hex : ∃ l : ℝ → ℝ, Continuous l ∧ (if pres then StrictMono l else StrictAnti l) ∧
      (∀ r : ℝ, k (ee r) = ee (l r)) := by
    cases pres
    · simp only [Bool.false_eq_true, ↓reduceIte] at hk ⊢
      obtain ⟨l₀, hl₀c, hl₀m, hl₀e⟩ := hk
      refine ⟨fun r => l₀ (2 * Real.pi * (-r)) / (2 * Real.pi),
        (hl₀c.comp (continuous_const.mul continuous_neg)).div_const _,
        fun a b h => div_lt_div_of_pos_right (hl₀m (mul_lt_mul_of_pos_left (neg_lt_neg h) (by positivity))) (by positivity),
        fun r => ?_⟩
      have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
      have h1 : (Homeomorph.inv Circle).trans k (ee (-r)) = Circle.exp (l₀ (2 * Real.pi * (-r))) := by
        simpa only [ee] using hl₀e (2 * Real.pi * (-r))
      have h2 : (Homeomorph.inv Circle) (ee (-r)) = ee r := by
        show (ee (-r))⁻¹ = ee r; unfold ee; rw [mul_neg, Circle.exp_neg, inv_inv]
      simp only [Homeomorph.trans_apply, h2] at h1
      rw [h1]; unfold ee; congr 1; field_simp
    · simp only [↓reduceIte] at hk ⊢
      obtain ⟨l₀, hl₀c, hl₀m, hl₀e⟩ := hk
      refine ⟨fun r => l₀ (2 * Real.pi * r) / (2 * Real.pi),
        (hl₀c.comp (continuous_const.mul continuous_id)).div_const _,
        fun a b h => div_lt_div_of_pos_right (hl₀m (mul_lt_mul_of_pos_left h (by positivity))) (by positivity),
        fun r => ?_⟩
      have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
      have h1 : k (ee r) = Circle.exp (l₀ (2 * Real.pi * r)) := by
        simpa only [ee] using hl₀e (2 * Real.pi * r)
      rw [h1]; unfold ee; congr 1; field_simp
  obtain ⟨l, hlc, hlm, hle⟩ := hex
  refine ⟨l, hlc, hlm, hle, fun r => ?_⟩
  have h1 : ee (l (r + 1)) = ee (l r) := by rw [← hle, ← hle, ee_add_one]
  obtain ⟨j, hj⟩ := ee_eq_iff.mp h1
  have hle1 : |j| ≤ 1 := by
    by_contra hgt; push Not at hgt
    have h2 : 2 ≤ |j| := by omega
    cases pres <;> simp only [Bool.false_eq_true, ↓reduceIte] at hlm
    · have hlt := hlm (lt_add_one r)
      have hjneg : j < 0 := by exact_mod_cast (show (j : ℝ) < 0 by linarith)
      have hj2 : (j : ℝ) ≤ -2 := by have := abs_of_neg hjneg; exact_mod_cast (show j ≤ -2 by omega)
      have hmid : l r - 1 ∈ Ioo (l (r + 1)) (l r) := ⟨by linarith, by linarith⟩
      obtain ⟨x, hx, hxe⟩ := intermediate_value_Ioo' (by linarith : r ≤ r + 1) hlc.continuousOn hmid
      have hee : ee x = ee r := k.injective (by rw [hle, hle, hxe]; exact ee_eq_iff.mpr ⟨-1, by push_cast; ring⟩)
      exact ee_ne hx.1 hx.2 hee.symm
    · have hlt := hlm (lt_add_one r)
      have hjpos : 0 < j := by exact_mod_cast (show (0 : ℝ) < j by linarith)
      have hj2 : (2 : ℝ) ≤ j := by have := abs_of_pos hjpos; exact_mod_cast (show 2 ≤ j by omega)
      have hmid : l r + 1 ∈ Ioo (l r) (l (r + 1)) := ⟨by linarith, by linarith⟩
      obtain ⟨x, hx, hxe⟩ := intermediate_value_Ioo (by linarith : r ≤ r + 1) hlc.continuousOn hmid
      have hee : ee x = ee r := k.injective (by rw [hle, hle, hxe]; exact ee_eq_iff.mpr ⟨1, by push_cast; ring⟩)
      exact ee_ne hx.1 hx.2 hee.symm
  have hj_abs := abs_le.mp hle1
  cases pres <;> simp only [Bool.false_eq_true, ↓reduceIte] at hlm ⊢
  · have : j < 0 := by exact_mod_cast (show (j : ℝ) < 0 by linarith [hlm (lt_add_one r)])
    have hj1 : j = -1 := by omega
    subst hj1; simpa using hj
  · have : 0 < j := by exact_mod_cast (show (0 : ℝ) < j by linarith [hlm (lt_add_one r)])
    have hj1 : j = 1 := by omega
    subst hj1; simpa using hj

/-! ### Section 1: Path-independence of `cocInt` along an `I`-arc -/

section ArcCocInt

variable {S : Type u} [TopologicalSpace S]

/-- Two continuous paths agreeing pointwise on `[0, 1]` have equal cocycle integrals. -/
theorem cocInt_congr {A : Type} [AddCommGroup A] {ω : S → S → A} (hω : IsCoc ω)
    {γ₁ γ₂ : ℝ → S} (hγ₁ : ContinuousOn γ₁ (Icc 0 1)) (hγ₂ : ContinuousOn γ₂ (Icc 0 1))
    (heq : ∀ u ∈ Icc (0 : ℝ) 1, γ₁ u = γ₂ u) : cocInt ω γ₁ = cocInt ω γ₂ := by
  obtain ⟨N, hN, hcoc⟩ := hω
  obtain ⟨n₁, hn₁, h1⟩ := cocInt_eq_sum hN hcoc hγ₁
  obtain ⟨n₂, hn₂, h2⟩ := cocInt_eq_sum hN hcoc hγ₂
  set n := max n₁ n₂
  have hn : 0 < n := lt_of_lt_of_le hn₁ (le_max_left _ _)
  rw [h1 n (le_max_left _ _), h2 n (le_max_right _ _)]
  unfold cocSum
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k < n := Finset.mem_range.mp hk
  have ha : (k : ℝ) / n ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), (div_le_one (Nat.cast_pos.mpr hn)).mpr (by exact_mod_cast hkn.le)⟩
  have hb : ((k + 1 : ℕ) : ℝ) / n ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), (div_le_one (Nat.cast_pos.mpr hn)).mpr (by exact_mod_cast Nat.succ_le_of_lt hkn)⟩
  rw [heq _ ha, heq _ hb]

/-- Any two continuous paths `[0, 1] → F` from `s` to `t` inside an `I`-arc `F` with ends `s, t`
have the same cocycle integral for any local cocycle `ω`. -/
theorem cocInt_eq_of_arc_eq {A : Type} [AddCommGroup A] {ω : S → S → A} (hω : IsCoc ω)
    {F : Set S} {s t : S} (hl : IsLineWithEnds F s t)
    {γ₁ γ₂ : ℝ → S} (hγ₁ : ContinuousOn γ₁ (Icc 0 1)) (hγ₂ : ContinuousOn γ₂ (Icc 0 1))
    (hsub₁ : γ₁ '' Icc 0 1 ⊆ F) (hsub₂ : γ₂ '' Icc 0 1 ⊆ F)
    (h10 : γ₁ 0 = s) (h11 : γ₁ 1 = t) (h20 : γ₂ 0 = s) (h21 : γ₂ 1 = t) :
    cocInt ω γ₁ = cocInt ω γ₂ := by
  obtain ⟨e, he0, he1⟩ := hl
  let cl : ℝ → ℝ := fun x => max 0 (min x 1)
  have hcl_mem : ∀ x : ℝ, cl x ∈ Icc (0 : ℝ) 1 := fun x => ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  have hcl_eq : ∀ {x : ℝ}, x ∈ Icc (0 : ℝ) 1 → cl x = x := fun hx => by
    simp only [cl, min_eq_left hx.2, max_eq_right hx.1]
  have hcl_c : Continuous cl := continuous_const.max (continuous_id.min continuous_const)
  let clampI : ℝ → unitInterval := fun x => ⟨cl x, hcl_mem x⟩
  have hclampI_c : Continuous clampI := Continuous.subtype_mk hcl_c hcl_mem
  let f₁ : ℝ → ℝ := fun u => (e.symm ⟨γ₁ (cl u), hsub₁ ⟨cl u, hcl_mem u, rfl⟩⟩).1
  let f₂ : ℝ → ℝ := fun u => (e.symm ⟨γ₂ (cl u), hsub₂ ⟨cl u, hcl_mem u, rfl⟩⟩).1
  have hf₁c : Continuous f₁ :=
    continuous_subtype_val.comp (e.symm.continuous.comp (Continuous.subtype_mk
      (hγ₁.comp_continuous hcl_c hcl_mem) fun u => hsub₁ ⟨cl u, hcl_mem u, rfl⟩))
  have hf₂c : Continuous f₂ :=
    continuous_subtype_val.comp (e.symm.continuous.comp (Continuous.subtype_mk
      (hγ₂.comp_continuous hcl_c hcl_mem) fun u => hsub₂ ⟨cl u, hcl_mem u, rfl⟩))
  have hf₁m : ∀ u : ℝ, f₁ u ∈ Icc (0 : ℝ) 1 := fun u => (e.symm _).2
  have hf₂m : ∀ u : ℝ, f₂ u ∈ Icc (0 : ℝ) 1 := fun u => (e.symm _).2
  have hf₁e : ∀ u ∈ Icc (0 : ℝ) 1, (e (clampI (f₁ u))).1 = γ₁ u := fun u hu => by
    have h1 : clampI (f₁ u) = e.symm ⟨γ₁ (cl u), hsub₁ ⟨cl u, hcl_mem u, rfl⟩⟩ :=
      Subtype.ext (hcl_eq (hf₁m u))
    rw [h1, e.apply_symm_apply]; dsimp only; exact congrArg γ₁ (hcl_eq hu)
  have hf₂e : ∀ u ∈ Icc (0 : ℝ) 1, (e (clampI (f₂ u))).1 = γ₂ u := fun u hu => by
    have h1 : clampI (f₂ u) = e.symm ⟨γ₂ (cl u), hsub₂ ⟨cl u, hcl_mem u, rfl⟩⟩ :=
      Subtype.ext (hcl_eq (hf₂m u))
    rw [h1, e.apply_symm_apply]; dsimp only; exact congrArg γ₂ (hcl_eq hu)
  have hf10 : f₁ 0 = 0 := by
    have h0 : clampI (f₁ 0) = (0 : unitInterval) :=
      e.injective (Subtype.ext ((hf₁e 0 ⟨le_rfl, zero_le_one⟩).trans (h10.trans he0.symm)))
    have := congrArg Subtype.val h0
    simpa [clampI, hcl_eq (hf₁m 0)] using this
  have hf11 : f₁ 1 = 1 := by
    have h1 : clampI (f₁ 1) = (1 : unitInterval) :=
      e.injective (Subtype.ext ((hf₁e 1 ⟨zero_le_one, le_rfl⟩).trans (h11.trans he1.symm)))
    have := congrArg Subtype.val h1
    simpa [clampI, hcl_eq (hf₁m 1)] using this
  have hf20 : f₂ 0 = 0 := by
    have h0 : clampI (f₂ 0) = (0 : unitInterval) :=
      e.injective (Subtype.ext ((hf₂e 0 ⟨le_rfl, zero_le_one⟩).trans (h20.trans he0.symm)))
    have := congrArg Subtype.val h0
    simpa [clampI, hcl_eq (hf₂m 0)] using this
  have hf21 : f₂ 1 = 1 := by
    have h1 : clampI (f₂ 1) = (1 : unitInterval) :=
      e.injective (Subtype.ext ((hf₂e 1 ⟨zero_le_one, le_rfl⟩).trans (h21.trans he1.symm)))
    have := congrArg Subtype.val h1
    simpa [clampI, hcl_eq (hf₂m 1)] using this
  let H : ℝ → ℝ → S := fun r u => (e (clampI ((1 - r) * f₁ u + r * f₂ u))).1
  have hHc : ContinuousOn (fun p : ℝ × ℝ => H p.1 p.2) (Icc 0 1 ×ˢ Icc 0 1) :=
    (continuous_subtype_val.comp (e.continuous.comp (hclampI_c.comp
      (((continuous_const.sub continuous_fst).mul (hf₁c.comp continuous_snd)).add
       (continuous_fst.mul (hf₂c.comp continuous_snd)))))).continuousOn
  have hH0 : ∀ r ∈ Icc (0 : ℝ) 1, H r 0 = H 0 0 := fun r _ => by simp only [H, hf10, hf20, mul_zero, add_zero]
  have hH1 : ∀ r ∈ Icc (0 : ℝ) 1, H r 1 = H 0 1 := fun r _ => by simp only [H, hf11, hf21, mul_one, sub_add_cancel]
  have hhom := cocInt_homotopy hω hHc hH0 hH1
  have h0eq : ∀ u ∈ Icc (0 : ℝ) 1, H 0 u = γ₁ u := fun u hu => by
    simp only [H, sub_zero, one_mul, zero_mul, add_zero]; exact hf₁e u hu
  have h1eq : ∀ u ∈ Icc (0 : ℝ) 1, H 1 u = γ₂ u := fun u hu => by
    simp only [H, sub_self, zero_mul, one_mul, zero_add]; exact hf₂e u hu
  have hH0c : ContinuousOn (H 0) (Icc 0 1) :=
    (continuous_subtype_val.comp (e.continuous.comp (hclampI_c.comp
      ((continuous_const.mul hf₁c).add (continuous_const.mul hf₂c))))).continuousOn
  have hH1c : ContinuousOn (H 1) (Icc 0 1) :=
    (continuous_subtype_val.comp (e.continuous.comp (hclampI_c.comp
      ((continuous_const.mul hf₁c).add (continuous_const.mul hf₂c))))).continuousOn
  exact (cocInt_congr hω hH0c hγ₁ h0eq).symm.trans (hhom.trans (cocInt_congr hω hH1c hγ₂ h1eq))

end ArcCocInt

/-! ### Section 2: Local direction constancy and circle orientation -/

section LocalDirTools

variable {Y S : Type u} [TopologicalSpace Y] [TopologicalSpace S]

/-- On an open interval `Ioo p q` (`q - p < 1`) where `ψ ∘ φY ∘ ee` stays in `CS \ F`, the local
direction bit relative to `φS` is constant across all `v₁, v₂ ∈ Ioo p q`. -/
theorem local_dir_eq_on_interval {ψ : Y → S} {F : Set S} (hψ : IsCutting ψ F)
    {CY : Set Y} {CS : Set S} (φY : Circle ≃ₜ CY) (φS : Circle ≃ₜ CS)
    {p q : ℝ} (hpq : p < q) (hspan : q - p < 1)
    (hin : ∀ v ∈ Ioo p q, ψ (φY (ee v)).1 ∈ CS ∧ ψ (φY (ee v)).1 ∉ F)
    {v₁ v₂ : ℝ} (hv₁ : v₁ ∈ Ioo p q) (hv₂ : v₂ ∈ Ioo p q)
    {δ₁ δ₂ : ℝ} (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂)
    {m₁ m₂ : ℝ → ℝ} {dir₁ dir₂ : Bool}
    (hm₁c : ContinuousOn m₁ (Icc (-δ₁) δ₁)) (hm₂c : ContinuousOn m₂ (Icc (-δ₂) δ₂))
    (hm₁d : if dir₁ then StrictMonoOn m₁ (Icc (-δ₁) δ₁) else StrictAntiOn m₁ (Icc (-δ₁) δ₁))
    (hm₂d : if dir₂ then StrictMonoOn m₂ (Icc (-δ₂) δ₂) else StrictAntiOn m₂ (Icc (-δ₂) δ₂))
    (he₁ : ∀ r ∈ Icc (-δ₁) δ₁, ψ (φY (ee (v₁ + r))).1 = (φS (ee (m₁ r))).1)
    (he₂ : ∀ r ∈ Icc (-δ₂) δ₂, ψ (φY (ee (v₂ + r))).1 = (φS (ee (m₂ r))).1) :
    dir₁ = dir₂ := by
  set a := min v₁ v₂
  set b := max v₁ v₂
  have ha_in : a ∈ Ioo p q := ⟨lt_min hv₁.1 hv₂.1, (min_le_left _ _).trans_lt hv₁.2⟩
  have hb_in : b ∈ Ioo p q := ⟨hv₁.1.trans_le (le_max_left _ _), max_lt hv₁.2 hv₂.2⟩
  have hab : a ≤ b := min_le_max
  set ε := min (min (a - p) (q - b)) (min δ₁ δ₂) / 2
  have hε : 0 < ε := by
    have h1 : 0 < a - p := sub_pos.mpr ha_in.1
    have h2 : 0 < q - b := sub_pos.mpr hb_in.2
    positivity
  have hε1 : ε ≤ δ₁ := by
    have : ε ≤ min δ₁ δ₂ / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    linarith [min_le_left δ₁ δ₂]
  have hε2 : ε ≤ δ₂ := by
    have : ε ≤ min δ₁ δ₂ / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    linarith [min_le_right δ₁ δ₂]
  have hIsub : Icc (a - ε) (b + ε) ⊆ Ioo p q := fun v hv => by
    have h1 : ε < a - p := lt_of_le_of_lt (div_le_div_of_nonneg_right ((min_le_left _ _).trans (min_le_left _ _)) (by norm_num))
      (half_lt_self (sub_pos.mpr ha_in.1))
    have h2 : ε < q - b := lt_of_le_of_lt (div_le_div_of_nonneg_right ((min_le_left _ _).trans (min_le_right _ _)) (by norm_num))
      (half_lt_self (sub_pos.mpr hb_in.2))
    exact ⟨by linarith [hv.1], by linarith [hv.2]⟩
  have hlt_ab : a - ε < b + ε := by linarith
  let γ : ℝ → S := fun w => ψ (φY (ee (lin (a - ε) (b + ε) w))).1
  have hγc : ContinuousOn γ (Icc 0 1) :=
    hψ.1.comp_continuousOn (continuous_subtype_val.comp (φY.continuous.comp continuous_ee)).continuousOn
      |>.comp (continuousOn_lin _ _) fun _ _ => mem_univ _
  have hγCS : ∀ w ∈ Icc (0 : ℝ) 1, γ w ∈ CS := fun w hw =>
    (hin _ (hIsub ⟨by simp only [lin]; nlinarith [hw.1, hlt_ab], by simp only [lin]; nlinarith [hw.2, hlt_ab]⟩)).1
  obtain ⟨l₀, hl₀c, hl₀e⟩ := exists_lift φS hγc hγCS
  let l : ℝ → ℝ := fun v => l₀ ((v - (a - ε)) / (b + ε - (a - ε)))
  have hlc : ContinuousOn l (Icc (a - ε) (b + ε)) :=
    hl₀c.comp (by fun_prop) fun v hv => ⟨div_nonneg (by linarith [hv.1]) (by linarith),
      (div_le_one (by linarith)).mpr (by linarith [hv.2])⟩
  have hle : ∀ v ∈ Icc (a - ε) (b + ε), (φS (ee (l v))).1 = ψ (φY (ee v)).1 := fun v hv => by
    have hmem : (v - (a - ε)) / (b + ε - (a - ε)) ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (by linarith [hv.1]) (by linarith), (div_le_one (by linarith)).mpr (by linarith [hv.2])⟩
    have h1 := hl₀e _ hmem
    have h2 : lin (a - ε) (b + ε) ((v - (a - ε)) / (b + ε - (a - ε))) = v := by
      simp only [lin]; field_simp [show b + ε - (a - ε) ≠ 0 by linarith]; ring
    simpa only [γ, h2, l] using h1
  have hlinj : InjOn l (Icc (a - ε) (b + ε)) := fun x hx y hy he => by
    have h1 : ψ (φY (ee x)).1 = ψ (φY (ee y)).1 := by rw [← hle x hx, ← hle y hy, he]
    have h2 := hψ.2.2.1 (hin x (hIsub hx)).2 (hin y (hIsub hy)).2 h1
    obtain ⟨k, hk⟩ := ee_eq_iff.mp (φY.injective (Subtype.ext h2))
    have hx' := hIsub hx; have hy' := hIsub hy
    have hklt : |(k : ℝ)| < 1 := by rw [abs_lt]; exact ⟨by linarith [hx'.1, hy'.2], by linarith [hx'.2, hy'.1]⟩
    have hk0 : k = 0 := by have := abs_lt.mp (show |k| < 1 by exact_mod_cast hklt); omega
    subst hk0; simp only [Int.cast_zero, add_zero] at hk; exact hk
  have hl_mo := hlc.strictMonoOn_of_injOn_Icc' hlt_ab.le hlinj
  have hcmp : ∀ (v₀ : ℝ) (hv0 : v₀ ∈ Icc a b) (δ : ℝ) (hεδ : ε ≤ δ) (m : ℝ → ℝ) (dir : Bool),
      ContinuousOn m (Icc (-δ) δ) →
      (if dir then StrictMonoOn m (Icc (-δ) δ) else StrictAntiOn m (Icc (-δ) δ)) →
      (∀ r ∈ Icc (-δ) δ, ψ (φY (ee (v₀ + r))).1 = (φS (ee (m r))).1) →
      (if dir then l v₀ < l (v₀ + ε) else l (v₀ + ε) < l v₀) := by
    intro v₀ hv0 δ hεδ m dir hmc hmd hme
    let d : ℝ → ℝ := fun r => l (v₀ + r) - m r
    have hsub : ∀ r ∈ Icc (0 : ℝ) ε, v₀ + r ∈ Icc (a - ε) (b + ε) := fun r hr =>
      ⟨by linarith [hv0.1, hr.1], by linarith [hv0.2, hr.2]⟩
    have hsubm : ∀ r ∈ Icc (0 : ℝ) ε, r ∈ Icc (-δ) δ := fun r hr => ⟨by linarith [hr.1], by linarith [hr.2]⟩
    have hdc : ContinuousOn d (Icc 0 ε) :=
      (hlc.comp (continuousOn_const.add continuousOn_id) hsub).sub (hmc.mono hsubm)
    have hd_int : ∀ r ∈ Icc (0 : ℝ) ε, ∃ k : ℤ, d r = k := fun r hr => by
      have h1 : (φS (ee (l (v₀ + r)))).1 = (φS (ee (m r))).1 := (hle _ (hsub r hr)).trans (hme r (hsubm r hr))
      obtain ⟨k, hk⟩ := ee_eq_iff.mp (φS.injective (Subtype.ext h1))
      exact ⟨k, by simp only [d]; linarith⟩
    obtain ⟨k0, hk0⟩ := hd_int 0 ⟨le_rfl, hε.le⟩
    have hd_const : ∀ r ∈ Icc (0 : ℝ) ε, d r = k0 := fun r hr => by
      by_contra hne
      have hlt_or : d r < k0 ∨ k0 < d r := lt_or_gt_of_ne hne
      obtain ⟨kr, hkr⟩ := hd_int r hr
      rcases hlt_or with hlt | hgt
      · have hmid : (k0 : ℝ) - 1 / 2 ∈ Icc (d r) (d 0) := by
          have : kr ≤ k0 - 1 := by
            have : kr < k0 := by exact_mod_cast (show (kr : ℝ) < k0 by rw [← hkr]; exact hlt)
            omega
          have : (kr : ℝ) ≤ k0 - 1 := by exact_mod_cast this
          rw [hkr, hk0]; constructor <;> linarith
        obtain ⟨r', hr', hr'e⟩ := intermediate_value_Icc' hr.1 (hdc.mono fun x hx => ⟨hx.1, hx.2.trans hr.2⟩) hmid
        obtain ⟨k', hk'⟩ := hd_int r' ⟨hr'.1, hr'.2.trans hr.2⟩
        have : (2 * k' : ℤ) = 2 * k0 - 1 := by exact_mod_cast (show (2 * k' : ℝ) = 2 * k0 - 1 by linarith [hk', hr'e])
        omega
      · have hmid : (k0 : ℝ) + 1 / 2 ∈ Icc (d 0) (d r) := by
          have : k0 + 1 ≤ kr := by
            have : k0 < kr := by exact_mod_cast (show (k0 : ℝ) < kr by rw [← hkr]; exact hgt)
            omega
          have : (k0 : ℝ) + 1 ≤ kr := by exact_mod_cast this
          rw [hkr, hk0]; constructor <;> linarith
        obtain ⟨r', hr', hr'e⟩ := intermediate_value_Icc hr.1 (hdc.mono fun x hx => ⟨hx.1, hx.2.trans hr.2⟩) hmid
        obtain ⟨k', hk'⟩ := hd_int r' ⟨hr'.1, hr'.2.trans hr.2⟩
        have : (2 * k' : ℤ) = 2 * k0 + 1 := by exact_mod_cast (show (2 * k' : ℝ) = 2 * k0 + 1 by linarith [hk', hr'e])
        omega
    have h0 : l v₀ - m 0 = k0 := by simpa [d] using hd_const 0 ⟨le_rfl, hε.le⟩
    have h1 : l (v₀ + ε) - m ε = k0 := hd_const ε ⟨hε.le, le_rfl⟩
    cases dir
    · simp only [Bool.false_eq_true, ↓reduceIte] at hmd ⊢
      have := hmd (hsubm 0 ⟨le_rfl, hε.le⟩) (hsubm ε ⟨hε.le, le_rfl⟩) hε
      linarith
    · simp only [↓reduceIte] at hmd ⊢
      have := hmd (hsubm 0 ⟨le_rfl, hε.le⟩) (hsubm ε ⟨hε.le, le_rfl⟩) hε
      linarith
  have hc1 := hcmp v₁ ⟨min_le_left _ _, le_max_left _ _⟩ δ₁ hε1 m₁ dir₁ hm₁c hm₁d he₁
  have hc2 := hcmp v₂ ⟨min_le_right _ _, le_max_right _ _⟩ δ₂ hε2 m₂ dir₂ hm₂c hm₂d he₂
  have hv1a : v₁ ∈ Icc (a - ε) (b + ε) := ⟨by linarith [min_le_left v₁ v₂], by linarith [le_max_left v₁ v₂]⟩
  have hv1b : v₁ + ε ∈ Icc (a - ε) (b + ε) := ⟨by linarith [min_le_left v₁ v₂], by linarith [le_max_left v₁ v₂]⟩
  have hv2a : v₂ ∈ Icc (a - ε) (b + ε) := ⟨by linarith [min_le_right v₁ v₂], by linarith [le_max_right v₁ v₂]⟩
  have hv2b : v₂ + ε ∈ Icc (a - ε) (b + ε) := ⟨by linarith [min_le_right v₁ v₂], by linarith [le_max_right v₁ v₂]⟩
  rcases hl_mo with hsm | hsa
  · have h1 := hsm hv1a hv1b (by linarith)
    have h2 := hsm hv2a hv2b (by linarith)
    cases dir₁ <;> cases dir₂ <;> simp only [Bool.false_eq_true, ↓reduceIte] at hc1 hc2 ⊢ <;> linarith
  · have h1 := hsa hv1a hv1b (by linarith)
    have h2 := hsa hv2a hv2b (by linarith)
    cases dir₁ <;> cases dir₂ <;> simp only [Bool.false_eq_true, ↓reduceIte] at hc1 hc2 ⊢ <;> linarith

/-- On an untouched cuff `CY` (completely disjoint from `ψ ⁻¹' F` and mapping into `CS`), the local
direction bit relative to `φS` is constant across all `v₁, v₂ : ℝ`. -/
theorem local_dir_eq_on_untouched {ψ : Y → S} {F : Set S} (hψ : IsCutting ψ F)
    {CY : Set Y} {CS : Set S} (φY : Circle ≃ₜ CY) (φS : Circle ≃ₜ CS)
    (hin : ∀ z : Circle, ψ (φY z).1 ∈ CS ∧ ψ (φY z).1 ∉ F)
    {v₁ v₂ : ℝ} {δ₁ δ₂ : ℝ} (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂)
    {m₁ m₂ : ℝ → ℝ} {dir₁ dir₂ : Bool}
    (hm₁c : ContinuousOn m₁ (Icc (-δ₁) δ₁)) (hm₂c : ContinuousOn m₂ (Icc (-δ₂) δ₂))
    (hm₁d : if dir₁ then StrictMonoOn m₁ (Icc (-δ₁) δ₁) else StrictAntiOn m₁ (Icc (-δ₁) δ₁))
    (hm₂d : if dir₂ then StrictMonoOn m₂ (Icc (-δ₂) δ₂) else StrictAntiOn m₂ (Icc (-δ₂) δ₂))
    (he₁ : ∀ r ∈ Icc (-δ₁) δ₁, ψ (φY (ee (v₁ + r))).1 = (φS (ee (m₁ r))).1)
    (he₂ : ∀ r ∈ Icc (-δ₂) δ₂, ψ (φY (ee (v₂ + r))).1 = (φS (ee (m₂ r))).1) :
    dir₁ = dir₂ := by
  set k : ℤ := ⌊v₂ - v₁ + 1 / 2⌋
  set v₂' := v₂ - k
  have hv2'_ee : ∀ r : ℝ, ee (v₂' + r) = ee (v₂ + r) := fun r =>
    ee_eq_iff.mpr ⟨-k, by simp only [v₂', Int.cast_neg]; ring⟩
  have he₂' : ∀ r ∈ Icc (-δ₂) δ₂, ψ (φY (ee (v₂' + r))).1 = (φS (ee (m₂ r))).1 := fun r hr => by
    rw [hv2'_ee r]; exact he₂ r hr
  have hlo : v₁ - 1 / 2 ≤ v₂' := by have := Int.floor_le (v₂ - v₁ + 1 / 2); simp only [v₂']; linarith
  have hhi : v₂' < v₁ + 1 / 2 := by have := Int.lt_floor_add_one (v₂ - v₁ + 1 / 2); simp only [v₂']; linarith
  by_cases hle : v₁ ≤ v₂'
  · exact local_dir_eq_on_interval hψ φY φS (p := v₁ - 1 / 8) (q := v₁ + 5 / 8) (by linarith) (by linarith)
      (fun v _ => hin (ee v)) ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
      hδ₁ hδ₂ hm₁c hm₂c hm₁d hm₂d he₁ he₂'
  · exact local_dir_eq_on_interval hψ φY φS (p := v₁ - 5 / 8) (q := v₁ + 1 / 8) (by linarith) (by linarith)
      (fun v _ => hin (ee v)) ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
      hδ₁ hδ₂ hm₁c hm₂c hm₁d hm₂d he₁ he₂'

/-- On an open gap `Ioo p q` (`p < q`, `q - p < 1`) avoiding `ψ ⁻¹' F`, if the endpoints map to
`x₁ = φS (ee u₁)` and `x₂ = φS (ee u₂)` (`u₁ < u₂ < u₁ + 1`) and the interior maps into
`(φS ∘ ee) '' Ioo u₁ u₂`, then the local direction bit at any `v₀ ∈ Ioo p q` is `true` if
`p ↦ x₁, q ↦ x₂` and `false` if `p ↦ x₂, q ↦ x₁`. -/
theorem gap_dir_eq {ψ : Y → S} {F : Set S} (hψ : IsCutting ψ F)
    {CY : Set Y} {CS : Set S} (φY : Circle ≃ₜ CY) (φS : Circle ≃ₜ CS)
    {u₁ u₂ : ℝ} (hu12 : u₁ < u₂) (hu21 : u₂ < u₁ + 1)
    {p q : ℝ} (hpq : p < q) (hspan : q - p < 1)
    (hoff : ∀ v ∈ Ioo p q, ψ (φY (ee v)).1 ∉ F)
    (hgap : ∀ v ∈ Ioo p q, ψ (φY (ee v)).1 ∈ (fun w => (φS (ee w)).1) '' Ioo u₁ u₂)
    {v₀ : ℝ} (hv₀ : v₀ ∈ Ioo p q)
    {δ : ℝ} (hδ : 0 < δ) {m : ℝ → ℝ} {dir : Bool}
    (hmc : ContinuousOn m (Icc (-δ) δ))
    (hmd : if dir then StrictMonoOn m (Icc (-δ) δ) else StrictAntiOn m (Icc (-δ) δ))
    (hme : ∀ r ∈ Icc (-δ) δ, ψ (φY (ee (v₀ + r))).1 = (φS (ee (m r))).1) :
    ((ψ (φY (ee p)).1 = (φS (ee u₁)).1 ∧ ψ (φY (ee q)).1 = (φS (ee u₂)).1) → dir = true) ∧
    ((ψ (φY (ee p)).1 = (φS (ee u₂)).1 ∧ ψ (φY (ee q)).1 = (φS (ee u₁)).1) → dir = false) := by
  have hCS_all : ∀ v ∈ Icc p q,
      (ψ (φY (ee p)).1 = (φS (ee u₁)).1 ∧ ψ (φY (ee q)).1 = (φS (ee u₂)).1) ∨
      (ψ (φY (ee p)).1 = (φS (ee u₂)).1 ∧ ψ (φY (ee q)).1 = (φS (ee u₁)).1) →
      ψ (φY (ee v)).1 ∈ CS := fun v hv hend => by
    rcases eq_or_lt_of_le hv.1 with rfl | h1
    · rcases hend with ⟨hp, -⟩ | ⟨hp, -⟩ <;> rw [hp] <;> exact (φS _).2
    · rcases eq_or_lt_of_le hv.2 with rfl | h2
      · rcases hend with ⟨-, hq⟩ | ⟨-, hq⟩ <;> rw [hq] <;> exact (φS _).2
      · obtain ⟨w, -, hw⟩ := hgap v ⟨h1, h2⟩; rw [← hw]; exact (φS _).2
  have hmain : ∀ (b : Bool),
      (if b then ψ (φY (ee p)).1 = (φS (ee u₁)).1 ∧ ψ (φY (ee q)).1 = (φS (ee u₂)).1
       else ψ (φY (ee p)).1 = (φS (ee u₂)).1 ∧ ψ (φY (ee q)).1 = (φS (ee u₁)).1) → dir = b := by
    intro b hend
    have hend' : (ψ (φY (ee p)).1 = (φS (ee u₁)).1 ∧ ψ (φY (ee q)).1 = (φS (ee u₂)).1) ∨
        (ψ (φY (ee p)).1 = (φS (ee u₂)).1 ∧ ψ (φY (ee q)).1 = (φS (ee u₁)).1) := by
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hend
      · exact .inr hend
      · exact .inl hend
    let γ : ℝ → S := fun w => ψ (φY (ee (lin p q w))).1
    have hγc : ContinuousOn γ (Icc 0 1) :=
      (hψ.1.comp_continuousOn (continuous_subtype_val.comp (φY.continuous.comp continuous_ee)).continuousOn).comp
        (continuousOn_lin p q) fun _ _ => mem_univ _
    have hγCS : ∀ w ∈ Icc (0 : ℝ) 1, γ w ∈ CS := fun w hw =>
      hCS_all _ ⟨by simp only [lin]; nlinarith [hw.1, hpq], by simp only [lin]; nlinarith [hw.2, hpq]⟩ hend'
    obtain ⟨l, hlc, hle⟩ := exists_lift φS hγc hγCS
    have hl_inj : InjOn l (Ioo 0 1) := fun w₁ hw₁ w₂ hw₂ he => by
      have h1 : ψ (φY (ee (lin p q w₁))).1 = ψ (φY (ee (lin p q w₂))).1 := by
        have e1 : (φS (ee (l w₁))).1 = ψ (φY (ee (lin p q w₁))).1 := hle w₁ (Ioo_subset_Icc_self hw₁)
        have e2 : (φS (ee (l w₂))).1 = ψ (φY (ee (lin p q w₂))).1 := hle w₂ (Ioo_subset_Icc_self hw₂)
        rw [← e1, ← e2, he]
      have h2 := hψ.2.2.1 (hoff _ (lin_mem hpq.le hw₁ hpq)) (hoff _ (lin_mem hpq.le hw₂ hpq)) h1
      obtain ⟨k, hk⟩ := ee_eq_iff.mp (φY.injective (Subtype.ext h2))
      have hl1 := lin_mem hpq.le hw₁ hpq; have hl2 := lin_mem hpq.le hw₂ hpq
      have hklt : |(k : ℝ)| < 1 := by rw [abs_lt]; exact ⟨by linarith [hl1.1, hl2.2], by linarith [hl1.2, hl2.1]⟩
      have hk0 : k = 0 := by have := abs_lt.mp (show |k| < 1 by exact_mod_cast hklt); omega
      subst hk0; simp only [Int.cast_zero, add_zero] at hk
      exact (strictMonoOn_lin hpq).injOn (Ioo_subset_Icc_self hw₁) (Ioo_subset_Icc_self hw₂) hk
    have hno12 : ∀ w ∈ Ioo (0 : ℝ) 1, ee (l w) ≠ ee u₁ ∧ ee (l w) ≠ ee u₂ := fun w hw => by
      obtain ⟨z, hz, hze⟩ := hgap _ (lin_mem hpq.le hw hpq)
      have h1 : ee (l w) = ee z := φS.injective (Subtype.ext ((hle w (Ioo_subset_Icc_self hw)).trans hze.symm))
      exact ⟨fun h => ee_ne hz.1 (by linarith [hz.2]) (h1.symm.trans h).symm,
             fun h => ee_ne hz.2 (by linarith [hz.1]) (h1.symm.trans h)⟩
    obtain ⟨z₀, hz₀, hz₀e⟩ := hgap _ (lin_mem hpq.le (show (1 / 2 : ℝ) ∈ Ioo 0 1 by norm_num) hpq)
    obtain ⟨k, hk⟩ := ee_eq_iff.mp (φS.injective (Subtype.ext ((hle (1 / 2) (by norm_num)).trans hz₀e.symm)))
    have hl12 : l (1 / 2) ∈ Ioo (u₁ + k) (u₂ + k) := ⟨by linarith [hz₀.1], by linarith [hz₀.2]⟩
    have hl_in : ∀ w ∈ Ioo (0 : ℝ) 1, l w ∈ Ioo (u₁ + k) (u₂ + k) := fun w hw => by
      constructor
      · by_contra hle'
        have hmem : u₁ + k ∈ Icc (l w) (l (1 / 2)) := ⟨not_lt.mp hle', hl12.1.le⟩
        rcases le_total w (1 / 2) with hord | hord
        · obtain ⟨x, hx, hxe⟩ := intermediate_value_Icc hord (hlc.mono fun t ht => ⟨by linarith [ht.1, hw.1], by linarith [ht.2]⟩) hmem
          exact (hno12 x ⟨by linarith [hx.1, hw.1], by linarith [hx.2]⟩).1 (by rw [hxe]; exact ee_eq_iff.mpr ⟨k, rfl⟩)
        · obtain ⟨x, hx, hxe⟩ := intermediate_value_Icc' hord (hlc.mono fun t ht => ⟨by linarith [ht.1], by linarith [ht.2, hw.2]⟩) hmem
          exact (hno12 x ⟨by linarith [hx.1], by linarith [hx.2, hw.2]⟩).1 (by rw [hxe]; exact ee_eq_iff.mpr ⟨k, rfl⟩)
      · by_contra hge'
        have hmem : u₂ + k ∈ Icc (l (1 / 2)) (l w) := ⟨hl12.2.le, not_lt.mp hge'⟩
        rcases le_total (1 / 2) w with hord | hord
        · obtain ⟨x, hx, hxe⟩ := intermediate_value_Icc hord (hlc.mono fun t ht => ⟨by linarith [ht.1], by linarith [ht.2, hw.2]⟩) hmem
          exact (hno12 x ⟨by linarith [hx.1], by linarith [hx.2, hw.2]⟩).2 (by rw [hxe]; exact ee_eq_iff.mpr ⟨k, rfl⟩)
        · obtain ⟨x, hx, hxe⟩ := intermediate_value_Icc' hord (hlc.mono fun t ht => ⟨by linarith [ht.1, hw.1], by linarith [ht.2]⟩) hmem
          exact (hno12 x ⟨by linarith [hx.1, hw.1], by linarith [hx.2]⟩).2 (by rw [hxe]; exact ee_eq_iff.mpr ⟨k, rfl⟩)
    have hl0_in : l 0 ∈ Icc (u₁ + k) (u₂ + k) := by
      by_contra hnot
      rw [mem_Icc, not_and_or, not_le, not_le] at hnot
      rcases hnot with hlt | hgt
      · obtain ⟨r, hr, hrsub⟩ := Metric.continuousWithinAt_iff.mp (hlc 0 ⟨le_rfl, zero_le_one⟩) (u₁ + k - l 0) (by linarith)
        set t := min (r / 2) (1 / 2)
        have ht : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_min (half_pos hr) (by norm_num), (min_le_right _ _).trans_lt (by norm_num)⟩
        have hd := hrsub (Ioo_subset_Icc_self ht) (by rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]; exact (min_le_left _ _).trans_lt (half_lt_self hr))
        rw [Real.dist_eq, abs_lt] at hd; linarith [(hl_in t ht).1]
      · obtain ⟨r, hr, hrsub⟩ := Metric.continuousWithinAt_iff.mp (hlc 0 ⟨le_rfl, zero_le_one⟩) (l 0 - (u₂ + k)) (by linarith)
        set t := min (r / 2) (1 / 2)
        have ht : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_min (half_pos hr) (by norm_num), (min_le_right _ _).trans_lt (by norm_num)⟩
        have hd := hrsub (Ioo_subset_Icc_self ht) (by rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]; exact (min_le_left _ _).trans_lt (half_lt_self hr))
        rw [Real.dist_eq, abs_lt] at hd; linarith [(hl_in t ht).2]
    have hl1_in : l 1 ∈ Icc (u₁ + k) (u₂ + k) := by
      by_contra hnot
      rw [mem_Icc, not_and_or, not_le, not_le] at hnot
      rcases hnot with hlt | hgt
      · obtain ⟨r, hr, hrsub⟩ := Metric.continuousWithinAt_iff.mp (hlc 1 ⟨zero_le_one, le_rfl⟩) (u₁ + k - l 1) (by linarith)
        set t := 1 - min (r / 2) (1 / 2)
        have ht : t ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [min_le_right (r / 2) (1 / 2)], by linarith [lt_min (half_pos hr) (by norm_num : (0 : ℝ) < 1 / 2)]⟩
        have hd := hrsub (Ioo_subset_Icc_self ht) (by rw [Real.dist_eq, show t - 1 = -min (r / 2) (1 / 2) by simp [t], abs_neg, abs_of_pos (lt_min (half_pos hr) (by norm_num))]; exact (min_le_left _ _).trans_lt (half_lt_self hr))
        rw [Real.dist_eq, abs_lt] at hd; linarith [(hl_in t ht).1]
      · obtain ⟨r, hr, hrsub⟩ := Metric.continuousWithinAt_iff.mp (hlc 1 ⟨zero_le_one, le_rfl⟩) (l 1 - (u₂ + k)) (by linarith)
        set t := 1 - min (r / 2) (1 / 2)
        have ht : t ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [min_le_right (r / 2) (1 / 2)], by linarith [lt_min (half_pos hr) (by norm_num : (0 : ℝ) < 1 / 2)]⟩
        have hd := hrsub (Ioo_subset_Icc_self ht) (by rw [Real.dist_eq, show t - 1 = -min (r / 2) (1 / 2) by simp [t], abs_neg, abs_of_pos (lt_min (half_pos hr) (by norm_num))]; exact (min_le_left _ _).trans_lt (half_lt_self hr))
        rw [Real.dist_eq, abs_lt] at hd; linarith [(hl_in t ht).2]
    have hunique1 : ∀ x ∈ Icc (u₁ + k) (u₂ + k), ee x = ee u₁ → x = u₁ + k := fun x hx he => by
      obtain ⟨j, hj⟩ := ee_eq_iff.mp he
      have hjlt : |(j - k : ℝ)| < 1 := by rw [abs_lt]; exact ⟨by linarith [hx.1, hu12, hu21], by linarith [hx.2, hu12, hu21]⟩
      have hjk : j = k := by have := abs_lt.mp (show |j - k| < 1 by exact_mod_cast hjlt); omega
      subst hjk; exact hj
    have hunique2 : ∀ x ∈ Icc (u₁ + k) (u₂ + k), ee x = ee u₂ → x = u₂ + k := fun x hx he => by
      obtain ⟨j, hj⟩ := ee_eq_iff.mp he
      have hjlt : |(j - k : ℝ)| < 1 := by rw [abs_lt]; exact ⟨by linarith [hx.1, hu12, hu21], by linarith [hx.2, hu12, hu21]⟩
      have hjk : j = k := by have := abs_lt.mp (show |j - k| < 1 by exact_mod_cast hjlt); omega
      subst hjk; exact hj
    have h0e : ee (l 0) = ee (if b then u₁ else u₂) := by
      apply φS.injective; apply Subtype.ext
      have h1 : (φS (ee (l 0))).1 = ψ (φY (ee p)).1 := by simpa only [γ, lin_zero] using hle 0 ⟨le_rfl, zero_le_one⟩
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hend ⊢ <;> exact h1.trans hend.1
    have h1e : ee (l 1) = ee (if b then u₂ else u₁) := by
      apply φS.injective; apply Subtype.ext
      have h1 : (φS (ee (l 1))).1 = ψ (φY (ee q)).1 := by simpa only [γ, lin_one] using hle 1 ⟨zero_le_one, le_rfl⟩
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hend ⊢ <;> exact h1.trans hend.2
    have hl0_val : l 0 = (if b then u₁ else u₂) + k := by
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at h0e ⊢
      · exact hunique2 _ hl0_in h0e
      · exact hunique1 _ hl0_in h0e
    have hl1_val : l 1 = (if b then u₂ else u₁) + k := by
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at h1e ⊢
      · exact hunique1 _ hl1_in h1e
      · exact hunique2 _ hl1_in h1e
    have hlinj_all : InjOn l (Icc 0 1) := fun w₁ hw₁ w₂ hw₂ he => by
      rcases eq_or_lt_of_le hw₁.1 with rfl | h1a
      · rcases eq_or_lt_of_le hw₂.1 with rfl | h2a
        · rfl
        · rcases eq_or_lt_of_le hw₂.2 with rfl | h2b
          · exfalso; rw [hl0_val, hl1_val] at he; cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at he <;> linarith
          · exfalso; have := hl_in w₂ ⟨h2a, h2b⟩; rw [← he, hl0_val] at this; cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at this <;> linarith [this.1, this.2]
      · rcases eq_or_lt_of_le hw₁.2 with rfl | h1b
        · rcases eq_or_lt_of_le hw₂.1 with rfl | h2a
          · exfalso; rw [hl0_val, hl1_val] at he; cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at he <;> linarith
          · rcases eq_or_lt_of_le hw₂.2 with rfl | h2b
            · rfl
            · exfalso; have := hl_in w₂ ⟨h2a, h2b⟩; rw [← he, hl1_val] at this; cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at this <;> linarith [this.1, this.2]
        · rcases eq_or_lt_of_le hw₂.1 with rfl | h2a
          · exfalso; have := hl_in w₁ ⟨h1a, h1b⟩; rw [he, hl0_val] at this; cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at this <;> linarith [this.1, this.2]
          · rcases eq_or_lt_of_le hw₂.2 with rfl | h2b
            · exfalso; have := hl_in w₁ ⟨h1a, h1b⟩; rw [he, hl1_val] at this; cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at this <;> linarith [this.1, this.2]
            · exact hl_inj ⟨h1a, h1b⟩ ⟨h2a, h2b⟩ he
    have hl_mo := hlc.strictMonoOn_of_injOn_Icc' zero_le_one hlinj_all
    have hl_dir : if b then StrictMonoOn l (Icc 0 1) else StrictAntiOn l (Icc 0 1) := by
      rcases hl_mo with hsm | hsa
      · have h01 := hsm ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one
        rw [hl0_val, hl1_val] at h01
        cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at h01 ⊢
        · linarith
        · exact hsm
      · have h01 := hsa ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one
        rw [hl0_val, hl1_val] at h01
        cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at h01 ⊢
        · exact hsa
        · linarith
    set ε' := min (v₀ - p) (q - v₀) / 2
    have hε' : 0 < ε' := half_pos (lt_min (sub_pos.mpr hv₀.1) (sub_pos.mpr hv₀.2))
    let m' : ℝ → ℝ := fun r => l ((v₀ + r - p) / (q - p))
    have hmap : MapsTo (fun r => (v₀ + r - p) / (q - p)) (Icc (-ε') ε') (Icc 0 1) := fun r hr => by
      have h1 : ε' < v₀ - p := (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)).trans_lt (half_lt_self (sub_pos.mpr hv₀.1))
      have h2 : ε' < q - v₀ := (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)).trans_lt (half_lt_self (sub_pos.mpr hv₀.2))
      exact ⟨div_nonneg (by linarith [hr.1]) (by linarith), (div_le_one (by linarith)).mpr (by linarith [hr.2])⟩
    have hm'c : ContinuousOn m' (Icc (-ε') ε') := hlc.comp (by fun_prop) hmap
    have hm'd : if b then StrictMonoOn m' (Icc (-ε') ε') else StrictAntiOn m' (Icc (-ε') ε') := by
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hl_dir ⊢ <;>
        exact fun x hx y hy hxy => hl_dir (hmap hx) (hmap hy) (div_lt_div_of_pos_right (by linarith) (by linarith))
    have hm'e : ∀ r ∈ Icc (-ε') ε', ψ (φY (ee (v₀ + r))).1 = (φS (ee (m' r))).1 := fun r hr => by
      have h1 := hle _ (hmap hr)
      have h2 : lin p q ((v₀ + r - p) / (q - p)) = v₀ + r := by
        simp only [lin]; field_simp [show q - p ≠ 0 by linarith]; ring
      simpa only [γ, h2, m'] using h1.symm
    exact local_dir_eq_on_interval hψ φY φS hpq hspan (fun v hv => ⟨(hCS_all v (Ioo_subset_Icc_self hv) hend'), hoff v hv⟩)
      hv₀ hv₀ hδ hε' hmc hm'c hmd hm'd hme hm'e
  exact ⟨hmain true, hmain false⟩

/-- If `α : S ≃ₜ S` descends from `H : Y ≃ₜ Y'`, preserves cuff `D`, and at one point `v₀` of `φY`
with `H (φY (ee v₀)) = φY' (ee v₀')` the circle action `kH` of `H` (`pres : Bool` = orientation-preserving)
matches the local directions `dir₁, dir₂` of `ψ ∘ φY` and `ψ' ∘ φY'` (i.e., `pres = (dir₁ == dir₂)`),
then `α` preserves the orientation of `D`. -/
theorem preservesCircleOrientation_of_local_dirs
    {Y' : Type u} [TopologicalSpace Y']
    {ψ : Y → S} {ψ' : Y' → S} {H : Y ≃ₜ Y'} {α : S ≃ₜ S}
    (hα : ∀ y, α (ψ y) = ψ' (H y))
    {D : Set S} (hαD : ∀ x, x ∈ D ↔ α x ∈ D) (φS : Circle ≃ₜ D)
    {CY : Set Y} {CY' : Set Y'} (φY : Circle ≃ₜ CY) (φY' : Circle ≃ₜ CY')
    {kH : Circle ≃ₜ Circle} (pres : Bool)
    (hkH_orient : if pres then PreservesCircleOrientation kH
      else PreservesCircleOrientation ((Homeomorph.inv Circle).trans kH))
    (hkH_eq : ∀ z : Circle, H (φY z).1 = (φY' (kH z)).1)
    {v₀ v₀' : ℝ} (hv0 : kH (ee v₀) = ee v₀')
    {δ₁ δ₂ : ℝ} (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂)
    {m₁ m₂ : ℝ → ℝ} {dir₁ dir₂ : Bool}
    (hm₁c : ContinuousOn m₁ (Icc (-δ₁) δ₁)) (hm₂c : ContinuousOn m₂ (Icc (-δ₂) δ₂))
    (hm₁d : if dir₁ then StrictMonoOn m₁ (Icc (-δ₁) δ₁) else StrictAntiOn m₁ (Icc (-δ₁) δ₁))
    (hm₂d : if dir₂ then StrictMonoOn m₂ (Icc (-δ₂) δ₂) else StrictAntiOn m₂ (Icc (-δ₂) δ₂))
    (he₁ : ∀ r ∈ Icc (-δ₁) δ₁, ψ (φY (ee (v₀ + r))).1 = (φS (ee (m₁ r))).1)
    (he₂ : ∀ r ∈ Icc (-δ₂) δ₂, ψ' (φY' (ee (v₀' + r))).1 = (φS (ee (m₂ r))).1)
    (hmatch : pres = (dir₁ == dir₂)) :
    ∃ h : Circle ≃ₜ Circle, PreservesCircleOrientation h ∧ ∀ z, α (φS z).1 = (φS (h z)).1 := by
  let αD : D ≃ₜ D := α.subtype hαD
  let h : Circle ≃ₜ Circle := φS.trans (αD.trans φS.symm)
  have hh_eq : ∀ z : Circle, α (φS z).1 = (φS (h z)).1 := fun z => by
    simp only [h, αD, Homeomorph.trans_apply, Homeomorph.apply_symm_apply]; rfl
  obtain ⟨lH₀, hlH₀c, hlH₀m, hlH₀e, _⟩ := circle_lift_of_orient pres hkH_orient
  obtain ⟨kshift, hkshift⟩ := ee_eq_iff.mp ((hlH₀e v₀).symm.trans hv0)
  let lH : ℝ → ℝ := fun v => lH₀ v - kshift
  have hlHc : Continuous lH := hlH₀c.sub continuous_const
  have hlHm : if pres then StrictMono lH else StrictAnti lH := by
    cases pres <;> simp only [Bool.false_eq_true, ↓reduceIte] at hlH₀m ⊢ <;>
      exact fun a b hab => sub_lt_sub_right (hlH₀m hab) _
  have hlHe : ∀ v : ℝ, kH (ee v) = ee (lH v) := fun v => (hlH₀e v).trans (ee_eq_iff.mpr ⟨kshift, by simp only [lH]; ring⟩)
  have hlH0 : lH v₀ = v₀' := by simp only [lH]; linarith
  -- Shrink `δ' ≤ δ₁` so `|lH (v₀ + r) - v₀'| ≤ δ₂` AND `|m₁ r - m₁ 0| < 1 / 4` (giving `p 1 - p 0 < 1`):
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.continuousAt_iff.mp (hlHc.continuousAt (x := v₀)) δ₂ hδ₂
  obtain ⟨ρ₁, hρ₁, hρ₁sub⟩ := Metric.continuousWithinAt_iff.mp (hm₁c 0 ⟨by linarith, hδ₁.le⟩) (1 / 4) (by norm_num)
  set δ' := min δ₁ (min (ρ / 2) (ρ₁ / 2))
  have hδ' : 0 < δ' := lt_min hδ₁ (lt_min (half_pos hρ) (half_pos hρ₁))
  have hδ'1 : δ' ≤ δ₁ := min_le_left _ _
  have hsub1 : Icc (-δ') δ' ⊆ Icc (-δ₁) δ₁ := fun r hr => ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hlH_in : ∀ r ∈ Icc (-δ') δ', lH (v₀ + r) - v₀' ∈ Icc (-δ₂) δ₂ := fun r hr => by
    have hd : dist (v₀ + r) v₀ < ρ := by
      rw [Real.dist_eq, add_sub_cancel_left, abs_lt]
      have : δ' < ρ := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (half_lt_self hρ)
      exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
    have h2 := hρsub hd; rw [hlH0, Real.dist_eq, abs_lt] at h2; exact ⟨h2.1.le, h2.2.le⟩
  have hm₁_span : |m₁ δ' - m₁ (-δ')| < 1 := by
    have hδ'ρ₁ : δ' < ρ₁ := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (half_lt_self hρ₁)
    have h1 := hρ₁sub (hsub1 ⟨by linarith, le_rfl⟩) (by rw [Real.dist_eq, sub_zero, abs_of_pos hδ']; exact hδ'ρ₁)
    have h2 := hρ₁sub (hsub1 ⟨le_rfl, by linarith⟩) (by rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos hδ']; exact hδ'ρ₁)
    rw [Real.dist_eq, abs_lt] at h1 h2; rw [abs_lt]; constructor <;> linarith
  let g : ℝ → ℝ := fun r => m₂ (lH (v₀ + r) - v₀')
  have hgc : ContinuousOn g (Icc (-δ') δ') :=
    hm₂c.comp ((hlHc.comp (continuous_const.add continuous_id)).sub continuous_const).continuousOn hlH_in
  have hge : ∀ r ∈ Icc (-δ') δ', h (ee (m₁ r)) = ee (g r) := fun r hr => by
    apply φS.injective; apply Subtype.ext
    rw [← hh_eq, ← he₁ r (hsub1 hr), hα, hkH_eq, hlHe,
        show lH (v₀ + r) = v₀' + (lH (v₀ + r) - v₀') by ring, he₂ _ (hlH_in r hr)]
  have hgd : if dir₁ then StrictMonoOn g (Icc (-δ') δ') else StrictAntiOn g (Icc (-δ') δ') := by
    subst hmatch
    cases dir₁ <;> cases dir₂ <;> simp at hlHm hm₂d ⊢
    · exact fun a ha b hb hab => hm₂d (hlH_in a ha) (hlH_in b hb) (sub_lt_sub_right (hlHm (by linarith)) _)
    · exact fun a ha b hb hab => hm₂d (hlH_in b hb) (hlH_in a ha) (sub_lt_sub_right (hlHm (by linarith)) _)
    · exact fun a ha b hb hab => hm₂d (hlH_in b hb) (hlH_in a ha) (sub_lt_sub_right (hlHm (by linarith)) _)
    · exact fun a ha b hb hab => hm₂d (hlH_in a ha) (hlH_in b hb) (sub_lt_sub_right (hlHm (by linarith)) _)
  cases dir₁
  · simp only [Bool.false_eq_true, ↓reduceIte] at hm₁d hgd
    let p : ℝ → ℝ := fun t => m₁ (lin δ' (-δ') t)
    let q : ℝ → ℝ := fun t => g (lin δ' (-δ') t)
    have hmap : MapsTo (lin δ' (-δ')) (Icc 0 1) (Icc (-δ') δ') := fun t ht =>
      ⟨by simp only [lin]; nlinarith [ht.2, hδ'], by simp only [lin]; nlinarith [ht.1, hδ']⟩
    have hpc : ContinuousOn p (Icc 0 1) := (hm₁c.mono hsub1).comp (continuousOn_lin _ _) hmap
    have hpm : StrictMonoOn p (Icc 0 1) := fun a ha b hb hab =>
      hm₁d (hsub1 (hmap hb)) (hsub1 (hmap ha)) (by simp only [lin]; nlinarith)
    have hqc : ContinuousOn q (Icc 0 1) := hgc.comp (continuousOn_lin _ _) hmap
    have hqm : StrictMonoOn q (Icc 0 1) := fun a ha b hb hab =>
      hgd (hmap hb) (hmap ha) (by simp only [lin]; nlinarith)
    obtain ⟨pinv, hpinvc, hpinvm, hpinvl, hpinvr⟩ := exists_inv_strictMonoOn hpc hpm
    have hp01 : p 0 < p 1 := hpm ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one
    have hpspan : p 1 - p 0 < 1 := by
      simp only [p, lin_zero, lin_one]; linarith [(abs_lt.mp hm₁_span).1]
    have hpinv_maps : MapsTo pinv (Icc (p 0) (p 1)) (Icc 0 1) := fun x hx =>
      ⟨by rw [← hpinvl 0 ⟨le_rfl, zero_le_one⟩]; exact hpinvm.monotoneOn ⟨le_rfl, hp01.le⟩ hx hx.1,
       by rw [← hpinvl 1 ⟨zero_le_one, le_rfl⟩]; exact hpinvm.monotoneOn hx ⟨hp01.le, le_rfl⟩ hx.2⟩
    refine ⟨h, preservesCircleOrientation_of_local_mono hp01 hpspan (hqc.comp hpinvc hpinv_maps)
      (fun x hx y hy hxy => hqm (hpinv_maps hx) (hpinv_maps hy) (hpinvm hx hy hxy))
      (fun x hx => ?_), hh_eq⟩
    have h1 := hge (lin δ' (-δ') (pinv x)) (hmap (hpinv_maps hx))
    have h2 : p (pinv x) = x := hpinvr x hx
    change h (ee (p (pinv x))) = ee (q (pinv x)) at h1
    rwa [h2] at h1
  · simp only [↓reduceIte] at hm₁d hgd
    let p : ℝ → ℝ := fun t => m₁ (lin (-δ') δ' t)
    let q : ℝ → ℝ := fun t => g (lin (-δ') δ' t)
    have hmap : MapsTo (lin (-δ') δ') (Icc 0 1) (Icc (-δ') δ') := fun t ht =>
      ⟨by simp only [lin]; nlinarith [ht.1, hδ'], by simp only [lin]; nlinarith [ht.2, hδ']⟩
    have hpc : ContinuousOn p (Icc 0 1) := (hm₁c.mono hsub1).comp (continuousOn_lin _ _) hmap
    have hpm : StrictMonoOn p (Icc 0 1) := fun a ha b hb hab =>
      hm₁d (hsub1 (hmap ha)) (hsub1 (hmap hb)) (by simp only [lin]; nlinarith)
    have hqc : ContinuousOn q (Icc 0 1) := hgc.comp (continuousOn_lin _ _) hmap
    have hqm : StrictMonoOn q (Icc 0 1) := fun a ha b hb hab =>
      hgd (hmap ha) (hmap hb) (by simp only [lin]; nlinarith)
    obtain ⟨pinv, hpinvc, hpinvm, hpinvl, hpinvr⟩ := exists_inv_strictMonoOn hpc hpm
    have hp01 : p 0 < p 1 := hpm ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one
    have hpspan : p 1 - p 0 < 1 := by
      simp only [p, lin_zero, lin_one]; linarith [(abs_lt.mp hm₁_span).2]
    have hpinv_maps : MapsTo pinv (Icc (p 0) (p 1)) (Icc 0 1) := fun x hx =>
      ⟨by rw [← hpinvl 0 ⟨le_rfl, zero_le_one⟩]; exact hpinvm.monotoneOn ⟨le_rfl, hp01.le⟩ hx hx.1,
       by rw [← hpinvl 1 ⟨zero_le_one, le_rfl⟩]; exact hpinvm.monotoneOn hx ⟨hp01.le, le_rfl⟩ hx.2⟩
    refine ⟨h, preservesCircleOrientation_of_local_mono hp01 hpspan (hqc.comp hpinvc hpinv_maps)
      (fun x hx y hy hxy => hqm (hpinv_maps hx) (hpinv_maps hy) (hpinvm hx hy hxy))
      (fun x hx => ?_), hh_eq⟩
    have h1 := hge (lin (-δ') δ' (pinv x)) (hmap (hpinv_maps hx))
    have h2 : p (pinv x) = x := hpinvr x hx
    change h (ee (p (pinv x))) = ee (q (pinv x)) at h1
    rwa [h2] at h1

end LocalDirTools

/-! ### Section 3: Cuff-matching and arbitrary-direction arc alignment -/

section MatchAndAlign

variable {Y Y' : Type u} [TopologicalSpace Y] [T2Space Y] [TopologicalSpace Y'] [T2Space Y']

/-- Combined cuff-matching homeomorphism between two surfaces presented by `ew a b c`:
permutes cuffs by `π : Equiv.Perm (Fin c)` and flips cuffs according to `flip : Fin c → Bool`
(requiring `flip` to be constant when `b = 0`). -/
theorem exists_homeo_match_cuffs {a b c : ℕ} {f : ℕ × ℂ → Y} {f' : ℕ × ℂ → Y'}
    (hf : Presents (sW (ew a b c)) f) (hf' : Presents (sW (ew a b c)) f')
    (π : Equiv.Perm (Fin c)) (flip : Fin c → Bool)
    (hconst : b = 0 → ∀ i j : Fin c, flip i = flip j) :
    ∃ H : Y ≃ₜ Y', ∀ i : Fin c, ∀ z : Circle,
      H (holeParam hf i.isLt z).1 = (holeParam hf' (π i).isLt (if flip i then z⁻¹ else z)).1 := by
  obtain ⟨hP, hhP⟩ := exists_homeo_perm_cuffs hf hf' π
  have hfrom_holeP : ∀ (H : Y ≃ₜ Y'),
      (∀ i : Fin c, ∀ u ∈ Icc (0 : ℝ) 1,
        H (holeP a b c f i.1 u) = holeP a b c f' (π i).1 (if flip i then 1 - u else u)) →
      ∀ i : Fin c, ∀ z : Circle,
        H (holeParam hf i.isLt z).1 = (holeParam hf' (π i).isLt (if flip i then z⁻¹ else z)).1 := by
    intro H hH i z
    obtain ⟨u, hu, rfl⟩ := exists_param z
    rw [holeParam_ee hf i.isLt (Ico_subset_Icc_self hu), hH i u (Ico_subset_Icc_self hu)]
    cases hfi : flip i
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact (holeParam_ee hf' (π i).isLt (Ico_subset_Icc_self hu)).symm
    · simp only [↓reduceIte]
      have hinv : (ee u)⁻¹ = ee (1 - u) := by
        unfold ee; rw [← Circle.exp_neg, eq_comm]
        have : ee (1 - u) = ee (-u) := ee_eq_iff.mpr ⟨1, by push_cast; ring⟩
        unfold ee at this; rw [this, mul_neg]
      rw [hinv]
      exact (holeParam_ee hf' (π i).isLt (rev_mem (Ico_subset_Icc_self hu))).symm
  cases b with
  | zero =>
    by_cases hc : c = 0
    · subst hc; exact ⟨hP, fun i => Fin.elim0 i⟩
    · let i0 : Fin c := ⟨0, Nat.pos_of_ne_zero hc⟩
      cases hf0 : flip i0
      · refine ⟨hP, hfrom_holeP hP fun i u hu => ?_⟩
        rw [hconst rfl i i0, hf0]; simp only [Bool.false_eq_true, ↓reduceIte]; exact hhP i u hu
      · obtain ⟨hR, hhR⟩ := exists_homeo_reverse_all_cuffs hf'
        refine ⟨hP.trans hR, hfrom_holeP (hP.trans hR) fun i u hu => ?_⟩
        rw [hconst rfl i i0, hf0]; simp only [↓reduceIte, Homeomorph.trans_apply]
        rw [hhP i u hu]; exact hhR (π i).1 (π i).isLt u hu
  | succ b' =>
    let flip' : Fin c → Bool := fun j => flip (π.symm j)
    obtain ⟨hF, hhF⟩ := exists_homeo_flip_cuffs hf' flip'
    refine ⟨hP.trans hF, hfrom_holeP (hP.trans hF) fun i u hu => ?_⟩
    simp only [Homeomorph.trans_apply]
    rw [hhP i u hu, hhF (π i) u hu]
    simp [flip']

omit [T2Space Y] in
/-- Align one arc `p` onto `q` on cuff `C` via an orientation-preserving `M : Y ≃ₜ Y` fixing all
other cuffs, when `p` and `q` have the same monotonicity `dir`. -/
theorem exists_align_one_arc_any (hY : IsSurface Y) {C : Set Y} (hC : C ∈ cuffs Y) (φ : Circle ≃ₜ C)
    {p q : ℝ → ℝ} (dir : Bool)
    (hpc : ContinuousOn p (Icc 0 1)) (hqc : ContinuousOn q (Icc 0 1))
    (hpd : if dir then StrictMonoOn p (Icc 0 1) else StrictAntiOn p (Icc 0 1))
    (hqd : if dir then StrictMonoOn q (Icc 0 1) else StrictAntiOn q (Icc 0 1))
    (hp_inj : InjOn (fun u => ee (p u)) (Icc 0 1)) (hq_inj : InjOn (fun u => ee (q u)) (Icc 0 1)) :
    ∃ M : Y ≃ₜ Y,
      (∀ u ∈ Icc (0 : ℝ) 1, M (φ (ee (p u))).1 = (φ (ee (q u))).1) ∧
      (∀ D ∈ cuffs Y, D ≠ C → ∀ y ∈ D, M y = y) ∧
      (∃ k : Circle ≃ₜ Circle, PreservesCircleOrientation k ∧ ∀ x, M (φ x).1 = (φ (k x)).1) := by
  cases dir
  · simp only [Bool.false_eq_true, ↓reduceIte] at hpd hqd
    let p' : ℝ → ℝ := fun u => p (1 - u)
    let q' : ℝ → ℝ := fun u => q (1 - u)
    have hp'c : ContinuousOn p' (Icc 0 1) := hpc.comp (by fun_prop) fun _ hu => rev_mem hu
    have hq'c : ContinuousOn q' (Icc 0 1) := hqc.comp (by fun_prop) fun _ hu => rev_mem hu
    have hp'm : StrictMonoOn p' (Icc 0 1) := fun a ha b hb h => hpd (rev_mem hb) (rev_mem ha) (by linarith)
    have hq'm : StrictMonoOn q' (Icc 0 1) := fun a ha b hb h => hqd (rev_mem hb) (rev_mem ha) (by linarith)
    have hp'i : InjOn (fun u => ee (p' u)) (Icc 0 1) := fun a ha b hb he => by
      have := hp_inj (rev_mem ha) (rev_mem hb) he; linarith
    have hq'i : InjOn (fun u => ee (q' u)) (Icc 0 1) := fun a ha b hb he => by
      have := hq_inj (rev_mem ha) (rev_mem hb) he; linarith
    obtain ⟨M, hM1, hM2, hM3⟩ := exists_align_one_arc hY hC φ hp'c hp'm hq'c hq'm
      (lift_lt_add_one hp'c hp'm hp'i) (lift_lt_add_one hq'c hq'm hq'i)
    refine ⟨M, fun u hu => ?_, hM2, hM3⟩
    have := hM1 (1 - u) (rev_mem hu)
    simpa only [p', q', sub_sub_cancel] using this
  · simp only [↓reduceIte] at hpd hqd
    exact exists_align_one_arc hY hC φ hpc hpd hqc hqd
      (lift_lt_add_one hpc hpd hp_inj) (lift_lt_add_one hqc hqd hq_inj)

omit [T2Space Y] in
/-- Align two disjoint arcs `(p₁, p₂)` onto two disjoint arcs `(q₁, q₂)` on cuff `C` via an
orientation-preserving `M : Y ≃ₜ Y` fixing all other cuffs, when `p₁, q₁` have the same monotonicity
`dir₁` and `p₂, q₂` have the same monotonicity `dir₂`. -/
theorem exists_align_two_arcs_any (hY : IsSurface Y) {C : Set Y} (hC : C ∈ cuffs Y) (φ : Circle ≃ₜ C)
    {p₁ p₂ q₁ q₂ : ℝ → ℝ} (dir₁ dir₂ : Bool)
    (hp₁c : ContinuousOn p₁ (Icc 0 1)) (hp₂c : ContinuousOn p₂ (Icc 0 1))
    (hq₁c : ContinuousOn q₁ (Icc 0 1)) (hq₂c : ContinuousOn q₂ (Icc 0 1))
    (hp₁d : if dir₁ then StrictMonoOn p₁ (Icc 0 1) else StrictAntiOn p₁ (Icc 0 1))
    (hp₂d : if dir₂ then StrictMonoOn p₂ (Icc 0 1) else StrictAntiOn p₂ (Icc 0 1))
    (hq₁d : if dir₁ then StrictMonoOn q₁ (Icc 0 1) else StrictAntiOn q₁ (Icc 0 1))
    (hq₂d : if dir₂ then StrictMonoOn q₂ (Icc 0 1) else StrictAntiOn q₂ (Icc 0 1))
    (hp₁i : InjOn (fun u => ee (p₁ u)) (Icc 0 1)) (hp₂i : InjOn (fun u => ee (p₂ u)) (Icc 0 1))
    (hq₁i : InjOn (fun u => ee (q₁ u)) (Icc 0 1)) (hq₂i : InjOn (fun u => ee (q₂ u)) (Icc 0 1))
    (hpdj : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1, ee (p₁ u) ≠ ee (p₂ v))
    (hqdj : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1, ee (q₁ u) ≠ ee (q₂ v)) :
    ∃ M : Y ≃ₜ Y,
      (∀ u ∈ Icc (0 : ℝ) 1, M (φ (ee (p₁ u))).1 = (φ (ee (q₁ u))).1) ∧
      (∀ u ∈ Icc (0 : ℝ) 1, M (φ (ee (p₂ u))).1 = (φ (ee (q₂ u))).1) ∧
      (∀ D ∈ cuffs Y, D ≠ C → ∀ y ∈ D, M y = y) ∧
      (∃ k : Circle ≃ₜ Circle, PreservesCircleOrientation k ∧ ∀ x, M (φ x).1 = (φ (k x)).1) := by
  let flipU : Bool → ℝ → ℝ := fun d u => if d then u else 1 - u
  have hflip_mem : ∀ d {u : ℝ}, u ∈ Icc (0 : ℝ) 1 → flipU d u ∈ Icc (0 : ℝ) 1 := fun d _ hu => by
    cases d <;> simp [flipU, hu, rev_mem hu]
  have hflip_inv : ∀ d u, flipU d (flipU d u) = u := fun d u => by cases d <;> simp [flipU]
  have hflip_c : ∀ d, ContinuousOn (flipU d) (Icc 0 1) := fun d => by
    cases d <;> simp only [flipU, Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  have hmake_mono : ∀ (d : Bool) (r : ℝ → ℝ),
      ContinuousOn r (Icc 0 1) →
      (if d then StrictMonoOn r (Icc 0 1) else StrictAntiOn r (Icc 0 1)) →
      InjOn (fun u => ee (r u)) (Icc 0 1) →
      ContinuousOn (fun u => r (flipU d u)) (Icc 0 1) ∧
      StrictMonoOn (fun u => r (flipU d u)) (Icc 0 1) ∧
      InjOn (fun u => ee (r (flipU d u))) (Icc 0 1) := by
    intro d r hrc hrd hri
    refine ⟨hrc.comp (hflip_c d) fun _ hu => hflip_mem d hu, ?_, fun a ha b hb he => ?_⟩
    · cases d <;> simp only [flipU, Bool.false_eq_true, ↓reduceIte] at hrd ⊢
      · exact fun a ha b hb hab => hrd (rev_mem hb) (rev_mem ha) (by linarith)
      · exact hrd
    · have h1 := hri (hflip_mem d ha) (hflip_mem d hb) he
      cases d <;> simp only [flipU, Bool.false_eq_true, ↓reduceIte] at h1 <;> linarith
  obtain ⟨hp₁'c, hp₁'m, hp₁'i⟩ := hmake_mono dir₁ p₁ hp₁c hp₁d hp₁i
  obtain ⟨hp₂'c, hp₂'m, hp₂'i⟩ := hmake_mono dir₂ p₂ hp₂c hp₂d hp₂i
  obtain ⟨hq₁'c, hq₁'m, hq₁'i⟩ := hmake_mono dir₁ q₁ hq₁c hq₁d hq₁i
  obtain ⟨hq₂'c, hq₂'m, hq₂'i⟩ := hmake_mono dir₂ q₂ hq₂c hq₂d hq₂i
  let p₁' : ℝ → ℝ := fun u => p₁ (flipU dir₁ u)
  let p₂' : ℝ → ℝ := fun u => p₂ (flipU dir₂ u)
  let q₁' : ℝ → ℝ := fun u => q₁ (flipU dir₁ u)
  let q₂' : ℝ → ℝ := fun u => q₂ (flipU dir₂ u)
  have hord_of : ∀ (a₁ a₂ : ℝ → ℝ),
      ContinuousOn a₁ (Icc 0 1) → StrictMonoOn a₁ (Icc 0 1) → InjOn (fun u => ee (a₁ u)) (Icc 0 1) →
      ContinuousOn a₂ (Icc 0 1) → StrictMonoOn a₂ (Icc 0 1) → InjOn (fun u => ee (a₂ u)) (Icc 0 1) →
      (∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1, ee (a₁ u) ≠ ee (a₂ v)) →
      ∃ k : ℤ, a₁ 1 < a₂ 0 + k ∧ a₂ 1 + k < a₁ 0 + 1 := by
    intro a₁ a₂ ha₁c ha₁m ha₁i ha₂c ha₂m ha₂i hdj
    obtain ⟨k, _, hord⟩ := exists_two_lifts_order φ ha₁c ha₁m (fun _ _ => rfl) ha₂c (.inl ha₂m) (fun _ _ => rfl)
      (fun u hu v hv he => ha₁i hu hv (φ.injective (Subtype.ext he)))
      (fun u hu v hv he => ha₂i hu hv (φ.injective (Subtype.ext he)))
      (fun u hu v hv he => hdj u hu v hv (φ.injective (Subtype.ext he)))
    rcases hord with ⟨-, _, h12, _, h34⟩ | ⟨ha, -⟩
    · exact ⟨k, h12, h34⟩
    · exact absurd (ha ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one)
        (not_lt.mpr (ha₂m ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one).le)
  obtain ⟨kp, hkp1, hkp2⟩ := hord_of p₁' p₂' hp₁'c hp₁'m hp₁'i hp₂'c hp₂'m hp₂'i
    (fun u hu v hv => hpdj _ (hflip_mem dir₁ hu) _ (hflip_mem dir₂ hv))
  obtain ⟨kq, hkq1, hkq2⟩ := hord_of q₁' q₂' hq₁'c hq₁'m hq₁'i hq₂'c hq₂'m hq₂'i
    (fun u hu v hv => hqdj _ (hflip_mem dir₁ hu) _ (hflip_mem dir₂ hv))
  obtain ⟨M, hM1, hM2, hM3, hM4⟩ := exists_align_two_arcs hY hC φ
    hp₁'c hp₁'m (p₂ := fun u => p₂' u + kp) (hp₂'c.add continuousOn_const) (fun a ha b hb h => by dsimp only; linarith [hp₂'m ha hb h])
    hq₁'c hq₁'m (q₂ := fun u => q₂' u + kq) (hq₂'c.add continuousOn_const) (fun a ha b hb h => by dsimp only; linarith [hq₂'m ha hb h])
    hkp1 hkp2 hkq1 hkq2
  refine ⟨M, fun u hu => ?_, fun u hu => ?_, hM3, hM4⟩
  · have := hM1 (flipU dir₁ u) (hflip_mem dir₁ hu)
    simpa only [p₁', q₁', hflip_inv] using this
  · have := hM2 (flipU dir₂ u) (hflip_mem dir₂ hu)
    have hkp : ee (p₂' (flipU dir₂ u) + kp) = ee (p₂ u) := by
      rw [show p₂' (flipU dir₂ u) = p₂ u by simp [p₂', hflip_inv]]
      exact ee_eq_iff.mpr ⟨kp, rfl⟩
    have hkq : ee (q₂' (flipU dir₂ u) + kq) = ee (q₂ u) := by
      rw [show q₂' (flipU dir₂ u) = q₂ u by simp [q₂', hflip_inv]]
      exact ee_eq_iff.mpr ⟨kq, rfl⟩
    rwa [hkp, hkq] at this

end MatchAndAlign

/-! ### Section 4: Cut-cuff gap structure helpers -/

section CutCuffInfo

variable {Z S : Type u} [TopologicalSpace Z] [T2Space Z] [TopologicalSpace S]

/-- Any open gap `Ioo p q` avoiding `FZ` with endpoints over `{s, t}` (`C_s = C_t`) that hits
`(φS ∘ ee) '' Ioo u₁ u₂` maps completely into `(φS ∘ ee) '' Ioo u₁ u₂`. -/
theorem gap_into_G_of_hit (hZ : IsSurface Z) (hS : IsSurface S)
    {ψZ : Z → S} {FZ : Set S} {s t : S} (hψZ : IsCutting ψZ FZ) (hFZ : IsClosed FZ)
    (hbZ : FZ ∩ bd S = {s, t})
    (_hsame : connectedComponentIn (bd S) s = connectedComponentIn (bd S) t)
    (φS : Circle ≃ₜ connectedComponentIn (bd S) s)
    {CZ : Set Z} (hCZ_bd : CZ ⊆ bd Z) (φZ : Circle ≃ₜ CZ)
    {p q : ℝ} (hpq : p < q) (hoff : ∀ v ∈ Ioo p q, ψZ (φZ (ee v)).1 ∉ FZ)
    (hend : (ψZ (φZ (ee p)).1 = s ∧ ψZ (φZ (ee q)).1 = t) ∨ (ψZ (φZ (ee p)).1 = t ∧ ψZ (φZ (ee q)).1 = s))
    {u₁ u₂ : ℝ} (_hu12 : u₁ < u₂) (_hu21 : u₂ < u₁ + 1)
    (hx12 : (φS (ee u₁)).1 ∈ ({s, t} : Set S) ∧ (φS (ee u₂)).1 ∈ ({s, t} : Set S) ∧ (φS (ee u₁)).1 ≠ (φS (ee u₂)).1)
    (hhit : ∃ v₀ ∈ Ioo p q, ψZ (φZ (ee v₀)).1 ∈ (fun w => (φS (ee w)).1) '' Ioo u₁ u₂) :
    ∀ v ∈ Ioo p q, ψZ (φZ (ee v)).1 ∈ (fun w => (φS (ee w)).1) '' Ioo u₁ u₂ := by
  have hsb : s ∈ bd S := (show s ∈ FZ ∩ bd S from hbZ ▸ mem_insert _ _).2
  have htb : t ∈ bd S := (show t ∈ FZ ∩ bd S from hbZ ▸ mem_insert_of_mem _ rfl).2
  obtain ⟨v₀, hv₀, w₀, hw₀, hw₀e⟩ := hhit
  intro v hv
  have hgap_c : ContinuousOn (fun w => ψZ (φZ (ee w)).1) (Icc p q) :=
    hψZ.1.comp_continuousOn (continuous_subtype_val.comp (φZ.continuous.comp continuous_ee)).continuousOn
  have hgap_bd : (fun z => ψZ (φZ (ee z)).1) '' Icc p q ⊆ bd S := by
    rintro _ ⟨z, hz, rfl⟩; dsimp only
    rcases eq_or_lt_of_le hz.1 with rfl | h1
    · rcases hend with ⟨hp, -⟩ | ⟨hp, -⟩ <;> [exact hp.symm ▸ hsb; exact hp.symm ▸ htb]
    · rcases eq_or_lt_of_le hz.2 with rfl | h2
      · rcases hend with ⟨-, hq⟩ | ⟨-, hq⟩ <;> [exact hq.symm ▸ htb; exact hq.symm ▸ hsb]
      · exact (mem_bd_cut_iff hZ hS hψZ hFZ (hoff z ⟨h1, h2⟩)).mp (hCZ_bd (φZ _).2)
  have hgap_CS : ∀ w ∈ Icc p q, ψZ (φZ (ee w)).1 ∈ connectedComponentIn (bd S) s := fun w hw => by
    have hsub := (isPreconnected_Icc.image (fun z => ψZ (φZ (ee z)).1) hgap_c).subset_connectedComponentIn
      (by
        rcases hend with ⟨hp, -⟩ | ⟨-, hq⟩
        · exact ⟨p, ⟨le_rfl, hpq.le⟩, hp⟩
        · exact ⟨q, ⟨hpq.le, le_rfl⟩, hq⟩)
      hgap_bd
    exact hsub ⟨w, hw, rfl⟩
  obtain ⟨l, hlc, hle⟩ := exists_lift φS (hgap_c.comp (continuousOn_lin p q)
    fun w hw => ⟨by simp only [lin]; nlinarith [hw.1, hpq], by simp only [lin]; nlinarith [hw.2, hpq]⟩)
    (fun w hw => hgap_CS _ ⟨by simp only [lin]; nlinarith [hw.1, hpq], by simp only [lin]; nlinarith [hw.2, hpq]⟩)
  let toW : ℝ → ℝ := fun x => (x - p) / (q - p)
  have hlin_toW : ∀ x, lin p q (toW x) = x := fun x => by simp only [lin, toW]; field_simp [show q - p ≠ 0 by linarith]; ring
  have htoW_mem : ∀ x ∈ Ioo p q, toW x ∈ Ioo (0 : ℝ) 1 := fun x hx =>
    ⟨div_pos (by linarith [hx.1]) (by linarith), (div_lt_one (by linarith)).mpr (by linarith [hx.2])⟩
  have hl_no : ∀ w ∈ Ioo (0 : ℝ) 1, ee (l w) ≠ ee u₁ ∧ ee (l w) ≠ ee u₂ := fun w hw => by
    have hlv : (φS (ee (l w))).1 = ψZ (φZ (ee (lin p q w))).1 := hle w (Ioo_subset_Icc_self hw)
    have hoffw := hoff _ (lin_mem hpq.le hw hpq)
    refine ⟨fun h => hoffw ?_, fun h => hoffw ?_⟩
    · rw [← hlv, h]; rcases hx12.1 with h1 | h1 <;> rw [h1]
      · exact (show s ∈ FZ ∩ bd S from hbZ ▸ mem_insert _ _).1
      · exact (show t ∈ FZ ∩ bd S from hbZ ▸ mem_insert_of_mem _ rfl).1
    · rw [← hlv, h]; rcases hx12.2.1 with h2 | h2 <;> rw [h2]
      · exact (show s ∈ FZ ∩ bd S from hbZ ▸ mem_insert _ _).1
      · exact (show t ∈ FZ ∩ bd S from hbZ ▸ mem_insert_of_mem _ rfl).1
  have hlv0_e : ee (l (toW v₀)) = ee w₀ := by
    apply φS.injective; apply Subtype.ext
    have h1 : (φS (ee (l (toW v₀)))).1 = ψZ (φZ (ee (lin p q (toW v₀)))).1 :=
      hle _ (Ioo_subset_Icc_self (htoW_mem v₀ hv₀))
    rw [h1, hlin_toW, ← hw₀e]
  obtain ⟨k, hk⟩ := ee_eq_iff.mp hlv0_e
  have hlm : l (toW v₀) ∈ Ioo (u₁ + k) (u₂ + k) := ⟨by linarith [hw₀.1], by linarith [hw₀.2]⟩
  have hwm := htoW_mem v₀ hv₀
  have hwv := htoW_mem v hv
  have hlv_in : l (toW v) ∈ Ioo (u₁ + k) (u₂ + k) := by
    constructor
    · by_contra hle'
      have hmem : u₁ + k ∈ Icc (l (toW v)) (l (toW v₀)) := ⟨not_lt.mp hle', hlm.1.le⟩
      rcases le_total (toW v) (toW v₀) with hord | hord
      · obtain ⟨w, hw, hwe⟩ := intermediate_value_Icc hord (hlc.mono fun x hx => ⟨by linarith [hx.1, hwv.1], by linarith [hx.2, hwm.2]⟩) hmem
        exact (hl_no w ⟨by linarith [hw.1, hwv.1], by linarith [hw.2, hwm.2]⟩).1 (by rw [hwe]; exact ee_eq_iff.mpr ⟨k, rfl⟩)
      · obtain ⟨w, hw, hwe⟩ := intermediate_value_Icc' hord (hlc.mono fun x hx => ⟨by linarith [hx.1, hwm.1], by linarith [hx.2, hwv.2]⟩) hmem
        exact (hl_no w ⟨by linarith [hw.1, hwm.1], by linarith [hw.2, hwv.2]⟩).1 (by rw [hwe]; exact ee_eq_iff.mpr ⟨k, rfl⟩)
    · by_contra hge'
      have hmem : u₂ + k ∈ Icc (l (toW v₀)) (l (toW v)) := ⟨hlm.2.le, not_lt.mp hge'⟩
      rcases le_total (toW v₀) (toW v) with hord | hord
      · obtain ⟨w, hw, hwe⟩ := intermediate_value_Icc hord (hlc.mono fun x hx => ⟨by linarith [hx.1, hwm.1], by linarith [hx.2, hwv.2]⟩) hmem
        exact (hl_no w ⟨by linarith [hw.1, hwm.1], by linarith [hw.2, hwv.2]⟩).2 (by rw [hwe]; exact ee_eq_iff.mpr ⟨k, rfl⟩)
      · obtain ⟨w, hw, hwe⟩ := intermediate_value_Icc' hord (hlc.mono fun x hx => ⟨by linarith [hx.1, hwv.1], by linarith [hx.2, hwm.2]⟩) hmem
        exact (hl_no w ⟨by linarith [hw.1, hwv.1], by linarith [hw.2, hwm.2]⟩).2 (by rw [hwe]; exact ee_eq_iff.mpr ⟨k, rfl⟩)
  refine ⟨l (toW v) - k, ⟨by linarith [hlv_in.1], by linarith [hlv_in.2]⟩, ?_⟩
  have hee : ee (l (toW v) - k) = ee (l (toW v)) := ee_eq_iff.mpr ⟨-k, by push_cast; ring⟩
  have h1 : (φS (ee (l (toW v)))).1 = ψZ (φZ (ee (lin p q (toW v)))).1 :=
    hle _ (Ioo_subset_Icc_self (htoW_mem v hv))
  dsimp only; rw [hee, h1, hlin_toW]

/-- Gap structure for a 1-sided same-cuff cutting (`C_s = C_t`, `C_ξ = C_η`): both lifts run in the
same direction `dl` (which equals the local direction at any point over `G₁`), and `v_1` lies in one
of the two gaps `(p₁, q₁)` or `(p₂, q₂)`. -/
theorem onesided_cuff_info (hZ : IsSurface Z) (hS : IsSurface S)
    {ψZ : Z → S} {FZ : Set S} {s t : S} (hne : s ≠ t) (hψZ : IsCutting ψZ FZ) (hFZ : IsClosed FZ)
    (hbZ : FZ ∩ bd S = {s, t})
    {XZ XZ' : Set Z} (hPZ : LiftPair ψZ FZ s t XZ XZ')
    {aZ : ℝ → S} {ξZ ηZ : ℝ → Z} (LZ : ArcLift ψZ FZ aZ ξZ ηZ)
    (haZ0 : aZ 0 = s) (haZ1 : aZ 1 = t)
    (him1 : ξZ '' Icc 0 1 = XZ) (him2 : ηZ '' Icc 0 1 = XZ')
    (hi1 : InjOn ξZ (Icc 0 1)) (hi2 : InjOn ηZ (Icc 0 1))
    (hsame : connectedComponentIn (bd S) s = connectedComponentIn (bd S) t)
    (φS : Circle ≃ₜ connectedComponentIn (bd S) s)
    {u_s u_t : ℝ} (hu1 : u_s < u_t) (hu2 : u_t < u_s + 1)
    (hus : (φS (ee u_s)).1 = s) (hut : (φS (ee u_t)).1 = t)
    {CZ : Set Z} (hCZ : CZ ∈ cuffs Z) (φZ : Circle ≃ₜ CZ)
    {m₁ m₂ : ℝ → ℝ}
    (hm1c : ContinuousOn m₁ (Icc 0 1)) (hm1e : ∀ u ∈ Icc (0 : ℝ) 1, (φZ (ee (m₁ u))).1 = ξZ u)
    (hm2c : ContinuousOn m₂ (Icc 0 1)) (hm2e : ∀ u ∈ Icc (0 : ℝ) 1, (φZ (ee (m₂ u))).1 = ηZ u)
    {x₁ : S} (hx₁G₁ : x₁ ∈ (fun v => (φS (ee v)).1) '' Ioo u_t (u_s + 1)) (hx₁_bd : x₁ ∈ bd S \ {s, t})
    {v_1 : ℝ} (hv_1ψ : ψZ (φZ (ee v_1)).1 = x₁)
    {δ : ℝ} (hδ : 0 < δ) {ml : ℝ → ℝ} {dl : Bool}
    (hmlc : ContinuousOn ml (Icc (-δ) δ))
    (hmld : if dl then StrictMonoOn ml (Icc (-δ) δ) else StrictAntiOn ml (Icc (-δ) δ))
    (hmle : ∀ r ∈ Icc (-δ) δ, ψZ (φZ (ee (v_1 + r))).1 = (φS (ee (ml r))).1) :
    (if dl then StrictMonoOn m₁ (Icc 0 1) else StrictAntiOn m₁ (Icc 0 1)) ∧
    (if dl then StrictMonoOn m₂ (Icc 0 1) else StrictAntiOn m₂ (Icc 0 1)) ∧
    ∃ (k : ℤ) (g1 : Bool),
      (let p₁ := if dl then m₁ 1 else m₁ 0
       let q₁ := if dl then m₂ 0 + k else m₂ 1 + k
       let p₂ := if dl then m₂ 1 + k else m₂ 0 + k
       let q₂ := if dl then m₁ 0 + 1 else m₁ 1 + 1
       p₁ < q₁ ∧ q₁ - p₁ < 1 ∧ p₂ < q₂ ∧ q₂ - p₂ < 1 ∧
       (∀ v ∈ Ioo p₁ q₁, ψZ (φZ (ee v)).1 ∉ FZ) ∧
       (∀ v ∈ Ioo p₂ q₂, ψZ (φZ (ee v)).1 ∉ FZ) ∧
       (if g1 then (∃ v ∈ Ioo p₁ q₁, ee v = ee v_1) ∧ (∀ v ∈ Ioo p₁ q₁, ψZ (φZ (ee v)).1 ∈ (fun w => (φS (ee w)).1) '' Ioo u_t (u_s + 1))
        else (∃ v ∈ Ioo p₂ q₂, ee v = ee v_1) ∧ (∀ v ∈ Ioo p₂ q₂, ψZ (φZ (ee v)).1 ∈ (fun w => (φS (ee w)).1) '' Ioo u_t (u_s + 1)))) := by
  obtain ⟨_, _, _, _, _, _, hdZ, hunZ, -⟩ := id hPZ
  have hCZ_bd : CZ ⊆ bd Z := by obtain ⟨z, -, rfl⟩ := hCZ; exact connectedComponentIn_subset _ _
  have hdjZ : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1, ξZ u ≠ ηZ v := fun u hu v hv he =>
    Set.disjoint_left.mp hdZ (show ξZ u ∈ XZ from him1 ▸ ⟨u, hu, rfl⟩) (he ▸ show ηZ v ∈ XZ' from him2 ▸ ⟨v, hv, rfl⟩)
  have hmo1 := lift_mono hm1c (inj_of_lift hm1e hi1)
  have hboth_dir : ∃ dm : Bool,
      (if dm then StrictMonoOn m₁ (Icc 0 1) else StrictAntiOn m₁ (Icc 0 1)) ∧
      (if dm then StrictMonoOn m₂ (Icc 0 1) else StrictAntiOn m₂ (Icc 0 1)) := by
    rcases hmo1 with hm1m | hm1a
    · exact ⟨true, hm1m, (cut_single_cuff_dirs hZ hS hne hψZ hFZ hbZ hPZ LZ haZ0 haZ1 him1 him2 hi1 hi2 hCZ φZ hm1c hm1m hm1e hm2c hm2e).2 hsame⟩
    · let φZr : Circle ≃ₜ CZ := (Homeomorph.inv Circle).trans φZ
      have hinv_e : ∀ r : ℝ, (φZr (ee (-r))).1 = (φZ (ee r)).1 := fun r => by
        simp only [φZr, Homeomorph.trans_apply]; change (φZ (ee (-r))⁻¹).1 = _
        rw [show (ee (-r))⁻¹ = ee r by unfold ee; rw [mul_neg, Circle.exp_neg, inv_inv]]
      have hm2m' := (cut_single_cuff_dirs hZ hS hne hψZ hFZ hbZ hPZ LZ haZ0 haZ1 him1 him2 hi1 hi2 hCZ φZr
        hm1c.neg (fun a ha b hb h => neg_lt_neg (hm1a ha hb h)) (fun u hu => (hinv_e _).trans (hm1e u hu))
        hm2c.neg (fun u hu => (hinv_e _).trans (hm2e u hu))).2 hsame
      exact ⟨false, hm1a, fun a ha b hb h => lt_of_neg_lt_neg (hm2m' ha hb h)⟩
  obtain ⟨dm, hdm1, hdm2⟩ := hboth_dir
  have hord_ex : ∃ k : ℤ,
      let p₁ := if dm then m₁ 1 else m₁ 0
      let q₁ := if dm then m₂ 0 + k else m₂ 1 + k
      let p₂ := if dm then m₂ 1 + k else m₂ 0 + k
      let q₂ := if dm then m₁ 0 + 1 else m₁ 1 + 1
      (if dm then m₁ 0 < m₁ 1 else m₁ 1 < m₁ 0) ∧
      p₁ < q₁ ∧ (if dm then m₂ 0 + k < m₂ 1 + k else m₂ 1 + k < m₂ 0 + k) ∧ p₂ < q₂ := by
    cases dm
    · simp only [Bool.false_eq_true, ↓reduceIte] at hdm1 hdm2 ⊢
      let n₁ : ℝ → ℝ := fun u => m₁ (1 - u)
      let n₂ : ℝ → ℝ := fun u => m₂ (1 - u)
      have hn1c : ContinuousOn n₁ (Icc 0 1) := hm1c.comp (by fun_prop) fun _ hu => rev_mem hu
      have hn2c : ContinuousOn n₂ (Icc 0 1) := hm2c.comp (by fun_prop) fun _ hu => rev_mem hu
      have hn1m : StrictMonoOn n₁ (Icc 0 1) := fun a ha b hb h => hdm1 (rev_mem hb) (rev_mem ha) (by linarith)
      have hn2m : StrictMonoOn n₂ (Icc 0 1) := fun a ha b hb h => hdm2 (rev_mem hb) (rev_mem ha) (by linarith)
      obtain ⟨k, _, hord⟩ := exists_two_lifts_order φZ hn1c hn1m (fun u hu => hm1e _ (rev_mem hu))
        hn2c (.inl hn2m) (fun u hu => hm2e _ (rev_mem hu))
        (fun a ha b hb he => by have := hi1 (rev_mem ha) (rev_mem hb) he; linarith)
        (fun a ha b hb he => by have := hi2 (rev_mem ha) (rev_mem hb) he; linarith)
        (fun u hu v hv => hdjZ _ (rev_mem hu) _ (rev_mem hv))
      rcases hord with ⟨-, h1, h2, h3, h4⟩ | ⟨ha, -⟩
      · exact ⟨k, by simpa [n₁] using h1, by simpa [n₁, n₂] using h2, by simpa [n₂] using h3, by simpa [n₁, n₂] using h4⟩
      · exact absurd (ha ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one)
          (not_lt.mpr (hn2m ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one).le)
    · simp only [↓reduceIte] at hdm1 hdm2 ⊢
      obtain ⟨k, _, hord⟩ := exists_two_lifts_order φZ hm1c hdm1 hm1e hm2c (.inl hdm2) hm2e hi1 hi2 hdjZ
      rcases hord with ⟨-, h1, h2, h3, h4⟩ | ⟨ha, -⟩
      · exact ⟨k, h1, h2, h3, h4⟩
      · exact absurd (ha ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one)
          (not_lt.mpr (hdm2 ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one).le)
  obtain ⟨k, h01, h12, h23, h34⟩ := hord_ex
  set p₁ := if dm then m₁ 1 else m₁ 0
  set q₁ := if dm then m₂ 0 + k else m₂ 1 + k
  set p₂ := if dm then m₂ 1 + k else m₂ 0 + k
  set q₂ := if dm then m₁ 0 + 1 else m₁ 1 + 1
  set a₀v := if dm then m₁ 0 else m₁ 1
  have hq2_eq : q₂ = a₀v + 1 := by cases dm <;> rfl
  have hspan1 : q₁ - p₁ < 1 := by
    cases dm <;> simp only [p₁, q₁, p₂, q₂, Bool.false_eq_true, ↓reduceIte] at h01 h12 h23 h34 ⊢ <;> linarith
  have hspan2 : q₂ - p₂ < 1 := by
    cases dm <;> simp only [p₁, q₁, p₂, q₂, Bool.false_eq_true, ↓reduceIte] at h01 h12 h23 h34 ⊢ <;> linarith
  have hoff1 : ∀ v ∈ Ioo p₁ q₁, ψZ (φZ (ee v)).1 ∉ FZ := fun v hv hF' => by
    rcases (hunZ.symm ▸ hF' : (φZ (ee v)).1 ∈ XZ ∪ XZ') with hx | hx'
    · obtain ⟨u, hu, hu'⟩ := him1.symm.subset hx
      have h1 := φZ.injective (Subtype.ext ((hm1e u hu).trans hu'))
      cases dm <;> simp only [p₁, q₁, p₂, q₂, Bool.false_eq_true, ↓reduceIte] at hdm1 hv h01 h12 h23 h34
      · exact ee_ne (by linarith [hv.1, hdm1.antitoneOn ⟨le_rfl, zero_le_one⟩ hu hu.1])
          (by linarith [hv.2, hdm1.antitoneOn hu ⟨zero_le_one, le_rfl⟩ hu.2]) h1
      · exact ee_ne (by linarith [hv.1, hdm1.monotoneOn hu ⟨zero_le_one, le_rfl⟩ hu.2])
          (by linarith [hv.2, hdm1.monotoneOn ⟨le_rfl, zero_le_one⟩ hu hu.1]) h1
    · obtain ⟨u, hu, hu'⟩ := him2.symm.subset hx'
      have h1 : ee (m₂ u + k) = ee v := (ee_eq_iff.mpr ⟨k, rfl⟩).trans (φZ.injective (Subtype.ext ((hm2e u hu).trans hu')))
      cases dm <;> simp only [p₁, q₁, p₂, q₂, Bool.false_eq_true, ↓reduceIte] at hdm2 hv h01 h12 h23 h34
      · exact ee_ne (by linarith [hv.2, hdm2.antitoneOn hu ⟨zero_le_one, le_rfl⟩ hu.2])
          (by linarith [hv.1, hdm2.antitoneOn ⟨le_rfl, zero_le_one⟩ hu hu.1]) h1.symm
      · exact ee_ne (by linarith [hv.2, hdm2.monotoneOn ⟨le_rfl, zero_le_one⟩ hu hu.1])
          (by linarith [hv.1, hdm2.monotoneOn hu ⟨zero_le_one, le_rfl⟩ hu.2]) h1.symm
  have hoff2 : ∀ v ∈ Ioo p₂ q₂, ψZ (φZ (ee v)).1 ∉ FZ := fun v hv hF' => by
    rcases (hunZ.symm ▸ hF' : (φZ (ee v)).1 ∈ XZ ∪ XZ') with hx | hx'
    · obtain ⟨u, hu, hu'⟩ := him1.symm.subset hx
      have h1 := φZ.injective (Subtype.ext ((hm1e u hu).trans hu'))
      cases dm <;> simp only [p₁, q₁, p₂, q₂, Bool.false_eq_true, ↓reduceIte] at hdm1 hv h01 h12 h23 h34
      · exact ee_ne (by linarith [hv.1, hdm1.antitoneOn ⟨le_rfl, zero_le_one⟩ hu hu.1])
          (by linarith [hv.2, hdm1.antitoneOn hu ⟨zero_le_one, le_rfl⟩ hu.2]) h1
      · exact ee_ne (by linarith [hv.1, hdm1.monotoneOn hu ⟨zero_le_one, le_rfl⟩ hu.2])
          (by linarith [hv.2, hdm1.monotoneOn ⟨le_rfl, zero_le_one⟩ hu hu.1]) h1
    · obtain ⟨u, hu, hu'⟩ := him2.symm.subset hx'
      have h1 : ee (m₂ u + k) = ee v := (ee_eq_iff.mpr ⟨k, rfl⟩).trans (φZ.injective (Subtype.ext ((hm2e u hu).trans hu')))
      cases dm <;> simp only [p₁, q₁, p₂, q₂, Bool.false_eq_true, ↓reduceIte] at hdm2 hv h01 h12 h23 h34
      · exact ee_ne (by linarith [hv.1, hdm2.antitoneOn ⟨le_rfl, zero_le_one⟩ hu hu.1])
          (by linarith [hv.2, hdm2.antitoneOn hu ⟨zero_le_one, le_rfl⟩ hu.2]) h1
      · exact ee_ne (by linarith [hv.1, hdm2.monotoneOn hu ⟨zero_le_one, le_rfl⟩ hu.2])
          (by linarith [hv.2, hdm2.monotoneOn ⟨le_rfl, zero_le_one⟩ hu hu.1]) h1
  set v_s := a₀v + Int.fract (v_1 - a₀v)
  have hvs_ee : ee v_s = ee v_1 := ee_eq_iff.mpr ⟨-⌊v_1 - a₀v⌋, by simp only [v_s, Int.cast_neg]; linarith [Int.floor_add_fract (v_1 - a₀v)]⟩
  have hvs_nF : ψZ (φZ (ee v_s)).1 ∉ FZ := fun h => hx₁_bd.2 (hbZ ▸ ⟨by rwa [hvs_ee, hv_1ψ] at h, hx₁_bd.1⟩)
  have hvs_lo : a₀v ≤ v_s := by simp only [v_s]; linarith [Int.fract_nonneg (v_1 - a₀v)]
  have hvs_hi : v_s < q₂ := by rw [hq2_eq]; simp only [v_s]; linarith [Int.fract_lt_one (v_1 - a₀v)]
  have hvs_gt1 : p₁ < v_s := by
    by_contra hle'
    have hmem' : v_s ∈ Icc (m₁ 0) (m₁ 1) ∨ v_s ∈ Icc (m₁ 1) (m₁ 0) := by
      cases dm <;> simp only [p₁, a₀v, Bool.false_eq_true, ↓reduceIte] at hvs_lo hle'
      · exact .inr ⟨hvs_lo, not_lt.mp hle'⟩
      · exact .inl ⟨hvs_lo, not_lt.mp hle'⟩
    obtain ⟨u, hu, hue⟩ : ∃ u ∈ Icc (0 : ℝ) 1, m₁ u = v_s :=
      hmem'.elim (fun h => intermediate_value_Icc zero_le_one hm1c h) (fun h => intermediate_value_Icc' zero_le_one hm1c h)
    exact hvs_nF (by rw [← hue, hm1e u hu]; exact show ξZ u ∈ ψZ ⁻¹' FZ from hunZ ▸ Or.inl (him1 ▸ ⟨u, hu, rfl⟩))
  have hvs_not2 : v_s ∉ Icc q₁ p₂ := fun hmem => by
    have hmem' : v_s - k ∈ Icc (m₂ 0) (m₂ 1) ∨ v_s - k ∈ Icc (m₂ 1) (m₂ 0) := by
      cases dm <;> simp only [q₁, p₂, Bool.false_eq_true, ↓reduceIte] at hmem
      · exact .inr ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
      · exact .inl ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
    obtain ⟨u, hu, hue⟩ : ∃ u ∈ Icc (0 : ℝ) 1, m₂ u = v_s - k :=
      hmem'.elim (fun h => intermediate_value_Icc zero_le_one hm2c h) (fun h => intermediate_value_Icc' zero_le_one hm2c h)
    have heee : ee v_s = ee (m₂ u) := ee_eq_iff.mpr ⟨k, by linarith⟩
    exact hvs_nF (by rw [heee, hm2e u hu]; exact show ηZ u ∈ ψZ ⁻¹' FZ from hunZ ▸ Or.inr (him2 ▸ ⟨u, hu, rfl⟩))
  have hps1 : (ψZ (φZ (ee p₁)).1 = (φS (ee (if dm then u_t else u_s))).1) ∧
      (ψZ (φZ (ee q₁)).1 = (φS (ee (if dm then u_s + 1 else u_t))).1) := by
    cases dm <;> simp only [p₁, q₁, Bool.false_eq_true, ↓reduceIte, ee_add_one]
    · exact ⟨by rw [hm1e 0 ⟨le_rfl, zero_le_one⟩, LZ.hξ 0 ⟨le_rfl, zero_le_one⟩, haZ0, hus],
             by rw [ee_eq_iff.mpr ⟨k, rfl⟩, hm2e 1 ⟨zero_le_one, le_rfl⟩, LZ.hη 1 ⟨zero_le_one, le_rfl⟩, haZ1, hut]⟩
    · exact ⟨by rw [hm1e 1 ⟨zero_le_one, le_rfl⟩, LZ.hξ 1 ⟨zero_le_one, le_rfl⟩, haZ1, hut],
             by rw [ee_eq_iff.mpr ⟨k, rfl⟩, hm2e 0 ⟨le_rfl, zero_le_one⟩, LZ.hη 0 ⟨le_rfl, zero_le_one⟩, haZ0, hus]⟩
  have hps2 : (ψZ (φZ (ee p₂)).1 = (φS (ee (if dm then u_t else u_s))).1) ∧
      (ψZ (φZ (ee q₂)).1 = (φS (ee (if dm then u_s + 1 else u_t))).1) := by
    cases dm <;> simp only [p₂, q₂, Bool.false_eq_true, ↓reduceIte, ee_add_one]
    · exact ⟨by rw [ee_eq_iff.mpr ⟨k, rfl⟩, hm2e 0 ⟨le_rfl, zero_le_one⟩, LZ.hη 0 ⟨le_rfl, zero_le_one⟩, haZ0, hus],
             by rw [hm1e 1 ⟨zero_le_one, le_rfl⟩, LZ.hξ 1 ⟨zero_le_one, le_rfl⟩, haZ1, hut]⟩
    · exact ⟨by rw [ee_eq_iff.mpr ⟨k, rfl⟩, hm2e 1 ⟨zero_le_one, le_rfl⟩, LZ.hη 1 ⟨zero_le_one, le_rfl⟩, haZ1, hut],
             by rw [hm1e 0 ⟨le_rfl, zero_le_one⟩, LZ.hξ 0 ⟨le_rfl, zero_le_one⟩, haZ0, hus]⟩
  have hG1_ends : (φS (ee u_t)).1 ∈ ({s, t} : Set S) ∧ (φS (ee (u_s + 1))).1 ∈ ({s, t} : Set S) ∧ (φS (ee u_t)).1 ≠ (φS (ee (u_s + 1))).1 := by
    rw [hut, ee_add_one, hus]; exact ⟨mem_insert_of_mem _ rfl, mem_insert _ _, hne.symm⟩
  have hml_vs : ∀ r ∈ Icc (-δ) δ, ψZ (φZ (ee (v_s + r))).1 = (φS (ee (ml r))).1 := fun r hr => by
    obtain ⟨j, hj⟩ := ee_eq_iff.mp hvs_ee
    rw [show ee (v_s + r) = ee (v_1 + r) from ee_eq_iff.mpr ⟨j, by linarith⟩]; exact hmle r hr
  by_cases hvs_g1 : v_s < q₁
  · have hgap1 := gap_into_G_of_hit hZ hS hψZ hFZ hbZ hsame φS hCZ_bd φZ h12 hoff1
      (by cases dm <;> simp only [Bool.false_eq_true, ↓reduceIte, ee_add_one, hus, hut] at hps1 <;> [exact .inl hps1; exact .inr hps1])
      hu2 (by linarith) hG1_ends ⟨v_s, ⟨hvs_gt1, hvs_g1⟩, by rw [hvs_ee, hv_1ψ]; exact hx₁G₁⟩
    have hdl_eq : dl = dm := by
      have hgd := gap_dir_eq hψZ φZ φS hu2 (by linarith) h12 hspan1 hoff1 hgap1 ⟨hvs_gt1, hvs_g1⟩ hδ hmlc hmld hml_vs
      cases dm <;> simp only [Bool.false_eq_true, ↓reduceIte] at hps1
      · exact hgd.2 ⟨by rw [hps1.1, ee_add_one], hps1.2⟩
      · exact hgd.1 hps1
    subst hdl_eq
    exact ⟨hdm1, hdm2, k, true, h12, hspan1, h34, hspan2, hoff1, hoff2, ⟨v_s, ⟨hvs_gt1, hvs_g1⟩, hvs_ee⟩, hgap1⟩
  · have hvs_gt2 : p₂ < v_s := lt_of_not_ge fun hle' => hvs_not2 ⟨not_lt.mp hvs_g1, hle'⟩
    have hgap2 := gap_into_G_of_hit hZ hS hψZ hFZ hbZ hsame φS hCZ_bd φZ h34 hoff2
      (by cases dm <;> simp only [Bool.false_eq_true, ↓reduceIte, ee_add_one, hus, hut] at hps2 <;> [exact .inl hps2; exact .inr hps2])
      hu2 (by linarith) hG1_ends ⟨v_s, ⟨hvs_gt2, hvs_hi⟩, by rw [hvs_ee, hv_1ψ]; exact hx₁G₁⟩
    have hdl_eq : dl = dm := by
      have hgd := gap_dir_eq hψZ φZ φS hu2 (by linarith) h34 hspan2 hoff2 hgap2 ⟨hvs_gt2, hvs_hi⟩ hδ hmlc hmld hml_vs
      cases dm <;> simp only [Bool.false_eq_true, ↓reduceIte] at hps2
      · exact hgd.2 ⟨by rw [hps2.1, ee_add_one], hps2.2⟩
      · exact hgd.1 hps2
    subst hdl_eq
    exact ⟨hdm1, hdm2, k, false, h12, hspan1, h34, hspan2, hoff1, hoff2, ⟨v_s, ⟨hvs_gt2, hvs_hi⟩, hvs_ee⟩, hgap2⟩

/-- Gap structure for a 2-sided same-cuff cutting (`C_s = C_t`, `C_ξ ≠ C_η`) on one of the two
cut cuffs `CZ`. -/
theorem twosided_cuff_info (hZ : IsSurface Z) (hS : IsSurface S)
    {ψZ : Z → S} {FZ : Set S} {s t : S} (hne : s ≠ t) (hψZ : IsCutting ψZ FZ) (hFZ : IsClosed FZ)
    (hbZ : FZ ∩ bd S = {s, t})
    {XZ XZ' : Set Z} (hPZ : LiftPair ψZ FZ s t XZ XZ')
    {aZ : ℝ → S} {ξZ ηZ : ℝ → Z} (LZ : ArcLift ψZ FZ aZ ξZ ηZ)
    (haZ0 : aZ 0 = s) (haZ1 : aZ 1 = t)
    (him1 : ξZ '' Icc 0 1 = XZ) (hi1 : InjOn ξZ (Icc 0 1))
    (hsame : connectedComponentIn (bd S) s = connectedComponentIn (bd S) t)
    (φS : Circle ≃ₜ connectedComponentIn (bd S) s)
    {CZ CZ' : Set Z} (hCZ : CZ ∈ cuffs Z) (hCZ' : CZ' ∈ cuffs Z) (hneC : CZ ≠ CZ')
    (hXZ'C : XZ' ⊆ CZ') (φZ : Circle ≃ₜ CZ)
    {m : ℝ → ℝ} (hmc : ContinuousOn m (Icc 0 1)) (hme : ∀ u ∈ Icc (0 : ℝ) 1, (φZ (ee (m u))).1 = ξZ u)
    {u₁ u₂ : ℝ} (hu12 : u₁ < u₂) (hu21 : u₂ < u₁ + 1)
    (hx12 : ((φS (ee u₁)).1 = t ∧ (φS (ee u₂)).1 = s) ∨ ((φS (ee u₁)).1 = s ∧ (φS (ee u₂)).1 = t))
    {v₀ : ℝ} (hv0_in : ψZ (φZ (ee v₀)).1 ∈ (fun w => (φS (ee w)).1) '' Ioo u₁ u₂)
    {δ : ℝ} (hδ : 0 < δ) {ml : ℝ → ℝ} {dl : Bool}
    (hmlc : ContinuousOn ml (Icc (-δ) δ))
    (hmld : if dl then StrictMonoOn ml (Icc (-δ) δ) else StrictAntiOn ml (Icc (-δ) δ))
    (hmle : ∀ r ∈ Icc (-δ) δ, ψZ (φZ (ee (v₀ + r))).1 = (φS (ee (ml r))).1) :
    ∃ dm : Bool,
      (if dm then StrictMonoOn m (Icc 0 1) else StrictAntiOn m (Icc 0 1)) ∧
      (((φS (ee u₁)).1 = t → dl = dm) ∧ ((φS (ee u₁)).1 = s → dl = !dm)) ∧
      (let p := if dm then m 1 else m 0
       let q := if dm then m 0 + 1 else m 1 + 1
       p < q ∧ q - p < 1 ∧ (∀ v ∈ Ioo p q, ψZ (φZ (ee v)).1 ∉ FZ) ∧
       (∀ v ∈ Ioo p q, ψZ (φZ (ee v)).1 ∈ (fun w => (φS (ee w)).1) '' Ioo u₁ u₂) ∧
       (∃ v ∈ Ioo p q, ee v = ee v₀)) := by
  obtain ⟨_, _, _, _, _, _, _, hunZ, -⟩ := id hPZ
  have hCZ_bd : CZ ⊆ bd Z := by obtain ⟨z, -, rfl⟩ := hCZ; exact connectedComponentIn_subset _ _
  have hdisC := cuffs_disjoint hCZ hCZ' hneC
  have hmo := lift_mono hmc (inj_of_lift hme hi1)
  have hdm_ex : ∃ dm : Bool, if dm then StrictMonoOn m (Icc 0 1) else StrictAntiOn m (Icc 0 1) :=
    hmo.elim (fun h => ⟨true, h⟩) (fun h => ⟨false, h⟩)
  obtain ⟨dm, hdm⟩ := hdm_ex
  set p := if dm then m 1 else m 0
  set q := if dm then m 0 + 1 else m 1 + 1
  set a₀v := if dm then m 0 else m 1
  have hpq : p < q := by
    cases dm <;> simp only [p, q, Bool.false_eq_true, ↓reduceIte] at hdm ⊢
    · let n : ℝ → ℝ := fun u => m (1 - u)
      have hnc : ContinuousOn n (Icc 0 1) := hmc.comp (by fun_prop) fun _ hu => rev_mem hu
      have hnm : StrictMonoOn n (Icc 0 1) := fun a ha b hb h => hdm (rev_mem hb) (rev_mem ha) (by linarith)
      have hni : InjOn (fun u => ee (n u)) (Icc 0 1) := fun a ha b hb he => by
        have := inj_of_lift hme hi1 (rev_mem ha) (rev_mem hb) he; linarith
      simpa [n] using lift_lt_add_one hnc hnm hni
    · exact lift_lt_add_one hmc hdm (inj_of_lift hme hi1)
  have h01 : a₀v < p := by
    cases dm <;> simp only [p, a₀v, Bool.false_eq_true, ↓reduceIte] at hdm ⊢ <;>
      exact hdm ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one
  have hsp : q - p < 1 := by
    have : q = a₀v + 1 := by cases dm <;> rfl
    linarith
  have hoff : ∀ v ∈ Ioo p q, ψZ (φZ (ee v)).1 ∉ FZ := fun v hv hF' => by
    rcases (hunZ.symm ▸ hF' : (φZ (ee v)).1 ∈ XZ ∪ XZ') with hx | hx'
    · obtain ⟨u, hu, hu'⟩ := him1.symm.subset hx
      have h1 := φZ.injective (Subtype.ext ((hme u hu).trans hu'))
      cases dm <;> simp only [p, q, a₀v, Bool.false_eq_true, ↓reduceIte] at hdm hv h01 hpq
      · exact ee_ne (by linarith [hv.1, hdm.antitoneOn ⟨le_rfl, zero_le_one⟩ hu hu.1])
          (by linarith [hv.2, hdm.antitoneOn hu ⟨zero_le_one, le_rfl⟩ hu.2]) h1
      · exact ee_ne (by linarith [hv.1, hdm.monotoneOn hu ⟨zero_le_one, le_rfl⟩ hu.2])
          (by linarith [hv.2, hdm.monotoneOn ⟨le_rfl, zero_le_one⟩ hu hu.1]) h1
    · exact Set.disjoint_left.mp hdisC (φZ _).2 (hXZ'C hx')
  set v_s := a₀v + Int.fract (v₀ - a₀v)
  have hvs_ee : ee v_s = ee v₀ := ee_eq_iff.mpr ⟨-⌊v₀ - a₀v⌋, by simp only [v_s, Int.cast_neg]; linarith [Int.floor_add_fract (v₀ - a₀v)]⟩
  have hvs_nF : ψZ (φZ (ee v_s)).1 ∉ FZ := fun hF' => by
    rw [hvs_ee] at hF'
    obtain ⟨w, hw, hwe⟩ := hv0_in
    dsimp only at hwe
    have hbd : ψZ (φZ (ee v₀)).1 ∈ bd S := by rw [← hwe]; exact connectedComponentIn_subset _ _ (φS _).2
    have hst' : (φS (ee w)).1 ∈ ({s, t} : Set S) := hbZ ▸ ⟨hwe.symm ▸ hF', hwe.symm ▸ hbd⟩
    rcases hx12 with ⟨h1t, h2s⟩ | ⟨h1s, h2t⟩
    · rcases hst' with hs' | ht'
      · exact ee_ne hw.2 (by linarith [hw.1]) (φS.injective (Subtype.ext (h2s.trans hs'.symm))).symm
      · exact ee_ne hw.1 (by linarith [hw.2]) (φS.injective (Subtype.ext (h1t.trans ht'.symm)))
    · rcases hst' with hs' | ht'
      · exact ee_ne hw.1 (by linarith [hw.2]) (φS.injective (Subtype.ext (h1s.trans hs'.symm)))
      · exact ee_ne hw.2 (by linarith [hw.1]) (φS.injective (Subtype.ext (h2t.trans ht'.symm))).symm
  have hvs_in : v_s ∈ Ioo p q := by
    have hlo : a₀v ≤ v_s := by simp only [v_s]; linarith [Int.fract_nonneg (v₀ - a₀v)]
    have hhi : v_s < q := by have : q = a₀v + 1 := by cases dm <;> rfl
                             rw [this]; simp only [v_s]; linarith [Int.fract_lt_one (v₀ - a₀v)]
    refine ⟨?_, hhi⟩
    by_contra hle'
    have hmem : v_s ∈ Icc (m 0) (m 1) ∨ v_s ∈ Icc (m 1) (m 0) := by
      cases dm <;> simp only [p, a₀v, Bool.false_eq_true, ↓reduceIte] at hlo hle'
      · exact .inr ⟨hlo, not_lt.mp hle'⟩
      · exact .inl ⟨hlo, not_lt.mp hle'⟩
    obtain ⟨u, hu, hue⟩ : ∃ u ∈ Icc (0 : ℝ) 1, m u = v_s :=
      hmem.elim (fun h => intermediate_value_Icc zero_le_one hmc h) (fun h => intermediate_value_Icc' zero_le_one hmc h)
    exact hvs_nF (by rw [← hue, hme u hu]; exact show ξZ u ∈ ψZ ⁻¹' FZ from hunZ ▸ Or.inl (him1 ▸ ⟨u, hu, rfl⟩))
  have hp_val : ψZ (φZ (ee p)).1 = if dm then t else s := by
    cases dm <;> simp only [p, Bool.false_eq_true, ↓reduceIte]
    · rw [hme 0 ⟨le_rfl, zero_le_one⟩, LZ.hξ 0 ⟨le_rfl, zero_le_one⟩, haZ0]
    · rw [hme 1 ⟨zero_le_one, le_rfl⟩, LZ.hξ 1 ⟨zero_le_one, le_rfl⟩, haZ1]
  have hq_val : ψZ (φZ (ee q)).1 = if dm then s else t := by
    cases dm <;> simp only [q, Bool.false_eq_true, ↓reduceIte, ee_add_one]
    · rw [hme 1 ⟨zero_le_one, le_rfl⟩, LZ.hξ 1 ⟨zero_le_one, le_rfl⟩, haZ1]
    · rw [hme 0 ⟨le_rfl, zero_le_one⟩, LZ.hξ 0 ⟨le_rfl, zero_le_one⟩, haZ0]
  have hgap := gap_into_G_of_hit hZ hS hψZ hFZ hbZ hsame φS hCZ_bd φZ hpq hoff
    (by cases dm <;> simp only [Bool.false_eq_true, ↓reduceIte] at hp_val hq_val <;> [exact .inl ⟨hp_val, hq_val⟩; exact .inr ⟨hp_val, hq_val⟩])
    hu12 hu21
    (by rcases hx12 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
        · exact ⟨mem_insert_of_mem _ rfl, mem_insert _ _, hne.symm⟩
        · exact ⟨mem_insert _ _, mem_insert_of_mem _ rfl, hne⟩)
    ⟨v_s, hvs_in, by rwa [hvs_ee]⟩
  have hml_vs : ∀ r ∈ Icc (-δ) δ, ψZ (φZ (ee (v_s + r))).1 = (φS (ee (ml r))).1 := fun r hr => by
    obtain ⟨j, hj⟩ := ee_eq_iff.mp hvs_ee
    rw [show ee (v_s + r) = ee (v₀ + r) from ee_eq_iff.mpr ⟨j, by linarith⟩]; exact hmle r hr
  have hgd := gap_dir_eq hψZ φZ φS hu12 hu21 hpq hsp hoff hgap hvs_in hδ hmlc hmld hml_vs
  refine ⟨dm, hdm, ?_, hpq, hsp, hoff, hgap, ⟨v_s, hvs_in, hvs_ee⟩⟩
  rcases hx12 with ⟨h1t, h2s⟩ | ⟨h1s, h2t⟩
  · refine ⟨fun _ => ?_, fun h1s => absurd (h1s.symm.trans h1t) hne⟩
    cases dm <;> simp only [Bool.false_eq_true, ↓reduceIte] at hp_val hq_val
    · exact hgd.2 ⟨hp_val.trans h2s.symm, hq_val.trans h1t.symm⟩
    · exact hgd.1 ⟨hp_val.trans h1t.symm, hq_val.trans h2s.symm⟩
  · refine ⟨fun h1t => absurd (h1s.symm.trans h1t) hne, fun _ => ?_⟩
    cases dm <;> simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true] at hp_val hq_val ⊢
    · exact hgd.1 ⟨hp_val.trans h1s.symm, hq_val.trans h2t.symm⟩
    · exact hgd.2 ⟨hp_val.trans h2t.symm, hq_val.trans h1s.symm⟩

/-- Gap structure and `w₁` relation for a distinct-cuff cutting (`C_s ≠ C_t`, `C_ξ = C_η`). -/
theorem diff_cuff_info (hZ : IsSurface Z) (hS : IsSurface S) (AZ : SurfAtlas Z) (AS : SurfAtlas S)
    {ψZ : Z → S} {FZ : Set S} {s t : S} (hne : s ≠ t) (hψZ : IsCutting ψZ FZ) (hFZ : IsClosed FZ)
    (hbZ : FZ ∩ bd S = {s, t})
    {XZ XZ' : Set Z} (hPZ : LiftPair ψZ FZ s t XZ XZ')
    {aZ : ℝ → S} {ξZ ηZ : ℝ → Z} (LZ : ArcLift ψZ FZ aZ ξZ ηZ)
    (haZ0 : aZ 0 = s) (haZ1 : aZ 1 = t)
    (him1 : ξZ '' Icc 0 1 = XZ) (him2 : ηZ '' Icc 0 1 = XZ')
    (hi1 : InjOn ξZ (Icc 0 1)) (hi2 : InjOn ηZ (Icc 0 1))
    (hst : connectedComponentIn (bd S) s ≠ connectedComponentIn (bd S) t)
    (φs : Circle ≃ₜ connectedComponentIn (bd S) s)
    (φt : Circle ≃ₜ connectedComponentIn (bd S) t)
    {CZ : Set Z} (hCZ : CZ ∈ cuffs Z) (φZ : Circle ≃ₜ CZ)
    {m₁ m₂ : ℝ → ℝ}
    (hm1c : ContinuousOn m₁ (Icc 0 1)) (hm1e : ∀ u ∈ Icc (0 : ℝ) 1, (φZ (ee (m₁ u))).1 = ξZ u)
    (hm2c : ContinuousOn m₂ (Icc 0 1)) (hm2e : ∀ u ∈ Icc (0 : ℝ) 1, (φZ (ee (m₂ u))).1 = ηZ u) :
    ∃ (dm : Bool) (_k : ℤ) (ps qs pt qt : ℝ) (σ_s σ_t : Bool),
      (if dm then StrictMonoOn m₁ (Icc 0 1) else StrictAntiOn m₁ (Icc 0 1)) ∧
      (if dm then StrictAntiOn m₂ (Icc 0 1) else StrictMonoOn m₂ (Icc 0 1)) ∧
      ps < qs ∧ qs - ps < 1 ∧ pt < qt ∧ qt - pt < 1 ∧
      (∀ v ∈ Ioo ps qs, ψZ (φZ (ee v)).1 ∈ connectedComponentIn (bd S) s ∧ ψZ (φZ (ee v)).1 ∉ FZ) ∧
      (∀ v ∈ Ioo pt qt, ψZ (φZ (ee v)).1 ∈ connectedComponentIn (bd S) t ∧ ψZ (φZ (ee v)).1 ∉ FZ) ∧
      (ψZ (φZ (ee ps)).1 = s ∧ ψZ (φZ (ee qs)).1 = s ∧ ψZ (φZ (ee pt)).1 = t ∧ ψZ (φZ (ee qt)).1 = t) ∧
      (∀ v ∈ Ioo ps qs, ∃ (δ : ℝ) (ml : ℝ → ℝ), 0 < δ ∧ ContinuousOn ml (Icc (-δ) δ) ∧
        (if σ_s then StrictMonoOn ml (Icc (-δ) δ) else StrictAntiOn ml (Icc (-δ) δ)) ∧
        (∀ r ∈ Icc (-δ) δ, ψZ (φZ (ee (v + r))).1 = (φs (ee (ml r))).1)) ∧
      (∀ v ∈ Ioo pt qt, ∃ (δ : ℝ) (ml : ℝ → ℝ), 0 < δ ∧ ContinuousOn ml (Icc (-δ) δ) ∧
        (if σ_t then StrictMonoOn ml (Icc (-δ) δ) else StrictAntiOn ml (Icc (-δ) δ)) ∧
        (∀ r ∈ Icc (-δ) δ, ψZ (φZ (ee (v + r))).1 = (φt (ee (ml r))).1)) ∧
      cocInt (w1 AS) aZ =
        (cuffSign AS φt t + (if σ_t then 0 else 1)) - (cuffSign AS φs s + (if σ_s then 0 else 1)) ∧
      (∀ v : ℝ, ψZ (φZ (ee v)).1 ∈ connectedComponentIn (bd S) s \ {s, t} → ∃ w ∈ Ioo ps qs, ee w = ee v) ∧
      (∀ v : ℝ, ψZ (φZ (ee v)).1 ∈ connectedComponentIn (bd S) t \ {s, t} → ∃ w ∈ Ioo pt qt, ee w = ee v) := by
  have hsb : s ∈ bd S := (show s ∈ FZ ∩ bd S from hbZ ▸ mem_insert _ _).2
  have htb : t ∈ bd S := (show t ∈ FZ ∩ bd S from hbZ ▸ mem_insert_of_mem _ rfl).2
  have hCs_cuff : connectedComponentIn (bd S) s ∈ cuffs S := ⟨s, hsb, rfl⟩
  have hCt_cuff : connectedComponentIn (bd S) t ∈ cuffs S := ⟨t, htb, rfl⟩
  have hCZ_bd : CZ ⊆ bd Z := by obtain ⟨z, -, rfl⟩ := hCZ; exact connectedComponentIn_subset _ _
  have hmo1 := lift_mono hm1c (inj_of_lift hm1e hi1)
  have hopp : ∃ dm : Bool,
      (if dm then StrictMonoOn m₁ (Icc 0 1) else StrictAntiOn m₁ (Icc 0 1)) ∧
      (if dm then StrictAntiOn m₂ (Icc 0 1) else StrictMonoOn m₂ (Icc 0 1)) := by
    rcases hmo1 with hm1m | hm1a
    · exact ⟨true, hm1m, (cut_single_cuff_dirs hZ hS hne hψZ hFZ hbZ hPZ LZ haZ0 haZ1 him1 him2 hi1 hi2 hCZ φZ hm1c hm1m hm1e hm2c hm2e).1 hst⟩
    · let φZr : Circle ≃ₜ CZ := (Homeomorph.inv Circle).trans φZ
      have hinv_e : ∀ r : ℝ, (φZr (ee (-r))).1 = (φZ (ee r)).1 := fun r => by
        simp only [φZr, Homeomorph.trans_apply]; change (φZ (ee (-r))⁻¹).1 = _
        rw [show (ee (-r))⁻¹ = ee r by unfold ee; rw [mul_neg, Circle.exp_neg, inv_inv]]
      have hm2a' := (cut_single_cuff_dirs hZ hS hne hψZ hFZ hbZ hPZ LZ haZ0 haZ1 him1 him2 hi1 hi2 hCZ φZr
        hm1c.neg (fun a ha b hb h => neg_lt_neg (hm1a ha hb h)) (fun u hu => (hinv_e _).trans (hm1e u hu))
        hm2c.neg (fun u hu => (hinv_e _).trans (hm2e u hu))).1 hst
      exact ⟨false, hm1a, fun a ha b hb h => lt_of_neg_lt_neg (hm2a' ha hb h)⟩
  obtain ⟨dm, hdm1, hdm2⟩ := hopp
  have hord_pos : ∀ (ξP ηP : ℝ → Z) (XP XP' : Set Z) (hPP : LiftPair ψZ FZ s t XP XP')
      (LP : ArcLift ψZ FZ aZ ξP ηP) (himP1 : ξP '' Icc 0 1 = XP) (himP2 : ηP '' Icc 0 1 = XP')
      (hiP1 : InjOn ξP (Icc 0 1)) (hiP2 : InjOn ηP (Icc 0 1))
      (mp mn : ℝ → ℝ) (hmpc : ContinuousOn mp (Icc 0 1)) (hmpm : StrictMonoOn mp (Icc 0 1))
      (hmpe : ∀ u ∈ Icc (0 : ℝ) 1, (φZ (ee (mp u))).1 = ξP u)
      (hmnc : ContinuousOn mn (Icc 0 1)) (hmna : StrictAntiOn mn (Icc 0 1))
      (hmne : ∀ u ∈ Icc (0 : ℝ) 1, (φZ (ee (mn u))).1 = ηP u),
      ∃ (k : ℤ) (ps qs pt qt : ℝ) (σ_s σ_t : Bool),
        ps < qs ∧ qs - ps < 1 ∧ pt < qt ∧ qt - pt < 1 ∧
        (∀ v ∈ Ioo ps qs, ψZ (φZ (ee v)).1 ∈ connectedComponentIn (bd S) s ∧ ψZ (φZ (ee v)).1 ∉ FZ) ∧
        (∀ v ∈ Ioo pt qt, ψZ (φZ (ee v)).1 ∈ connectedComponentIn (bd S) t ∧ ψZ (φZ (ee v)).1 ∉ FZ) ∧
        (ψZ (φZ (ee ps)).1 = s ∧ ψZ (φZ (ee qs)).1 = s ∧ ψZ (φZ (ee pt)).1 = t ∧ ψZ (φZ (ee qt)).1 = t) ∧
        (∀ v ∈ Ioo ps qs, ∃ (δ : ℝ) (ml : ℝ → ℝ), 0 < δ ∧ ContinuousOn ml (Icc (-δ) δ) ∧
          (if σ_s then StrictMonoOn ml (Icc (-δ) δ) else StrictAntiOn ml (Icc (-δ) δ)) ∧
          (∀ r ∈ Icc (-δ) δ, ψZ (φZ (ee (v + r))).1 = (φs (ee (ml r))).1)) ∧
        (∀ v ∈ Ioo pt qt, ∃ (δ : ℝ) (ml : ℝ → ℝ), 0 < δ ∧ ContinuousOn ml (Icc (-δ) δ) ∧
          (if σ_t then StrictMonoOn ml (Icc (-δ) δ) else StrictAntiOn ml (Icc (-δ) δ)) ∧
          (∀ r ∈ Icc (-δ) δ, ψZ (φZ (ee (v + r))).1 = (φt (ee (ml r))).1)) ∧
        cocInt (w1 AS) aZ =
          (cuffSign AS φt t + (if σ_t then 0 else 1)) - (cuffSign AS φs s + (if σ_s then 0 else 1)) ∧
        (∀ v : ℝ, ψZ (φZ (ee v)).1 ∈ connectedComponentIn (bd S) s \ {s, t} → ∃ w ∈ Ioo ps qs, ee w = ee v) ∧
        (∀ v : ℝ, ψZ (φZ (ee v)).1 ∈ connectedComponentIn (bd S) t \ {s, t} → ∃ w ∈ Ioo pt qt, ee w = ee v) := by
    intro ξP ηP XP XP' hPP LP himP1 himP2 hiP1 hiP2 mp mn hmpc hmpm hmpe hmnc hmna hmne
    obtain ⟨_, _, _, _, _, _, hdP, hunP, -⟩ := id hPP
    have hdjP : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1, ξP u ≠ ηP v := fun u hu v hv he =>
      Set.disjoint_left.mp hdP (show ξP u ∈ XP from himP1 ▸ ⟨u, hu, rfl⟩) (he ▸ show ηP v ∈ XP' from himP2 ▸ ⟨v, hv, rfl⟩)
    obtain ⟨k, hke, hord⟩ := exists_two_lifts_order φZ hmpc hmpm hmpe hmnc (.inr hmna) hmne hiP1 hiP2 hdjP
    have hord' : mp 0 < mp 1 ∧ mp 1 < mn 1 + k ∧ mn 1 + k < mn 0 + k ∧ mn 0 + k < mp 0 + 1 := by
      rcases hord with ⟨hm, -⟩ | ⟨-, h⟩
      · exact absurd (hm ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one)
          (not_lt.mpr (hmna ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one).le)
      · exact h
    set pt := mp 1
    set qt := mn 1 + k
    set ps := mn 0 + k
    set qs := mp 0 + 1
    have hoff_t : ∀ v ∈ Ioo pt qt, ψZ (φZ (ee v)).1 ∉ FZ := fun v hv hF' => by
      rcases (hunP.symm ▸ hF' : (φZ (ee v)).1 ∈ XP ∪ XP') with hx | hx'
      · obtain ⟨u, hu, hu'⟩ := himP1.symm.subset hx
        have h1 := φZ.injective (Subtype.ext ((hmpe u hu).trans hu'))
        exact ee_ne (by linarith [hv.1, hmpm.monotoneOn hu ⟨zero_le_one, le_rfl⟩ hu.2])
          (by linarith [hv.2, hmpm.monotoneOn ⟨le_rfl, zero_le_one⟩ hu hu.1, hord'.2.2.1, hord'.2.2.2]) h1
      · obtain ⟨u, hu, hu'⟩ := himP2.symm.subset hx'
        have h1 := φZ.injective (Subtype.ext ((hke u hu).trans hu'))
        exact ee_ne (by linarith [hv.2, hmna.antitoneOn hu ⟨zero_le_one, le_rfl⟩ hu.2])
          (by linarith [hv.1, hmna.antitoneOn ⟨le_rfl, zero_le_one⟩ hu hu.1, hord'.1, hord'.2.2.2]) h1.symm
    have hoff_s : ∀ v ∈ Ioo ps qs, ψZ (φZ (ee v)).1 ∉ FZ := fun v hv hF' => by
      rcases (hunP.symm ▸ hF' : (φZ (ee v)).1 ∈ XP ∪ XP') with hx | hx'
      · obtain ⟨u, hu, hu'⟩ := himP1.symm.subset hx
        have h1 := φZ.injective (Subtype.ext ((hmpe u hu).trans hu'))
        exact ee_ne (by linarith [hv.1, hmpm.monotoneOn hu ⟨zero_le_one, le_rfl⟩ hu.2, hord'.2.1, hord'.2.2.1])
          (by linarith [hv.2, hmpm.monotoneOn ⟨le_rfl, zero_le_one⟩ hu hu.1]) h1
      · obtain ⟨u, hu, hu'⟩ := himP2.symm.subset hx'
        have h1 := φZ.injective (Subtype.ext ((hke u hu).trans hu'))
        exact ee_ne (by linarith [hv.1, hmna.antitoneOn ⟨le_rfl, zero_le_one⟩ hu hu.1])
          (by linarith [hv.2, hmna.antitoneOn hu ⟨zero_le_one, le_rfl⟩ hu.2, hord'.1, hord'.2.1]) h1
    have hpt_e : ψZ (φZ (ee pt)).1 = t := by rw [hmpe 1 ⟨zero_le_one, le_rfl⟩, LP.hξ 1 ⟨zero_le_one, le_rfl⟩, haZ1]
    have hqt_e : ψZ (φZ (ee qt)).1 = t := by rw [hke 1 ⟨zero_le_one, le_rfl⟩, LP.hη 1 ⟨zero_le_one, le_rfl⟩, haZ1]
    have hps_e : ψZ (φZ (ee ps)).1 = s := by rw [hke 0 ⟨le_rfl, zero_le_one⟩, LP.hη 0 ⟨le_rfl, zero_le_one⟩, haZ0]
    have hqs_e : ψZ (φZ (ee qs)).1 = s := by rw [show qs = mp 0 + 1 from rfl, ee_add_one, hmpe 0 ⟨le_rfl, zero_le_one⟩, LP.hξ 0 ⟨le_rfl, zero_le_one⟩, haZ0]
    have hin_s : ∀ v ∈ Ioo ps qs, ψZ (φZ (ee v)).1 ∈ connectedComponentIn (bd S) s ∧ ψZ (φZ (ee v)).1 ∉ FZ := fun v hv => by
      refine ⟨?_, hoff_s v hv⟩
      have hsub := (isPreconnected_Icc.image (fun w => ψZ (φZ (ee w)).1)
        (hψZ.1.comp_continuousOn (continuous_subtype_val.comp (φZ.continuous.comp continuous_ee)).continuousOn)).subset_connectedComponentIn
        ⟨ps, ⟨le_rfl, hord'.2.2.2.le⟩, hps_e⟩ (by
          rintro _ ⟨w, hw, rfl⟩; dsimp only
          rcases eq_or_lt_of_le hw.1 with rfl | h1
          · rw [hps_e]; exact hsb
          · rcases eq_or_lt_of_le hw.2 with rfl | h2
            · rw [hqs_e]; exact hsb
            · exact (mem_bd_cut_iff hZ hS hψZ hFZ (hoff_s w ⟨h1, h2⟩)).mp (hCZ_bd (φZ _).2))
      exact hsub ⟨v, Ioo_subset_Icc_self hv, rfl⟩
    have hin_t : ∀ v ∈ Ioo pt qt, ψZ (φZ (ee v)).1 ∈ connectedComponentIn (bd S) t ∧ ψZ (φZ (ee v)).1 ∉ FZ := fun v hv => by
      refine ⟨?_, hoff_t v hv⟩
      have hsub := (isPreconnected_Icc.image (fun w => ψZ (φZ (ee w)).1)
        (hψZ.1.comp_continuousOn (continuous_subtype_val.comp (φZ.continuous.comp continuous_ee)).continuousOn)).subset_connectedComponentIn
        ⟨pt, ⟨le_rfl, hord'.2.1.le⟩, hpt_e⟩ (by
          rintro _ ⟨w, hw, rfl⟩; dsimp only
          rcases eq_or_lt_of_le hw.1 with rfl | h1
          · rw [hpt_e]; exact htb
          · rcases eq_or_lt_of_le hw.2 with rfl | h2
            · rw [hqt_e]; exact htb
            · exact (mem_bd_cut_iff hZ hS hψZ hFZ (hoff_t w ⟨h1, h2⟩)).mp (hCZ_bd (φZ _).2))
      exact hsub ⟨v, Ioo_subset_Icc_self hv, rfl⟩
    set ε := min (qs - ps) (qt - pt) / 2
    have hε : 0 < ε := half_pos (lt_min (by linarith [hord'.2.2.2]) (by linarith [hord'.2.1]))
    have hε_s : ε < qs - ps := (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)).trans_lt (half_lt_self (by linarith [hord'.2.2.2]))
    have hε_t : ε < qt - pt := (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)).trans_lt (half_lt_self (by linarith [hord'.2.1]))
    have hlift_s : ∃ (ms : ℝ → ℝ) (σ_s : Bool), ContinuousOn ms (Icc (-ε) 0) ∧
        (if σ_s then StrictMonoOn ms (Icc (-ε) 0) else StrictAntiOn ms (Icc (-ε) 0)) ∧
        (∀ r ∈ Icc (-ε) 0, ψZ (φZ (ee (mp 0 + r))).1 = (φs (ee (ms r))).1) := by
      let γ : ℝ → S := fun u => ψZ (φZ (ee (mp 0 + lin (-ε) 0 u))).1
      have hγc : ContinuousOn γ (Icc 0 1) :=
        hψZ.1.comp_continuousOn ((continuous_subtype_val.comp (φZ.continuous.comp continuous_ee)).continuousOn.comp
          (continuousOn_const.add (continuousOn_lin _ _)) fun _ _ => mem_univ _)
      have hγCS : ∀ u ∈ Icc (0 : ℝ) 1, γ u ∈ connectedComponentIn (bd S) s := fun u hu => by
        rcases eq_or_lt_of_le hu.2 with rfl | hlt
        · simp only [γ, lin_one, add_zero]; rw [hmpe 0 ⟨le_rfl, zero_le_one⟩, LP.hξ 0 ⟨le_rfl, zero_le_one⟩, haZ0]; exact mem_connectedComponentIn hsb
        · have hlr : lin (-ε) 0 u ∈ Ico (-ε) 0 := ⟨by simp only [lin]; nlinarith [hu.1, hε], by simp only [lin]; nlinarith [hlt, hε]⟩
          have he1 : ee (mp 0 + lin (-ε) 0 u) = ee (qs + lin (-ε) 0 u) := ee_eq_iff.mpr ⟨-1, by simp only [qs, Int.cast_neg, Int.cast_one]; ring⟩
          dsimp only [γ]; rw [he1]; exact (hin_s _ ⟨by linarith [hlr.1], by linarith [hlr.2]⟩).1
      obtain ⟨l₀, hl0c, hl0e⟩ := exists_lift φs hγc hγCS
      let ms : ℝ → ℝ := fun r => l₀ ((r + ε) / ε)
      have hmsc : ContinuousOn ms (Icc (-ε) 0) :=
        hl0c.comp (by fun_prop) fun r hr => ⟨div_nonneg (by linarith [hr.1]) hε.le, (div_le_one hε).mpr (by linarith [hr.2])⟩
      have hmse : ∀ r ∈ Icc (-ε) 0, ψZ (φZ (ee (mp 0 + r))).1 = (φs (ee (ms r))).1 := fun r hr => by
        have h1 := hl0e ((r + ε) / ε) ⟨div_nonneg (by linarith [hr.1]) hε.le, (div_le_one hε).mpr (by linarith [hr.2])⟩
        have h2 : lin (-ε) 0 ((r + ε) / ε) = r := by simp only [lin]; field_simp [hε.ne']; ring
        simpa only [γ, h2, ms] using h1.symm
      have hms_inj : InjOn ms (Icc (-ε) 0) := fun r₁ hr₁ r₂ hr₂ he => by
        have h1 : ψZ (φZ (ee (mp 0 + r₁))).1 = ψZ (φZ (ee (mp 0 + r₂))).1 := by rw [hmse r₁ hr₁, hmse r₂ hr₂, he]
        rcases eq_or_lt_of_le hr₁.2 with rfl | h1lt
        · rcases eq_or_lt_of_le hr₂.2 with rfl | h2lt
          · rfl
          · exfalso
            have he2 : ee (mp 0 + r₂) = ee (qs + r₂) := ee_eq_iff.mpr ⟨-1, by simp only [qs, Int.cast_neg, Int.cast_one]; ring⟩
            have hsF : s ∈ FZ := (show s ∈ FZ ∩ bd S from hbZ ▸ mem_insert _ _).1
            have hs1 : ψZ (φZ (ee (mp 0 + 0))).1 = s := by rw [add_zero, hmpe 0 ⟨le_rfl, zero_le_one⟩, LP.hξ 0 ⟨le_rfl, zero_le_one⟩, haZ0]
            exact hoff_s (qs + r₂) ⟨by linarith [hr₂.1], by linarith⟩ (by rw [← he2, ← h1, hs1]; exact hsF)
        · rcases eq_or_lt_of_le hr₂.2 with rfl | h2lt
          · exfalso
            have he1 : ee (mp 0 + r₁) = ee (qs + r₁) := ee_eq_iff.mpr ⟨-1, by simp only [qs, Int.cast_neg, Int.cast_one]; ring⟩
            have hsF : s ∈ FZ := (show s ∈ FZ ∩ bd S from hbZ ▸ mem_insert _ _).1
            have hs2 : ψZ (φZ (ee (mp 0 + 0))).1 = s := by rw [add_zero, hmpe 0 ⟨le_rfl, zero_le_one⟩, LP.hξ 0 ⟨le_rfl, zero_le_one⟩, haZ0]
            exact hoff_s (qs + r₁) ⟨by linarith [hr₁.1], by linarith⟩ (by rw [← he1, h1, hs2]; exact hsF)
          · have he1 : ee (mp 0 + r₁) = ee (qs + r₁) := ee_eq_iff.mpr ⟨-1, by simp only [qs, Int.cast_neg, Int.cast_one]; ring⟩
            have he2 : ee (mp 0 + r₂) = ee (qs + r₂) := ee_eq_iff.mpr ⟨-1, by simp only [qs, Int.cast_neg, Int.cast_one]; ring⟩
            have h2 := hψZ.2.2.1 (by rw [he1]; exact hoff_s _ ⟨by linarith [hr₁.1], by linarith⟩)
              (by rw [he2]; exact hoff_s _ ⟨by linarith [hr₂.1], by linarith⟩) h1
            obtain ⟨j, hj⟩ := ee_eq_iff.mp (φZ.injective (Subtype.ext h2))
            have hjlt : |(j : ℝ)| < 1 := by rw [abs_lt]; exact ⟨by linarith [hr₁.1, hr₂.2, hε_s, hord'.1, hord'.2.1, hord'.2.2.1, hord'.2.2.2], by linarith [hr₁.2, hr₂.1, hε_s, hord'.1, hord'.2.1, hord'.2.2.1, hord'.2.2.2]⟩
            have hj0 : j = 0 := by have := abs_lt.mp (show |j| < 1 by exact_mod_cast hjlt); omega
            subst hj0; simp only [Int.cast_zero, add_zero] at hj; linarith
      rcases hmsc.strictMonoOn_of_injOn_Icc' (by linarith) hms_inj with hsm | hsa
      · exact ⟨ms, true, hmsc, hsm, hmse⟩
      · exact ⟨ms, false, hmsc, hsa, hmse⟩
    have hlift_t : ∃ (mt : ℝ → ℝ) (σ_t : Bool), ContinuousOn mt (Icc 0 ε) ∧
        (if σ_t then StrictMonoOn mt (Icc 0 ε) else StrictAntiOn mt (Icc 0 ε)) ∧
        (∀ r ∈ Icc 0 ε, ψZ (φZ (ee (mp 1 + r))).1 = (φt (ee (mt r))).1) := by
      let γ : ℝ → S := fun u => ψZ (φZ (ee (mp 1 + lin 0 ε u))).1
      have hγc : ContinuousOn γ (Icc 0 1) :=
        hψZ.1.comp_continuousOn ((continuous_subtype_val.comp (φZ.continuous.comp continuous_ee)).continuousOn.comp
          (continuousOn_const.add (continuousOn_lin _ _)) fun _ _ => mem_univ _)
      have hγCT : ∀ u ∈ Icc (0 : ℝ) 1, γ u ∈ connectedComponentIn (bd S) t := fun u hu => by
        rcases eq_or_lt_of_le hu.1 with rfl | hgt
        · simp only [γ, lin_zero, add_zero]; rw [hmpe 1 ⟨zero_le_one, le_rfl⟩, LP.hξ 1 ⟨zero_le_one, le_rfl⟩, haZ1]; exact mem_connectedComponentIn htb
        · have hlr : lin 0 ε u ∈ Ioc 0 ε := ⟨by simp only [lin]; nlinarith [hgt, hε], by simp only [lin]; nlinarith [hu.2, hε]⟩
          exact (hin_t _ ⟨by linarith [hlr.1], by linarith [hlr.2]⟩).1
      obtain ⟨l₀, hl0c, hl0e⟩ := exists_lift φt hγc hγCT
      let mt : ℝ → ℝ := fun r => l₀ (r / ε)
      have hmtc : ContinuousOn mt (Icc 0 ε) :=
        hl0c.comp (by fun_prop) fun r hr => ⟨div_nonneg hr.1 hε.le, (div_le_one hε).mpr hr.2⟩
      have hmte : ∀ r ∈ Icc 0 ε, ψZ (φZ (ee (mp 1 + r))).1 = (φt (ee (mt r))).1 := fun r hr => by
        have h1 := hl0e _ ⟨div_nonneg hr.1 hε.le, (div_le_one hε).mpr hr.2⟩
        have h2 : lin 0 ε (r / ε) = r := by simp only [lin]; field_simp [hε.ne']; ring
        simpa only [γ, h2, mt] using h1.symm
      have hmt_inj : InjOn mt (Icc 0 ε) := fun r₁ hr₁ r₂ hr₂ he => by
        have h1 : ψZ (φZ (ee (mp 1 + r₁))).1 = ψZ (φZ (ee (mp 1 + r₂))).1 := by rw [hmte r₁ hr₁, hmte r₂ hr₂, he]
        rcases eq_or_lt_of_le hr₁.1 with rfl | h1gt
        · rcases eq_or_lt_of_le hr₂.1 with rfl | h2gt
          · rfl
          · exfalso
            have htF : t ∈ FZ := (show t ∈ FZ ∩ bd S from hbZ ▸ mem_insert_of_mem _ rfl).1
            have ht1 : ψZ (φZ (ee (mp 1 + 0))).1 = t := by rw [add_zero, hmpe 1 ⟨zero_le_one, le_rfl⟩, LP.hξ 1 ⟨zero_le_one, le_rfl⟩, haZ1]
            exact hoff_t (pt + r₂) ⟨by linarith, by linarith [hr₂.2]⟩ (by rw [show pt = mp 1 from rfl, ← h1, ht1]; exact htF)
        · rcases eq_or_lt_of_le hr₂.1 with rfl | h2gt
          · exfalso
            have htF : t ∈ FZ := (show t ∈ FZ ∩ bd S from hbZ ▸ mem_insert_of_mem _ rfl).1
            have ht2 : ψZ (φZ (ee (mp 1 + 0))).1 = t := by rw [add_zero, hmpe 1 ⟨zero_le_one, le_rfl⟩, LP.hξ 1 ⟨zero_le_one, le_rfl⟩, haZ1]
            exact hoff_t (pt + r₁) ⟨by linarith, by linarith [hr₁.2]⟩ (by rw [show pt = mp 1 from rfl, h1, ht2]; exact htF)
          · have h2 := hψZ.2.2.1 (hoff_t _ ⟨by linarith, by linarith [hr₁.2]⟩) (hoff_t _ ⟨by linarith, by linarith [hr₂.2]⟩) h1
            obtain ⟨j, hj⟩ := ee_eq_iff.mp (φZ.injective (Subtype.ext h2))
            have hjlt : |(j : ℝ)| < 1 := by rw [abs_lt]; exact ⟨by linarith [hr₁.1, hr₂.2, hε_t, hord'.1, hord'.2.1, hord'.2.2.1, hord'.2.2.2], by linarith [hr₁.2, hr₂.1, hε_t, hord'.1, hord'.2.1, hord'.2.2.1, hord'.2.2.2]⟩
            have hj0 : j = 0 := by have := abs_lt.mp (show |j| < 1 by exact_mod_cast hjlt); omega
            subst hj0; simp only [Int.cast_zero, add_zero] at hj; linarith
      rcases hmtc.strictMonoOn_of_injOn_Icc' hε.le hmt_inj with hsm | hsa
      · exact ⟨mt, true, hmtc, hsm, hmte⟩
      · exact ⟨mt, false, hmtc, hsa, hmte⟩
    obtain ⟨ms, σ_s, hmsc, hmsd, hmse⟩ := hlift_s
    obtain ⟨mt, σ_t, hmtc, hmtd, hmte⟩ := hlift_t
    have hcoc := cocInt_arc_diff_cuff_mono hZ hS hψZ hFZ LP haZ0 haZ1 AZ AS hCZ_bd φZ
      (connectedComponentIn_subset _ _) (connectedComponentIn_subset _ _) φs φt hmpc hmpe hε σ_s σ_t
      hmsc hmtc hmsd hmtd hmse hmte
      (fun r hr => by
        have he1 : ee (mp 0 + r) = ee (qs + r) := ee_eq_iff.mpr ⟨-1, by simp only [qs, Int.cast_neg, Int.cast_one]; ring⟩
        rw [he1]; exact hoff_s _ ⟨by linarith [hr.1], by linarith [hr.2]⟩)
      (fun r hr => hoff_t _ ⟨by linarith [hr.1], by linarith [hr.2]⟩)
    refine ⟨k, ps, qs, pt, qt, σ_s, σ_t, hord'.2.2.2, by linarith [hord'.1, hord'.2.1, hord'.2.2.1],
      hord'.2.1, by linarith [hord'.1, hord'.2.2.1, hord'.2.2.2], hin_s, hin_t, ⟨hps_e, hqs_e, hpt_e, hqt_e⟩,
      fun v hv => ?_, fun v hv => ?_, hcoc, fun v hv => ?_, fun v hv => ?_⟩
    · obtain ⟨δ, ml, dl, hδ, _, hmlc, hmld, hmle, _⟩ :=
        exists_cuff_local_dir hZ hS hψZ hFZ AZ AS hCZ_bd hCs_cuff φZ φs (hin_s v hv).1 (hin_s v hv).2
      have hmid_in : qs - ε / 2 ∈ Ioo ps qs := ⟨by linarith, by linarith⟩
      have hms_loc : ∀ r ∈ Icc (-(ε / 4)) (ε / 4), ψZ (φZ (ee (qs - ε / 2 + r))).1 = (φs (ee (ms (-ε / 2 + r)))).1 := fun r hr => by
        have he1 : ee (qs - ε / 2 + r) = ee (mp 0 + (-ε / 2 + r)) := ee_eq_iff.mpr ⟨1, by simp only [qs, Int.cast_one]; ring⟩
        rw [he1]; exact hmse _ ⟨by linarith [hr.1], by linarith [hr.2]⟩
      have hdl_eq : dl = σ_s := local_dir_eq_on_interval hψZ φZ φs hord'.2.2.2 (by linarith [hord'.1, hord'.2.1, hord'.2.2.1])
        hin_s hv hmid_in hδ (by linarith : (0 : ℝ) < ε / 4) (m₂ := fun r => ms (-ε / 2 + r)) hmlc
        (hmsc.comp ((continuousOn_const (c := -ε / 2)).add continuousOn_id) fun r hr => ⟨by linarith [hr.1], by linarith [hr.2]⟩)
        hmld
        (by cases σ_s <;> simp only [Bool.false_eq_true, ↓reduceIte] at hmsd ⊢ <;>
            exact fun a ha b hb h => hmsd ⟨by linarith [ha.1], by linarith [ha.2]⟩ ⟨by linarith [hb.1], by linarith [hb.2]⟩ (by linarith))
        hmle hms_loc
      subst hdl_eq; exact ⟨δ, ml, hδ, hmlc, hmld, hmle⟩
    · obtain ⟨δ, ml, dl, hδ, _, hmlc, hmld, hmle, _⟩ :=
        exists_cuff_local_dir hZ hS hψZ hFZ AZ AS hCZ_bd hCt_cuff φZ φt (hin_t v hv).1 (hin_t v hv).2
      have hmid_in : pt + ε / 2 ∈ Ioo pt qt := ⟨by linarith, by linarith⟩
      have hmt_loc : ∀ r ∈ Icc (-(ε / 4)) (ε / 4), ψZ (φZ (ee (pt + ε / 2 + r))).1 = (φt (ee (mt (ε / 2 + r)))).1 := fun r hr => by
        rw [show pt + ε / 2 + r = mp 1 + (ε / 2 + r) by simp [pt]; ring]
        exact hmte _ ⟨by linarith [hr.1], by linarith [hr.2]⟩
      have hdl_eq : dl = σ_t := local_dir_eq_on_interval hψZ φZ φt hord'.2.1 (by linarith [hord'.1, hord'.2.2.1, hord'.2.2.2])
        hin_t hv hmid_in hδ (by linarith : (0 : ℝ) < ε / 4) (m₂ := fun r => mt (ε / 2 + r)) hmlc
        (hmtc.comp ((continuousOn_const (c := ε / 2)).add continuousOn_id) fun r hr => ⟨by linarith [hr.1], by linarith [hr.2]⟩)
        hmld
        (by cases σ_t <;> simp only [Bool.false_eq_true, ↓reduceIte] at hmtd ⊢ <;>
            exact fun a ha b hb h => hmtd ⟨by linarith [ha.1], by linarith [ha.2]⟩ ⟨by linarith [hb.1], by linarith [hb.2]⟩ (by linarith))
        hmle hmt_loc
      subst hdl_eq; exact ⟨δ, ml, hδ, hmlc, hmld, hmle⟩
    · set w := mp 0 + Int.fract (v - mp 0)
      have hwee : ee w = ee v := ee_eq_iff.mpr ⟨-⌊v - mp 0⌋, by simp only [w, Int.cast_neg]; linarith [Int.floor_add_fract (v - mp 0)]⟩
      have hwnF : ψZ (φZ (ee w)).1 ∉ FZ := fun h => hv.2 (hbZ ▸ ⟨by rwa [hwee] at h, connectedComponentIn_subset _ _ hv.1⟩)
      have hw_lo : mp 0 ≤ w := by simp only [w]; linarith [Int.fract_nonneg (v - mp 0)]
      have hw_hi : w < qs := by simp only [w, qs]; linarith [Int.fract_lt_one (v - mp 0)]
      have hw_gt1 : pt < w := by
        by_contra hle'
        obtain ⟨u, hu, hue⟩ := intermediate_value_Icc zero_le_one hmpc (show w ∈ Icc (mp 0) (mp 1) from ⟨hw_lo, not_lt.mp hle'⟩)
        exact hwnF (by rw [← hue, hmpe u hu]; exact show ξP u ∈ ψZ ⁻¹' FZ from hunP ▸ Or.inl (himP1 ▸ ⟨u, hu, rfl⟩))
      have hw_not2 : w ∉ Icc qt ps := fun hmem => by
        obtain ⟨u, hu, hue⟩ := intermediate_value_Icc' zero_le_one hmnc (show w - k ∈ Icc (mn 1) (mn 0) from ⟨by linarith [hmem.1], by linarith [hmem.2]⟩)
        exact hwnF (by rw [show ee w = ee (mn u) from ee_eq_iff.mpr ⟨k, by linarith⟩, hmne u hu]; exact show ηP u ∈ ψZ ⁻¹' FZ from hunP ▸ Or.inr (himP2 ▸ ⟨u, hu, rfl⟩))
      have hw_nott : ¬ w < qt := fun hlt =>
        Set.disjoint_left.mp (cuffs_disjoint hCs_cuff hCt_cuff hst) (hwee ▸ hv.1) (hin_t w ⟨hw_gt1, hlt⟩).1
      exact ⟨w, ⟨lt_of_not_ge fun hle' => hw_not2 ⟨not_lt.mp hw_nott, hle'⟩, hw_hi⟩, hwee⟩
    · set w := mp 0 + Int.fract (v - mp 0)
      have hwee : ee w = ee v := ee_eq_iff.mpr ⟨-⌊v - mp 0⌋, by simp only [w, Int.cast_neg]; linarith [Int.floor_add_fract (v - mp 0)]⟩
      have hwnF : ψZ (φZ (ee w)).1 ∉ FZ := fun h => hv.2 (hbZ ▸ ⟨by rwa [hwee] at h, connectedComponentIn_subset _ _ hv.1⟩)
      have hw_lo : mp 0 ≤ w := by simp only [w]; linarith [Int.fract_nonneg (v - mp 0)]
      have hw_hi : w < qs := by simp only [w, qs]; linarith [Int.fract_lt_one (v - mp 0)]
      have hw_gt1 : pt < w := by
        by_contra hle'
        obtain ⟨u, hu, hue⟩ := intermediate_value_Icc zero_le_one hmpc (show w ∈ Icc (mp 0) (mp 1) from ⟨hw_lo, not_lt.mp hle'⟩)
        exact hwnF (by rw [← hue, hmpe u hu]; exact show ξP u ∈ ψZ ⁻¹' FZ from hunP ▸ Or.inl (himP1 ▸ ⟨u, hu, rfl⟩))
      have hw_not2 : w ∉ Icc qt ps := fun hmem => by
        obtain ⟨u, hu, hue⟩ := intermediate_value_Icc' zero_le_one hmnc (show w - k ∈ Icc (mn 1) (mn 0) from ⟨by linarith [hmem.1], by linarith [hmem.2]⟩)
        exact hwnF (by rw [show ee w = ee (mn u) from ee_eq_iff.mpr ⟨k, by linarith⟩, hmne u hu]; exact show ηP u ∈ ψZ ⁻¹' FZ from hunP ▸ Or.inr (himP2 ▸ ⟨u, hu, rfl⟩))
      have hw_lt : w < qt := by
        by_contra hge'
        have hw_gt2 : ps < w := lt_of_not_ge fun hle' => hw_not2 ⟨not_lt.mp hge', hle'⟩
        exact Set.disjoint_left.mp (cuffs_disjoint hCs_cuff hCt_cuff hst) (hin_s w ⟨hw_gt2, hw_hi⟩).1 (hwee ▸ hv.1)
      exact ⟨w, ⟨hw_gt1, hw_lt⟩, hwee⟩
  cases dm
  · simp only [Bool.false_eq_true, ↓reduceIte] at hdm1 hdm2
    have hPZ_sw : LiftPair ψZ FZ s t XZ' XZ := by
      obtain ⟨x0, x1, y0, y1, l1, l2, hd0, hun0, b1, b2, h7, h8, h9, h10⟩ := id hPZ
      exact ⟨y0, y1, x0, x1, l2, l1, hd0.symm, by rw [union_comm]; exact hun0, b2, b1, h8, h7, h10, h9⟩
    obtain ⟨k, ps, qs, pt, qt, σ_s, σ_t, hrest⟩ :=
      hord_pos ηZ ξZ XZ' XZ hPZ_sw LZ.swap him2 him1 hi2 hi1 m₂ m₁ hm2c hdm2 hm2e hm1c hdm1 hm1e
    exact ⟨false, k, ps, qs, pt, qt, σ_s, σ_t, hdm1, hdm2, hrest⟩
  · simp only [↓reduceIte] at hdm1 hdm2
    obtain ⟨k, ps, qs, pt, qt, σ_s, σ_t, hrest⟩ :=
      hord_pos ξZ ηZ XZ XZ' hPZ LZ him1 him2 hi1 hi2 m₁ m₂ hm1c hdm1 hm1e hm2c hdm2 hm2e
    exact ⟨true, k, ps, qs, pt, qt, σ_s, σ_t, hdm1, hdm2, hrest⟩

end CutCuffInfo

end GraphMinor.GHR18
