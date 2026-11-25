module

public import GraphMinor.GHR18.ArcCocycle

/-!
# Orientation integrals along cuffs and cut lifts

This file proves the four orientation-integral lemmas needed for the Master Arc-Parallelism Theorem:
1. `cocInt_pbk_cont`: pullback of `cocInt` along any continuous map;
2. `cocInt_w1_cuff` and `cocInt_w1_cut_cuff`: integrating `w1` along a path inside a boundary cuff
   (before or after projecting through a cutting `ψ : Y → S`);
3. `cut_lift_opp_sign`: along the two lifts `ξ, η` of a proper `I`-arc `F` under a cutting `ψ : Y → S`,
   the local orientation invariant `cuffSign + cutOrientDiff + dirSign` takes OPPOSITE values in
   `ZMod 2` at `ξ(1/2)` and `η(1/2)`;
4. `same_cuff_oneSided_of_cocInt` and `diff_cuff_relOrient_of_cocInt`:
   - when `s, t` lie on the same cuff `C`, `cocInt (w1 AS) (a ++ A₁)` equals `0` if `F` is 2-sided
     (splits `C` into two cuffs of `Y`) and `1` if `F` is 1-sided (keeps `C` as one cuff of `Y`);
   - when `s ∈ C_s` and `t ∈ C_t` lie on distinct cuffs, `cocInt (w1 AS) a` determines the relative
     orientation of `C_s` and `C_t` in the merged cuff of `Y`.
-/

@[expose] public section

namespace GraphMinor.GHR18

open Set Topology Function Metric GraphMinor.Surface

universe u

/-! ### Cocycle integrals along continuous pullbacks and boundary cuffs -/

section CocIntCuff

variable {X Y S : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace S]

/-- Pullback of `cocInt` along any continuous map `f : X → Y`. -/
theorem cocInt_pbk_cont {A : Type} [AddCommGroup A] {f : X → Y} (hf : Continuous f)
    {φ : Y → Y → A} (hφ : IsCoc φ) {γ : ℝ → X} (hγ : ContinuousOn γ (Icc 0 1)) :
    cocInt (pbk f φ) γ = cocInt φ (f ∘ γ) := by
  obtain ⟨N, hN, hc⟩ := hφ
  have hNf : NearDiag ((fun p : X × X => (f p.1, f p.2)) ⁻¹' N) := fun x =>
    ((hf.comp continuous_fst).prodMk (hf.comp continuous_snd)).continuousAt.preimage_mem_nhds (hN (f x))
  obtain ⟨n₁, -, hn₁⟩ := cocInt_eq_sum (φ := pbk f φ) hNf (fun x y z h1 h2 h3 => hc _ _ _ h1 h2 h3) hγ
  obtain ⟨n₂, -, hn₂⟩ := cocInt_eq_sum hN hc (hf.comp_continuousOn hγ)
  set M := max n₁ n₂
  rw [hn₁ M (le_max_left _ _), hn₂ M (le_max_right _ _)]
  rfl

/-- Integrating `w1 A` along any continuous path inside a cuff `C ⊆ bd S` parameterized by `φ`
equals the difference of `cuffSign A φ` at its endpoints. -/
theorem cocInt_w1_cuff (hS : IsSurface S) (A : SurfAtlas S) {C : Set S} (hC : C ⊆ bd S)
    (φ : Circle ≃ₜ C) {γ : ℝ → S} (hγ : ContinuousOn γ (Icc 0 1)) (hγC : ∀ u ∈ Icc (0 : ℝ) 1, γ u ∈ C) :
    cocInt (w1 A) γ = cuffSign A φ (γ 1) - cuffSign A φ (γ 0) := by
  obtain ⟨N₁, hN₁, hcoc⟩ := isCoc_w1 hS A
  obtain ⟨N₂, hN₂, hdiff⟩ := cuffSign_diff hS A hC φ
  have hN : NearDiag (N₁ ∩ N₂) := fun x => Filter.inter_mem (hN₁ x) (hN₂ x)
  obtain ⟨δ, hδpos, hδ⟩ := exists_delta_curve hγ hN
  obtain ⟨n₀, -, hn₀⟩ := cocInt_eq_sum hN₁ hcoc hγ
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / δ)
  set n := max n₀ (max m 1)
  have hn_pos : 0 < n := lt_of_lt_of_le one_pos ((le_max_right m 1).trans (le_max_right _ _))
  have hn_r : (0 : ℝ) < n := by exact_mod_cast hn_pos
  have hn_lt : 1 / (n : ℝ) < δ := by
    have h1 : 1 / δ < n := lt_of_lt_of_le hm (by exact_mod_cast (le_max_left m 1).trans (le_max_right _ _))
    rw [div_lt_iff₀ hn_r]; have := (div_lt_iff₀ hδpos).mp h1; linarith
  rw [hn₀ n (le_max_left _ _)]
  unfold cocSum
  have hstep : ∀ k ∈ Finset.range n,
      w1 A (γ ((k : ℝ) / n)) (γ (((k + 1 : ℕ) : ℝ) / n)) =
        cuffSign A φ (γ (((k + 1 : ℕ) : ℝ) / n)) - cuffSign A φ (γ ((k : ℝ) / n)) := by
    intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    have hk1 : (k : ℝ) / n ∈ Icc (0 : ℝ) 1 := ⟨by positivity, (div_le_one hn_r).mpr (by exact_mod_cast hk'.le)⟩
    have hk2 : ((k + 1 : ℕ) : ℝ) / n ∈ Icc (0 : ℝ) 1 := ⟨by positivity, (div_le_one hn_r).mpr (by exact_mod_cast hk')⟩
    have hnear := hδ _ hk1 _ hk2 (by
      have hsub : (k : ℝ) / n - ((k + 1 : ℕ) : ℝ) / n = -1 / (n : ℝ) := by push_cast; field_simp; ring
      rw [hsub, abs_div, abs_neg, abs_one, abs_of_pos hn_r]
      exact hn_lt)
    exact hdiff _ (hγC _ hk1) _ (hγC _ hk2) hnear.2
  rw [Finset.sum_congr rfl hstep, Finset.sum_range_sub (fun k => cuffSign A φ (γ ((k : ℝ) / n))) n]
  have hn0 : (n : ℝ) ≠ 0 := hn_r.ne'
  simp [hn0]

/-- Integrating `w1 AS` along `ψ ∘ γ`, where `γ` is a continuous path inside a cuff `C ⊆ bd Y`
of a cut surface `Y`, equals the change in `cuffSign AY φ + cutOrientDiff AY AS ψ`! -/
theorem cocInt_w1_cut_cuff (hY : IsSurface Y) (hS : IsSurface S) {ψ : Y → S} {F : Set S}
    (hψ : IsCutting ψ F) (hF : IsClosed F) (AY : SurfAtlas Y) (AS : SurfAtlas S)
    {C : Set Y} (hC : C ⊆ bd Y) (φ : Circle ≃ₜ C)
    {γ : ℝ → Y} (hγ : ContinuousOn γ (Icc 0 1)) (hγC : ∀ u ∈ Icc (0 : ℝ) 1, γ u ∈ C) :
    cocInt (w1 AS) (ψ ∘ γ) =
      (cuffSign AY φ (γ 1) + cutOrientDiff AY AS ψ (γ 1)) -
      (cuffSign AY φ (γ 0) + cutOrientDiff AY AS ψ (γ 0)) := by
  have hcocS := isCoc_w1 hS AS
  have hcocY := isCoc_w1 hY AY
  have hcocP : IsCoc (pbk ψ (w1 AS)) := by
    obtain ⟨NS, hNS, hcS⟩ := hcocS
    exact ⟨(fun p : Y × Y => (ψ p.1, ψ p.2)) ⁻¹' NS, fun y =>
      ((hψ.1.comp continuous_fst).prodMk (hψ.1.comp continuous_snd)).continuousAt.preimage_mem_nhds (hNS (ψ y)),
      fun _ _ _ h1 h2 h3 => hcS _ _ _ h1 h2 h3⟩
  obtain ⟨N, hN, hdiff⟩ := cohRel_w1_cut_explicit hY hS hψ hF AY AS
  have h1 := cocInt_of_cohRel hcocP hcocY hN hdiff hγ
  have h2 := cocInt_pbk_cont hψ.1 hcocS hγ
  have h3 := cocInt_w1_cuff hY AY hC φ hγ hγC
  rw [h2, h3] at h1
  linear_combination h1

/-- Reparameterizing a path on `[0, 1]` by a strictly increasing bijection `[0, 1] → [0, 1]`
preserves `cocInt`. -/
theorem cocInt_reparam_mono {A : Type} [AddCommGroup A] {φ : X → X → A} (hφ : IsCoc φ)
    {γ : ℝ → X} (hγ : ContinuousOn γ (Icc 0 1)) {ρ : ℝ → ℝ}
    (hρc : ContinuousOn ρ (Icc 0 1)) (hρm : ∀ u ∈ Icc (0 : ℝ) 1, ρ u ∈ Icc (0 : ℝ) 1)
    (hρ0 : ρ 0 = 0) (hρ1 : ρ 1 = 1) :
    cocInt φ (γ ∘ ρ) = cocInt φ γ :=
  cocInt_reparam hφ hγ hρc hρm hρ0 hρ1

end CocIntCuff

/-! ### Local orientation of a reflection-plus-monotone map `x + i y ↦ (-x + 2) + i * σ(y)` -/

section MonotoneReflection

/-- Homotopy lemma: for a continuous strictly increasing `σ : ℝ → ℝ`, the map
`g(z) = (-z.re + 2) + σ(z.im) * I` is locally orientation-reversing (`¬ IsPosLocal g z₀`). -/
theorem not_isPosLocal_flip_re_strictMono {σ : ℝ → ℝ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hσc : ContinuousOn σ (Icc (z₀.im - r) (z₀.im + r)))
    (hσm : StrictMonoOn σ (Icc (z₀.im - r) (z₀.im + r))) :
    ¬ IsPosLocal (fun z : ℂ => ((-z.re + 2 : ℝ) : ℂ) + (σ z.im : ℂ) * Complex.I) z₀ := by
  let g : ℂ → ℂ := fun z => ((-z.re + 2 : ℝ) : ℂ) + (σ z.im : ℂ) * Complex.I
  have hmem_im : ∀ z ∈ closedBall z₀ r, z.im ∈ Icc (z₀.im - r) (z₀.im + r) := fun z hz => by
    have h1 : |z.im - z₀.im| ≤ r := (Complex.abs_im_le_norm (z - z₀)).trans (by simpa [mem_closedBall, dist_eq_norm] using hz)
    exact ⟨by linarith [(abs_le.mp h1).1], by linarith [(abs_le.mp h1).2]⟩
  have hgc : ContinuousOn g (closedBall z₀ r) := by
    refine ContinuousOn.add (Complex.continuous_ofReal.comp_continuousOn
      ((Complex.continuous_re.neg.add continuous_const).continuousOn)) ?_
    exact (Complex.continuous_ofReal.comp_continuousOn (hσc.comp Complex.continuous_im.continuousOn hmem_im)).mul continuousOn_const
  have hgi : InjOn g (closedBall z₀ r) := by
    intro z₁ hz₁ z₂ hz₂ he
    have hre : -z₁.re + 2 = -z₂.re + 2 := by simpa [g] using congrArg Complex.re he
    have him : σ z₁.im = σ z₂.im := by simpa [g] using congrArg Complex.im he
    exact Complex.ext (by linarith) (hσm.injOn (hmem_im z₁ hz₁) (hmem_im z₂ hz₂) him)
  rw [isPosLocal_iff_wind_pos hr hgc hgi]
  let cl : ℝ → ℝ := fun u => max 0 (min u 1)
  have hcl_cont : Continuous cl := continuous_const.max (continuous_id.min continuous_const)
  let F : ℝ → Circle → ℂ := fun u w =>
    let z := z₀ + (r : ℂ) * (w : ℂ)
    ((-z.re + 2 : ℝ) : ℂ) + (((1 - cl u) * (σ z.im - σ z₀.im) + cl u * (z.im - z₀.im) + σ z₀.im : ℝ) : ℂ) * Complex.I
  have hFc : Continuous (fun q : ℝ × Circle => F q.1 q.2) := by
    have hz_c : Continuous (fun q : ℝ × Circle => z₀ + (r : ℂ) * (q.2 : ℂ)) :=
      continuous_const.add (continuous_const.mul (continuous_subtype_val.comp continuous_snd))
    have hσ_c : Continuous (fun q : ℝ × Circle => σ (z₀ + (r : ℂ) * (q.2 : ℂ)).im) :=
      hσc.comp_continuous (Complex.continuous_im.comp hz_c) fun q => hmem_im _ (by
        simp [mem_closedBall, dist_eq_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, Circle.norm_coe])
    have hcl_c : Continuous (fun q : ℝ × Circle => cl q.1) := hcl_cont.comp continuous_fst
    refine Continuous.add (Complex.continuous_ofReal.comp ((Complex.continuous_re.comp hz_c).neg.add continuous_const)) ?_
    refine (Complex.continuous_ofReal.comp ?_).mul continuous_const
    exact (((continuous_const.sub hcl_c).mul (hσ_c.sub continuous_const)).add
      (hcl_c.mul ((Complex.continuous_im.comp hz_c).sub continuous_const))).add continuous_const
  have hne : ∀ u (w : Circle), F u w ≠ g z₀ := by
    intro u w h
    set z := z₀ + (r : ℂ) * (w : ℂ)
    have hre : -z.re + 2 = -z₀.re + 2 := by simpa [F, g, z] using congrArg Complex.re h
    have him : (1 - cl u) * (σ z.im - σ z₀.im) + cl u * (z.im - z₀.im) + σ z₀.im = σ z₀.im := by
      simpa [F, g, z] using congrArg Complex.im h
    have him0 : (1 - cl u) * (σ z.im - σ z₀.im) + cl u * (z.im - z₀.im) = 0 := by linarith
    have hz_mem : z ∈ closedBall z₀ r := by
      simp [z, mem_closedBall, dist_eq_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, Circle.norm_coe]
    have hz_ne : z ≠ z₀ := by
      intro hz0
      have h1 : (r : ℂ) * (w : ℂ) = 0 := by linear_combination hz0
      have h2 := congrArg norm h1
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, Circle.norm_coe] at h2
      linarith
    have him_ne : z.im ≠ z₀.im := fun him_eq => hz_ne (Complex.ext (by linarith) him_eq)
    have hcl0 : 0 ≤ cl u := le_max_left _ _
    have hcl1 : cl u ≤ 1 := max_le zero_le_one (min_le_right _ _)
    have h1cl : 0 ≤ 1 - cl u := by linarith
    rcases lt_or_gt_of_ne him_ne with hlt | hgt
    · have hσlt : σ z.im < σ z₀.im := hσm (hmem_im z hz_mem) (hmem_im z₀ (mem_closedBall_self hr.le)) hlt
      have : (1 - cl u) * (σ z.im - σ z₀.im) + cl u * (z.im - z₀.im) < 0 := by
        by_cases hc0 : cl u = 0
        · rw [hc0]; simp; linarith
        · nlinarith [lt_of_le_of_ne hcl0 (Ne.symm hc0)]
      linarith
    · have hσgt : σ z₀.im < σ z.im := hσm (hmem_im z₀ (mem_closedBall_self hr.le)) (hmem_im z hz_mem) hgt
      have : 0 < (1 - cl u) * (σ z.im - σ z₀.im) + cl u * (z.im - z₀.im) := by
        by_cases hc0 : cl u = 0
        · rw [hc0]; simp; linarith
        · nlinarith [lt_of_le_of_ne hcl0 (Ne.symm hc0)]
      linarith
  have hhom := wind_eq_of_family hFc continuous_const hne 0 1
  have hF0 : F 0 = fun w : Circle => g (z₀ + (r : ℂ) * (w : ℂ)) := by
    funext w; apply Complex.ext <;> simp [F, g, cl]
  have hF1 : F 1 = fun w : Circle => g z₀ + (-(r : ℂ)) * (starRingEnd ℂ (w : ℂ)) := by
    funext w; apply Complex.ext <;> simp [F, g, cl] <;> ring
  rw [hF0, hF1] at hhom
  -- Compare with `-starRingEnd ℂ z + (2 + (σ z₀.im - z₀.im) * I)` which is NOT `IsPosLocal`!
  let f1 : ℂ → ℂ := fun z => (-1 : ℂ) * starRingEnd ℂ z + ((2 : ℂ) + ((σ z₀.im - z₀.im : ℝ) : ℂ) * Complex.I)
  have hf1_eq : ∀ w : Circle, f1 (z₀ + (r : ℂ) * (w : ℂ)) = g z₀ + (-(r : ℂ)) * (starRingEnd ℂ (w : ℂ)) := fun w => by
    apply Complex.ext <;> simp [f1, g] <;> ring
  have hf1_z0 : f1 z₀ = g z₀ := by apply Complex.ext <;> simp [f1, g]
  have hf1_not : ¬ IsPosLocal f1 z₀ := by
    have hcomp : f1 = (fun w => (-1 : ℂ) * w + ((2 : ℂ) + ((σ z₀.im - z₀.im : ℝ) : ℂ) * Complex.I)) ∘ (starRingEnd ℂ) := rfl
    have haff_c : ContinuousOn (fun w : ℂ => (-1 : ℂ) * w + ((2 : ℂ) + ((σ z₀.im - z₀.im : ℝ) : ℂ) * Complex.I)) univ := by fun_prop
    have haff_i : InjOn (fun w : ℂ => (-1 : ℂ) * w + ((2 : ℂ) + ((σ z₀.im - z₀.im : ℝ) : ℂ) * Complex.I)) univ :=
      fun a _ b _ h => by linear_combination -h
    rw [hcomp, isPosLocal_comp isOpen_univ Complex.continuous_conj.continuousOn
      (starRingEnd ℂ).injective.injOn (subset_univ _) haff_c haff_i (mem_univ z₀)]
    have haff := isPosLocal_affine (show (-1 : ℂ) ≠ 0 by norm_num)
      ((2 : ℂ) + ((σ z₀.im - z₀.im : ℝ) : ℂ) * Complex.I) (starRingEnd ℂ z₀)
    have hconj := not_isPosLocal_conj z₀
    tauto
  have hf1_c : ContinuousOn f1 (closedBall z₀ r) :=
    ((continuous_const.mul Complex.continuous_conj).add continuous_const).continuousOn
  have hf1_i : InjOn f1 (closedBall z₀ r) := fun a _ b _ h => by
    have h1 : starRingEnd ℂ a = starRingEnd ℂ b := by linear_combination -h
    exact (starRingEnd ℂ).injective h1
  rw [isPosLocal_iff_wind_pos hr hf1_c hf1_i, hf1_z0] at hf1_not
  have hfun_eq : (fun w : Circle => f1 (z₀ + (r : ℂ) * (w : ℂ))) =
      fun w : Circle => g z₀ + (-(r : ℂ)) * (starRingEnd ℂ (w : ℂ)) := funext hf1_eq
  rw [hfun_eq] at hf1_not
  rw [hhom]
  exact hf1_not

/-- Homotopy lemma: for a continuous strictly decreasing `σ : ℝ → ℝ`, the map
`g(z) = (-z.re + 2) + σ(z.im) * I` is locally orientation-preserving (`IsPosLocal g z₀`). -/
theorem isPosLocal_flip_re_strictAnti {σ : ℝ → ℝ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hσc : ContinuousOn σ (Icc (z₀.im - r) (z₀.im + r)))
    (hσa : StrictAntiOn σ (Icc (z₀.im - r) (z₀.im + r))) :
    IsPosLocal (fun z : ℂ => ((-z.re + 2 : ℝ) : ℂ) + (σ z.im : ℂ) * Complex.I) z₀ := by
  let g : ℂ → ℂ := fun z => ((-z.re + 2 : ℝ) : ℂ) + (σ z.im : ℂ) * Complex.I
  -- Compose `g` with `starRingEnd ℂ` on the left: `conj ∘ g` has `σ' = -σ` (strictly increasing)!
  let g' : ℂ → ℂ := fun z => ((-z.re + 2 : ℝ) : ℂ) + ((-σ z.im : ℝ) : ℂ) * Complex.I
  have hmem_im : ∀ z ∈ closedBall z₀ r, z.im ∈ Icc (z₀.im - r) (z₀.im + r) := fun z hz => by
    have h1 : |z.im - z₀.im| ≤ r := (Complex.abs_im_le_norm (z - z₀)).trans (by simpa [mem_closedBall, dist_eq_norm] using hz)
    exact ⟨by linarith [(abs_le.mp h1).1], by linarith [(abs_le.mp h1).2]⟩
  have hgc : ContinuousOn g (ball z₀ r) := by
    refine ContinuousOn.add (Complex.continuous_ofReal.comp_continuousOn
      ((Complex.continuous_re.neg.add continuous_const).continuousOn)) ?_
    exact (Complex.continuous_ofReal.comp_continuousOn
      (hσc.comp Complex.continuous_im.continuousOn (fun z hz => hmem_im z (ball_subset_closedBall hz)))).mul continuousOn_const
  have hgi : InjOn g (ball z₀ r) := by
    intro z₁ hz₁ z₂ hz₂ he
    have hre : -z₁.re + 2 = -z₂.re + 2 := by simpa [g] using congrArg Complex.re he
    have him : σ z₁.im = σ z₂.im := by simpa [g] using congrArg Complex.im he
    exact Complex.ext (by linarith)
      (hσa.injOn (hmem_im z₁ (ball_subset_closedBall hz₁)) (hmem_im z₂ (ball_subset_closedBall hz₂)) him)
  have hcomp : g' = (starRingEnd ℂ) ∘ g := by
    funext z; apply Complex.ext <;> simp [g', g]
  have hnot : ¬ IsPosLocal g' z₀ :=
    not_isPosLocal_flip_re_strictMono hr hσc.neg (fun a ha b hb hab => neg_lt_neg (hσa ha hb hab))
  rw [hcomp, isPosLocal_comp isOpen_ball hgc hgi (subset_univ _) Complex.continuous_conj.continuousOn
    (starRingEnd ℂ).injective.injOn (mem_ball_self hr)] at hnot
  have hconj := not_isPosLocal_conj (g z₀)
  tauto

end MonotoneReflection

/-! ### Opposite boundary orientation along the two lifts of a cut arc -/

section LiftOppSign

variable {Y S : Type u} [TopologicalSpace Y] [TopologicalSpace S]

/-- Helper: comparing `cuffPos c φ (ξ (1/2))` against the monotonicity directions of `m` (lift of `ξ`
into `φ`) and `u ↦ (c.j (ξ u)).im` (vertical direction of `ξ` in chart `c`). -/
private theorem cuffPos_iff_dir_eq {c : SurfChart Y} {C : Set Y} (hC : C ⊆ bd Y)
    (φ : Circle ≃ₜ C) {ξ : ℝ → Y} {m : ℝ → ℝ} {u₀ : ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hξU : ∀ u ∈ Icc (u₀ - δ) (u₀ + δ), ξ u ∈ c.U)
    (hmc : ContinuousOn m (Icc (u₀ - δ) (u₀ + δ)))
    (hmξ : ∀ u ∈ Icc (u₀ - δ) (u₀ + δ), (φ (ee (m u))).1 = ξ u)
    (hσm : Bool)
    (hm_dir : if hσm then StrictMonoOn m (Icc (u₀ - δ) (u₀ + δ)) else StrictAntiOn m (Icc (u₀ - δ) (u₀ + δ)))
    (hσc : Bool)
    (hc_dir : if hσc then StrictMonoOn (fun u => (c.j (ξ u)).im) (Icc (u₀ - δ) (u₀ + δ))
              else StrictAntiOn (fun u => (c.j (ξ u)).im) (Icc (u₀ - δ) (u₀ + δ))) :
    cuffPos c φ (ξ u₀) ↔ hσm = hσc := by
  have hu₀ : u₀ ∈ Icc (u₀ - δ) (u₀ + δ) := ⟨by linarith, by linarith⟩
  have hCmem : ξ u₀ ∈ C := (hmξ u₀ hu₀) ▸ (φ (ee (m u₀))).2
  obtain ⟨v₀, δ₁, hδ₁, -, hv₀, hδ₁U, hmo⟩ := cuff_im_mono_or_anti hC φ hCmem (hξU u₀ hu₀)
  obtain ⟨k, hk⟩ := ee_eq_iff.mp (φ.injective (Subtype.ext (hv₀.trans (hmξ u₀ hu₀).symm)))
  have hshift : ∀ t, (φ (ee (v₀ + t))).1 = (φ (ee (m u₀ + t))).1 := fun t => by
    have : ee (v₀ + t) = ee (m u₀ + t) := ee_eq_iff.mpr ⟨k, by linarith⟩
    rw [this]
  -- Pick `η > 0` small enough so `m (u₀ + η) - m u₀ ∈ (-δ₁, δ₁)`:
  have hm_at : ContinuousAt m u₀ := hmc.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.continuousAt_iff.mp hm_at δ₁ hδ₁
  set η := min (δ / 2) (ρ / 2)
  have hη : 0 < η := lt_min (half_pos hδ) (half_pos hρ)
  have huη : u₀ + η ∈ Icc (u₀ - δ) (u₀ + δ) :=
    ⟨by linarith [min_le_left (δ / 2) (ρ / 2)], by linarith [min_le_left (δ / 2) (ρ / 2)]⟩
  have hdist_m : |m (u₀ + η) - m u₀| < δ₁ := by
    have := hρsub (x := u₀ + η) (by
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hη]
      exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hρ))
    simpa [Real.dist_eq] using this
  set t₁ := m (u₀ + η) - m u₀
  have ht₁I : t₁ ∈ Icc (-δ₁) δ₁ := ⟨by linarith [(abs_lt.mp hdist_m).1], by linarith [(abs_lt.mp hdist_m).2]⟩
  have h0I : (0 : ℝ) ∈ Icc (-δ₁) δ₁ := ⟨by linarith, hδ₁.le⟩
  have heq0 : (φ (ee (v₀ + 0))).1 = ξ u₀ := by rw [add_zero]; exact hv₀
  have heq1 : (φ (ee (v₀ + t₁))).1 = ξ (u₀ + η) := by
    rw [hshift t₁, show m u₀ + t₁ = m (u₀ + η) by ring]; exact hmξ (u₀ + η) huη
  have hnot_anti : StrictAntiOn (fun t => (c.j (φ (ee (v₀ + t))).1).im) (Icc (-δ₁) δ₁) → ¬ cuffPos c φ (ξ u₀) := by
    rintro hanti ⟨u', δ', hδ', hu', -, hmono'⟩
    obtain ⟨k', hk'⟩ := ee_eq_iff.mp (φ.injective (Subtype.ext (hu'.trans hv₀.symm)))
    set s := min δ₁ δ'
    have hs : 0 < s := lt_min hδ₁ hδ'
    have h1 := hanti h0I ⟨by linarith [min_le_left δ₁ δ'], min_le_left _ _⟩ hs
    have h2 := hmono' ⟨by linarith, hδ'.le⟩ ⟨by linarith [min_le_right δ₁ δ'], min_le_right _ _⟩ hs
    have he1 : ee (u' + 0) = ee (v₀ + 0) := ee_eq_iff.mpr ⟨k', by linarith⟩
    have he2 : ee (u' + s) = ee (v₀ + s) := ee_eq_iff.mpr ⟨k', by linarith⟩
    change (c.j (φ (ee (v₀ + s))).1).im < (c.j (φ (ee (v₀ + 0))).1).im at h1
    change (c.j (φ (ee (u' + 0))).1).im < (c.j (φ (ee (u' + s))).1).im at h2
    rw [he1, he2] at h2; linarith
  cases hσm <;> cases hσc
  · -- `false, false`: `m` decreasing (`t₁ < 0`), `im` decreasing (`im(u₀ + η) < im(u₀)`):
    simp only [Bool.false_eq_true, ↓reduceIte] at hm_dir hc_dir
    have ht₁_neg : t₁ < 0 := sub_neg.mpr (hm_dir hu₀ huη (by linarith))
    have him_lt : (c.j (ξ (u₀ + η))).im < (c.j (ξ u₀)).im := hc_dir hu₀ huη (by linarith)
    rcases hmo with hmono | hanti
    · exact iff_of_true ⟨v₀, δ₁, hδ₁, hv₀, hδ₁U, hmono⟩ rfl
    · exfalso; have := hanti ht₁I h0I ht₁_neg
      change (c.j (φ (ee (v₀ + 0))).1).im < (c.j (φ (ee (v₀ + t₁))).1).im at this
      rw [heq0, heq1] at this; linarith
  · -- `false, true`: `m` decreasing (`t₁ < 0`), `im` increasing (`im(u₀) < im(u₀ + η)`):
    simp only [Bool.false_eq_true, ↓reduceIte] at hm_dir hc_dir
    have ht₁_neg : t₁ < 0 := sub_neg.mpr (hm_dir hu₀ huη (by linarith))
    have him_lt : (c.j (ξ u₀)).im < (c.j (ξ (u₀ + η))).im := hc_dir hu₀ huη (by linarith)
    rcases hmo with hmono | hanti
    · exfalso; have := hmono ht₁I h0I ht₁_neg
      change (c.j (φ (ee (v₀ + t₁))).1).im < (c.j (φ (ee (v₀ + 0))).1).im at this
      rw [heq0, heq1] at this; linarith
    · exact iff_of_false (hnot_anti hanti) (by decide)
  · -- `true, false`: `m` increasing (`0 < t₁`), `im` decreasing (`im(u₀ + η) < im(u₀)`):
    simp only [Bool.false_eq_true, ↓reduceIte] at hm_dir hc_dir
    have ht₁_pos : 0 < t₁ := sub_pos.mpr (hm_dir hu₀ huη (by linarith))
    have him_lt : (c.j (ξ (u₀ + η))).im < (c.j (ξ u₀)).im := hc_dir hu₀ huη (by linarith)
    rcases hmo with hmono | hanti
    · exfalso; have := hmono h0I ht₁I ht₁_pos
      change (c.j (φ (ee (v₀ + 0))).1).im < (c.j (φ (ee (v₀ + t₁))).1).im at this
      rw [heq0, heq1] at this; linarith
    · exact iff_of_false (hnot_anti hanti) (by decide)
  · -- `true, true`: `m` increasing (`0 < t₁`), `im` increasing (`im(u₀) < im(u₀ + η)`):
    simp only [↓reduceIte] at hm_dir hc_dir
    have ht₁_pos : 0 < t₁ := sub_pos.mpr (hm_dir hu₀ huη (by linarith))
    have him_lt : (c.j (ξ u₀)).im < (c.j (ξ (u₀ + η))).im := hc_dir hu₀ huη (by linarith)
    rcases hmo with hmono | hanti
    · exact iff_of_true ⟨v₀, δ₁, hδ₁, hv₀, hδ₁U, hmono⟩ rfl
    · exfalso; have := hanti h0I ht₁I ht₁_pos
      change (c.j (φ (ee (v₀ + t₁))).1).im < (c.j (φ (ee (v₀ + 0))).1).im at this
      rw [heq0, heq1] at this; linarith

set_option maxHeartbeats 800000 in
/-- **Key Gluing Orientation Lemma**: for any cutting `ψ : Y → S` along a proper `I`-arc `F` with
lifts `ξ, η`, at the interior midpoint `u = 1/2`, the boundary-plus-cutting orientation invariant
`cuffSign AY φ (lift (1/2)) + cutOrientDiff AY AS ψ (lift (1/2)) + dirSign` takes OPPOSITE values
in `ZMod 2` on the two lifts `ξ` and `η`! -/
theorem cut_lift_opp_sign (hY : IsSurface Y) (hS : IsSurface S) [T2Space Y]
    {ψ : Y → S} {F : Set S} {s t : S} (hψ : IsCutting ψ F) (hF : IsClosed F)
    (_hb : F ∩ bd S = {s, t}) {X X' : Set Y} (hP : LiftPair ψ F s t X X')
    {a : ℝ → S} {ξ η : ℝ → Y} (L : ArcLift ψ F a ξ η)
    (_ha0 : a 0 = s) (_ha1 : a 1 = t) (himξ : ξ '' Icc 0 1 = X) (himη : η '' Icc 0 1 = X')
    (hiξ : InjOn ξ (Icc 0 1)) (hiη : InjOn η (Icc 0 1))
    (AY : SurfAtlas Y) (AS : SurfAtlas S)
    {C₁ C₂ : Set Y} (hC₁ : C₁ ⊆ bd Y) (hC₂ : C₂ ⊆ bd Y)
    (φ₁ : Circle ≃ₜ C₁) (φ₂ : Circle ≃ₜ C₂)
    {m₁ m₂ : ℝ → ℝ} (hm₁c : ContinuousOn m₁ (Icc 0 1)) (hm₂c : ContinuousOn m₂ (Icc 0 1))
    (hm₁ξ : ∀ u ∈ Icc (0 : ℝ) 1, (φ₁ (ee (m₁ u))).1 = ξ u)
    (hm₂η : ∀ u ∈ Icc (0 : ℝ) 1, (φ₂ (ee (m₂ u))).1 = η u)
    (σ₁ σ₂ : Bool)
    (hm₁_dir : if σ₁ then StrictMonoOn m₁ (Icc 0 1) else StrictAntiOn m₁ (Icc 0 1))
    (hm₂_dir : if σ₂ then StrictMonoOn m₂ (Icc 0 1) else StrictAntiOn m₂ (Icc 0 1)) :
    (cuffSign AY φ₁ (ξ (1 / 2)) + cutOrientDiff AY AS ψ (ξ (1 / 2)) + (if σ₁ then 0 else 1)) +
    (cuffSign AY φ₂ (η (1 / 2)) + cutOrientDiff AY AS ψ (η (1 / 2)) + (if σ₂ then 0 else 1)) = 1 := by
  classical
  have : CompactSpace Y := hY.1
  have : T2Space S := hS.2.1
  obtain ⟨x0, x1, y0, y1, l1, l2, hd, hun, hbijX, hbijX', -⟩ := id hP
  have hmidI : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hmidO : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
  -- Separate `X` and `X'` by disjoint open sets `V_X, V_X'`, and separate `ξ(1/2)` and `η(1/2)`:
  obtain ⟨V_X, V_X', hVX, hVX', hXV, hX'V', hclDisj⟩ :=
    exists_disjoint_closure_nhds l1.isCompact.isClosed l2.isCompact.isClosed hd
  have hVdisj : Disjoint V_X V_X' := hclDisj.mono subset_closure subset_closure
  -- Get half-plane charts `c₁'` at `ξ(1/2)` and `c₂'` at `η(1/2)` and shift vertically so `j(mid) = 0`:
  obtain ⟨c₁', hξc₁'⟩ := exists_surfChart (hY.2.2 (ξ (1 / 2)))
  obtain ⟨c₂', hηc₂'⟩ := exists_surfChart (hY.2.2 (η (1 / 2)))
  have hξbd : ξ (1 / 2) ∈ bd Y := hψ.2.2.2.2 (show ξ (1 / 2) ∈ ψ ⁻¹' F from hun ▸ Or.inl (himξ ▸ ⟨1 / 2, hmidI, rfl⟩))
  have hηbd : η (1 / 2) ∈ bd Y := hψ.2.2.2.2 (show η (1 / 2) ∈ ψ ⁻¹' F from hun ▸ Or.inr (himη ▸ ⟨1 / 2, hmidI, rfl⟩))
  have hre1 : (c₁'.j (ξ (1 / 2))).re = 0 := (c₁'.mem_bd_iff hξc₁').mp hξbd
  have hre2 : (c₂'.j (η (1 / 2))).re = 0 := (c₂'.mem_bd_iff hηc₂').mp hηbd
  let shiftChart : SurfChart Y → ℝ → SurfChart Y := fun c y0 =>
    { U := c.U
      O := (fun w : ℂ => w + (y0 : ℂ) * Complex.I) ⁻¹' c.O
      j := fun x => c.j x - (y0 : ℂ) * Complex.I
      k := fun w => c.k (w + (y0 : ℂ) * Complex.I)
      hU := c.hU
      hO := c.hO.preimage (continuous_id.add continuous_const)
      hj := c.hj.sub continuousOn_const
      hk := c.hk.comp (continuous_id.add continuous_const).continuousOn (fun w hw => ⟨hw.1, by simpa [halfPlane] using hw.2⟩)
      hm := fun _ hx => ⟨by simpa using (c.hm hx).1, by simpa [halfPlane] using (c.hm hx).2⟩
      hk' := fun _ hw => c.hk' ⟨hw.1, by simpa [halfPlane] using hw.2⟩
      hl := fun _ hx => by simpa using c.hl hx
      hr := fun _ hw => by dsimp only; rw [c.hr ⟨hw.1, by simpa [halfPlane] using hw.2⟩]; ring }
  let c₁ := shiftChart c₁' (c₁'.j (ξ (1 / 2))).im
  let c₂ := shiftChart c₂' (c₂'.j (η (1 / 2))).im
  have hξc₁ : ξ (1 / 2) ∈ c₁.U := hξc₁'
  have hηc₂ : η (1 / 2) ∈ c₂.U := hηc₂'
  have hc₁0 : c₁.j (ξ (1 / 2)) = 0 := Complex.ext
    (by change (c₁'.j (ξ (1 / 2)) - _).re = 0; simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero]; exact hre1)
    (by simp [c₁, shiftChart])
  have hc₂0 : c₂.j (η (1 / 2)) = 0 := Complex.ext
    (by change (c₂'.j (η (1 / 2)) - _).re = 0; simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero]; exact hre2)
    (by simp [c₂, shiftChart])
  -- Choose small boxes `(-r₁, r₁)² ⊆ c₁.O` and `(-r₂, r₂)² ⊆ c₂.O` mapping into `V_X` (avoiding `{ξ 0, ξ 1}`)
  -- and `V_X'` (avoiding `{η 0, η 1}`), so their boundary edges lie strictly inside `ξ '' Ioo 0 1` and `η '' Ioo 0 1`!
  have hbd_sub_X : ∀ (c : SurfChart Y) (V Z : Set Y) (z₀ : Y), z₀ ∈ c.U → c.j z₀ = 0 →
      IsOpen V → z₀ ∈ V → (∀ y ∈ V, y ∈ bd Y → y ∈ Z) →
      ∃ r > 0, r < 1 ∧ (Ioo (-r) r ×ℂ Ioo (-r) r ⊆ c.O) ∧
        ∀ w ∈ Ioo (-r) r ×ℂ Ioo (-r) r, w ∈ halfPlane → c.k w ∈ V := by
    intro c V _ z₀ hzU hj0 hVo hzV _
    have hnhd : c.k ⁻¹' V ∈ 𝓝[c.O ∩ halfPlane] 0 :=
      (c.hk 0 (hj0 ▸ c.hm hzU)).preimage_mem_nhdsWithin (hVo.mem_nhds (by rw [← hj0, c.hl hzU]; exact hzV))
    obtain ⟨ρ₁, hρ₁, hρ₁sub⟩ := Metric.mem_nhdsWithin_iff.mp hnhd
    obtain ⟨ρ₂, hρ₂, hρ₂sub⟩ := Metric.isOpen_iff.mp c.hO 0 (hj0 ▸ c.hm hzU).1
    set r := min (1 / 2) (min (ρ₁ / 3) (ρ₂ / 3))
    have hr : 0 < r := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
    have hbox : ∀ w ∈ Ioo (-r) r ×ℂ Ioo (-r) r, ‖w‖ < min ρ₁ ρ₂ := fun w hw => by
      have hre := (Complex.mem_reProdIm.mp hw).1
      have him := (Complex.mem_reProdIm.mp hw).2
      have h1 : ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
      have h2 : |w.re| < r := abs_lt.mpr hre
      have h3 : |w.im| < r := abs_lt.mpr him
      have hr1 : r ≤ ρ₁ / 3 := (min_le_right _ _).trans (min_le_left _ _)
      have hr2 : r ≤ ρ₂ / 3 := (min_le_right _ _).trans (min_le_right _ _)
      exact lt_min (by linarith) (by linarith)
    refine ⟨r, hr, lt_of_le_of_lt (min_le_left _ _) (by norm_num),
      fun w hw => hρ₂sub (by simpa [mem_ball, dist_eq_norm] using lt_of_lt_of_le (hbox w hw) (min_le_right _ _)),
      fun w hw hwh => hρ₁sub ⟨by simpa [mem_ball, dist_eq_norm] using lt_of_lt_of_le (hbox w hw) (min_le_left _ _),
        ⟨hρ₂sub (by simpa [mem_ball, dist_eq_norm] using lt_of_lt_of_le (hbox w hw) (min_le_right _ _)), hwh⟩⟩⟩
  -- Shrink `V_X` away from `ξ 0, ξ 1` and `bd Y \ X`, and similarly `V_X'`:
  -- Wait: `X = ξ '' [0, 1]` and `ξ '' (0, 1)` is OPEN in `bd Y` (since `ψ⁻¹(F \ {s, t})`? Even simpler:
  -- on `C₁`, `φ₁ ∘ ee ∘ m₁` covers `ξ([0,1])`, so `ξ(1/2)` has an open nbhd in `Y` whose intersection with `bd Y`
  -- is contained in `ξ '' (1/4, 3/4)`!).
  have hnbhd_lift : ∀ (C : Set Y) (φ : Circle ≃ₜ C) (m : ℝ → ℝ) (f : ℝ → Y) (V : Set Y),
      C ∈ cuffs Y → (∀ u ∈ Icc (0 : ℝ) 1, (φ (ee (m u))).1 = f u) →
      ContinuousOn m (Icc 0 1) → InjOn f (Icc 0 1) →
      IsOpen V → f (1 / 2) ∈ V →
      ∃ V₀ : Set Y, IsOpen V₀ ∧ f (1 / 2) ∈ V₀ ∧ V₀ ⊆ V ∧ ∀ y ∈ V₀, y ∈ bd Y → y ∈ f '' Ioo (0 : ℝ) 1 := by
    intro C φ m f V hC hm hmc hfi hVo hfV
    have hCcl : IsClosed (⋃₀ (cuffs Y \ {C})) :=
      ((cuff_statement.{u} Y hY).2.1.subset sdiff_subset).isClosed_sUnion fun D hD =>
        ((cuff_statement.{u} Y hY).2.2 D hD.1).isCompact.isClosed
    have hfC : f (1 / 2) ∈ C := (hm (1 / 2) hmidI) ▸ (φ _).2
    have hnot_other : f (1 / 2) ∉ ⋃₀ (cuffs Y \ {C}) := by
      rintro ⟨D, ⟨hD, hDne⟩, hmem⟩
      exact Set.disjoint_left.mp (cuffs_disjoint hC hD (fun h => hDne h.symm)) hfC hmem
    -- Inside `C`, `f '' (0, 1)` is open in `C` because `m` is strictly monotone on `[0, 1]`!
    have hKcl : IsClosed (C \ f '' Ioo (0 : ℝ) 1) := by
      -- `f '' [0, 1]` has complement in `C` equal to `φ '' (ee '' Ioo (m 1) (m 0 + 1))`, or directly:
      -- `f '' Ioo (0, 1)` is open in `C`, because `C \ f '' Ioo (0, 1)` is compact? Wait: check `f '' Ioo (0, 1)` open!
      -- Use `lift_mono`: `m '' Ioo 0 1 = Ioo (min (m 0) (m 1)) (max (m 0) (m 1))`!
      have hmo := lift_mono hmc (inj_of_lift hm hfi)
      have hopenC : IsOpen ((Subtype.val ⁻¹' (f '' Ioo (0 : ℝ) 1)) : Set C) := by
        rw [← φ.isOpen_preimage]
        rw [← isQuotientMap_ee.isOpen_preimage]
        have hpre : ee ⁻¹' (φ ⁻¹' (Subtype.val ⁻¹' (f '' Ioo (0 : ℝ) 1))) =
            ⋃ k : ℤ, (fun x : ℝ => x + k) ⁻¹' (m '' Ioo (0 : ℝ) 1) := by
          ext x; simp only [mem_preimage, mem_iUnion, mem_image]
          constructor
          · rintro ⟨u, hu, heq⟩
            have h1 : (φ (ee (m u))).1 = (φ (ee x)).1 := (hm u (Ioo_subset_Icc_self hu)).trans heq
            obtain ⟨k, hk⟩ := ee_eq_iff.mp (φ.injective (Subtype.ext h1))
            exact ⟨k, u, hu, hk⟩
          · rintro ⟨k, u, hu, hmu⟩
            refine ⟨u, hu, ?_⟩
            rw [← hm u (Ioo_subset_Icc_self hu)]
            exact congrArg (fun z => (φ z).1) (ee_eq_iff.mpr ⟨k, hmu⟩)
        rw [hpre]
        refine isOpen_iUnion fun k => ?_
        have him : IsOpen (m '' Ioo (0 : ℝ) 1) := by
          rcases hmo with hsm | hsa
          · have : m '' Ioo (0 : ℝ) 1 = Ioo (m 0) (m 1) := by
              ext y; constructor
              · rintro ⟨u, hu, rfl⟩; exact ⟨hsm (by simp) (Ioo_subset_Icc_self hu) hu.1, hsm (Ioo_subset_Icc_self hu) (by simp) hu.2⟩
              · intro hy
                obtain ⟨u, hu, rfl⟩ := intermediate_value_Ioo zero_le_one hmc hy
                exact ⟨u, hu, rfl⟩
            rw [this]; exact isOpen_Ioo
          · have : m '' Ioo (0 : ℝ) 1 = Ioo (m 1) (m 0) := by
              ext y; constructor
              · rintro ⟨u, hu, rfl⟩; exact ⟨hsa (Ioo_subset_Icc_self hu) (by simp) hu.2, hsa (by simp) (Ioo_subset_Icc_self hu) hu.1⟩
              · intro hy
                obtain ⟨u, hu, rfl⟩ := intermediate_value_Ioo' zero_le_one hmc hy
                exact ⟨u, hu, rfl⟩
            rw [this]; exact isOpen_Ioo
        exact him.preimage (continuous_id.add continuous_const)
      have hCclosed : IsClosed C := ((cuff_statement.{u} Y hY).2.2 C hC).isCompact.isClosed
      have h1 : IsClosed (Subtype.val '' (Subtype.val ⁻¹' (f '' Ioo (0 : ℝ) 1) : Set C)ᶜ : Set Y) :=
        hCclosed.isClosedEmbedding_subtypeVal.isClosedMap _ hopenC.isClosed_compl
      have h2 : Subtype.val '' (Subtype.val ⁻¹' (f '' Ioo (0 : ℝ) 1) : Set C)ᶜ = C \ f '' Ioo (0 : ℝ) 1 := by
        ext y; simp only [mem_image, mem_compl_iff, mem_preimage, mem_sdiff]
        constructor
        · rintro ⟨⟨z, hz⟩, hnot, rfl⟩; exact ⟨hz, hnot⟩
        · rintro ⟨hyC, hnot⟩; exact ⟨⟨y, hyC⟩, hnot, rfl⟩
      rwa [← h2]
    refine ⟨V ∩ (⋃₀ (cuffs Y \ {C}))ᶜ ∩ (C \ f '' Ioo (0 : ℝ) 1)ᶜ,
      (hVo.inter hCcl.isOpen_compl).inter hKcl.isOpen_compl,
      ⟨⟨hfV, hnot_other⟩, fun h => h.2 ⟨1 / 2, hmidO, rfl⟩⟩,
      fun y hy => hy.1.1, fun y hy hybd => ?_⟩
    have hycuff : y ∈ ⋃₀ cuffs Y := (sUnion_cuffs (S := Y)).symm ▸ hybd
    obtain ⟨D, hD, hyD⟩ := hycuff
    have hDC : D = C := by_contra fun hne => hy.1.2 ⟨D, ⟨hD, hne⟩, hyD⟩
    subst hDC
    by_contra hnot
    exact hy.2 ⟨hyD, hnot⟩
  have hC₁_cuff : C₁ ∈ cuffs Y := by
    have hξ0 : ξ (1 / 2) ∈ C₁ := (hm₁ξ (1 / 2) hmidI) ▸ (φ₁ _).2
    have hD : connectedComponentIn (bd Y) (ξ (1 / 2)) ∈ cuffs Y := ⟨_, hξbd, rfl⟩
    obtain ⟨φD⟩ := (cuff_statement.{u} Y hY).2.2 _ hD
    have hIm : (Subtype.val ∘ φ₁) '' univ = C₁ := by
      ext z; simp only [mem_image, mem_univ, true_and, comp_apply]
      exact ⟨fun ⟨w, hw⟩ => hw ▸ (φ₁ w).2, fun hz => ⟨φ₁.symm ⟨z, hz⟩, by simp⟩⟩
    have hsub : C₁ ⊆ connectedComponentIn (bd Y) (ξ (1 / 2)) :=
      (hIm ▸ isPreconnected_univ.image (Subtype.val ∘ φ₁) (continuous_subtype_val.comp φ₁.continuous).continuousOn).subset_connectedComponentIn hξ0 hC₁
    rwa [oarc_eq φD ⟨φ₁⟩ hsub]
  have hC₂_cuff : C₂ ∈ cuffs Y := by
    have hη0 : η (1 / 2) ∈ C₂ := (hm₂η (1 / 2) hmidI) ▸ (φ₂ _).2
    have hD : connectedComponentIn (bd Y) (η (1 / 2)) ∈ cuffs Y := ⟨_, hηbd, rfl⟩
    obtain ⟨φD⟩ := (cuff_statement.{u} Y hY).2.2 _ hD
    have hIm : (Subtype.val ∘ φ₂) '' univ = C₂ := by
      ext z; simp only [mem_image, mem_univ, true_and, comp_apply]
      exact ⟨fun ⟨w, hw⟩ => hw ▸ (φ₂ w).2, fun hz => ⟨φ₂.symm ⟨z, hz⟩, by simp⟩⟩
    have hsub : C₂ ⊆ connectedComponentIn (bd Y) (η (1 / 2)) :=
      (hIm ▸ isPreconnected_univ.image (Subtype.val ∘ φ₂) (continuous_subtype_val.comp φ₂.continuous).continuousOn).subset_connectedComponentIn hη0 hC₂
    rwa [oarc_eq φD ⟨φ₂⟩ hsub]
  obtain ⟨V₁, hV₁o, hξV₁, hV₁sub, hV₁bd⟩ := hnbhd_lift C₁ φ₁ m₁ ξ V_X hC₁_cuff hm₁ξ hm₁c hiξ hVX (hXV (himξ ▸ ⟨1 / 2, hmidI, rfl⟩))
  obtain ⟨V₂, hV₂o, hηV₂, hV₂sub, hV₂bd⟩ := hnbhd_lift C₂ φ₂ m₂ η V_X' hC₂_cuff hm₂η hm₂c hiη hVX' (hX'V' (himη ▸ ⟨1 / 2, hmidI, rfl⟩))
  obtain ⟨r₁, hr₁, hr₁lt, hr₁O, hr₁V⟩ := hbd_sub_X c₁ V₁ (ξ '' Ioo 0 1) (ξ (1 / 2)) hξc₁ hc₁0 hV₁o hξV₁ hV₁bd
  obtain ⟨r₂, hr₂, hr₂lt, hr₂O, hr₂V⟩ := hbd_sub_X c₂ V₂ (η '' Ioo 0 1) (η (1 / 2)) hηc₂ hc₂0 hV₂o hηV₂ hV₂bd
  -- Pick `δ > 0` small enough so `ξ '' [1/2 - δ, 1/2 + δ] ⊆ c₁.k '' (box r₁ ∩ {Re = 0})`
  -- AND `η '' [1/2 - δ, 1/2 + δ] ⊆ c₂.k '' (box r₂ ∩ {Re = 0})`!
  have hξ_nhd : ξ ⁻¹' (c₁.U ∩ c₁.j ⁻¹' (Ioo (-r₁) r₁ ×ℂ Ioo (-r₁) r₁)) ∈ 𝓝[Icc (0 : ℝ) 1] (1 / 2) := by
    have hO₁ : IsOpen (c₁.U ∩ c₁.j ⁻¹' (Ioo (-r₁) r₁ ×ℂ Ioo (-r₁) r₁)) :=
      c₁.hj.isOpen_inter_preimage c₁.hU ((isOpen_Ioo.preimage Complex.continuous_re).inter (isOpen_Ioo.preimage Complex.continuous_im))
    exact (L.cξ (1 / 2) hmidI).preimage_mem_nhdsWithin (hO₁.mem_nhds ⟨hξc₁, by
      show c₁.j (ξ (1 / 2)) ∈ Ioo (-r₁) r₁ ×ℂ Ioo (-r₁) r₁; rw [hc₁0]
      exact Complex.mem_reProdIm.mpr ⟨⟨by simp; linarith, by simp; exact hr₁⟩, ⟨by simp; linarith, by simp; exact hr₁⟩⟩⟩)
  have hη_nhd : η ⁻¹' (c₂.U ∩ c₂.j ⁻¹' (Ioo (-r₂) r₂ ×ℂ Ioo (-r₂) r₂)) ∈ 𝓝[Icc (0 : ℝ) 1] (1 / 2) := by
    have hO₂ : IsOpen (c₂.U ∩ c₂.j ⁻¹' (Ioo (-r₂) r₂ ×ℂ Ioo (-r₂) r₂)) :=
      c₂.hj.isOpen_inter_preimage c₂.hU ((isOpen_Ioo.preimage Complex.continuous_re).inter (isOpen_Ioo.preimage Complex.continuous_im))
    exact (L.cη (1 / 2) hmidI).preimage_mem_nhdsWithin (hO₂.mem_nhds ⟨hηc₂, by
      show c₂.j (η (1 / 2)) ∈ Ioo (-r₂) r₂ ×ℂ Ioo (-r₂) r₂; rw [hc₂0]
      exact Complex.mem_reProdIm.mpr ⟨⟨by simp; linarith, by simp; exact hr₂⟩, ⟨by simp; linarith, by simp; exact hr₂⟩⟩⟩)
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhdsWithin_iff.mp (Filter.inter_mem hξ_nhd hη_nhd)
  set δ := min (1 / 4) (ρ / 2)
  have hδ : 0 < δ := lt_min (by norm_num) (half_pos hρ)
  have hIδ : Icc (1 / 2 - δ) (1 / 2 + δ) ⊆ Icc (0 : ℝ) 1 := fun u hu =>
    ⟨by linarith [hu.1, min_le_left (1 / 4) (ρ / 2)], by linarith [hu.2, min_le_left (1 / 4) (ρ / 2)]⟩
  have hδ_in : ∀ u ∈ Icc (1 / 2 - δ) (1 / 2 + δ),
      (ξ u ∈ c₁.U ∧ c₁.j (ξ u) ∈ Ioo (-r₁) r₁ ×ℂ Ioo (-r₁) r₁) ∧
      (η u ∈ c₂.U ∧ c₂.j (η u) ∈ Ioo (-r₂) r₂ ×ℂ Ioo (-r₂) r₂) := fun u hu =>
    hρsub ⟨by
      rw [mem_ball, Real.dist_eq, abs_lt]
      have h1 : δ < ρ := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hρ)
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩, hIδ hu⟩
  -- Vertical coordinate functions `p₁ u = (c₁.j (ξ u)).im` and `p₂ u = (c₂.j (η u)).im` on `[1/2 - δ, 1/2 + δ]`!
  let p₁ : ℝ → ℝ := fun u => (c₁.j (ξ u)).im
  let p₂ : ℝ → ℝ := fun u => (c₂.j (η u)).im
  have hp₁c : ContinuousOn p₁ (Icc (1 / 2 - δ) (1 / 2 + δ)) :=
    Complex.continuous_im.comp_continuousOn (c₁.hj.comp (L.cξ.mono hIδ) fun u hu => (hδ_in u hu).1.1)
  have hp₂c : ContinuousOn p₂ (Icc (1 / 2 - δ) (1 / 2 + δ)) :=
    Complex.continuous_im.comp_continuousOn (c₂.hj.comp (L.cη.mono hIδ) fun u hu => (hδ_in u hu).2.1)
  have hp₁_re : ∀ u ∈ Icc (1 / 2 - δ) (1 / 2 + δ), (c₁.j (ξ u)).re = 0 := fun u hu =>
    (c₁.mem_bd_iff (hδ_in u hu).1.1).mp (hψ.2.2.2.2 (show ξ u ∈ ψ ⁻¹' F from hun ▸ Or.inl (himξ ▸ ⟨u, hIδ hu, rfl⟩)))
  have hp₂_re : ∀ u ∈ Icc (1 / 2 - δ) (1 / 2 + δ), (c₂.j (η u)).re = 0 := fun u hu =>
    (c₂.mem_bd_iff (hδ_in u hu).2.1).mp (hψ.2.2.2.2 (show η u ∈ ψ ⁻¹' F from hun ▸ Or.inr (himη ▸ ⟨u, hIδ hu, rfl⟩)))
  have hp₁_inj : InjOn p₁ (Icc (1 / 2 - δ) (1 / 2 + δ)) := fun u hu v hv he => by
    have hj : c₁.j (ξ u) = c₁.j (ξ v) := Complex.ext ((hp₁_re u hu).trans (hp₁_re v hv).symm) he
    have hξeq : ξ u = ξ v := by rw [← c₁.hl (hδ_in u hu).1.1, ← c₁.hl (hδ_in v hv).1.1, hj]
    exact hiξ (hIδ hu) (hIδ hv) hξeq
  have hp₂_inj : InjOn p₂ (Icc (1 / 2 - δ) (1 / 2 + δ)) := fun u hu v hv he => by
    have hj : c₂.j (η u) = c₂.j (η v) := Complex.ext ((hp₂_re u hu).trans (hp₂_re v hv).symm) he
    have hηeq : η u = η v := by rw [← c₂.hl (hδ_in u hu).2.1, ← c₂.hl (hδ_in v hv).2.1, hj]
    exact hiη (hIδ hu) (hIδ hv) hηeq
  have hp₁_mo := hp₁c.strictMonoOn_of_injOn_Icc' (by linarith) hp₁_inj
  have hp₂_mo := hp₂c.strictMonoOn_of_injOn_Icc' (by linarith) hp₂_inj
  have hp₁_ex : ∃ s₁ : Bool, if s₁ then StrictMonoOn p₁ (Icc (1 / 2 - δ) (1 / 2 + δ))
      else StrictAntiOn p₁ (Icc (1 / 2 - δ) (1 / 2 + δ)) :=
    hp₁_mo.elim (fun h => ⟨true, h⟩) (fun h => ⟨false, h⟩)
  have hp₂_ex : ∃ s₂ : Bool, if s₂ then StrictMonoOn p₂ (Icc (1 / 2 - δ) (1 / 2 + δ))
      else StrictAntiOn p₂ (Icc (1 / 2 - δ) (1 / 2 + δ)) :=
    hp₂_mo.elim (fun h => ⟨true, h⟩) (fun h => ⟨false, h⟩)
  obtain ⟨s₁, hs₁⟩ := hp₁_ex
  obtain ⟨s₂, hs₂⟩ := hp₂_ex
  have hp₁0 : p₁ (1 / 2) = 0 := by dsimp only [p₁]; rw [hc₁0]; rfl
  have hp₂0 : p₂ (1 / 2) = 0 := by dsimp only [p₂]; rw [hc₂0]; rfl
  -- Pick `ε > 0` so `[-ε, ε] ⊆ p₁ '' [1/2 - δ, 1/2 + δ]` and `ε < r₁`, `ε < r₂`:
  have hp₁_img_nhd : ∃ ε₁ > 0, Icc (-ε₁) ε₁ ⊆ p₁ '' Icc (1 / 2 - δ) (1 / 2 + δ) := by
    have hL : 1 / 2 - δ ∈ Icc (1 / 2 - δ) (1 / 2 + δ) := ⟨le_rfl, by linarith⟩
    have hM : (1 / 2 : ℝ) ∈ Icc (1 / 2 - δ) (1 / 2 + δ) := ⟨by linarith, by linarith⟩
    have hR : 1 / 2 + δ ∈ Icc (1 / 2 - δ) (1 / 2 + δ) := ⟨by linarith, le_rfl⟩
    rcases hp₁_mo with hsm | hsa
    · have hlt1 : p₁ (1 / 2 - δ) < 0 := hp₁0 ▸ hsm hL hM (by linarith)
      have hlt2 : 0 < p₁ (1 / 2 + δ) := hp₁0 ▸ hsm hM hR (by linarith)
      set ε₁ := min (-p₁ (1 / 2 - δ) / 2) (p₁ (1 / 2 + δ) / 2)
      refine ⟨ε₁, lt_min (by linarith) (by linarith), fun y hy => ?_⟩
      exact intermediate_value_Icc (by linarith) hp₁c
        ⟨by linarith [hy.1, min_le_left (-p₁ (1 / 2 - δ) / 2) (p₁ (1 / 2 + δ) / 2)],
         by linarith [hy.2, min_le_right (-p₁ (1 / 2 - δ) / 2) (p₁ (1 / 2 + δ) / 2)]⟩
    · have hlt1 : 0 < p₁ (1 / 2 - δ) := hp₁0 ▸ hsa hL hM (by linarith)
      have hlt2 : p₁ (1 / 2 + δ) < 0 := hp₁0 ▸ hsa hM hR (by linarith)
      set ε₁ := min (p₁ (1 / 2 - δ) / 2) (-p₁ (1 / 2 + δ) / 2)
      refine ⟨ε₁, lt_min (by linarith) (by linarith), fun y hy => ?_⟩
      exact intermediate_value_Icc' (by linarith) hp₁c
        ⟨by linarith [hy.1, min_le_right (p₁ (1 / 2 - δ) / 2) (-p₁ (1 / 2 + δ) / 2)],
         by linarith [hy.2, min_le_left (p₁ (1 / 2 - δ) / 2) (-p₁ (1 / 2 + δ) / 2)]⟩
  obtain ⟨ε₁, hε₁, hε₁sub⟩ := hp₁_img_nhd
  set ε := min ε₁ (min (r₁ / 2) (r₂ / 2))
  have hε : 0 < ε := lt_min hε₁ (lt_min (half_pos hr₁) (half_pos hr₂))
  have hε_r₁ : ε < r₁ := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (half_lt_self hr₁)
  have hε_r₂ : ε < r₂ := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (half_lt_self hr₂)
  have hε_1 : ε < 1 := lt_trans hε_r₁ hr₁lt
  -- Inverse `p₁_inv : [-ε, ε] → [1/2 - δ, 1/2 + δ]` of `p₁`, and `τ := p₂ ∘ p₁_inv : [-ε, ε] → (-r₂, r₂)`:
  have hex_u : ∀ y ∈ Icc (-ε) ε, ∃ u ∈ Icc (1 / 2 - δ) (1 / 2 + δ), p₁ u = y := fun y hy =>
    hε₁sub ⟨by linarith [hy.1, min_le_left ε₁ (min (r₁ / 2) (r₂ / 2))],
            by linarith [hy.2, min_le_left ε₁ (min (r₁ / 2) (r₂ / 2))]⟩
  choose! uOf huOf_mem hp₁_uOf using hex_u
  let τ : ℝ → ℝ := fun y => p₂ (uOf y)
  have huOf_0 : uOf 0 = 1 / 2 :=
    hp₁_inj (huOf_mem 0 ⟨by linarith, hε.le⟩) ⟨by linarith, by linarith⟩
      ((hp₁_uOf 0 ⟨by linarith, hε.le⟩).trans hp₁0.symm)
  have hτ0 : τ 0 = 0 := by dsimp only [τ]; rw [huOf_0, hp₂0]
  have huOf_mono : if s₁ then StrictMonoOn uOf (Icc (-ε) ε) else StrictAntiOn uOf (Icc (-ε) ε) := by
    cases s₁
    · simp only [Bool.false_eq_true, ↓reduceIte] at hs₁ ⊢
      intro y₁ hy₁ y₂ hy₂ hlt
      by_contra hge
      rcases eq_or_lt_of_le (not_lt.mp hge) with he | hgt
      · have := (hp₁_uOf y₁ hy₁).symm.trans ((congrArg p₁ he).trans (hp₁_uOf y₂ hy₂))
        linarith
      · have := hs₁ (huOf_mem y₁ hy₁) (huOf_mem y₂ hy₂) hgt
        rw [hp₁_uOf y₁ hy₁, hp₁_uOf y₂ hy₂] at this; linarith
    · simp only [↓reduceIte] at hs₁ ⊢
      intro y₁ hy₁ y₂ hy₂ hlt
      by_contra hge
      rcases eq_or_lt_of_le (not_lt.mp hge) with he | hgt
      · have := (hp₁_uOf y₁ hy₁).symm.trans ((congrArg p₁ he.symm).trans (hp₁_uOf y₂ hy₂))
        linarith
      · have := hs₁ (huOf_mem y₂ hy₂) (huOf_mem y₁ hy₁) hgt
        rw [hp₁_uOf y₁ hy₁, hp₁_uOf y₂ hy₂] at this; linarith
  have hτ_dir : if (s₁ == s₂) then StrictMonoOn τ (Icc (-ε) ε) else StrictAntiOn τ (Icc (-ε) ε) := by
    cases s₁ <;> cases s₂ <;> simp only [beq_iff_eq, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte] at hs₁ hs₂ huOf_mono ⊢
    · intro y₁ hy₁ y₂ hy₂ hlt; exact hs₂ (huOf_mem y₂ hy₂) (huOf_mem y₁ hy₁) (huOf_mono hy₁ hy₂ hlt)
    · intro y₁ hy₁ y₂ hy₂ hlt; exact hs₂ (huOf_mem y₂ hy₂) (huOf_mem y₁ hy₁) (huOf_mono hy₁ hy₂ hlt)
    · intro y₁ hy₁ y₂ hy₂ hlt; exact hs₂ (huOf_mem y₁ hy₁) (huOf_mem y₂ hy₂) (huOf_mono hy₁ hy₂ hlt)
    · intro y₁ hy₁ y₂ hy₂ hlt; exact hs₂ (huOf_mem y₁ hy₁) (huOf_mem y₂ hy₂) (huOf_mono hy₁ hy₂ hlt)
  -- Continuity of `uOf` on `[-ε, ε]` (compact-to-T2 inverse of `p₁`!):
  have huOf_cont : ContinuousOn uOf (Icc (-ε) ε) := by
    let f₁ : Icc (1 / 2 - δ) (1 / 2 + δ) → ℝ := fun u => p₁ u.1
    have hf₁c : Continuous f₁ := continuousOn_iff_continuous_domRestrict.mp hp₁c
    have hf₁i : Injective f₁ := fun u v he => Subtype.ext (hp₁_inj u.2 v.2 he)
    have hf₁ce : IsClosedEmbedding f₁ := hf₁c.isClosedEmbedding hf₁i
    let e := hf₁ce.isEmbedding.toHomeomorph
    have heq : ∀ (y : ℝ) (hy : y ∈ Icc (-ε) ε), uOf y = (e.symm ⟨y, ⟨⟨uOf y, huOf_mem y hy⟩, hp₁_uOf y hy⟩⟩).1 := fun y hy => by
      have h1 : e ⟨uOf y, huOf_mem y hy⟩ = ⟨y, ⟨⟨uOf y, huOf_mem y hy⟩, hp₁_uOf y hy⟩⟩ :=
        Subtype.ext (hp₁_uOf y hy)
      rw [← h1, e.symm_apply_apply]
    have hcont_sub : Continuous (fun y : Icc (-ε) ε => (e.symm ⟨y.1, ⟨⟨uOf y.1, huOf_mem y.1 y.2⟩, hp₁_uOf y.1 y.2⟩⟩).1) :=
      continuous_subtype_val.comp (e.symm.continuous.comp (Continuous.subtype_mk continuous_subtype_val _))
    rw [continuousOn_iff_continuous_domRestrict]
    exact hcont_sub.congr fun ⟨y, hy⟩ => (heq y hy).symm
  have hτ_cont : ContinuousOn τ (Icc (-ε) ε) := hp₂c.comp huOf_cont huOf_mem
  have hτ_r₂ : ∀ y ∈ Icc (-ε) ε, τ y ∈ Ioo (-r₂) r₂ := fun y hy =>
    (Complex.mem_reProdIm.mp (hδ_in (uOf y) (huOf_mem y hy)).2.2).2
  -- Image `τ '' Ioo (-ε) ε = Ioo a_τ b_τ` containing `0`:
  set a_τ := min (τ (-ε)) (τ ε)
  set b_τ := max (τ (-ε)) (τ ε)
  have hτ_open_img : τ '' Ioo (-ε) ε = Ioo a_τ b_τ := by
    ext z; constructor
    · rintro ⟨y, hy, rfl⟩
      have hyI := Ioo_subset_Icc_self hy
      have hL : -ε ∈ Icc (-ε) ε := ⟨le_rfl, by linarith⟩
      have hR : ε ∈ Icc (-ε) ε := ⟨by linarith, le_rfl⟩
      cases hsb : (s₁ == s₂)
      · rw [hsb] at hτ_dir; simp only [Bool.false_eq_true, ↓reduceIte] at hτ_dir
        have h1 : τ ε < τ y := hτ_dir hyI hR hy.2
        have h2 : τ y < τ (-ε) := hτ_dir hL hyI hy.1
        exact ⟨by simp [a_τ]; right; exact h1, by simp [b_τ]; left; exact h2⟩
      · rw [hsb] at hτ_dir; simp only [↓reduceIte] at hτ_dir
        have h1 : τ (-ε) < τ y := hτ_dir hL hyI hy.1
        have h2 : τ y < τ ε := hτ_dir hyI hR hy.2
        exact ⟨by simp [a_τ]; left; exact h1, by simp [b_τ]; right; exact h2⟩
    · intro hz
      cases hsb : (s₁ == s₂)
      · rw [hsb] at hτ_dir; simp only [Bool.false_eq_true, ↓reduceIte] at hτ_dir
        have hlt : τ ε < τ (-ε) := hτ_dir ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
        have ha : a_τ = τ ε := min_eq_right hlt.le
        have hb' : b_τ = τ (-ε) := max_eq_left hlt.le
        rw [ha, hb'] at hz
        obtain ⟨y, hy, rfl⟩ := intermediate_value_Ioo' (by linarith : -ε ≤ ε) hτ_cont hz
        exact ⟨y, hy, rfl⟩
      · rw [hsb] at hτ_dir; simp only [↓reduceIte] at hτ_dir
        have hlt : τ (-ε) < τ ε := hτ_dir ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
        have ha : a_τ = τ (-ε) := min_eq_left hlt.le
        have hb' : b_τ = τ ε := max_eq_right hlt.le
        rw [ha, hb'] at hz
        obtain ⟨y, hy, rfl⟩ := intermediate_value_Ioo (by linarith : -ε ≤ ε) hτ_cont hz
        exact ⟨y, hy, rfl⟩
  have h0_ab : (0 : ℝ) ∈ Ioo a_τ b_τ := hτ_open_img ▸ ⟨0, ⟨by linarith, hε⟩, hτ0⟩
  -- Inverse `τ_inv : Ioo a_τ b_τ → Ioo (-ε) ε` (actually on `Icc` for closed sub-interval):
  have hτ_inj : InjOn τ (Icc (-ε) ε) := by
    cases hsb : (s₁ == s₂) <;> rw [hsb] at hτ_dir <;> simp only [Bool.false_eq_true, ↓reduceIte] at hτ_dir
    · exact hτ_dir.injOn
    · exact hτ_dir.injOn
  -- Build the glued interior `SurfChart S` `cS` on `O_S := Ioo (2 - ε) (2 + ε) ×ℂ Ioo (-ε) ε`!
  let O_S : Set ℂ := Ioo (2 - ε) (2 + ε) ×ℂ Ioo (-ε) ε
  have hOS_open : IsOpen O_S :=
    (isOpen_Ioo.preimage Complex.continuous_re).inter (isOpen_Ioo.preimage Complex.continuous_im)
  have hOS_sub : O_S ⊆ halfPlane := fun w hw => by
    have := (Complex.mem_reProdIm.mp hw).1.1; show 0 ≤ w.re; linarith
  have hOS_inter : O_S ∩ halfPlane = O_S := inter_eq_left.mpr hOS_sub
  let g₁ : ℂ → ℂ := fun w => w - 2
  let g₂ : ℂ → ℂ := fun w => ((2 - w.re : ℝ) : ℂ) + (τ w.im : ℂ) * Complex.I
  let kS : ℂ → S := fun w => if 2 ≤ w.re then ψ (c₁.k (g₁ w)) else ψ (c₂.k (g₂ w))
  have hg₁_mem : ∀ w ∈ O_S, 2 ≤ w.re → g₁ w ∈ Ioo (-r₁) r₁ ×ℂ Ioo (-r₁) r₁ ∧ g₁ w ∈ halfPlane := fun w hw h2 => by
    have hre := (Complex.mem_reProdIm.mp hw).1
    have him := (Complex.mem_reProdIm.mp hw).2
    exact ⟨Complex.mem_reProdIm.mpr ⟨⟨by simp [g₁]; linarith [hre.1, hε_r₁], by simp [g₁]; linarith [hre.2, hε_r₁]⟩,
      ⟨by simp [g₁]; linarith [him.1, hε_r₁], by simp [g₁]; linarith [him.2, hε_r₁]⟩⟩, by simp [halfPlane, g₁]; linarith⟩
  have hg₂_mem : ∀ w ∈ O_S, w.re ≤ 2 → g₂ w ∈ Ioo (-r₂) r₂ ×ℂ Ioo (-r₂) r₂ ∧ g₂ w ∈ halfPlane := fun w hw h2 => by
    have hre := (Complex.mem_reProdIm.mp hw).1
    have him := (Complex.mem_reProdIm.mp hw).2
    have hτm := hτ_r₂ w.im (Ioo_subset_Icc_self him)
    exact ⟨Complex.mem_reProdIm.mpr ⟨⟨by simp [g₂]; linarith [hre.2, hε_r₂], by simp [g₂]; linarith [hre.1, hε_r₂]⟩,
      by simpa [g₂] using hτm⟩, by simp [halfPlane, g₂]; linarith⟩
  -- Agreement on the seam `w.re = 2`:
  have hseam : ∀ w ∈ O_S, w.re = 2 → ψ (c₁.k (g₁ w)) = ψ (c₂.k (g₂ w)) := fun w hw h2 => by
    have him := Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hw).2
    set u := uOf w.im
    have hu := huOf_mem w.im him
    have hg1_eq : g₁ w = c₁.j (ξ u) :=
      Complex.ext (by simp [g₁, h2, hp₁_re u hu])
        (by show (g₁ w).im = (c₁.j (ξ u)).im; simp only [g₁, Complex.sub_im, Complex.im_ofNat, sub_zero]
            exact (hp₁_uOf w.im him).symm)
    have hg2_eq : g₂ w = c₂.j (η u) :=
      Complex.ext (by simp [g₂, h2, hp₂_re u hu]) (by simp [g₂, τ, p₂, u])
    rw [hg1_eq, hg2_eq, c₁.hl (hδ_in u hu).1.1, c₂.hl (hδ_in u hu).2.1, L.hξ u (hIδ hu), L.hη u (hIδ hu)]
  -- Continuity of `kS` on `O_S`:
  have hg₁_cont : Continuous g₁ := continuous_id.sub continuous_const
  have hg₂_cont : ContinuousOn g₂ O_S := by
    refine ContinuousOn.add (Complex.continuous_ofReal.comp_continuousOn
      ((continuous_const.sub Complex.continuous_re).continuousOn)) ?_
    exact (Complex.continuous_ofReal.comp_continuousOn
      (hτ_cont.comp Complex.continuous_im.continuousOn
        (fun w hw => Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hw).2))).mul continuousOn_const
  have hkS_cont : ContinuousOn kS O_S := by
    have h1 : ContinuousOn (fun w => ψ (c₁.k (g₁ w))) (O_S ∩ {w : ℂ | 2 ≤ w.re}) :=
      hψ.1.comp_continuousOn (c₁.hk.comp hg₁_cont.continuousOn fun w hw =>
        ⟨hr₁O (hg₁_mem w hw.1 hw.2).1, (hg₁_mem w hw.1 hw.2).2⟩)
    have h2 : ContinuousOn (fun w => ψ (c₂.k (g₂ w))) (O_S ∩ {w : ℂ | w.re ≤ 2}) :=
      hψ.1.comp_continuousOn (c₂.hk.comp (hg₂_cont.mono inter_subset_left) fun w hw =>
        ⟨hr₂O (hg₂_mem w hw.1 hw.2).1, (hg₂_mem w hw.1 hw.2).2⟩)
    have hk_ge : ∀ z : ℂ, 2 ≤ z.re → kS z = ψ (c₁.k (g₁ z)) := fun z hz => ite_eq_left hz
    have hk_lt : ∀ z : ℂ, z.re < 2 → kS z = ψ (c₂.k (g₂ z)) := fun z hz => ite_eq_right (not_le.mpr hz)
    intro w hw
    by_cases hgt : 2 < w.re
    · have hnhd : O_S ∩ {z : ℂ | 2 < z.re} ∈ 𝓝[O_S] w :=
        inter_mem_nhdsWithin O_S ((isOpen_lt (continuous_const (y := (2 : ℝ))) Complex.continuous_re).mem_nhds hgt)
      have hev : kS =ᶠ[𝓝[O_S] w] fun z => ψ (c₁.k (g₁ z)) :=
        Filter.mem_of_superset hnhd fun z hz => hk_ge z (le_of_lt hz.2)
      have hc1 := (h1.mono (show O_S ∩ {z : ℂ | 2 < z.re} ⊆ O_S ∩ {z : ℂ | 2 ≤ z.re} from
        fun z hz => ⟨hz.1, show 2 ≤ z.re from le_of_lt hz.2⟩)) w ⟨hw, hgt⟩
      exact (hc1.mono_of_mem_nhdsWithin hnhd).congr_of_eventuallyEq hev (hk_ge w hgt.le)
    · by_cases hlt : w.re < 2
      · have hnhd : O_S ∩ {z : ℂ | z.re < 2} ∈ 𝓝[O_S] w :=
          inter_mem_nhdsWithin O_S ((isOpen_lt Complex.continuous_re (continuous_const (y := (2 : ℝ)))).mem_nhds hlt)
        have hev : kS =ᶠ[𝓝[O_S] w] fun z => ψ (c₂.k (g₂ z)) :=
          Filter.mem_of_superset hnhd fun z hz => hk_lt z hz.2
        have hc2 := (h2.mono (show O_S ∩ {z : ℂ | z.re < 2} ⊆ O_S ∩ {z : ℂ | z.re ≤ 2} from
          fun z hz => ⟨hz.1, show z.re ≤ 2 from le_of_lt hz.2⟩)) w ⟨hw, hlt⟩
        exact (hc2.mono_of_mem_nhdsWithin hnhd).congr_of_eventuallyEq hev (hk_lt w hlt)
      · have hweq : w.re = 2 := by linarith
        have hka : ContinuousWithinAt kS (O_S ∩ {z : ℂ | 2 ≤ z.re}) w :=
          (h1 w ⟨hw, hweq.ge⟩).congr (fun z hz => hk_ge z hz.2) (hk_ge w hweq.ge)
        have hkb : ContinuousWithinAt kS (O_S ∩ {z : ℂ | z.re ≤ 2}) w :=
          (h2 w ⟨hw, hweq.le⟩).congr (fun z hz => by
            by_cases hz2 : 2 ≤ z.re
            · rw [hk_ge z hz2]; exact hseam z hz.1 (le_antisymm hz.2 hz2)
            · exact hk_lt z (lt_of_not_ge hz2)) (by rw [hk_ge w hweq.ge]; exact hseam w hw hweq)
        have hun_O : O_S ∩ {z : ℂ | 2 ≤ z.re} ∪ O_S ∩ {z : ℂ | z.re ≤ 2} = O_S := by
          ext z; simp only [mem_union, mem_inter_iff, mem_ofPred_eq]
          exact ⟨fun h => h.elim And.left And.left, fun h => (le_total 2 z.re).imp (⟨h, ·⟩) (⟨h, ·⟩)⟩
        rw [← hun_O]; exact hka.union hkb
  -- Open sets in `Y` corresponding to the two halves of `O_S`:
  let Q₁ : Set Y := c₁.k '' ((Ioo (-ε) ε ×ℂ Ioo (-ε) ε) ∩ halfPlane)
  let Q₂ : Set Y := c₂.k '' ((Ioo (-ε) ε ×ℂ Ioo a_τ b_τ) ∩ halfPlane)
  have hQ₁_open : IsOpen Q₁ := by
    have hpre : Q₁ = c₁.U ∩ c₁.j ⁻¹' (Ioo (-ε) ε ×ℂ Ioo (-ε) ε) := by
      ext y; constructor
      · rintro ⟨z, ⟨hzR, hzh⟩, rfl⟩
        have hzO : z ∈ c₁.O ∩ halfPlane :=
          ⟨hr₁O (Complex.mem_reProdIm.mpr ⟨⟨by linarith [(Complex.mem_reProdIm.mp hzR).1.1],
            by linarith [(Complex.mem_reProdIm.mp hzR).1.2]⟩,
            ⟨by linarith [(Complex.mem_reProdIm.mp hzR).2.1], by linarith [(Complex.mem_reProdIm.mp hzR).2.2]⟩⟩), hzh⟩
        exact ⟨c₁.hk' hzO, by show c₁.j (c₁.k z) ∈ Ioo (-ε) ε ×ℂ Ioo (-ε) ε; rwa [c₁.hr hzO]⟩
      · rintro ⟨hyU, hyR⟩
        exact ⟨c₁.j y, ⟨hyR, (c₁.hm hyU).2⟩, c₁.hl hyU⟩
    rw [hpre]
    exact c₁.hj.isOpen_inter_preimage c₁.hU ((isOpen_Ioo.preimage Complex.continuous_re).inter (isOpen_Ioo.preimage Complex.continuous_im))
  have hQ₂_open : IsOpen Q₂ := by
    have hpre : Q₂ = c₂.U ∩ c₂.j ⁻¹' (Ioo (-ε) ε ×ℂ Ioo a_τ b_τ) := by
      ext y; constructor
      · rintro ⟨z, ⟨hzR, hzh⟩, rfl⟩
        have hab : z.im ∈ Ioo (-r₂) r₂ := by
          obtain ⟨t', ht', ht'eq⟩ := hτ_open_img.symm.subset (Complex.mem_reProdIm.mp hzR).2
          exact ht'eq ▸ hτ_r₂ t' (Ioo_subset_Icc_self ht')
        have hzO : z ∈ c₂.O ∩ halfPlane :=
          ⟨hr₂O (Complex.mem_reProdIm.mpr ⟨⟨by linarith [(Complex.mem_reProdIm.mp hzR).1.1],
            by linarith [(Complex.mem_reProdIm.mp hzR).1.2]⟩, hab⟩), hzh⟩
        exact ⟨c₂.hk' hzO, by show c₂.j (c₂.k z) ∈ Ioo (-ε) ε ×ℂ Ioo a_τ b_τ; rwa [c₂.hr hzO]⟩
      · rintro ⟨hyU, hyR⟩
        exact ⟨c₂.j y, ⟨hyR, (c₂.hm hyU).2⟩, c₂.hl hyU⟩
    rw [hpre]
    exact c₂.hj.isOpen_inter_preimage c₂.hU ((isOpen_Ioo.preimage Complex.continuous_re).inter (isOpen_Ioo.preimage Complex.continuous_im))
  have hQ₁_subV : Q₁ ⊆ V₁ := by
    rintro _ ⟨z, ⟨hzR, hzh⟩, rfl⟩
    exact hr₁V z (Complex.mem_reProdIm.mpr ⟨⟨by linarith [(Complex.mem_reProdIm.mp hzR).1.1],
      by linarith [(Complex.mem_reProdIm.mp hzR).1.2]⟩,
      ⟨by linarith [(Complex.mem_reProdIm.mp hzR).2.1], by linarith [(Complex.mem_reProdIm.mp hzR).2.2]⟩⟩) hzh
  have hQ₂_subV : Q₂ ⊆ V₂ := by
    rintro _ ⟨z, ⟨hzR, hzh⟩, rfl⟩
    obtain ⟨t', ht', ht'eq⟩ := hτ_open_img.symm.subset (Complex.mem_reProdIm.mp hzR).2
    exact hr₂V z (Complex.mem_reProdIm.mpr ⟨⟨by linarith [(Complex.mem_reProdIm.mp hzR).1.1],
      by linarith [(Complex.mem_reProdIm.mp hzR).1.2]⟩, ht'eq ▸ hτ_r₂ t' (Ioo_subset_Icc_self ht')⟩) hzh
  have hQ₁₂_disj : Disjoint Q₁ Q₂ := hVdisj.mono (hQ₁_subV.trans hV₁sub) (hQ₂_subV.trans hV₂sub)
  -- `U_S := kS '' O_S` has saturated preimage `Q₁ ∪ Q₂` under `ψ`, hence `U_S` is open in `S`!
  let U_S : Set S := kS '' O_S
  have hUS_pre : ψ ⁻¹' U_S = Q₁ ∪ Q₂ := by
    ext y; simp only [mem_preimage, mem_union]
    constructor
    · rintro ⟨w, hwO, hkw⟩
      have hre := (Complex.mem_reProdIm.mp hwO).1
      have him := (Complex.mem_reProdIm.mp hwO).2
      by_cases hgt : 2 < w.re
      · have hkw' : ψ (c₁.k (g₁ w)) = ψ y := by rwa [show kS w = ψ (c₁.k (g₁ w)) from ite_eq_left hgt.le] at hkw
        have hnotF : ψ (c₁.k (g₁ w)) ∉ F := fun hFmem => by
          have hbd := hψ.2.2.2.2 hFmem
          have hre0 := (c₁.mem_bd_iff (c₁.hk' ⟨hr₁O (hg₁_mem w hwO hgt.le).1, (hg₁_mem w hwO hgt.le).2⟩)).mp hbd
          rw [c₁.hr ⟨hr₁O (hg₁_mem w hwO hgt.le).1, (hg₁_mem w hwO hgt.le).2⟩] at hre0
          simp [g₁] at hre0; linarith
        have hy_eq : y = c₁.k (g₁ w) := hψ.2.2.1 (show ψ y ∉ F by rw [← hkw']; exact hnotF) hnotF hkw'.symm
        left; rw [hy_eq]
        exact ⟨g₁ w, ⟨Complex.mem_reProdIm.mpr ⟨⟨by simp [g₁]; linarith [hre.1], by simp [g₁]; linarith [hre.2]⟩, by simpa [g₁] using him⟩,
          by simp [halfPlane, g₁]; linarith⟩, rfl⟩
      · by_cases hlt : w.re < 2
        · have hkw' : ψ (c₂.k (g₂ w)) = ψ y := by rwa [show kS w = ψ (c₂.k (g₂ w)) from ite_eq_right (not_le.mpr hlt)] at hkw
          have hnotF : ψ (c₂.k (g₂ w)) ∉ F := fun hFmem => by
            have hbd := hψ.2.2.2.2 hFmem
            have hre0 := (c₂.mem_bd_iff (c₂.hk' ⟨hr₂O (hg₂_mem w hwO hlt.le).1, (hg₂_mem w hwO hlt.le).2⟩)).mp hbd
            rw [c₂.hr ⟨hr₂O (hg₂_mem w hwO hlt.le).1, (hg₂_mem w hwO hlt.le).2⟩] at hre0
            simp [g₂] at hre0; linarith
          have hy_eq : y = c₂.k (g₂ w) := hψ.2.2.1 (show ψ y ∉ F by rw [← hkw']; exact hnotF) hnotF hkw'.symm
          right; rw [hy_eq]
          exact ⟨g₂ w, ⟨Complex.mem_reProdIm.mpr ⟨⟨by simp [g₂]; linarith [hre.2], by simp [g₂]; linarith [hre.1]⟩,
            by simpa [g₂] using (hτ_open_img ▸ ⟨w.im, him, rfl⟩ : τ w.im ∈ Ioo a_τ b_τ)⟩,
            by simp [halfPlane, g₂]; linarith⟩, rfl⟩
        · have hweq : w.re = 2 := by linarith
          have hkw' : ψ (c₁.k (g₁ w)) = ψ y := by rwa [show kS w = ψ (c₁.k (g₁ w)) from ite_eq_left hweq.ge] at hkw
          set u := uOf w.im
          have hu := huOf_mem w.im (Ioo_subset_Icc_self him)
          have h1eq : c₁.k (g₁ w) = ξ u := by
            have hg1 : g₁ w = c₁.j (ξ u) := Complex.ext (by simp [g₁, hweq, hp₁_re u hu])
              (by show (g₁ w).im = (c₁.j (ξ u)).im; simp only [g₁, Complex.sub_im, Complex.im_ofNat, sub_zero]
                  exact (hp₁_uOf w.im (Ioo_subset_Icc_self him)).symm)
            rw [hg1, c₁.hl (hδ_in u hu).1.1]
          have h2eq : c₂.k (g₂ w) = η u := by
            have hg2 : g₂ w = c₂.j (η u) := Complex.ext (by simp [g₂, hweq, hp₂_re u hu]) (by simp [g₂, τ, p₂, u])
            rw [hg2, c₂.hl (hδ_in u hu).2.1]
          have hy_pair : y = ξ u ∨ y = η u := by
            rw [h1eq] at hkw'
            by_cases h1 : y = ξ u
            · exact .inl h1
            · obtain ⟨v, hv, hpair⟩ := L.fib y (ξ u) hkw'.symm h1
              rcases hpair with ⟨rfl, hξeq⟩ | ⟨-, rfl⟩
              · have hξuX : ξ u ∈ X := himξ ▸ ⟨u, hIδ hu, rfl⟩
                have hξuX' : ξ u ∈ X' := himη ▸ ⟨v, hv, hξeq.symm⟩
                exact absurd hξuX' (Set.disjoint_left.mp hd hξuX)
              · exact .inr (hbijX'.injOn (himη ▸ ⟨v, hv, rfl⟩) (himη ▸ ⟨u, hIδ hu, rfl⟩)
                  (hkw'.symm.trans ((L.hξ u (hIδ hu)).trans (L.hη u (hIδ hu)).symm)))
          rcases hy_pair with rfl | rfl
          · left; rw [← h1eq]
            exact ⟨g₁ w, ⟨Complex.mem_reProdIm.mpr ⟨⟨by simp [g₁, hweq]; linarith, by simp [g₁, hweq]; linarith⟩, by simpa [g₁] using him⟩,
              by simp [halfPlane, g₁, hweq]⟩, rfl⟩
          · right; rw [← h2eq]
            exact ⟨g₂ w, ⟨Complex.mem_reProdIm.mpr ⟨⟨by simp [g₂, hweq]; linarith, by simp [g₂, hweq]; linarith⟩,
              by simpa [g₂] using (hτ_open_img ▸ ⟨w.im, him, rfl⟩ : τ w.im ∈ Ioo a_τ b_τ)⟩,
              by simp [halfPlane, g₂, hweq]⟩, rfl⟩
    · rintro (⟨z, ⟨hzR, hzh⟩, rfl⟩ | ⟨z, ⟨hzR, hzh⟩, rfl⟩)
      · have hre := (Complex.mem_reProdIm.mp hzR).1
        have him := (Complex.mem_reProdIm.mp hzR).2
        have hwO : z + 2 ∈ O_S := Complex.mem_reProdIm.mpr ⟨⟨by simp; linarith [show 0 ≤ z.re from hzh], by simp; linarith [hre.2]⟩, by simpa using him⟩
        refine ⟨z + 2, hwO, ?_⟩
        rw [show kS (z + 2) = ψ (c₁.k (g₁ (z + 2))) from ite_eq_left (by simp; exact hzh)]
        simp [g₁]
      · have hre := (Complex.mem_reProdIm.mp hzR).1
        have him := (Complex.mem_reProdIm.mp hzR).2
        obtain ⟨y', hy', hτy'⟩ := hτ_open_img.symm.subset him
        set w : ℂ := ((2 - z.re : ℝ) : ℂ) + (y' : ℂ) * Complex.I
        have hwO : w ∈ O_S := Complex.mem_reProdIm.mpr
          ⟨⟨by simp [w]; linarith [hre.2], by simp [w]; linarith [show 0 ≤ z.re from hzh]⟩, by simpa [w] using hy'⟩
        have hg2w : g₂ w = z := Complex.ext (by simp [g₂, w]) (by simp [g₂, w, hτy'])
        refine ⟨w, hwO, ?_⟩
        by_cases h0 : z.re = 0
        · have hw2 : w.re = 2 := by simp [w, h0]
          rw [show kS w = ψ (c₁.k (g₁ w)) from ite_eq_left hw2.ge, hseam w hwO hw2, hg2w]
        · have hwlt : w.re < 2 := by simp [w]; exact lt_of_le_of_ne hzh (Ne.symm h0)
          rw [show kS w = ψ (c₂.k (g₂ w)) from ite_eq_right (not_le.mpr hwlt), hg2w]
  have hq : IsQuotientMap ψ := hψ.1.isClosedMap.isQuotientMap hψ.1 hψ.2.1
  have hUS_open : IsOpen U_S := by rw [← hq.isOpen_preimage, hUS_pre]; exact hQ₁_open.union hQ₂_open
  -- Inverse `τ_inv` on `Ioo a_τ b_τ`:
  have hex_τ : ∀ y ∈ Ioo a_τ b_τ, ∃ t' ∈ Ioo (-ε) ε, τ t' = y := fun y hy => hτ_open_img.symm.subset hy
  choose! τ_inv hτ_inv_mem hτ_inv_eq using hex_τ
  have hτ_inv_left : ∀ t' ∈ Ioo (-ε) ε, τ_inv (τ t') = t' := fun t' ht' =>
    hτ_inj (Ioo_subset_Icc_self (hτ_inv_mem (τ t') (hτ_open_img ▸ ⟨t', ht', rfl⟩))) (Ioo_subset_Icc_self ht')
      (hτ_inv_eq (τ t') (hτ_open_img ▸ ⟨t', ht', rfl⟩))
  have hτ_inv_cont : ContinuousOn τ_inv (Ioo a_τ b_τ) := by
    let f₂ : Icc (-ε) ε → ℝ := fun x => τ x.1
    have hf₂c : Continuous f₂ := continuousOn_iff_continuous_domRestrict.mp hτ_cont
    have hf₂i : Injective f₂ := fun x y he => Subtype.ext (hτ_inj x.2 y.2 he)
    let e := (hf₂c.isClosedEmbedding hf₂i).isEmbedding.toHomeomorph
    have heq : ∀ (y : ℝ) (hy : y ∈ Ioo a_τ b_τ), τ_inv y = (e.symm ⟨y, ⟨⟨τ_inv y, Ioo_subset_Icc_self (hτ_inv_mem y hy)⟩, hτ_inv_eq y hy⟩⟩).1 := fun y hy => by
      have h1 : e ⟨τ_inv y, Ioo_subset_Icc_self (hτ_inv_mem y hy)⟩ =
          ⟨y, ⟨⟨τ_inv y, Ioo_subset_Icc_self (hτ_inv_mem y hy)⟩, hτ_inv_eq y hy⟩⟩ := Subtype.ext (hτ_inv_eq y hy)
      rw [← h1, e.symm_apply_apply]
    have hcont_sub : Continuous (fun y : Ioo a_τ b_τ =>
        (e.symm ⟨y.1, ⟨⟨τ_inv y.1, Ioo_subset_Icc_self (hτ_inv_mem y.1 y.2)⟩, hτ_inv_eq y.1 y.2⟩⟩).1) :=
      continuous_subtype_val.comp (e.symm.continuous.comp (Continuous.subtype_mk continuous_subtype_val _))
    rw [continuousOn_iff_continuous_domRestrict]
    exact hcont_sub.congr fun ⟨y, hy⟩ => (heq y hy).symm
  -- Injectivity of `kS` on `O_S` and continuous inverse `jS` on `U_S` via `jpre`:
  let jpre : Y → ℂ := fun y =>
    if y ∈ Q₁ then c₁.j y + 2 else ((2 - (c₂.j y).re : ℝ) : ℂ) + (τ_inv (c₂.j y).im : ℂ) * Complex.I
  have hjpre_eq : ∀ w ∈ O_S, ∀ y ∈ Q₁ ∪ Q₂, ψ y = kS w → jpre y = w := by
    intro w hwO y hyQ hψy
    have hre := (Complex.mem_reProdIm.mp hwO).1
    have him := (Complex.mem_reProdIm.mp hwO).2
    have h1_calc : ∀ y₁ ∈ Q₁, jpre y₁ = c₁.j y₁ + 2 := fun y₁ hy₁ => ite_eq_left hy₁
    have h2_calc : ∀ y₂ ∈ Q₂, jpre y₂ = ((2 - (c₂.j y₂).re : ℝ) : ℂ) + (τ_inv (c₂.j y₂).im : ℂ) * Complex.I :=
      fun y₂ hy₂ => ite_eq_right fun h => Set.disjoint_left.mp hQ₁₂_disj h hy₂
    by_cases hgt : 2 < w.re
    · have hk : kS w = ψ (c₁.k (g₁ w)) := ite_eq_left hgt.le
      rw [hk] at hψy
      have hnotF : ψ (c₁.k (g₁ w)) ∉ F := fun hFmem => by
        have hre0 := (c₁.mem_bd_iff (c₁.hk' ⟨hr₁O (hg₁_mem w hwO hgt.le).1, (hg₁_mem w hwO hgt.le).2⟩)).mp (hψ.2.2.2.2 hFmem)
        rw [c₁.hr ⟨hr₁O (hg₁_mem w hwO hgt.le).1, (hg₁_mem w hwO hgt.le).2⟩] at hre0; simp [g₁] at hre0; linarith
      have hy_eq : y = c₁.k (g₁ w) := hψ.2.2.1 (show ψ y ∉ F by rw [hψy]; exact hnotF) hnotF hψy
      have hyQ₁ : y ∈ Q₁ := hy_eq ▸ ⟨g₁ w, ⟨Complex.mem_reProdIm.mpr ⟨⟨by simp [g₁]; linarith [hre.1], by simp [g₁]; linarith [hre.2]⟩, by simpa [g₁] using him⟩,
        by simp [halfPlane, g₁]; linarith⟩, rfl⟩
      rw [h1_calc y hyQ₁, hy_eq, c₁.hr ⟨hr₁O (hg₁_mem w hwO hgt.le).1, (hg₁_mem w hwO hgt.le).2⟩]; simp [g₁]
    · by_cases hlt : w.re < 2
      · have hk : kS w = ψ (c₂.k (g₂ w)) := ite_eq_right (not_le.mpr hlt)
        rw [hk] at hψy
        have hnotF : ψ (c₂.k (g₂ w)) ∉ F := fun hFmem => by
          have hre0 := (c₂.mem_bd_iff (c₂.hk' ⟨hr₂O (hg₂_mem w hwO hlt.le).1, (hg₂_mem w hwO hlt.le).2⟩)).mp (hψ.2.2.2.2 hFmem)
          rw [c₂.hr ⟨hr₂O (hg₂_mem w hwO hlt.le).1, (hg₂_mem w hwO hlt.le).2⟩] at hre0; simp [g₂] at hre0; linarith
        have hy_eq : y = c₂.k (g₂ w) := hψ.2.2.1 (show ψ y ∉ F by rw [hψy]; exact hnotF) hnotF hψy
        have hyQ₂ : y ∈ Q₂ := hy_eq ▸ ⟨g₂ w, ⟨Complex.mem_reProdIm.mpr ⟨⟨by simp [g₂]; linarith [hre.2], by simp [g₂]; linarith [hre.1]⟩,
          by simpa [g₂] using (hτ_open_img ▸ ⟨w.im, him, rfl⟩ : τ w.im ∈ Ioo a_τ b_τ)⟩, by simp [halfPlane, g₂]; linarith⟩, rfl⟩
        rw [h2_calc y hyQ₂, hy_eq, c₂.hr ⟨hr₂O (hg₂_mem w hwO hlt.le).1, (hg₂_mem w hwO hlt.le).2⟩]
        apply Complex.ext
        · simp [g₂]
        · simp [g₂, hτ_inv_left w.im him]
      · have hweq : w.re = 2 := by linarith
        have hk : kS w = ψ (c₁.k (g₁ w)) := ite_eq_left hweq.ge
        rw [hk] at hψy
        set u := uOf w.im
        have hu := huOf_mem w.im (Ioo_subset_Icc_self him)
        have h1eq : c₁.k (g₁ w) = ξ u := by
          have hg1 : g₁ w = c₁.j (ξ u) := Complex.ext (by simp [g₁, hweq, hp₁_re u hu])
            (by show (g₁ w).im = (c₁.j (ξ u)).im; simp only [g₁, Complex.sub_im, Complex.im_ofNat, sub_zero]
                exact (hp₁_uOf w.im (Ioo_subset_Icc_self him)).symm)
          rw [hg1, c₁.hl (hδ_in u hu).1.1]
        have h2eq : c₂.k (g₂ w) = η u := by
          have hg2 : g₂ w = c₂.j (η u) := Complex.ext (by simp [g₂, hweq, hp₂_re u hu]) (by simp [g₂, τ, p₂, u])
          rw [hg2, c₂.hl (hδ_in u hu).2.1]
        rcases hyQ with hy1 | hy2
        · have hyX : y ∈ X := by
            have hyF : ψ y ∈ F := by
              rw [hψy, h1eq]; exact show ξ u ∈ ψ ⁻¹' F from hun ▸ Or.inl (himξ ▸ ⟨u, hIδ hu, rfl⟩)
            have : y ∈ X ∪ X' := hun.symm ▸ hyF
            exact this.resolve_right fun hyX' => Set.disjoint_left.mp hVdisj (hV₁sub (hQ₁_subV hy1)) (hX'V' hyX')
          have hy_eq : y = ξ u := hbijX.injOn hyX (himξ ▸ ⟨u, hIδ hu, rfl⟩) (hψy.trans (congrArg ψ h1eq))
          rw [h1_calc y hy1, hy_eq, ← h1eq, c₁.hr ⟨hr₁O (hg₁_mem w hwO hweq.ge).1, (hg₁_mem w hwO hweq.ge).2⟩]; simp [g₁]
        · have hyX' : y ∈ X' := by
            have hyF : ψ y ∈ F := by
              rw [hψy, h1eq]; exact show ξ u ∈ ψ ⁻¹' F from hun ▸ Or.inl (himξ ▸ ⟨u, hIδ hu, rfl⟩)
            have : y ∈ X ∪ X' := hun.symm ▸ hyF
            exact this.resolve_left fun hyX => Set.disjoint_left.mp hVdisj (hXV hyX) (hV₂sub (hQ₂_subV hy2))
          have hy_eq : y = η u := hbijX'.injOn hyX' (himη ▸ ⟨u, hIδ hu, rfl⟩)
            (hψy.trans ((congrArg ψ h1eq).trans ((L.hξ u (hIδ hu)).trans (L.hη u (hIδ hu)).symm)))
          rw [h2_calc y hy2, hy_eq, ← h2eq, c₂.hr ⟨hr₂O (hg₂_mem w hwO hweq.le).1, (hg₂_mem w hwO hweq.le).2⟩]
          apply Complex.ext
          · simp [g₂, hweq]
          · simp [g₂, hτ_inv_left w.im him]
  let jS : S → ℂ := fun x => if hx : x ∈ U_S then hx.choose else 0
  have hjS_kS : ∀ w ∈ O_S, jS (kS w) = w := fun w hw => by
    have hx : kS w ∈ U_S := ⟨w, hw, rfl⟩
    simp only [jS, dite_eq_left hx]
    set w' := hx.choose
    obtain ⟨hw', hkw'⟩ := hx.choose_spec
    obtain ⟨y, hy⟩ := hψ.2.1 (kS w')
    have hyQ : y ∈ Q₁ ∪ Q₂ := hUS_pre ▸ (show ψ y ∈ U_S by rw [hy]; exact ⟨w', hw', rfl⟩)
    exact (hjpre_eq w' hw' y hyQ hy).symm.trans (hjpre_eq w hw y hyQ (hy.trans hkw'))
  have hjS_ψ : ∀ y ∈ Q₁ ∪ Q₂, jS (ψ y) = jpre y := fun y hy => by
    have hU : ψ y ∈ U_S := show y ∈ ψ ⁻¹' U_S from hUS_pre.symm ▸ hy
    obtain ⟨w, hw, hkw⟩ := hU
    rw [← hkw, hjS_kS w hw, hjpre_eq w hw y hy hkw.symm]
  have hjS_cont : ContinuousOn jS U_S := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine (hq.restrictPreimage_isOpen hUS_open).continuous_iff.mpr ?_
    have hfun : (U_S.domRestrict jS) ∘ (U_S.restrictPreimage ψ) = fun y => jpre y.1 := by
      funext ⟨y, hy⟩; exact hjS_ψ y (hUS_pre ▸ hy)
    rw [hfun, continuous_iff_continuousAt]
    rintro ⟨y, hy⟩
    rcases (hUS_pre ▸ hy : y ∈ Q₁ ∪ Q₂) with hy1 | hy2
    · have hnhd : (Subtype.val ⁻¹' Q₁ : Set (ψ ⁻¹' U_S)) ∈ 𝓝 (⟨y, hy⟩ : ψ ⁻¹' U_S) :=
        (hQ₁_open.preimage continuous_subtype_val).mem_nhds hy1
      have hev : (fun x : ψ ⁻¹' U_S => jpre x.1) =ᶠ[𝓝 ⟨y, hy⟩] fun x => c₁.j x.1 + 2 :=
        Filter.mem_of_superset hnhd fun x hx => ite_eq_left hx
      refine ContinuousAt.congr ?_ hev.symm
      have hyU : y ∈ c₁.U := by
        obtain ⟨z, ⟨hzR, hzh⟩, rfl⟩ := hy1
        exact c₁.hk' ⟨hr₁O (Complex.mem_reProdIm.mpr ⟨⟨by linarith [(Complex.mem_reProdIm.mp hzR).1.1],
          by linarith [(Complex.mem_reProdIm.mp hzR).1.2]⟩,
          ⟨by linarith [(Complex.mem_reProdIm.mp hzR).2.1], by linarith [(Complex.mem_reProdIm.mp hzR).2.2]⟩⟩), hzh⟩
      exact ContinuousAt.comp (g := fun w : Y => c₁.j w + 2)
        ((c₁.hj.continuousAt (c₁.hU.mem_nhds hyU)).add continuousAt_const)
        continuous_subtype_val.continuousAt
    · have hnhd : (Subtype.val ⁻¹' Q₂ : Set (ψ ⁻¹' U_S)) ∈ 𝓝 (⟨y, hy⟩ : ψ ⁻¹' U_S) :=
        (hQ₂_open.preimage continuous_subtype_val).mem_nhds hy2
      have hev : (fun x : ψ ⁻¹' U_S => jpre x.1) =ᶠ[𝓝 ⟨y, hy⟩]
          fun x => ((2 - (c₂.j x.1).re : ℝ) : ℂ) + (τ_inv (c₂.j x.1).im : ℂ) * Complex.I :=
        Filter.mem_of_superset hnhd fun x hx => ite_eq_right fun h => Set.disjoint_left.mp hQ₁₂_disj h hx
      refine ContinuousAt.congr ?_ hev.symm
      obtain ⟨z, ⟨hzR, hzh⟩, rfl⟩ := hy2
      have hab : z.im ∈ Ioo a_τ b_τ := (Complex.mem_reProdIm.mp hzR).2
      obtain ⟨t', ht', ht'eq⟩ := hτ_open_img.symm.subset hab
      have hzO : z ∈ c₂.O ∩ halfPlane :=
        ⟨hr₂O (Complex.mem_reProdIm.mpr ⟨⟨by linarith [(Complex.mem_reProdIm.mp hzR).1.1],
          by linarith [(Complex.mem_reProdIm.mp hzR).1.2]⟩, ht'eq ▸ hτ_r₂ t' (Ioo_subset_Icc_self ht')⟩), hzh⟩
      have hc₂_at : ContinuousAt c₂.j (c₂.k z) := c₂.hj.continuousAt (c₂.hU.mem_nhds (c₂.hk' hzO))
      have him_at : ContinuousAt (fun w : Y => (c₂.j w).im) (c₂.k z) :=
        Complex.continuous_im.continuousAt.comp hc₂_at
      have hτinv_at : ContinuousAt τ_inv (c₂.j (c₂.k z)).im := by
        rw [c₂.hr hzO]; exact hτ_inv_cont.continuousAt (isOpen_Ioo.mem_nhds hab)
      have hre_at : ContinuousAt (fun w : Y => ((2 - (c₂.j w).re : ℝ) : ℂ)) (c₂.k z) :=
        Complex.continuous_ofReal.continuousAt.comp (continuousAt_const.sub (Complex.continuous_re.continuousAt.comp hc₂_at))
      have him2_at : ContinuousAt (fun w : Y => (τ_inv (c₂.j w).im : ℂ) * Complex.I) (c₂.k z) :=
        (Complex.continuous_ofReal.continuousAt.comp
          (ContinuousAt.comp (f := fun w : Y => (c₂.j w).im) (g := τ_inv) hτinv_at him_at)).mul continuousAt_const
      exact ContinuousAt.comp (g := fun w : Y => ((2 - (c₂.j w).re : ℝ) : ℂ) + (τ_inv (c₂.j w).im : ℂ) * Complex.I)
        (hre_at.add him2_at) continuous_subtype_val.continuousAt
  let cS : SurfChart S :=
    ⟨U_S, O_S, jS, kS, hUS_open, hOS_open, hjS_cont, hOS_inter.symm ▸ hkS_cont,
     by rintro _ ⟨w, hw, rfl⟩; rw [hjS_kS w hw, hOS_inter]; exact hw,
     fun w hw => ⟨w, hw.1, rfl⟩,
     by rintro _ ⟨w, hw, rfl⟩; rw [hjS_kS w hw],
     fun w hw => hjS_kS w hw.1⟩
  have hξ_inS : ψ (ξ (1 / 2)) ∈ cS.U := by
    have h1 : ξ (1 / 2) ∈ Q₁ :=
      ⟨0, ⟨Complex.mem_reProdIm.mpr ⟨⟨by simp; linarith, by simp; exact hε⟩, ⟨by simp; linarith, by simp; exact hε⟩⟩,
        by simp [halfPlane]⟩, by rw [← hc₁0, c₁.hl hξc₁]⟩
    exact show ξ (1 / 2) ∈ ψ ⁻¹' U_S from hUS_pre.symm ▸ Or.inl h1
  have hη_inS : ψ (η (1 / 2)) ∈ cS.U := by
    rw [L.hη (1 / 2) hmidI, ← L.hξ (1 / 2) hmidI]; exact hξ_inS
  -- 1. Compute `cutChartPos c₁ cS ψ (ξ (1/2))`: TRUE (`z ↦ z + 2`)!
  have hcut1 : cutChartPos c₁ cS ψ (ξ (1 / 2)) := by
    refine ⟨Q₁, hQ₁_open,
      ⟨0, ⟨Complex.mem_reProdIm.mpr ⟨⟨by simp; linarith, by simp; exact hε⟩, ⟨by simp; linarith, by simp; exact hε⟩⟩,
        by simp [halfPlane]⟩, by rw [← hc₁0, c₁.hl hξc₁]⟩,
      fun y hy => ⟨by
        obtain ⟨z, ⟨hzR, hzh⟩, rfl⟩ := hy
        exact c₁.hk' ⟨hr₁O (Complex.mem_reProdIm.mpr ⟨⟨by linarith [(Complex.mem_reProdIm.mp hzR).1.1],
          by linarith [(Complex.mem_reProdIm.mp hzR).1.2]⟩,
          ⟨by linarith [(Complex.mem_reProdIm.mp hzR).2.1], by linarith [(Complex.mem_reProdIm.mp hzR).2.2]⟩⟩), hzh⟩,
        hUS_pre.symm ▸ Or.inl hy⟩, fun y' ⟨hy'Q, hy'I⟩ => ?_⟩
    obtain ⟨z, ⟨hzR, hzh⟩, rfl⟩ := hy'Q
    have hzO : z ∈ c₁.O ∩ halfPlane :=
      ⟨hr₁O (Complex.mem_reProdIm.mpr ⟨⟨by linarith [(Complex.mem_reProdIm.mp hzR).1.1],
        by linarith [(Complex.mem_reProdIm.mp hzR).1.2]⟩,
        ⟨by linarith [(Complex.mem_reProdIm.mp hzR).2.1], by linarith [(Complex.mem_reProdIm.mp hzR).2.2]⟩⟩), hzh⟩
    have hzre : 0 < z.re := lt_of_le_of_ne hzh (Ne.symm fun h0 => hy'I ((c₁.mem_bd_iff (c₁.hk' hzO)).mpr (by rw [c₁.hr hzO]; exact h0)))
    rw [c₁.hr hzO]
    have hev : (cS.j ∘ ψ ∘ c₁.k) =ᶠ[𝓝 z] fun w : ℂ => (1 : ℂ) * w + 2 := by
      have hO' : IsOpen ((Ioo (-ε) ε ×ℂ Ioo (-ε) ε) ∩ {w : ℂ | 0 < w.re}) :=
        ((isOpen_Ioo.preimage Complex.continuous_re).inter (isOpen_Ioo.preimage Complex.continuous_im)).inter
          (isOpen_lt (continuous_const (y := (0 : ℝ))) Complex.continuous_re)
      filter_upwards [hO'.mem_nhds ⟨hzR, hzre⟩] with w ⟨hwR, hwre⟩
      have hwpos : 0 < w.re := hwre
      have hwO : w ∈ c₁.O ∩ halfPlane :=
        ⟨hr₁O (Complex.mem_reProdIm.mpr ⟨⟨by linarith [(Complex.mem_reProdIm.mp hwR).1.1],
          by linarith [(Complex.mem_reProdIm.mp hwR).1.2]⟩,
          ⟨by linarith [(Complex.mem_reProdIm.mp hwR).2.1], by linarith [(Complex.mem_reProdIm.mp hwR).2.2]⟩⟩), hwpos.le⟩
      have hkwQ : c₁.k w ∈ Q₁ := ⟨w, ⟨hwR, hwpos.le⟩, rfl⟩
      show jS (ψ (c₁.k w)) = (1 : ℂ) * w + 2
      rw [hjS_ψ _ (.inl hkwQ), show jpre (c₁.k w) = c₁.j (c₁.k w) + 2 from ite_eq_left hkwQ, c₁.hr hwO, one_mul]
    rw [isPosLocal_congr hev]
    exact isPosLocal_affine one_ne_zero 2 z
  -- 2. Compute `cutChartPos c₂ cS ψ (η (1/2)) ↔ (s₁ ≠ s₂)`!
  have hcut2 : cutChartPos c₂ cS ψ (η (1 / 2)) ↔ s₁ ≠ s₂ := by
    have hQ₂_sub : Q₂ ⊆ c₂.U ∩ ψ ⁻¹' cS.U := fun y hy => ⟨by
      obtain ⟨z, ⟨hzR, hzh⟩, rfl⟩ := hy
      obtain ⟨t', ht', ht'eq⟩ := hτ_open_img.symm.subset (Complex.mem_reProdIm.mp hzR).2
      exact c₂.hk' ⟨hr₂O (Complex.mem_reProdIm.mpr ⟨⟨by linarith [(Complex.mem_reProdIm.mp hzR).1.1],
        by linarith [(Complex.mem_reProdIm.mp hzR).1.2]⟩, ht'eq ▸ hτ_r₂ t' (Ioo_subset_Icc_self ht')⟩), hzh⟩,
      hUS_pre.symm ▸ Or.inr hy⟩
    have hηQ₂ : η (1 / 2) ∈ Q₂ :=
      ⟨0, ⟨Complex.mem_reProdIm.mpr ⟨⟨by simp; linarith, by simp; exact hε⟩, by simp; exact h0_ab⟩,
        by simp [halfPlane]⟩, by rw [← hc₂0, c₂.hl hηc₂]⟩
    -- Interior point `y₀ := c₂.k (ε / 2) ∈ Q₂ ∩ (bd Y)ᶜ`:
    set z₀ : ℂ := ((ε / 2 : ℝ) : ℂ)
    have hz₀R : z₀ ∈ Ioo (-ε) ε ×ℂ Ioo a_τ b_τ :=
      Complex.mem_reProdIm.mpr ⟨⟨by simp [z₀]; linarith, by simp [z₀]; linarith⟩, by simpa [z₀] using h0_ab⟩
    have hz₀O : z₀ ∈ c₂.O ∩ halfPlane :=
      ⟨hr₂O (Complex.mem_reProdIm.mpr ⟨⟨by simp [z₀]; linarith [hε, hε_r₂], by simp [z₀]; linarith [hε, hε_r₂]⟩,
        ⟨by simp [z₀]; linarith [hr₂], by simp [z₀]; exact hr₂⟩⟩), by simp [halfPlane, z₀]; linarith [hε]⟩
    have hy₀Q₂ : c₂.k z₀ ∈ Q₂ := ⟨z₀, ⟨hz₀R, hz₀O.2⟩, rfl⟩
    have hy₀I : c₂.k z₀ ∈ (bd Y)ᶜ := by
      rw [mem_compl_iff, c₂.mem_bd_iff (c₂.hk' hz₀O), c₂.hr hz₀O]; simp [z₀]; linarith
    have hQ₂_conn : IsPreconnected (c₂.j '' (Q₂ ∩ (bd Y)ᶜ)) := by
      have heq : c₂.j '' (Q₂ ∩ (bd Y)ᶜ) = Ioo 0 ε ×ℂ Ioo a_τ b_τ := by
        ext z; constructor
        · rintro ⟨y, ⟨⟨w, ⟨hwR, hwh⟩, rfl⟩, hyI⟩, rfl⟩
          obtain ⟨t', ht', ht'eq⟩ := hτ_open_img.symm.subset (Complex.mem_reProdIm.mp hwR).2
          have hwO : w ∈ c₂.O ∩ halfPlane :=
            ⟨hr₂O (Complex.mem_reProdIm.mpr ⟨⟨by linarith [(Complex.mem_reProdIm.mp hwR).1.1, hε_r₂],
              by linarith [(Complex.mem_reProdIm.mp hwR).1.2, hε_r₂]⟩, ht'eq ▸ hτ_r₂ t' (Ioo_subset_Icc_self ht')⟩), hwh⟩
          have hwpos : 0 < w.re := lt_of_le_of_ne hwh (Ne.symm fun h0 => hyI ((c₂.mem_bd_iff (c₂.hk' hwO)).mpr (by rw [c₂.hr hwO]; exact h0)))
          rw [c₂.hr hwO]
          exact Complex.mem_reProdIm.mpr ⟨⟨hwpos, (Complex.mem_reProdIm.mp hwR).1.2⟩, (Complex.mem_reProdIm.mp hwR).2⟩
        · intro hz
          have hre := (Complex.mem_reProdIm.mp hz).1
          have him := (Complex.mem_reProdIm.mp hz).2
          obtain ⟨t', ht', ht'eq⟩ := hτ_open_img.symm.subset him
          have hzO : z ∈ c₂.O ∩ halfPlane :=
            ⟨hr₂O (Complex.mem_reProdIm.mpr ⟨⟨by linarith [hre.1, hr₂], by linarith [hre.2, hε_r₂]⟩, ht'eq ▸ hτ_r₂ t' (Ioo_subset_Icc_self ht')⟩), hre.1.le⟩
          refine ⟨c₂.k z, ⟨⟨z, ⟨Complex.mem_reProdIm.mpr ⟨⟨by linarith [hre.1, hε], hre.2⟩, him⟩, hre.1.le⟩, rfl⟩, ?_⟩, c₂.hr hzO⟩
          rw [mem_compl_iff, c₂.mem_bd_iff (c₂.hk' hzO), c₂.hr hzO]; exact hre.1.ne'
      rw [heq]
      have him_eq : (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) '' (Ioo 0 ε ×ˢ Ioo a_τ b_τ) =
          Ioo 0 ε ×ℂ Ioo a_τ b_τ := by
        ext z; constructor
        · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
          exact Complex.mem_reProdIm.mpr ⟨by simpa using hx, by simpa using hy⟩
        · intro hz
          exact ⟨(z.re, z.im), Complex.mem_reProdIm.mp hz, Complex.re_add_im z⟩
      rw [← him_eq]
      exact (isPreconnected_Ioo.prod isPreconnected_Ioo).image _
        ((Complex.continuous_ofReal.comp continuous_fst).add
          ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)).continuousOn
    rw [cutChartPos_iff_of_int hψ hF hQ₂_open hηQ₂ hy₀Q₂ hy₀I hQ₂_sub hQ₂_conn, c₂.hr hz₀O]
    -- Near `z₀`, `cS.j ∘ ψ ∘ c₂.k` equals `w ↦ (-w.re + 2) + τ_inv(w.im) * I`!
    have hev : (cS.j ∘ ψ ∘ c₂.k) =ᶠ[𝓝 z₀] fun w : ℂ => ((-w.re + 2 : ℝ) : ℂ) + (τ_inv w.im : ℂ) * Complex.I := by
      have hO' : IsOpen (Ioo 0 ε ×ℂ Ioo a_τ b_τ) :=
        (isOpen_Ioo.preimage Complex.continuous_re).inter (isOpen_Ioo.preimage Complex.continuous_im)
      filter_upwards [hO'.mem_nhds (Complex.mem_reProdIm.mpr ⟨⟨by simp [z₀]; linarith, by simp [z₀]; linarith⟩, by simpa [z₀] using h0_ab⟩)]
        with w hw
      have hre := (Complex.mem_reProdIm.mp hw).1
      have him := (Complex.mem_reProdIm.mp hw).2
      obtain ⟨t', ht', ht'eq⟩ := hτ_open_img.symm.subset him
      have hwO : w ∈ c₂.O ∩ halfPlane :=
        ⟨hr₂O (Complex.mem_reProdIm.mpr ⟨⟨by linarith [hre.1, hr₂], by linarith [hre.2, hε_r₂]⟩, ht'eq ▸ hτ_r₂ t' (Ioo_subset_Icc_self ht')⟩), hre.1.le⟩
      have hkwQ : c₂.k w ∈ Q₂ := ⟨w, ⟨Complex.mem_reProdIm.mpr ⟨⟨by linarith [hre.1, hε], hre.2⟩, him⟩, hre.1.le⟩, rfl⟩
      show jS (ψ (c₂.k w)) = ((-w.re + 2 : ℝ) : ℂ) + (τ_inv w.im : ℂ) * Complex.I
      rw [hjS_ψ _ (.inr hkwQ),
        show jpre (c₂.k w) = ((2 - (c₂.j (c₂.k w)).re : ℝ) : ℂ) + (τ_inv (c₂.j (c₂.k w)).im : ℂ) * Complex.I from
          ite_eq_right fun h => Set.disjoint_left.mp hQ₁₂_disj h hkwQ,
        c₂.hr hwO]
      apply Complex.ext <;> simp; ring
    rw [isPosLocal_congr hev]
    -- Choose `r₀ > 0` so `[z₀.im - r₀, z₀.im + r₀] = [-r₀, r₀] ⊆ Ioo a_τ b_τ`:
    set r₀ := min (-a_τ / 2) (b_τ / 2)
    have hr₀ : 0 < r₀ := lt_min (by linarith [h0_ab.1]) (by linarith [h0_ab.2])
    have hr₀_sub : Icc (z₀.im - r₀) (z₀.im + r₀) ⊆ Ioo a_τ b_τ := fun y hy => by
      simp only [z₀, Complex.ofReal_im, zero_sub, zero_add] at hy
      exact ⟨by linarith [hy.1, min_le_left (-a_τ / 2) (b_τ / 2), h0_ab.1],
             by linarith [hy.2, min_le_right (-a_τ / 2) (b_τ / 2), h0_ab.2]⟩
    cases hsb : (s₁ == s₂)
    · -- `s₁ ≠ s₂`: `τ` is strictly decreasing, so `τ_inv` is strictly decreasing → `IsPosLocal`!
      rw [hsb] at hτ_dir; simp only [Bool.false_eq_true, ↓reduceIte] at hτ_dir
      have hτinv_anti : StrictAntiOn τ_inv (Icc (z₀.im - r₀) (z₀.im + r₀)) := fun y₁ hy₁ y₂ hy₂ hlt => by
        by_contra hge
        have h1 := hτ_inv_mem y₁ (hr₀_sub hy₁)
        have h2 := hτ_inv_mem y₂ (hr₀_sub hy₂)
        rcases eq_or_lt_of_le (not_lt.mp hge) with he | hgt
        · have := (hτ_inv_eq y₁ (hr₀_sub hy₁)).symm.trans ((congrArg τ he).trans (hτ_inv_eq y₂ (hr₀_sub hy₂)))
          linarith
        · have := hτ_dir (Ioo_subset_Icc_self h1) (Ioo_subset_Icc_self h2) hgt
          rw [hτ_inv_eq y₁ (hr₀_sub hy₁), hτ_inv_eq y₂ (hr₀_sub hy₂)] at this; linarith
      exact iff_of_true (isPosLocal_flip_re_strictAnti hr₀ (hτ_inv_cont.mono hr₀_sub) hτinv_anti) (by simpa using hsb)
    · -- `s₁ = s₂`: `τ` is strictly increasing, so `τ_inv` is strictly increasing → `¬ IsPosLocal`!
      rw [hsb] at hτ_dir; simp only [↓reduceIte] at hτ_dir
      have hτinv_mono : StrictMonoOn τ_inv (Icc (z₀.im - r₀) (z₀.im + r₀)) := fun y₁ hy₁ y₂ hy₂ hlt => by
        by_contra hge
        have h1 := hτ_inv_mem y₁ (hr₀_sub hy₁)
        have h2 := hτ_inv_mem y₂ (hr₀_sub hy₂)
        rcases eq_or_lt_of_le (not_lt.mp hge) with he | hgt
        · have := (hτ_inv_eq y₁ (hr₀_sub hy₁)).symm.trans ((congrArg τ he.symm).trans (hτ_inv_eq y₂ (hr₀_sub hy₂)))
          linarith
        · have := hτ_dir (Ioo_subset_Icc_self h2) (Ioo_subset_Icc_self h1) hgt
          rw [hτ_inv_eq y₁ (hr₀_sub hy₁), hτ_inv_eq y₂ (hr₀_sub hy₂)] at this; linarith
      exact iff_of_false (not_isPosLocal_flip_re_strictMono hr₀ (hτ_inv_cont.mono hr₀_sub) hτinv_mono) (by simpa using hsb)
  -- 3. Compute `cuffPos c₁ φ₁ (ξ (1/2))` and `cuffPos c₂ φ₂ (η (1/2))`:
  have hcp1 : cuffPos c₁ φ₁ (ξ (1 / 2)) ↔ σ₁ = s₁ :=
    cuffPos_iff_dir_eq hC₁ φ₁ hδ (fun u hu => (hδ_in u hu).1.1) (hm₁c.mono hIδ)
      (fun u hu => hm₁ξ u (hIδ hu)) σ₁
      (by cases σ₁ <;> simp only [Bool.false_eq_true, ↓reduceIte] at hm₁_dir ⊢; exact hm₁_dir.mono hIδ; exact hm₁_dir.mono hIδ)
      s₁ hs₁
  have hcp2 : cuffPos c₂ φ₂ (η (1 / 2)) ↔ σ₂ = s₂ :=
    cuffPos_iff_dir_eq hC₂ φ₂ hδ (fun u hu => (hδ_in u hu).2.1) (hm₂c.mono hIδ)
      (fun u hu => hm₂η u (hIδ hu)) σ₂
      (by cases σ₂ <;> simp only [Bool.false_eq_true, ↓reduceIte] at hm₂_dir ⊢; exact hm₂_dir.mono hIδ; exact hm₂_dir.mono hIδ)
      s₂ hs₂
  -- 4. Combine via `cuffSignChart_change` and `cutChartSign_change`!
  have hch_cuff1 := cuffSignChart_change hC₁ φ₁ ((hm₁ξ (1 / 2) hmidI) ▸ (φ₁ _).2) hξc₁ (AY.mem_chart _)
  have hch_cuff2 := cuffSignChart_change hC₂ φ₂ ((hm₂η (1 / 2) hmidI) ▸ (φ₂ _).2) hηc₂ (AY.mem_chart _)
  have hch_cut1 := cutChartSign_change hψ hF hξc₁ (AY.mem_chart _) hξ_inS (AS.mem_chart _)
  have hch_cut2 := cutChartSign_change hψ hF hηc₂ (AY.mem_chart _) hη_inS (AS.mem_chart _)
  have hsym1 := chartSign_symm (AY.mem_chart (ξ (1 / 2))) hξc₁
  have hsym2 := chartSign_symm (AY.mem_chart (η (1 / 2))) hηc₂
  have hψ_mid : ψ (ξ (1 / 2)) = ψ (η (1 / 2)) := (L.hξ (1 / 2) hmidI).trans (L.hη (1 / 2) hmidI).symm
  have hS_same : chartSign cS (AS.chart (AS.idx (ψ (ξ (1 / 2))))) (ψ (ξ (1 / 2))) =
      chartSign cS (AS.chart (AS.idx (ψ (η (1 / 2))))) (ψ (η (1 / 2))) := by rw [hψ_mid]
  have hcs1 : cuffSign AY φ₁ (ξ (1 / 2)) =
      chartSign c₁ (AY.chart (AY.idx (ξ (1 / 2)))) (ξ (1 / 2)) + cuffSignChart c₁ φ₁ (ξ (1 / 2)) :=
    eq_add_of_sub_eq hch_cuff1
  have hcs2 : cuffSign AY φ₂ (η (1 / 2)) =
      chartSign c₂ (AY.chart (AY.idx (η (1 / 2)))) (η (1 / 2)) + cuffSignChart c₂ φ₂ (η (1 / 2)) :=
    eq_add_of_sub_eq hch_cuff2
  unfold cutOrientDiff
  rw [hcs1, hcs2, hch_cut1, hch_cut2, hsym1, hsym2, hS_same]
  have hsimp :
      (chartSign (AY.chart (AY.idx (ξ (1 / 2)))) c₁ (ξ (1 / 2)) + cuffSignChart c₁ φ₁ (ξ (1 / 2)) +
        (chartSign (AY.chart (AY.idx (ξ (1 / 2)))) c₁ (ξ (1 / 2)) + cutChartSign c₁ cS ψ (ξ (1 / 2)) +
          chartSign cS (AS.chart (AS.idx (ψ (η (1 / 2))))) (ψ (η (1 / 2)))) +
        (if σ₁ then (0 : ZMod 2) else 1)) +
      (chartSign (AY.chart (AY.idx (η (1 / 2)))) c₂ (η (1 / 2)) + cuffSignChart c₂ φ₂ (η (1 / 2)) +
        (chartSign (AY.chart (AY.idx (η (1 / 2)))) c₂ (η (1 / 2)) + cutChartSign c₂ cS ψ (η (1 / 2)) +
          chartSign cS (AS.chart (AS.idx (ψ (η (1 / 2))))) (ψ (η (1 / 2)))) +
        (if σ₂ then (0 : ZMod 2) else 1)) =
      cuffSignChart c₁ φ₁ (ξ (1 / 2)) + cutChartSign c₁ cS ψ (ξ (1 / 2)) + (if σ₁ then 0 else 1) +
      (cuffSignChart c₂ φ₂ (η (1 / 2)) + cutChartSign c₂ cS ψ (η (1 / 2)) + (if σ₂ then 0 else 1)) := by
    ring_nf; simp [zmod2_two]
  rw [hsimp]
  unfold cuffSignChart cutChartSign
  simp only [hcp1, hcp2, hcut1, hcut2, ↓reduceIte]
  cases σ₁ <;> cases σ₂ <;> cases s₁ <;> cases s₂ <;> decide

end LiftOppSign

/-! ### Determining 1-sidedness (same cuff) and relative orientation (distinct cuffs) via `cocInt (w1 AS)` -/

section ArcInvariants

variable {Y S : Type u} [TopologicalSpace Y] [TopologicalSpace S]

/-- **Same-cuff 1-sidedness criterion**: when `s, t` lie on the same cuff `C` of `S` and `A₁` is a
continuous path in `C` from `t` to `s` whose interior avoids `F`, let `ψ : Y → S` cut `S` along `F`
with lifts `ξ, η` on cuffs `C_ξ, C_η`:
- if `C_ξ ≠ C_η` (`F` is 2-sided), then `cocInt (w1 AS) (conc2 a A₁) = 0`;
- if `C_ξ = C_η` (`F` is 1-sided) and `ξ, η` run in the SAME direction along `C_ξ`, then
  `cocInt (w1 AS) (conc2 a A₁) = 1`! -/
theorem cocInt_loop_same_cuff (hY : IsSurface Y) (hS : IsSurface S) [T2Space Y]
    {ψ : Y → S} {F : Set S} {s t : S} (hψ : IsCutting ψ F) (hF : IsClosed F)
    (hb : F ∩ bd S = {s, t}) {X X' : Set Y} (hP : LiftPair ψ F s t X X')
    {a : ℝ → S} {ξ η : ℝ → Y} (L : ArcLift ψ F a ξ η)
    (ha0 : a 0 = s) (ha1 : a 1 = t) (himξ : ξ '' Icc 0 1 = X) (himη : η '' Icc 0 1 = X')
    (hiξ : InjOn ξ (Icc 0 1)) (hiη : InjOn η (Icc 0 1))
    (AY : SurfAtlas Y) (AS : SurfAtlas S)
    {A₁ : ℝ → S} (hA₁c : ContinuousOn A₁ (Icc 0 1))
    (hA₁0 : A₁ 0 = t) (_hA₁1 : A₁ 1 = s) (_hA₁off : ∀ u ∈ Ioo (0 : ℝ) 1, A₁ u ∉ F)
    {C_ξ : Set Y} (hCξ : C_ξ ⊆ bd Y) (φ : Circle ≃ₜ C_ξ)
    {m₁ : ℝ → ℝ} (hm₁c : ContinuousOn m₁ (Icc 0 1))
    (hm₁ξ : ∀ u ∈ Icc (0 : ℝ) 1, (φ (ee (m₁ u))).1 = ξ u)
    (hm₁m : StrictMonoOn m₁ (Icc 0 1))
    {γ_gap : ℝ → Y} (hgc : ContinuousOn γ_gap (Icc 0 1))
    (hgC : ∀ u ∈ Icc (0 : ℝ) 1, γ_gap u ∈ C_ξ)
    (hgψ : ∀ u ∈ Icc (0 : ℝ) 1, ψ (γ_gap u) = A₁ u)
    (hg0 : γ_gap 0 = ξ 1) :
    (γ_gap 1 = ξ 0 → cocInt (w1 AS) (conc2 a A₁) = 0) ∧
    (γ_gap 1 = η 0 →
      (∃ m₂ : ℝ → ℝ, ContinuousOn m₂ (Icc 0 1) ∧ StrictMonoOn m₂ (Icc 0 1) ∧
        ∀ u ∈ Icc (0 : ℝ) 1, (φ (ee (m₂ u))).1 = η u) →
      cocInt (w1 AS) (conc2 a A₁) = 1) := by
  have hcocS := isCoc_w1 hS AS
  have ha_cont : ContinuousOn a (Icc 0 1) :=
    (hψ.1.comp_continuousOn L.cξ).congr fun u hu => (L.hξ u hu).symm
  have hξC : ∀ u ∈ Icc (0 : ℝ) 1, ξ u ∈ C_ξ := fun u hu => (hm₁ξ u hu) ▸ (φ _).2
  -- Note `cocInt (w1 AS) (conc2 a A₁) = cocInt (w1 AS) (ψ ∘ conc2 ξ γ_gap)` since they agree on `Icc 0 1`!
  have hconc_eq : ∀ u ∈ Icc (0 : ℝ) 1, (ψ ∘ conc2 ξ γ_gap) u = conc2 a A₁ u := fun u hu => by
    unfold conc2; simp only [comp_apply]
    split_ifs with h
    · exact L.hξ (2 * u) ⟨by linarith [hu.1], by linarith⟩
    · exact hgψ (2 * u - 1) ⟨by linarith [not_le.mp h], by linarith [hu.2]⟩
  have hcoc_eq : ∀ {γ₁ γ₂ : ℝ → S}, ContinuousOn γ₁ (Icc 0 1) →
      (∀ u ∈ Icc (0 : ℝ) 1, γ₁ u = γ₂ u) → cocInt (w1 AS) γ₁ = cocInt (w1 AS) γ₂ := by
    intro γ₁ γ₂ h1 heq
    have h2 : ContinuousOn γ₂ (Icc 0 1) := h1.congr fun u hu => (heq u hu).symm
    obtain ⟨N, hN, hcoc⟩ := hcocS
    obtain ⟨n₁, -, hn₁⟩ := cocInt_eq_sum hN hcoc h1
    obtain ⟨n₂, -, hn₂⟩ := cocInt_eq_sum hN hcoc h2
    set M := max n₁ (max n₂ 1)
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le one_pos ((le_max_right n₂ 1).trans (le_max_right _ _)))
    rw [hn₁ M (le_max_left _ _), hn₂ M ((le_max_left _ _).trans (le_max_right _ _))]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < M := Finset.mem_range.mp hk
    have hI1 : (k : ℝ) / M ∈ Icc (0 : ℝ) 1 := ⟨by positivity, (div_le_one hM0).mpr (by exact_mod_cast hk'.le)⟩
    have hI2 : ((k + 1 : ℕ) : ℝ) / M ∈ Icc (0 : ℝ) 1 := ⟨by positivity, (div_le_one hM0).mpr (by exact_mod_cast hk')⟩
    rw [heq _ hI1, heq _ hI2]
  constructor
  · intro hg1
    have hγc : ContinuousOn (conc2 ξ γ_gap) (Icc 0 1) := continuousOn_conc2 L.cξ hgc hg0.symm
    have hγC : ∀ u ∈ Icc (0 : ℝ) 1, conc2 ξ γ_gap u ∈ C_ξ := fun u hu => by
      unfold conc2; split_ifs with h
      · exact hξC _ ⟨by linarith [hu.1], by linarith⟩
      · exact hgC _ ⟨by linarith [not_le.mp h], by linarith [hu.2]⟩
    rw [← hcoc_eq (hψ.1.comp_continuousOn hγc) hconc_eq, cocInt_w1_cut_cuff hY hS hψ hF AY AS hCξ φ hγc hγC]
    have hc1 : conc2 ξ γ_gap 1 = ξ 0 := by
      unfold conc2; rw [ite_eq_right (by norm_num), show (2 : ℝ) * 1 - 1 = 1 by norm_num]; exact hg1
    have hc0 : conc2 ξ γ_gap 0 = ξ 0 := by
      unfold conc2; rw [ite_eq_left (by norm_num)]; simp
    rw [hc1, hc0, sub_self]
  · intro hg1 ⟨m₂, hm₂c, hm₂m, hm₂η⟩
    have hηC : ∀ u ∈ Icc (0 : ℝ) 1, η u ∈ C_ξ := fun u hu => (hm₂η u hu) ▸ (φ _).2
    -- Split `a` at `1/2`: `a_lo u = a (u / 2)` (`0 → 1/2`), `a_hi u = a ((u + 1) / 2)` (`1/2 → 1`)!
    let ξ_lo : ℝ → Y := fun u => ξ (u / 2)
    let ξ_hi : ℝ → Y := fun u => ξ ((u + 1) / 2)
    let η_lo : ℝ → Y := fun u => η (u / 2)
    have hξlo_c : ContinuousOn ξ_lo (Icc 0 1) := L.cξ.comp (by fun_prop) fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hξhi_c : ContinuousOn ξ_hi (Icc 0 1) := L.cξ.comp (by fun_prop) fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hηlo_c : ContinuousOn η_lo (Icc 0 1) := L.cη.comp (by fun_prop) fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
    -- Notice `conc2 ξ_lo ξ_hi` equals `ξ` on `Icc 0 1`, and `ψ ∘ η_lo = ψ ∘ ξ_lo` on `Icc 0 1`!
    have h_a_split : cocInt (w1 AS) a = cocInt (w1 AS) (ψ ∘ η_lo) + cocInt (w1 AS) (ψ ∘ ξ_hi) := by
      have heq1 : ∀ u ∈ Icc (0 : ℝ) 1, (ψ ∘ conc2 ξ_lo ξ_hi) u = a u := fun u hu => by
        unfold conc2; simp only [comp_apply, ξ_lo, ξ_hi]
        split_ifs with h
        · rw [show 2 * u / 2 = u by ring]; exact L.hξ u hu
        · rw [show (2 * u - 1 + 1) / 2 = u by ring]; exact L.hξ u hu
      have heq2 : ∀ u ∈ Icc (0 : ℝ) 1, (ψ ∘ ξ_lo) u = (ψ ∘ η_lo) u := fun u hu => by
        simp only [comp_apply, ξ_lo, η_lo]
        exact (L.hξ _ ⟨by linarith [hu.1], by linarith [hu.2]⟩).trans
          (L.hη _ ⟨by linarith [hu.1], by linarith [hu.2]⟩).symm
      rw [← hcoc_eq (hψ.1.comp_continuousOn (continuousOn_conc2 hξlo_c hξhi_c (by simp [ξ_lo, ξ_hi]))) heq1]
      have heq3 : ∀ u ∈ Icc (0 : ℝ) 1, (ψ ∘ conc2 ξ_lo ξ_hi) u = conc2 (ψ ∘ ξ_lo) (ψ ∘ ξ_hi) u := fun u _ => by
        unfold conc2; simp only [comp_apply]; split_ifs <;> rfl
      rw [hcoc_eq (hψ.1.comp_continuousOn (continuousOn_conc2 hξlo_c hξhi_c (by simp [ξ_lo, ξ_hi]))) heq3,
        cocInt_conc2 hcocS (hψ.1.comp_continuousOn hξlo_c) (hψ.1.comp_continuousOn hξhi_c) (by simp [ξ_lo, ξ_hi]),
        hcoc_eq (hψ.1.comp_continuousOn hξlo_c) heq2]
    have hA₁_eq : cocInt (w1 AS) A₁ = cocInt (w1 AS) (ψ ∘ γ_gap) :=
      (hcoc_eq (hψ.1.comp_continuousOn hgc) hgψ).symm
    rw [cocInt_conc2 hcocS ha_cont hA₁c (ha1.trans hA₁0.symm), h_a_split, hA₁_eq,
      cocInt_w1_cut_cuff hY hS hψ hF AY AS hCξ φ hξhi_c (fun u hu => hξC _ ⟨by linarith [hu.1], by linarith [hu.2]⟩),
      cocInt_w1_cut_cuff hY hS hψ hF AY AS hCξ φ hgc hgC,
      cocInt_w1_cut_cuff hY hS hψ hF AY AS hCξ φ hηlo_c (fun u hu => hηC _ ⟨by linarith [hu.1], by linarith [hu.2]⟩)]
    simp only [ξ_hi, η_lo, zero_add, zero_div, hg0, hg1]
    have h11 : (1 + 1 : ℝ) / 2 = 1 := by norm_num
    rw [h11]
    have hopp := cut_lift_opp_sign hY hS hψ hF hb hP L ha0 ha1 himξ himη hiξ hiη AY AS hCξ hCξ φ φ
      hm₁c hm₂c hm₁ξ hm₂η true true hm₁m hm₂m
    simp only [↓reduceIte, add_zero] at hopp
    rw [← hopp]
    simp only [zmod2_sub_eq_add]
    ring_nf
    simp [zmod2_two]

/-- **Distinct-cuffs relative orientation criterion**: when `s ∈ C_s` and `t ∈ C_t` lie on distinct
cuffs of `S`, `Y` has a single merged cuff `C_Y` parameterized by `φ_Y` containing `ξ` (`m` strictly
increasing on `[0, 1]`), with `G_s` just before `m 0` matching `φ_s : Circle ≃ₜ C_s` with sign `σ_s`
and `G_t` just after `m 1` matching `φ_t : Circle ≃ₜ C_t` with sign `σ_t`, then:
`cocInt (w1 AS) a = (cuffSign AS φ_t t + if σ_t then 0 else 1) - (cuffSign AS φ_s s + if σ_s then 0 else 1)`! -/
theorem cocInt_arc_diff_cuff (hY : IsSurface Y) (hS : IsSurface S) [T2Space Y]
    {ψ : Y → S} {F : Set S} {s t : S} (hψ : IsCutting ψ F) (hF : IsClosed F)
    {a : ℝ → S} {ξ η : ℝ → Y} (L : ArcLift ψ F a ξ η) (ha0 : a 0 = s) (ha1 : a 1 = t)
    (AY : SurfAtlas Y) (AS : SurfAtlas S)
    {C_Y : Set Y} (hCY : C_Y ⊆ bd Y) (φY : Circle ≃ₜ C_Y)
    {C_s C_t : Set S} (hCs : C_s ⊆ bd S) (hCt : C_t ⊆ bd S)
    (φs : Circle ≃ₜ C_s) (φt : Circle ≃ₜ C_t)
    {m : ℝ → ℝ} (_hmc : ContinuousOn m (Icc 0 1)) (hmξ : ∀ u ∈ Icc (0 : ℝ) 1, (φY (ee (m u))).1 = ξ u)
    {ε : ℝ} (hε : 0 < ε) (σ_s σ_t : Bool) {u_s u_t : ℝ}
    (hmatch_s : ∀ r ∈ Icc (-ε) 0, ψ (φY (ee (m 0 + r))).1 = (φs (ee (u_s + if σ_s then r else -r))).1)
    (hmatch_t : ∀ r ∈ Icc 0 ε, ψ (φY (ee (m 1 + r))).1 = (φt (ee (u_t + if σ_t then r else -r))).1)
    (hoff_s : ψ (φY (ee (m 0 - ε / 2))).1 ∉ F)
    (hoff_t : ψ (φY (ee (m 1 + ε / 2))).1 ∉ F) :
    cocInt (w1 AS) a =
      (cuffSign AS φt t + (if σ_t then 0 else 1)) -
      (cuffSign AS φs s + (if σ_s then 0 else 1)) := by
  have hcocS := isCoc_w1 hS AS
  have ha_cont : ContinuousOn a (Icc 0 1) :=
    (hψ.1.comp_continuousOn L.cξ).congr fun u hu => (L.hξ u hu).symm
  -- Three paths on `C_Y`:
  -- `γ_s`: `m 0 - ε/2 → m 0` (projects to `C_s`, ending at `s`)
  -- `ξ`:   `0 → 1` (projects to `a`, from `s` to `t`)
  -- `γ_t`: `m 1 → m 1 + ε/2` (projects to `C_t`, starting at `t`)
  let γ_s : ℝ → Y := fun u => (φY (ee (m 0 - ε / 2 + u * (ε / 2)))).1
  let γ_t : ℝ → Y := fun u => (φY (ee (m 1 + u * (ε / 2)))).1
  have hγs_c : ContinuousOn γ_s (Icc 0 1) :=
    (continuous_subtype_val.comp (φY.continuous.comp (continuous_ee.comp (by fun_prop)))).continuousOn
  have hγt_c : ContinuousOn γ_t (Icc 0 1) :=
    (continuous_subtype_val.comp (φY.continuous.comp (continuous_ee.comp (by fun_prop)))).continuousOn
  have hγs_1 : γ_s 1 = ξ 0 := by
    have : m 0 - ε / 2 + 1 * (ε / 2) = m 0 := by ring
    simp only [γ_s, this]; exact hmξ 0 (by simp)
  have hγt_0 : γ_t 0 = ξ 1 := by
    simp only [γ_t, zero_mul, add_zero]; exact hmξ 1 (by simp)
  have hγs_Cs : ∀ u ∈ Icc (0 : ℝ) 1, ψ (γ_s u) ∈ C_s := fun u hu => by
    have hr : (u - 1) * (ε / 2) ∈ Icc (-ε) 0 := ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩
    have h1 : m 0 - ε / 2 + u * (ε / 2) = m 0 + (u - 1) * (ε / 2) := by ring
    simp only [γ_s, h1, hmatch_s _ hr]; exact (φs _).2
  have hγt_Ct : ∀ u ∈ Icc (0 : ℝ) 1, ψ (γ_t u) ∈ C_t := fun u hu => by
    have hr : u * (ε / 2) ∈ Icc 0 ε := ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩
    simp only [γ_t, hmatch_t _ hr]; exact (φt _).2
  -- Compute `cocInt (w1 AS)` on each of the 3 pieces in two ways!
  have e_s1 := cocInt_w1_cut_cuff hY hS hψ hF AY AS hCY φY hγs_c (fun u _ => (φY _).2)
  have e_s2 := cocInt_w1_cuff hS AS hCs φs (hψ.1.comp_continuousOn hγs_c) hγs_Cs
  have e_t1 := cocInt_w1_cut_cuff hY hS hψ hF AY AS hCY φY hγt_c (fun u _ => (φY _).2)
  have e_t2 := cocInt_w1_cuff hS AS hCt φt (hψ.1.comp_continuousOn hγt_c) hγt_Ct
  have e_a := cocInt_w1_cut_cuff hY hS hψ hF AY AS hCY φY L.cξ (fun u hu => (hmξ u hu) ▸ (φY _).2)
  -- `cocInt (w1 AS) (ψ ∘ ξ) = cocInt (w1 AS) a`:
  have hξ_a : cocInt (w1 AS) (ψ ∘ ξ) = cocInt (w1 AS) a := by
    obtain ⟨N, hN, hcoc⟩ := hcocS
    obtain ⟨n₁, -, hn₁⟩ := cocInt_eq_sum hN hcoc (hψ.1.comp_continuousOn L.cξ)
    obtain ⟨n₂, -, hn₂⟩ := cocInt_eq_sum hN hcoc ha_cont
    set M := max n₁ (max n₂ 1)
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le one_pos ((le_max_right n₂ 1).trans (le_max_right _ _)))
    rw [hn₁ M (le_max_left _ _), hn₂ M ((le_max_left _ _).trans (le_max_right _ _))]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < M := Finset.mem_range.mp hk
    have hI1 : (k : ℝ) / M ∈ Icc (0 : ℝ) 1 := ⟨by positivity, (div_le_one hM0).mpr (by exact_mod_cast hk'.le)⟩
    have hI2 : ((k + 1 : ℕ) : ℝ) / M ∈ Icc (0 : ℝ) 1 := ⟨by positivity, (div_le_one hM0).mpr (by exact_mod_cast hk')⟩
    simp only [comp_apply, L.hξ _ hI1, L.hξ _ hI2]
  rw [hξ_a] at e_a
  -- Apply `cutOrientDiff_cuff` at `y_s = γ_s 0` and `y_t = γ_t 1`:
  have hy_s_eq : γ_s 0 = (φY (ee (m 0 - ε / 2))).1 := by simp [γ_s]
  have hy_t_eq : γ_t 1 = (φY (ee (m 1 + ε / 2))).1 := by simp [γ_t]
  have hcut_s := cutOrientDiff_cuff hY hS hψ hF AY AS hCY hCs φY φs
    (y := (φY (ee (m 0 - ε / 2))).1) (φY _).2 hoff_s
    (u₀ := m 0 - ε / 2) (v₀ := u_s + if σ_s then -(ε / 2) else ε / 2) (δ := ε / 4) (by positivity) σ_s
    (fun r hr => by
      have hr' : r - ε / 2 ∈ Icc (-ε) 0 := ⟨by linarith [hr.1], by linarith [hr.2]⟩
      have h1 : m 0 - ε / 2 + r = m 0 + (r - ε / 2) := by ring
      rw [h1, hmatch_s _ hr']
      congr 3; cases σ_s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ring) rfl
  have hcut_t := cutOrientDiff_cuff hY hS hψ hF AY AS hCY hCt φY φt
    (y := (φY (ee (m 1 + ε / 2))).1) (φY _).2 hoff_t
    (u₀ := m 1 + ε / 2) (v₀ := u_t + if σ_t then ε / 2 else -(ε / 2)) (δ := ε / 4) (by positivity) σ_t
    (fun r hr => by
      have hr' : r + ε / 2 ∈ Icc 0 ε := ⟨by linarith [hr.1], by linarith [hr.2]⟩
      have h1 : m 1 + ε / 2 + r = m 1 + (r + ε / 2) := by ring
      rw [h1, hmatch_t _ hr']
      congr 3; cases σ_t <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ring) rfl
  -- Simplify endpoints `(ψ ∘ γ_s) 1 = s` and `(ψ ∘ γ_t) 0 = t`:
  have hs_end : (ψ ∘ γ_s) 1 = s := by simp only [comp_apply, hγs_1, L.hξ 0 (by simp), ha0]
  have ht_start : (ψ ∘ γ_t) 0 = t := by simp only [comp_apply, hγt_0, L.hξ 1 (by simp), ha1]
  rw [hs_end] at e_s2
  rw [ht_start] at e_t2
  rw [hγs_1] at e_s1
  rw [hγt_0] at e_t1
  -- Combine all 5 `ZMod 2` equations!
  have hcomb : cocInt (w1 AS) a -
      ((cuffSign AS φt t + (if σ_t then 0 else 1)) - (cuffSign AS φs s + (if σ_s then 0 else 1))) = 0 := by
    have h1 := e_s1.symm.trans e_s2
    have h2 := e_t1.symm.trans e_t2
    rw [e_a]
    simp only [comp_apply] at h1 h2
    have h3 : (cuffSign AY φY (ξ 1) + cutOrientDiff AY AS ψ (ξ 1)) -
        (cuffSign AY φY (ξ 0) + cutOrientDiff AY AS ψ (ξ 0)) -
        ((cuffSign AS φt t + (if σ_t then 0 else 1)) - (cuffSign AS φs s + (if σ_s then 0 else 1))) =
        (cuffSign AS φs s - cuffSign AS φs (ψ (γ_s 0)) -
          ((cuffSign AY φY (ξ 0) + cutOrientDiff AY AS ψ (ξ 0)) - (cuffSign AY φY (γ_s 0) + cutOrientDiff AY AS ψ (γ_s 0)))) +
        (cuffSign AS φt (ψ (γ_t 1)) - cuffSign AS φt t -
          ((cuffSign AY φY (γ_t 1) + cutOrientDiff AY AS ψ (γ_t 1)) - (cuffSign AY φY (ξ 1) + cutOrientDiff AY AS ψ (ξ 1)))) +
        (cuffSign AS φs (ψ (γ_s 0)) - cuffSign AY φY (γ_s 0) - (cutOrientDiff AY AS ψ (γ_s 0) + (if σ_s then 0 else 1))) +
        (cuffSign AS φt (ψ (γ_t 1)) - cuffSign AY φY (γ_t 1) - (cutOrientDiff AY AS ψ (γ_t 1) + (if σ_t then 0 else 1))) := by
      simp only [zmod2_sub_eq_add]
      ring_nf
      simp [zmod2_two]
    rw [h3, ← h1, ← h2, hy_s_eq, hy_t_eq, hcut_s, hcut_t]
    simp
  exact sub_eq_zero.mp hcomb

end ArcInvariants

end GraphMinor.GHR18
