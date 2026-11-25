module

public import GraphMinor.GHR18.CutOrientation
public import GraphMinor.Surface.CuffHomeo
public import GraphMinor.Surface.CutParallel

/-!
# Cuff Alignment, Orientation-Preserving Descent, and Global Orientable Flip

Reusable topological infrastructure for `GraphMinor.GHR18.ArcType`:
- `exists_descend_cut_two` & `exists_descend_of_lifts`: descend a fiber-preserving homeomorphism
  `H : Y ≃ₜ Y'` between two cuttings `ψ : Y → S` and `ψ' : Y' → S` along `F, F'` to `α : S ≃ₜ S`
  with `α '' F = F'`.
- `preservesCircleOrientation_of_local_mono`: deduce `PreservesCircleOrientation h` for a circle
  homeomorphism `h : Circle ≃ₜ Circle` from a strictly increasing local lift on one interval.
- `exists_circle_homeo_match_mono`: build an orientation-preserving `h : Circle ≃ₜ Circle` matching
  an arbitrary continuous strictly increasing lift on a closed subinterval `[a, b]` of length `< 1`.
- `cutOrientDiff_cuff_mono` and `cocInt_arc_diff_cuff_mono`: arbitrary-monotone-lift upgrades of
  `cutOrientDiff_cuff` and `cocInt_arc_diff_cuff`.
- `exists_align_one_arc` and `exists_align_two_arcs`: adjust a homeomorphism `Y ≃ₜ Y'` on a single
  cuff of `Y'` via `exists_move_loop` (fixing all other cuffs) to match one or two lifts pointwise.
- `holeParam`: canonical `Circle ≃ₜ holeC a b c f i` agreeing with `holeP a b c f i` on `[0, 1]`.
- `exists_cuff_local_dir`: extract the local direction bit of `ψ` on a boundary point `y ∉ ψ⁻¹(F)`.
- `orient_cut_global_flip`: when `b = 0`, prove that all cuffs of `Y` and `Y'` differ by a single
  global orientation bit `Δ : ZMod 2` across all of `bd S \ {s, t}`.
-/

@[expose] public section

open Set Function Topology Filter Metric GraphMinor.Surface

namespace GraphMinor.GHR18

universe u

/-! ### Descending a homeomorphism between two cuttings -/

section DescendTwo

variable {Y Y' S : Type u} [TopologicalSpace Y] [TopologicalSpace Y'] [TopologicalSpace S]

/-- A homeomorphism `H : Y ≃ₜ Y'` between two cuttings `ψ : Y → S` (along `F`) and `ψ' : Y' → S`
(along `F'`) that preserves fibers in both directions descends to a homeomorphism `α : S ≃ₜ S`
satisfying `α (ψ y) = ψ' (H y)` and `α '' F = F'`. -/
theorem exists_descend_cut_two [CompactSpace Y] [CompactSpace Y'] [T2Space S]
    {ψ : Y → S} {ψ' : Y' → S} {F F' : Set S}
    (hψ : IsCutting ψ F) (hψ' : IsCutting ψ' F')
    (H : Y ≃ₜ Y')
    (hH : ∀ y₁ y₂, ψ y₁ = ψ y₂ → ψ' (H y₁) = ψ' (H y₂))
    (hH' : ∀ y₁ y₂, ψ' y₁ = ψ' y₂ → ψ (H.symm y₁) = ψ (H.symm y₂))
    (hHF : ∀ y, ψ y ∈ F ↔ ψ' (H y) ∈ F') :
    ∃ α : S ≃ₜ S, (∀ y, α (ψ y) = ψ' (H y)) ∧ α '' F = F' := by
  have hq : IsQuotientMap ψ := hψ.1.isClosedMap.isQuotientMap hψ.1 hψ.2.1
  have hq' : IsQuotientMap ψ' := hψ'.1.isClosedMap.isQuotientMap hψ'.1 hψ'.2.1
  let f : S → S := fun x => ψ' (H (surjInv hψ.2.1 x))
  let f' : S → S := fun x => ψ (H.symm (surjInv hψ'.2.1 x))
  have hf_eq : ∀ y, f (ψ y) = ψ' (H y) := fun y =>
    hH _ y (surjInv_eq hψ.2.1 (ψ y))
  have hf'_eq : ∀ y', f' (ψ' y') = ψ (H.symm y') := fun y' =>
    hH' _ y' (surjInv_eq hψ'.2.1 (ψ' y'))
  have hfc : Continuous f := by
    rw [hq.continuous_iff]
    have : f ∘ ψ = ψ' ∘ H := funext hf_eq
    rw [this]; exact hψ'.1.comp H.continuous
  have hf'c : Continuous f' := by
    rw [hq'.continuous_iff]
    have : f' ∘ ψ' = ψ ∘ H.symm := funext hf'_eq
    rw [this]; exact hψ.1.comp H.symm.continuous
  refine ⟨{
    toFun := f
    invFun := f'
    left_inv := fun x => by
      obtain ⟨y, rfl⟩ := hψ.2.1 x
      rw [hf_eq, hf'_eq, H.symm_apply_apply]
    right_inv := fun x => by
      obtain ⟨y', rfl⟩ := hψ'.2.1 x
      rw [hf'_eq, hf_eq, H.apply_symm_apply]
    continuous_toFun := hfc
    continuous_invFun := hf'c }, hf_eq, ?_⟩
  ext x; constructor
  · rintro ⟨w, hwF, rfl⟩
    obtain ⟨y, rfl⟩ := hψ.2.1 w
    change f (ψ y) ∈ F'
    rw [hf_eq]; exact (hHF y).mp hwF
  · intro hxF'
    obtain ⟨y', rfl⟩ := hψ'.2.1 x
    refine ⟨ψ (H.symm y'), ?_, ?_⟩
    · exact (hHF (H.symm y')).mpr (by simpa using hxF')
    · change f (ψ (H.symm y')) = ψ' y'
      rw [hf_eq, H.apply_symm_apply]

/-- Fiber-preservation conditions follow automatically when `H : Y ≃ₜ Y'` maps the two lifts
`(ξ, η)` of `F` onto the two lifts `(ξ', η')` of `F'` with matching parameter `u ∈ [0, 1]`. -/
theorem exists_descend_of_lifts [CompactSpace Y] [CompactSpace Y'] [T2Space S]
    {ψ : Y → S} {ψ' : Y' → S} {F F' : Set S} {s t : S}
    (hψ : IsCutting ψ F) (hψ' : IsCutting ψ' F')
    {a a' : ℝ → S} {ξ η : ℝ → Y} {ξ' η' : ℝ → Y'}
    (L : ArcLift ψ F a ξ η) (L' : ArcLift ψ' F' a' ξ' η')
    {X X' : Set Y} {X₂ X₂' : Set Y'}
    (hP : LiftPair ψ F s t X X') (hP' : LiftPair ψ' F' s t X₂ X₂')
    (himξ : ξ '' Icc 0 1 = X) (himη : η '' Icc 0 1 = X')
    (himξ' : ξ' '' Icc 0 1 = X₂) (himη' : η' '' Icc 0 1 = X₂')
    (H : Y ≃ₜ Y')
    (hHξ : ∀ u ∈ Icc (0 : ℝ) 1, H (ξ u) = ξ' u)
    (hHη : ∀ u ∈ Icc (0 : ℝ) 1, H (η u) = η' u) :
    ∃ α : S ≃ₜ S, (∀ y, α (ψ y) = ψ' (H y)) ∧ α '' F = F' := by
  obtain ⟨_, _, _, _, _, _, _, hun, -⟩ := id hP
  obtain ⟨_, _, _, _, _, _, _, hun', -⟩ := id hP'
  have hHF : ∀ y, ψ y ∈ F ↔ ψ' (H y) ∈ F' := fun y => by
    constructor
    · intro hyF
      have hy : y ∈ X ∪ X' := hun.symm ▸ hyF
      rcases hy with hyX | hyX'
      · obtain ⟨u, hu, rfl⟩ := himξ.symm.subset hyX
        rw [hHξ u hu]; exact show ξ' u ∈ ψ' ⁻¹' F' from hun' ▸ Or.inl (himξ' ▸ ⟨u, hu, rfl⟩)
      · obtain ⟨u, hu, rfl⟩ := himη.symm.subset hyX'
        rw [hHη u hu]; exact show η' u ∈ ψ' ⁻¹' F' from hun' ▸ Or.inr (himη' ▸ ⟨u, hu, rfl⟩)
    · intro hHyF'
      have hHy : H y ∈ X₂ ∪ X₂' := hun'.symm ▸ hHyF'
      rcases hHy with hHy1 | hHy2
      · obtain ⟨u, hu, he⟩ := himξ'.symm.subset hHy1
        have hy_eq : y = ξ u := H.injective (he.symm.trans (hHξ u hu).symm)
        rw [hy_eq]; exact show ξ u ∈ ψ ⁻¹' F from hun ▸ Or.inl (himξ ▸ ⟨u, hu, rfl⟩)
      · obtain ⟨u, hu, he⟩ := himη'.symm.subset hHy2
        have hy_eq : y = η u := H.injective (he.symm.trans (hHη u hu).symm)
        rw [hy_eq]; exact show η u ∈ ψ ⁻¹' F from hun ▸ Or.inr (himη ▸ ⟨u, hu, rfl⟩)
  have hH : ∀ y₁ y₂, ψ y₁ = ψ y₂ → ψ' (H y₁) = ψ' (H y₂) := fun y₁ y₂ he => by
    by_cases h12 : y₁ = y₂
    · rw [h12]
    · obtain ⟨u, hu, hpair⟩ := L.fib y₁ y₂ he h12
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hHξ u hu, hHη u hu, L'.hξ u hu, L'.hη u hu]
      · rw [hHξ u hu, hHη u hu, L'.hξ u hu, L'.hη u hu]
  have hH' : ∀ y₁ y₂, ψ' y₁ = ψ' y₂ → ψ (H.symm y₁) = ψ (H.symm y₂) := fun y₁ y₂ he => by
    by_cases h12 : y₁ = y₂
    · rw [h12]
    · obtain ⟨u, hu, hpair⟩ := L'.fib y₁ y₂ he h12
      have hinvξ : H.symm (ξ' u) = ξ u := H.symm_apply_eq.mpr (hHξ u hu).symm
      have hinvη : H.symm (η' u) = η u := H.symm_apply_eq.mpr (hHη u hu).symm
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hinvξ, hinvη, L.hξ u hu, L.hη u hu]
      · rw [hinvξ, hinvη, L.hξ u hu, L.hη u hu]
  exact exists_descend_cut_two hψ hψ' H hH hH' hHF

end DescendTwo

/-! ### Circle orientation helpers and monotone-lift upgrades -/

section CircleOrient

/-- Composing a cuff parameterization with `k : Circle ≃ₜ Circle` preserves `cuffSign` iff
`PreservesCircleOrientation k`. -/
theorem cuffSign_comp_circle {S : Type u} [TopologicalSpace S] (A : SurfAtlas S)
    {C : Set S} (hC : C ⊆ bd S) (φ : Circle ≃ₜ C) (k : Circle ≃ₜ Circle)
    {x : S} (hxC : x ∈ C) :
    cuffSign A (k.trans φ) x =
      cuffSign A φ x + (open Classical in if PreservesCircleOrientation k then 0 else 1) := by
  classical
  unfold cuffSign cuffSignChart
  have h := cuffPos_comp_circle hC φ k hxC (A.mem_chart x)
  by_cases hp : cuffPos (A.chart (A.idx x)) φ x <;>
  by_cases hk : PreservesCircleOrientation k <;>
  (simp [h, hp, hk]; try rfl)

/-- Composition of orientation-preserving circle homeomorphisms preserves orientation. -/
theorem preservesCircleOrientation_trans {h₁ h₂ : Circle ≃ₜ Circle}
    (h1 : PreservesCircleOrientation h₁) (h2 : PreservesCircleOrientation h₂) :
    PreservesCircleOrientation (h₁.trans h₂) := by
  obtain ⟨l₁, hc₁, hm₁, he₁⟩ := h1
  obtain ⟨l₂, hc₂, hm₂, he₂⟩ := h2
  refine ⟨l₂ ∘ l₁, hc₂.comp hc₁, hm₂.comp hm₁, fun t => ?_⟩
  simp only [Homeomorph.trans_apply, Function.comp_apply, he₁, he₂]

/-- Rotation `Circle.exp (t + c)` preserves circle orientation. -/
theorem preservesCircleOrientation_rot (r : ℝ) :
    ∃ rot : Circle ≃ₜ Circle, PreservesCircleOrientation rot ∧ ∀ u : ℝ, rot (ee u) = ee (u + r) := by
  let c : Circle := ee r
  let rot : Circle ≃ₜ Circle := Homeomorph.mulRight c
  refine ⟨rot, ⟨fun t => t + 2 * Real.pi * r, continuous_id.add continuous_const,
    fun x y hxy => by linarith, fun t => ?_⟩, fun u => ?_⟩
  · show Circle.exp t * Circle.exp (2 * Real.pi * r) = Circle.exp (t + 2 * Real.pi * r)
    exact (Circle.exp_add t (2 * Real.pi * r)).symm
  · show Circle.exp (2 * Real.pi * u) * Circle.exp (2 * Real.pi * r) = Circle.exp (2 * Real.pi * (u + r))
    rw [← Circle.exp_add, mul_add]

/-- A circle homeomorphism `h : Circle ≃ₜ Circle` preserves orientation if it has a continuous
strictly increasing local lift on a non-degenerate closed interval `[t₁, t₂]` of length `< 1`. -/
theorem preservesCircleOrientation_of_local_mono {h : Circle ≃ₜ Circle}
    {t₁ t₂ : ℝ} (hlt : t₁ < t₂) (hspan : t₂ - t₁ < 1) {g : ℝ → ℝ}
    (hgc : ContinuousOn g (Icc t₁ t₂)) (hgm : StrictMonoOn g (Icc t₁ t₂))
    (hge : ∀ t ∈ Icc t₁ t₂, h (ee t) = ee (g t)) :
    PreservesCircleOrientation h := by
  let φid : Circle ≃ₜ (univ : Set Circle) := (Homeomorph.Set.univ Circle).symm
  obtain ⟨m, hmc, hme⟩ := exists_lift φid
    (h.continuous.comp (continuous_ee.comp (continuous_const.add continuous_id))).continuousOn
    (fun _ _ => mem_univ _)
  have hm_ee : ∀ u ∈ Icc (0 : ℝ) 1, ee (m u) = h (ee (t₁ + u)) := fun u hu => by
    simpa [φid] using hme u hu
  have hinj_Ico : InjOn (fun u => ee (m u)) (Ico 0 1) := fun a ha b hb he => by
    dsimp only at he
    have h1 : h (ee (t₁ + a)) = h (ee (t₁ + b)) := by
      rw [← hm_ee a (Ico_subset_Icc_self ha), ← hm_ee b (Ico_subset_Icc_self hb), he]
    have h2 : ee (t₁ + a) = ee (t₁ + b) := h.injective h1
    obtain ⟨k, hk⟩ := ee_eq_iff.mp h2
    have hka : (k : ℝ) = a - b := by linarith
    have hklt : |(k : ℝ)| < 1 := by
      rw [hka, abs_lt]; exact ⟨by linarith [ha.1, hb.2], by linarith [ha.2, hb.1]⟩
    have hk0 : k = 0 := by
      have := abs_lt.mp (show |k| < 1 by exact_mod_cast hklt); omega
    subst hk0; simp only [Int.cast_zero, add_zero] at hk; linarith
  have hne01 : m 0 ≠ m 1 := by
    intro h01
    have hhalf : (1 / 2 : ℝ) ∈ Ico 0 1 := ⟨by norm_num, by norm_num⟩
    have hneq : m (1 / 2) ≠ m 0 := fun he => by
      have := hinj_Ico hhalf ⟨le_rfl, zero_lt_one⟩ (by dsimp only; rw [he])
      norm_num at this
    rcases lt_or_gt_of_ne hneq with hlt' | hgt'
    · let y := (m 0 + m (1 / 2)) / 2
      have h1 : y ∈ Icc (m (1 / 2)) (m 0) := ⟨by dsimp only [y]; linarith, by dsimp only [y]; linarith⟩
      obtain ⟨u₁, hu₁, he₁⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (hmc.mono fun x hx => ⟨hx.1, by linarith [hx.2]⟩) h1
      obtain ⟨u₂, hu₂, he₂⟩ := intermediate_value_Icc (by norm_num : (1 / 2 : ℝ) ≤ 1)
        (hmc.mono fun x hx => ⟨by linarith [hx.1], hx.2⟩) (h01 ▸ h1)
      have hu₁_lt : u₁ < 1 / 2 := lt_of_le_of_ne hu₁.2 fun he => by rw [he] at he₁; dsimp only [y] at he₁; linarith
      have hu₂_gt : 1 / 2 < u₂ := lt_of_le_of_ne hu₂.1 fun he => by rw [← he] at he₂; dsimp only [y] at he₂; linarith
      have hu₂_lt : u₂ < 1 := lt_of_le_of_ne hu₂.2 fun he => by rw [he, ← h01] at he₂; dsimp only [y] at he₂; linarith
      have := hinj_Ico ⟨hu₁.1, by linarith⟩ ⟨by linarith, hu₂_lt⟩ (by dsimp only; rw [he₁, he₂])
      linarith
    · let y := (m 0 + m (1 / 2)) / 2
      have h1 : y ∈ Icc (m 0) (m (1 / 2)) := ⟨by dsimp only [y]; linarith, by dsimp only [y]; linarith⟩
      obtain ⟨u₁, hu₁, he₁⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (hmc.mono fun x hx => ⟨hx.1, by linarith [hx.2]⟩) h1
      obtain ⟨u₂, hu₂, he₂⟩ := intermediate_value_Icc' (by norm_num : (1 / 2 : ℝ) ≤ 1)
        (hmc.mono fun x hx => ⟨by linarith [hx.1], hx.2⟩) (h01 ▸ h1)
      have hu₁_lt : u₁ < 1 / 2 := lt_of_le_of_ne hu₁.2 fun he => by rw [he] at he₁; dsimp only [y] at he₁; linarith
      have hu₂_gt : 1 / 2 < u₂ := lt_of_le_of_ne hu₂.1 fun he => by rw [← he] at he₂; dsimp only [y] at he₂; linarith
      have hu₂_lt : u₂ < 1 := lt_of_le_of_ne hu₂.2 fun he => by rw [he, ← h01] at he₂; dsimp only [y] at he₂; linarith
      have := hinj_Ico ⟨hu₁.1, by linarith⟩ ⟨by linarith, hu₂_lt⟩ (by dsimp only; rw [he₁, he₂])
      linarith
  have hm_inj : InjOn m (Icc 0 1) := fun a ha b hb he => by
    by_cases ha1 : a = 1
    · by_cases hb1 : b = 1
      · rw [ha1, hb1]
      · subst ha1
        have h10 : ee (m 1) = ee (m 0) := by
          rw [hm_ee 1 ⟨zero_le_one, le_rfl⟩, hm_ee 0 ⟨le_rfl, zero_le_one⟩, add_zero, ee_add_one]
        have hb0 : b = 0 := hinj_Ico ⟨hb.1, lt_of_le_of_ne hb.2 hb1⟩ ⟨le_rfl, zero_lt_one⟩ (by dsimp only; rw [← he, h10])
        subst hb0; exact absurd he.symm hne01
    · by_cases hb1 : b = 1
      · subst hb1
        have h10 : ee (m 1) = ee (m 0) := by
          rw [hm_ee 1 ⟨zero_le_one, le_rfl⟩, hm_ee 0 ⟨le_rfl, zero_le_one⟩, add_zero, ee_add_one]
        have ha0 : a = 0 := hinj_Ico ⟨ha.1, lt_of_le_of_ne ha.2 ha1⟩ ⟨le_rfl, zero_lt_one⟩ (by dsimp only; rw [he, h10])
        subst ha0; exact absurd he hne01
      · exact hinj_Ico ⟨ha.1, lt_of_le_of_ne ha.2 ha1⟩ ⟨hb.1, lt_of_le_of_ne hb.2 hb1⟩ (by dsimp only; rw [he])
  have hmo := hmc.strictMonoOn_of_injOn_Icc' zero_le_one hm_inj
  have hsub : Icc (0 : ℝ) (t₂ - t₁) ⊆ Icc 0 1 := fun u hu => ⟨hu.1, by linarith [hu.2]⟩
  have hdiff_int : ∀ u ∈ Icc (0 : ℝ) (t₂ - t₁), ∃ k : ℤ, m u - g (t₁ + u) = k := fun u hu => by
    have h1 : ee (m u) = ee (g (t₁ + u)) := by
      rw [hm_ee u (hsub hu), hge (t₁ + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩]
    obtain ⟨k, hk⟩ := ee_eq_iff.mp h1
    exact ⟨k, by linarith⟩
  have hdiff_c : ContinuousOn (fun u => m u - g (t₁ + u)) (Icc 0 (t₂ - t₁)) :=
    (hmc.mono hsub).sub (hgc.comp (continuous_const.add continuous_id).continuousOn
      fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩)
  have hdiff_const : ∀ u ∈ Icc (0 : ℝ) (t₂ - t₁), m u - g (t₁ + u) = m 0 - g (t₁ + 0) := by
    obtain ⟨k₀, hk₀⟩ := hdiff_int 0 ⟨le_rfl, by linarith⟩
    intro u hu
    by_contra hne
    obtain ⟨k₁, hk₁⟩ := hdiff_int u hu
    have hk_ne : k₁ ≠ k₀ := fun he => hne (by rw [hk₁, hk₀, he])
    rcases lt_or_gt_of_ne hk_ne with hlt_k | hgt_k
    · have hk1 : (k₁ : ℝ) ≤ (k₀ : ℝ) - 1 := by exact_mod_cast Int.le_sub_one_of_lt hlt_k
      obtain ⟨v, hv, hveq⟩ := intermediate_value_Icc' hu.1
        (hdiff_c.mono fun x hx => ⟨hx.1, hx.2.trans hu.2⟩)
        (show (k₀ : ℝ) - 1 / 2 ∈ Icc (m u - g (t₁ + u)) (m 0 - g (t₁ + 0)) by rw [hk₀, hk₁]; exact ⟨by linarith, by linarith⟩)
      obtain ⟨kv, hkv⟩ := hdiff_int v ⟨hv.1, hv.2.trans hu.2⟩
      have : (2 * kv : ℤ) = 2 * k₀ - 1 := by exact_mod_cast (by linarith [hveq, hkv] : (2 : ℝ) * kv = 2 * k₀ - 1)
      omega
    · have hk1 : (k₀ : ℝ) + 1 ≤ (k₁ : ℝ) := by exact_mod_cast Int.add_one_le_of_lt hgt_k
      obtain ⟨v, hv, hveq⟩ := intermediate_value_Icc hu.1
        (hdiff_c.mono fun x hx => ⟨hx.1, hx.2.trans hu.2⟩)
        (show (k₀ : ℝ) + 1 / 2 ∈ Icc (m 0 - g (t₁ + 0)) (m u - g (t₁ + u)) by rw [hk₀, hk₁]; exact ⟨by linarith, by linarith⟩)
      obtain ⟨kv, hkv⟩ := hdiff_int v ⟨hv.1, hv.2.trans hu.2⟩
      have : (2 * kv : ℤ) = 2 * k₀ + 1 := by exact_mod_cast (by linarith [hveq, hkv] : (2 : ℝ) * kv = 2 * k₀ + 1)
      omega
  have hm_mono : StrictMonoOn m (Icc 0 1) := by
    refine hmo.resolve_right fun hanti => ?_
    have h1 := hanti ⟨le_rfl, zero_le_one⟩ (hsub ⟨by linarith, le_rfl⟩) (by linarith)
    have h2 := hdiff_const (t₂ - t₁) ⟨by linarith, le_rfl⟩
    have h3 : g t₁ < g t₂ := hgm ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩ hlt
    have : t₁ + (t₂ - t₁) = t₂ := by ring
    rw [this, add_zero] at h2; linarith
  have hm1_eq : m 1 = m 0 + 1 := by
    have h10 : ee (m 1) = ee (m 0) := by
      rw [hm_ee 1 ⟨zero_le_one, le_rfl⟩, hm_ee 0 ⟨le_rfl, zero_le_one⟩, add_zero, ee_add_one]
    obtain ⟨d, hd⟩ := ee_eq_iff.mp h10
    have hd_pos : 0 < d := by
      have : m 0 < m 1 := hm_mono ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one
      have : (0 : ℝ) < d := by linarith
      exact_mod_cast this
    have hd_le : d ≤ 1 := by
      by_contra hgt
      have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast (by omega : 2 ≤ d)
      obtain ⟨u, hu, hueq⟩ := intermediate_value_Ioo zero_le_one hmc
        (show m 0 + 1 ∈ Ioo (m 0) (m 1) by constructor <;> linarith)
      have hee : ee (m u) = ee (m 0) := by rw [hueq, ee_add_one]
      have := hinj_Ico ⟨hu.1.le, hu.2⟩ ⟨le_rfl, zero_lt_one⟩ hee
      linarith [hu.1]
    have hd1 : d = 1 := by omega
    subst hd1; simp only [Int.cast_one] at hd; linarith
  obtain ⟨H', hH'p, hH'e⟩ := exists_circle_homeo hmc hm_mono hm1_eq
  obtain ⟨rot, hrotp, hrote⟩ := preservesCircleOrientation_rot (-t₁)
  have heq : h = rot.trans H' := by
    ext x
    obtain ⟨u, hu, hu_eq⟩ := exists_param (rot x)
    have hx : x = ee (t₁ + u) :=
      rot.injective (by rw [← hu_eq, hrote (t₁ + u), show t₁ + u + -t₁ = u by ring])
    subst hx
    simp only [Homeomorph.trans_apply, hrote (t₁ + u), show t₁ + u + -t₁ = u by ring,
      hH'e u (Ico_subset_Icc_self hu), hm_ee u (Ico_subset_Icc_self hu)]
  rw [heq]; exact preservesCircleOrientation_trans hrotp hH'p

/-- Build an orientation-preserving circle homeomorphism `k : Circle ≃ₜ Circle` matching any
continuous strictly increasing lift `m` on a closed interval `[a, b]` of length `< 1` whose
image also has length `< 1`. -/
theorem exists_circle_homeo_match_mono {a b : ℝ} (hab : a < b) (hba : b - a < 1)
    {m : ℝ → ℝ} (hmc : ContinuousOn m (Icc a b)) (hmm : StrictMonoOn m (Icc a b))
    (hmspan : m b - m a < 1) :
    ∃ k : Circle ≃ₜ Circle, PreservesCircleOrientation k ∧ ∀ t ∈ Icc a b, k (ee t) = ee (m t) := by
  set d := b - a
  have hd0 : 0 < d := by linarith
  have hd1 : d < 1 := hba
  let τ : ℝ → ℝ := fun u =>
    if u ≤ d then m (a + u) else m b + ((u - d) / (1 - d)) * (m a + 1 - m b)
  have hτ_le : ∀ u, u ≤ d → τ u = m (a + u) := fun u hu => ite_eq_left hu
  have hτ_ge : ∀ u, d ≤ u → τ u = m b + ((u - d) / (1 - d)) * (m a + 1 - m b) := fun u hu => by
    by_cases h : u ≤ d
    · have hde : u = d := le_antisymm h hu
      subst hde; simp [τ, show a + d = b by ring]
    · exact ite_eq_right h
  have hτc : ContinuousOn τ (Icc 0 1) := by
    have h1 : ContinuousOn (fun u => m (a + u)) (Icc 0 d) :=
      hmc.comp (continuous_const.add continuous_id).continuousOn fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have h2 : ContinuousOn (fun u => m b + ((u - d) / (1 - d)) * (m a + 1 - m b)) (Icc d 1) := by fun_prop
    have h1' : ContinuousOn τ (Icc 0 d) := h1.congr fun u hu => hτ_le u hu.2
    have h2' : ContinuousOn τ (Icc d 1) := h2.congr fun u hu => hτ_ge u hu.1
    have hun : Icc (0 : ℝ) d ∪ Icc d 1 = Icc 0 1 := Icc_union_Icc_eq_Icc hd0.le hd1.le
    rw [← hun]
    intro x hx
    rcases lt_trichotomy x d with hlt | rfl | hgt
    · exact (h1' x ⟨hx.elim And.left (fun h => by linarith [h.1]), hlt.le⟩).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (inter_mem_nhdsWithin _ (Iio_mem_nhds hlt)) fun y ⟨hyu, hyl⟩ =>
          ⟨hyu.elim And.left (fun h => by linarith [h.1]), hyl.le⟩)
    · exact (h1' d ⟨hd0.le, le_rfl⟩).union (h2' d ⟨le_rfl, hd1.le⟩)
    · exact (h2' x ⟨hgt.le, hx.elim (fun h => by linarith [h.2]) And.right⟩).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (inter_mem_nhdsWithin _ (Ioi_mem_nhds hgt)) fun y ⟨hyu, hyr⟩ =>
          ⟨hyr.le, hyu.elim (fun h => by linarith [h.2]) And.right⟩)
  have hτm : StrictMonoOn τ (Icc 0 1) := by
    intro x hx y hy hxy
    have hpos : 0 < (m a + 1 - m b) / (1 - d) := div_pos (by linarith) (by linarith)
    by_cases hx' : x ≤ d
    · by_cases hy' : y ≤ d
      · rw [hτ_le x hx', hτ_le y hy']
        exact hmm ⟨by linarith [hx.1], by linarith⟩ ⟨by linarith [hy.1], by linarith⟩ (by linarith)
      · have hylt : d < y := not_le.mp hy'
        rw [hτ_le x hx', hτ_ge y hylt.le]
        have h1 : m (a + x) ≤ m b := by
          rcases eq_or_lt_of_le hx' with rfl | hxl
          · rw [show a + d = b by ring]
          · exact (hmm ⟨by linarith [hx.1], by linarith⟩ ⟨hab.le, le_rfl⟩ (by linarith)).le
        have h2 : 0 < ((y - d) / (1 - d)) * (m a + 1 - m b) :=
          mul_pos (div_pos (by linarith) (by linarith)) (by linarith)
        linarith
    · have hxgt : d < x := not_le.mp hx'
      rw [hτ_ge x hxgt.le, hτ_ge y (by linarith)]
      have h1 : (x - d) / (1 - d) < (y - d) / (1 - d) :=
        div_lt_div_of_pos_right (by linarith) (by linarith)
      have h2 := mul_lt_mul_of_pos_right h1 (by linarith : 0 < m a + 1 - m b)
      linarith
  have hτ1 : τ 1 = τ 0 + 1 := by
    rw [hτ_ge 1 hd1.le, hτ_le 0 hd0.le, add_zero, div_self (by linarith : (1 - d : ℝ) ≠ 0), one_mul]
    ring
  obtain ⟨H', hH'p, hH'e⟩ := exists_circle_homeo hτc hτm hτ1
  obtain ⟨rot, hrotp, hrote⟩ := preservesCircleOrientation_rot (-a)
  refine ⟨rot.trans H', preservesCircleOrientation_trans hrotp hH'p, fun t ht => ?_⟩
  have htd : t - a ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  simp only [Homeomorph.trans_apply, hrote t, show t + -a = t - a by ring, hH'e (t - a) htd]
  rw [hτ_le (t - a) (by linarith [ht.2]), show a + (t - a) = t by ring]

/-- Upgrade of `cutOrientDiff_cuff` allowing an arbitrary continuous strictly-monotone local lift `m`
instead of a unit-speed linear lift. -/
theorem cutOrientDiff_cuff_mono {Y S : Type u} [TopologicalSpace Y] [TopologicalSpace S]
    (hY : IsSurface Y) (hS : IsSurface S) {ψ : Y → S} {F : Set S}
    (hψ : IsCutting ψ F) (hF : IsClosed F) (AY : SurfAtlas Y) (AS : SurfAtlas S)
    {CY : Set Y} {CS : Set S} (hCY : CY ⊆ bd Y) (hCS : CS ⊆ bd S)
    (φY : Circle ≃ₜ CY) (φS : Circle ≃ₜ CS) {y : Y} (hyC : y ∈ CY) (hyF : ψ y ∉ F)
    {u₀ δ : ℝ} (hδ : 0 < δ) (hsgn : Bool) {m : ℝ → ℝ}
    (hmc : ContinuousOn m (Icc (-δ) δ))
    (hmm : if hsgn then StrictMonoOn m (Icc (-δ) δ) else StrictAntiOn m (Icc (-δ) δ))
    (hmatch : ∀ t ∈ Icc (-δ) δ, ψ (φY (ee (u₀ + t))).1 = (φS (ee (m t))).1)
    (hy0 : (φY (ee u₀)).1 = y) :
    cuffSign AS φS (ψ y) - cuffSign AY φY y =
      cutOrientDiff AY AS ψ y + (if hsgn then 0 else 1) := by
  have hm_at : ContinuousAt m 0 := hmc.continuousAt (Icc_mem_nhds (by linarith) hδ)
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.continuousAt_iff.mp hm_at (1 / 4) (by norm_num)
  set δ' := min (δ / 2) (min (ρ / 2) (1 / 8))
  have hδ' : 0 < δ' := lt_min (half_pos hδ) (lt_min (half_pos hρ) (by norm_num))
  have hδ'δ : δ' ≤ δ := (min_le_left _ _).trans (by linarith)
  have hδ'ρ : δ' < ρ := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (half_lt_self hρ)
  have hδ'4 : δ' < 1 / 4 := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (by norm_num)
  have hsub : Icc (-δ') δ' ⊆ Icc (-δ) δ := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hdist : ∀ t ∈ Icc (-δ') δ', |m t - m 0| < 1 / 4 := fun t ht => by
    have := hρsub (x := t) (by rw [Real.dist_eq, sub_zero, abs_lt]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    simpa [Real.dist_eq] using this
  let g : ℝ → ℝ := fun t => if hsgn then m t else m (-t)
  have hgc : ContinuousOn g (Icc (-δ') δ') := by
    cases hsgn
    · simp only [g, Bool.false_eq_true, ↓reduceIte]
      exact (hmc.mono hsub).comp continuous_neg.continuousOn fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩
    · simp only [g, ↓reduceIte]; exact hmc.mono hsub
  have hgm : StrictMonoOn g (Icc (-δ') δ') := by
    cases hsgn
    · simp only [g, Bool.false_eq_true, ↓reduceIte] at hmm ⊢
      intro a ha b hb hab
      exact hmm (hsub ⟨by linarith [hb.2], by linarith [hb.1]⟩)
        (hsub ⟨by linarith [ha.2], by linarith [ha.1]⟩) (by linarith)
    · simp only [g, ↓reduceIte] at hmm ⊢
      exact hmm.mono hsub
  have hgspan : g δ' - g (-δ') < 1 := by
    have h1 := (abs_lt.mp (hdist δ' ⟨by linarith, le_rfl⟩)).2
    have h2 := (abs_lt.mp (hdist (-δ') ⟨le_rfl, by linarith⟩)).1
    have h3 := (abs_lt.mp (hdist δ' ⟨by linarith, le_rfl⟩)).1
    have h4 := (abs_lt.mp (hdist (-δ') ⟨le_rfl, by linarith⟩)).2
    cases hsgn <;> simp only [g, Bool.false_eq_true, ↓reduceIte, neg_neg] <;> linarith
  obtain ⟨k, hkp, hke⟩ := exists_circle_homeo_match_mono (by linarith : -δ' < δ') (by linarith : δ' - -δ' < 1) hgc hgm hgspan
  have hmatch' : ∀ t ∈ Icc (-δ') δ', ψ (φY (ee (u₀ + t))).1 = ((k.trans φS) (ee (0 + if hsgn then t else -t))).1 := fun t ht => by
    rw [hmatch t (hsub ht)]
    simp only [Homeomorph.trans_apply, zero_add]
    cases hsgn
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hke (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩]; simp [g]
    · simp only [↓reduceIte]
      rw [hke t ht]; simp [g]
  have hψyC : ψ y ∈ CS := by
    have h0 := hmatch 0 ⟨by linarith, hδ.le⟩
    rw [add_zero, hy0] at h0; rw [h0]; exact (φS _).2
  have hres := cutOrientDiff_cuff hY hS hψ hF AY AS hCY hCS φY (k.trans φS) hyC hyF hδ' hsgn hmatch' hy0
  rw [cuffSign_comp_circle AS hCS φS k hψyC, ite_eq_left hkp, add_zero] at hres
  exact hres

/-- Upgrade of `cocInt_arc_diff_cuff` allowing arbitrary continuous strictly-monotone local lifts
`m_s` on `[-ε, 0]` and `m_t` on `[0, ε]` instead of unit-speed linear lifts. -/
theorem cocInt_arc_diff_cuff_mono {Y S : Type u} [TopologicalSpace Y] [TopologicalSpace S]
    (hY : IsSurface Y) (hS : IsSurface S) [T2Space Y]
    {ψ : Y → S} {F : Set S} {s t : S} (hψ : IsCutting ψ F) (hF : IsClosed F)
    {a : ℝ → S} {ξ η : ℝ → Y} (L : ArcLift ψ F a ξ η) (ha0 : a 0 = s) (ha1 : a 1 = t)
    (AY : SurfAtlas Y) (AS : SurfAtlas S)
    {C_Y : Set Y} (hCY : C_Y ⊆ bd Y) (φY : Circle ≃ₜ C_Y)
    {C_s C_t : Set S} (hCs : C_s ⊆ bd S) (hCt : C_t ⊆ bd S)
    (φs : Circle ≃ₜ C_s) (φt : Circle ≃ₜ C_t)
    {m : ℝ → ℝ} (hmc : ContinuousOn m (Icc 0 1)) (hmξ : ∀ u ∈ Icc (0 : ℝ) 1, (φY (ee (m u))).1 = ξ u)
    {ε : ℝ} (hε : 0 < ε) (σ_s σ_t : Bool) {m_s m_t : ℝ → ℝ}
    (hms_c : ContinuousOn m_s (Icc (-ε) 0)) (hmt_c : ContinuousOn m_t (Icc 0 ε))
    (hms_m : if σ_s then StrictMonoOn m_s (Icc (-ε) 0) else StrictAntiOn m_s (Icc (-ε) 0))
    (hmt_m : if σ_t then StrictMonoOn m_t (Icc 0 ε) else StrictAntiOn m_t (Icc 0 ε))
    (hmatch_s : ∀ r ∈ Icc (-ε) 0, ψ (φY (ee (m 0 + r))).1 = (φs (ee (m_s r))).1)
    (hmatch_t : ∀ r ∈ Icc 0 ε, ψ (φY (ee (m 1 + r))).1 = (φt (ee (m_t r))).1)
    (hoff_s : ∀ r ∈ Ico (-ε) 0, ψ (φY (ee (m 0 + r))).1 ∉ F)
    (hoff_t : ∀ r ∈ Ioc 0 ε, ψ (φY (ee (m 1 + r))).1 ∉ F) :
    cocInt (w1 AS) a =
      (cuffSign AS φt t + (if σ_t then 0 else 1)) -
      (cuffSign AS φs s + (if σ_s then 0 else 1)) := by
  have hs_at : ContinuousWithinAt m_s (Icc (-ε) 0) 0 := hms_c 0 ⟨by linarith, le_rfl⟩
  have ht_at : ContinuousWithinAt m_t (Icc 0 ε) 0 := hmt_c 0 ⟨le_rfl, hε.le⟩
  obtain ⟨ρs, hρs, hρs_sub⟩ := Metric.continuousWithinAt_iff.mp hs_at (1 / 4) (by norm_num)
  obtain ⟨ρt, hρt, hρt_sub⟩ := Metric.continuousWithinAt_iff.mp ht_at (1 / 4) (by norm_num)
  set ε' := min (ε / 2) (min (ρs / 2) (min (ρt / 2) (1 / 8)))
  have hε' : 0 < ε' := lt_min (half_pos hε) (lt_min (half_pos hρs) (lt_min (half_pos hρt) (by norm_num)))
  have hε'ε : ε' ≤ ε := (min_le_left _ _).trans (by linarith)
  have hε'ρs : ε' < ρs := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (half_lt_self hρs)
  have hε'ρt : ε' < ρt := lt_of_le_of_lt ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))) (half_lt_self hρt)
  have hε'4 : ε' < 1 / 4 := lt_of_le_of_lt ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))) (by norm_num)
  have hsub_s : Icc (-ε') 0 ⊆ Icc (-ε) 0 := fun r hr => ⟨by linarith [hr.1], hr.2⟩
  have hsub_t : Icc 0 ε' ⊆ Icc 0 ε := fun r hr => ⟨hr.1, by linarith [hr.2]⟩
  have hds : |m_s (-ε') - m_s 0| < 1 / 4 := by
    have := hρs_sub (x := -ε') (hsub_s ⟨le_rfl, by linarith⟩) (by rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos hε']; exact hε'ρs)
    simpa [Real.dist_eq] using this
  have hdt : |m_t ε' - m_t 0| < 1 / 4 := by
    have := hρt_sub (x := ε') (hsub_t ⟨hε'.le, le_rfl⟩) (by rw [Real.dist_eq, sub_zero, abs_of_pos hε']; exact hε'ρt)
    simpa [Real.dist_eq] using this
  -- Build orientation-preserving `k_s : Circle ≃ₜ Circle` matching `m_s` on `[-ε', 0]` (or `[0, ε']` if `!σ_s`):
  have hex_ks : ∃ k_s : Circle ≃ₜ Circle, PreservesCircleOrientation k_s ∧
      ∀ r ∈ Icc (-ε') 0, k_s (ee (0 + if σ_s then r else -r)) = ee (m_s r) := by
    cases σ_s
    · simp only [Bool.false_eq_true, ↓reduceIte, zero_add] at hms_m ⊢
      obtain ⟨k, hkp, hke⟩ := exists_circle_homeo_match_mono hε' (by linarith : ε' - 0 < 1)
        (m := fun x => m_s (-x))
        ((hms_c.mono hsub_s).comp continuous_neg.continuousOn fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩)
        (fun a ha b hb hab => hms_m (hsub_s ⟨by linarith [hb.2], by linarith [hb.1]⟩)
          (hsub_s ⟨by linarith [ha.2], by linarith [ha.1]⟩) (by linarith))
        (by simp only [neg_zero]; linarith [(abs_lt.mp hds).2])
      exact ⟨k, hkp, fun r hr => by simpa using hke (-r) ⟨by linarith [hr.2], by linarith [hr.1]⟩⟩
    · simp only [↓reduceIte, zero_add] at hms_m ⊢
      obtain ⟨k, hkp, hke⟩ := exists_circle_homeo_match_mono (by linarith : -ε' < 0) (by linarith : 0 - -ε' < 1)
        (hms_c.mono hsub_s) (hms_m.mono hsub_s) (by linarith [(abs_lt.mp hds).1])
      exact ⟨k, hkp, hke⟩
  have hex_kt : ∃ k_t : Circle ≃ₜ Circle, PreservesCircleOrientation k_t ∧
      ∀ r ∈ Icc 0 ε', k_t (ee (0 + if σ_t then r else -r)) = ee (m_t r) := by
    cases σ_t
    · simp only [Bool.false_eq_true, ↓reduceIte, zero_add] at hmt_m ⊢
      obtain ⟨k, hkp, hke⟩ := exists_circle_homeo_match_mono (by linarith : -ε' < 0) (by linarith : 0 - -ε' < 1)
        (m := fun x => m_t (-x))
        ((hmt_c.mono hsub_t).comp continuous_neg.continuousOn fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩)
        (fun a ha b hb hab => hmt_m (hsub_t ⟨by linarith [hb.2], by linarith [hb.1]⟩)
          (hsub_t ⟨by linarith [ha.2], by linarith [ha.1]⟩) (by linarith))
        (by simp only [neg_zero, neg_neg]; linarith [(abs_lt.mp hdt).1])
      exact ⟨k, hkp, fun r hr => by simpa using hke (-r) ⟨by linarith [hr.2], by linarith [hr.1]⟩⟩
    · simp only [↓reduceIte, zero_add] at hmt_m ⊢
      obtain ⟨k, hkp, hke⟩ := exists_circle_homeo_match_mono hε' (by linarith : ε' - 0 < 1)
        (hmt_c.mono hsub_t) (hmt_m.mono hsub_t) (by linarith [(abs_lt.mp hdt).2])
      exact ⟨k, hkp, hke⟩
  obtain ⟨k_s, hks_p, hks_e⟩ := hex_ks
  obtain ⟨k_t, hkt_p, hkt_e⟩ := hex_kt
  have hsC : s ∈ C_s := by
    have h0 := hmatch_s 0 ⟨by linarith, le_rfl⟩
    rw [add_zero, hmξ 0 ⟨le_rfl, zero_le_one⟩, L.hξ 0 ⟨le_rfl, zero_le_one⟩, ha0] at h0
    rw [h0]; exact (φs _).2
  have htC : t ∈ C_t := by
    have h0 := hmatch_t 0 ⟨le_rfl, hε.le⟩
    rw [add_zero, hmξ 1 ⟨zero_le_one, le_rfl⟩, L.hξ 1 ⟨zero_le_one, le_rfl⟩, ha1] at h0
    rw [h0]; exact (φt _).2
  have hres := cocInt_arc_diff_cuff hY hS hψ hF L ha0 ha1 AY AS hCY φY hCs hCt (k_s.trans φs) (k_t.trans φt)
    hmc hmξ hε' σ_s σ_t (u_s := 0) (u_t := 0)
    (fun r hr => by rw [hmatch_s r (hsub_s hr)]; simp only [Homeomorph.trans_apply, hks_e r hr])
    (fun r hr => by rw [hmatch_t r (hsub_t hr)]; simp only [Homeomorph.trans_apply, hkt_e r hr])
    (by
      have := hoff_s (-(ε' / 2)) ⟨by linarith, by linarith⟩
      simpa [sub_eq_add_neg] using this)
    (hoff_t (ε' / 2) ⟨by linarith, by linarith⟩)
  rw [cuffSign_comp_circle AS hCs φs k_s hsC, ite_eq_left hks_p, add_zero,
      cuffSign_comp_circle AS hCt φt k_t htC, ite_eq_left hkt_p, add_zero] at hres
  exact hres

end CircleOrient

/-! ### Aligning one or two arcs on a single cuff via `exists_move_loop` -/

section AlignCuff

variable {Y : Type u} [TopologicalSpace Y]

/-- Continuous strictly increasing inverse of a continuous strictly increasing map `p` on `[0, 1]`. -/
theorem exists_inv_strictMonoOn {p : ℝ → ℝ} (hpc : ContinuousOn p (Icc 0 1))
    (hpm : StrictMonoOn p (Icc 0 1)) :
    ∃ p_inv : ℝ → ℝ, ContinuousOn p_inv (Icc (p 0) (p 1)) ∧ StrictMonoOn p_inv (Icc (p 0) (p 1)) ∧
      (∀ u ∈ Icc (0 : ℝ) 1, p_inv (p u) = u) ∧ (∀ y ∈ Icc (p 0) (p 1), p (p_inv y) = y) := by
  have hex : ∀ y ∈ Icc (p 0) (p 1), ∃ u ∈ Icc (0 : ℝ) 1, p u = y := fun y hy =>
    intermediate_value_Icc zero_le_one hpc hy
  choose! p_inv hp_mem hp_eq using hex
  have hleft : ∀ u ∈ Icc (0 : ℝ) 1, p_inv (p u) = u := fun u hu =>
    hpm.injOn (hp_mem (p u) ⟨hpm.monotoneOn ⟨le_rfl, zero_le_one⟩ hu hu.1,
      hpm.monotoneOn hu ⟨zero_le_one, le_rfl⟩ hu.2⟩) hu
      (hp_eq (p u) ⟨hpm.monotoneOn ⟨le_rfl, zero_le_one⟩ hu hu.1,
        hpm.monotoneOn hu ⟨zero_le_one, le_rfl⟩ hu.2⟩)
  have hmono : StrictMonoOn p_inv (Icc (p 0) (p 1)) := fun y₁ hy₁ y₂ hy₂ hlt => by
    by_contra hge
    rcases eq_or_lt_of_le (not_lt.mp hge) with he | hgt
    · have := (hp_eq y₁ hy₁).symm.trans ((congrArg p he.symm).trans (hp_eq y₂ hy₂))
      linarith
    · have := hpm (hp_mem y₂ hy₂) (hp_mem y₁ hy₁) hgt
      rw [hp_eq y₁ hy₁, hp_eq y₂ hy₂] at this; linarith
  have hcont : ContinuousOn p_inv (Icc (p 0) (p 1)) := by
    let f : Icc (0 : ℝ) 1 → ℝ := fun u => p u.1
    have hfc : Continuous f := continuousOn_iff_continuous_domRestrict.mp hpc
    have hfi : Injective f := fun u v he => Subtype.ext (hpm.injOn u.2 v.2 he)
    let e := (hfc.isClosedEmbedding hfi).isEmbedding.toHomeomorph
    have heq : ∀ (y : ℝ) (hy : y ∈ Icc (p 0) (p 1)),
        p_inv y = (e.symm ⟨y, ⟨⟨p_inv y, hp_mem y hy⟩, hp_eq y hy⟩⟩).1 := fun y hy => by
      have h1 : e ⟨p_inv y, hp_mem y hy⟩ = ⟨y, ⟨⟨p_inv y, hp_mem y hy⟩, hp_eq y hy⟩⟩ := Subtype.ext (hp_eq y hy)
      rw [← h1, e.symm_apply_apply]
    have hcs : Continuous (fun y : Icc (p 0) (p 1) =>
        (e.symm ⟨y.1, ⟨⟨p_inv y.1, hp_mem y.1 y.2⟩, hp_eq y.1 y.2⟩⟩).1) :=
      continuous_subtype_val.comp (e.symm.continuous.comp (Continuous.subtype_mk continuous_subtype_val _))
    rw [continuousOn_iff_continuous_domRestrict]
    exact hcs.congr fun ⟨y, hy⟩ => (heq y hy).symm
  exact ⟨p_inv, hcont, hmono, hleft, hp_eq⟩

/-- Open neighborhood of a cuff `C` of a surface `Y` that is disjoint from all other cuffs of `Y`. -/
theorem exists_cuff_open_disj (hY : IsSurface Y) {C : Set Y} (hC : C ∈ cuffs Y) :
    ∃ U : Set Y, IsOpen U ∧ C ⊆ U ∧ ∀ D ∈ cuffs Y, D ≠ C → Disjoint U D := by
  have : T2Space Y := hY.2.1
  have hcf := cuff_statement.{u} Y hY
  let K : Set Y := ⋃₀ (cuffs Y \ {C})
  have hK_closed : IsClosed K := by
    have hfin : (cuffs Y \ {C}).Finite := hcf.2.1.sdiff
    exact hfin.isClosed_sUnion fun D hD => (hcf.2.2 D hD.1).isCompact.isClosed
  refine ⟨Kᶜ, hK_closed.isOpen_compl, ?_, fun D hD hne => ?_⟩
  · intro y hy hyK
    obtain ⟨D, ⟨hDc, hDne⟩, hyD⟩ := hyK
    exact Set.disjoint_left.mp (cuffs_disjoint hC hDc (Ne.symm hDne)) hy hyD
  · exact disjoint_compl_left.mono_right (subset_sUnion_of_mem (show D ∈ cuffs Y \ {C} from ⟨hD, hne⟩))

/-- Move one strictly-increasing arc `p` on cuff `C` onto another strictly-increasing arc `q` on `C`
via a homeomorphism `M : Y ≃ₜ Y` that fixes all other cuffs pointwise and preserves orientation on `C`. -/
theorem exists_align_one_arc (hY : IsSurface Y) {C : Set Y} (hC : C ∈ cuffs Y) (φ : Circle ≃ₜ C)
    {p q : ℝ → ℝ} (hpc : ContinuousOn p (Icc 0 1)) (hpm : StrictMonoOn p (Icc 0 1))
    (hqc : ContinuousOn q (Icc 0 1)) (hqm : StrictMonoOn q (Icc 0 1))
    (hp1 : p 1 < p 0 + 1) (hq1 : q 1 < q 0 + 1) :
    ∃ M : Y ≃ₜ Y,
      (∀ u ∈ Icc (0 : ℝ) 1, M (φ (ee (p u))).1 = (φ (ee (q u))).1) ∧
      (∀ D ∈ cuffs Y, D ≠ C → ∀ y ∈ D, M y = y) ∧
      (∃ k : Circle ≃ₜ Circle, PreservesCircleOrientation k ∧ ∀ x, M (φ x).1 = (φ (k x)).1) := by
  obtain ⟨U, hUo, hCU, hUdisj⟩ := exists_cuff_open_disj hY hC
  obtain ⟨rot, hrotp, hrote⟩ := preservesCircleOrientation_rot (p 0)
  let φ₀ : Circle ≃ₜ C := rot.trans φ
  have hφ₀_e : ∀ r : ℝ, (φ₀ (ee r)).1 = (φ (ee (r + p 0))).1 := fun r => by
    simp only [φ₀, Homeomorph.trans_apply, hrote]
  let p₀ : ℝ → ℝ := fun u => p u - p 0
  have hp₀c : ContinuousOn p₀ (Icc 0 1) := hpc.sub continuousOn_const
  have hp₀m : StrictMonoOn p₀ (Icc 0 1) := fun a ha b hb h => sub_lt_sub_right (hpm ha hb h) (p 0)
  have hp₀0 : p₀ 0 = 0 := sub_self (p 0)
  have hp₀1_pos : 0 < p₀ 1 := hp₀0 ▸ hp₀m ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one
  have hp₀1_lt : p₀ 1 < 1 := by simp only [p₀]; linarith
  obtain ⟨pinv, hpinv_c, hpinv_m, hpinv_l, hpinv_r⟩ := exists_inv_strictMonoOn hp₀c hp₀m
  set d := p₀ 1
  let τ : ℝ → ℝ := fun t =>
    if t ≤ d then q (pinv t) - p 0
    else (q 1 - p 0) + ((t - d) / (1 - d)) * (q 0 + 1 - q 1)
  have hτ_le : ∀ t, t ≤ d → τ t = q (pinv t) - p 0 := fun t ht => ite_eq_left ht
  have hτ_ge : ∀ t, d ≤ t → τ t = (q 1 - p 0) + ((t - d) / (1 - d)) * (q 0 + 1 - q 1) := fun t ht => by
    by_cases h : t ≤ d
    · have hte : t = d := le_antisymm h ht
      subst hte
      have hp1_inv : pinv d = 1 := hpinv_l 1 ⟨zero_le_one, le_rfl⟩
      simp [τ, hp1_inv]
    · exact ite_eq_right h
  have hpinv_maps : MapsTo pinv (Icc 0 d) (Icc 0 1) := fun t ht => by
    have ht' : t ∈ Icc (p₀ 0) (p₀ 1) := by rw [hp₀0]; exact ht
    have h0 := hpinv_m.monotoneOn (by rw [hp₀0]; exact ⟨le_rfl, hp₀1_pos.le⟩) ht' (show p₀ 0 ≤ t by rw [hp₀0]; exact ht.1)
    have h1 := hpinv_m.monotoneOn ht' (by rw [hp₀0]; exact ⟨hp₀1_pos.le, le_rfl⟩) ht.2
    have h0' : pinv (p₀ 0) = 0 := hpinv_l 0 ⟨le_rfl, zero_le_one⟩
    have h1' : pinv (p₀ 1) = 1 := hpinv_l 1 ⟨zero_le_one, le_rfl⟩
    rw [h0'] at h0; rw [h1'] at h1
    exact ⟨h0, h1⟩
  have hτc : ContinuousOn τ (Icc 0 1) := by
    have h1 : ContinuousOn τ (Icc 0 d) :=
      ((hqc.comp (by rw [← hp₀0]; exact hpinv_c) hpinv_maps).sub continuousOn_const).congr fun t ht => hτ_le t ht.2
    have h2 : ContinuousOn τ (Icc d 1) :=
      (by fun_prop : ContinuousOn (fun t => (q 1 - p 0) + ((t - d) / (1 - d)) * (q 0 + 1 - q 1)) (Icc d 1)).congr
        fun t ht => hτ_ge t ht.1
    rw [← Icc_union_Icc_eq_Icc hp₀1_pos.le hp₀1_lt.le]
    intro x hx
    rcases lt_trichotomy x d with hlt | rfl | hgt
    · exact (h1 x ⟨hx.elim And.left (fun h => by linarith [h.1]), hlt.le⟩).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (inter_mem_nhdsWithin _ (Iio_mem_nhds hlt)) fun y ⟨hyu, hyl⟩ =>
          ⟨hyu.elim And.left (fun h => by linarith [h.1]), hyl.le⟩)
    · exact (h1 d ⟨hp₀1_pos.le, le_rfl⟩).union (h2 d ⟨le_rfl, hp₀1_lt.le⟩)
    · exact (h2 x ⟨hgt.le, hx.elim (fun h => by linarith [h.2]) And.right⟩).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (inter_mem_nhdsWithin _ (Ioi_mem_nhds hgt)) fun y ⟨hyu, hyr⟩ =>
          ⟨hyr.le, hyu.elim (fun h => by linarith [h.2]) And.right⟩)
  have hτm : StrictMonoOn τ (Icc 0 1) := by
    intro x hx y hy hxy
    by_cases hx' : x ≤ d
    · by_cases hy' : y ≤ d
      · rw [hτ_le x hx', hτ_le y hy']
        have hxI : x ∈ Icc (p₀ 0) (p₀ 1) := by rw [hp₀0]; exact ⟨hx.1, hx'⟩
        have hyI : y ∈ Icc (p₀ 0) (p₀ 1) := by rw [hp₀0]; exact ⟨hy.1, hy'⟩
        exact sub_lt_sub_right (hqm (hpinv_maps ⟨hx.1, hx'⟩) (hpinv_maps ⟨hy.1, hy'⟩) (hpinv_m hxI hyI hxy)) (p 0)
      · have hylt : d < y := not_le.mp hy'
        rw [hτ_le x hx', hτ_ge y hylt.le]
        have h1 : q (pinv x) ≤ q 1 := hqm.monotoneOn (hpinv_maps ⟨hx.1, hx'⟩) ⟨zero_le_one, le_rfl⟩ (hpinv_maps ⟨hx.1, hx'⟩).2
        have h2 : 0 < ((y - d) / (1 - d)) * (q 0 + 1 - q 1) :=
          mul_pos (div_pos (by linarith) (by linarith)) (by linarith)
        linarith
    · have hxgt : d < x := not_le.mp hx'
      rw [hτ_ge x hxgt.le, hτ_ge y (by linarith)]
      have h1 : (x - d) / (1 - d) < (y - d) / (1 - d) := div_lt_div_of_pos_right (by linarith) (by linarith)
      linarith [mul_lt_mul_of_pos_right h1 (by linarith : 0 < q 0 + 1 - q 1)]
  have hτ1 : τ 1 = τ 0 + 1 := by
    have hp0_inv : pinv 0 = 0 := by have := hpinv_l 0 ⟨le_rfl, zero_le_one⟩; rwa [hp₀0] at this
    rw [hτ_ge 1 hp₀1_lt.le, hτ_le 0 hp₀1_pos.le, hp0_inv,
      div_self (by linarith : (1 - d : ℝ) ≠ 0), one_mul]
    ring
  obtain ⟨h, hhp, hhe⟩ := exists_circle_homeo hτc hτm hτ1
  obtain ⟨M, hMφ₀, hMoff⟩ := move_cuff Y C U φ₀ h hY hC hUo hCU hhp
  refine ⟨M, fun u hu => ?_, fun D hD hne y hyD => hMoff y (Set.disjoint_right.mp (hUdisj D hD hne) hyD), ?_⟩
  · have hp₀u : p₀ u ∈ Icc (0 : ℝ) d :=
      ⟨hp₀0 ▸ hp₀m.monotoneOn ⟨le_rfl, zero_le_one⟩ hu hu.1, hp₀m.monotoneOn hu ⟨zero_le_one, le_rfl⟩ hu.2⟩
    have h1 : (φ (ee (p u))).1 = (φ₀ (ee (p₀ u))).1 := by
      rw [hφ₀_e (p₀ u), show p₀ u + p 0 = p u by simp [p₀]]
    rw [h1, hMφ₀ (ee (p₀ u)), hhe (p₀ u) ⟨hp₀u.1, hp₀u.2.trans hp₀1_lt.le⟩, hφ₀_e, hτ_le (p₀ u) hp₀u.2,
      hpinv_l u hu, show q u - p 0 + p 0 = q u by ring]
  · obtain ⟨rot_inv, hrip, hrie⟩ := preservesCircleOrientation_rot (-p 0)
    have hinv_eq : rot.symm = rot_inv := Homeomorph.ext fun x => by
      obtain ⟨u, -, rfl⟩ := exists_param x
      apply rot.injective; rw [rot.apply_symm_apply, hrie u, hrote (u + -p 0), show u + -p 0 + p 0 = u by ring]
    refine ⟨rot_inv.trans (h.trans rot),
      preservesCircleOrientation_trans hrip (preservesCircleOrientation_trans hhp hrotp), fun x => ?_⟩
    have h2 : (φ x).1 = (φ₀ (rot_inv x)).1 := by
      rw [← hinv_eq]; simp [φ₀]
    rw [h2, hMφ₀ (rot_inv x)]
    rfl

/-- Move two disjoint strictly-increasing arcs `(p₁, p₂)` on cuff `C` onto two disjoint
strictly-increasing arcs `(q₁, q₂)` in the same cyclic order on `C`, via a homeomorphism
`M : Y ≃ₜ Y` fixing all other cuffs pointwise and preserving orientation on `C`. -/
theorem exists_align_two_arcs (hY : IsSurface Y) {C : Set Y} (hC : C ∈ cuffs Y) (φ : Circle ≃ₜ C)
    {p₁ p₂ q₁ q₂ : ℝ → ℝ}
    (hp₁c : ContinuousOn p₁ (Icc 0 1)) (hp₁m : StrictMonoOn p₁ (Icc 0 1))
    (hp₂c : ContinuousOn p₂ (Icc 0 1)) (hp₂m : StrictMonoOn p₂ (Icc 0 1))
    (hq₁c : ContinuousOn q₁ (Icc 0 1)) (hq₁m : StrictMonoOn q₁ (Icc 0 1))
    (hq₂c : ContinuousOn q₂ (Icc 0 1)) (hq₂m : StrictMonoOn q₂ (Icc 0 1))
    (hp_ord1 : p₁ 1 < p₂ 0) (hp_ord2 : p₂ 1 < p₁ 0 + 1)
    (hq_ord1 : q₁ 1 < q₂ 0) (hq_ord2 : q₂ 1 < q₁ 0 + 1) :
    ∃ M : Y ≃ₜ Y,
      (∀ u ∈ Icc (0 : ℝ) 1, M (φ (ee (p₁ u))).1 = (φ (ee (q₁ u))).1) ∧
      (∀ u ∈ Icc (0 : ℝ) 1, M (φ (ee (p₂ u))).1 = (φ (ee (q₂ u))).1) ∧
      (∀ D ∈ cuffs Y, D ≠ C → ∀ y ∈ D, M y = y) ∧
      (∃ k : Circle ≃ₜ Circle, PreservesCircleOrientation k ∧ ∀ x, M (φ x).1 = (φ (k x)).1) := by
  obtain ⟨U, hUo, hCU, hUdisj⟩ := exists_cuff_open_disj hY hC
  obtain ⟨rot, hrotp, hrote⟩ := preservesCircleOrientation_rot (p₁ 0)
  let φ₀ : Circle ≃ₜ C := rot.trans φ
  have hφ₀_e : ∀ r : ℝ, (φ₀ (ee r)).1 = (φ (ee (r + p₁ 0))).1 := fun r => by
    simp only [φ₀, Homeomorph.trans_apply, hrote]
  let p₁' : ℝ → ℝ := fun u => p₁ u - p₁ 0
  let p₂' : ℝ → ℝ := fun u => p₂ u - p₁ 0
  have hp₁'c : ContinuousOn p₁' (Icc 0 1) := hp₁c.sub continuousOn_const
  have hp₁'m : StrictMonoOn p₁' (Icc 0 1) := fun a ha b hb h => sub_lt_sub_right (hp₁m ha hb h) (p₁ 0)
  have hp₂'c : ContinuousOn p₂' (Icc 0 1) := hp₂c.sub continuousOn_const
  have hp₂'m : StrictMonoOn p₂' (Icc 0 1) := fun a ha b hb h => sub_lt_sub_right (hp₂m ha hb h) (p₁ 0)
  set a₁ := p₁' 1
  set a₂ := p₂' 0
  set a₃ := p₂' 1
  have hp₁'0 : p₁' 0 = 0 := sub_self (p₁ 0)
  have ha₁_pos : 0 < a₁ := hp₁'0 ▸ hp₁'m ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one
  have ha₁₂ : a₁ < a₂ := by simp only [a₁, a₂, p₁', p₂']; linarith
  have ha₂₃ : a₂ < a₃ := hp₂'m ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one
  have ha₃_lt : a₃ < 1 := by simp only [a₃, p₂']; linarith
  obtain ⟨pinv₁, hp1i_c, hp1i_m, hp1i_l, _⟩ := exists_inv_strictMonoOn hp₁'c hp₁'m
  obtain ⟨pinv₂, hp2i_c, hp2i_m, hp2i_l, _⟩ := exists_inv_strictMonoOn hp₂'c hp₂'m
  -- Piecewise 4-interval map `τ : [0, 1] → ℝ`:
  let f₁ : ℝ → ℝ := fun t => q₁ (pinv₁ t) - p₁ 0
  let f₂ : ℝ → ℝ := fun t => (q₁ 1 - p₁ 0) + ((t - a₁) / (a₂ - a₁)) * (q₂ 0 - q₁ 1)
  let f₃ : ℝ → ℝ := fun t => q₂ (pinv₂ t) - p₁ 0
  let f₄ : ℝ → ℝ := fun t => (q₂ 1 - p₁ 0) + ((t - a₃) / (1 - a₃)) * (q₁ 0 + 1 - q₂ 1)
  let τ : ℝ → ℝ := fun t => if t ≤ a₁ then f₁ t else if t ≤ a₂ then f₂ t else if t ≤ a₃ then f₃ t else f₄ t
  have hf12 : f₁ a₁ = f₂ a₁ := by
    have h1 : pinv₁ a₁ = 1 := hp1i_l 1 ⟨zero_le_one, le_rfl⟩
    simp only [f₁, f₂, h1, sub_self, zero_div, zero_mul, add_zero]
  have hf23 : f₂ a₂ = f₃ a₂ := by
    have h2 : pinv₂ a₂ = 0 := hp2i_l 0 ⟨le_rfl, zero_le_one⟩
    simp only [f₂, f₃, h2, div_self (by linarith : (a₂ - a₁ : ℝ) ≠ 0), one_mul]
    ring
  have hf34 : f₃ a₃ = f₄ a₃ := by
    have h3 : pinv₂ a₃ = 1 := hp2i_l 1 ⟨zero_le_one, le_rfl⟩
    simp only [f₃, f₄, h3, sub_self, zero_div, zero_mul, add_zero]
  have hτ1 : ∀ t, t ≤ a₁ → τ t = f₁ t := fun t ht => ite_eq_left ht
  have hτ2 : ∀ t, a₁ ≤ t → t ≤ a₂ → τ t = f₂ t := fun t h1 h2 => by
    by_cases h : t ≤ a₁
    · have he : t = a₁ := le_antisymm h h1; subst he; rw [hτ1 _ le_rfl, hf12]
    · simp only [τ, ite_eq_right h, ite_eq_left h2]
  have hτ3 : ∀ t, a₂ ≤ t → t ≤ a₃ → τ t = f₃ t := fun t h2 h3 => by
    have h1 : ¬ t ≤ a₁ := by linarith
    by_cases h : t ≤ a₂
    · have he : t = a₂ := le_antisymm h h2; subst he; rw [hτ2 _ ha₁₂.le le_rfl, hf23]
    · simp only [τ, ite_eq_right h1, ite_eq_right h, ite_eq_left h3]
  have hτ4 : ∀ t, a₃ ≤ t → τ t = f₄ t := fun t h3 => by
    have h1 : ¬ t ≤ a₁ := by linarith
    have h2 : ¬ t ≤ a₂ := by linarith
    by_cases h : t ≤ a₃
    · have he : t = a₃ := le_antisymm h h3; subst he; rw [hτ3 _ ha₂₃.le le_rfl, hf34]
    · simp only [τ, ite_eq_right h1, ite_eq_right h2, ite_eq_right h]
  have hp1_maps : MapsTo pinv₁ (Icc 0 a₁) (Icc 0 1) := fun t ht => by
    have ht' : t ∈ Icc (p₁' 0) (p₁' 1) := by rw [hp₁'0]; exact ht
    have h0 := hp1i_m.monotoneOn (by rw [hp₁'0]; exact ⟨le_rfl, ha₁_pos.le⟩) ht' (show p₁' 0 ≤ t by rw [hp₁'0]; exact ht.1)
    have h1 := hp1i_m.monotoneOn ht' (by rw [hp₁'0]; exact ⟨ha₁_pos.le, le_rfl⟩) ht.2
    have h0' : pinv₁ (p₁' 0) = 0 := hp1i_l 0 ⟨le_rfl, zero_le_one⟩
    have h1' : pinv₁ (p₁' 1) = 1 := hp1i_l 1 ⟨zero_le_one, le_rfl⟩
    rw [h0'] at h0; rw [h1'] at h1
    exact ⟨h0, h1⟩
  have hp2_maps : MapsTo pinv₂ (Icc a₂ a₃) (Icc 0 1) := fun t ht => by
    have h0 := hp2i_m.monotoneOn ⟨le_rfl, ha₂₃.le⟩ ht ht.1
    have h1 := hp2i_m.monotoneOn ht ⟨ha₂₃.le, le_rfl⟩ ht.2
    rw [hp2i_l 0 ⟨le_rfl, zero_le_one⟩] at h0; rw [hp2i_l 1 ⟨zero_le_one, le_rfl⟩] at h1
    exact ⟨h0, h1⟩
  have hc_glue : ∀ {x₀ x₁ x₂ : ℝ}, x₀ ≤ x₁ → x₁ ≤ x₂ →
      ContinuousOn τ (Icc x₀ x₁) → ContinuousOn τ (Icc x₁ x₂) → ContinuousOn τ (Icc x₀ x₂) := by
    intro x₀ x₁ x₂ h01 h12 hc1 hc2
    rw [← Icc_union_Icc_eq_Icc h01 h12]
    intro x hx
    rcases lt_trichotomy x x₁ with hlt | rfl | hgt
    · exact (hc1 x ⟨hx.elim And.left (fun h => by linarith [h.1]), hlt.le⟩).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (inter_mem_nhdsWithin _ (Iio_mem_nhds hlt)) fun y ⟨hyu, hyl⟩ =>
          ⟨hyu.elim And.left (fun h => by linarith [h.1]), hyl.le⟩)
    · exact (hc1 x ⟨h01, le_rfl⟩).union (hc2 x ⟨le_rfl, h12⟩)
    · exact (hc2 x ⟨hgt.le, hx.elim (fun h => by linarith [h.2]) And.right⟩).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (inter_mem_nhdsWithin _ (Ioi_mem_nhds hgt)) fun y ⟨hyu, hyr⟩ =>
          ⟨hyr.le, hyu.elim (fun h => by linarith [h.2]) And.right⟩)
  have hc1 : ContinuousOn τ (Icc 0 a₁) :=
    ((hq₁c.comp (by rw [← hp₁'0]; exact hp1i_c) hp1_maps).sub continuousOn_const).congr fun t ht => hτ1 t ht.2
  have hc2 : ContinuousOn τ (Icc a₁ a₂) :=
    (by fun_prop : ContinuousOn f₂ (Icc a₁ a₂)).congr fun t ht => hτ2 t ht.1 ht.2
  have hc3 : ContinuousOn τ (Icc a₂ a₃) :=
    ((hq₂c.comp hp2i_c hp2_maps).sub continuousOn_const).congr fun t ht => hτ3 t ht.1 ht.2
  have hc4 : ContinuousOn τ (Icc a₃ 1) :=
    (by fun_prop : ContinuousOn f₄ (Icc a₃ 1)).congr fun t ht => hτ4 t ht.1
  have hτc : ContinuousOn τ (Icc 0 1) :=
    hc_glue (by linarith) ha₃_lt.le (hc_glue (by linarith) ha₂₃.le (hc_glue ha₁_pos.le ha₁₂.le hc1 hc2) hc3) hc4
  have hm_glue : ∀ {x₀ x₁ x₂ : ℝ}, x₀ ≤ x₁ → x₁ ≤ x₂ →
      StrictMonoOn τ (Icc x₀ x₁) → StrictMonoOn τ (Icc x₁ x₂) → StrictMonoOn τ (Icc x₀ x₂) := by
    intro x₀ x₁ x₂ h01 h12 hm1 hm2 x hx y hy hxy
    by_cases hx1 : x ≤ x₁
    · by_cases hy1 : y ≤ x₁
      · exact hm1 ⟨hx.1, hx1⟩ ⟨hy.1, hy1⟩ hxy
      · have hylt : x₁ < y := not_le.mp hy1
        have h1 : τ x ≤ τ x₁ := hm1.monotoneOn ⟨hx.1, hx1⟩ ⟨h01, le_rfl⟩ hx1
        have h2 : τ x₁ < τ y := hm2 ⟨le_rfl, h12⟩ ⟨hylt.le, hy.2⟩ hylt
        linarith
    · exact hm2 ⟨(not_le.mp hx1).le, hx.2⟩ ⟨by linarith [not_le.mp hx1], hy.2⟩ hxy
  have hm1 : StrictMonoOn τ (Icc 0 a₁) := fun x hx y hy hxy => by
    rw [hτ1 x hx.2, hτ1 y hy.2]
    exact sub_lt_sub_right (hq₁m (hp1_maps hx) (hp1_maps hy) (hp1i_m (by rw [hp₁'0]; exact hx) (by rw [hp₁'0]; exact hy) hxy)) (p₁ 0)
  have hm2 : StrictMonoOn τ (Icc a₁ a₂) := fun x hx y hy hxy => by
    rw [hτ2 x hx.1 hx.2, hτ2 y hy.1 hy.2]
    have h1 : (x - a₁) / (a₂ - a₁) < (y - a₁) / (a₂ - a₁) := div_lt_div_of_pos_right (by linarith) (by linarith)
    linarith [mul_lt_mul_of_pos_right h1 (by linarith : 0 < q₂ 0 - q₁ 1)]
  have hm3 : StrictMonoOn τ (Icc a₂ a₃) := fun x hx y hy hxy => by
    rw [hτ3 x hx.1 hx.2, hτ3 y hy.1 hy.2]
    exact sub_lt_sub_right (hq₂m (hp2_maps hx) (hp2_maps hy) (hp2i_m hx hy hxy)) (p₁ 0)
  have hm4 : StrictMonoOn τ (Icc a₃ 1) := fun x hx y hy hxy => by
    rw [hτ4 x hx.1, hτ4 y hy.1]
    have h1 : (x - a₃) / (1 - a₃) < (y - a₃) / (1 - a₃) := div_lt_div_of_pos_right (by linarith) (by linarith)
    linarith [mul_lt_mul_of_pos_right h1 (by linarith : 0 < q₁ 0 + 1 - q₂ 1)]
  have hτm : StrictMonoOn τ (Icc 0 1) :=
    hm_glue (by linarith) ha₃_lt.le (hm_glue (by linarith) ha₂₃.le (hm_glue ha₁_pos.le ha₁₂.le hm1 hm2) hm3) hm4
  have hτ1_eq : τ 1 = τ 0 + 1 := by
    have hp0_inv : pinv₁ 0 = 0 := by have := hp1i_l 0 ⟨le_rfl, zero_le_one⟩; rwa [hp₁'0] at this
    rw [hτ4 1 ha₃_lt.le, hτ1 0 ha₁_pos.le]
    simp only [f₄, f₁, hp0_inv, div_self (by linarith : (1 - a₃ : ℝ) ≠ 0), one_mul]
    ring
  obtain ⟨h, hhp, hhe⟩ := exists_circle_homeo hτc hτm hτ1_eq
  obtain ⟨M, hMφ₀, hMoff⟩ := move_cuff Y C U φ₀ h hY hC hUo hCU hhp
  refine ⟨M, fun u hu => ?_, fun u hu => ?_,
    fun D hD hne y hyD => hMoff y (Set.disjoint_right.mp (hUdisj D hD hne) hyD), ?_⟩
  · have hp₁u : p₁' u ∈ Icc (0 : ℝ) a₁ :=
      ⟨hp₁'0 ▸ hp₁'m.monotoneOn ⟨le_rfl, zero_le_one⟩ hu hu.1, hp₁'m.monotoneOn hu ⟨zero_le_one, le_rfl⟩ hu.2⟩
    have h1 : (φ (ee (p₁ u))).1 = (φ₀ (ee (p₁' u))).1 := by
      rw [hφ₀_e (p₁' u), show p₁' u + p₁ 0 = p₁ u by simp [p₁']]
    rw [h1, hMφ₀ (ee (p₁' u)), hhe (p₁' u) ⟨hp₁u.1, by linarith [hp₁u.2]⟩, hφ₀_e, hτ1 (p₁' u) hp₁u.2]
    simp only [f₁, hp1i_l u hu, sub_add_cancel]
  · have hp₂u : p₂' u ∈ Icc a₂ a₃ :=
      ⟨hp₂'m.monotoneOn ⟨le_rfl, zero_le_one⟩ hu hu.1, hp₂'m.monotoneOn hu ⟨zero_le_one, le_rfl⟩ hu.2⟩
    have h1 : (φ (ee (p₂ u))).1 = (φ₀ (ee (p₂' u))).1 := by
      rw [hφ₀_e (p₂' u), show p₂' u + p₁ 0 = p₂ u by simp [p₂']]
    rw [h1, hMφ₀ (ee (p₂' u)), hhe (p₂' u) ⟨by linarith [hp₂u.1], by linarith [hp₂u.2]⟩, hφ₀_e, hτ3 (p₂' u) hp₂u.1 hp₂u.2]
    simp only [f₃, hp2i_l u hu, sub_add_cancel]
  · obtain ⟨rot_inv, hrip, hrie⟩ := preservesCircleOrientation_rot (-p₁ 0)
    have hinv_eq : rot.symm = rot_inv := Homeomorph.ext fun x => by
      obtain ⟨u, -, rfl⟩ := exists_param x
      apply rot.injective; rw [rot.apply_symm_apply, hrie u, hrote (u + -p₁ 0), show u + -p₁ 0 + p₁ 0 = u by ring]
    refine ⟨rot_inv.trans (h.trans rot),
      preservesCircleOrientation_trans hrip (preservesCircleOrientation_trans hhp hrotp), fun x => ?_⟩
    have h2 : (φ x).1 = (φ₀ (rot_inv x)).1 := by
      rw [← hinv_eq]; simp [φ₀]
    rw [h2, hMφ₀ (rot_inv x)]
    rfl

end AlignCuff

/-! ### Canonical cuff parameterization `holeParam` and local boundary direction -/

section HoleParamAndDir

variable {Y S : Type u} [TopologicalSpace Y] [TopologicalSpace S]

/-- Canonical circle homeomorphism `Circle ≃ₜ holeC a b c f i` sending `ee u ↦ holeP a b c f i u`
for all `u ∈ Icc 0 1`. -/
noncomputable def holeParam [T2Space Y] {a b c : ℕ} {f : ℕ × ℂ → Y}
    (hf : Presents (sW (ew a b c)) f) {i : ℕ} (hi : i < c) :
    Circle ≃ₜ holeC a b c f i := by
  have hloop := hole_loop hf hi
  have hmem : ∀ u ∈ Icc (0 : ℝ) 1, holeP a b c f i u ∈ holeC a b c f i := fun u hu => ⟨u, hu, rfl⟩
  let g : Circle → holeC a b c f i := fun z =>
    let u := (exists_param z).choose
    ⟨holeP a b c f i u, hmem u (Ico_subset_Icc_self (exists_param z).choose_spec.1)⟩
  have hg_ee : ∀ u ∈ Icc (0 : ℝ) 1, (g (ee u)).1 = holeP a b c f i u := fun u hu => by
    dsimp only [g]
    set v := (exists_param (ee u)).choose
    have hv := (exists_param (ee u)).choose_spec
    rcases eq_or_lt_of_le hu.2 with rfl | hlt
    · have hv0 : v = 0 := by
        obtain ⟨k, hk⟩ := ee_eq_iff.mp (hv.2.trans (show ee 1 = ee 0 by simpa using ee_add_one 0))
        have hklt : |(k : ℝ)| < 1 := by rw [abs_lt]; exact ⟨by linarith [hv.1.1], by linarith [hv.1.2]⟩
        have hk0 : k = 0 := by have := abs_lt.mp (show |k| < 1 by exact_mod_cast hklt); omega
        subst hk0; simp only [Int.cast_zero, add_zero] at hk; exact hk
      rw [hv0, hloop.2.2]
    · have hve : v = u := by
        obtain ⟨k, hk⟩ := ee_eq_iff.mp hv.2
        have hklt : |(k : ℝ)| < 1 := by rw [abs_lt]; exact ⟨by linarith [hv.1.1, hlt], by linarith [hv.1.2, hu.1]⟩
        have hk0 : k = 0 := by have := abs_lt.mp (show |k| < 1 by exact_mod_cast hklt); omega
        subst hk0; simp only [Int.cast_zero, add_zero] at hk; exact hk
      rw [hve]
  have hg_cont : Continuous g := by
    have hq : IsQuotientMap (fun t : ℝ => ee t) :=
      (Circle.isCoveringMap_exp.isQuotientMap fun z => ⟨_, Circle.exp_arg z⟩).comp
        (Homeomorph.mulLeft₀ (2 * Real.pi) (by positivity)).isQuotientMap
    rw [hq.continuous_iff]
    have hcomp : g ∘ ee = fun t : ℝ =>
        ⟨holeP a b c f i (Int.fract t), hmem _ ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩⟩ := by
      funext t
      have hfr : ee t = ee (Int.fract t) := by
        rw [ee_eq_iff]; exact ⟨⌊t⌋, by linarith [Int.floor_add_fract t]⟩
      ext; simp only [comp_apply, hfr]
      exact hg_ee (Int.fract t) ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
    rw [hcomp]
    refine Continuous.subtype_mk ?_ _
    exact ContinuousOn.comp_fract'' hloop.1 hloop.2.2
  have hg_bij : Bijective g := by
    refine ⟨fun z₁ z₂ he => ?_, fun ⟨y, u, hu, hy⟩ => ⟨ee u, Subtype.ext ((hg_ee u hu).trans hy)⟩⟩
    obtain ⟨u₁, hu₁, rfl⟩ := exists_param z₁
    obtain ⟨u₂, hu₂, rfl⟩ := exists_param z₂
    have he' : holeP a b c f i u₁ = holeP a b c f i u₂ := by
      rw [← hg_ee u₁ (Ico_subset_Icc_self hu₁), ← hg_ee u₂ (Ico_subset_Icc_self hu₂), he]
    rw [hloop.2.1 hu₁ hu₂ he']
  exact hg_cont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g hg_bij)

theorem holeParam_ee [T2Space Y] {a b c : ℕ} {f : ℕ × ℂ → Y}
    (hf : Presents (sW (ew a b c)) f) {i : ℕ} (hi : i < c) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    (holeParam hf hi (ee u)).1 = holeP a b c f i u := by
  have hloop := hole_loop hf hi
  change (let v := (exists_param (ee u)).choose; holeP a b c f i v) = holeP a b c f i u
  set v := (exists_param (ee u)).choose
  have hv := (exists_param (ee u)).choose_spec
  rcases eq_or_lt_of_le hu.2 with rfl | hlt
  · have hv0 : v = 0 := by
      obtain ⟨k, hk⟩ := ee_eq_iff.mp (hv.2.trans (show ee 1 = ee 0 by simpa using ee_add_one 0))
      have hklt : |(k : ℝ)| < 1 := by rw [abs_lt]; exact ⟨by linarith [hv.1.1], by linarith [hv.1.2]⟩
      have hk0 : k = 0 := by have := abs_lt.mp (show |k| < 1 by exact_mod_cast hklt); omega
      subst hk0; simp only [Int.cast_zero, add_zero] at hk; exact hk
    rw [hv0, hloop.2.2]
  · have hve : v = u := by
      obtain ⟨k, hk⟩ := ee_eq_iff.mp hv.2
      have hklt : |(k : ℝ)| < 1 := by rw [abs_lt]; exact ⟨by linarith [hv.1.1, hlt], by linarith [hv.1.2, hu.1]⟩
      have hk0 : k = 0 := by have := abs_lt.mp (show |k| < 1 by exact_mod_cast hklt); omega
      subst hk0; simp only [Int.cast_zero, add_zero] at hk; exact hk
    rw [hve]

/-- At any boundary point `y₀ = φY (ee u₀) ∈ CY` whose image `ψ y₀` lies in `CS \ F`, `ψ` maps a
small arc around `y₀` in `CY` monotonically into `CS` with a unique direction bit `dir : Bool`,
related to `cutOrientDiff` via `cuffSign AS φS (ψ y₀) - cuffSign AY φY y₀ = cutOrientDiff AY AS ψ y₀ + (if dir then 0 else 1)`. -/
theorem exists_cuff_local_dir (hY : IsSurface Y) (hS : IsSurface S) [T2Space Y]
    {ψ : Y → S} {F : Set S} (hψ : IsCutting ψ F) (hF : IsClosed F)
    (AY : SurfAtlas Y) (AS : SurfAtlas S)
    {CY : Set Y} {CS : Set S} (hCY : CY ⊆ bd Y) (hCS : CS ∈ cuffs S)
    (φY : Circle ≃ₜ CY) (φS : Circle ≃ₜ CS) {u₀ : ℝ}
    (hyS : ψ (φY (ee u₀)).1 ∈ CS) (hyF : ψ (φY (ee u₀)).1 ∉ F) :
    ∃ (δ : ℝ) (m : ℝ → ℝ) (dir : Bool), 0 < δ ∧ δ < 1 / 4 ∧
      ContinuousOn m (Icc (-δ) δ) ∧
      (if dir then StrictMonoOn m (Icc (-δ) δ) else StrictAntiOn m (Icc (-δ) δ)) ∧
      (∀ t ∈ Icc (-δ) δ, ψ (φY (ee (u₀ + t))).1 = (φS (ee (m t))).1) ∧
      (cuffSign AS φS (ψ (φY (ee u₀)).1) - cuffSign AY φY (φY (ee u₀)).1 =
        cutOrientDiff AY AS ψ (φY (ee u₀)).1 + (if dir then 0 else 1)) := by
  have : CompactSpace Y := hY.1
  have : T2Space S := hS.2.1
  have hCS_bd : CS ⊆ bd S := by obtain ⟨z, -, rfl⟩ := hCS; exact connectedComponentIn_subset _ _
  obtain ⟨U_S, hUo, hCSU, hUdisj⟩ := exists_cuff_open_disj hS hCS
  -- Open neighborhood `W := (ψ ⁻¹' (U_S ∩ Fᶜ))` of `φY (ee u₀)` in `Y`:
  have hWo : IsOpen (ψ ⁻¹' (U_S ∩ Fᶜ)) := (hUo.inter hF.isOpen_compl).preimage hψ.1
  have hWmem : (φY (ee u₀)).1 ∈ ψ ⁻¹' (U_S ∩ Fᶜ) := ⟨hCSU hyS, hyF⟩
  have hcont : Continuous (fun t : ℝ => (φY (ee (u₀ + t))).1) :=
    continuous_subtype_val.comp (φY.continuous.comp (continuous_ee.comp (continuous_const.add continuous_id)))
  have hnhd : (fun t : ℝ => (φY (ee (u₀ + t))).1) ⁻¹' (ψ ⁻¹' (U_S ∩ Fᶜ)) ∈ 𝓝 (0 : ℝ) :=
    (hWo.preimage hcont).mem_nhds (by simpa using hWmem)
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hnhd
  set δ := min (ρ / 2) (1 / 8)
  have hδ : 0 < δ := lt_min (half_pos hρ) (by norm_num)
  have hδ4 : δ < 1 / 4 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδρ : δ < ρ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hρ)
  have hin : ∀ t ∈ Icc (-δ) δ, ψ (φY (ee (u₀ + t))).1 ∈ CS ∧ ψ (φY (ee (u₀ + t))).1 ∉ F := fun t ht => by
    have h1 := hρsub (show t ∈ ball (0 : ℝ) ρ by rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    have hbdY : (φY (ee (u₀ + t))).1 ∈ bd Y := hCY (φY _).2
    have hbdS : ψ (φY (ee (u₀ + t))).1 ∈ bd S := by
      -- Since `ψ y ∉ F`, `y ∈ bd Y ↔ ψ y ∈ bd S`:
      have hneF : ψ (φY (ee (u₀ + t))).1 ∉ F := h1.2
      exact (mem_bd_iff_of_not_mem hY hS hψ hF hneF).mp hbdY
    have hcov : ψ (φY (ee (u₀ + t))).1 ∈ ⋃₀ cuffs S := (sUnion_cuffs (S := S)).symm ▸ hbdS
    obtain ⟨D, hD, hxD⟩ := hcov
    have hDC : D = CS := by
      by_contra hne
      exact Set.disjoint_left.mp (hUdisj D hD hne) h1.1 hxD
    exact ⟨hDC ▸ hxD, h1.2⟩
  -- Lift `u ↦ ψ (φY (ee (u₀ - δ + 2δ u))).1` on `[0, 1]` into `φS`:
  let γ : ℝ → S := fun u => ψ (φY (ee (u₀ + (-δ + 2 * δ * u)))).1
  have hγc : ContinuousOn γ (Icc 0 1) :=
    (hψ.1.comp (hcont.comp (continuous_const.add (continuous_const.mul continuous_id)))).continuousOn
  have hγCS : ∀ u ∈ Icc (0 : ℝ) 1, γ u ∈ CS := fun u hu =>
    (hin (-δ + 2 * δ * u) ⟨by nlinarith [hu.1, hδ], by nlinarith [hu.2, hδ]⟩).1
  obtain ⟨m₀, hm₀c, hm₀e⟩ := exists_lift φS hγc hγCS
  let m : ℝ → ℝ := fun t => m₀ ((t + δ) / (2 * δ))
  have hmc : ContinuousOn m (Icc (-δ) δ) :=
    hm₀c.comp (by fun_prop) fun t ht => ⟨div_nonneg (by linarith [ht.1]) (by linarith),
      (div_le_one (by linarith)).mpr (by linarith [ht.2])⟩
  have hme : ∀ t ∈ Icc (-δ) δ, ψ (φY (ee (u₀ + t))).1 = (φS (ee (m t))).1 := fun t ht => by
    have h1 := hm₀e ((t + δ) / (2 * δ)) ⟨div_nonneg (by linarith [ht.1]) (by linarith),
      (div_le_one (by linarith)).mpr (by linarith [ht.2])⟩
    have h2 : -δ + 2 * δ * ((t + δ) / (2 * δ)) = t := by field_simp; ring
    simpa only [γ, h2, m] using h1.symm
  have hm_inj : InjOn m (Icc (-δ) δ) := fun t₁ ht₁ t₂ ht₂ he => by
    have h1 : ψ (φY (ee (u₀ + t₁))).1 = ψ (φY (ee (u₀ + t₂))).1 := by rw [hme t₁ ht₁, hme t₂ ht₂, he]
    have h2 : (φY (ee (u₀ + t₁))).1 = (φY (ee (u₀ + t₂))).1 :=
      hψ.2.2.1 (hin t₁ ht₁).2 (hin t₂ ht₂).2 h1
    have h3 : ee (u₀ + t₁) = ee (u₀ + t₂) := φY.injective (Subtype.ext h2)
    obtain ⟨k, hk⟩ := ee_eq_iff.mp h3
    have hkt : |(k : ℝ)| < 1 := by rw [abs_lt]; exact ⟨by linarith [ht₁.1, ht₂.2], by linarith [ht₁.2, ht₂.1]⟩
    have hk0 : k = 0 := by have := abs_lt.mp (show |k| < 1 by exact_mod_cast hkt); omega
    subst hk0; simp only [Int.cast_zero, add_zero] at hk; linarith
  have hmo := hmc.strictMonoOn_of_injOn_Icc' (by linarith) hm_inj
  have hex_dir : ∃ dir : Bool, if dir then StrictMonoOn m (Icc (-δ) δ) else StrictAntiOn m (Icc (-δ) δ) :=
    hmo.elim (fun h => ⟨true, h⟩) (fun h => ⟨false, h⟩)
  obtain ⟨dir, hdir⟩ := hex_dir
  have hsign := cutOrientDiff_cuff_mono hY hS hψ hF AY AS hCY hCS_bd φY φS (φY _).2 hyF hδ dir hmc hdir hme rfl
  exact ⟨δ, m, dir, hδ, hδ4, hmc, hdir, hme, hsign⟩
where
  mem_bd_iff_of_not_mem (hY : IsSurface Y) (hS : IsSurface S)
      {ψ : Y → S} {F : Set S} (hψ : IsCutting ψ F) (hF : IsClosed F)
      {y : Y} (hyF : ψ y ∉ F) : y ∈ bd Y ↔ ψ y ∈ bd S := by
    have : CompactSpace Y := hY.1
    have : T2Space S := hS.2.1
    constructor
    · intro hybd
      by_contra hnotbd
      have hopenS : IsOpen (Fᶜ : Set S) := hF.isOpen_compl
      have hbij : Bijective (Fᶜ.restrictPreimage ψ) := by
        refine ⟨fun a b h => Subtype.ext (hψ.2.2.1 a.2 b.2 (congrArg Subtype.val h)), fun ⟨x, hx⟩ => ?_⟩
        obtain ⟨w, rfl⟩ := hψ.2.1 x; exact ⟨⟨w, hx⟩, rfl⟩
      have hq := hψ.1.isClosedMap.isQuotientMap hψ.1 hψ.2.1
      have hqr : IsQuotientMap (Fᶜ.restrictPreimage ψ) := hq.restrictPreimage_isOpen hopenS
      let eEq := Equiv.ofBijective (Fᶜ.restrictPreimage ψ) hbij
      let eF : (ψ ⁻¹' Fᶜ : Set Y) ≃ₜ (Fᶜ : Set S) := {
        toEquiv := eEq
        continuous_toFun := hqr.continuous
        continuous_invFun := by
          rw [hqr.continuous_iff]
          have : eEq.invFun ∘ Fᶜ.restrictPreimage ψ = id := funext fun x => eEq.symm_apply_apply x
          rw [this]; exact continuous_id }
      obtain ⟨cS, hcS⟩ := exists_surfChart (hS.2.2 (ψ y))
      have hre_pos : 0 < (cS.j (ψ y)).re :=
        lt_of_le_of_ne (cS.hm hcS).2 (Ne.symm fun h0 => hnotbd ((cS.mem_bd_iff hcS).mpr h0))
      have hO' : IsOpen (cS.O ∩ {w : ℂ | 0 < w.re} ∩ cS.k ⁻¹' Fᶜ) := by
        have h1 : IsOpen (cS.O ∩ {w : ℂ | 0 < w.re}) :=
          cS.hO.inter (isOpen_lt (continuous_const (y := (0 : ℝ))) Complex.continuous_re)
        have hsub : cS.O ∩ {w : ℂ | 0 < w.re} ⊆ cS.O ∩ halfPlane := fun w hw => ⟨hw.1, show 0 ≤ w.re from le_of_lt hw.2⟩
        exact (cS.hk.mono hsub).isOpen_inter_preimage h1 hopenS
      have hmem0 : cS.j (ψ y) ∈ cS.O ∩ {w : ℂ | 0 < w.re} ∩ cS.k ⁻¹' Fᶜ :=
        ⟨⟨(cS.hm hcS).1, hre_pos⟩, by show cS.k (cS.j (ψ y)) ∉ F; rw [cS.hl hcS]; exact hyF⟩
      obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hO' _ hmem0
      have hB_open : IsOpen (ball (cS.j (ψ y)) r) := isOpen_ball
      have hB_sub : ball (cS.j (ψ y)) r ⊆ cS.O ∩ halfPlane := fun w hw => ⟨(hrsub hw).1.1, show 0 ≤ w.re from le_of_lt (hrsub hw).1.2⟩
      let US : Set S := cS.k '' ball (cS.j (ψ y)) r
      have hUS_eq : US = cS.U ∩ cS.j ⁻¹' ball (cS.j (ψ y)) r := by
        ext x; constructor
        · rintro ⟨w, hw, rfl⟩; exact ⟨cS.hk' (hB_sub hw), by show cS.j (cS.k w) ∈ ball (cS.j (ψ y)) r; rwa [cS.hr (hB_sub hw)]⟩
        · rintro ⟨hxU, hxB⟩; exact ⟨cS.j x, hxB, cS.hl hxU⟩
      have hUS_open : IsOpen US := hUS_eq ▸ cS.hj.isOpen_inter_preimage cS.hU hB_open
      have hUS_subF : US ⊆ Fᶜ := by rintro _ ⟨w, hw, rfl⟩; exact (hrsub hw).2
      let UY : Set Y := ψ ⁻¹' US
      have hUY_open : IsOpen UY := hUS_open.preimage hψ.1
      have hyUY : y ∈ UY := ⟨cS.j (ψ y), mem_ball_self hr, cS.hl hcS⟩
      have hHomeo : Nonempty (UY ≃ₜ OpenUnitDisc) := by
        let e1 : UY ≃ₜ US := {
          toFun := fun z => ⟨ψ z.1, z.2⟩
          invFun := fun z => ⟨(eF.symm ⟨z.1, hUS_subF z.2⟩).1, by
            have := congrArg Subtype.val (eF.apply_symm_apply ⟨z.1, hUS_subF z.2⟩)
            show ψ (eF.symm ⟨z.1, hUS_subF z.2⟩).1 ∈ US
            rw [show ψ (eF.symm ⟨z.1, hUS_subF z.2⟩).1 = (eF (eF.symm ⟨z.1, hUS_subF z.2⟩)).1 from rfl, this]
            exact z.2⟩
          left_inv := fun z => Subtype.ext (by
            dsimp only
            exact congrArg Subtype.val (eF.symm_apply_apply ⟨z.1, hUS_subF z.2⟩))
          right_inv := fun z => Subtype.ext (by
            dsimp only
            exact congrArg Subtype.val (eF.apply_symm_apply ⟨z.1, hUS_subF z.2⟩))
          continuous_toFun := continuous_induced_rng.mpr (hψ.1.comp continuous_subtype_val)
          continuous_invFun := by
            rw [continuous_induced_rng]
            show Continuous (fun z : US => (eF.symm ⟨z.1, hUS_subF z.2⟩).1)
            refine continuous_subtype_val.comp (eF.symm.continuous.comp ?_)
            rw [continuous_induced_rng]
            exact continuous_subtype_val }
        let e2 : US ≃ₜ ball (cS.j (ψ y)) r := {
          toFun := fun x => ⟨cS.j x.1, ((Set.ext_iff.mp hUS_eq x.1).mp x.2).2⟩
          invFun := fun w => ⟨cS.k w.1, ⟨w.1, w.2, rfl⟩⟩
          left_inv := fun x => Subtype.ext (cS.hl ((Set.ext_iff.mp hUS_eq x.1).mp x.2).1)
          right_inv := fun w => Subtype.ext (cS.hr (hB_sub w.2))
          continuous_toFun := continuous_induced_rng.mpr
            (cS.hj.comp_continuous continuous_subtype_val fun x => ((Set.ext_iff.mp hUS_eq x.1).mp x.2).1)
          continuous_invFun := continuous_induced_rng.mpr
            (cS.hk.comp_continuous continuous_subtype_val fun w => hB_sub w.2) }
        let z₀ := cS.j (ψ y)
        let e3 : ball z₀ r ≃ₜ ball (0 : ℂ) 1 := {
          toFun := fun w => ⟨(w.1 - z₀) / (r : ℂ), by
            rw [mem_ball_zero_iff, norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le, div_lt_one hr]
            exact mem_ball_iff_norm.mp w.2⟩
          invFun := fun v => ⟨z₀ + (r : ℂ) * v.1, by
            rw [mem_ball_iff_norm, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]
            have hv : ‖v.1‖ < 1 := mem_ball_zero_iff.mp v.2
            nlinarith⟩
          left_inv := fun w => Subtype.ext (by
            dsimp only
            rw [mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hr.ne'), add_sub_cancel])
          right_inv := fun v => Subtype.ext (by
            dsimp only
            rw [add_sub_cancel_left, mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hr.ne')])
          continuous_toFun := continuous_induced_rng.mpr ((continuous_subtype_val.sub continuous_const).div_const _)
          continuous_invFun := continuous_induced_rng.mpr (continuous_const.add (continuous_const.mul continuous_subtype_val)) }
        have hnorm_eq : ∀ z : ℂ, ‖((EuclideanSpace.equiv (Fin 2) ℝ).symm ![z.re, z.im] : EuclideanPlane)‖ = ‖z‖ := fun z => by
          rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Complex.norm_def, Complex.normSq_apply]
          simp [EuclideanSpace.equiv, Real.norm_eq_abs, sq_abs]; ring_nf
        have hnorm_eq' : ∀ p : EuclideanPlane, ‖(((p 0 : ℝ) : ℂ) + ((p 1 : ℝ) : ℂ) * Complex.I)‖ = ‖p‖ := fun p => by
          rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Complex.norm_def, Complex.normSq_apply]
          simp [Real.norm_eq_abs, sq_abs]; ring_nf
        let e4 : ball (0 : ℂ) 1 ≃ₜ OpenUnitDisc := {
          toFun := fun z => ⟨(EuclideanSpace.equiv (Fin 2) ℝ).symm ![z.1.re, z.1.im], by
            rw [OpenUnitDisc, mem_ball_zero_iff, hnorm_eq]; exact mem_ball_zero_iff.mp z.2⟩
          invFun := fun p => ⟨((p.1 0 : ℝ) : ℂ) + ((p.1 1 : ℝ) : ℂ) * Complex.I, by
            rw [mem_ball_zero_iff, hnorm_eq']; exact mem_ball_zero_iff.mp p.2⟩
          left_inv := fun z => Subtype.ext (by
            apply Complex.ext <;> simp [EuclideanSpace.equiv])
          right_inv := fun p => Subtype.ext (by
            ext i; fin_cases i <;> simp [EuclideanSpace.equiv])
          continuous_toFun := Continuous.subtype_mk
            (f := fun z : ball (0 : ℂ) 1 => (EuclideanSpace.equiv (Fin 2) ℝ).symm ![z.1.re, z.1.im])
            ((EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
              (continuous_pi fun i : Fin 2 => by
                fin_cases i
                · exact Complex.continuous_re.comp continuous_subtype_val
                · exact Complex.continuous_im.comp continuous_subtype_val))
            (fun z => by rw [OpenUnitDisc, mem_ball_zero_iff, hnorm_eq]; exact mem_ball_zero_iff.mp z.2)
          continuous_invFun := Continuous.subtype_mk
            (f := fun p : OpenUnitDisc => ((p.1 0 : ℝ) : ℂ) + ((p.1 1 : ℝ) : ℂ) * Complex.I)
            ((Complex.continuous_ofReal.comp ((EuclideanSpace.proj (0 : Fin 2)).continuous.comp continuous_subtype_val)).add
              ((Complex.continuous_ofReal.comp ((EuclideanSpace.proj (1 : Fin 2)).continuous.comp continuous_subtype_val)).mul continuous_const))
            (fun p => by rw [mem_ball_zero_iff, hnorm_eq']; exact mem_ball_zero_iff.mp p.2) }
        exact ⟨((e1.trans e2).trans e3).trans e4⟩
      exact hybd ⟨UY, hUY_open, hyUY, hHomeo⟩
    · intro hψbd
      exact bd_lift hψ hF hψbd hyF

/-- **Global Orientable Flip Theorem**: When `Y` and `Y'` are connected orientable (`b = 0`) cuttings
of `F` and `F'` with `BdCohRel s t (arcCocycle F') (arcCocycle F)`, there is a SINGLE global bit
`Δ : ZMod 2` such that at EVERY `x ∈ bd S \ {s, t}` (lying in any cuff `CS ∈ cuffs S` with
parameterization `φS`), the local direction bits `dir, dir'` of `ψ ∘ holeParam hf hi` and
`ψ' ∘ holeParam hf' hj` at the unique preimages `y, y'` of `x` satisfy:
`(if dir then (0 : ZMod 2) else 1) - (if dir' then 0 else 1) = Δ`! -/
theorem orient_cut_global_flip [ConnectedSpace S] (hS : IsSurface S)
    {F F' : Set S} {s t : S} (hne : s ≠ t)
    (hb : F ∩ bd S = {s, t}) (hb' : F' ∩ bd S = {s, t})
    (hl : IsLineWithEnds F s t) (hl' : IsLineWithEnds F' s t)
    {Y Y' : Type u} [TopologicalSpace Y] [T2Space Y] [TopologicalSpace Y'] [T2Space Y']
    [ConnectedSpace Y] [ConnectedSpace Y']
    {ψ : Y → S} {ψ' : Y' → S} (hY : IsSurface Y) (hY' : IsSurface Y')
    (hψ : IsCutting ψ F) (hψ' : IsCutting ψ' F')
    {X X' : Set Y} {X₂ X₂' : Set Y'}
    (hP : LiftPair ψ F s t X X') (hP' : LiftPair ψ' F' s t X₂ X₂')
    {a c : ℕ} {f : ℕ × ℂ → Y} {f' : ℕ × ℂ → Y'}
    (hf : Presents (sW (ew a 0 c)) f) (hf' : Presents (sW (ew a 0 c)) f')
    (hrel : BdCohRel s t (arcCocycle hS hne hb' hl') (arcCocycle hS hne hb hl)) :
    ∃ Δ : ZMod 2,
      ∀ (x : S), x ∈ bd S \ {s, t} →
      ∀ (CS : Set S) (_hCS : CS ∈ cuffs S) (φS : Circle ≃ₜ CS), x ∈ CS →
      ∀ (i j : ℕ) (hi : i < c) (hj : j < c) (u₀ u₀' : ℝ),
        ψ (holeParam hf hi (ee u₀)).1 = x → ψ' (holeParam hf' hj (ee u₀')).1 = x →
        ∀ (δ δ' : ℝ) (m m' : ℝ → ℝ) (dir dir' : Bool),
          0 < δ → 0 < δ' →
          ContinuousOn m (Icc (-δ) δ) → ContinuousOn m' (Icc (-δ') δ') →
          (if dir then StrictMonoOn m (Icc (-δ) δ) else StrictAntiOn m (Icc (-δ) δ)) →
          (if dir' then StrictMonoOn m' (Icc (-δ') δ') else StrictAntiOn m' (Icc (-δ') δ')) →
          (∀ r ∈ Icc (-δ) δ, ψ (holeParam hf hi (ee (u₀ + r))).1 = (φS (ee (m r))).1) →
          (∀ r ∈ Icc (-δ') δ', ψ' (holeParam hf' hj (ee (u₀' + r))).1 = (φS (ee (m' r))).1) →
          (if dir then (0 : ZMod 2) else 1) - (if dir' then 0 else 1) = Δ := by
  classical
  have : CompactSpace Y := hY.1
  have : CompactSpace Y' := hY'.1
  have : T2Space S := hS.2.1
  have hF : IsClosed F := hl.isCompact.isClosed
  have hF' : IsClosed F' := hl'.isCompact.isClosed
  obtain ⟨AY⟩ := exists_surfAtlas hY
  obtain ⟨AY'⟩ := exists_surfAtlas hY'
  obtain ⟨AS⟩ := exists_surfAtlas hS
  -- Global primitives `h_Y` of `w1 AY` and `h_Y'` of `w1 AY'` (since `b = 0`!):
  have hwY0 : CohRel (w1 AY) (fun _ _ => 0) := (cohRel_w1_zero_iff hf AY).mpr rfl
  have hwY'0 : CohRel (w1 AY') (fun _ _ => 0) := (cohRel_w1_zero_iff hf' AY').mpr rfl
  obtain ⟨h_Y, N_Y, hNY, hhY_raw⟩ := hwY0
  obtain ⟨h_Y', N_Y', hNY', hhY'_raw⟩ := hwY'0
  have hhY : ∀ y₁ y₂, (y₁, y₂) ∈ N_Y → w1 AY y₁ y₂ = h_Y y₂ - h_Y y₁ := fun y₁ y₂ h => by
    have := hhY_raw y₁ y₂ h; simp only [sub_zero] at this; exact this
  have hhY' : ∀ y₁ y₂, (y₁, y₂) ∈ N_Y' → w1 AY' y₁ y₂ = h_Y' y₂ - h_Y' y₁ := fun y₁ y₂ h => by
    have := hhY'_raw y₁ y₂ h; simp only [sub_zero] at this; exact this
  -- Constant `cuffSign - h_Y` across ALL cuffs of `Y` (and `Y'`):
  obtain ⟨C_Y, hCY_const⟩ := orient_cuffSign_const hf AY hNY (fun y₁ y₂ h => by rw [hhY y₁ y₂ h]; ring)
  obtain ⟨C_Y', hCY'_const⟩ := orient_cuffSign_const hf' AY' hNY' (fun y₁ y₂ h => by rw [hhY' y₁ y₂ h]; ring)
  -- Key claim: there exist `g_S, g_S' : S → ZMod 2` and a global constant `K : ZMod 2` such that
  -- on `bd S \ {s, t}`, `g_S x - g_S' x = K`, and for all `y ∉ ψ⁻¹(F)` / `y' ∉ ψ'⁻¹(F')`:
  -- `g_S (ψ y) = h_Y y + cutOrientDiff AY AS ψ y` and `g_S' (ψ' y') = h_Y' y' + cutOrientDiff AY' AS ψ' y'`!
  have hex_g : ∃ (g_S g_S' : S → ZMod 2) (K : ZMod 2),
      (∀ x ∈ bd S \ {s, t}, g_S x - g_S' x = K) ∧
      (∀ y : Y, ψ y ∉ F → g_S (ψ y) = h_Y y + cutOrientDiff AY AS ψ y) ∧
      (∀ y' : Y', ψ' y' ∉ F' → g_S' (ψ' y') = h_Y' y' + cutOrientDiff AY' AS ψ' y') := by
    obtain ⟨_, _, _, _, l1, l2, hd, hun, -⟩ := id hP
    obtain ⟨_, _, _, _, l1', l2', hd', hun', -⟩ := id hP'
    obtain ⟨V_X, V_X', hVX, hVX', hXV, hX'V', hcl⟩ :=
      exists_disjoint_closure_nhds l1.isCompact.isClosed l2.isCompact.isClosed hd
    obtain ⟨V_X₂, V_X₂', hVX₂, hVX₂', hXV₂, hX'V₂', hcl₂⟩ :=
      exists_disjoint_closure_nhds l1'.isCompact.isClosed l2'.isCompact.isClosed hd'
    by_cases hS_ori : CohRel (w1 AS) (fun _ _ => 0)
    · -- Case 1: `S` is orientable (`w1 AS = δ g_S`):
      obtain ⟨g_S, N_S, hNS, hgS⟩ := hS_ori
      have hcutY := cohRel_w1_cut_explicit hY hS hψ hF AY AS
      obtain ⟨N_cY, hNcY, hdiffY⟩ := hcutY
      -- `g_S (ψ y) - (h_Y y + cutOrientDiff AY AS ψ y)` is locally constant on connected `Y`!
      let N1 : Set (Y × Y) := N_Y ∩ N_cY ∩ (fun p : Y × Y => (ψ p.1, ψ p.2)) ⁻¹' N_S
      have hN1 : NearDiag N1 := fun y => Filter.inter_mem (Filter.inter_mem (hNY y) (hNcY y))
        ((hψ.1.prodMap hψ.1).continuousAt.preimage_mem_nhds (hNS (ψ y)))
      have hloc1 : ∀ y₁ y₂, (y₁, y₂) ∈ N1 →
          g_S (ψ y₁) - (h_Y y₁ + cutOrientDiff AY AS ψ y₁) =
          g_S (ψ y₂) - (h_Y y₂ + cutOrientDiff AY AS ψ y₂) := fun y₁ y₂ h => by
        have e1 := hhY y₁ y₂ h.1.1
        have e2 := hdiffY y₁ y₂ h.1.2
        have e3 := hgS (ψ y₁) (ψ y₂) h.2
        simp only [sub_zero] at e2 e3
        rw [e1, e3] at e2
        have : (g_S (ψ y₁) - (h_Y y₁ + cutOrientDiff AY AS ψ y₁)) -
               (g_S (ψ y₂) - (h_Y y₂ + cutOrientDiff AY AS ψ y₂)) = 0 := by
          simp only [zmod2_sub_eq_add] at e2 ⊢
          calc g_S (ψ y₁) + (h_Y y₁ + cutOrientDiff AY AS ψ y₁) +
                (g_S (ψ y₂) + (h_Y y₂ + cutOrientDiff AY AS ψ y₂))
              = (g_S (ψ y₂) + g_S (ψ y₁) + (h_Y y₂ + h_Y y₁)) +
                (cutOrientDiff AY AS ψ y₂ + cutOrientDiff AY AS ψ y₁) := by ring
            _ = (cutOrientDiff AY AS ψ y₂ + cutOrientDiff AY AS ψ y₁) +
                (cutOrientDiff AY AS ψ y₂ + cutOrientDiff AY AS ψ y₁) := by rw [e2]
            _ = 0 := zmod2_add_self _
        exact sub_eq_zero.mp this
      have hconst1 := const_of_nearDiag_eq hN1 hloc1
      obtain ⟨y₀, -⟩ := hψ.2.1 s
      set K₁ := g_S (ψ y₀) - (h_Y y₀ + cutOrientDiff AY AS ψ y₀)
      have hK₁ : ∀ y : Y, g_S (ψ y) - (h_Y y + cutOrientDiff AY AS ψ y) = K₁ := fun y => hconst1 y y₀
      -- Same on `Y'`:
      obtain ⟨N_cY', hNcY', hdiffY'⟩ := cohRel_w1_cut_explicit hY' hS hψ' hF' AY' AS
      let N2 : Set (Y' × Y') := N_Y' ∩ N_cY' ∩ (fun p : Y' × Y' => (ψ' p.1, ψ' p.2)) ⁻¹' N_S
      have hN2 : NearDiag N2 := fun y => Filter.inter_mem (Filter.inter_mem (hNY' y) (hNcY' y))
        ((hψ'.1.prodMap hψ'.1).continuousAt.preimage_mem_nhds (hNS (ψ' y)))
      have hloc2 : ∀ y₁ y₂, (y₁, y₂) ∈ N2 →
          g_S (ψ' y₁) - (h_Y' y₁ + cutOrientDiff AY' AS ψ' y₁) =
          g_S (ψ' y₂) - (h_Y' y₂ + cutOrientDiff AY' AS ψ' y₂) := fun y₁ y₂ h => by
        have e1 := hhY' y₁ y₂ h.1.1
        have e2 := hdiffY' y₁ y₂ h.1.2
        have e3 := hgS (ψ' y₁) (ψ' y₂) h.2
        simp only [sub_zero] at e2 e3
        rw [e1, e3] at e2
        have : (g_S (ψ' y₁) - (h_Y' y₁ + cutOrientDiff AY' AS ψ' y₁)) -
               (g_S (ψ' y₂) - (h_Y' y₂ + cutOrientDiff AY' AS ψ' y₂)) = 0 := by
          simp only [zmod2_sub_eq_add] at e2 ⊢
          calc g_S (ψ' y₁) + (h_Y' y₁ + cutOrientDiff AY' AS ψ' y₁) +
                (g_S (ψ' y₂) + (h_Y' y₂ + cutOrientDiff AY' AS ψ' y₂))
              = (g_S (ψ' y₂) + g_S (ψ' y₁) + (h_Y' y₂ + h_Y' y₁)) +
                (cutOrientDiff AY' AS ψ' y₂ + cutOrientDiff AY' AS ψ' y₁) := by ring
            _ = (cutOrientDiff AY' AS ψ' y₂ + cutOrientDiff AY' AS ψ' y₁) +
                (cutOrientDiff AY' AS ψ' y₂ + cutOrientDiff AY' AS ψ' y₁) := by rw [e2]
            _ = 0 := zmod2_add_self _
        exact sub_eq_zero.mp this
      have hconst2 := const_of_nearDiag_eq hN2 hloc2
      obtain ⟨y₀', -⟩ := hψ'.2.1 s
      set K₂ := g_S (ψ' y₀') - (h_Y' y₀' + cutOrientDiff AY' AS ψ' y₀')
      have hK₂ : ∀ y' : Y', g_S (ψ' y') - (h_Y' y' + cutOrientDiff AY' AS ψ' y') = K₂ := fun y' => hconst2 y' y₀'
      refine ⟨fun x => g_S x - K₁, fun x => g_S x - K₂, K₂ - K₁, fun x _ => by ring, fun y _ => ?_, fun y' _ => ?_⟩
      · have := hK₁ y; simp only [zmod2_sub_eq_add] at this ⊢
        calc g_S (ψ y) + K₁ = g_S (ψ y) + (g_S (ψ y) + (h_Y y + cutOrientDiff AY AS ψ y)) := by rw [← this]
          _ = (g_S (ψ y) + g_S (ψ y)) + (h_Y y + cutOrientDiff AY AS ψ y) := by ring
          _ = h_Y y + cutOrientDiff AY AS ψ y := by rw [zmod2_add_self, zero_add]
      · have := hK₂ y'; simp only [zmod2_sub_eq_add] at this ⊢
        calc g_S (ψ' y') + K₂ = g_S (ψ' y') + (g_S (ψ' y') + (h_Y' y' + cutOrientDiff AY' AS ψ' y')) := by rw [← this]
          _ = (g_S (ψ' y') + g_S (ψ' y')) + (h_Y' y' + cutOrientDiff AY' AS ψ' y') := by ring
          _ = h_Y' y' + cutOrientDiff AY' AS ψ' y' := by rw [zmod2_add_self, zero_add]
    · -- Case 2: `S` is non-orientable (`¬ CohRel (w1 AS) 0`), while `Y` and `Y'` are orientable!
      have hdesc1 := exists_w1_cut_descent hS hY hψ hF hP hVX hVX' hXV hX'V' hcl AY AS hNY hhY
      have hdesc2 := exists_w1_cut_descent hS hY' hψ' hF' hP' hVX₂ hVX₂' hXV₂ hX'V₂' hcl₂ AY' AS hNY' hhY'
      have h1 : ∃ g_S : S → ZMod 2,
          (∀ y : Y, g_S (ψ y) = h_Y y + cutOrientDiff AY AS ψ y + (if y ∈ X then 1 else 0)) ∧
          ∃ N : Set (S × S), NearDiag N ∧
            ∀ x₁ x₂, (x₁, x₂) ∈ N → w1 AS x₁ x₂ - cutCocycle ψ V_X V_X' X x₁ x₂ = g_S x₂ - g_S x₁ :=
        hdesc1.resolve_left fun ⟨g, _, N, hN, hg⟩ => hS_ori ⟨g, N, hN, fun x₁ x₂ h => by simp [hg x₁ x₂ h]⟩
      have h2 : ∃ g_S' : S → ZMod 2,
          (∀ y' : Y', g_S' (ψ' y') = h_Y' y' + cutOrientDiff AY' AS ψ' y' + (if y' ∈ X₂ then 1 else 0)) ∧
          ∃ N' : Set (S × S), NearDiag N' ∧
            ∀ x₁ x₂, (x₁, x₂) ∈ N' → w1 AS x₁ x₂ - cutCocycle ψ' V_X₂ V_X₂' X₂ x₁ x₂ = g_S' x₂ - g_S' x₁ :=
        hdesc2.resolve_left fun ⟨g, _, N, hN, hg⟩ => hS_ori ⟨g, N, hN, fun x₁ x₂ h => by simp [hg x₁ x₂ h]⟩
      obtain ⟨g_S, hgS_eq, N₁, hN₁, hgS_cob⟩ := h1
      obtain ⟨g_S', hgS'_eq, N₂, hN₂, hgS'_cob⟩ := h2
      -- Relate `cutCocycle F'` and `cutCocycle F` via `BdCohRel`:
      have hbd1 := arcCocycle_bdCohRel_cutCocycle hS hne hb hl hY hψ hP hVX hVX' hXV hX'V' hcl
      have hbd2 := arcCocycle_bdCohRel_cutCocycle hS hne hb' hl' hY' hψ' hP' hVX₂ hVX₂' hXV₂ hX'V₂' hcl₂
      have hbd_cut : BdCohRel s t (cutCocycle ψ' V_X₂ V_X₂' X₂) (cutCocycle ψ V_X V_X' X) :=
        bdCohRel_trans (bdCohRel_symm hbd2) (bdCohRel_trans hrel hbd1)
      obtain ⟨q, hq_bd, N_q, hNq, hq_cob⟩ := hbd_cut
      -- `g_S - g_S' - q` is locally constant on connected `S`!
      let N3 : Set (S × S) := N₁ ∩ N₂ ∩ N_q
      have hN3 : NearDiag N3 := fun x => Filter.inter_mem (Filter.inter_mem (hN₁ x) (hN₂ x)) (hNq x)
      have hloc3 : ∀ x₁ x₂, (x₁, x₂) ∈ N3 → g_S x₁ - g_S' x₁ - q x₁ = g_S x₂ - g_S' x₂ - q x₂ := fun x₁ x₂ h => by
        have e1 := hgS_cob x₁ x₂ h.1.1
        have e2 := hgS'_cob x₁ x₂ h.1.2
        have e3 := hq_cob x₁ x₂ h.2
        simp only [zmod2_sub_eq_add] at e1 e2 e3
        have hsum : (g_S x₂ + g_S x₁) + (g_S' x₂ + g_S' x₁) = q x₂ + q x₁ := by
          rw [← e1, ← e2, ← e3]
          ring_nf; simp [zmod2_two]
        have : (g_S x₁ - g_S' x₁ - q x₁) - (g_S x₂ - g_S' x₂ - q x₂) = 0 := by
          simp only [zmod2_sub_eq_add]
          calc g_S x₁ + g_S' x₁ + q x₁ + (g_S x₂ + g_S' x₂ + q x₂)
              = ((g_S x₂ + g_S x₁) + (g_S' x₂ + g_S' x₁)) + (q x₂ + q x₁) := by ring
            _ = (q x₂ + q x₁) + (q x₂ + q x₁) := by rw [hsum]
            _ = 0 := zmod2_add_self _
        exact sub_eq_zero.mp this
      have hconst3 := const_of_nearDiag_eq hN3 hloc3
      set K := g_S s - g_S' s - q s
      have hK : ∀ x : S, g_S x - g_S' x - q x = K := fun x => hconst3 x s
      refine ⟨g_S, g_S', K, fun x hx => ?_, fun y hyF => ?_, fun y' hy'F => ?_⟩
      · have := hK x; rw [hq_bd x hx, sub_zero] at this; exact this
      · have hyX : y ∉ X := fun h => hyF (show y ∈ ψ ⁻¹' F from hun ▸ Or.inl h)
        rw [hgS_eq y, ite_eq_right hyX, add_zero]
      · have hy'X : y' ∉ X₂ := fun h => hy'F (show y' ∈ ψ' ⁻¹' F' from hun' ▸ Or.inl h)
        rw [hgS'_eq y', ite_eq_right hy'X, add_zero]
  obtain ⟨g_S, g_S', K, hg_diff, hg_Y, hg_Y'⟩ := hex_g
  refine ⟨C_Y' - C_Y + K, fun x hx CS hCS φS hxCS i j hi hj u₀ u₀' hψu hψ'u δ δ' m m' dir dir' hδ hδ' hmc hmc' hdir hdir' hms hms' => ?_⟩
  have hxF : x ∉ F := fun hxF' => hx.2 (hb ▸ ⟨hxF', hx.1⟩)
  have hxF' : x ∉ F' := fun hxF'' => hx.2 (hb' ▸ ⟨hxF'', hx.1⟩)
  have hCS_bd : CS ⊆ bd S := by obtain ⟨z, -, rfl⟩ := hCS; exact connectedComponentIn_subset _ _
  have hi_bd : holeC a 0 c f i ⊆ bd Y := by
    have hmem : holeC a 0 c f i ∈ cuffs Y := (cuffs_eq_holeC hf) ▸ ⟨i, hi, rfl⟩
    obtain ⟨z, -, hz⟩ := hmem; exact hz ▸ connectedComponentIn_subset _ _
  have hj_bd : holeC a 0 c f' j ⊆ bd Y' := by
    have hmem : holeC a 0 c f' j ∈ cuffs Y' := (cuffs_eq_holeC hf') ▸ ⟨j, hj, rfl⟩
    obtain ⟨z, -, hz⟩ := hmem; exact hz ▸ connectedComponentIn_subset _ _
  set y := (holeParam hf hi (ee u₀)).1
  set y' := (holeParam hf' hj (ee u₀')).1
  have h1 := cutOrientDiff_cuff_mono hY hS hψ hF AY AS hi_bd hCS_bd (holeParam hf hi) φS
    (holeParam hf hi (ee u₀)).2 (hψu.symm ▸ hxF) hδ dir hmc hdir hms rfl
  have h2 := cutOrientDiff_cuff_mono hY' hS hψ' hF' AY' AS hj_bd hCS_bd (holeParam hf' hj) φS
    (holeParam hf' hj (ee u₀')).2 (hψ'u.symm ▸ hxF') hδ' dir' hmc' hdir' hms' rfl
  have hc1 := hCY_const i hi (holeParam hf hi) (fun u hu => holeParam_ee hf hi hu) y (holeParam hf hi (ee u₀)).2
  have hc2 := hCY'_const j hj (holeParam hf' hj) (fun u hu => holeParam_ee hf' hj hu) y' (holeParam hf' hj (ee u₀')).2
  have hg1 := hg_Y y (hψu.symm ▸ hxF)
  have hg2 := hg_Y' y' (hψ'u.symm ▸ hxF')
  have hgd := hg_diff x hx
  rw [hψu] at h1 hg1
  rw [hψ'u] at h2 hg2
  simp only [zmod2_sub_eq_add] at h1 h2 hc1 hc2 hgd ⊢
  -- Eliminate everything in `ZMod 2`:
  have hd1 : (if dir then (0 : ZMod 2) else 1) = cuffSign AS φS x + C_Y + g_S x := by
    calc (if dir then (0 : ZMod 2) else 1)
        = (cuffSign AS φS x + cuffSign AY (holeParam hf hi) y) + cutOrientDiff AY AS ψ y := by
          rw [h1, add_comm (cutOrientDiff AY AS ψ y), add_assoc, zmod2_add_self, add_zero]
      _ = cuffSign AS φS x + (cuffSign AY (holeParam hf hi) y + h_Y y) + (h_Y y + cutOrientDiff AY AS ψ y) := by
          ring_nf; simp [zmod2_two]
      _ = cuffSign AS φS x + C_Y + g_S x := by rw [hc1, ← hg1]
  have hd2 : (if dir' then (0 : ZMod 2) else 1) = cuffSign AS φS x + C_Y' + g_S' x := by
    calc (if dir' then (0 : ZMod 2) else 1)
        = (cuffSign AS φS x + cuffSign AY' (holeParam hf' hj) y') + cutOrientDiff AY' AS ψ' y' := by
          rw [h2, add_comm (cutOrientDiff AY' AS ψ' y'), add_assoc, zmod2_add_self, add_zero]
      _ = cuffSign AS φS x + (cuffSign AY' (holeParam hf' hj) y' + h_Y' y') + (h_Y' y' + cutOrientDiff AY' AS ψ' y') := by
          ring_nf; simp [zmod2_two]
      _ = cuffSign AS φS x + C_Y' + g_S' x := by rw [hc2, ← hg2]
  rw [hd1, hd2]
  calc (cuffSign AS φS x + C_Y + g_S x) + (cuffSign AS φS x + C_Y' + g_S' x)
      = C_Y' + C_Y + (g_S x + g_S' x) := by ring_nf; simp [zmod2_two]
    _ = C_Y' + C_Y + K := by rw [hgd]

end HoleParamAndDir

end GraphMinor.GHR18
