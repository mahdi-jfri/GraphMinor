module

public import GraphMinor.GHR18.Transverse

/-!
# Proper 1-manifolds, rectangle band-surgery, and parity reduction (GHR18 Theorem 2.6, Step 1)

This file develops the surgery framework for proper 1-manifolds on a surface `S`:

1. **Path & loop primitives** (`subArc`, `conc2`, `rev`, `isOArc_of_loop`, `oArc_rebase`,
   `subarc_param_interval`): basic concatenation, reversal, rebasing, and interval-extraction
   lemmas for `I`-arcs and `O`-arcs.
2. **`ProperManifold S s t`**: a proper `I`-arc `P₀` with ends `s ≠ t` together with a finite
   list `Os` of pairwise disjoint interior `O`-arcs disjoint from `P₀`, equipped with:
   - total union `M.U` (closed, `M.U ∩ bd S = {s, t}`);
   - `M.exists_crossingCocycle`: crossing cocycle and `HasLocalTwoSides` on `M.U`;
   - `M.w1Total AS`: total Stiefel-Whitney integral `cocInt (w1 AS) γ₀ + ∑ cocInt (w1 AS) α_k` in
     `ZMod 2`.
3. **Master `rectangle_surgery`**: given an embedded closed rectangle
   `Δ = f '' (Icc x₁ x₂ ×ℂ Icc (-d) d) ⊆ (bd S)ᶜ` meeting `M.U` solely along its two vertical
   sides `{x₁} × [-d, d]` and `{x₂} × [-d, d]`, replaces those two vertical sides by the two
   horizontal sides `[x₁, x₂] × {±d}` to produce a new `ProperManifold` `M'` with:
   - `M'.U \ Δ = M.U \ Δ` and `M'.U ∩ Δ = T ∪ B`;
   - `M'.w1Total AS = M.w1Total AS`;
   - `BdCohRel s t ω' ω` for any crossing cocycles `ω', ω`;
   - if the two vertical sides lie in different components of `M`, then `M'.Os.length + 1 = M.Os.length`.
   This single surgery theorem powers BOTH parity reduction (`parity_surgery`, this file) and
   component merging (`BandSum.lean`).
4. **Parity reduction (`parity_surgery`)**: eliminates pairs of consecutive crossings on every
   strip box `sb.box i`, reducing `M` to a transverse `ProperManifold` with at most `1` crossing
   on every `Q i`.
-/

@[expose] public section

namespace GraphMinor.GHR18

open Set Topology Function Metric Complex GraphMinor.Surface

variable {S : Type} [TopologicalSpace S]

/-! ### Section 1: Path, concatenation, and loop utilities -/

section PathUtils

/-- Linear restriction of a curve `γ : ℝ → S` to `[a, b]`, reparameterized on `[0, 1]`. -/
def subArc (γ : ℝ → S) (a b : ℝ) : ℝ → S := fun r => γ (lin a b r)

omit [TopologicalSpace S] in
theorem subArc_zero (γ : ℝ → S) (a b : ℝ) : subArc γ a b 0 = γ a := by
  simp [subArc, lin_zero]

omit [TopologicalSpace S] in
theorem subArc_one (γ : ℝ → S) (a b : ℝ) : subArc γ a b 1 = γ b := by
  simp [subArc, lin_one]

theorem lin_mapsTo_Icc {a b : ℝ} (hab : a ≤ b) : MapsTo (lin a b) (Icc 0 1) (Icc a b) := fun r hr =>
  ⟨by simp only [lin]; nlinarith [hr.1, hab], by simp only [lin]; nlinarith [hr.2, hab]⟩

theorem continuousOn_subArc {γ : ℝ → S} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) : ContinuousOn (subArc γ a b) (Icc 0 1) :=
  hγ.comp (continuousOn_lin a b) (lin_mapsTo_Icc hab)

omit [TopologicalSpace S] in
theorem injOn_subArc {γ : ℝ → S} {a b : ℝ} (hab : a < b) (hγ : InjOn γ (Icc a b)) :
    InjOn (subArc γ a b) (Icc 0 1) := fun r₁ hr₁ r₂ hr₂ he => by
  have h1 := hγ (lin_mapsTo_Icc hab.le hr₁) (lin_mapsTo_Icc hab.le hr₂) he
  simp only [lin] at h1
  nlinarith

omit [TopologicalSpace S] in
theorem subArc_image {γ : ℝ → S} {a b : ℝ} (hab : a ≤ b) :
    subArc γ a b '' Icc 0 1 = γ '' Icc a b := by
  ext y; constructor
  · rintro ⟨r, hr, rfl⟩; exact ⟨lin a b r, lin_mapsTo_Icc hab hr, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    rcases hab.eq_or_lt with rfl | hlt
    · have hxa : x = a := le_antisymm hx.2 hx.1
      exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [subArc, lin_zero, hxa]⟩
    · let r := (x - a) / (b - a)
      refine ⟨r, ⟨div_nonneg (sub_nonneg.mpr hx.1) (sub_pos.mpr hlt).le,
        (div_le_one (sub_pos.mpr hlt)).mpr (sub_le_sub_right hx.2 a)⟩, ?_⟩
      simp only [subArc, lin, r]; congr 1; field_simp [(sub_pos.mpr hlt).ne']; ring

omit [TopologicalSpace S] in
theorem conc2_zero (γ₁ γ₂ : ℝ → S) : conc2 γ₁ γ₂ 0 = γ₁ 0 := by
  simp [conc2]

omit [TopologicalSpace S] in
theorem conc2_one (γ₁ γ₂ : ℝ → S) : conc2 γ₁ γ₂ 1 = γ₂ 1 := by
  unfold conc2; rw [ite_eq_right (by norm_num : ¬ (1 : ℝ) ≤ 1 / 2)]; norm_num

omit [TopologicalSpace S] in
theorem conc2_image {γ₁ γ₂ : ℝ → S} (h12 : γ₁ 1 = γ₂ 0) :
    conc2 γ₁ γ₂ '' Icc 0 1 = γ₁ '' Icc 0 1 ∪ γ₂ '' Icc 0 1 := by
  ext y; constructor
  · rintro ⟨r, hr, rfl⟩
    dsimp only [conc2]; split_ifs with h
    · exact Or.inl ⟨2 * r, ⟨by linarith [hr.1], by linarith⟩, rfl⟩
    · exact Or.inr ⟨2 * r - 1, ⟨by linarith, by linarith [hr.2]⟩, rfl⟩
  · rintro (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩)
    · refine ⟨r / 2, ⟨by linarith [hr.1], by linarith [hr.2]⟩, ?_⟩
      simp only [conc2, ite_eq_left (show r / 2 ≤ 1 / 2 by linarith [hr.2])]
      congr 1; ring
    · rcases hr.1.eq_or_lt with rfl | hr0
      · exact ⟨1 / 2, ⟨by norm_num, by norm_num⟩, by simp [conc2, h12]⟩
      · refine ⟨(r + 1) / 2, ⟨by linarith, by linarith [hr.2]⟩, ?_⟩
        simp only [conc2, ite_eq_right (show ¬ (r + 1) / 2 ≤ 1 / 2 by linarith)]
        congr 1; ring

omit [TopologicalSpace S] in
theorem conc2_injOn_Icc {γ₁ γ₂ : ℝ → S} (h₁ : InjOn γ₁ (Icc 0 1)) (h₂ : InjOn γ₂ (Icc 0 1))
    (hmeet : ∀ r₁ ∈ Icc (0 : ℝ) 1, ∀ r₂ ∈ Icc (0 : ℝ) 1, γ₁ r₁ = γ₂ r₂ → r₁ = 1 ∧ r₂ = 0) :
    InjOn (conc2 γ₁ γ₂) (Icc 0 1) := by
  intro r₁ hr₁ r₂ hr₂ he
  dsimp only [conc2] at he
  split_ifs at he with h1 h2 h2'
  · linarith [h₁ ⟨by linarith [hr₁.1], by linarith⟩ ⟨by linarith [hr₂.1], by linarith⟩ he]
  · obtain ⟨ha, hb⟩ := hmeet (2 * r₁) ⟨by linarith [hr₁.1], by linarith⟩ (2 * r₂ - 1) ⟨by linarith, by linarith [hr₂.2]⟩ he
    linarith
  · obtain ⟨ha, hb⟩ := hmeet (2 * r₂) ⟨by linarith [hr₂.1], by linarith⟩ (2 * r₁ - 1) ⟨by linarith, by linarith [hr₁.2]⟩ he.symm
    linarith
  · linarith [h₂ ⟨by linarith, by linarith [hr₁.2]⟩ ⟨by linarith, by linarith [hr₂.2]⟩ he]

omit [TopologicalSpace S] in
theorem conc2_injOn_Ico {γ₁ γ₂ : ℝ → S} (h₁ : InjOn γ₁ (Icc 0 1)) (h₂ : InjOn γ₂ (Icc 0 1))
    (hmeet : ∀ r₁ ∈ Icc (0 : ℝ) 1, ∀ r₂ ∈ Icc (0 : ℝ) 1, γ₁ r₁ = γ₂ r₂ →
      (r₁ = 1 ∧ r₂ = 0) ∨ (r₁ = 0 ∧ r₂ = 1)) :
    InjOn (conc2 γ₁ γ₂) (Ico 0 1) := by
  intro r₁ hr₁ r₂ hr₂ he
  dsimp only [conc2] at he
  split_ifs at he with h1 h2 h2'
  · linarith [h₁ ⟨by linarith [hr₁.1], by linarith⟩ ⟨by linarith [hr₂.1], by linarith⟩ he]
  · rcases hmeet (2 * r₁) ⟨by linarith [hr₁.1], by linarith⟩ (2 * r₂ - 1) ⟨by linarith, by linarith [hr₂.2]⟩ he with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · linarith
    · linarith [hr₂.2]
  · rcases hmeet (2 * r₂) ⟨by linarith [hr₂.1], by linarith⟩ (2 * r₁ - 1) ⟨by linarith, by linarith [hr₁.2]⟩ he.symm with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · linarith
    · linarith [hr₁.2]
  · linarith [h₂ ⟨by linarith, by linarith [hr₁.2]⟩ ⟨by linarith, by linarith [hr₂.2]⟩ he]

theorem continuousOn_rev {γ : ℝ → S} (hγ : ContinuousOn γ (Icc 0 1)) :
    ContinuousOn (fun r => γ (1 - r)) (Icc 0 1) :=
  hγ.comp (continuous_const.sub continuous_id).continuousOn fun r hr => ⟨by linarith [hr.2], by linarith [hr.1]⟩

omit [TopologicalSpace S] in
theorem injOn_rev {γ : ℝ → S} (hγ : InjOn γ (Icc 0 1)) :
    InjOn (fun r => γ (1 - r)) (Icc 0 1) := fun r₁ hr₁ r₂ hr₂ he => by
  have := hγ ⟨by linarith [hr₁.2], by linarith [hr₁.1]⟩ ⟨by linarith [hr₂.2], by linarith [hr₂.1]⟩ he
  linarith

omit [TopologicalSpace S] in
theorem rev_image (γ : ℝ → S) : (fun r => γ (1 - r)) '' Icc 0 1 = γ '' Icc 0 1 := by
  ext y; constructor
  · rintro ⟨r, hr, rfl⟩; exact ⟨1 - r, ⟨by linarith [hr.2], by linarith [hr.1]⟩, rfl⟩
  · rintro ⟨r, hr, rfl⟩; exact ⟨1 - r, ⟨by linarith [hr.2], by linarith [hr.1]⟩, by simp⟩

theorem cocInt_rev_zmod2 {φ : S → S → ZMod 2} (hφ : IsCoc φ) {γ : ℝ → S}
    (hγ : ContinuousOn γ (Icc 0 1)) :
    cocInt φ (fun r => γ (1 - r)) = cocInt φ γ := by
  rw [cocInt_rev hφ hγ]
  have hneg : ∀ x : ZMod 2, -x = x := by decide
  exact hneg _

/-- Splitting `cocInt φ γ` into two subintervals `[0, u]` and `[u, 1]`. -/
theorem cocInt_split_two {A : Type} [AddCommGroup A] {φ : S → S → A} (hφ : IsCoc φ)
    {γ : ℝ → S} (hγc : ContinuousOn γ (Icc 0 1)) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    cocInt φ γ = cocInt φ (subArc γ 0 u) + cocInt φ (subArc γ u 1) := by
  let γ₁ := subArc γ 0 u
  let γ₂ := subArc γ u 1
  have h1c : ContinuousOn γ₁ (Icc 0 1) := continuousOn_subArc hu0.le (hγc.mono (Icc_subset_Icc_right hu1.le))
  have h2c : ContinuousOn γ₂ (Icc 0 1) := continuousOn_subArc hu1.le (hγc.mono (Icc_subset_Icc_left hu0.le))
  have h12 : γ₁ 1 = γ₂ 0 := by simp [γ₁, γ₂, subArc_one, subArc_zero]
  let ρ : ℝ → ℝ := fun r => if r ≤ 1 / 2 then lin 0 u (2 * r) else lin u 1 (2 * r - 1)
  have hρc : ContinuousOn ρ (Icc 0 1) := by
    have hcov : Icc (0 : ℝ) 1 = Icc 0 (1 / 2) ∪ Icc (1 / 2) 1 := by
      ext r; simp only [mem_Icc, mem_union]; constructor
      · intro hr; by_cases h : r ≤ 1 / 2
        · exact Or.inl ⟨hr.1, h⟩
        · exact Or.inr ⟨by linarith, hr.2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact ⟨by linarith, by linarith⟩
    rw [hcov]
    refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
    · exact ((continuousOn_lin 0 u).comp (show ContinuousOn (fun r : ℝ => 2 * r) (Icc 0 (1 / 2)) by fun_prop)
        (fun r hr => ⟨by linarith [hr.1], by linarith [hr.2]⟩)).congr fun r hr =>
        by dsimp only [ρ, Function.comp]; exact ite_eq_left hr.2
    · exact ((continuousOn_lin u 1).comp (show ContinuousOn (fun r : ℝ => 2 * r - 1) (Icc (1 / 2) 1) by fun_prop)
        (fun r hr => ⟨by linarith [hr.1], by linarith [hr.2]⟩)).congr fun r hr => by
        dsimp only [ρ, Function.comp]
        by_cases h : r ≤ 1 / 2
        · have he : r = 1 / 2 := le_antisymm h hr.1; rw [ite_eq_left h, he]; norm_num [lin]
        · exact ite_eq_right h
  have hρm : MapsTo ρ (Icc 0 1) (Icc 0 1) := fun r hr => by
    dsimp only [ρ]; split_ifs with h
    · exact Icc_subset_Icc_right hu1.le (lin_mapsTo_Icc hu0.le ⟨by linarith [hr.1], by linarith⟩)
    · exact Icc_subset_Icc_left hu0.le (lin_mapsTo_Icc hu1.le ⟨by linarith, by linarith [hr.2]⟩)
  have hρ0 : ρ 0 = 0 := by simp [ρ, lin]
  have hρ1 : ρ 1 = 1 := by unfold ρ; rw [ite_eq_right (by norm_num : ¬ (1 : ℝ) ≤ 1 / 2)]; norm_num [lin]
  have heq : ∀ r ∈ Icc (0 : ℝ) 1, (γ ∘ ρ) r = conc2 γ₁ γ₂ r := fun r _ => by
    simp only [Function.comp, ρ, conc2, γ₁, γ₂, subArc]
    split_ifs <;> rfl
  rw [← cocInt_reparam hφ hγc hρc hρm hρ0 hρ1,
    cocInt_congr hφ (hγc.comp hρc hρm) (continuousOn_conc2 h1c h2c h12) heq,
    cocInt_conc2 hφ h1c h2c h12]

/-- Splitting `cocInt φ γ` into five subintervals `[0, u₁], [u₁, v₁], [v₁, u₂], [u₂, v₂], [v₂, 1]`. -/
theorem cocInt_split_five {A : Type} [AddCommGroup A] {φ : S → S → A} (hφ : IsCoc φ)
    {γ : ℝ → S} (hγc : ContinuousOn γ (Icc 0 1))
    {u₁ v₁ u₂ v₂ : ℝ} (hu₁0 : 0 < u₁) (huv₁ : u₁ < v₁) (hv₁u₂ : v₁ < u₂) (huv₂ : u₂ < v₂) (hv₂1 : v₂ < 1) :
    cocInt φ γ =
      cocInt φ (subArc γ 0 u₁) + cocInt φ (subArc γ u₁ v₁) + cocInt φ (subArc γ v₁ u₂) +
      cocInt φ (subArc γ u₂ v₂) + cocInt φ (subArc γ v₂ 1) := by
  have h1 := cocInt_split_three hφ hγc hu₁0 huv₁ (by linarith)
  have h2 := cocInt_split_three hφ
    (continuousOn_subArc (show v₁ ≤ 1 by linarith) (hγc.mono (Icc_subset_Icc_left (by linarith))))
    (show 0 < (u₂ - v₁) / (1 - v₁) from div_pos (sub_pos.mpr hv₁u₂) (by linarith))
    (div_lt_div_of_pos_right (sub_lt_sub_right huv₂ v₁) (by linarith))
    ((div_lt_one (by linarith)).mpr (sub_lt_sub_right hv₂1 v₁))
  have hEq1 : ∀ r ∈ Icc (0 : ℝ) 1, subArc γ v₁ 1 (lin 0 ((u₂ - v₁) / (1 - v₁)) r) = subArc γ v₁ u₂ r := fun r _ => by
    simp only [subArc, lin]; congr 1; field_simp [(show 1 - v₁ ≠ 0 by linarith)]; ring
  have hEq2 : ∀ r ∈ Icc (0 : ℝ) 1, subArc γ v₁ 1 (lin ((u₂ - v₁) / (1 - v₁)) ((v₂ - v₁) / (1 - v₁)) r) = subArc γ u₂ v₂ r := fun r _ => by
    simp only [subArc, lin]; congr 1; field_simp [(show 1 - v₁ ≠ 0 by linarith)]; ring
  have hEq3 : ∀ r ∈ Icc (0 : ℝ) 1, subArc γ v₁ 1 (lin ((v₂ - v₁) / (1 - v₁)) 1 r) = subArc γ v₂ 1 r := fun r _ => by
    simp only [subArc, lin]; congr 1; field_simp [(show 1 - v₁ ≠ 0 by linarith)]; ring
  have h1c : ContinuousOn (subArc γ v₁ u₂) (Icc 0 1) := continuousOn_subArc hv₁u₂.le (hγc.mono (Icc_subset_Icc (by linarith) (by linarith)))
  have h2c : ContinuousOn (subArc γ u₂ v₂) (Icc 0 1) := continuousOn_subArc huv₂.le (hγc.mono (Icc_subset_Icc (by linarith) (by linarith)))
  have h3c : ContinuousOn (subArc γ v₂ 1) (Icc 0 1) := continuousOn_subArc hv₂1.le (hγc.mono (Icc_subset_Icc_left (by linarith)))
  have hc1 := cocInt_congr hφ (h1c.congr hEq1) h1c hEq1
  have hc2 := cocInt_congr hφ (h2c.congr hEq2) h2c hEq2
  have hc3 := cocInt_congr hφ (h3c.congr hEq3) h3c hEq3
  change cocInt φ γ = cocInt φ (subArc γ 0 u₁) + (cocInt φ (subArc γ u₁ v₁) + cocInt φ (subArc γ v₁ 1)) at h1
  rw [h1, h2, hc1, hc2, hc3]; abel

/-- Construct `IsLineWithEnds P s t` from an injective continuous parameterization on `[0, 1]`. -/
theorem isLineWithEnds_of_param [T2Space S] {γ : ℝ → S} {s t : S} {P : Set S}
    (hγc : ContinuousOn γ (Icc 0 1)) (hγi : InjOn γ (Icc 0 1))
    (hγ0 : γ 0 = s) (hγ1 : γ 1 = t) (hγim : γ '' Icc 0 1 = P) :
    IsLineWithEnds P s t := by
  let g : unitInterval → P := fun x => ⟨γ x.1, hγim ▸ ⟨x.1, x.2, rfl⟩⟩
  have hgc : Continuous g := Continuous.subtype_mk (hγc.comp_continuous continuous_subtype_val fun x => x.2) _
  have hgb : Bijective g := ⟨fun x y h => Subtype.ext (hγi x.2 y.2 (congrArg Subtype.val h)),
    fun ⟨y, hy⟩ => by obtain ⟨r, hr, hre⟩ := hγim ▸ hy; exact ⟨⟨r, hr⟩, Subtype.ext hre⟩⟩
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g hgb) hgc, hγ0, hγ1⟩

/-- Construct `IsOArc O` from a continuous loop `α : ℝ → S` on `[0, 1]` with `α 0 = α 1`
that is injective on `[0, 1)`. -/
theorem isOArc_of_loop [T2Space S] {α : ℝ → S} {O : Set S}
    (hαc : ContinuousOn α (Icc 0 1)) (hαi : InjOn α (Ico 0 1))
    (hα01 : α 0 = α 1) (hαim : α '' Icc 0 1 = O) :
    IsOArc O := by
  let αp : ℝ → S := fun x => α (Int.fract x)
  have hαp_per : ∀ x : ℝ, αp (x + 1) = αp x := fun x => by simp [αp]
  have hαp_eq_on : ∀ (n : ℤ) (x : ℝ), x ∈ Icc (n : ℝ) ((n : ℝ) + 1) → αp x = α (x - n) := fun n x hx => by
    rcases hx.2.eq_or_lt with rfl | hlt
    · have h1 : Int.fract ((n : ℝ) + 1) = 0 := by rw [Int.fract_add_one, Int.fract_intCast]
      simp only [αp, h1, add_sub_cancel_left, hα01]
    · have hfl : ⌊x⌋ = n := Int.floor_eq_iff.mpr ⟨hx.1, hlt⟩
      simp only [αp, Int.fract, hfl]
  have hαp_c : Continuous αp := by
    rw [continuous_iff_continuousAt]
    intro x
    let n : ℤ := ⌊x⌋
    have hn1 : (n : ℝ) ≤ x := Int.floor_le x
    have hn2 : x < (n : ℝ) + 1 := Int.lt_floor_add_one x
    let K1 : Set ℝ := Icc ((n : ℝ) - 1) (n : ℝ)
    let K2 : Set ℝ := Icc (n : ℝ) ((n : ℝ) + 1)
    have hc1 : ContinuousOn αp K1 :=
      (hαc.comp (show ContinuousOn (fun y : ℝ => y - ((n : ℝ) - 1)) K1 by fun_prop)
        (fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩)).congr fun y hy => by
        have hy' : y ∈ Icc (((n - 1 : ℤ) : ℝ)) (((n - 1 : ℤ) : ℝ) + 1) := by
          push_cast; exact ⟨hy.1, by linarith [hy.2]⟩
        have e := hαp_eq_on (n - 1) y hy'
        rw [e]; push_cast; rfl
    have hc2 : ContinuousOn αp K2 :=
      (hαc.comp (show ContinuousOn (fun y : ℝ => y - (n : ℝ)) K2 by fun_prop)
        (fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩)).congr fun y hy => hαp_eq_on n y hy
    have hcu : ContinuousOn αp (K1 ∪ K2) := hc1.union_of_isClosed hc2 isClosed_Icc isClosed_Icc
    have hmem : K1 ∪ K2 ∈ 𝓝 x := by
      refine Filter.mem_of_superset (isOpen_Ioo.mem_nhds (show x ∈ Ioo ((n : ℝ) - 1) ((n : ℝ) + 1) from ⟨by linarith, hn2⟩)) ?_
      intro y hy
      by_cases hyn : y ≤ n
      · exact Or.inl ⟨hy.1.le, hyn⟩
      · exact Or.inr ⟨le_of_not_ge hyn, hy.2.le⟩
    exact hcu.continuousAt hmem
  have hαp_mem : ∀ x : ℝ, αp x ∈ O := fun x =>
    hαim ▸ ⟨Int.fract x, ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩, rfl⟩
  let g : ℝ → O := fun x => ⟨αp x, hαp_mem x⟩
  have hgc : Continuous g := Continuous.subtype_mk hαp_c _
  have hgp : ∀ x : ℝ, g (x + 1) = g x := fun x => Subtype.ext (hαp_per x)
  obtain ⟨G, hGc, hGee⟩ := exists_circle_descend hgc hgp
  have hGb : Bijective G := by
    refine ⟨fun z₁ z₂ he => ?_, fun ⟨y, hy⟩ => ?_⟩
    · obtain ⟨x₁, rfl⟩ := ee_surjective z₁
      obtain ⟨x₂, rfl⟩ := ee_surjective z₂
      rw [hGee x₁, hGee x₂] at he
      have hval : α (Int.fract x₁) = α (Int.fract x₂) := congrArg Subtype.val he
      have hfr : Int.fract x₁ = Int.fract x₂ :=
        hαi ⟨Int.fract_nonneg x₁, Int.fract_lt_one x₁⟩ ⟨Int.fract_nonneg x₂, Int.fract_lt_one x₂⟩ hval
      exact ee_eq_iff.mpr ⟨⌊x₁⌋ - ⌊x₂⌋, by
        have h1 := Int.floor_add_fract x₁
        have h2 := Int.floor_add_fract x₂
        push_cast; linarith⟩
    · obtain ⟨r, hr, rfl⟩ := hαim ▸ hy
      refine ⟨ee r, ?_⟩
      rw [hGee r]; apply Subtype.ext
      rcases hr.2.eq_or_lt with rfl | hlt
      · change αp 1 = α 1; simp [αp, hα01]
      · change αp r = α r; simp [αp, Int.fract_eq_self.mpr ⟨hr.1, hlt⟩]
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective G hGb) hGc⟩

/-- Cyclic rebase of a loop `α` on `[0, 1]` to start at `α c` (`0 < c < 1`), preserving image,
injectivity on `[0, 1)`, and `cocInt` for any cocycle in any `AddCommGroup`. -/
theorem oArc_rebase {α : ℝ → S}
    (hαc : ContinuousOn α (Icc 0 1)) (hαi : InjOn α (Ico 0 1)) (hα01 : α 0 = α 1)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    let α' := conc2 (subArc α c 1) (subArc α 0 c)
    ContinuousOn α' (Icc 0 1) ∧ InjOn α' (Ico 0 1) ∧ α' 0 = α' 1 ∧ α' 0 = α c ∧
    α' '' Icc 0 1 = α '' Icc 0 1 ∧
    ∀ {A : Type} [AddCommGroup A] {φ : S → S → A}, IsCoc φ → cocInt φ α' = cocInt φ α := by
  intro α'
  have h1c : ContinuousOn (subArc α c 1) (Icc 0 1) := continuousOn_subArc hc1.le (hαc.mono (Icc_subset_Icc_left hc0.le))
  have h2c : ContinuousOn (subArc α 0 c) (Icc 0 1) := continuousOn_subArc hc0.le (hαc.mono (Icc_subset_Icc_right hc1.le))
  have h12 : subArc α c 1 1 = subArc α 0 c 0 := by simp [subArc_one, subArc_zero, hα01]
  have h1i : InjOn (subArc α c 1) (Icc 0 1) := fun r₁ hr₁ r₂ hr₂ he => by
    have m1 := lin_mapsTo_Icc hc1.le hr₁
    have m2 := lin_mapsTo_Icc hc1.le hr₂
    simp only [subArc] at he
    have hlin_eq : lin c 1 r₁ = lin c 1 r₂ := by
      rcases m1.2.eq_or_lt with h1e | h1lt <;> rcases m2.2.eq_or_lt with h2e | h2lt
      · exact h1e.trans h2e.symm
      · rw [h1e, ← hα01] at he
        have := hαi ⟨le_rfl, zero_lt_one⟩ ⟨by linarith [m2.1], h2lt⟩ he; linarith [m2.1]
      · rw [h2e, ← hα01] at he
        have := hαi ⟨by linarith [m1.1], h1lt⟩ ⟨le_rfl, zero_lt_one⟩ he; linarith [m1.1]
      · exact hαi ⟨by linarith [m1.1], h1lt⟩ ⟨by linarith [m2.1], h2lt⟩ he
    simp only [lin] at hlin_eq; nlinarith
  have h2i : InjOn (subArc α 0 c) (Icc 0 1) :=
    injOn_subArc hc0 (hαi.mono (show Icc 0 c ⊆ Ico 0 1 from fun x hx => ⟨hx.1, hx.2.trans_lt hc1⟩))
  have hmeet : ∀ r₁ ∈ Icc (0 : ℝ) 1, ∀ r₂ ∈ Icc (0 : ℝ) 1,
      subArc α c 1 r₁ = subArc α 0 c r₂ → (r₁ = 1 ∧ r₂ = 0) ∨ (r₁ = 0 ∧ r₂ = 1) := by
    intro r₁ hr₁ r₂ hr₂ he
    have m1 := lin_mapsTo_Icc hc1.le hr₁
    have m2 := lin_mapsTo_Icc hc0.le hr₂
    simp only [subArc] at he
    rcases m1.2.eq_or_lt with h1e | h1lt
    · rw [h1e, ← hα01] at he
      have h0 := hαi ⟨le_rfl, zero_lt_one⟩ ⟨m2.1, m2.2.trans_lt hc1⟩ he
      left; constructor <;> simp only [lin] at h1e h0 <;> nlinarith
    · have hEq := hαi ⟨by linarith [m1.1], h1lt⟩ ⟨m2.1, m2.2.trans_lt hc1⟩ he
      have hc_eq : lin c 1 r₁ = c := le_antisymm (hEq ▸ m2.2) m1.1
      have hc_eq2 : lin 0 c r₂ = c := hEq.symm.trans hc_eq
      right; constructor <;> simp only [lin] at hc_eq hc_eq2 <;> nlinarith
  refine ⟨continuousOn_conc2 h1c h2c h12, conc2_injOn_Ico h1i h2i hmeet,
    by simp [α', conc2_zero, conc2_one, subArc_zero, subArc_one],
    by simp [α', conc2_zero, subArc_zero], ?_, ?_⟩
  · rw [conc2_image h12, subArc_image hc1.le, subArc_image hc0.le, ← image_union]
    congr 1; ext x; simp only [mem_union, mem_Icc]; constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact ⟨by linarith, by linarith⟩
    · intro hx; by_cases h : c ≤ x
      · exact Or.inl ⟨h, hx.2⟩
      · exact Or.inr ⟨hx.1, le_of_not_ge h⟩
  · intro A _ φ hφ
    rw [cocInt_conc2 hφ h1c h2c h12, add_comm, ← cocInt_split_two hφ hαc hc0 hc1]

/-- A continuous injective function `τ : ℝ → ℝ` on a closed interval `[a, b]` (`a < b`) is
either strictly increasing or strictly decreasing on `[a, b]`. -/
theorem continuousOn_strictMono_or_strictAnti {τ : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hc : ContinuousOn τ (Icc a b)) (hi : InjOn τ (Icc a b)) :
    StrictMonoOn τ (Icc a b) ∨ StrictAntiOn τ (Icc a b) := by
  have hne : τ a ≠ τ b := fun h => hab.ne (hi ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ h)
  have hmid : ∀ {x y z : ℝ}, x ∈ Icc a b → y ∈ Icc a b → z ∈ Icc a b →
      x < y → y < z → τ x < τ z → τ x < τ y ∧ τ y < τ z := by
    intro x y z hx hy hz hxy hyz hlt
    have hxy_ne : τ x ≠ τ y := fun h => hxy.ne (hi hx hy h)
    have hyz_ne : τ y ≠ τ z := fun h => hyz.ne (hi hy hz h)
    constructor
    · by_contra hge; push Not at hge
      have hlt' : τ y < τ x := lt_of_le_of_ne hge hxy_ne.symm
      obtain ⟨w, hw, hwe⟩ := intermediate_value_Icc hyz.le (hc.mono (Icc_subset_Icc hy.1 hz.2)) ⟨hlt'.le, hlt.le⟩
      have hwx : w = x := hi ⟨by linarith [hy.1, hw.1], by linarith [hw.2, hz.2]⟩ hx hwe
      linarith [hw.1]
    · by_contra hge; push Not at hge
      have hlt' : τ z < τ y := lt_of_le_of_ne hge hyz_ne.symm
      obtain ⟨w, hw, hwe⟩ := intermediate_value_Icc hxy.le (hc.mono (Icc_subset_Icc hx.1 hy.2)) ⟨hlt.le, hlt'.le⟩
      have hwz : w = z := hi ⟨by linarith [hx.1, hw.1], by linarith [hw.2, hy.2]⟩ hz hwe
      linarith [hw.2]
  have hmid_rev : ∀ {x y z : ℝ}, x ∈ Icc a b → y ∈ Icc a b → z ∈ Icc a b →
      x < y → y < z → τ z < τ x → τ z < τ y ∧ τ y < τ x := by
    intro x y z hx hy hz hxy hyz hlt
    have hxy_ne : τ x ≠ τ y := fun h => hxy.ne (hi hx hy h)
    have hyz_ne : τ y ≠ τ z := fun h => hyz.ne (hi hy hz h)
    constructor
    · by_contra hge; push Not at hge
      have hlt' : τ y < τ z := lt_of_le_of_ne hge hyz_ne
      obtain ⟨w, hw, hwe⟩ := intermediate_value_Icc' hxy.le (hc.mono (Icc_subset_Icc hx.1 hy.2)) ⟨hlt'.le, hlt.le⟩
      have hwz : w = z := hi ⟨by linarith [hx.1, hw.1], by linarith [hw.2, hy.2]⟩ hz hwe
      linarith [hw.2]
    · by_contra hge; push Not at hge
      have hlt' : τ x < τ y := lt_of_le_of_ne hge hxy_ne
      obtain ⟨w, hw, hwe⟩ := intermediate_value_Icc' hyz.le (hc.mono (Icc_subset_Icc hy.1 hz.2)) ⟨hlt.le, hlt'.le⟩
      have hwx : w = x := hi ⟨by linarith [hy.1, hw.1], by linarith [hw.2, hz.2]⟩ hx hwe
      linarith [hw.1]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · left; intro x hx y hy hxy
    have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩; have hb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
    rcases hx.1.eq_or_lt with rfl | hax
    · rcases hy.2.eq_or_lt with rfl | hyb
      · exact hlt
      · exact (hmid ha hy hb hxy hyb hlt).1
    · rcases hy.2.eq_or_lt with rfl | hyb
      · exact (hmid ha hx hb hax hxy hlt).2
      · exact (hmid hx hy hb hxy hyb (hmid ha hx hb hax (hxy.trans hyb) hlt).2).1
  · right; intro x hx y hy hxy
    have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩; have hb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
    rcases hx.1.eq_or_lt with rfl | hax
    · rcases hy.2.eq_or_lt with rfl | hyb
      · exact hgt
      · exact (hmid_rev ha hy hb hxy hyb hgt).2
    · rcases hy.2.eq_or_lt with rfl | hyb
      · exact (hmid_rev ha hx hb hax hxy hgt).1
      · exact (hmid_rev hx hy hb hxy hyb (hmid_rev ha hx hb hax (hxy.trans hyb) hgt).1).2

/-- Extracting the parameter subinterval `[u, v] ⊆ (0, 1)` of an embedded sub-arc `L = σ '' [-d, d]`
lying inside `γ '' (0, 1)` for a continuous injective curve `γ` on `[0, 1]`. -/
theorem subarc_param_interval [T2Space S] {γ : ℝ → S}
    (hγc : ContinuousOn γ (Icc 0 1)) (hγi : InjOn γ (Icc 0 1))
    {σ : ℝ → S} {d : ℝ} (hd : 0 < d)
    (hσc : ContinuousOn σ (Icc (-d) d)) (hσi : InjOn σ (Icc (-d) d))
    (hsub : σ '' Icc (-d) d ⊆ γ '' Ioo 0 1) :
    ∃ u v : ℝ, 0 < u ∧ u < v ∧ v < 1 ∧
      γ '' Icc u v = σ '' Icc (-d) d ∧
      ((γ u = σ (-d) ∧ γ v = σ d) ∨ (γ u = σ d ∧ γ v = σ (-d))) := by
  obtain ⟨ginv, hginvc, hginvl⟩ := exists_inv_of_compactOn isCompact_Icc hγc hγi
  let τ : ℝ → ℝ := ginv ∘ σ
  have hσ_in_im : MapsTo σ (Icc (-d) d) (γ '' Icc 0 1) := fun t ht =>
    image_mono Ioo_subset_Icc_self (hsub ⟨t, ht, rfl⟩)
  have hτc : ContinuousOn τ (Icc (-d) d) := hginvc.comp hσc hσ_in_im
  have hγτ : ∀ t ∈ Icc (-d) d, τ t ∈ Ioo (0 : ℝ) 1 ∧ γ (τ t) = σ t := fun t ht => by
    obtain ⟨r, hr, hre⟩ := hsub ⟨t, ht, rfl⟩
    have htr : τ t = r := by show ginv (σ t) = r; rw [← hre]; exact hginvl (Ioo_subset_Icc_self hr)
    exact ⟨htr ▸ hr, htr ▸ hre⟩
  have hτi : InjOn τ (Icc (-d) d) := fun t₁ ht₁ t₂ ht₂ he =>
    hσi ht₁ ht₂ (by rw [← (hγτ t₁ ht₁).2, ← (hγτ t₂ ht₂).2, he])
  rcases continuousOn_strictMono_or_strictAnti (show -d < d by linarith) hτc hτi with hmono | hanti
  · let u := τ (-d); let v := τ d
    have hu := hγτ (-d) ⟨le_rfl, by linarith⟩; have hv := hγτ d ⟨by linarith, le_rfl⟩
    have huv : u < v := hmono ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
    refine ⟨u, v, hu.1.1, huv, hv.1.2, ?_, Or.inl ⟨hu.2, hv.2⟩⟩
    ext y; constructor
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨t, ht, hte⟩ := intermediate_value_Icc (show -d ≤ d by linarith) hτc hr
      exact ⟨t, ht, (hγτ t ht).2.symm.trans (congrArg γ hte)⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨τ t, ⟨hmono.monotoneOn ⟨le_rfl, by linarith⟩ ht ht.1, hmono.monotoneOn ht ⟨by linarith, le_rfl⟩ ht.2⟩, (hγτ t ht).2⟩
  · let u := τ d; let v := τ (-d)
    have hu := hγτ d ⟨by linarith, le_rfl⟩; have hv := hγτ (-d) ⟨le_rfl, by linarith⟩
    have huv : u < v := hanti ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
    refine ⟨u, v, hu.1.1, huv, hv.1.2, ?_, Or.inr ⟨hu.2, hv.2⟩⟩
    ext y; constructor
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨t, ht, hte⟩ := intermediate_value_Icc' (show -d ≤ d by linarith) hτc hr
      exact ⟨t, ht, (hγτ t ht).2.symm.trans (congrArg γ hte)⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨τ t, ⟨hanti.antitoneOn ht ⟨by linarith, le_rfl⟩ ht.2, hanti.antitoneOn ⟨le_rfl, by linarith⟩ ht ht.1⟩, (hγτ t ht).2⟩

/-- Same subinterval extraction for a loop `α` on `[0, 1]` whose basepoint `α 0 = α 1` lies off `L`. -/
theorem subarc_param_interval_loop [T2Space S] {α : ℝ → S}
    (hαc : ContinuousOn α (Icc 0 1)) (hαi : InjOn α (Ico 0 1)) (hα01 : α 0 = α 1)
    {σ : ℝ → S} {d : ℝ} (hd : 0 < d)
    (hσc : ContinuousOn σ (Icc (-d) d)) (hσi : InjOn σ (Icc (-d) d))
    (hsub : σ '' Icc (-d) d ⊆ α '' Icc 0 1) (hbase : α 0 ∉ σ '' Icc (-d) d) :
    ∃ u v : ℝ, 0 < u ∧ u < v ∧ v < 1 ∧
      α '' Icc u v = σ '' Icc (-d) d ∧
      ((α u = σ (-d) ∧ α v = σ d) ∨ (α u = σ d ∧ α v = σ (-d))) := by
  have hLc : IsClosed (σ '' Icc (-d) d) := (isCompact_Icc.image_of_continuousOn hσc).isClosed
  have h0m : Icc (0 : ℝ) 1 ∩ α ⁻¹' (σ '' Icc (-d) d)ᶜ ∈ 𝓝[Icc 0 1] (0 : ℝ) :=
    Filter.inter_mem self_mem_nhdsWithin ((hαc 0 ⟨le_rfl, zero_le_one⟩).preimage_mem_nhdsWithin (hLc.isOpen_compl.mem_nhds hbase))
  have h1m : Icc (0 : ℝ) 1 ∩ α ⁻¹' (σ '' Icc (-d) d)ᶜ ∈ 𝓝[Icc 0 1] (1 : ℝ) :=
    Filter.inter_mem self_mem_nhdsWithin ((hαc 1 ⟨zero_le_one, le_rfl⟩).preimage_mem_nhdsWithin (hLc.isOpen_compl.mem_nhds (hα01 ▸ hbase)))
  obtain ⟨δ₀, hδ₀, hδ₀sub⟩ := Metric.mem_nhdsWithin_iff.mp h0m
  obtain ⟨δ₁, hδ₁, hδ₁sub⟩ := Metric.mem_nhdsWithin_iff.mp h1m
  let ε := min (min (δ₀ / 2) (δ₁ / 2)) (1 / 4)
  have hε : 0 < ε := lt_min (lt_min (half_pos hδ₀) (half_pos hδ₁)) (by norm_num)
  have hε4 : ε ≤ 1 / 4 := min_le_right _ _
  have hεlt : ε < 1 - ε := by linarith
  have hL_in_mid : σ '' Icc (-d) d ⊆ subArc α ε (1 - ε) '' Ioo 0 1 := by
    intro y hy
    obtain ⟨r, hr, rfl⟩ := hsub hy
    have hr_gt : ε < r := by
      by_contra hle; push Not at hle
      have hball : r ∈ ball (0 : ℝ) δ₀ := by
        rw [mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hr.1]
        have : ε ≤ δ₀ / 2 := (min_le_left _ _).trans (min_le_left _ _); linarith
      exact (hδ₀sub ⟨hball, hr⟩).2 hy
    have hr_lt : r < 1 - ε := by
      by_contra hge; push Not at hge
      have hball : r ∈ ball (1 : ℝ) δ₁ := by
        rw [mem_ball, Real.dist_eq, abs_lt]
        have : ε ≤ δ₁ / 2 := (min_le_left _ _).trans (min_le_right _ _); exact ⟨by linarith, by linarith [hr.2]⟩
      exact (hδ₁sub ⟨hball, hr⟩).2 hy
    let s := (r - ε) / ((1 - ε) - ε)
    refine ⟨s, ⟨div_pos (sub_pos.mpr hr_gt) (sub_pos.mpr hεlt),
      (div_lt_one (sub_pos.mpr hεlt)).mpr (sub_lt_sub_right hr_lt ε)⟩, ?_⟩
    simp only [subArc, lin, s]; congr 1; field_simp [(sub_pos.mpr hεlt).ne']; ring
  have hαsub_c : ContinuousOn (subArc α ε (1 - ε)) (Icc 0 1) :=
    continuousOn_subArc hεlt.le (hαc.mono (show Icc ε (1 - ε) ⊆ Icc 0 1 from fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩))
  have hαsub_i : InjOn (subArc α ε (1 - ε)) (Icc 0 1) :=
    injOn_subArc hεlt (hαi.mono (show Icc ε (1 - ε) ⊆ Ico 0 1 from fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩))
  obtain ⟨u', v', hu'0, hu'v', hv'1, him', hends'⟩ :=
    subarc_param_interval hαsub_c hαsub_i hd hσc hσi hL_in_mid
  let u := lin ε (1 - ε) u'
  let v := lin ε (1 - ε) v'
  refine ⟨u, v, by simp only [u, lin]; nlinarith, by simp only [u, v, lin]; nlinarith, by simp only [v, lin]; nlinarith, ?_, hends'⟩
  rw [← him']
  ext y; constructor
  · rintro ⟨x, hx, rfl⟩
    let r := (x - ε) / ((1 - ε) - ε)
    have hr1 : u' ≤ r := by simp only [u, lin] at hx; rw [le_div_iff₀ (sub_pos.mpr hεlt)]; nlinarith [hx.1]
    have hr2 : r ≤ v' := by simp only [v, lin] at hx; rw [div_le_iff₀ (sub_pos.mpr hεlt)]; nlinarith [hx.2]
    refine ⟨r, ⟨hr1, hr2⟩, ?_⟩
    simp only [subArc, lin, r]; congr 1; field_simp [(sub_pos.mpr hεlt).ne']; ring
  · rintro ⟨r, hr, rfl⟩
    exact ⟨lin ε (1 - ε) r, ⟨by simp only [u, lin]; nlinarith [hr.1], by simp only [v, lin]; nlinarith [hr.2]⟩, rfl⟩

/-- Helper: exterior arc of a loop `α` on `[0, 1]` after removing `(u, v) ⊆ (0, 1)`, going from `α v` to `α u`. -/
theorem loop_complement_arc {α : ℝ → S}
    (hαc : ContinuousOn α (Icc 0 1)) (hαi : InjOn α (Ico 0 1)) (hα01 : α 0 = α 1)
    {u v : ℝ} (hu0 : 0 < u) (huv : u < v) (hv1 : v < 1) :
    let E := conc2 (subArc α v 1) (subArc α 0 u)
    ContinuousOn E (Icc 0 1) ∧ InjOn E (Icc 0 1) ∧ E 0 = α v ∧ E 1 = α u ∧
    E '' Icc 0 1 = α '' (Icc 0 u ∪ Icc v 1) ∧
    (∀ {A : Type} [AddCommGroup A] {φ : S → S → A}, IsCoc φ →
      cocInt φ E = cocInt φ (subArc α v 1) + cocInt φ (subArc α 0 u)) := by
  intro E
  have h1c : ContinuousOn (subArc α v 1) (Icc 0 1) := continuousOn_subArc hv1.le (hαc.mono (Icc_subset_Icc_left (by linarith)))
  have h2c : ContinuousOn (subArc α 0 u) (Icc 0 1) := continuousOn_subArc hu0.le (hαc.mono (Icc_subset_Icc_right (by linarith)))
  have h12 : subArc α v 1 1 = subArc α 0 u 0 := by simp [subArc_one, subArc_zero, hα01]
  have h1i : InjOn (subArc α v 1) (Icc 0 1) := fun r₁ hr₁ r₂ hr₂ he => by
    have m1 := lin_mapsTo_Icc hv1.le hr₁; have m2 := lin_mapsTo_Icc hv1.le hr₂
    simp only [subArc] at he
    have hlin_eq : lin v 1 r₁ = lin v 1 r₂ := by
      rcases m1.2.eq_or_lt with h1e | h1lt <;> rcases m2.2.eq_or_lt with h2e | h2lt
      · exact h1e.trans h2e.symm
      · rw [h1e, ← hα01] at he; have := hαi ⟨le_rfl, zero_lt_one⟩ ⟨by linarith [m2.1], h2lt⟩ he; linarith [m2.1]
      · rw [h2e, ← hα01] at he; have := hαi ⟨by linarith [m1.1], h1lt⟩ ⟨le_rfl, zero_lt_one⟩ he; linarith [m1.1]
      · exact hαi ⟨by linarith [m1.1], h1lt⟩ ⟨by linarith [m2.1], h2lt⟩ he
    simp only [lin] at hlin_eq; nlinarith
  have h2i : InjOn (subArc α 0 u) (Icc 0 1) :=
    injOn_subArc hu0 (hαi.mono (show Icc 0 u ⊆ Ico 0 1 from fun x hx => ⟨hx.1, by linarith [hx.2]⟩))
  have hEi : InjOn E (Icc 0 1) := conc2_injOn_Icc h1i h2i fun r₁ hr₁ r₂ hr₂ he => by
    have m1 := lin_mapsTo_Icc hv1.le hr₁; have m2 := lin_mapsTo_Icc hu0.le hr₂
    simp only [subArc] at he
    rcases m1.2.eq_or_lt with h1e | h1lt
    · rw [h1e, ← hα01] at he; have h0 := hαi ⟨le_rfl, zero_lt_one⟩ ⟨m2.1, by linarith [m2.2]⟩ he
      exact ⟨by simp only [lin] at h1e; nlinarith, by simp only [lin] at h0; nlinarith⟩
    · have := hαi ⟨by linarith [m1.1], h1lt⟩ ⟨m2.1, by linarith [m2.2]⟩ he; linarith [m1.1, m2.2]
  refine ⟨continuousOn_conc2 h1c h2c h12, hEi, by simp [E, conc2_zero, subArc_zero], by simp [E, conc2_one, subArc_one], ?_,
    fun hφ => cocInt_conc2 hφ h1c h2c h12⟩
  rw [conc2_image h12, subArc_image hv1.le, subArc_image hu0.le, union_comm, image_union]

end PathUtils

/-! ### Section 2: `OArcData` and `ProperManifold` -/

section ProperManifoldDef

/-- Parameterized interior `O`-arc on a surface `S`. -/
structure OArcData (S : Type) [TopologicalSpace S] where
  O : Set S
  α : ℝ → S
  hO : IsOArc O
  hOint : O ⊆ (bd S)ᶜ
  hαc : ContinuousOn α (Icc 0 1)
  hαi : InjOn α (Ico 0 1)
  hα01 : α 0 = α 1
  hαim : α '' Icc 0 1 = O

/-- Build `OArcData S` from a continuous injective loop in `(bd S)ᶜ`. -/
def OArcData.ofLoop [T2Space S] (α : ℝ → S)
    (hαc : ContinuousOn α (Icc 0 1)) (hαi : InjOn α (Ico 0 1)) (hα01 : α 0 = α 1)
    (hint : α '' Icc 0 1 ⊆ (bd S)ᶜ) : OArcData S where
  O := α '' Icc 0 1
  α := α
  hO := isOArc_of_loop hαc hαi hα01 rfl
  hOint := hint
  hαc := hαc
  hαi := hαi
  hα01 := hα01
  hαim := rfl

/-- A proper 1-manifold with boundary `{s, t}` on `S`: one proper `I`-arc `P₀` with ends `s, t`
plus a finite list `Os` of pairwise disjoint interior `O`-arcs disjoint from `P₀`. -/
structure ProperManifold (S : Type) [TopologicalSpace S] (s t : S) where
  P₀ : Set S
  γ₀ : ℝ → S
  hP₀b : P₀ ∩ bd S = {s, t}
  hP₀l : IsLineWithEnds P₀ s t
  hγ₀c : ContinuousOn γ₀ (Icc 0 1)
  hγ₀i : InjOn γ₀ (Icc 0 1)
  hγ₀0 : γ₀ 0 = s
  hγ₀1 : γ₀ 1 = t
  hγ₀im : γ₀ '' Icc 0 1 = P₀
  Os : List (OArcData S)
  hOs_disj : Os.Pairwise fun a b => Disjoint a.O b.O
  hP₀_disj : ∀ a ∈ Os, Disjoint P₀ a.O

namespace ProperManifold

/-- Union of all `O`-arc components in a list. -/
def listUnion (Os : List (OArcData S)) : Set S :=
  ⋃ a ∈ Os, a.O

theorem listUnion_nil : listUnion ([] : List (OArcData S)) = ∅ := by simp [listUnion]

theorem listUnion_cons (a : OArcData S) (l : List (OArcData S)) :
    listUnion (a :: l) = a.O ∪ listUnion l := by
  ext x; simp [listUnion]

theorem listUnion_append (l₁ l₂ : List (OArcData S)) :
    listUnion (l₁ ++ l₂) = listUnion l₁ ∪ listUnion l₂ := by
  ext x; simp [listUnion, or_and_right, exists_or]

/-- Total underlying point-set of a `ProperManifold`. -/
def U {s t : S} (M : ProperManifold S s t) : Set S :=
  M.P₀ ∪ listUnion M.Os

/-- Total `w₁` integral of `M` in `ZMod 2`. -/
noncomputable def w1Total {s t : S} (M : ProperManifold S s t) (AS : SurfAtlas S) : ZMod 2 :=
  cocInt (w1 AS) M.γ₀ + (M.Os.map fun a => cocInt (w1 AS) a.α).sum

theorem isClosed_listUnion [T2Space S] (Os : List (OArcData S)) : IsClosed (listUnion Os) := by
  induction Os with
  | nil => simp [listUnion]
  | cons a l ih => rw [listUnion_cons]; exact a.hO.isCompact.isClosed.union ih

theorem isClosed_U [T2Space S] {s t : S} (M : ProperManifold S s t) : IsClosed M.U :=
  M.hP₀l.isCompact.isClosed.union (isClosed_listUnion M.Os)

theorem U_inter_bd {s t : S} (M : ProperManifold S s t) : M.U ∩ bd S = {s, t} := by
  ext x; constructor
  · rintro ⟨hxP | hxO, hxbd⟩
    · exact M.hP₀b ▸ ⟨hxP, hxbd⟩
    · obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp hxO
      exact (a.hOint hxa hxbd).elim
  · intro hx
    have h1 : x ∈ M.P₀ ∩ bd S := M.hP₀b.symm ▸ hx
    exact ⟨Or.inl h1.1, h1.2⟩

/-- `HasLocalTwoSides` is preserved under disjoint union of closed sets. -/
theorem hasLocalTwoSides_union {M₁ M₂ : Set S} (hM₁ : IsClosed M₁) (hM₂ : IsClosed M₂)
    (hdisj : Disjoint M₁ M₂)
    (h₁ : ∀ z ∈ M₁, HasLocalTwoSides M₁ z) (h₂ : ∀ z ∈ M₂, HasLocalTwoSides M₂ z) :
    ∀ z ∈ M₁ ∪ M₂, HasLocalTwoSides (M₁ ∪ M₂) z := by
  rintro z (hz₁ | hz₂) V hVo hzV
  · have hz₂ : z ∉ M₂ := Set.disjoint_left.mp hdisj hz₁
    obtain ⟨U, A, B, hUo, hzU, hUV, hsplit, hd, hAo, hBo, hAc, hBc, hAne, hBne⟩ :=
      h₁ z hz₁ (V ∩ M₂ᶜ) (hVo.inter hM₂.isOpen_compl) ⟨hzV, hz₂⟩
    refine ⟨U, A, B, hUo, hzU, hUV.trans inter_subset_left, ?_, hd, hAo, hBo, hAc, hBc, hAne, hBne⟩
    rw [← hsplit]; ext x; constructor
    · rintro ⟨hxU, hnot⟩; exact ⟨hxU, fun h => hnot (Or.inl h)⟩
    · rintro ⟨hxU, hx1⟩; exact ⟨hxU, fun h => h.elim hx1 (hUV hxU).2⟩
  · have hz₁ : z ∉ M₁ := Set.disjoint_right.mp hdisj hz₂
    obtain ⟨U, A, B, hUo, hzU, hUV, hsplit, hd, hAo, hBo, hAc, hBc, hAne, hBne⟩ :=
      h₂ z hz₂ (V ∩ M₁ᶜ) (hVo.inter hM₁.isOpen_compl) ⟨hzV, hz₁⟩
    refine ⟨U, A, B, hUo, hzU, hUV.trans inter_subset_left, ?_, hd, hAo, hBo, hAc, hBc, hAne, hBne⟩
    rw [← hsplit]; ext x; constructor
    · rintro ⟨hxU, hnot⟩; exact ⟨hxU, fun h => hnot (Or.inr h)⟩
    · rintro ⟨hxU, hx2⟩; exact ⟨hxU, fun h => h.elim (hUV hxU).2 hx2⟩

/-- Every `ProperManifold` admits a crossing cocycle and has local two sides everywhere on `M.U`. -/
theorem exists_crossingCocycle [ConnectedSpace S] (hS : IsSurface S) {s t : S} (hst : s ≠ t)
    (M : ProperManifold S s t) :
    (∃ ω : S → S → ZMod 2, IsCrossingCocycle M.U ω) ∧ ∀ z ∈ M.U, HasLocalTwoSides M.U z := by
  have : T2Space S := hS.2.1
  have hlist : ∀ (Os : List (OArcData S)), (Os.Pairwise fun a b => Disjoint a.O b.O) →
      (∃ ω : S → S → ZMod 2, IsCrossingCocycle (listUnion Os) ω) ∧
      ∀ z ∈ listUnion Os, HasLocalTwoSides (listUnion Os) z := by
    intro Os
    induction Os with
    | nil =>
      intro _
      refine ⟨⟨fun _ _ => 0, ⟨univ, fun _ => Filter.univ_mem, fun _ _ _ _ _ _ => by simp⟩,
        fun z _ => ⟨univ, isOpen_univ, mem_univ z, fun _ _ _ _ => rfl⟩,
        fun z hz => by simp [listUnion] at hz⟩, fun z hz => by simp [listUnion] at hz⟩
    | cons a l ih =>
      intro hpw
      rw [List.pairwise_cons] at hpw
      obtain ⟨⟨ωl, hωl⟩, htwol⟩ := ih hpw.2
      obtain ⟨⟨ωa, hωa⟩, htwoa⟩ := exists_oArcCocycle hS a.hO a.hOint
      have hdisj : Disjoint a.O (listUnion l) := by
        rw [Set.disjoint_left]; intro x hxa hxl
        obtain ⟨b, hb, hxb⟩ := mem_iUnion₂.mp hxl
        exact Set.disjoint_left.mp (hpw.1 b hb) hxa hxb
      rw [listUnion_cons]
      exact ⟨⟨fun x y => ωa x y + ωl x y, isCrossingCocycle_union a.hO.isCompact.isClosed (isClosed_listUnion l) hdisj hωa hωl⟩,
        hasLocalTwoSides_union a.hO.isCompact.isClosed (isClosed_listUnion l) hdisj htwoa htwol⟩
  obtain ⟨⟨ωO, hωO⟩, htwoO⟩ := hlist M.Os M.hOs_disj
  obtain ⟨hωP, htwoP⟩ := arcCocycle_isCrossingCocycle hS hst M.hP₀b M.hP₀l
  have hdisjP : Disjoint M.P₀ (listUnion M.Os) := by
    rw [Set.disjoint_left]; intro x hxP hxO
    obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp hxO
    exact Set.disjoint_left.mp (M.hP₀_disj a ha) hxP hxa
  exact ⟨⟨fun x y => arcCocycle hS hst M.hP₀b M.hP₀l x y + ωO x y,
      isCrossingCocycle_union M.hP₀l.isCompact.isClosed (isClosed_listUnion M.Os) hdisjP hωP hωO⟩,
    hasLocalTwoSides_union M.hP₀l.isCompact.isClosed (isClosed_listUnion M.Os) hdisjP htwoP htwoO⟩

/-- Build a `ProperManifold` with `Os = []` from a single parameterized proper `I`-arc. -/
def ofIArc {s t : S} (P : Set S) (γ : ℝ → S)
    (hPb : P ∩ bd S = {s, t}) (hPl : IsLineWithEnds P s t)
    (hγc : ContinuousOn γ (Icc 0 1)) (hγi : InjOn γ (Icc 0 1))
    (hγ0 : γ 0 = s) (hγ1 : γ 1 = t) (hγim : γ '' Icc 0 1 = P) : ProperManifold S s t where
  P₀ := P
  γ₀ := γ
  hP₀b := hPb
  hP₀l := hPl
  hγ₀c := hγc
  hγ₀i := hγi
  hγ₀0 := hγ0
  hγ₀1 := hγ1
  hγ₀im := hγim
  Os := []
  hOs_disj := List.Pairwise.nil
  hP₀_disj := fun _ h => (List.not_mem_nil h).elim

end ProperManifold

end ProperManifoldDef

/-! ### Section 3: Shared rectangle geometry & master `rectangle_surgery` -/

section RectangleSurgery

/-- Bundled geometry of an embedded closed rectangle `f : Icc x₁ x₂ ×ℂ Icc (-d) d → (bd S)ᶜ`. -/
structure RectGeom (S : Type) [TopologicalSpace S] where
  f : ℂ → S
  x₁ : ℝ
  x₂ : ℝ
  d : ℝ
  hx : x₁ < x₂
  hd : 0 < d
  hfc : ContinuousOn f (Icc x₁ x₂ ×ℂ Icc (-d) d)
  hfi : InjOn f (Icc x₁ x₂ ×ℂ Icc (-d) d)
  hΔint : f '' (Icc x₁ x₂ ×ℂ Icc (-d) d) ⊆ (bd S)ᶜ

namespace RectGeom

def R (rg : RectGeom S) : Set ℂ := Icc rg.x₁ rg.x₂ ×ℂ Icc (-rg.d) rg.d
def Δ (rg : RectGeom S) : Set S := rg.f '' rg.R
def Lset (rg : RectGeom S) : Set S := rg.f '' (({rg.x₁} : Set ℝ) ×ℂ Icc (-rg.d) rg.d)
def Rset (rg : RectGeom S) : Set S := rg.f '' (({rg.x₂} : Set ℝ) ×ℂ Icc (-rg.d) rg.d)
def T (rg : RectGeom S) : Set S := rg.f '' (Icc rg.x₁ rg.x₂ ×ℂ ({rg.d} : Set ℝ))
def B (rg : RectGeom S) : Set S := rg.f '' (Icc rg.x₁ rg.x₂ ×ℂ ({-rg.d} : Set ℝ))
def bot (rg : RectGeom S) : ℝ → S := fun r => rg.f ((lin rg.x₁ rg.x₂ r : ℂ) + ((-rg.d : ℝ) : ℂ) * I)
def top (rg : RectGeom S) : ℝ → S := fun r => rg.f ((lin rg.x₁ rg.x₂ r : ℂ) + (rg.d : ℂ) * I)
def σL (rg : RectGeom S) : ℝ → S := fun y => rg.f ((rg.x₁ : ℂ) + (y : ℂ) * I)
def σR (rg : RectGeom S) : ℝ → S := fun y => rg.f ((rg.x₂ : ℂ) + (y : ℂ) * I)

theorem isClosedDisc_Δ [T2Space S] (rg : RectGeom S) : IsClosedDisc rg.Δ := by
  obtain ⟨finv, hfinvc, hfinvl⟩ := exists_inv_of_compactOn (isCompact_Icc.reProdIm isCompact_Icc) rg.hfc rg.hfi
  exact ((isClosedDisc_reProdIm_Icc rg.hx (show -rg.d < rg.d by linarith [rg.hd])).1.image rg.hfc hfinvc (fun _ hy => hfinvl hy)).1

theorem bot_mem_R (rg : RectGeom S) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    ((lin rg.x₁ rg.x₂ r : ℂ) + ((-rg.d : ℝ) : ℂ) * I) ∈ rg.R :=
  Complex.mem_reProdIm.mpr ⟨by simpa using lin_mapsTo_Icc rg.hx.le hr, by simp; linarith [rg.hd]⟩

theorem top_mem_R (rg : RectGeom S) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    ((lin rg.x₁ rg.x₂ r : ℂ) + (rg.d : ℂ) * I) ∈ rg.R :=
  Complex.mem_reProdIm.mpr ⟨by simpa using lin_mapsTo_Icc rg.hx.le hr, by simp; linarith [rg.hd]⟩

theorem bot_c (rg : RectGeom S) : ContinuousOn rg.bot (Icc 0 1) :=
  rg.hfc.comp (by unfold lin; fun_prop) fun _ hr => rg.bot_mem_R hr

theorem top_c (rg : RectGeom S) : ContinuousOn rg.top (Icc 0 1) :=
  rg.hfc.comp (by unfold lin; fun_prop) fun _ hr => rg.top_mem_R hr

theorem bot_i (rg : RectGeom S) : InjOn rg.bot (Icc 0 1) := fun r₁ hr₁ r₂ hr₂ he => by
  have h1 := congrArg Complex.re (rg.hfi (rg.bot_mem_R hr₁) (rg.bot_mem_R hr₂) he)
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, lin] at h1
  nlinarith [rg.hx]

theorem top_i (rg : RectGeom S) : InjOn rg.top (Icc 0 1) := fun r₁ hr₁ r₂ hr₂ he => by
  have h1 := congrArg Complex.re (rg.hfi (rg.top_mem_R hr₁) (rg.top_mem_R hr₂) he)
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, lin] at h1
  nlinarith [rg.hx]

theorem bot_im (rg : RectGeom S) : rg.bot '' Icc 0 1 = rg.B := by
  ext y; constructor
  · rintro ⟨r, hr, rfl⟩; exact ⟨_, Complex.mem_reProdIm.mpr ⟨by simpa using lin_mapsTo_Icc rg.hx.le hr, by simp⟩, rfl⟩
  · rintro ⟨w, hw, rfl⟩; rw [Complex.mem_reProdIm] at hw
    let r := (w.re - rg.x₁) / (rg.x₂ - rg.x₁)
    refine ⟨r, ⟨div_nonneg (sub_nonneg.mpr hw.1.1) (sub_pos.mpr rg.hx).le,
      (div_le_one (sub_pos.mpr rg.hx)).mpr (sub_le_sub_right hw.1.2 rg.x₁)⟩, ?_⟩
    show rg.f _ = rg.f w; congr 1; apply Complex.ext
    · simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, lin, r]
      field_simp [(sub_pos.mpr rg.hx).ne']; ring
    · simp [mem_singleton_iff.mp hw.2]

theorem top_im (rg : RectGeom S) : rg.top '' Icc 0 1 = rg.T := by
  ext y; constructor
  · rintro ⟨r, hr, rfl⟩; exact ⟨_, Complex.mem_reProdIm.mpr ⟨by simpa using lin_mapsTo_Icc rg.hx.le hr, by simp⟩, rfl⟩
  · rintro ⟨w, hw, rfl⟩; rw [Complex.mem_reProdIm] at hw
    let r := (w.re - rg.x₁) / (rg.x₂ - rg.x₁)
    refine ⟨r, ⟨div_nonneg (sub_nonneg.mpr hw.1.1) (sub_pos.mpr rg.hx).le,
      (div_le_one (sub_pos.mpr rg.hx)).mpr (sub_le_sub_right hw.1.2 rg.x₁)⟩, ?_⟩
    show rg.f _ = rg.f w; congr 1; apply Complex.ext
    · simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, lin, r]
      field_simp [(sub_pos.mpr rg.hx).ne']; ring
    · simp [mem_singleton_iff.mp hw.2]

theorem bot_subΔ (rg : RectGeom S) : rg.bot '' Icc 0 1 ⊆ rg.Δ := by
  rintro _ ⟨r, hr, rfl⟩; exact ⟨_, rg.bot_mem_R hr, rfl⟩

theorem top_subΔ (rg : RectGeom S) : rg.top '' Icc 0 1 ⊆ rg.Δ := by
  rintro _ ⟨r, hr, rfl⟩; exact ⟨_, rg.top_mem_R hr, rfl⟩

theorem T_subΔ (rg : RectGeom S) : rg.T ⊆ rg.Δ := rg.top_im ▸ rg.top_subΔ
theorem B_subΔ (rg : RectGeom S) : rg.B ⊆ rg.Δ := rg.bot_im ▸ rg.bot_subΔ

theorem TB_disj (rg : RectGeom S) : Disjoint rg.T rg.B := by
  rw [Set.disjoint_left]; rintro _ ⟨w₁, hw₁, rfl⟩ ⟨w₂, hw₂, hfe⟩
  rw [Complex.mem_reProdIm] at hw₁ hw₂
  have := congrArg Complex.im (rg.hfi
    (Complex.mem_reProdIm.mpr ⟨hw₁.1, by rw [mem_singleton_iff.mp hw₁.2]; exact ⟨by linarith [rg.hd], le_rfl⟩⟩)
    (Complex.mem_reProdIm.mpr ⟨hw₂.1, by rw [mem_singleton_iff.mp hw₂.2]; exact ⟨le_rfl, by linarith [rg.hd]⟩⟩) hfe.symm)
  rw [mem_singleton_iff.mp hw₁.2, mem_singleton_iff.mp hw₂.2] at this; linarith [rg.hd]

theorem L_subΔ (rg : RectGeom S) : rg.Lset ⊆ rg.Δ := by
  rintro _ ⟨w, hw, rfl⟩; rw [Complex.mem_reProdIm] at hw
  exact ⟨w, Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hw.1]; exact ⟨le_rfl, rg.hx.le⟩, hw.2⟩, rfl⟩

theorem R_subΔ (rg : RectGeom S) : rg.Rset ⊆ rg.Δ := by
  rintro _ ⟨w, hw, rfl⟩; rw [Complex.mem_reProdIm] at hw
  exact ⟨w, Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hw.1]; exact ⟨rg.hx.le, le_rfl⟩, hw.2⟩, rfl⟩

theorem LR_disj (rg : RectGeom S) : Disjoint rg.Lset rg.Rset := by
  rw [Set.disjoint_left]; rintro _ ⟨w₁, hw₁, rfl⟩ ⟨w₂, hw₂, hfe⟩; rw [Complex.mem_reProdIm] at hw₁ hw₂
  have := congrArg Complex.re (rg.hfi
    (Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hw₁.1]; exact ⟨le_rfl, rg.hx.le⟩, hw₁.2⟩)
    (Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hw₂.1]; exact ⟨rg.hx.le, le_rfl⟩, hw₂.2⟩) hfe.symm)
  rw [mem_singleton_iff.mp hw₁.1, mem_singleton_iff.mp hw₂.1] at this; linarith [rg.hx]

theorem σL_mem_R (rg : RectGeom S) {y : ℝ} (hy : y ∈ Icc (-rg.d) rg.d) :
    ((rg.x₁ : ℂ) + (y : ℂ) * I) ∈ rg.R :=
  Complex.mem_reProdIm.mpr ⟨by simp [rg.hx.le], by simpa using hy⟩

theorem σR_mem_R (rg : RectGeom S) {y : ℝ} (hy : y ∈ Icc (-rg.d) rg.d) :
    ((rg.x₂ : ℂ) + (y : ℂ) * I) ∈ rg.R :=
  Complex.mem_reProdIm.mpr ⟨by simp [rg.hx.le], by simpa using hy⟩

theorem σL_c (rg : RectGeom S) : ContinuousOn rg.σL (Icc (-rg.d) rg.d) :=
  rg.hfc.comp (by fun_prop) fun _ hy => rg.σL_mem_R hy

theorem σR_c (rg : RectGeom S) : ContinuousOn rg.σR (Icc (-rg.d) rg.d) :=
  rg.hfc.comp (by fun_prop) fun _ hy => rg.σR_mem_R hy

theorem σL_i (rg : RectGeom S) : InjOn rg.σL (Icc (-rg.d) rg.d) := fun y₁ hy₁ y₂ hy₂ he => by
  have := congrArg Complex.im (rg.hfi (rg.σL_mem_R hy₁) (rg.σL_mem_R hy₂) he); simpa using this

theorem σR_i (rg : RectGeom S) : InjOn rg.σR (Icc (-rg.d) rg.d) := fun y₁ hy₁ y₂ hy₂ he => by
  have := congrArg Complex.im (rg.hfi (rg.σR_mem_R hy₁) (rg.σR_mem_R hy₂) he); simpa using this

theorem σL_im (rg : RectGeom S) : rg.σL '' Icc (-rg.d) rg.d = rg.Lset := by
  ext z; constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨_, Complex.mem_reProdIm.mpr ⟨by simp, by simpa using hy⟩, rfl⟩
  · rintro ⟨w, hw, rfl⟩; rw [Complex.mem_reProdIm] at hw
    exact ⟨w.im, hw.2, congrArg rg.f (Complex.ext (by simp [mem_singleton_iff.mp hw.1]) (by simp))⟩

theorem σR_im (rg : RectGeom S) : rg.σR '' Icc (-rg.d) rg.d = rg.Rset := by
  ext z; constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨_, Complex.mem_reProdIm.mpr ⟨by simp, by simpa using hy⟩, rfl⟩
  · rintro ⟨w, hw, rfl⟩; rw [Complex.mem_reProdIm] at hw
    exact ⟨w.im, hw.2, congrArg rg.f (Complex.ext (by simp [mem_singleton_iff.mp hw.1]) (by simp))⟩

theorem isConnected_L (rg : RectGeom S) : IsConnected rg.Lset := by
  rw [← rg.σL_im]
  exact ⟨⟨rg.σL 0, 0, ⟨by linarith [rg.hd], rg.hd.le⟩, rfl⟩, isPreconnected_Icc.image rg.σL rg.σL_c⟩

theorem isConnected_R (rg : RectGeom S) : IsConnected rg.Rset := by
  rw [← rg.σR_im]
  exact ⟨⟨rg.σR 0, 0, ⟨by linarith [rg.hd], rg.hd.le⟩, rfl⟩, isPreconnected_Icc.image rg.σR rg.σR_c⟩

/-- Horizontal reflection of `rg`, swapping `Lset ↔ Rset` while preserving `Δ`, `T`, `B`. -/
def flip (rg : RectGeom S) : RectGeom S where
  f := fun z => rg.f (((rg.x₁ + rg.x₂ - z.re : ℝ) : ℂ) + (z.im : ℂ) * I)
  x₁ := rg.x₁
  x₂ := rg.x₂
  d := rg.d
  hx := rg.hx
  hd := rg.hd
  hfc := rg.hfc.comp (by fun_prop) fun z hz => by
    rw [Complex.mem_reProdIm] at hz ⊢
    exact ⟨⟨by simp; linarith [hz.1.2], by simp; linarith [hz.1.1]⟩, by simpa using hz.2⟩
  hfi := fun z₁ hz₁ z₂ hz₂ he => by
    have h1 := rg.hfi
      (by rw [Complex.mem_reProdIm] at hz₁ ⊢; exact ⟨⟨by simp; linarith [hz₁.1.2], by simp; linarith [hz₁.1.1]⟩, by simpa using hz₁.2⟩)
      (by rw [Complex.mem_reProdIm] at hz₂ ⊢; exact ⟨⟨by simp; linarith [hz₂.1.2], by simp; linarith [hz₂.1.1]⟩, by simpa using hz₂.2⟩) he
    apply Complex.ext
    · have := congrArg Complex.re h1; simp at this; linarith
    · have := congrArg Complex.im h1; simpa using this
  hΔint := by
    rintro _ ⟨z, hz, rfl⟩; apply rg.hΔint
    refine ⟨_, ?_, rfl⟩; rw [Complex.mem_reProdIm] at hz ⊢
    exact ⟨⟨by simp; linarith [hz.1.2], by simp; linarith [hz.1.1]⟩, by simpa using hz.2⟩

theorem flip_Δ (rg : RectGeom S) : rg.flip.Δ = rg.Δ := by
  ext y; constructor
  · rintro ⟨z, hz, rfl⟩
    simp only [flip, R, Complex.mem_reProdIm] at hz
    exact ⟨_, Complex.mem_reProdIm.mpr ⟨⟨by simp; linarith [hz.1.2], by simp; linarith [hz.1.1]⟩, by simpa using hz.2⟩, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    simp only [R, Complex.mem_reProdIm] at hz
    refine ⟨((rg.x₁ + rg.x₂ - z.re : ℝ) : ℂ) + (z.im : ℂ) * I,
      Complex.mem_reProdIm.mpr ⟨⟨by simp [flip]; linarith [hz.1.2], by simp [flip]; linarith [hz.1.1]⟩, by simpa [flip] using hz.2⟩, ?_⟩
    show rg.f _ = rg.f z; congr 1; apply Complex.ext <;> simp

theorem flip_L (rg : RectGeom S) : rg.flip.Lset = rg.Rset := by
  ext y; constructor
  · rintro ⟨z, hz, rfl⟩; simp only [flip, Complex.mem_reProdIm] at hz
    exact ⟨_, Complex.mem_reProdIm.mpr ⟨by simp [mem_singleton_iff.mp hz.1], by simpa using hz.2⟩, rfl⟩
  · rintro ⟨z, hz, rfl⟩; rw [Complex.mem_reProdIm] at hz
    refine ⟨((rg.x₁ : ℝ) : ℂ) + (z.im : ℂ) * I, Complex.mem_reProdIm.mpr ⟨by simp [flip], by simpa [flip] using hz.2⟩, ?_⟩
    show rg.f _ = rg.f z; congr 1; apply Complex.ext <;> simp [mem_singleton_iff.mp hz.1]

theorem flip_R (rg : RectGeom S) : rg.flip.Rset = rg.Lset := by
  ext y; constructor
  · rintro ⟨z, hz, rfl⟩; simp only [flip, Complex.mem_reProdIm] at hz
    exact ⟨_, Complex.mem_reProdIm.mpr ⟨by simp [mem_singleton_iff.mp hz.1], by simpa using hz.2⟩, rfl⟩
  · rintro ⟨z, hz, rfl⟩; rw [Complex.mem_reProdIm] at hz
    refine ⟨((rg.x₂ : ℝ) : ℂ) + (z.im : ℂ) * I, Complex.mem_reProdIm.mpr ⟨by simp [flip], by simpa [flip] using hz.2⟩, ?_⟩
    show rg.f _ = rg.f z; congr 1; apply Complex.ext <;> simp [mem_singleton_iff.mp hz.1]

theorem flip_T (rg : RectGeom S) : rg.flip.T = rg.T := by
  ext y; constructor
  · rintro ⟨z, hz, rfl⟩; simp only [flip, Complex.mem_reProdIm] at hz
    exact ⟨_, Complex.mem_reProdIm.mpr ⟨⟨by simp; linarith [hz.1.2], by simp; linarith [hz.1.1]⟩, by simp [mem_singleton_iff.mp hz.2]⟩, rfl⟩
  · rintro ⟨z, hz, rfl⟩; rw [Complex.mem_reProdIm] at hz
    refine ⟨((rg.x₁ + rg.x₂ - z.re : ℝ) : ℂ) + (z.im : ℂ) * I,
      Complex.mem_reProdIm.mpr ⟨⟨by simp [flip]; linarith [hz.1.2], by simp [flip]; linarith [hz.1.1]⟩, by simp [flip, mem_singleton_iff.mp hz.2]⟩, ?_⟩
    show rg.f _ = rg.f z; congr 1; apply Complex.ext <;> simp

theorem flip_B (rg : RectGeom S) : rg.flip.B = rg.B := by
  ext y; constructor
  · rintro ⟨z, hz, rfl⟩; simp only [flip, Complex.mem_reProdIm] at hz
    exact ⟨_, Complex.mem_reProdIm.mpr ⟨⟨by simp; linarith [hz.1.2], by simp; linarith [hz.1.1]⟩, by simp [mem_singleton_iff.mp hz.2]⟩, rfl⟩
  · rintro ⟨z, hz, rfl⟩; rw [Complex.mem_reProdIm] at hz
    refine ⟨((rg.x₁ + rg.x₂ - z.re : ℝ) : ℂ) + (z.im : ℂ) * I,
      Complex.mem_reProdIm.mpr ⟨⟨by simp [flip]; linarith [hz.1.2], by simp [flip]; linarith [hz.1.1]⟩, by simp [flip, mem_singleton_iff.mp hz.2]⟩, ?_⟩
    show rg.f _ = rg.f z; congr 1; apply Complex.ext <;> simp

end RectGeom

/-- Four-endpoint `ZMod 2` cancellation inside `rg.Δ`: if `Lc, Rc` are curves in `rg.Δ` whose
4 endpoints are the 4 corners `{σL (-d), σL d, σR (-d), σR d}`, then
`cocInt (w1 AS) Lc + cocInt (w1 AS) Rc = cocInt (w1 AS) rg.bot + cocInt (w1 AS) rg.top`. -/
private theorem rect_w1_cancel (hS : IsSurface S) (AS : SurfAtlas S) (rg : RectGeom S)
    {Lc Rc : ℝ → S}
    (hLcc : ContinuousOn Lc (Icc 0 1)) (hRcc : ContinuousOn Rc (Icc 0 1))
    (hLcs : Lc '' Icc 0 1 ⊆ rg.Δ) (hRcs : Rc '' Icc 0 1 ⊆ rg.Δ)
    (hLends : (Lc 0 = rg.σL (-rg.d) ∧ Lc 1 = rg.σL rg.d) ∨ (Lc 0 = rg.σL rg.d ∧ Lc 1 = rg.σL (-rg.d)))
    (hRends : (Rc 0 = rg.σR (-rg.d) ∧ Rc 1 = rg.σR rg.d) ∨ (Rc 0 = rg.σR rg.d ∧ Rc 1 = rg.σR (-rg.d))) :
    cocInt (w1 AS) Lc + cocInt (w1 AS) Rc = cocInt (w1 AS) rg.bot + cocInt (w1 AS) rg.top := by
  have : T2Space S := hS.2.1
  have hcoc := isCoc_w1 hS AS
  have hΔ := rg.isClosedDisc_Δ
  have hint : ∀ x ∈ discBd rg.Δ, IsInteriorPoint x := fun x hx => not_not.mp (rg.hΔint (discBd_subset rg.Δ hx))
  obtain ⟨Δ', hΔ', hsub', -⟩ :=
    exists_disc_around hS.2.2 hΔ hint (isClosed_bd S).isOpen_compl (fun x hx => rg.hΔint (discBd_subset rg.Δ hx))
  have hUo : IsOpen (discInt Δ') := hΔ'.isOpen_discInt hS.2.2
  obtain ⟨h, N, hN, hpot⟩ := exists_potential_on_ball hcoc hUo (discIntHomeo hΔ')
  rw [cocInt_eq_sub_of_subset_ball hcoc hN hpot hLcc (hLcs.trans hsub'),
      cocInt_eq_sub_of_subset_ball hcoc hN hpot hRcc (hRcs.trans hsub'),
      cocInt_eq_sub_of_subset_ball hcoc hN hpot rg.bot_c (rg.bot_subΔ.trans hsub'),
      cocInt_eq_sub_of_subset_ball hcoc hN hpot rg.top_c (rg.top_subΔ.trans hsub')]
  have hsub2 : ∀ x y : ZMod 2, x - y = x + y := by decide
  simp only [RectGeom.bot, RectGeom.top, RectGeom.σL, RectGeom.σR, lin_zero, lin_one, hsub2] at hLends hRends ⊢
  rcases hLends with ⟨hL0, hL1⟩ | ⟨hL0, hL1⟩ <;> rcases hRends with ⟨hR0, hR1⟩ | ⟨hR0, hR1⟩ <;>
    rw [hL0, hL1, hR0, hR1] <;> ring

/-- Every `O`-arc `a` has a point outside a closed vertical segment `f '' ({x₀} × [-d, d])`. -/
private theorem exists_oArc_point_off_seg [T2Space S] (a : OArcData S) (rg : RectGeom S)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Icc rg.x₁ rg.x₂) :
    ∃ c ∈ Ioo (0 : ℝ) 1, a.α c ∉ rg.f '' (({x₀} : Set ℝ) ×ℂ Icc (-rg.d) rg.d) := by
  let K := rg.f '' (({x₀} : Set ℝ) ×ℂ Icc (-rg.d) rg.d)
  by_contra hnot; push Not at hnot
  have hKc : IsClosed K := ((isCompact_singleton.reProdIm isCompact_Icc).image_of_continuousOn
    (rg.hfc.mono fun w hw => by rw [Complex.mem_reProdIm] at hw ⊢; exact ⟨by rw [mem_singleton_iff.mp hw.1]; exact hx₀, hw.2⟩)).isClosed
  have hO_sub_K : a.O ⊆ K := by
    rw [← a.hαim]; rintro _ ⟨r, hr, rfl⟩
    have h0mem : a.α 0 ∈ K := by
      have hlim : Filter.Tendsto (fun n : ℕ => a.α (1 / ((n : ℝ) + 2))) Filter.atTop (𝓝 (a.α 0)) := by
        refine (a.hαc.continuousWithinAt ⟨le_rfl, zero_le_one⟩).tendsto.comp ?_
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ (Filter.Eventually.of_forall fun n => ⟨by positivity, by
          rw [div_le_one (by positivity)]; linarith⟩)
        have ht1 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (Filter.tendsto_add_atTop_nat 1)
        exact ht1.congr fun n => by simp; ring
      exact hKc.mem_of_tendsto hlim (Filter.Eventually.of_forall fun n =>
        hnot _ ⟨by positivity, by rw [div_lt_one (by positivity)]; linarith⟩)
    rcases hr.1.eq_or_lt with rfl | hr0; · exact h0mem
    rcases hr.2.eq_or_lt with rfl | hr1; · exact a.hα01 ▸ h0mem
    exact hnot r ⟨hr0, hr1⟩
  let σ : ℝ → S := fun y => rg.f ((x₀ : ℂ) + (y : ℂ) * I)
  have hσR : ∀ y ∈ Icc (-rg.d) rg.d, ((x₀ : ℂ) + (y : ℂ) * I) ∈ rg.R := fun y hy =>
    Complex.mem_reProdIm.mpr ⟨by simp [hx₀], by simpa using hy⟩
  have hσc : ContinuousOn σ (Icc (-rg.d) rg.d) := rg.hfc.comp (by fun_prop) hσR
  have hσi : InjOn σ (Icc (-rg.d) rg.d) := fun y₁ hy₁ y₂ hy₂ he => by
    have := congrArg Complex.im (rg.hfi (hσR y₁ hy₁) (hσR y₂ hy₂) he); simpa using this
  have hσim : σ '' Icc (-rg.d) rg.d = K := by
    ext z; constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨_, Complex.mem_reProdIm.mpr ⟨by simp, by simpa using hy⟩, rfl⟩
    · rintro ⟨w, hw, rfl⟩; rw [Complex.mem_reProdIm] at hw
      exact ⟨w.im, hw.2, congrArg rg.f (Complex.ext (by simp [mem_singleton_iff.mp hw.1]) (by simp))⟩
  obtain ⟨ginv, hginvc, hginvl⟩ := exists_inv_of_compactOn isCompact_Icc hσc hσi
  let g : Circle → ℝ := fun z => ginv (a.hO.some z).1
  have hgc : Continuous g := hginvc.comp_continuous (continuous_subtype_val.comp a.hO.some.continuous) fun z => hσim ▸ hO_sub_K (a.hO.some z).2
  have hgi : Injective g := fun z₁ z₂ he => by
    obtain ⟨y₁, hy₁, he₁⟩ := hσim ▸ hO_sub_K (a.hO.some z₁).2
    obtain ⟨y₂, hy₂, he₂⟩ := hσim ▸ hO_sub_K (a.hO.some z₂).2
    have e1 : g z₁ = y₁ := by simp only [g, ← he₁]; exact hginvl hy₁
    have e2 : g z₂ = y₂ := by simp only [g, ← he₂]; exact hginvl hy₂
    exact a.hO.some.injective (Subtype.ext (he₁.symm.trans (by rw [← e1, he, e2, he₂])))
  have hne : g (ee 0) ≠ g (ee (1 / 2)) := fun h => by
    obtain ⟨m, hm⟩ := ee_eq_iff.mp (hgi h)
    have h2 : (2 * m : ℤ) = -1 := by exact_mod_cast (by linarith : (2 * m : ℝ) = -1)
    omega
  let mid : ℝ := (g (ee 0) + g (ee (1 / 2))) / 2
  have hmid : mid = (g (ee 0) + g (ee (1 / 2))) / 2 := rfl
  have htop_iv : ∃ t₁ ∈ Ioo (0 : ℝ) (1 / 2), g (ee t₁) = mid := by
    have hc' : ContinuousOn (fun t => g (ee t)) (Icc 0 (1 / 2)) := (hgc.comp continuous_ee).continuousOn
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · obtain ⟨t₁, ht₁, he₁⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2) hc' (show mid ∈ Icc _ _ from ⟨by linarith [hmid], by linarith [hmid]⟩)
      dsimp only at he₁
      exact ⟨t₁, ⟨lt_of_le_of_ne ht₁.1 fun h => by rw [← h] at he₁; linarith [hmid],
        lt_of_le_of_ne ht₁.2 fun h => by rw [h] at he₁; linarith [hmid]⟩, he₁⟩
    · obtain ⟨t₁, ht₁, he₁⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1 / 2) hc' (show mid ∈ Icc _ _ from ⟨by linarith [hmid], by linarith [hmid]⟩)
      dsimp only at he₁
      exact ⟨t₁, ⟨lt_of_le_of_ne ht₁.1 fun h => by rw [← h] at he₁; linarith [hmid],
        lt_of_le_of_ne ht₁.2 fun h => by rw [h] at he₁; linarith [hmid]⟩, he₁⟩
  have hbot_iv : ∃ t₂ ∈ Ioo (1 / 2 : ℝ) 1, g (ee t₂) = mid := by
    have hc' : ContinuousOn (fun t => g (ee t)) (Icc (1 / 2) 1) := (hgc.comp continuous_ee).continuousOn
    have he1 : g (ee 1) = g (ee 0) := by rw [show (1 : ℝ) = 0 + 1 by ring, ee_add_one]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · obtain ⟨t₂, ht₂, he₂⟩ := intermediate_value_Icc' (by norm_num : (1 / 2 : ℝ) ≤ 1) hc' (show mid ∈ Icc _ _ from ⟨by linarith [hmid, he1], by linarith [hmid, he1]⟩)
      dsimp only at he₂
      exact ⟨t₂, ⟨lt_of_le_of_ne ht₂.1 fun h => by rw [← h] at he₂; linarith [hmid],
        lt_of_le_of_ne ht₂.2 fun h => by rw [h, he1] at he₂; linarith [hmid]⟩, he₂⟩
    · obtain ⟨t₂, ht₂, he₂⟩ := intermediate_value_Icc (by norm_num : (1 / 2 : ℝ) ≤ 1) hc' (show mid ∈ Icc _ _ from ⟨by linarith [hmid, he1], by linarith [hmid, he1]⟩)
      dsimp only at he₂
      exact ⟨t₂, ⟨lt_of_le_of_ne ht₂.1 fun h => by rw [← h] at he₂; linarith [hmid],
        lt_of_le_of_ne ht₂.2 fun h => by rw [h, he1] at he₂; linarith [hmid]⟩, he₂⟩
  obtain ⟨t₁, ht₁, he₁⟩ := htop_iv; obtain ⟨t₂, ht₂, he₂⟩ := hbot_iv
  obtain ⟨m, hm⟩ := ee_eq_iff.mp (hgi (he₁.trans he₂.symm))
  have hm1' : (-1 : ℤ) < m := by exact_mod_cast (by linarith [ht₁.1, ht₂.2] : (-1 : ℝ) < m)
  have hm2' : m < 0 := by exact_mod_cast (by linarith [ht₁.2, ht₂.1] : (m : ℝ) < 0)
  omega

/-! #### Abstract 5-arc and 4-arc splicing lemmas (eliminates local-context blowup!) -/

/-- **Abstract `I`-arc splice** (used by Case A1 and Case B):
Given 3 pairwise-disjoint exterior curves `E₁, E₂, E₃` (with `E₁` from `s` to `a₁`, `E₂` from `b₁` to `b₂`,
`E₃` from `a₂` to `t`) and 2 disjoint bridge curves `seg₁` (`a₁ → b₁`), `seg₂` (`b₂ → a₂`) inside `Δ`
meeting `E₁, E₂, E₃` ONLY at their endpoints, builds a single continuous injective `I`-arc
`γ' = conc2 (conc2 E₁ seg₁) (conc2 (conc2 E₂ seg₂) E₃)` from `s` to `t` with exact image and `cocInt`. -/
private theorem splice_I_32 {E₁ E₂ E₃ seg₁ seg₂ : ℝ → S} {Δ : Set S}
    (hE₁c : ContinuousOn E₁ (Icc 0 1)) (hE₂c : ContinuousOn E₂ (Icc 0 1)) (hE₃c : ContinuousOn E₃ (Icc 0 1))
    (h1c : ContinuousOn seg₁ (Icc 0 1)) (h2c : ContinuousOn seg₂ (Icc 0 1))
    (hE₁i : InjOn E₁ (Icc 0 1)) (hE₂i : InjOn E₂ (Icc 0 1)) (hE₃i : InjOn E₃ (Icc 0 1))
    (h1i : InjOn seg₁ (Icc 0 1)) (h2i : InjOn seg₂ (Icc 0 1))
    (he1 : E₁ 1 = seg₁ 0) (he2 : seg₁ 1 = E₂ 0) (he3 : E₂ 1 = seg₂ 0) (he4 : seg₂ 1 = E₃ 0)
    (hE12 : Disjoint (E₁ '' Icc 0 1) (E₂ '' Icc 0 1))
    (hE13 : Disjoint (E₁ '' Icc 0 1) (E₃ '' Icc 0 1))
    (hE23 : Disjoint (E₂ '' Icc 0 1) (E₃ '' Icc 0 1))
    (h12 : Disjoint (seg₁ '' Icc 0 1) (seg₂ '' Icc 0 1))
    (h1sub : seg₁ '' Icc 0 1 ⊆ Δ) (h2sub : seg₂ '' Icc 0 1 ⊆ Δ)
    (hE₁Δ : ∀ r ∈ Icc (0 : ℝ) 1, E₁ r ∈ Δ → r = 1)
    (hE₂Δ : ∀ r ∈ Icc (0 : ℝ) 1, E₂ r ∈ Δ → r = 0 ∨ r = 1)
    (hE₃Δ : ∀ r ∈ Icc (0 : ℝ) 1, E₃ r ∈ Δ → r = 0) :
    let γ' := conc2 (conc2 E₁ seg₁) (conc2 (conc2 E₂ seg₂) E₃)
    ContinuousOn γ' (Icc 0 1) ∧ InjOn γ' (Icc 0 1) ∧ γ' 0 = E₁ 0 ∧ γ' 1 = E₃ 1 ∧
    γ' '' Icc 0 1 = E₁ '' Icc 0 1 ∪ E₂ '' Icc 0 1 ∪ E₃ '' Icc 0 1 ∪ seg₁ '' Icc 0 1 ∪ seg₂ '' Icc 0 1 ∧
    (∀ {φ : S → S → ZMod 2}, IsCoc φ →
      cocInt φ γ' = cocInt φ E₁ + cocInt φ E₂ + cocInt φ E₃ + cocInt φ seg₁ + cocInt φ seg₂) := by
  intro γ'
  let g1 := conc2 E₁ seg₁
  let g2a := conc2 E₂ seg₂
  let g2 := conc2 g2a E₃
  have hg1c : ContinuousOn g1 (Icc 0 1) := continuousOn_conc2 hE₁c h1c he1
  have hg2ac : ContinuousOn g2a (Icc 0 1) := continuousOn_conc2 hE₂c h2c he3
  have hg2e : g2a 1 = E₃ 0 := (conc2_one E₂ seg₂).trans he4
  have hg2c : ContinuousOn g2 (Icc 0 1) := continuousOn_conc2 hg2ac hE₃c hg2e
  have hγe : g1 1 = g2 0 := by simp [g1, g2, g2a, conc2_one, conc2_zero, he2]
  have hg1i : InjOn g1 (Icc 0 1) := conc2_injOn_Icc hE₁i h1i fun r₁ hr₁ r₂ hr₂ he => by
    have hr1 : r₁ = 1 := hE₁Δ r₁ hr₁ (he ▸ h1sub ⟨r₂, hr₂, rfl⟩)
    exact ⟨hr1, h1i hr₂ ⟨le_rfl, zero_le_one⟩ (he.symm.trans (hr1 ▸ he1))⟩
  have hg2ai : InjOn g2a (Icc 0 1) := conc2_injOn_Icc hE₂i h2i fun r₁ hr₁ r₂ hr₂ he => by
    rcases hE₂Δ r₁ hr₁ (he ▸ h2sub ⟨r₂, hr₂, rfl⟩) with rfl | rfl
    · exact (Set.disjoint_left.mp h12 ⟨1, ⟨zero_le_one, le_rfl⟩, he2⟩ ⟨r₂, hr₂, he.symm⟩).elim
    · exact ⟨rfl, h2i hr₂ ⟨le_rfl, zero_le_one⟩ (he.symm.trans he3)⟩
  have hg2i : InjOn g2 (Icc 0 1) := conc2_injOn_Icc hg2ai hE₃i fun r₁ hr₁ r₂ hr₂ he => by
    dsimp only [g2a, conc2] at he; split_ifs at he with hhalf
    · exact (Set.disjoint_left.mp hE23 ⟨2 * r₁, ⟨by linarith [hr₁.1], by linarith⟩, rfl⟩ ⟨r₂, hr₂, he.symm⟩).elim
    · have hr2 : r₂ = 0 := hE₃Δ r₂ hr₂ (he ▸ h2sub ⟨2 * r₁ - 1, ⟨by linarith, by linarith [hr₁.2]⟩, rfl⟩)
      have hr1' := h2i ⟨by linarith, by linarith [hr₁.2]⟩ ⟨zero_le_one, le_rfl⟩ (he.trans (hr2 ▸ he4.symm))
      exact ⟨by linarith, hr2⟩
  have hγi : InjOn γ' (Icc 0 1) := conc2_injOn_Icc hg1i hg2i fun r₁ hr₁ r₂ hr₂ he => by
    change g1 r₁ = g2 r₂ at he
    have hm1 : g1 r₁ ∈ E₁ '' Icc 0 1 ∪ seg₁ '' Icc 0 1 := by rw [← conc2_image he1]; exact ⟨r₁, hr₁, rfl⟩
    have hm2 : g2 r₂ ∈ (E₂ '' Icc 0 1 ∪ seg₂ '' Icc 0 1) ∪ E₃ '' Icc 0 1 := by
      rw [← conc2_image he3, ← conc2_image hg2e]; exact ⟨r₂, hr₂, rfl⟩
    have huniq : g1 r₁ = E₂ 0 := by
      rcases hm1 with ⟨t₁, ht₁, hte₁⟩ | hs₁
      · rcases hm2 with (hx2 | hs₂) | hx3
        · exact (Set.disjoint_left.mp hE12 ⟨t₁, ht₁, hte₁⟩ (he ▸ hx2)).elim
        · have ht1 : t₁ = 1 := hE₁Δ t₁ ht₁ (by rw [hte₁, he]; exact h2sub hs₂)
          have hEq : E₁ 1 = g2 r₂ := by rw [← ht1, hte₁, he]
          exact (Set.disjoint_left.mp h12 ⟨0, ⟨le_rfl, zero_le_one⟩, he1.symm⟩ (hEq ▸ hs₂)).elim
        · exact (Set.disjoint_left.mp hE13 ⟨t₁, ht₁, hte₁⟩ (he ▸ hx3)).elim
      · rcases hm2 with (⟨t₂, ht₂, hte₂⟩ | hs₂) | ⟨t₂, ht₂, hte₂⟩
        · rcases hE₂Δ t₂ ht₂ (by rw [hte₂, ← he]; exact h1sub hs₁) with rfl | rfl
          · exact he.trans hte₂.symm
          · exact (Set.disjoint_left.mp h12 (by rw [hte₂, ← he]; exact hs₁) ⟨0, ⟨le_rfl, zero_le_one⟩, he3.symm⟩).elim
        · exact (Set.disjoint_left.mp h12 hs₁ (he ▸ hs₂)).elim
        · have ht2 : t₂ = 0 := hE₃Δ t₂ ht₂ (by rw [hte₂, ← he]; exact h1sub hs₁)
          have hEq : E₃ 0 = g1 r₁ := by rw [← ht2, hte₂, ← he]
          exact (Set.disjoint_left.mp h12 (hEq ▸ hs₁) ⟨1, ⟨zero_le_one, le_rfl⟩, he4⟩).elim
    exact ⟨hg1i hr₁ ⟨zero_le_one, le_rfl⟩ (huniq.trans (by simp [g1, conc2_one, he2])),
      hg2i hr₂ ⟨le_rfl, zero_le_one⟩ ((he.symm.trans huniq).trans (by simp [g2, g2a, conc2_zero]))⟩
  refine ⟨continuousOn_conc2 hg1c hg2c hγe, hγi, by simp [γ', conc2_zero], by simp [γ', conc2_one], ?_, fun hφ => ?_⟩
  · rw [conc2_image hγe, conc2_image he1, conc2_image hg2e, conc2_image he3]
    ext x; simp only [mem_union]; tauto
  · rw [cocInt_conc2 hφ hg1c hg2c hγe, cocInt_conc2 hφ hE₁c h1c he1,
        cocInt_conc2 hφ hg2ac hE₃c hg2e, cocInt_conc2 hφ hE₂c h2c he3]; ring

/-- **Abstract 2-arc `I`-splice** (`E₁ ++ seg₁ ++ E₃`, used in Case A2). -/
private theorem splice_I_21 {E₁ E₃ seg₁ : ℝ → S} {Δ : Set S}
    (hE₁c : ContinuousOn E₁ (Icc 0 1)) (hE₃c : ContinuousOn E₃ (Icc 0 1)) (h1c : ContinuousOn seg₁ (Icc 0 1))
    (hE₁i : InjOn E₁ (Icc 0 1)) (hE₃i : InjOn E₃ (Icc 0 1)) (h1i : InjOn seg₁ (Icc 0 1))
    (he1 : E₁ 1 = seg₁ 0) (he2 : seg₁ 1 = E₃ 0)
    (hE13 : Disjoint (E₁ '' Icc 0 1) (E₃ '' Icc 0 1))
    (h1sub : seg₁ '' Icc 0 1 ⊆ Δ)
    (hE₁Δ : ∀ r ∈ Icc (0 : ℝ) 1, E₁ r ∈ Δ → r = 1)
    (hE₃Δ : ∀ r ∈ Icc (0 : ℝ) 1, E₃ r ∈ Δ → r = 0) :
    let γ' := conc2 (conc2 E₁ seg₁) E₃
    ContinuousOn γ' (Icc 0 1) ∧ InjOn γ' (Icc 0 1) ∧ γ' 0 = E₁ 0 ∧ γ' 1 = E₃ 1 ∧
    γ' '' Icc 0 1 = E₁ '' Icc 0 1 ∪ E₃ '' Icc 0 1 ∪ seg₁ '' Icc 0 1 ∧
    (∀ {φ : S → S → ZMod 2}, IsCoc φ → cocInt φ γ' = cocInt φ E₁ + cocInt φ E₃ + cocInt φ seg₁) := by
  intro γ'
  let g1 := conc2 E₁ seg₁
  have hg1c : ContinuousOn g1 (Icc 0 1) := continuousOn_conc2 hE₁c h1c he1
  have hg1i : InjOn g1 (Icc 0 1) := conc2_injOn_Icc hE₁i h1i fun r₁ hr₁ r₂ hr₂ he => by
    have hr1 : r₁ = 1 := hE₁Δ r₁ hr₁ (he ▸ h1sub ⟨r₂, hr₂, rfl⟩)
    exact ⟨hr1, h1i hr₂ ⟨le_rfl, zero_le_one⟩ (he.symm.trans (hr1 ▸ he1))⟩
  have hγe : g1 1 = E₃ 0 := (conc2_one E₁ seg₁).trans he2
  have hγi : InjOn γ' (Icc 0 1) := conc2_injOn_Icc hg1i hE₃i fun r₁ hr₁ r₂ hr₂ he => by
    dsimp only [g1, conc2] at he; split_ifs at he with hhalf
    · exact (Set.disjoint_left.mp hE13 ⟨2 * r₁, ⟨by linarith [hr₁.1], by linarith⟩, rfl⟩ ⟨r₂, hr₂, he.symm⟩).elim
    · have hr2 : r₂ = 0 := hE₃Δ r₂ hr₂ (he ▸ h1sub ⟨2 * r₁ - 1, ⟨by linarith, by linarith [hr₁.2]⟩, rfl⟩)
      have hr1' := h1i ⟨by linarith, by linarith [hr₁.2]⟩ ⟨zero_le_one, le_rfl⟩ (he.trans (hr2 ▸ he2.symm))
      exact ⟨by linarith, hr2⟩
  refine ⟨continuousOn_conc2 hg1c hE₃c hγe, hγi, by simp [γ', conc2_zero], by simp [γ', conc2_one], ?_, fun hφ => ?_⟩
  · rw [conc2_image hγe, conc2_image he1]; ext x; simp only [mem_union]; tauto
  · rw [cocInt_conc2 hφ hg1c hE₃c hγe, cocInt_conc2 hφ hE₁c h1c he1]; ring

/-- **Abstract 1-arc `O`-loop splice** (`E ++ seg`, used in Case A2 and Case D2). -/
private theorem splice_O_11 {E seg : ℝ → S} {Δ : Set S}
    (hEc : ContinuousOn E (Icc 0 1)) (hsc : ContinuousOn seg (Icc 0 1))
    (hEi : InjOn E (Icc 0 1)) (hsi : InjOn seg (Icc 0 1))
    (he1 : E 1 = seg 0) (he2 : seg 1 = E 0)
    (hsub : seg '' Icc 0 1 ⊆ Δ)
    (hEΔ : ∀ r ∈ Icc (0 : ℝ) 1, E r ∈ Δ → r = 0 ∨ r = 1) :
    let α := conc2 E seg
    ContinuousOn α (Icc 0 1) ∧ InjOn α (Ico 0 1) ∧ α 0 = α 1 ∧
    α '' Icc 0 1 = E '' Icc 0 1 ∪ seg '' Icc 0 1 ∧
    (∀ {φ : S → S → ZMod 2}, IsCoc φ → cocInt φ α = cocInt φ E + cocInt φ seg) := by
  intro α
  have hαi : InjOn α (Ico 0 1) := conc2_injOn_Ico hEi hsi fun r₁ hr₁ r₂ hr₂ he => by
    rcases hEΔ r₁ hr₁ (he ▸ hsub ⟨r₂, hr₂, rfl⟩) with rfl | rfl
    · exact Or.inr ⟨rfl, hsi hr₂ ⟨zero_le_one, le_rfl⟩ (he.symm.trans he2.symm)⟩
    · exact Or.inl ⟨rfl, hsi hr₂ ⟨le_rfl, zero_le_one⟩ (he.symm.trans he1)⟩
  refine ⟨continuousOn_conc2 hEc hsc he1, hαi, by simp [α, conc2_zero, conc2_one, he2],
    conc2_image he1, fun hφ => cocInt_conc2 hφ hEc hsc he1⟩

/-- **Abstract 2-arc `O`-loop splice** (`(E₁ ++ seg₁) ++ (E₂ ++ seg₂)`, used in Case C and Case D1). -/
private theorem splice_O_22 {E₁ E₂ seg₁ seg₂ : ℝ → S} {Δ : Set S}
    (hE₁c : ContinuousOn E₁ (Icc 0 1)) (hE₂c : ContinuousOn E₂ (Icc 0 1))
    (h1c : ContinuousOn seg₁ (Icc 0 1)) (h2c : ContinuousOn seg₂ (Icc 0 1))
    (hE₁i : InjOn E₁ (Icc 0 1)) (hE₂i : InjOn E₂ (Icc 0 1))
    (h1i : InjOn seg₁ (Icc 0 1)) (h2i : InjOn seg₂ (Icc 0 1))
    (he1 : E₁ 1 = seg₁ 0) (he2 : seg₁ 1 = E₂ 0) (he3 : E₂ 1 = seg₂ 0) (he4 : seg₂ 1 = E₁ 0)
    (hE12 : Disjoint (E₁ '' Icc 0 1) (E₂ '' Icc 0 1))
    (h12 : Disjoint (seg₁ '' Icc 0 1) (seg₂ '' Icc 0 1))
    (h1sub : seg₁ '' Icc 0 1 ⊆ Δ) (h2sub : seg₂ '' Icc 0 1 ⊆ Δ)
    (hE₁Δ : ∀ r ∈ Icc (0 : ℝ) 1, E₁ r ∈ Δ → r = 0 ∨ r = 1)
    (hE₂Δ : ∀ r ∈ Icc (0 : ℝ) 1, E₂ r ∈ Δ → r = 0 ∨ r = 1) :
    let α := conc2 (conc2 E₁ seg₁) (conc2 E₂ seg₂)
    ContinuousOn α (Icc 0 1) ∧ InjOn α (Ico 0 1) ∧ α 0 = α 1 ∧
    α '' Icc 0 1 = E₁ '' Icc 0 1 ∪ E₂ '' Icc 0 1 ∪ seg₁ '' Icc 0 1 ∪ seg₂ '' Icc 0 1 ∧
    (∀ {φ : S → S → ZMod 2}, IsCoc φ → cocInt φ α = cocInt φ E₁ + cocInt φ E₂ + cocInt φ seg₁ + cocInt φ seg₂) := by
  intro α
  let g1 := conc2 E₁ seg₁; let g2 := conc2 E₂ seg₂
  have hg1c : ContinuousOn g1 (Icc 0 1) := continuousOn_conc2 hE₁c h1c he1
  have hg2c : ContinuousOn g2 (Icc 0 1) := continuousOn_conc2 hE₂c h2c he3
  have hg1i : InjOn g1 (Icc 0 1) := conc2_injOn_Icc hE₁i h1i fun r₁ hr₁ r₂ hr₂ he => by
    rcases hE₁Δ r₁ hr₁ (he ▸ h1sub ⟨r₂, hr₂, rfl⟩) with rfl | rfl
    · exact (Set.disjoint_left.mp h12 ⟨r₂, hr₂, he.symm⟩ ⟨1, ⟨zero_le_one, le_rfl⟩, he4⟩).elim
    · exact ⟨rfl, h1i hr₂ ⟨le_rfl, zero_le_one⟩ (he.symm.trans he1)⟩
  have hg2i : InjOn g2 (Icc 0 1) := conc2_injOn_Icc hE₂i h2i fun r₁ hr₁ r₂ hr₂ he => by
    rcases hE₂Δ r₁ hr₁ (he ▸ h2sub ⟨r₂, hr₂, rfl⟩) with rfl | rfl
    · exact (Set.disjoint_left.mp h12 ⟨1, ⟨zero_le_one, le_rfl⟩, he2⟩ ⟨r₂, hr₂, he.symm⟩).elim
    · exact ⟨rfl, h2i hr₂ ⟨le_rfl, zero_le_one⟩ (he.symm.trans he3)⟩
  have hαe : g1 1 = g2 0 := by simp [g1, g2, conc2_one, conc2_zero, he2]
  have hαi : InjOn α (Ico 0 1) := conc2_injOn_Ico hg1i hg2i fun r₁ hr₁ r₂ hr₂ he => by
    change g1 r₁ = g2 r₂ at he
    have hm1 : g1 r₁ ∈ E₁ '' Icc 0 1 ∪ seg₁ '' Icc 0 1 := by rw [← conc2_image he1]; exact ⟨r₁, hr₁, rfl⟩
    have hm2 : g2 r₂ ∈ E₂ '' Icc 0 1 ∪ seg₂ '' Icc 0 1 := by rw [← conc2_image he3]; exact ⟨r₂, hr₂, rfl⟩
    rcases hm1 with ⟨t₁, ht₁, hte₁⟩ | hs₁
    · rcases hm2 with hx2 | hs₂
      · exact (Set.disjoint_left.mp hE12 ⟨t₁, ht₁, hte₁⟩ (he ▸ hx2)).elim
      · rcases hE₁Δ t₁ ht₁ (by rw [hte₁, he]; exact h2sub hs₂) with rfl | rfl
        · right; exact ⟨hg1i hr₁ ⟨le_rfl, zero_le_one⟩ (hte₁.symm.trans (by simp [g1, conc2_zero])),
            hg2i hr₂ ⟨zero_le_one, le_rfl⟩ ((he.symm.trans hte₁.symm).trans (by simp [g2, conc2_one, he4]))⟩
        · exact (Set.disjoint_left.mp h12 ⟨0, ⟨le_rfl, zero_le_one⟩, he1.symm⟩ (by rw [hte₁, he]; exact hs₂)).elim
    · rcases hm2 with ⟨t₂, ht₂, hte₂⟩ | hs₂
      · rcases hE₂Δ t₂ ht₂ (by rw [hte₂, ← he]; exact h1sub hs₁) with rfl | rfl
        · left; exact ⟨hg1i hr₁ ⟨zero_le_one, le_rfl⟩ ((he.trans hte₂.symm).trans (by simp [g1, conc2_one, he2])),
            hg2i hr₂ ⟨le_rfl, zero_le_one⟩ (hte₂.symm.trans (by simp [g2, conc2_zero]))⟩
        · exact (Set.disjoint_left.mp h12 (by rw [hte₂, ← he]; exact hs₁) ⟨0, ⟨le_rfl, zero_le_one⟩, he3.symm⟩).elim
      · exact (Set.disjoint_left.mp h12 hs₁ (he ▸ hs₂)).elim
  refine ⟨continuousOn_conc2 hg1c hg2c hαe, hαi, by simp [α, conc2_zero, conc2_one, he4], ?_, fun hφ => ?_⟩
  · rw [conc2_image hαe, conc2_image he1, conc2_image he3]; ext x; simp only [mem_union]; tauto
  · rw [cocInt_conc2 hφ hg1c hg2c hαe, cocInt_conc2 hφ hE₁c h1c he1, cocInt_conc2 hφ hE₂c h2c he3]; ring

/-! #### The 4 surgery cases (A, B, C, D) using `RectGeom` + abstract splices -/

/-- Case A (`Lset, Rset ⊆ M.P₀` with `0 < u₁ < v₁ < u₂ < v₂ < 1`). -/
private theorem rect_surgery_caseA (hS : IsSurface S) (AS : SurfAtlas S)
    {s t : S} (M : ProperManifold S s t) (rg : RectGeom S)
    (hMΔ : M.U ∩ rg.Δ = rg.Lset ∪ rg.Rset)
    {u₁ v₁ u₂ v₂ : ℝ} (hu₁0 : 0 < u₁) (huv₁ : u₁ < v₁) (hv₁u₂ : v₁ < u₂) (huv₂ : u₂ < v₂) (hv₂1 : v₂ < 1)
    (hL_eq : M.γ₀ '' Icc u₁ v₁ = rg.Lset) (hR_eq : M.γ₀ '' Icc u₂ v₂ = rg.Rset)
    (hL_ends : (M.γ₀ u₁ = rg.σL (-rg.d) ∧ M.γ₀ v₁ = rg.σL rg.d) ∨ (M.γ₀ u₁ = rg.σL rg.d ∧ M.γ₀ v₁ = rg.σL (-rg.d)))
    (hR_ends : (M.γ₀ u₂ = rg.σR (-rg.d) ∧ M.γ₀ v₂ = rg.σR rg.d) ∨ (M.γ₀ u₂ = rg.σR rg.d ∧ M.γ₀ v₂ = rg.σR (-rg.d))) :
    ∃ M' : ProperManifold S s t,
      M'.U \ rg.Δ = M.U \ rg.Δ ∧ M'.U ∩ rg.Δ = rg.T ∪ rg.B ∧ M'.w1Total AS = M.w1Total AS := by
  have : T2Space S := hS.2.1
  let hcoc := isCoc_w1 hS AS
  let A₁ := subArc M.γ₀ 0 u₁; let Lc := subArc M.γ₀ u₁ v₁
  let A₂ := subArc M.γ₀ v₁ u₂; let Rc := subArc M.γ₀ u₂ v₂; let A₃ := subArc M.γ₀ v₂ 1
  have hA₁c : ContinuousOn A₁ (Icc 0 1) := continuousOn_subArc hu₁0.le (M.hγ₀c.mono (Icc_subset_Icc_right (by linarith)))
  have hLcc : ContinuousOn Lc (Icc 0 1) := continuousOn_subArc huv₁.le (M.hγ₀c.mono (Icc_subset_Icc (by linarith) (by linarith)))
  have hA₂c : ContinuousOn A₂ (Icc 0 1) := continuousOn_subArc hv₁u₂.le (M.hγ₀c.mono (Icc_subset_Icc (by linarith) (by linarith)))
  have hRcc : ContinuousOn Rc (Icc 0 1) := continuousOn_subArc huv₂.le (M.hγ₀c.mono (Icc_subset_Icc (by linarith) (by linarith)))
  have hA₃c : ContinuousOn A₃ (Icc 0 1) := continuousOn_subArc hv₂1.le (M.hγ₀c.mono (Icc_subset_Icc_left (by linarith)))
  have hA₁i : InjOn A₁ (Icc 0 1) := injOn_subArc hu₁0 (M.hγ₀i.mono (Icc_subset_Icc_right (by linarith)))
  have hA₂i : InjOn A₂ (Icc 0 1) := injOn_subArc hv₁u₂ (M.hγ₀i.mono (Icc_subset_Icc (by linarith) (by linarith)))
  have hA₃i : InjOn A₃ (Icc 0 1) := injOn_subArc hv₂1 (M.hγ₀i.mono (Icc_subset_Icc_left (by linarith)))
  have hγ₀Δ : ∀ r ∈ Icc (0 : ℝ) 1, M.γ₀ r ∈ rg.Δ ↔ r ∈ Icc u₁ v₁ ∪ Icc u₂ v₂ := fun r hr => by
    constructor
    · intro hΔr
      have h1 : M.γ₀ r ∈ M.U ∩ rg.Δ := ⟨Or.inl (M.hγ₀im ▸ ⟨r, hr, rfl⟩), hΔr⟩
      rw [hMΔ, ← hL_eq, ← hR_eq] at h1
      rcases h1 with ⟨r', hr', hre⟩ | ⟨r', hr', hre⟩
      · exact Or.inl ((M.hγ₀i hr ⟨by linarith [hr'.1], by linarith [hr'.2]⟩ hre.symm) ▸ hr')
      · exact Or.inr ((M.hγ₀i hr ⟨by linarith [hr'.1], by linarith [hr'.2]⟩ hre.symm) ▸ hr')
    · rintro (h | h)
      · exact rg.L_subΔ (hL_eq ▸ ⟨r, h, rfl⟩)
      · exact rg.R_subΔ (hR_eq ▸ ⟨r, h, rfl⟩)
  have hA₁Δ : ∀ r ∈ Icc (0 : ℝ) 1, A₁ r ∈ rg.Δ → r = 1 := fun r hr hΔr => by
    have m := lin_mapsTo_Icc hu₁0.le hr
    have hrin := (hγ₀Δ _ (Icc_subset_Icc_right (by linarith) m)).mp hΔr
    have heq : lin 0 u₁ r = u₁ := by
      rcases hrin with h | h
      · exact le_antisymm m.2 h.1
      · linarith [m.2, h.1]
    simp only [lin] at heq; nlinarith
  have hA₂Δ : ∀ r ∈ Icc (0 : ℝ) 1, A₂ r ∈ rg.Δ → r = 0 ∨ r = 1 := fun r hr hΔr => by
    have m := lin_mapsTo_Icc hv₁u₂.le hr
    rcases (hγ₀Δ _ (Icc_subset_Icc (by linarith) (by linarith) m)).mp hΔr with h | h
    · have : lin v₁ u₂ r = v₁ := le_antisymm h.2 m.1; simp only [lin] at this; exact Or.inl (by nlinarith)
    · have : lin v₁ u₂ r = u₂ := le_antisymm m.2 h.1; simp only [lin] at this; exact Or.inr (by nlinarith)
  have hA₃Δ : ∀ r ∈ Icc (0 : ℝ) 1, A₃ r ∈ rg.Δ → r = 0 := fun r hr hΔr => by
    have m := lin_mapsTo_Icc hv₂1.le hr
    have hrin := (hγ₀Δ _ (Icc_subset_Icc_left (by linarith) m)).mp hΔr
    have heq : lin v₂ 1 r = v₂ := by
      rcases hrin with h | h
      · linarith [m.1, h.2]
      · exact le_antisymm h.2 m.1
    simp only [lin] at heq; nlinarith
  have hA12 : Disjoint (A₁ '' Icc 0 1) (A₂ '' Icc 0 1) := by
    rw [subArc_image hu₁0.le, subArc_image hv₁u₂.le, Set.disjoint_left]
    rintro _ ⟨r₁, hr₁, rfl⟩ ⟨r₂, hr₂, he⟩
    have := M.hγ₀i ⟨hr₁.1, by linarith [hr₁.2]⟩ ⟨by linarith [hr₂.1], by linarith [hr₂.2]⟩ he.symm; linarith [hr₁.2, hr₂.1]
  have hA13 : Disjoint (A₁ '' Icc 0 1) (A₃ '' Icc 0 1) := by
    rw [subArc_image hu₁0.le, subArc_image hv₂1.le, Set.disjoint_left]
    rintro _ ⟨r₁, hr₁, rfl⟩ ⟨r₂, hr₂, he⟩
    have := M.hγ₀i ⟨hr₁.1, by linarith [hr₁.2]⟩ ⟨by linarith [hr₂.1], hr₂.2⟩ he.symm; linarith [hr₁.2, hr₂.1]
  have hA23 : Disjoint (A₂ '' Icc 0 1) (A₃ '' Icc 0 1) := by
    rw [subArc_image hv₁u₂.le, subArc_image hv₂1.le, Set.disjoint_left]
    rintro _ ⟨r₁, hr₁, rfl⟩ ⟨r₂, hr₂, he⟩
    have := M.hγ₀i ⟨by linarith [hr₁.1], by linarith [hr₁.2]⟩ ⟨by linarith [hr₂.1], hr₂.2⟩ he.symm; linarith [hr₁.2, hr₂.1]
  have hOs_disj_Δ : ∀ a ∈ M.Os, Disjoint a.O rg.Δ := fun a ha => by
    rw [Set.disjoint_left]; intro x hxa hxΔ
    have h1 : x ∈ M.U ∩ rg.Δ := ⟨Or.inr (mem_iUnion₂.mpr ⟨a, ha, hxa⟩), hxΔ⟩
    rw [hMΔ, ← hL_eq, ← hR_eq] at h1
    rcases h1 with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
    · exact Set.disjoint_left.mp (M.hP₀_disj a ha) (M.hγ₀im ▸ ⟨r, ⟨by linarith [hr.1], by linarith [hr.2]⟩, rfl⟩) hxa
    · exact Set.disjoint_left.mp (M.hP₀_disj a ha) (M.hγ₀im ▸ ⟨r, ⟨by linarith [hr.1], by linarith [hr.2]⟩, rfl⟩) hxa
  have hcancel : cocInt (w1 AS) Lc + cocInt (w1 AS) Rc = cocInt (w1 AS) rg.bot + cocInt (w1 AS) rg.top :=
    rect_w1_cancel hS AS rg hLcc hRcc (by rw [subArc_image huv₁.le, hL_eq]; exact rg.L_subΔ)
      (by rw [subArc_image huv₂.le, hR_eq]; exact rg.R_subΔ)
      (by simpa [Lc, subArc_zero, subArc_one] using hL_ends) (by simpa [Rc, subArc_zero, subArc_one] using hR_ends)
  have hsplit5 := cocInt_split_five hcoc M.hγ₀c hu₁0 huv₁ hv₁u₂ huv₂ hv₂1
  have hext : (A₁ '' Icc 0 1 ∪ A₂ '' Icc 0 1 ∪ A₃ '' Icc 0 1 ∪ rg.T ∪ rg.B) \ rg.Δ = M.P₀ \ rg.Δ ∧
      (A₁ '' Icc 0 1 ∪ A₂ '' Icc 0 1 ∪ A₃ '' Icc 0 1 ∪ rg.T ∪ rg.B) ∩ rg.Δ = rg.T ∪ rg.B := by
    have hA_sub : A₁ '' Icc 0 1 ∪ A₂ '' Icc 0 1 ∪ A₃ '' Icc 0 1 ⊆ M.P₀ := by
      rw [subArc_image hu₁0.le, subArc_image hv₁u₂.le, subArc_image hv₂1.le, ← M.hγ₀im]
      rintro _ ((⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩) | ⟨r, hr, rfl⟩)
      · exact ⟨r, ⟨hr.1, by linarith [hr.2]⟩, rfl⟩
      · exact ⟨r, ⟨by linarith [hr.1], by linarith [hr.2]⟩, rfl⟩
      · exact ⟨r, ⟨by linarith [hr.1], hr.2⟩, rfl⟩
    constructor
    · ext x; constructor
      · rintro ⟨(((hx | hx) | hx) | hxT) | hxB, hxΔ⟩
        · exact ⟨hA_sub (Or.inl (Or.inl hx)), hxΔ⟩
        · exact ⟨hA_sub (Or.inl (Or.inr hx)), hxΔ⟩
        · exact ⟨hA_sub (Or.inr hx), hxΔ⟩
        · exact (hxΔ (rg.T_subΔ hxT)).elim
        · exact (hxΔ (rg.B_subΔ hxB)).elim
      · rintro ⟨hxP, hxΔ⟩; obtain ⟨r, hr, rfl⟩ := M.hγ₀im ▸ hxP
        have hnot : r ∉ Icc u₁ v₁ ∪ Icc u₂ v₂ := fun h => hxΔ ((hγ₀Δ r hr).mpr h)
        refine ⟨?_, hxΔ⟩
        by_cases h1 : r ≤ u₁
        · exact Or.inl (Or.inl (Or.inl (Or.inl (by rw [subArc_image hu₁0.le]; exact ⟨r, ⟨hr.1, h1⟩, rfl⟩))))
        · by_cases h2 : r ≤ u₂
          · exact Or.inl (Or.inl (Or.inl (Or.inr (by rw [subArc_image hv₁u₂.le]; exact ⟨r, ⟨by by_contra h; exact hnot (Or.inl ⟨le_of_not_ge h1, le_of_not_ge h⟩), h2⟩, rfl⟩))))
          · exact Or.inl (Or.inl (Or.inr (by rw [subArc_image hv₂1.le]; exact ⟨r, ⟨by by_contra h; exact hnot (Or.inr ⟨le_of_not_ge h2, le_of_not_ge h⟩), hr.2⟩, rfl⟩)))
    · ext x; constructor
      · rintro ⟨(((⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩) | ⟨r, hr, rfl⟩) | hxT) | hxB, hxΔ⟩
        · rw [hA₁Δ r hr hxΔ]; dsimp only [A₁]; rw [subArc_one]; rcases hL_ends with ⟨he, _⟩ | ⟨he, _⟩
          · exact Or.inr (he ▸ rg.bot_im ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [RectGeom.bot, RectGeom.σL, lin_zero]⟩)
          · exact Or.inl (he ▸ rg.top_im ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [RectGeom.top, RectGeom.σL, lin_zero]⟩)
        · rcases hA₂Δ r hr hxΔ with rfl | rfl
          · dsimp only [A₂]; rw [subArc_zero]; rcases hL_ends with ⟨_, he⟩ | ⟨_, he⟩
            · exact Or.inl (he ▸ rg.top_im ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [RectGeom.top, RectGeom.σL, lin_zero]⟩)
            · exact Or.inr (he ▸ rg.bot_im ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [RectGeom.bot, RectGeom.σL, lin_zero]⟩)
          · dsimp only [A₂]; rw [subArc_one]; rcases hR_ends with ⟨he, _⟩ | ⟨he, _⟩
            · exact Or.inr (he ▸ rg.bot_im ▸ ⟨1, ⟨zero_le_one, le_rfl⟩, by simp [RectGeom.bot, RectGeom.σR, lin_one]⟩)
            · exact Or.inl (he ▸ rg.top_im ▸ ⟨1, ⟨zero_le_one, le_rfl⟩, by simp [RectGeom.top, RectGeom.σR, lin_one]⟩)
        · rw [hA₃Δ r hr hxΔ]; dsimp only [A₃]; rw [subArc_zero]; rcases hR_ends with ⟨_, he⟩ | ⟨_, he⟩
          · exact Or.inl (he ▸ rg.top_im ▸ ⟨1, ⟨zero_le_one, le_rfl⟩, by simp [RectGeom.top, RectGeom.σR, lin_one]⟩)
          · exact Or.inr (he ▸ rg.bot_im ▸ ⟨1, ⟨zero_le_one, le_rfl⟩, by simp [RectGeom.bot, RectGeom.σR, lin_one]⟩)
        · exact Or.inl hxT
        · exact Or.inr hxB
      · rintro (hxT | hxB)
        · exact ⟨Or.inl (Or.inr hxT), rg.T_subΔ hxT⟩
        · exact ⟨Or.inr hxB, rg.B_subΔ hxB⟩
  have hOsΔ0 : ProperManifold.listUnion M.Os ∩ rg.Δ = ∅ := by
    rw [eq_empty_iff_forall_notMem]; rintro x ⟨hxO, hxΔ⟩
    obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp hxO; exact Set.disjoint_left.mp (hOs_disj_Δ a ha) hxa hxΔ
  -- Parallel subcase A1:
  have hpar : ∀ (seg₁ seg₂ : ℝ → S), (seg₁ = rg.bot ∧ seg₂ = rg.top ∨ seg₁ = rg.top ∧ seg₂ = rg.bot) →
      seg₁ 0 = M.γ₀ u₁ → seg₁ 1 = M.γ₀ u₂ → seg₂ 0 = M.γ₀ v₁ → seg₂ 1 = M.γ₀ v₂ →
      ∃ M' : ProperManifold S s t, M'.U \ rg.Δ = M.U \ rg.Δ ∧ M'.U ∩ rg.Δ = rg.T ∪ rg.B ∧ M'.w1Total AS = M.w1Total AS := by
    intro seg₁ seg₂ hsegs hs10 hs11 hs20 hs21
    have h1c : ContinuousOn seg₁ (Icc 0 1) := hsegs.elim (fun h => h.1 ▸ rg.bot_c) (fun h => h.1 ▸ rg.top_c)
    have h2c : ContinuousOn seg₂ (Icc 0 1) := hsegs.elim (fun h => h.2 ▸ rg.top_c) (fun h => h.2 ▸ rg.bot_c)
    have h1i : InjOn seg₁ (Icc 0 1) := hsegs.elim (fun h => h.1 ▸ rg.bot_i) (fun h => h.1 ▸ rg.top_i)
    have h2i : InjOn seg₂ (Icc 0 1) := hsegs.elim (fun h => h.2 ▸ rg.top_i) (fun h => h.2 ▸ rg.bot_i)
    have h12 : Disjoint (seg₁ '' Icc 0 1) (seg₂ '' Icc 0 1) :=
      hsegs.elim (fun h => h.1 ▸ h.2 ▸ rg.bot_im ▸ rg.top_im ▸ rg.TB_disj.symm)
        (fun h => h.1 ▸ h.2 ▸ rg.top_im ▸ rg.bot_im ▸ rg.TB_disj)
    have h1sub : seg₁ '' Icc 0 1 ⊆ rg.Δ := hsegs.elim (fun h => h.1 ▸ rg.bot_subΔ) (fun h => h.1 ▸ rg.top_subΔ)
    have h2sub : seg₂ '' Icc 0 1 ⊆ rg.Δ := hsegs.elim (fun h => h.2 ▸ rg.top_subΔ) (fun h => h.2 ▸ rg.bot_subΔ)
    have him12 : seg₁ '' Icc 0 1 ∪ seg₂ '' Icc 0 1 = rg.T ∪ rg.B :=
      hsegs.elim (fun h => by rw [h.1, h.2, rg.bot_im, rg.top_im, union_comm]) (fun h => by rw [h.1, h.2, rg.top_im, rg.bot_im])
    let rA₂ := fun r => A₂ (1 - r)
    obtain ⟨hγ'c, hγ'i, hγ'0, hγ'1, hγ'im0, hγ'coc⟩ :=
      splice_I_32 hA₁c (continuousOn_rev hA₂c) hA₃c h1c h2c hA₁i (injOn_rev hA₂i) hA₃i h1i h2i
        ((subArc_one M.γ₀ 0 u₁).trans hs10.symm) (by simp [A₂, subArc_one, hs11])
        (by simp [A₂, subArc_zero, hs20]) (hs21.trans (subArc_zero M.γ₀ v₂ 1).symm)
        (by rw [rev_image]; exact hA12) hA13 (by rw [rev_image]; exact hA23) h12 h1sub h2sub hA₁Δ
        (fun r hr hΔ => by
          rcases hA₂Δ (1 - r) ⟨by linarith [hr.2], by linarith [hr.1]⟩ hΔ with h | h
          · exact Or.inr (by linarith)
          · exact Or.inl (by linarith)) hA₃Δ
    let γ' := conc2 (conc2 A₁ seg₁) (conc2 (conc2 rA₂ seg₂) A₃)
    have hγ'im : γ' '' Icc 0 1 = A₁ '' Icc 0 1 ∪ A₂ '' Icc 0 1 ∪ A₃ '' Icc 0 1 ∪ rg.T ∪ rg.B := by
      rw [hγ'im0, rev_image, union_assoc (A₁ '' Icc 0 1 ∪ A₂ '' Icc 0 1 ∪ A₃ '' Icc 0 1), him12, ← union_assoc]
    have hP'b : (γ' '' Icc 0 1) ∩ bd S = {s, t} := by
      ext x; constructor
      · rintro ⟨hx, hbd⟩; exact M.hP₀b ▸ ⟨(show x ∈ M.P₀ \ rg.Δ from hext.1 ▸ ⟨hγ'im ▸ hx, fun h => rg.hΔint h hbd⟩).1, hbd⟩
      · intro hx; have h1 := M.hP₀b.symm ▸ hx
        exact ⟨hγ'im.symm ▸ (show x ∈ _ \ rg.Δ from hext.1.symm ▸ ⟨h1.1, fun h => rg.hΔint h h1.2⟩).1, h1.2⟩
    have hP'disj : ∀ a ∈ M.Os, Disjoint (γ' '' Icc 0 1) a.O := fun a ha => by
      rw [Set.disjoint_left]; intro x hx hxa
      by_cases hxΔ : x ∈ rg.Δ
      · exact Set.disjoint_left.mp (hOs_disj_Δ a ha) hxa hxΔ
      · exact Set.disjoint_left.mp (M.hP₀_disj a ha) (show x ∈ M.P₀ \ rg.Δ from hext.1 ▸ ⟨hγ'im ▸ hx, hxΔ⟩).1 hxa
    have h0' : γ' 0 = s := hγ'0.trans (by simp [A₁, subArc_zero, M.hγ₀0])
    have h1' : γ' 1 = t := hγ'1.trans (by simp [A₃, subArc_one, M.hγ₀1])
    refine ⟨⟨γ' '' Icc 0 1, γ', hP'b, isLineWithEnds_of_param hγ'c hγ'i h0' h1' rfl, hγ'c, hγ'i, h0', h1', rfl, M.Os, M.hOs_disj, hP'disj⟩, ?_, ?_, ?_⟩
    · simp only [ProperManifold.U, union_sdiff_distrib, hγ'im, hext.1]
    · simp only [ProperManifold.U, union_inter_distrib_right, hγ'im, hext.2, hOsΔ0, union_empty]
    · simp only [ProperManifold.w1Total]; congr 1
      rw [hγ'coc hcoc, cocInt_rev_zmod2 hcoc hA₂c, hsplit5]
      have hss : cocInt (w1 AS) seg₁ + cocInt (w1 AS) seg₂ = cocInt (w1 AS) rg.bot + cocInt (w1 AS) rg.top :=
        hsegs.elim (fun h => by rw [h.1, h.2]) (fun h => by rw [h.1, h.2]; ring)
      linear_combination hss - hcancel
  -- Antiparallel subcase A2:
  have hanti : ∀ (seg₁ seg₂ : ℝ → S), (seg₁ = rg.bot ∧ seg₂ = rg.top ∨ seg₁ = rg.top ∧ seg₂ = rg.bot) →
      seg₁ 0 = M.γ₀ u₁ → seg₁ 1 = M.γ₀ v₂ → seg₂ 0 = M.γ₀ v₁ → seg₂ 1 = M.γ₀ u₂ →
      ∃ M' : ProperManifold S s t, M'.U \ rg.Δ = M.U \ rg.Δ ∧ M'.U ∩ rg.Δ = rg.T ∪ rg.B ∧ M'.w1Total AS = M.w1Total AS := by
    intro seg₁ seg₂ hsegs hs10 hs11 hs20 hs21
    have h1c : ContinuousOn seg₁ (Icc 0 1) := hsegs.elim (fun h => h.1 ▸ rg.bot_c) (fun h => h.1 ▸ rg.top_c)
    have h2c : ContinuousOn seg₂ (Icc 0 1) := hsegs.elim (fun h => h.2 ▸ rg.top_c) (fun h => h.2 ▸ rg.bot_c)
    have h1i : InjOn seg₁ (Icc 0 1) := hsegs.elim (fun h => h.1 ▸ rg.bot_i) (fun h => h.1 ▸ rg.top_i)
    have h2i : InjOn seg₂ (Icc 0 1) := hsegs.elim (fun h => h.2 ▸ rg.top_i) (fun h => h.2 ▸ rg.bot_i)
    have h12 : Disjoint (seg₁ '' Icc 0 1) (seg₂ '' Icc 0 1) :=
      hsegs.elim (fun h => h.1 ▸ h.2 ▸ rg.bot_im ▸ rg.top_im ▸ rg.TB_disj.symm)
        (fun h => h.1 ▸ h.2 ▸ rg.top_im ▸ rg.bot_im ▸ rg.TB_disj)
    have h1sub : seg₁ '' Icc 0 1 ⊆ rg.Δ := hsegs.elim (fun h => h.1 ▸ rg.bot_subΔ) (fun h => h.1 ▸ rg.top_subΔ)
    have h2sub : seg₂ '' Icc 0 1 ⊆ rg.Δ := hsegs.elim (fun h => h.2 ▸ rg.top_subΔ) (fun h => h.2 ▸ rg.bot_subΔ)
    have him12 : seg₁ '' Icc 0 1 ∪ seg₂ '' Icc 0 1 = rg.T ∪ rg.B :=
      hsegs.elim (fun h => by rw [h.1, h.2, rg.bot_im, rg.top_im, union_comm]) (fun h => by rw [h.1, h.2, rg.top_im, rg.bot_im])
    obtain ⟨hγ'c, hγ'i, hγ'0, hγ'1, hγ'im, hγ'coc⟩ :=
      splice_I_21 hA₁c hA₃c h1c hA₁i hA₃i h1i ((subArc_one M.γ₀ 0 u₁).trans hs10.symm) (hs11.trans (subArc_zero M.γ₀ v₂ 1).symm)
        hA13 h1sub hA₁Δ hA₃Δ
    let rseg₂ := fun r => seg₂ (1 - r)
    obtain ⟨hαc, hαi, hα01, hαim, hαcoc⟩ :=
      splice_O_11 hA₂c (continuousOn_rev h2c) hA₂i (injOn_rev h2i) (by simp [A₂, subArc_one, hs21])
        (by simp [A₂, subArc_zero, hs20]) (by rw [rev_image]; exact h2sub) hA₂Δ
    let γ' := conc2 (conc2 A₁ seg₁) A₃
    let α_new := conc2 A₂ rseg₂
    have hαint : α_new '' Icc 0 1 ⊆ (bd S)ᶜ := by
      rw [hαim, rev_image]; rintro x (⟨r, hr, rfl⟩ | hseg) hbd
      · have hmem : M.γ₀ (lin v₁ u₂ r) ∈ ({s, t} : Set S) :=
          M.hP₀b ▸ (⟨M.hγ₀im ▸ ⟨lin v₁ u₂ r, Icc_subset_Icc (by linarith) (by linarith) (lin_mapsTo_Icc hv₁u₂.le hr), rfl⟩, hbd⟩ : M.γ₀ (lin v₁ u₂ r) ∈ M.P₀ ∩ bd S)
        rcases hmem with hs | ht
        · have := M.hγ₀i (Icc_subset_Icc (by linarith) (by linarith) (lin_mapsTo_Icc hv₁u₂.le hr)) ⟨le_rfl, zero_le_one⟩ (hs.trans M.hγ₀0.symm)
          linarith [(lin_mapsTo_Icc hv₁u₂.le hr).1]
        · have := M.hγ₀i (Icc_subset_Icc (by linarith) (by linarith) (lin_mapsTo_Icc hv₁u₂.le hr)) ⟨zero_le_one, le_rfl⟩ ((mem_singleton_iff.mp ht).trans M.hγ₀1.symm)
          linarith [(lin_mapsTo_Icc hv₁u₂.le hr).2]
      · exact rg.hΔint (h2sub hseg) hbd
    let anew : OArcData S := OArcData.ofLoop α_new hαc hαi hα01 hαint
    have hdisj_Pa : Disjoint (γ' '' Icc 0 1) anew.O := by
      change Disjoint (γ' '' Icc 0 1) (α_new '' Icc 0 1)
      rw [hγ'im, hαim, rev_image, Set.disjoint_left]
      rintro x ((⟨t₁, ht₁, rfl⟩ | hx3) | hs₁) (⟨t₂, ht₂, he⟩ | hs₂)
      · exact Set.disjoint_left.mp hA12 ⟨t₁, ht₁, rfl⟩ ⟨t₂, ht₂, he⟩
      · have ht1 : t₁ = 1 := hA₁Δ t₁ ht₁ (h2sub hs₂)
        exact Set.disjoint_left.mp h12 ⟨0, ⟨le_rfl, zero_le_one⟩, hs10.trans (subArc_one M.γ₀ 0 u₁).symm⟩ (ht1 ▸ hs₂)
      · exact Set.disjoint_left.mp hA23 ⟨t₂, ht₂, he⟩ hx3
      · obtain ⟨t₁, ht₁, rfl⟩ := hx3; have ht1 : t₁ = 0 := hA₃Δ t₁ ht₁ (h2sub hs₂)
        exact Set.disjoint_left.mp h12 ⟨1, ⟨zero_le_one, le_rfl⟩, hs11.trans (subArc_zero M.γ₀ v₂ 1).symm⟩ (ht1 ▸ hs₂)
      · rcases hA₂Δ t₂ ht₂ (he ▸ h1sub hs₁) with rfl | rfl
        · exact Set.disjoint_left.mp h12 hs₁ ⟨0, ⟨le_rfl, zero_le_one⟩, hs20.trans ((subArc_zero M.γ₀ v₁ u₂).symm.trans he)⟩
        · exact Set.disjoint_left.mp h12 hs₁ ⟨1, ⟨zero_le_one, le_rfl⟩, hs21.trans ((subArc_one M.γ₀ v₁ u₂).symm.trans he)⟩
      · exact Set.disjoint_left.mp h12 hs₁ hs₂
    have htot : γ' '' Icc 0 1 ∪ anew.O = A₁ '' Icc 0 1 ∪ A₂ '' Icc 0 1 ∪ A₃ '' Icc 0 1 ∪ rg.T ∪ rg.B := by
      change γ' '' Icc 0 1 ∪ α_new '' Icc 0 1 = _
      rw [hγ'im, hαim, rev_image]
      calc (A₁ '' Icc 0 1 ∪ A₃ '' Icc 0 1 ∪ seg₁ '' Icc 0 1) ∪ (A₂ '' Icc 0 1 ∪ seg₂ '' Icc 0 1)
        _ = (A₁ '' Icc 0 1 ∪ A₂ '' Icc 0 1 ∪ A₃ '' Icc 0 1) ∪ (seg₁ '' Icc 0 1 ∪ seg₂ '' Icc 0 1) := by
          ext x; simp only [mem_union]; exact ⟨by rintro (((h | h) | h) | (h | h)) <;> simp [*], by rintro (((h | h) | h) | (h | h)) <;> simp [*]⟩
        _ = A₁ '' Icc 0 1 ∪ A₂ '' Icc 0 1 ∪ A₃ '' Icc 0 1 ∪ rg.T ∪ rg.B := by rw [him12, ← union_assoc]
    have hP'b : (γ' '' Icc 0 1) ∩ bd S = {s, t} := by
      ext x; constructor
      · rintro ⟨hx, hbd⟩; exact M.hP₀b ▸ ⟨(show x ∈ M.P₀ \ rg.Δ from hext.1 ▸ ⟨htot ▸ Or.inl hx, fun h => rg.hΔint h hbd⟩).1, hbd⟩
      · intro hx; have h1 := M.hP₀b.symm ▸ hx
        have h2 : x ∈ γ' '' Icc 0 1 ∪ anew.O := htot.symm ▸ (show x ∈ _ \ rg.Δ from hext.1.symm ▸ ⟨h1.1, fun h => rg.hΔint h h1.2⟩).1
        exact ⟨h2.resolve_right fun h => anew.hOint h h1.2, h1.2⟩
    have hOs_disj : ∀ a ∈ M.Os, Disjoint (γ' '' Icc 0 1 ∪ anew.O) a.O := fun a ha => by
      rw [Set.disjoint_left]; intro x hx hxa
      by_cases hxΔ : x ∈ rg.Δ
      · exact Set.disjoint_left.mp (hOs_disj_Δ a ha) hxa hxΔ
      · exact Set.disjoint_left.mp (M.hP₀_disj a ha) (show x ∈ M.P₀ \ rg.Δ from hext.1 ▸ ⟨htot ▸ hx, hxΔ⟩).1 hxa
    have h0' : γ' 0 = s := hγ'0.trans (by simp [A₁, subArc_zero, M.hγ₀0])
    have h1' : γ' 1 = t := hγ'1.trans (by simp [A₃, subArc_one, M.hγ₀1])
    refine ⟨⟨γ' '' Icc 0 1, γ', hP'b, isLineWithEnds_of_param hγ'c hγ'i h0' h1' rfl, hγ'c, hγ'i, h0', h1', rfl,
      anew :: M.Os, List.pairwise_cons.mpr ⟨fun a ha => (hOs_disj a ha).mono_left subset_union_right, M.hOs_disj⟩,
      fun a ha => by
        rcases List.mem_cons.mp ha with rfl | ha'
        · exact hdisj_Pa
        · exact (hOs_disj a ha').mono_left subset_union_left⟩, ?_, ?_, ?_⟩
    · simp only [ProperManifold.U, ProperManifold.listUnion_cons, ← union_assoc, htot, union_sdiff_distrib, hext.1]
    · simp only [ProperManifold.U, ProperManifold.listUnion_cons, ← union_assoc, htot, union_inter_distrib_right, hext.2, hOsΔ0, union_empty]
    · simp only [ProperManifold.w1Total, List.map_cons, List.sum_cons, anew, OArcData.ofLoop]
      rw [hγ'coc hcoc, hαcoc hcoc, cocInt_rev_zmod2 hcoc h2c, hsplit5]
      have hss : cocInt (w1 AS) seg₁ + cocInt (w1 AS) seg₂ = cocInt (w1 AS) rg.bot + cocInt (w1 AS) rg.top :=
        hsegs.elim (fun h => by rw [h.1, h.2]) (fun h => by rw [h.1, h.2]; ring)
      linear_combination hss - hcancel
  rcases hL_ends with ⟨hL0, hL1⟩ | ⟨hL0, hL1⟩ <;> rcases hR_ends with ⟨hR0, hR1⟩ | ⟨hR0, hR1⟩
  · exact hpar rg.bot rg.top (Or.inl ⟨rfl, rfl⟩) (by simp [RectGeom.bot, RectGeom.σL, lin_zero, hL0])
      (by simp [RectGeom.bot, RectGeom.σR, lin_one, hR0]) (by simp [RectGeom.top, RectGeom.σL, lin_zero, hL1])
      (by simp [RectGeom.top, RectGeom.σR, lin_one, hR1])
  · exact hanti rg.bot rg.top (Or.inl ⟨rfl, rfl⟩) (by simp [RectGeom.bot, RectGeom.σL, lin_zero, hL0])
      (by simp [RectGeom.bot, RectGeom.σR, lin_one, hR1]) (by simp [RectGeom.top, RectGeom.σL, lin_zero, hL1])
      (by simp [RectGeom.top, RectGeom.σR, lin_one, hR0])
  · exact hanti rg.top rg.bot (Or.inr ⟨rfl, rfl⟩) (by simp [RectGeom.top, RectGeom.σL, lin_zero, hL0])
      (by simp [RectGeom.top, RectGeom.σR, lin_one, hR1]) (by simp [RectGeom.bot, RectGeom.σL, lin_zero, hL1])
      (by simp [RectGeom.bot, RectGeom.σR, lin_one, hR0])
  · exact hpar rg.top rg.bot (Or.inr ⟨rfl, rfl⟩) (by simp [RectGeom.top, RectGeom.σL, lin_zero, hL0])
      (by simp [RectGeom.top, RectGeom.σR, lin_one, hR0]) (by simp [RectGeom.bot, RectGeom.σL, lin_zero, hL1])
      (by simp [RectGeom.bot, RectGeom.σR, lin_one, hR1])

/-- Case B (`Lset ⊆ M.P₀`, `Rset ⊆ a.O` for `a ∈ M.Os`): merges `a` into `M.P₀`, dropping `Os.length` by 1! -/
private theorem rect_surgery_caseB (hS : IsSurface S) (AS : SurfAtlas S)
    {s t : S} (M : ProperManifold S s t) (rg : RectGeom S)
    (hMΔ : M.U ∩ rg.Δ = rg.Lset ∪ rg.Rset)
    (l₁ l₂ : List (OArcData S)) (a : OArcData S) (hOs_eq : M.Os = l₁ ++ a :: l₂)
    (hL_sub : rg.Lset ⊆ M.P₀) (hR_sub : rg.Rset ⊆ a.O) :
    ∃ M' : ProperManifold S s t,
      M'.U \ rg.Δ = M.U \ rg.Δ ∧ M'.U ∩ rg.Δ = rg.T ∪ rg.B ∧ M'.w1Total AS = M.w1Total AS ∧
      M'.Os.length + 1 = M.Os.length := by
  have : T2Space S := hS.2.1
  let hcoc := isCoc_w1 hS AS
  obtain ⟨c, hc, hc_notR⟩ := exists_oArc_point_off_seg a rg ⟨rg.hx.le, le_rfl⟩
  obtain ⟨hα'c, hα'i, hα'01, hα'0, hα'im, hα'coc⟩ := oArc_rebase a.hαc a.hαi a.hα01 hc.1 hc.2
  let α' := conc2 (subArc a.α c 1) (subArc a.α 0 c)
  have hL_oo : rg.σL '' Icc (-rg.d) rg.d ⊆ M.γ₀ '' Ioo 0 1 := by
    rw [rg.σL_im]; intro z hz; obtain ⟨r, hr, rfl⟩ := M.hγ₀im ▸ hL_sub hz
    have hnb : M.γ₀ r ∉ bd S := rg.hΔint (rg.L_subΔ hz)
    exact ⟨r, ⟨lt_of_le_of_ne hr.1 fun h => hnb (by rw [← h, M.hγ₀0]; exact (M.hP₀b.symm ▸ Or.inl rfl : s ∈ M.P₀ ∩ bd S).2),
      lt_of_le_of_ne hr.2 fun h => hnb (by rw [h, M.hγ₀1]; exact (M.hP₀b.symm ▸ Or.inr rfl : t ∈ M.P₀ ∩ bd S).2)⟩, rfl⟩
  obtain ⟨u₁, v₁, hu₁0, huv₁, hv₁1, hLeq, hLends⟩ := subarc_param_interval M.hγ₀c M.hγ₀i rg.hd rg.σL_c rg.σL_i hL_oo
  obtain ⟨u₂, v₂, hu₂0, huv₂, hv₂1, hReq, hRends⟩ := subarc_param_interval_loop hα'c hα'i hα'01 rg.hd rg.σR_c rg.σR_i
    (rg.σR_im ▸ hR_sub.trans (hα'im.trans a.hαim).symm.subset) (rg.σR_im ▸ hα'0.symm ▸ hc_notR)
  rw [rg.σL_im] at hLeq; rw [rg.σR_im] at hReq
  let rest := l₁ ++ l₂
  have ha_mem : a ∈ M.Os := hOs_eq ▸ List.mem_append_right l₁ (List.mem_cons_self ..)
  have hPa_disj : Disjoint M.P₀ a.O := M.hP₀_disj a ha_mem
  have hrest_sub : ∀ b ∈ rest, b ∈ M.Os := fun b hb => hOs_eq ▸ by
    rcases List.mem_append.mp hb with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  have hrest_pw : rest.Pairwise fun x y => Disjoint x.O y.O := by
    have hpw := M.hOs_disj; rw [hOs_eq, List.pairwise_append] at hpw
    exact List.pairwise_append.mpr ⟨hpw.1, (List.pairwise_cons.mp hpw.2.1).2, fun x hx y hy => hpw.2.2 x hx y (List.mem_cons_of_mem a hy)⟩
  have hrest_disj_a : ∀ b ∈ rest, Disjoint b.O a.O := fun b hb => by
    have hpw := M.hOs_disj; rw [hOs_eq, List.pairwise_append] at hpw
    rcases List.mem_append.mp hb with h1 | h2
    · exact hpw.2.2 b h1 a (List.mem_cons_self ..)
    · exact ((List.pairwise_cons.mp hpw.2.1).1 b h2).symm
  have hrest_disj_Δ : ∀ b ∈ rest, Disjoint b.O rg.Δ := fun b hb => by
    rw [Set.disjoint_left]; intro x hxb hxΔ
    have h1 : x ∈ M.U ∩ rg.Δ := ⟨Or.inr (mem_iUnion₂.mpr ⟨b, hrest_sub b hb, hxb⟩), hxΔ⟩; rw [hMΔ] at h1
    rcases h1 with h | h
    · exact Set.disjoint_left.mp (M.hP₀_disj b (hrest_sub b hb)) (hL_sub h) hxb
    · exact Set.disjoint_left.mp (hrest_disj_a b hb) hxb (hR_sub h)
  have hPΔ : ∀ r ∈ Icc (0 : ℝ) 1, M.γ₀ r ∈ rg.Δ ↔ r ∈ Icc u₁ v₁ := fun r hr => by
    constructor
    · intro hΔr; have h1 : M.γ₀ r ∈ M.U ∩ rg.Δ := ⟨Or.inl (M.hγ₀im ▸ ⟨r, hr, rfl⟩), hΔr⟩; rw [hMΔ] at h1
      rcases h1 with hL | hR
      · obtain ⟨r', hr', hre⟩ := hLeq.symm ▸ hL
        exact (M.hγ₀i hr ⟨by linarith [hr'.1], by linarith [hr'.2]⟩ hre.symm) ▸ hr'
      · exact (Set.disjoint_left.mp hPa_disj (M.hγ₀im ▸ ⟨r, hr, rfl⟩) (hR_sub hR)).elim
    · intro hru; exact rg.L_subΔ (hLeq ▸ ⟨r, hru, rfl⟩)
  have haΔ : ∀ r ∈ Icc (0 : ℝ) 1, α' r ∈ rg.Δ ↔ r ∈ Icc u₂ v₂ := fun r hr => by
    constructor
    · intro hΔr; have h1 : α' r ∈ M.U ∩ rg.Δ := ⟨Or.inr (mem_iUnion₂.mpr ⟨a, ha_mem, (hα'im.trans a.hαim) ▸ ⟨r, hr, rfl⟩⟩), hΔr⟩; rw [hMΔ] at h1
      rcases h1 with hL | hR
      · exact (Set.disjoint_left.mp hPa_disj (hL_sub hL) ((hα'im.trans a.hαim) ▸ ⟨r, hr, rfl⟩)).elim
      · obtain ⟨r', hr', hre⟩ := hReq.symm ▸ hR
        have hlt : r < 1 := lt_of_le_of_ne hr.2 fun h1 => hc_notR (by rw [h1] at hR; dsimp only [α'] at hR; rw [← hα'01, hα'0] at hR; exact hR)
        exact (hα'i ⟨hr.1, hlt⟩ ⟨by linarith [hr'.1], by linarith [hr'.2]⟩ hre.symm) ▸ hr'
    · intro hru; exact rg.R_subΔ (hReq ▸ ⟨r, hru, rfl⟩)
  let A₁ := subArc M.γ₀ 0 u₁; let Lc := subArc M.γ₀ u₁ v₁; let A₂ := subArc M.γ₀ v₁ 1
  let Rc := subArc α' u₂ v₂
  obtain ⟨hBarcc, hBarci, hBarc0, hBarc1, hBarcim, hBarccoc⟩ := loop_complement_arc hα'c hα'i hα'01 hu₂0 huv₂ hv₂1
  let Barc := conc2 (subArc α' v₂ 1) (subArc α' 0 u₂)
  have hA₁c : ContinuousOn A₁ (Icc 0 1) := continuousOn_subArc hu₁0.le (M.hγ₀c.mono (Icc_subset_Icc_right (by linarith)))
  have hLcc : ContinuousOn Lc (Icc 0 1) := continuousOn_subArc huv₁.le (M.hγ₀c.mono (Icc_subset_Icc (by linarith) (by linarith)))
  have hA₂c : ContinuousOn A₂ (Icc 0 1) := continuousOn_subArc hv₁1.le (M.hγ₀c.mono (Icc_subset_Icc_left (by linarith)))
  have hRcc : ContinuousOn Rc (Icc 0 1) := continuousOn_subArc huv₂.le (hα'c.mono (Icc_subset_Icc (by linarith) (by linarith)))
  have hA₁i : InjOn A₁ (Icc 0 1) := injOn_subArc hu₁0 (M.hγ₀i.mono (Icc_subset_Icc_right (by linarith)))
  have hA₂i : InjOn A₂ (Icc 0 1) := injOn_subArc hv₁1 (M.hγ₀i.mono (Icc_subset_Icc_left (by linarith)))
  have hA₁Δ : ∀ r ∈ Icc (0 : ℝ) 1, A₁ r ∈ rg.Δ → r = 1 := fun r hr hΔ => by
    have m := lin_mapsTo_Icc hu₁0.le hr
    have heq : lin 0 u₁ r = u₁ := le_antisymm m.2 ((hPΔ _ (Icc_subset_Icc_right (by linarith) m)).mp hΔ).1
    simp only [lin] at heq; nlinarith
  have hA₂Δ : ∀ r ∈ Icc (0 : ℝ) 1, A₂ r ∈ rg.Δ → r = 0 := fun r hr hΔ => by
    have m := lin_mapsTo_Icc hv₁1.le hr
    have heq : lin v₁ 1 r = v₁ := le_antisymm ((hPΔ _ (Icc_subset_Icc_left (by linarith) m)).mp hΔ).2 m.1
    simp only [lin] at heq; nlinarith
  have hBarcΔ : ∀ r ∈ Icc (0 : ℝ) 1, Barc r ∈ rg.Δ → r = 0 ∨ r = 1 := fun r hr hΔ => by
    dsimp only [Barc, conc2] at hΔ; split_ifs at hΔ with hhalf
    · have m := lin_mapsTo_Icc hv₂1.le (show 2 * r ∈ Icc (0 : ℝ) 1 from ⟨by linarith [hr.1], by linarith⟩)
      change α' (lin v₂ 1 (2 * r)) ∈ rg.Δ at hΔ
      have heq : lin v₂ 1 (2 * r) = v₂ := le_antisymm ((haΔ _ ⟨by linarith [m.1], m.2⟩).mp hΔ).2 m.1
      simp only [lin] at heq; exact Or.inl (by nlinarith)
    · have m := lin_mapsTo_Icc hu₂0.le (show 2 * r - 1 ∈ Icc (0 : ℝ) 1 from ⟨by linarith, by linarith [hr.2]⟩)
      change α' (lin 0 u₂ (2 * r - 1)) ∈ rg.Δ at hΔ
      have heq : lin 0 u₂ (2 * r - 1) = u₂ := le_antisymm m.2 ((haΔ _ ⟨m.1, by linarith [m.2]⟩).mp hΔ).1
      simp only [lin] at heq; exact Or.inr (by nlinarith)
  have hBarc_sub_a : Barc '' Icc 0 1 ⊆ a.O := by
    rw [hBarcim, ← a.hαim, ← hα'im]; exact image_mono (union_subset (Icc_subset_Icc_right (by linarith)) (Icc_subset_Icc_left (by linarith)))
  have hA₁_sub_P : A₁ '' Icc 0 1 ⊆ M.P₀ := by rw [subArc_image hu₁0.le, ← M.hγ₀im]; exact image_mono (Icc_subset_Icc_right (by linarith))
  have hA₂_sub_P : A₂ '' Icc 0 1 ⊆ M.P₀ := by rw [subArc_image hv₁1.le, ← M.hγ₀im]; exact image_mono (Icc_subset_Icc_left (by linarith))
  have hA12 : Disjoint (A₁ '' Icc 0 1) (A₂ '' Icc 0 1) := by
    rw [subArc_image hu₁0.le, subArc_image hv₁1.le, Set.disjoint_left]
    rintro _ ⟨r₁, hr₁, rfl⟩ ⟨r₂, hr₂, he⟩
    have := M.hγ₀i ⟨hr₁.1, by linarith [hr₁.2]⟩ ⟨by linarith [hr₂.1], hr₂.2⟩ he.symm; linarith [hr₁.2, hr₂.1]
  have hcancel : cocInt (w1 AS) Lc + cocInt (w1 AS) Rc = cocInt (w1 AS) rg.bot + cocInt (w1 AS) rg.top :=
    rect_w1_cancel hS AS rg hLcc hRcc (by rw [subArc_image huv₁.le, hLeq]; exact rg.L_subΔ)
      (by rw [subArc_image huv₂.le, hReq]; exact rg.R_subΔ)
      (by simpa [Lc, subArc_zero, subArc_one] using hLends) (by simpa [Rc, subArc_zero, subArc_one] using hRends)
  have hext : (A₁ '' Icc 0 1 ∪ A₂ '' Icc 0 1 ∪ Barc '' Icc 0 1 ∪ rg.T ∪ rg.B) \ rg.Δ = (M.P₀ ∪ a.O) \ rg.Δ ∧
      (A₁ '' Icc 0 1 ∪ A₂ '' Icc 0 1 ∪ Barc '' Icc 0 1 ∪ rg.T ∪ rg.B) ∩ rg.Δ = rg.T ∪ rg.B := by
    constructor
    · ext x; constructor
      · rintro ⟨(((hx | hx) | hx) | hxT) | hxB, hxΔ⟩
        · exact ⟨Or.inl (hA₁_sub_P hx), hxΔ⟩
        · exact ⟨Or.inl (hA₂_sub_P hx), hxΔ⟩
        · exact ⟨Or.inr (hBarc_sub_a hx), hxΔ⟩
        · exact (hxΔ (rg.T_subΔ hxT)).elim
        · exact (hxΔ (rg.B_subΔ hxB)).elim
      · rintro ⟨hxP | hxa, hxΔ⟩
        · obtain ⟨r, hr, rfl⟩ := M.hγ₀im ▸ hxP
          have hnot : r ∉ Icc u₁ v₁ := fun h => hxΔ ((hPΔ r hr).mpr h)
          refine ⟨?_, hxΔ⟩
          by_cases h1 : r ≤ u₁
          · exact Or.inl (Or.inl (Or.inl (Or.inl (by rw [subArc_image hu₁0.le]; exact ⟨r, ⟨hr.1, h1⟩, rfl⟩))))
          · exact Or.inl (Or.inl (Or.inl (Or.inr (by rw [subArc_image hv₁1.le]; exact ⟨r, ⟨by by_contra h; exact hnot ⟨le_of_not_ge h1, le_of_not_ge h⟩, hr.2⟩, rfl⟩))))
        · obtain ⟨r, hr, rfl⟩ := (hα'im.trans a.hαim) ▸ hxa
          have hnot : r ∉ Icc u₂ v₂ := fun h => hxΔ ((haΔ r hr).mpr h)
          refine ⟨Or.inl (Or.inl (Or.inr ?_)), hxΔ⟩; rw [hBarcim]
          by_cases h1 : r ≤ u₂
          · exact ⟨r, Or.inl ⟨hr.1, h1⟩, rfl⟩
          · exact ⟨r, Or.inr ⟨by by_contra h; exact hnot ⟨le_of_not_ge h1, le_of_not_ge h⟩, hr.2⟩, rfl⟩
    · ext x; constructor
      · rintro ⟨(((⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩) | ⟨r, hr, rfl⟩) | hxT) | hxB, hxΔ⟩
        · rw [hA₁Δ r hr hxΔ]; dsimp only [A₁]; rw [subArc_one]; rcases hLends with ⟨he, _⟩ | ⟨he, _⟩
          · exact Or.inr (he ▸ rg.bot_im ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [RectGeom.bot, RectGeom.σL, lin_zero]⟩)
          · exact Or.inl (he ▸ rg.top_im ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [RectGeom.top, RectGeom.σL, lin_zero]⟩)
        · rw [hA₂Δ r hr hxΔ]; dsimp only [A₂]; rw [subArc_zero]; rcases hLends with ⟨_, he⟩ | ⟨_, he⟩
          · exact Or.inl (he ▸ rg.top_im ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [RectGeom.top, RectGeom.σL, lin_zero]⟩)
          · exact Or.inr (he ▸ rg.bot_im ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [RectGeom.bot, RectGeom.σL, lin_zero]⟩)
        · rcases hBarcΔ r hr hxΔ with rfl | rfl
          · dsimp only [Barc]; rw [hBarc0]; rcases hRends with ⟨_, he⟩ | ⟨_, he⟩
            · exact Or.inl (he ▸ rg.top_im ▸ ⟨1, ⟨zero_le_one, le_rfl⟩, by simp [RectGeom.top, RectGeom.σR, lin_one]⟩)
            · exact Or.inr (he ▸ rg.bot_im ▸ ⟨1, ⟨zero_le_one, le_rfl⟩, by simp [RectGeom.bot, RectGeom.σR, lin_one]⟩)
          · dsimp only [Barc]; rw [hBarc1]; rcases hRends with ⟨he, _⟩ | ⟨he, _⟩
            · exact Or.inr (he ▸ rg.bot_im ▸ ⟨1, ⟨zero_le_one, le_rfl⟩, by simp [RectGeom.bot, RectGeom.σR, lin_one]⟩)
            · exact Or.inl (he ▸ rg.top_im ▸ ⟨1, ⟨zero_le_one, le_rfl⟩, by simp [RectGeom.top, RectGeom.σR, lin_one]⟩)
        · exact Or.inl hxT
        · exact Or.inr hxB
      · rintro (hxT | hxB)
        · exact ⟨Or.inl (Or.inr hxT), rg.T_subΔ hxT⟩
        · exact ⟨Or.inr hxB, rg.B_subΔ hxB⟩
  have hbuild : ∀ (seg₁ seg₂ B_dir : ℝ → S), (seg₁ = rg.bot ∧ seg₂ = rg.top ∨ seg₁ = rg.top ∧ seg₂ = rg.bot) →
      (B_dir = Barc ∨ B_dir = fun r => Barc (1 - r)) →
      seg₁ 0 = M.γ₀ u₁ → seg₁ 1 = B_dir 0 → seg₂ 0 = M.γ₀ v₁ → seg₂ 1 = B_dir 1 →
      ∃ M' : ProperManifold S s t,
        M'.U \ rg.Δ = M.U \ rg.Δ ∧ M'.U ∩ rg.Δ = rg.T ∪ rg.B ∧ M'.w1Total AS = M.w1Total AS ∧ M'.Os.length + 1 = M.Os.length := by
    intro seg₁ seg₂ B_dir hsegs hBdir hs10 hs11 hs20 hs21
    have h1c : ContinuousOn seg₁ (Icc 0 1) := hsegs.elim (fun h => h.1 ▸ rg.bot_c) (fun h => h.1 ▸ rg.top_c)
    have h2c : ContinuousOn seg₂ (Icc 0 1) := hsegs.elim (fun h => h.2 ▸ rg.top_c) (fun h => h.2 ▸ rg.bot_c)
    have h1i : InjOn seg₁ (Icc 0 1) := hsegs.elim (fun h => h.1 ▸ rg.bot_i) (fun h => h.1 ▸ rg.top_i)
    have h2i : InjOn seg₂ (Icc 0 1) := hsegs.elim (fun h => h.2 ▸ rg.top_i) (fun h => h.2 ▸ rg.bot_i)
    have h12 : Disjoint (seg₁ '' Icc 0 1) (seg₂ '' Icc 0 1) :=
      hsegs.elim (fun h => h.1 ▸ h.2 ▸ rg.bot_im ▸ rg.top_im ▸ rg.TB_disj.symm)
        (fun h => h.1 ▸ h.2 ▸ rg.top_im ▸ rg.bot_im ▸ rg.TB_disj)
    have h1sub : seg₁ '' Icc 0 1 ⊆ rg.Δ := hsegs.elim (fun h => h.1 ▸ rg.bot_subΔ) (fun h => h.1 ▸ rg.top_subΔ)
    have h2sub : seg₂ '' Icc 0 1 ⊆ rg.Δ := hsegs.elim (fun h => h.2 ▸ rg.top_subΔ) (fun h => h.2 ▸ rg.bot_subΔ)
    have him12 : seg₁ '' Icc 0 1 ∪ seg₂ '' Icc 0 1 = rg.T ∪ rg.B :=
      hsegs.elim (fun h => by rw [h.1, h.2, rg.bot_im, rg.top_im, union_comm]) (fun h => by rw [h.1, h.2, rg.top_im, rg.bot_im])
    have hBdc : ContinuousOn B_dir (Icc 0 1) := hBdir.elim (fun h => h ▸ hBarcc) (fun h => h ▸ continuousOn_rev hBarcc)
    have hBdi : InjOn B_dir (Icc 0 1) := hBdir.elim (fun h => h ▸ hBarci) (fun h => h ▸ injOn_rev hBarci)
    have hBdim : B_dir '' Icc 0 1 = Barc '' Icc 0 1 := hBdir.elim (fun h => h ▸ rfl) (fun h => h ▸ rev_image Barc)
    have hBdΔ : ∀ r ∈ Icc (0 : ℝ) 1, B_dir r ∈ rg.Δ → r = 0 ∨ r = 1 := fun r hr hΔ => by
      rcases hBdir with rfl | rfl
      · exact hBarcΔ r hr hΔ
      · rcases hBarcΔ (1 - r) ⟨by linarith [hr.2], by linarith [hr.1]⟩ hΔ with h | h
        · exact Or.inr (by linarith)
        · exact Or.inl (by linarith)
    have hBdcoc : cocInt (w1 AS) B_dir = cocInt (w1 AS) Barc :=
      hBdir.elim (fun h => h ▸ rfl) (fun h => h ▸ cocInt_rev_zmod2 hcoc hBarcc)
    let rseg₂ := fun r => seg₂ (1 - r)
    obtain ⟨hγ'c, hγ'i, hγ'0, hγ'1, hγ'im0, hγ'coc⟩ :=
      splice_I_32 hA₁c hBdc hA₂c h1c (continuousOn_rev h2c) hA₁i hBdi hA₂i h1i (injOn_rev h2i)
        ((subArc_one M.γ₀ 0 u₁).trans hs10.symm) hs11 (by simp [hs21])
        (by simp [hs20, A₂, subArc_zero])
        (hPa_disj.mono hA₁_sub_P (hBdim ▸ hBarc_sub_a)) hA12
        (hPa_disj.symm.mono (hBdim ▸ hBarc_sub_a) hA₂_sub_P)
        (by rw [rev_image]; exact h12) h1sub (by rw [rev_image]; exact h2sub) hA₁Δ hBdΔ hA₂Δ
    let γ' := conc2 (conc2 A₁ seg₁) (conc2 (conc2 B_dir rseg₂) A₂)
    have hγ'im : γ' '' Icc 0 1 = A₁ '' Icc 0 1 ∪ A₂ '' Icc 0 1 ∪ Barc '' Icc 0 1 ∪ rg.T ∪ rg.B := by
      rw [hγ'im0, hBdim, rev_image]
      calc (A₁ '' Icc 0 1 ∪ Barc '' Icc 0 1 ∪ A₂ '' Icc 0 1 ∪ seg₁ '' Icc 0 1) ∪ seg₂ '' Icc 0 1
        _ = (A₁ '' Icc 0 1 ∪ A₂ '' Icc 0 1 ∪ Barc '' Icc 0 1) ∪ (seg₁ '' Icc 0 1 ∪ seg₂ '' Icc 0 1) := by
          ext x; simp only [mem_union]; exact ⟨by rintro ((((h | h) | h) | h) | h) <;> simp [*], by rintro (((h | h) | h) | (h | h)) <;> simp [*]⟩
        _ = A₁ '' Icc 0 1 ∪ A₂ '' Icc 0 1 ∪ Barc '' Icc 0 1 ∪ rg.T ∪ rg.B := by rw [him12, ← union_assoc]
    have hP'b : (γ' '' Icc 0 1) ∩ bd S = {s, t} := by
      ext x; constructor
      · rintro ⟨hx, hbd⟩
        have hPa := (show x ∈ (M.P₀ ∪ a.O) \ rg.Δ from hext.1 ▸ ⟨hγ'im ▸ hx, fun h => rg.hΔint h hbd⟩).1
        exact M.hP₀b ▸ ⟨hPa.resolve_right (fun h => a.hOint h hbd), hbd⟩
      · intro hx; have h1 := M.hP₀b.symm ▸ hx
        exact ⟨hγ'im.symm ▸ (show x ∈ _ \ rg.Δ from hext.1.symm ▸ ⟨Or.inl h1.1, fun h => rg.hΔint h h1.2⟩).1, h1.2⟩
    have hP'disj : ∀ b ∈ rest, Disjoint (γ' '' Icc 0 1) b.O := fun b hb => by
      rw [Set.disjoint_left]; intro x hx hxb
      by_cases hxΔ : x ∈ rg.Δ
      · exact Set.disjoint_left.mp (hrest_disj_Δ b hb) hxb hxΔ
      · rcases (show x ∈ (M.P₀ ∪ a.O) \ rg.Δ from hext.1 ▸ ⟨hγ'im ▸ hx, hxΔ⟩).1 with hxP | hxa
        · exact Set.disjoint_left.mp (M.hP₀_disj b (hrest_sub b hb)) hxP hxb
        · exact Set.disjoint_left.mp (hrest_disj_a b hb) hxb hxa
    have hMU_eq : M.U = (M.P₀ ∪ a.O) ∪ ProperManifold.listUnion rest := by
      simp only [ProperManifold.U, hOs_eq, ProperManifold.listUnion_append, ProperManifold.listUnion_cons, rest]
      ext x; simp only [mem_union]; exact ⟨by rintro (h | (h | (h | h))) <;> simp [*], by rintro ((h | h) | (h | h)) <;> simp [*]⟩
    have hrestΔ0 : ProperManifold.listUnion rest ∩ rg.Δ = ∅ := by
      rw [eq_empty_iff_forall_notMem]; rintro x ⟨hxO, hxΔ⟩
      obtain ⟨b, hb, hxb⟩ := mem_iUnion₂.mp hxO; exact Set.disjoint_left.mp (hrest_disj_Δ b hb) hxb hxΔ
    have h0' : γ' 0 = s := hγ'0.trans (by simp [A₁, subArc_zero, M.hγ₀0])
    have h1' : γ' 1 = t := hγ'1.trans (by simp [A₂, subArc_one, M.hγ₀1])
    refine ⟨⟨γ' '' Icc 0 1, γ', hP'b, isLineWithEnds_of_param hγ'c hγ'i h0' h1' rfl, hγ'c, hγ'i, h0', h1', rfl, rest, hrest_pw, hP'disj⟩, ?_, ?_, ?_, ?_⟩
    · rw [hMU_eq]; simp only [ProperManifold.U, union_sdiff_distrib, hγ'im, hext.1]
    · simp only [ProperManifold.U, union_inter_distrib_right, hγ'im, hext.2, hrestΔ0, union_empty]
    · simp only [ProperManifold.w1Total, hOs_eq, List.map_append, List.map_cons, List.sum_append, List.sum_cons, rest]
      rw [hγ'coc hcoc, hBdcoc, hBarccoc hcoc, cocInt_rev_zmod2 hcoc h2c,
          cocInt_split_three hcoc M.hγ₀c hu₁0 huv₁ hv₁1,
          ← hα'coc hcoc, cocInt_split_three hcoc hα'c hu₂0 huv₂ hv₂1]
      have hss : cocInt (w1 AS) seg₁ + cocInt (w1 AS) seg₂ = cocInt (w1 AS) rg.bot + cocInt (w1 AS) rg.top :=
        hsegs.elim (fun h => by rw [h.1, h.2]) (fun h => by rw [h.1, h.2]; ring)
      change cocInt (w1 AS) A₁ + (cocInt (w1 AS) (subArc α' v₂ 1) + cocInt (w1 AS) (subArc α' 0 u₂)) +
          cocInt (w1 AS) A₂ + cocInt (w1 AS) seg₁ + cocInt (w1 AS) seg₂ +
          ((l₁.map fun b => cocInt (w1 AS) b.α).sum + (l₂.map fun b => cocInt (w1 AS) b.α).sum) =
        cocInt (w1 AS) A₁ + (cocInt (w1 AS) Lc + cocInt (w1 AS) A₂) +
          ((l₁.map fun b => cocInt (w1 AS) b.α).sum +
            (cocInt (w1 AS) (subArc α' 0 u₂) + (cocInt (w1 AS) Rc + cocInt (w1 AS) (subArc α' v₂ 1)) +
              (l₂.map fun b => cocInt (w1 AS) b.α).sum))
      linear_combination hss - hcancel
    · simp only [rest, hOs_eq, List.length_append, List.length_cons]; omega
  rcases hLends with ⟨hL0, hL1⟩ | ⟨hL0, hL1⟩ <;> rcases hRends with ⟨hR0, hR1⟩ | ⟨hR0, hR1⟩
  · exact hbuild rg.bot rg.top (fun r => Barc (1 - r)) (Or.inl ⟨rfl, rfl⟩) (Or.inr rfl)
      (by simp [RectGeom.bot, RectGeom.σL, lin_zero, hL0]) (by simp [RectGeom.bot, RectGeom.σR, lin_one, Barc, α', hBarc1, hR0])
      (by simp [RectGeom.top, RectGeom.σL, lin_zero, hL1]) (by simp [RectGeom.top, RectGeom.σR, lin_one, Barc, α', hBarc0, hR1])
  · exact hbuild rg.bot rg.top Barc (Or.inl ⟨rfl, rfl⟩) (Or.inl rfl)
      (by simp [RectGeom.bot, RectGeom.σL, lin_zero, hL0]) (by simp [RectGeom.bot, RectGeom.σR, lin_one, Barc, α', hBarc0, hR1])
      (by simp [RectGeom.top, RectGeom.σL, lin_zero, hL1]) (by simp [RectGeom.top, RectGeom.σR, lin_one, Barc, α', hBarc1, hR0])
  · exact hbuild rg.top rg.bot Barc (Or.inr ⟨rfl, rfl⟩) (Or.inl rfl)
      (by simp [RectGeom.top, RectGeom.σL, lin_zero, hL0]) (by simp [RectGeom.top, RectGeom.σR, lin_one, Barc, α', hBarc0, hR1])
      (by simp [RectGeom.bot, RectGeom.σL, lin_zero, hL1]) (by simp [RectGeom.bot, RectGeom.σR, lin_one, Barc, α', hBarc1, hR0])
  · exact hbuild rg.top rg.bot (fun r => Barc (1 - r)) (Or.inr ⟨rfl, rfl⟩) (Or.inr rfl)
      (by simp [RectGeom.top, RectGeom.σL, lin_zero, hL0]) (by simp [RectGeom.top, RectGeom.σR, lin_one, Barc, α', hBarc1, hR0])
      (by simp [RectGeom.bot, RectGeom.σL, lin_zero, hL1]) (by simp [RectGeom.bot, RectGeom.σR, lin_one, Barc, α', hBarc0, hR1])

/-- Case C (`Lset ⊆ a.O`, `Rset ⊆ b.O` for two DISTINCT `O`-arcs `a, b ∈ M.Os`): merges `a, b` into ONE `O`-arc! -/
private theorem rect_surgery_caseC (hS : IsSurface S) (AS : SurfAtlas S)
    {s t : S} (M : ProperManifold S s t) (rg : RectGeom S)
    (hMΔ : M.U ∩ rg.Δ = rg.Lset ∪ rg.Rset)
    (l₁ m₁ m₂ : List (OArcData S)) (a b : OArcData S)
    (hOs_eq : M.Os = l₁ ++ a :: (m₁ ++ b :: m₂))
    (hL_sub : rg.Lset ⊆ a.O) (hR_sub : rg.Rset ⊆ b.O) :
    ∃ M' : ProperManifold S s t,
      M'.U \ rg.Δ = M.U \ rg.Δ ∧ M'.U ∩ rg.Δ = rg.T ∪ rg.B ∧ M'.w1Total AS = M.w1Total AS ∧
      M'.Os.length + 1 = M.Os.length := by
  have : T2Space S := hS.2.1
  let hcoc := isCoc_w1 hS AS
  obtain ⟨c₁, hc₁, hc₁_notL⟩ := exists_oArc_point_off_seg a rg ⟨le_rfl, rg.hx.le⟩
  obtain ⟨c₂, hc₂, hc₂_notR⟩ := exists_oArc_point_off_seg b rg ⟨rg.hx.le, le_rfl⟩
  obtain ⟨hα₁c, hα₁i, hα₁01, hα₁0, hα₁im, hα₁coc⟩ := oArc_rebase a.hαc a.hαi a.hα01 hc₁.1 hc₁.2
  obtain ⟨hα₂c, hα₂i, hα₂01, hα₂0, hα₂im, hα₂coc⟩ := oArc_rebase b.hαc b.hαi b.hα01 hc₂.1 hc₂.2
  let α₁ := conc2 (subArc a.α c₁ 1) (subArc a.α 0 c₁)
  let α₂ := conc2 (subArc b.α c₂ 1) (subArc b.α 0 c₂)
  obtain ⟨u₁, v₁, hu₁0, huv₁, hv₁1, hLeq, hLends⟩ := subarc_param_interval_loop hα₁c hα₁i hα₁01 rg.hd rg.σL_c rg.σL_i
    (rg.σL_im ▸ hL_sub.trans (hα₁im.trans a.hαim).symm.subset) (rg.σL_im ▸ hα₁0.symm ▸ hc₁_notL)
  obtain ⟨u₂, v₂, hu₂0, huv₂, hv₂1, hReq, hRends⟩ := subarc_param_interval_loop hα₂c hα₂i hα₂01 rg.hd rg.σR_c rg.σR_i
    (rg.σR_im ▸ hR_sub.trans (hα₂im.trans b.hαim).symm.subset) (rg.σR_im ▸ hα₂0.symm ▸ hc₂_notR)
  rw [rg.σL_im] at hLeq; rw [rg.σR_im] at hReq
  let rest := l₁ ++ m₁ ++ m₂
  have ha_mem : a ∈ M.Os := hOs_eq ▸ List.mem_append_right l₁ (List.mem_cons_self ..)
  have hb_mem : b ∈ M.Os := hOs_eq ▸ List.mem_append_right l₁ (List.mem_cons_of_mem a (List.mem_append_right m₁ (List.mem_cons_self ..)))
  have hab_disj : Disjoint a.O b.O := by
    have hpw := M.hOs_disj; rw [hOs_eq, List.pairwise_append] at hpw
    exact (List.pairwise_cons.mp hpw.2.1).1 b (List.mem_append_right m₁ (List.mem_cons_self ..))
  have hrest_sub : ∀ c ∈ rest, c ∈ M.Os := fun c hc => by
    rw [hOs_eq]
    rcases List.mem_append.mp hc with h12 | h3
    · rcases List.mem_append.mp h12 with h1 | h2
      · exact List.mem_append_left _ h1
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ h2))
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ h3)))
  have hrest_pw : rest.Pairwise fun x y => Disjoint x.O y.O := by
    have hpw := M.hOs_disj; rw [hOs_eq, List.pairwise_append, List.pairwise_cons, List.pairwise_append, List.pairwise_cons] at hpw
    refine List.pairwise_append.mpr ⟨List.pairwise_append.mpr ⟨hpw.1, hpw.2.1.2.1, fun x hx y hy =>
      hpw.2.2 x hx y (List.mem_cons_of_mem a (List.mem_append_left _ hy))⟩, hpw.2.1.2.2.1.2, fun x hx y hy => ?_⟩
    rcases List.mem_append.mp hx with h1 | h2
    · exact hpw.2.2 x h1 y (List.mem_cons_of_mem a (List.mem_append_right _ (List.mem_cons_of_mem b hy)))
    · exact hpw.2.1.2.2.2 x h2 y (List.mem_cons_of_mem b hy)
  have hrest_disj_a : ∀ c ∈ rest, Disjoint c.O a.O := fun c hc => by
    have hpw := M.hOs_disj; rw [hOs_eq, List.pairwise_append, List.pairwise_cons, List.pairwise_append, List.pairwise_cons] at hpw
    rcases List.mem_append.mp hc with h12 | h3
    · rcases List.mem_append.mp h12 with h1 | h2
      · exact hpw.2.2 c h1 a (List.mem_cons_self ..)
      · exact (hpw.2.1.1 c (List.mem_append_left _ h2)).symm
    · exact (hpw.2.1.1 c (List.mem_append_right _ (List.mem_cons_of_mem b h3))).symm
  have hrest_disj_b : ∀ c ∈ rest, Disjoint c.O b.O := fun c hc => by
    have hpw := M.hOs_disj; rw [hOs_eq, List.pairwise_append, List.pairwise_cons, List.pairwise_append, List.pairwise_cons] at hpw
    rcases List.mem_append.mp hc with h12 | h3
    · rcases List.mem_append.mp h12 with h1 | h2
      · exact hpw.2.2 c h1 b (List.mem_cons_of_mem a (List.mem_append_right _ (List.mem_cons_self ..)))
      · exact hpw.2.1.2.2.2 c h2 b (List.mem_cons_self ..)
    · exact (hpw.2.1.2.2.1.1 c h3).symm
  have hP_disj_Δ : Disjoint M.P₀ rg.Δ := by
    rw [Set.disjoint_left]; intro x hxP hxΔ
    have h1 : x ∈ M.U ∩ rg.Δ := ⟨Or.inl hxP, hxΔ⟩; rw [hMΔ] at h1
    rcases h1 with h | h
    · exact Set.disjoint_left.mp (M.hP₀_disj a ha_mem) hxP (hL_sub h)
    · exact Set.disjoint_left.mp (M.hP₀_disj b hb_mem) hxP (hR_sub h)
  have hrest_disj_Δ : ∀ c ∈ rest, Disjoint c.O rg.Δ := fun c hc => by
    rw [Set.disjoint_left]; intro x hxc hxΔ
    have h1 : x ∈ M.U ∩ rg.Δ := ⟨Or.inr (mem_iUnion₂.mpr ⟨c, hrest_sub c hc, hxc⟩), hxΔ⟩; rw [hMΔ] at h1
    rcases h1 with h | h
    · exact Set.disjoint_left.mp (hrest_disj_a c hc) hxc (hL_sub h)
    · exact Set.disjoint_left.mp (hrest_disj_b c hc) hxc (hR_sub h)
  have haΔ : ∀ r ∈ Icc (0 : ℝ) 1, α₁ r ∈ rg.Δ ↔ r ∈ Icc u₁ v₁ := fun r hr => by
    constructor
    · intro hΔr; have h1 : α₁ r ∈ M.U ∩ rg.Δ := ⟨Or.inr (mem_iUnion₂.mpr ⟨a, ha_mem, (hα₁im.trans a.hαim) ▸ ⟨r, hr, rfl⟩⟩), hΔr⟩; rw [hMΔ] at h1
      rcases h1 with hL | hR
      · obtain ⟨r', hr', hre⟩ := hLeq.symm ▸ hL
        have hlt : r < 1 := lt_of_le_of_ne hr.2 fun h1 => hc₁_notL (by rw [h1] at hL; dsimp only [α₁] at hL; rw [← hα₁01, hα₁0] at hL; exact hL)
        exact (hα₁i ⟨hr.1, hlt⟩ ⟨by linarith [hr'.1], by linarith [hr'.2]⟩ hre.symm) ▸ hr'
      · exact (Set.disjoint_left.mp hab_disj ((hα₁im.trans a.hαim) ▸ ⟨r, hr, rfl⟩) (hR_sub hR)).elim
    · intro hru; exact rg.L_subΔ (hLeq ▸ ⟨r, hru, rfl⟩)
  have hbΔ : ∀ r ∈ Icc (0 : ℝ) 1, α₂ r ∈ rg.Δ ↔ r ∈ Icc u₂ v₂ := fun r hr => by
    constructor
    · intro hΔr; have h1 : α₂ r ∈ M.U ∩ rg.Δ := ⟨Or.inr (mem_iUnion₂.mpr ⟨b, hb_mem, (hα₂im.trans b.hαim) ▸ ⟨r, hr, rfl⟩⟩), hΔr⟩; rw [hMΔ] at h1
      rcases h1 with hL | hR
      · exact (Set.disjoint_left.mp hab_disj (hL_sub hL) ((hα₂im.trans b.hαim) ▸ ⟨r, hr, rfl⟩)).elim
      · obtain ⟨r', hr', hre⟩ := hReq.symm ▸ hR
        have hlt : r < 1 := lt_of_le_of_ne hr.2 fun h1 => hc₂_notR (by rw [h1] at hR; dsimp only [α₂] at hR; rw [← hα₂01, hα₂0] at hR; exact hR)
        exact (hα₂i ⟨hr.1, hlt⟩ ⟨by linarith [hr'.1], by linarith [hr'.2]⟩ hre.symm) ▸ hr'
    · intro hru; exact rg.R_subΔ (hReq ▸ ⟨r, hru, rfl⟩)
  obtain ⟨hAarcc, hAarci, hAarc0, hAarc1, hAarcim, hAarccoc⟩ := loop_complement_arc hα₁c hα₁i hα₁01 hu₁0 huv₁ hv₁1
  obtain ⟨hBarcc, hBarci, hBarc0, hBarc1, hBarcim, hBarccoc⟩ := loop_complement_arc hα₂c hα₂i hα₂01 hu₂0 huv₂ hv₂1
  let Aarc := conc2 (subArc α₁ v₁ 1) (subArc α₁ 0 u₁)
  let Barc := conc2 (subArc α₂ v₂ 1) (subArc α₂ 0 u₂)
  let Lc := subArc α₁ u₁ v₁; let Rc := subArc α₂ u₂ v₂
  have hAarcΔ : ∀ r ∈ Icc (0 : ℝ) 1, Aarc r ∈ rg.Δ → r = 0 ∨ r = 1 := fun r hr hΔ => by
    dsimp only [Aarc, conc2] at hΔ; split_ifs at hΔ with hhalf
    · have m := lin_mapsTo_Icc hv₁1.le (show 2 * r ∈ Icc (0 : ℝ) 1 from ⟨by linarith [hr.1], by linarith⟩)
      change α₁ (lin v₁ 1 (2 * r)) ∈ rg.Δ at hΔ
      have heq : lin v₁ 1 (2 * r) = v₁ := le_antisymm ((haΔ _ ⟨by linarith [m.1], m.2⟩).mp hΔ).2 m.1
      simp only [lin] at heq; exact Or.inl (by nlinarith)
    · have m := lin_mapsTo_Icc hu₁0.le (show 2 * r - 1 ∈ Icc (0 : ℝ) 1 from ⟨by linarith, by linarith [hr.2]⟩)
      change α₁ (lin 0 u₁ (2 * r - 1)) ∈ rg.Δ at hΔ
      have heq : lin 0 u₁ (2 * r - 1) = u₁ := le_antisymm m.2 ((haΔ _ ⟨m.1, by linarith [m.2]⟩).mp hΔ).1
      simp only [lin] at heq; exact Or.inr (by nlinarith)
  have hBarcΔ : ∀ r ∈ Icc (0 : ℝ) 1, Barc r ∈ rg.Δ → r = 0 ∨ r = 1 := fun r hr hΔ => by
    dsimp only [Barc, conc2] at hΔ; split_ifs at hΔ with hhalf
    · have m := lin_mapsTo_Icc hv₂1.le (show 2 * r ∈ Icc (0 : ℝ) 1 from ⟨by linarith [hr.1], by linarith⟩)
      change α₂ (lin v₂ 1 (2 * r)) ∈ rg.Δ at hΔ
      have heq : lin v₂ 1 (2 * r) = v₂ := le_antisymm ((hbΔ _ ⟨by linarith [m.1], m.2⟩).mp hΔ).2 m.1
      simp only [lin] at heq; exact Or.inl (by nlinarith)
    · have m := lin_mapsTo_Icc hu₂0.le (show 2 * r - 1 ∈ Icc (0 : ℝ) 1 from ⟨by linarith, by linarith [hr.2]⟩)
      change α₂ (lin 0 u₂ (2 * r - 1)) ∈ rg.Δ at hΔ
      have heq : lin 0 u₂ (2 * r - 1) = u₂ := le_antisymm m.2 ((hbΔ _ ⟨m.1, by linarith [m.2]⟩).mp hΔ).1
      simp only [lin] at heq; exact Or.inr (by nlinarith)
  have hAarc_sub : Aarc '' Icc 0 1 ⊆ a.O := by
    rw [hAarcim, ← a.hαim, ← hα₁im]; exact image_mono (union_subset (Icc_subset_Icc_right (by linarith)) (Icc_subset_Icc_left (by linarith)))
  have hBarc_sub : Barc '' Icc 0 1 ⊆ b.O := by
    rw [hBarcim, ← b.hαim, ← hα₂im]; exact image_mono (union_subset (Icc_subset_Icc_right (by linarith)) (Icc_subset_Icc_left (by linarith)))
  have hcancel : cocInt (w1 AS) Lc + cocInt (w1 AS) Rc = cocInt (w1 AS) rg.bot + cocInt (w1 AS) rg.top :=
    rect_w1_cancel hS AS rg
      (continuousOn_subArc huv₁.le (hα₁c.mono (Icc_subset_Icc (by linarith) (by linarith))))
      (continuousOn_subArc huv₂.le (hα₂c.mono (Icc_subset_Icc (by linarith) (by linarith))))
      (by rw [subArc_image huv₁.le, hLeq]; exact rg.L_subΔ) (by rw [subArc_image huv₂.le, hReq]; exact rg.R_subΔ)
      (by simpa [Lc, subArc_zero, subArc_one] using hLends) (by simpa [Rc, subArc_zero, subArc_one] using hRends)
  have hext : (Aarc '' Icc 0 1 ∪ Barc '' Icc 0 1 ∪ rg.T ∪ rg.B) \ rg.Δ = (a.O ∪ b.O) \ rg.Δ ∧
      (Aarc '' Icc 0 1 ∪ Barc '' Icc 0 1 ∪ rg.T ∪ rg.B) ∩ rg.Δ = rg.T ∪ rg.B := by
    constructor
    · ext x; constructor
      · rintro ⟨((hx | hx) | hxT) | hxB, hxΔ⟩
        · exact ⟨Or.inl (hAarc_sub hx), hxΔ⟩
        · exact ⟨Or.inr (hBarc_sub hx), hxΔ⟩
        · exact (hxΔ (rg.T_subΔ hxT)).elim
        · exact (hxΔ (rg.B_subΔ hxB)).elim
      · rintro ⟨hxa | hxb, hxΔ⟩
        · obtain ⟨r, hr, rfl⟩ := (hα₁im.trans a.hαim) ▸ hxa
          have hnot : r ∉ Icc u₁ v₁ := fun h => hxΔ ((haΔ r hr).mpr h)
          refine ⟨Or.inl (Or.inl (Or.inl ?_)), hxΔ⟩; rw [hAarcim]
          by_cases h1 : r ≤ u₁; · exact ⟨r, Or.inl ⟨hr.1, h1⟩, rfl⟩
          · exact ⟨r, Or.inr ⟨by by_contra h; exact hnot ⟨le_of_not_ge h1, le_of_not_ge h⟩, hr.2⟩, rfl⟩
        · obtain ⟨r, hr, rfl⟩ := (hα₂im.trans b.hαim) ▸ hxb
          have hnot : r ∉ Icc u₂ v₂ := fun h => hxΔ ((hbΔ r hr).mpr h)
          refine ⟨Or.inl (Or.inl (Or.inr ?_)), hxΔ⟩; rw [hBarcim]
          by_cases h1 : r ≤ u₂; · exact ⟨r, Or.inl ⟨hr.1, h1⟩, rfl⟩
          · exact ⟨r, Or.inr ⟨by by_contra h; exact hnot ⟨le_of_not_ge h1, le_of_not_ge h⟩, hr.2⟩, rfl⟩
    · ext x; constructor
      · rintro ⟨((⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩) | hxT) | hxB, hxΔ⟩
        · rcases hAarcΔ r hr hxΔ with rfl | rfl
          · dsimp only [Aarc]; rw [hAarc0]; rcases hLends with ⟨_, he⟩ | ⟨_, he⟩
            · exact Or.inl (he ▸ rg.top_im ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [RectGeom.top, RectGeom.σL, lin_zero]⟩)
            · exact Or.inr (he ▸ rg.bot_im ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [RectGeom.bot, RectGeom.σL, lin_zero]⟩)
          · dsimp only [Aarc]; rw [hAarc1]; rcases hLends with ⟨he, _⟩ | ⟨he, _⟩
            · exact Or.inr (he ▸ rg.bot_im ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [RectGeom.bot, RectGeom.σL, lin_zero]⟩)
            · exact Or.inl (he ▸ rg.top_im ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [RectGeom.top, RectGeom.σL, lin_zero]⟩)
        · rcases hBarcΔ r hr hxΔ with rfl | rfl
          · dsimp only [Barc]; rw [hBarc0]; rcases hRends with ⟨_, he⟩ | ⟨_, he⟩
            · exact Or.inl (he ▸ rg.top_im ▸ ⟨1, ⟨zero_le_one, le_rfl⟩, by simp [RectGeom.top, RectGeom.σR, lin_one]⟩)
            · exact Or.inr (he ▸ rg.bot_im ▸ ⟨1, ⟨zero_le_one, le_rfl⟩, by simp [RectGeom.bot, RectGeom.σR, lin_one]⟩)
          · dsimp only [Barc]; rw [hBarc1]; rcases hRends with ⟨he, _⟩ | ⟨he, _⟩
            · exact Or.inr (he ▸ rg.bot_im ▸ ⟨1, ⟨zero_le_one, le_rfl⟩, by simp [RectGeom.bot, RectGeom.σR, lin_one]⟩)
            · exact Or.inl (he ▸ rg.top_im ▸ ⟨1, ⟨zero_le_one, le_rfl⟩, by simp [RectGeom.top, RectGeom.σR, lin_one]⟩)
        · exact Or.inl hxT
        · exact Or.inr hxB
      · rintro (hxT | hxB)
        · exact ⟨Or.inl (Or.inr hxT), rg.T_subΔ hxT⟩
        · exact ⟨Or.inr hxB, rg.B_subΔ hxB⟩
  have hbuild : ∀ (seg₁ seg₂ B_dir : ℝ → S), (seg₁ = rg.bot ∧ seg₂ = rg.top ∨ seg₁ = rg.top ∧ seg₂ = rg.bot) →
      (B_dir = Barc ∨ B_dir = fun r => Barc (1 - r)) →
      seg₁ 0 = Aarc 1 → seg₁ 1 = B_dir 0 → seg₂ 0 = Aarc 0 → seg₂ 1 = B_dir 1 →
      ∃ M' : ProperManifold S s t,
        M'.U \ rg.Δ = M.U \ rg.Δ ∧ M'.U ∩ rg.Δ = rg.T ∪ rg.B ∧ M'.w1Total AS = M.w1Total AS ∧ M'.Os.length + 1 = M.Os.length := by
    intro seg₁ seg₂ B_dir hsegs hBdir hs10 hs11 hs20 hs21
    have h1c : ContinuousOn seg₁ (Icc 0 1) := hsegs.elim (fun h => h.1 ▸ rg.bot_c) (fun h => h.1 ▸ rg.top_c)
    have h2c : ContinuousOn seg₂ (Icc 0 1) := hsegs.elim (fun h => h.2 ▸ rg.top_c) (fun h => h.2 ▸ rg.bot_c)
    have h1i : InjOn seg₁ (Icc 0 1) := hsegs.elim (fun h => h.1 ▸ rg.bot_i) (fun h => h.1 ▸ rg.top_i)
    have h2i : InjOn seg₂ (Icc 0 1) := hsegs.elim (fun h => h.2 ▸ rg.top_i) (fun h => h.2 ▸ rg.bot_i)
    have h12 : Disjoint (seg₁ '' Icc 0 1) (seg₂ '' Icc 0 1) :=
      hsegs.elim (fun h => h.1 ▸ h.2 ▸ rg.bot_im ▸ rg.top_im ▸ rg.TB_disj.symm)
        (fun h => h.1 ▸ h.2 ▸ rg.top_im ▸ rg.bot_im ▸ rg.TB_disj)
    have h1sub : seg₁ '' Icc 0 1 ⊆ rg.Δ := hsegs.elim (fun h => h.1 ▸ rg.bot_subΔ) (fun h => h.1 ▸ rg.top_subΔ)
    have h2sub : seg₂ '' Icc 0 1 ⊆ rg.Δ := hsegs.elim (fun h => h.2 ▸ rg.top_subΔ) (fun h => h.2 ▸ rg.bot_subΔ)
    have him12 : seg₁ '' Icc 0 1 ∪ seg₂ '' Icc 0 1 = rg.T ∪ rg.B :=
      hsegs.elim (fun h => by rw [h.1, h.2, rg.bot_im, rg.top_im, union_comm]) (fun h => by rw [h.1, h.2, rg.top_im, rg.bot_im])
    have hBdc : ContinuousOn B_dir (Icc 0 1) := hBdir.elim (fun h => h ▸ hBarcc) (fun h => h ▸ continuousOn_rev hBarcc)
    have hBdi : InjOn B_dir (Icc 0 1) := hBdir.elim (fun h => h ▸ hBarci) (fun h => h ▸ injOn_rev hBarci)
    have hBdim : B_dir '' Icc 0 1 = Barc '' Icc 0 1 := hBdir.elim (fun h => h ▸ rfl) (fun h => h ▸ rev_image Barc)
    have hBdΔ : ∀ r ∈ Icc (0 : ℝ) 1, B_dir r ∈ rg.Δ → r = 0 ∨ r = 1 := fun r hr hΔ => by
      rcases hBdir with rfl | rfl
      · exact hBarcΔ r hr hΔ
      · rcases hBarcΔ (1 - r) ⟨by linarith [hr.2], by linarith [hr.1]⟩ hΔ with h | h
        · exact Or.inr (by linarith)
        · exact Or.inl (by linarith)
    have hBdcoc : cocInt (w1 AS) B_dir = cocInt (w1 AS) Barc :=
      hBdir.elim (fun h => h ▸ rfl) (fun h => h ▸ cocInt_rev_zmod2 hcoc hBarcc)
    let rseg₂ := fun r => seg₂ (1 - r)
    obtain ⟨hαc, hαi, hα01, hαim0, hαcoc⟩ :=
      splice_O_22 hAarcc hBdc h1c (continuousOn_rev h2c) hAarci hBdi h1i (injOn_rev h2i)
        hs10.symm hs11 (by simp [hs21]) (by simp [hs20]; rfl)
        (hab_disj.mono hAarc_sub (hBdim ▸ hBarc_sub)) (by rw [rev_image]; exact h12)
        h1sub (by rw [rev_image]; exact h2sub) hAarcΔ hBdΔ
    let α_m := conc2 (conc2 Aarc seg₁) (conc2 B_dir rseg₂)
    have hαim : α_m '' Icc 0 1 = Aarc '' Icc 0 1 ∪ Barc '' Icc 0 1 ∪ rg.T ∪ rg.B := by
      rw [hαim0, hBdim, rev_image, union_assoc (Aarc '' Icc 0 1 ∪ Barc '' Icc 0 1), him12, ← union_assoc]
    have hαint : α_m '' Icc 0 1 ⊆ (bd S)ᶜ := by
      rw [hαim]; rintro x (((h1 | h2) | h3) | h4) hbd
      · exact a.hOint (hAarc_sub h1) hbd
      · exact b.hOint (hBarc_sub h2) hbd
      · exact rg.hΔint (rg.T_subΔ h3) hbd
      · exact rg.hΔint (rg.B_subΔ h4) hbd
    let am : OArcData S := OArcData.ofLoop α_m hαc hαi hα01 hαint
    have hP_disj_m : Disjoint M.P₀ am.O := by
      rw [Set.disjoint_left]; intro x hxP hxm
      by_cases hxΔ : x ∈ rg.Δ
      · exact Set.disjoint_left.mp hP_disj_Δ hxP hxΔ
      · rcases (show x ∈ (a.O ∪ b.O) \ rg.Δ from hext.1 ▸ ⟨hαim ▸ hxm, hxΔ⟩).1 with hxa | hxb
        · exact Set.disjoint_left.mp (M.hP₀_disj a ha_mem) hxP hxa
        · exact Set.disjoint_left.mp (M.hP₀_disj b hb_mem) hxP hxb
    have hm_disj_rest : ∀ c ∈ rest, Disjoint am.O c.O := fun c hc => by
      rw [Set.disjoint_left]; intro x hxm hxc
      by_cases hxΔ : x ∈ rg.Δ
      · exact Set.disjoint_left.mp (hrest_disj_Δ c hc) hxc hxΔ
      · rcases (show x ∈ (a.O ∪ b.O) \ rg.Δ from hext.1 ▸ ⟨hαim ▸ hxm, hxΔ⟩).1 with hxa | hxb
        · exact Set.disjoint_left.mp (hrest_disj_a c hc) hxc hxa
        · exact Set.disjoint_left.mp (hrest_disj_b c hc) hxc hxb
    let M' : ProperManifold S s t :=
      { P₀ := M.P₀, γ₀ := M.γ₀, hP₀b := M.hP₀b, hP₀l := M.hP₀l,
        hγ₀c := M.hγ₀c, hγ₀i := M.hγ₀i, hγ₀0 := M.hγ₀0, hγ₀1 := M.hγ₀1, hγ₀im := M.hγ₀im,
        Os := am :: rest, hOs_disj := List.pairwise_cons.mpr ⟨hm_disj_rest, hrest_pw⟩,
        hP₀_disj := fun c hc => by
          rcases List.mem_cons.mp hc with rfl | hc'
          · exact hP_disj_m
          · exact M.hP₀_disj c (hrest_sub c hc') }
    have hMU_eq : M.U = (M.P₀ ∪ ProperManifold.listUnion rest) ∪ (a.O ∪ b.O) := by
      simp only [ProperManifold.U, hOs_eq, ProperManifold.listUnion_append, ProperManifold.listUnion_cons, rest]
      ext x; simp only [mem_union]; exact ⟨by rintro (h | (h | (h | (h | (h | h))))) <;> simp [*], by rintro ((h | ((h | h) | h)) | (h | h)) <;> simp [*]⟩
    have hM'U_eq : M'.U = (M.P₀ ∪ ProperManifold.listUnion rest) ∪ am.O := by
      simp only [ProperManifold.U, M', ProperManifold.listUnion_cons]
      ext x; simp only [mem_union]; exact ⟨by rintro (h | (h | h)) <;> simp [*], by rintro ((h | h) | h) <;> simp [*]⟩
    refine ⟨M', ?_, ?_, ?_, ?_⟩
    · simp only [hM'U_eq, hMU_eq, union_sdiff_distrib,
        show am.O \ rg.Δ = (a.O ∪ b.O) \ rg.Δ from by rw [show am.O = α_m '' Icc 0 1 from rfl, hαim, hext.1]]
    · rw [hM'U_eq, union_inter_distrib_right]
      have h0 : (M.P₀ ∪ ProperManifold.listUnion rest) ∩ rg.Δ = ∅ := by
        rw [eq_empty_iff_forall_notMem]; rintro x ⟨hxP | hxO, hxΔ⟩
        · exact Set.disjoint_left.mp hP_disj_Δ hxP hxΔ
        · obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp hxO; exact Set.disjoint_left.mp (hrest_disj_Δ c hc) hxc hxΔ
      rw [h0, empty_union, show am.O = α_m '' Icc 0 1 from rfl, hαim, hext.2]
    · simp only [ProperManifold.w1Total, M', hOs_eq, List.map_append, List.map_cons, List.sum_append, List.sum_cons, rest, am, OArcData.ofLoop]
      rw [hαcoc hcoc, hBdcoc, hAarccoc hcoc, hBarccoc hcoc, cocInt_rev_zmod2 hcoc h2c,
          ← hα₁coc hcoc, cocInt_split_three hcoc hα₁c hu₁0 huv₁ hv₁1,
          ← hα₂coc hcoc, cocInt_split_three hcoc hα₂c hu₂0 huv₂ hv₂1]
      have hss : cocInt (w1 AS) seg₁ + cocInt (w1 AS) seg₂ = cocInt (w1 AS) rg.bot + cocInt (w1 AS) rg.top :=
        hsegs.elim (fun h => by rw [h.1, h.2]) (fun h => by rw [h.1, h.2]; ring)
      change cocInt (w1 AS) M.γ₀ +
          ((cocInt (w1 AS) (subArc α₁ v₁ 1) + cocInt (w1 AS) (subArc α₁ 0 u₁) +
            (cocInt (w1 AS) (subArc α₂ v₂ 1) + cocInt (w1 AS) (subArc α₂ 0 u₂)) +
            cocInt (w1 AS) seg₁ + cocInt (w1 AS) seg₂) +
            ((l₁.map fun c => cocInt (w1 AS) c.α).sum + (m₁.map fun c => cocInt (w1 AS) c.α).sum +
              (m₂.map fun c => cocInt (w1 AS) c.α).sum)) =
        cocInt (w1 AS) M.γ₀ +
          ((l₁.map fun c => cocInt (w1 AS) c.α).sum +
            ((cocInt (w1 AS) (subArc α₁ 0 u₁) + (cocInt (w1 AS) Lc + cocInt (w1 AS) (subArc α₁ v₁ 1))) +
              ((m₁.map fun c => cocInt (w1 AS) c.α).sum +
                ((cocInt (w1 AS) (subArc α₂ 0 u₂) + (cocInt (w1 AS) Rc + cocInt (w1 AS) (subArc α₂ v₂ 1))) +
                  (m₂.map fun c => cocInt (w1 AS) c.α).sum))))
      linear_combination hss - hcancel
    · simp only [M', rest, hOs_eq, List.length_cons, List.length_append]; omega
  rcases hLends with ⟨hL0, hL1⟩ | ⟨hL0, hL1⟩ <;> rcases hRends with ⟨hR0, hR1⟩ | ⟨hR0, hR1⟩
  · exact hbuild rg.bot rg.top (fun r => Barc (1 - r)) (Or.inl ⟨rfl, rfl⟩) (Or.inr rfl)
      (by simp [RectGeom.bot, RectGeom.σL, lin_zero, Aarc, α₁, hAarc1, hL0]) (by simp [RectGeom.bot, RectGeom.σR, lin_one, Barc, α₂, hBarc1, hR0])
      (by simp [RectGeom.top, RectGeom.σL, lin_zero, Aarc, α₁, hAarc0, hL1]) (by simp [RectGeom.top, RectGeom.σR, lin_one, Barc, α₂, hBarc0, hR1])
  · exact hbuild rg.bot rg.top Barc (Or.inl ⟨rfl, rfl⟩) (Or.inl rfl)
      (by simp [RectGeom.bot, RectGeom.σL, lin_zero, Aarc, α₁, hAarc1, hL0]) (by simp [RectGeom.bot, RectGeom.σR, lin_one, Barc, α₂, hBarc0, hR1])
      (by simp [RectGeom.top, RectGeom.σL, lin_zero, Aarc, α₁, hAarc0, hL1]) (by simp [RectGeom.top, RectGeom.σR, lin_one, Barc, α₂, hBarc1, hR0])
  · exact hbuild rg.top rg.bot Barc (Or.inr ⟨rfl, rfl⟩) (Or.inl rfl)
      (by simp [RectGeom.top, RectGeom.σL, lin_zero, Aarc, α₁, hAarc1, hL0]) (by simp [RectGeom.top, RectGeom.σR, lin_one, Barc, α₂, hBarc0, hR1])
      (by simp [RectGeom.bot, RectGeom.σL, lin_zero, Aarc, α₁, hAarc0, hL1]) (by simp [RectGeom.bot, RectGeom.σR, lin_one, Barc, α₂, hBarc1, hR0])
  · exact hbuild rg.top rg.bot (fun r => Barc (1 - r)) (Or.inr ⟨rfl, rfl⟩) (Or.inr rfl)
      (by simp [RectGeom.top, RectGeom.σL, lin_zero, Aarc, α₁, hAarc1, hL0]) (by simp [RectGeom.top, RectGeom.σR, lin_one, Barc, α₂, hBarc1, hR0])
      (by simp [RectGeom.bot, RectGeom.σL, lin_zero, Aarc, α₁, hAarc0, hL1]) (by simp [RectGeom.bot, RectGeom.σR, lin_one, Barc, α₂, hBarc0, hR1])

/-- Case D (`Lset, Rset ⊆ a.O` for the SAME `O`-arc `a ∈ M.Os`, rebased off `Lset ∪ Rset` with `v₁ < u₂`). -/
private theorem rect_surgery_caseD (hS : IsSurface S) (AS : SurfAtlas S)
    {s t : S} (M : ProperManifold S s t) (rg : RectGeom S)
    (hMΔ : M.U ∩ rg.Δ = rg.Lset ∪ rg.Rset)
    (l₁ l₂ : List (OArcData S)) (a : OArcData S) (hOs_eq : M.Os = l₁ ++ a :: l₂)
    {α' : ℝ → S} (hα'c : ContinuousOn α' (Icc 0 1)) (hα'i : InjOn α' (Ico 0 1))
    (hα'01 : α' 0 = α' 1) (hα'im : α' '' Icc 0 1 = a.O) (hα'coc : cocInt (w1 AS) α' = cocInt (w1 AS) a.α)
    {u₁ v₁ u₂ v₂ : ℝ} (hu₁0 : 0 < u₁) (huv₁ : u₁ < v₁) (hv₁u₂ : v₁ < u₂) (huv₂ : u₂ < v₂) (hv₂1 : v₂ < 1)
    (hL_eq : α' '' Icc u₁ v₁ = rg.Lset) (hR_eq : α' '' Icc u₂ v₂ = rg.Rset)
    (hL_ends : (α' u₁ = rg.σL (-rg.d) ∧ α' v₁ = rg.σL rg.d) ∨ (α' u₁ = rg.σL rg.d ∧ α' v₁ = rg.σL (-rg.d)))
    (hR_ends : (α' u₂ = rg.σR (-rg.d) ∧ α' v₂ = rg.σR rg.d) ∨ (α' u₂ = rg.σR rg.d ∧ α' v₂ = rg.σR (-rg.d))) :
    ∃ M' : ProperManifold S s t,
      M'.U \ rg.Δ = M.U \ rg.Δ ∧ M'.U ∩ rg.Δ = rg.T ∪ rg.B ∧ M'.w1Total AS = M.w1Total AS := by
  have : T2Space S := hS.2.1
  let hcoc := isCoc_w1 hS AS
  let rest := l₁ ++ l₂
  have ha_mem : a ∈ M.Os := hOs_eq ▸ List.mem_append_right l₁ (List.mem_cons_self ..)
  have hrest_sub : ∀ c ∈ rest, c ∈ M.Os := fun c hc => hOs_eq ▸ by
    rcases List.mem_append.mp hc with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  have hrest_pw : rest.Pairwise fun x y => Disjoint x.O y.O := by
    have hpw := M.hOs_disj; rw [hOs_eq, List.pairwise_append] at hpw
    exact List.pairwise_append.mpr ⟨hpw.1, (List.pairwise_cons.mp hpw.2.1).2, fun x hx y hy => hpw.2.2 x hx y (List.mem_cons_of_mem a hy)⟩
  have hrest_disj_a : ∀ c ∈ rest, Disjoint c.O a.O := fun c hc => by
    have hpw := M.hOs_disj; rw [hOs_eq, List.pairwise_append] at hpw
    rcases List.mem_append.mp hc with h1 | h2
    · exact hpw.2.2 c h1 a (List.mem_cons_self ..)
    · exact ((List.pairwise_cons.mp hpw.2.1).1 c h2).symm
  have hL_sub_a : rg.Lset ⊆ a.O := by rw [← hL_eq, ← hα'im]; exact image_mono (Icc_subset_Icc (by linarith) (by linarith))
  have hR_sub_a : rg.Rset ⊆ a.O := by rw [← hR_eq, ← hα'im]; exact image_mono (Icc_subset_Icc (by linarith) (by linarith))
  have hP_disj_Δ : Disjoint M.P₀ rg.Δ := by
    rw [Set.disjoint_left]; intro x hxP hxΔ
    have h1 : x ∈ M.U ∩ rg.Δ := ⟨Or.inl hxP, hxΔ⟩; rw [hMΔ] at h1
    rcases h1 with h | h
    · exact Set.disjoint_left.mp (M.hP₀_disj a ha_mem) hxP (hL_sub_a h)
    · exact Set.disjoint_left.mp (M.hP₀_disj a ha_mem) hxP (hR_sub_a h)
  have hrest_disj_Δ : ∀ c ∈ rest, Disjoint c.O rg.Δ := fun c hc => by
    rw [Set.disjoint_left]; intro x hxc hxΔ
    have h1 : x ∈ M.U ∩ rg.Δ := ⟨Or.inr (mem_iUnion₂.mpr ⟨c, hrest_sub c hc, hxc⟩), hxΔ⟩; rw [hMΔ] at h1
    rcases h1 with h | h
    · exact Set.disjoint_left.mp (hrest_disj_a c hc) hxc (hL_sub_a h)
    · exact Set.disjoint_left.mp (hrest_disj_a c hc) hxc (hR_sub_a h)
  have hα'0_notΔ : α' 0 ∉ rg.Δ := fun h0Δ => by
    have h1 : α' 0 ∈ M.U ∩ rg.Δ := ⟨Or.inr (mem_iUnion₂.mpr ⟨a, ha_mem, hα'im ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩⟩), h0Δ⟩
    rw [hMΔ, ← hL_eq, ← hR_eq] at h1
    rcases h1 with ⟨r, hr, hre⟩ | ⟨r, hr, hre⟩
    · have := hα'i ⟨le_rfl, zero_lt_one⟩ ⟨by linarith [hr.1], by linarith [hr.2]⟩ hre.symm; linarith [hr.1]
    · have := hα'i ⟨le_rfl, zero_lt_one⟩ ⟨by linarith [hr.1], by linarith [hr.2]⟩ hre.symm; linarith [hr.1]
  have haΔ : ∀ r ∈ Icc (0 : ℝ) 1, α' r ∈ rg.Δ ↔ r ∈ Icc u₁ v₁ ∪ Icc u₂ v₂ := fun r hr => by
    constructor
    · intro hΔr
      have hlt : r < 1 := lt_of_le_of_ne hr.2 fun h1 => hα'0_notΔ (hα'01 ▸ h1 ▸ hΔr)
      have h1 : α' r ∈ M.U ∩ rg.Δ := ⟨Or.inr (mem_iUnion₂.mpr ⟨a, ha_mem, hα'im ▸ ⟨r, hr, rfl⟩⟩), hΔr⟩
      rw [hMΔ, ← hL_eq, ← hR_eq] at h1
      rcases h1 with ⟨r', hr', hre⟩ | ⟨r', hr', hre⟩
      · exact Or.inl ((hα'i ⟨hr.1, hlt⟩ ⟨by linarith [hr'.1], by linarith [hr'.2]⟩ hre.symm) ▸ hr')
      · exact Or.inr ((hα'i ⟨hr.1, hlt⟩ ⟨by linarith [hr'.1], by linarith [hr'.2]⟩ hre.symm) ▸ hr')
    · rintro (h | h)
      · exact rg.L_subΔ (hL_eq ▸ ⟨r, h, rfl⟩)
      · exact rg.R_subΔ (hR_eq ▸ ⟨r, h, rfl⟩)
  let Lc := subArc α' u₁ v₁; let Rc := subArc α' u₂ v₂; let E₁ := subArc α' v₁ u₂
  obtain ⟨hE₂c, hE₂i, hE₂0, hE₂1, hE₂im, hE₂coc⟩ := loop_complement_arc hα'c hα'i hα'01 hu₁0 (huv₁.trans (hv₁u₂.trans huv₂)) hv₂1
  let E₂ := conc2 (subArc α' v₂ 1) (subArc α' 0 u₁)
  have hE₁c : ContinuousOn E₁ (Icc 0 1) := continuousOn_subArc hv₁u₂.le (hα'c.mono (Icc_subset_Icc (by linarith) (by linarith)))
  have hE₁i : InjOn E₁ (Icc 0 1) := injOn_subArc hv₁u₂ (hα'i.mono (show Icc v₁ u₂ ⊆ Ico 0 1 from fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩))
  have hE12 : Disjoint (E₁ '' Icc 0 1) (E₂ '' Icc 0 1) := by
    rw [subArc_image hv₁u₂.le, hE₂im, Set.disjoint_left]
    rintro _ ⟨r₁, hr₁, rfl⟩ ⟨r₂, hr₂ | hr₂, he⟩
    · have := hα'i ⟨by linarith [hr₁.1], by linarith [hr₁.2]⟩ ⟨hr₂.1, by linarith [hr₂.2]⟩ he.symm; linarith [hr₁.1, hr₂.2]
    · rcases hr₂.2.eq_or_lt with rfl | hlt
      · rw [← hα'01] at he; have := hα'i ⟨by linarith [hr₁.1], by linarith [hr₁.2]⟩ ⟨le_rfl, zero_lt_one⟩ he.symm; linarith [hr₁.1]
      · have := hα'i ⟨by linarith [hr₁.1], by linarith [hr₁.2]⟩ ⟨by linarith [hr₂.1], hlt⟩ he.symm; linarith [hr₁.2, hr₂.1]
  have hE₁Δ : ∀ r ∈ Icc (0 : ℝ) 1, E₁ r ∈ rg.Δ → r = 0 ∨ r = 1 := fun r hr hΔ => by
    have m := lin_mapsTo_Icc hv₁u₂.le hr
    rcases (haΔ _ ⟨by linarith [m.1], by linarith [m.2]⟩).mp hΔ with h | h
    · have : lin v₁ u₂ r = v₁ := le_antisymm h.2 m.1; simp only [lin] at this; exact Or.inl (by nlinarith)
    · have : lin v₁ u₂ r = u₂ := le_antisymm m.2 h.1; simp only [lin] at this; exact Or.inr (by nlinarith)
  have hE₂Δ : ∀ r ∈ Icc (0 : ℝ) 1, E₂ r ∈ rg.Δ → r = 0 ∨ r = 1 := fun r hr hΔ => by
    dsimp only [E₂, conc2] at hΔ; split_ifs at hΔ with hhalf
    · have m := lin_mapsTo_Icc hv₂1.le (show 2 * r ∈ Icc (0 : ℝ) 1 from ⟨by linarith [hr.1], by linarith⟩)
      change α' (lin v₂ 1 (2 * r)) ∈ rg.Δ at hΔ
      rcases (haΔ _ ⟨by linarith [m.1], m.2⟩).mp hΔ with h | h
      · linarith [m.1, h.2]
      · have : lin v₂ 1 (2 * r) = v₂ := le_antisymm h.2 m.1; simp only [lin] at this; exact Or.inl (by nlinarith)
    · have m := lin_mapsTo_Icc hu₁0.le (show 2 * r - 1 ∈ Icc (0 : ℝ) 1 from ⟨by linarith, by linarith [hr.2]⟩)
      change α' (lin 0 u₁ (2 * r - 1)) ∈ rg.Δ at hΔ
      rcases (haΔ _ ⟨m.1, by linarith [m.2]⟩).mp hΔ with h | h
      · have : lin 0 u₁ (2 * r - 1) = u₁ := le_antisymm m.2 h.1; simp only [lin] at this; exact Or.inr (by nlinarith)
      · linarith [m.2, h.1]
  have hE₁_sub : E₁ '' Icc 0 1 ⊆ a.O := by rw [subArc_image hv₁u₂.le, ← hα'im]; exact image_mono (Icc_subset_Icc (by linarith) (by linarith))
  have hE₂_sub : E₂ '' Icc 0 1 ⊆ a.O := by rw [hE₂im, ← hα'im]; exact image_mono (union_subset (Icc_subset_Icc_right (by linarith)) (Icc_subset_Icc_left (by linarith)))
  have hsplit5 := cocInt_split_five hcoc hα'c hu₁0 huv₁ hv₁u₂ huv₂ hv₂1
  have hcancel : cocInt (w1 AS) Lc + cocInt (w1 AS) Rc = cocInt (w1 AS) rg.bot + cocInt (w1 AS) rg.top :=
    rect_w1_cancel hS AS rg
      (continuousOn_subArc huv₁.le (hα'c.mono (Icc_subset_Icc (by linarith) (by linarith))))
      (continuousOn_subArc huv₂.le (hα'c.mono (Icc_subset_Icc (by linarith) (by linarith))))
      (by rw [subArc_image huv₁.le, hL_eq]; exact rg.L_subΔ) (by rw [subArc_image huv₂.le, hR_eq]; exact rg.R_subΔ)
      (by simpa [Lc, subArc_zero, subArc_one] using hL_ends) (by simpa [Rc, subArc_zero, subArc_one] using hR_ends)
  have hext : (E₁ '' Icc 0 1 ∪ E₂ '' Icc 0 1 ∪ rg.T ∪ rg.B) \ rg.Δ = a.O \ rg.Δ ∧
      (E₁ '' Icc 0 1 ∪ E₂ '' Icc 0 1 ∪ rg.T ∪ rg.B) ∩ rg.Δ = rg.T ∪ rg.B := by
    constructor
    · ext x; constructor
      · rintro ⟨((hx | hx) | hxT) | hxB, hxΔ⟩
        · exact ⟨hE₁_sub hx, hxΔ⟩
        · exact ⟨hE₂_sub hx, hxΔ⟩
        · exact (hxΔ (rg.T_subΔ hxT)).elim
        · exact (hxΔ (rg.B_subΔ hxB)).elim
      · rintro ⟨hxa, hxΔ⟩; obtain ⟨r, hr, rfl⟩ := hα'im ▸ hxa
        have hnot : r ∉ Icc u₁ v₁ ∪ Icc u₂ v₂ := fun h => hxΔ ((haΔ r hr).mpr h)
        refine ⟨?_, hxΔ⟩
        by_cases h1 : r ≤ u₁
        · exact Or.inl (Or.inl (Or.inr (hE₂im ▸ ⟨r, Or.inl ⟨hr.1, h1⟩, rfl⟩)))
        · by_cases h2 : r ≤ u₂
          · exact Or.inl (Or.inl (Or.inl (by rw [subArc_image hv₁u₂.le]; exact ⟨r, ⟨by by_contra h; exact hnot (Or.inl ⟨le_of_not_ge h1, le_of_not_ge h⟩), h2⟩, rfl⟩)))
          · exact Or.inl (Or.inl (Or.inr (hE₂im ▸ ⟨r, Or.inr ⟨by by_contra h; exact hnot (Or.inr ⟨le_of_not_ge h2, le_of_not_ge h⟩), hr.2⟩, rfl⟩)))
    · ext x; constructor
      · rintro ⟨((⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩) | hxT) | hxB, hxΔ⟩
        · rcases hE₁Δ r hr hxΔ with rfl | rfl
          · dsimp only [E₁]; rw [subArc_zero]; rcases hL_ends with ⟨_, he⟩ | ⟨_, he⟩
            · exact Or.inl (he ▸ rg.top_im ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [RectGeom.top, RectGeom.σL, lin_zero]⟩)
            · exact Or.inr (he ▸ rg.bot_im ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [RectGeom.bot, RectGeom.σL, lin_zero]⟩)
          · dsimp only [E₁]; rw [subArc_one]; rcases hR_ends with ⟨he, _⟩ | ⟨he, _⟩
            · exact Or.inr (he ▸ rg.bot_im ▸ ⟨1, ⟨zero_le_one, le_rfl⟩, by simp [RectGeom.bot, RectGeom.σR, lin_one]⟩)
            · exact Or.inl (he ▸ rg.top_im ▸ ⟨1, ⟨zero_le_one, le_rfl⟩, by simp [RectGeom.top, RectGeom.σR, lin_one]⟩)
        · rcases hE₂Δ r hr hxΔ with rfl | rfl
          · dsimp only [E₂]; rw [hE₂0]; rcases hR_ends with ⟨_, he⟩ | ⟨_, he⟩
            · exact Or.inl (he ▸ rg.top_im ▸ ⟨1, ⟨zero_le_one, le_rfl⟩, by simp [RectGeom.top, RectGeom.σR, lin_one]⟩)
            · exact Or.inr (he ▸ rg.bot_im ▸ ⟨1, ⟨zero_le_one, le_rfl⟩, by simp [RectGeom.bot, RectGeom.σR, lin_one]⟩)
          · dsimp only [E₂]; rw [hE₂1]; rcases hL_ends with ⟨he, _⟩ | ⟨he, _⟩
            · exact Or.inr (he ▸ rg.bot_im ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [RectGeom.bot, RectGeom.σL, lin_zero]⟩)
            · exact Or.inl (he ▸ rg.top_im ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [RectGeom.top, RectGeom.σL, lin_zero]⟩)
        · exact Or.inl hxT
        · exact Or.inr hxB
      · rintro (hxT | hxB)
        · exact ⟨Or.inl (Or.inr hxT), rg.T_subΔ hxT⟩
        · exact ⟨Or.inr hxB, rg.B_subΔ hxB⟩
  have hMU_eq : M.U = (M.P₀ ∪ ProperManifold.listUnion rest) ∪ a.O := by
    simp only [ProperManifold.U, hOs_eq, ProperManifold.listUnion_append, ProperManifold.listUnion_cons, rest]
    ext x; simp only [mem_union]; exact ⟨by rintro (h | (h | (h | h))) <;> simp [*], by rintro ((h | (h | h)) | h) <;> simp [*]⟩
  have hPrestΔ0 : (M.P₀ ∪ ProperManifold.listUnion rest) ∩ rg.Δ = ∅ := by
    rw [eq_empty_iff_forall_notMem]; rintro x ⟨hxP | hxO, hxΔ⟩
    · exact Set.disjoint_left.mp hP_disj_Δ hxP hxΔ
    · obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp hxO; exact Set.disjoint_left.mp (hrest_disj_Δ c hc) hxc hxΔ
  -- Subcase D1 (parallel: ONE `O`-arc):
  have hpar : ∀ (seg₁ seg₂ : ℝ → S), (seg₁ = rg.bot ∧ seg₂ = rg.top ∨ seg₁ = rg.top ∧ seg₂ = rg.bot) →
      seg₁ 0 = E₂ 1 → seg₁ 1 = E₁ 1 → seg₂ 0 = E₁ 0 → seg₂ 1 = E₂ 0 →
      ∃ M' : ProperManifold S s t, M'.U \ rg.Δ = M.U \ rg.Δ ∧ M'.U ∩ rg.Δ = rg.T ∪ rg.B ∧ M'.w1Total AS = M.w1Total AS := by
    intro seg₁ seg₂ hsegs hs10 hs11 hs20 hs21
    have h1c : ContinuousOn seg₁ (Icc 0 1) := hsegs.elim (fun h => h.1 ▸ rg.bot_c) (fun h => h.1 ▸ rg.top_c)
    have h2c : ContinuousOn seg₂ (Icc 0 1) := hsegs.elim (fun h => h.2 ▸ rg.top_c) (fun h => h.2 ▸ rg.bot_c)
    have h1i : InjOn seg₁ (Icc 0 1) := hsegs.elim (fun h => h.1 ▸ rg.bot_i) (fun h => h.1 ▸ rg.top_i)
    have h2i : InjOn seg₂ (Icc 0 1) := hsegs.elim (fun h => h.2 ▸ rg.top_i) (fun h => h.2 ▸ rg.bot_i)
    have h12 : Disjoint (seg₁ '' Icc 0 1) (seg₂ '' Icc 0 1) :=
      hsegs.elim (fun h => h.1 ▸ h.2 ▸ rg.bot_im ▸ rg.top_im ▸ rg.TB_disj.symm)
        (fun h => h.1 ▸ h.2 ▸ rg.top_im ▸ rg.bot_im ▸ rg.TB_disj)
    have h1sub : seg₁ '' Icc 0 1 ⊆ rg.Δ := hsegs.elim (fun h => h.1 ▸ rg.bot_subΔ) (fun h => h.1 ▸ rg.top_subΔ)
    have h2sub : seg₂ '' Icc 0 1 ⊆ rg.Δ := hsegs.elim (fun h => h.2 ▸ rg.top_subΔ) (fun h => h.2 ▸ rg.bot_subΔ)
    have him12 : seg₁ '' Icc 0 1 ∪ seg₂ '' Icc 0 1 = rg.T ∪ rg.B :=
      hsegs.elim (fun h => by rw [h.1, h.2, rg.bot_im, rg.top_im, union_comm]) (fun h => by rw [h.1, h.2, rg.top_im, rg.bot_im])
    let rE₁ := fun r => E₁ (1 - r)
    obtain ⟨hαc, hαi, hα01, hαim0, hαcoc⟩ :=
      splice_O_22 hE₂c (continuousOn_rev hE₁c) h1c h2c hE₂i (injOn_rev hE₁i) h1i h2i
        hs10.symm (by simp [hs11]) (by simp [hs20]) hs21
        (by rw [rev_image]; exact hE12.symm) h12 h1sub h2sub hE₂Δ
        (fun r hr hΔ => by
          rcases hE₁Δ (1 - r) ⟨by linarith [hr.2], by linarith [hr.1]⟩ hΔ with h | h
          · exact Or.inr (by linarith)
          · exact Or.inl (by linarith))
    let α_new := conc2 (conc2 E₂ seg₁) (conc2 rE₁ seg₂)
    have hαim : α_new '' Icc 0 1 = E₁ '' Icc 0 1 ∪ E₂ '' Icc 0 1 ∪ rg.T ∪ rg.B := by
      rw [hαim0, rev_image, union_comm (E₂ '' Icc 0 1) (E₁ '' Icc 0 1), union_assoc (E₁ '' Icc 0 1 ∪ E₂ '' Icc 0 1), him12, ← union_assoc]
    have hαint : α_new '' Icc 0 1 ⊆ (bd S)ᶜ := by
      rw [hαim]; rintro x (((h1 | h2) | h3) | h4) hbd
      · exact a.hOint (hE₁_sub h1) hbd
      · exact a.hOint (hE₂_sub h2) hbd
      · exact rg.hΔint (rg.T_subΔ h3) hbd
      · exact rg.hΔint (rg.B_subΔ h4) hbd
    let anew : OArcData S := OArcData.ofLoop α_new hαc hαi hα01 hαint
    have hP_disj : Disjoint M.P₀ anew.O := by
      rw [Set.disjoint_left]; intro x hxP hxn
      by_cases hxΔ : x ∈ rg.Δ; · exact Set.disjoint_left.mp hP_disj_Δ hxP hxΔ
      · exact Set.disjoint_left.mp (M.hP₀_disj a ha_mem) hxP (show x ∈ a.O \ rg.Δ from hext.1 ▸ ⟨hαim ▸ hxn, hxΔ⟩).1
    have hrest_disj : ∀ c ∈ rest, Disjoint anew.O c.O := fun c hc => by
      rw [Set.disjoint_left]; intro x hxn hxc
      by_cases hxΔ : x ∈ rg.Δ; · exact Set.disjoint_left.mp (hrest_disj_Δ c hc) hxc hxΔ
      · exact Set.disjoint_left.mp (hrest_disj_a c hc) hxc (show x ∈ a.O \ rg.Δ from hext.1 ▸ ⟨hαim ▸ hxn, hxΔ⟩).1
    let M' : ProperManifold S s t :=
      { P₀ := M.P₀, γ₀ := M.γ₀, hP₀b := M.hP₀b, hP₀l := M.hP₀l,
        hγ₀c := M.hγ₀c, hγ₀i := M.hγ₀i, hγ₀0 := M.hγ₀0, hγ₀1 := M.hγ₀1, hγ₀im := M.hγ₀im,
        Os := anew :: rest, hOs_disj := List.pairwise_cons.mpr ⟨hrest_disj, hrest_pw⟩,
        hP₀_disj := fun c hc => by
          rcases List.mem_cons.mp hc with rfl | hc'
          · exact hP_disj
          · exact M.hP₀_disj c (hrest_sub c hc') }
    have hM'U : M'.U = (M.P₀ ∪ ProperManifold.listUnion rest) ∪ anew.O := by
      simp only [ProperManifold.U, M', ProperManifold.listUnion_cons]
      ext x; simp only [mem_union]; exact ⟨by rintro (h | (h | h)) <;> simp [*], by rintro ((h | h) | h) <;> simp [*]⟩
    refine ⟨M', ?_, ?_, ?_⟩
    · simp only [hM'U, hMU_eq, union_sdiff_distrib,
        show anew.O \ rg.Δ = a.O \ rg.Δ from by rw [show anew.O = α_new '' Icc 0 1 from rfl, hαim, hext.1]]
    · rw [hM'U, union_inter_distrib_right, hPrestΔ0, empty_union]
      rw [show anew.O = α_new '' Icc 0 1 from rfl, hαim, hext.2]
    · simp only [ProperManifold.w1Total, M', hOs_eq, List.map_append, List.map_cons, List.sum_append, List.sum_cons, rest, anew, OArcData.ofLoop]
      rw [hαcoc hcoc, hE₂coc hcoc, cocInt_rev_zmod2 hcoc hE₁c, ← hα'coc, hsplit5]
      have hss : cocInt (w1 AS) seg₁ + cocInt (w1 AS) seg₂ = cocInt (w1 AS) rg.bot + cocInt (w1 AS) rg.top :=
        hsegs.elim (fun h => by rw [h.1, h.2]) (fun h => by rw [h.1, h.2]; ring)
      linear_combination hss - hcancel
  -- Subcase D2 (antiparallel: TWO `O`-arcs):
  have hanti : ∀ (seg₁ seg₂ : ℝ → S), (seg₁ = rg.bot ∧ seg₂ = rg.top ∨ seg₁ = rg.top ∧ seg₂ = rg.bot) →
      seg₁ 0 = E₂ 1 → seg₁ 1 = E₂ 0 → seg₂ 0 = E₁ 0 → seg₂ 1 = E₁ 1 →
      ∃ M' : ProperManifold S s t, M'.U \ rg.Δ = M.U \ rg.Δ ∧ M'.U ∩ rg.Δ = rg.T ∪ rg.B ∧ M'.w1Total AS = M.w1Total AS := by
    intro seg₁ seg₂ hsegs hs10 hs11 hs20 hs21
    have h1c : ContinuousOn seg₁ (Icc 0 1) := hsegs.elim (fun h => h.1 ▸ rg.bot_c) (fun h => h.1 ▸ rg.top_c)
    have h2c : ContinuousOn seg₂ (Icc 0 1) := hsegs.elim (fun h => h.2 ▸ rg.top_c) (fun h => h.2 ▸ rg.bot_c)
    have h1i : InjOn seg₁ (Icc 0 1) := hsegs.elim (fun h => h.1 ▸ rg.bot_i) (fun h => h.1 ▸ rg.top_i)
    have h2i : InjOn seg₂ (Icc 0 1) := hsegs.elim (fun h => h.2 ▸ rg.top_i) (fun h => h.2 ▸ rg.bot_i)
    have h12 : Disjoint (seg₁ '' Icc 0 1) (seg₂ '' Icc 0 1) :=
      hsegs.elim (fun h => h.1 ▸ h.2 ▸ rg.bot_im ▸ rg.top_im ▸ rg.TB_disj.symm)
        (fun h => h.1 ▸ h.2 ▸ rg.top_im ▸ rg.bot_im ▸ rg.TB_disj)
    have h1sub : seg₁ '' Icc 0 1 ⊆ rg.Δ := hsegs.elim (fun h => h.1 ▸ rg.bot_subΔ) (fun h => h.1 ▸ rg.top_subΔ)
    have h2sub : seg₂ '' Icc 0 1 ⊆ rg.Δ := hsegs.elim (fun h => h.2 ▸ rg.top_subΔ) (fun h => h.2 ▸ rg.bot_subΔ)
    have him12 : seg₁ '' Icc 0 1 ∪ seg₂ '' Icc 0 1 = rg.T ∪ rg.B :=
      hsegs.elim (fun h => by rw [h.1, h.2, rg.bot_im, rg.top_im, union_comm]) (fun h => by rw [h.1, h.2, rg.top_im, rg.bot_im])
    obtain ⟨h1_c, h1_i, h1_01, h1_im, h1_coc⟩ := splice_O_11 hE₂c h1c hE₂i h1i hs10.symm hs11 h1sub hE₂Δ
    let rseg₂ := fun r => seg₂ (1 - r)
    obtain ⟨h2_c, h2_i, h2_01, h2_im, h2_coc⟩ :=
      splice_O_11 hE₁c (continuousOn_rev h2c) hE₁i (injOn_rev h2i) (by simp [hs21])
        (by simp [hs20]) (by rw [rev_image]; exact h2sub) hE₁Δ
    let α₁_new := conc2 E₂ seg₁; let α₂_new := conc2 E₁ rseg₂
    have h1_int : α₁_new '' Icc 0 1 ⊆ (bd S)ᶜ := by
      rw [h1_im]; rintro x (h | h) hbd
      · exact a.hOint (hE₂_sub h) hbd
      · exact rg.hΔint (h1sub h) hbd
    have h2_int : α₂_new '' Icc 0 1 ⊆ (bd S)ᶜ := by
      rw [h2_im, rev_image]; rintro x (h | h) hbd
      · exact a.hOint (hE₁_sub h) hbd
      · exact rg.hΔint (h2sub h) hbd
    let a1 : OArcData S := OArcData.ofLoop α₁_new h1_c h1_i h1_01 h1_int
    let a2 : OArcData S := OArcData.ofLoop α₂_new h2_c h2_i h2_01 h2_int
    have ha12 : Disjoint a1.O a2.O := by
      change Disjoint (α₁_new '' Icc 0 1) (α₂_new '' Icc 0 1)
      rw [h1_im, h2_im, rev_image, Set.disjoint_left]
      rintro x (⟨t₁, ht₁, rfl⟩ | hs₁) (⟨t₂, ht₂, he⟩ | hs₂)
      · exact Set.disjoint_left.mp hE12 ⟨t₂, ht₂, he⟩ ⟨t₁, ht₁, rfl⟩
      · rcases hE₂Δ t₁ ht₁ (h2sub hs₂) with rfl | rfl
        · exact Set.disjoint_left.mp h12 ⟨1, ⟨zero_le_one, le_rfl⟩, hs11⟩ hs₂
        · exact Set.disjoint_left.mp h12 ⟨0, ⟨le_rfl, zero_le_one⟩, hs10⟩ hs₂
      · rcases hE₁Δ t₂ ht₂ (he ▸ h1sub hs₁) with rfl | rfl
        · exact Set.disjoint_left.mp h12 hs₁ ⟨0, ⟨le_rfl, zero_le_one⟩, hs20.trans he⟩
        · exact Set.disjoint_left.mp h12 hs₁ ⟨1, ⟨zero_le_one, le_rfl⟩, hs21.trans he⟩
      · exact Set.disjoint_left.mp h12 hs₁ hs₂
    have ha12_u : a1.O ∪ a2.O = E₁ '' Icc 0 1 ∪ E₂ '' Icc 0 1 ∪ rg.T ∪ rg.B := by
      change α₁_new '' Icc 0 1 ∪ α₂_new '' Icc 0 1 = _
      rw [h1_im, h2_im, rev_image]
      calc (E₂ '' Icc 0 1 ∪ seg₁ '' Icc 0 1) ∪ (E₁ '' Icc 0 1 ∪ seg₂ '' Icc 0 1)
        _ = (E₁ '' Icc 0 1 ∪ E₂ '' Icc 0 1) ∪ (seg₁ '' Icc 0 1 ∪ seg₂ '' Icc 0 1) := by
          ext x; simp only [mem_union]; exact ⟨by rintro ((h | h) | (h | h)) <;> simp [*], by rintro ((h | h) | (h | h)) <;> simp [*]⟩
        _ = E₁ '' Icc 0 1 ∪ E₂ '' Icc 0 1 ∪ rg.T ∪ rg.B := by rw [him12, ← union_assoc]
    have hP_disj : Disjoint M.P₀ (a1.O ∪ a2.O) := by
      rw [Set.disjoint_left]; intro x hxP hxn
      by_cases hxΔ : x ∈ rg.Δ; · exact Set.disjoint_left.mp hP_disj_Δ hxP hxΔ
      · exact Set.disjoint_left.mp (M.hP₀_disj a ha_mem) hxP (show x ∈ a.O \ rg.Δ from hext.1 ▸ ⟨ha12_u ▸ hxn, hxΔ⟩).1
    have hrest_disj : ∀ c ∈ rest, Disjoint (a1.O ∪ a2.O) c.O := fun c hc => by
      rw [Set.disjoint_left]; intro x hxn hxc
      by_cases hxΔ : x ∈ rg.Δ; · exact Set.disjoint_left.mp (hrest_disj_Δ c hc) hxc hxΔ
      · exact Set.disjoint_left.mp (hrest_disj_a c hc) hxc (show x ∈ a.O \ rg.Δ from hext.1 ▸ ⟨ha12_u ▸ hxn, hxΔ⟩).1
    let M' : ProperManifold S s t :=
      { P₀ := M.P₀, γ₀ := M.γ₀, hP₀b := M.hP₀b, hP₀l := M.hP₀l,
        hγ₀c := M.hγ₀c, hγ₀i := M.hγ₀i, hγ₀0 := M.hγ₀0, hγ₀1 := M.hγ₀1, hγ₀im := M.hγ₀im,
        Os := a1 :: a2 :: rest,
        hOs_disj := List.pairwise_cons.mpr ⟨fun c hc => by
            rcases List.mem_cons.mp hc with rfl | hc'
            · exact ha12
            · exact (hrest_disj c hc').mono_left subset_union_left,
          List.pairwise_cons.mpr ⟨fun c hc => (hrest_disj c hc).mono_left subset_union_right, hrest_pw⟩⟩,
        hP₀_disj := fun c hc => by
          rcases List.mem_cons.mp hc with rfl | hc1
          · exact hP_disj.mono_right subset_union_left
          · rcases List.mem_cons.mp hc1 with rfl | hc2
            · exact hP_disj.mono_right subset_union_right
            · exact M.hP₀_disj c (hrest_sub c hc2) }
    have hM'U : M'.U = (M.P₀ ∪ ProperManifold.listUnion rest) ∪ (a1.O ∪ a2.O) := by
      simp only [ProperManifold.U, M', ProperManifold.listUnion_cons]
      ext x; simp only [mem_union]; exact ⟨by rintro (h | (h | (h | h))) <;> simp [*], by rintro ((h | h) | (h | h)) <;> simp [*]⟩
    refine ⟨M', ?_, ?_, ?_⟩
    · simp only [hM'U, hMU_eq, union_sdiff_distrib, ha12_u, hext.1]
    · rw [hM'U, union_inter_distrib_right, hPrestΔ0, empty_union, ha12_u, hext.2]
    · simp only [ProperManifold.w1Total, M', hOs_eq, List.map_append, List.map_cons, List.sum_append, List.sum_cons, rest, a1, a2, OArcData.ofLoop]
      rw [h1_coc hcoc, h2_coc hcoc, hE₂coc hcoc, cocInt_rev_zmod2 hcoc h2c, ← hα'coc, hsplit5]
      have hss : cocInt (w1 AS) seg₁ + cocInt (w1 AS) seg₂ = cocInt (w1 AS) rg.bot + cocInt (w1 AS) rg.top :=
        hsegs.elim (fun h => by rw [h.1, h.2]) (fun h => by rw [h.1, h.2]; ring)
      linear_combination hss - hcancel
  rcases hL_ends with ⟨hL0, hL1⟩ | ⟨hL0, hL1⟩ <;> rcases hR_ends with ⟨hR0, hR1⟩ | ⟨hR0, hR1⟩
  · exact hpar rg.bot rg.top (Or.inl ⟨rfl, rfl⟩)
      (by simp [RectGeom.bot, RectGeom.σL, lin_zero, E₂, hE₂1, hL0]) (by simp [RectGeom.bot, RectGeom.σR, lin_one, E₁, subArc_one, hR0])
      (by simp [RectGeom.top, RectGeom.σL, lin_zero, E₁, subArc_zero, hL1]) (by simp [RectGeom.top, RectGeom.σR, lin_one, E₂, hE₂0, hR1])
  · exact hanti rg.bot rg.top (Or.inl ⟨rfl, rfl⟩)
      (by simp [RectGeom.bot, RectGeom.σL, lin_zero, E₂, hE₂1, hL0]) (by simp [RectGeom.bot, RectGeom.σR, lin_one, E₂, hE₂0, hR1])
      (by simp [RectGeom.top, RectGeom.σL, lin_zero, E₁, subArc_zero, hL1]) (by simp [RectGeom.top, RectGeom.σR, lin_one, E₁, subArc_one, hR0])
  · exact hanti rg.top rg.bot (Or.inr ⟨rfl, rfl⟩)
      (by simp [RectGeom.top, RectGeom.σL, lin_zero, E₂, hE₂1, hL0]) (by simp [RectGeom.top, RectGeom.σR, lin_one, E₂, hE₂0, hR1])
      (by simp [RectGeom.bot, RectGeom.σL, lin_zero, E₁, subArc_zero, hL1]) (by simp [RectGeom.bot, RectGeom.σR, lin_one, E₁, subArc_one, hR0])
  · exact hpar rg.top rg.bot (Or.inr ⟨rfl, rfl⟩)
      (by simp [RectGeom.top, RectGeom.σL, lin_zero, E₂, hE₂1, hL0]) (by simp [RectGeom.top, RectGeom.σR, lin_one, E₁, subArc_one, hR0])
      (by simp [RectGeom.bot, RectGeom.σL, lin_zero, E₁, subArc_zero, hL1]) (by simp [RectGeom.bot, RectGeom.σR, lin_one, E₂, hE₂0, hR1])

/-- **Master Rectangle Band-Surgery Theorem**:
Given a `ProperManifold` `M` and an embedded closed rectangle
`Δ = f '' (Icc x₁ x₂ ×ℂ Icc (-d) d) ⊆ (bd S)ᶜ` whose intersection with `M.U` is precisely the two
vertical sides `L = f '' ({x₁} × [-d, d])` and `R = f '' ({x₂} × [-d, d])`, there exists a new
`ProperManifold` `M'` replacing `L ∪ R` by the two horizontal sides `T ∪ B` (`[x₁, x₂] × {±d}`),
preserving `M.U \ Δ`, `w1Total AS`, and the crossing-cocycle cohomology class `BdCohRel s t`.
Moreover, if the left and right midpoints `f (x₁ : ℂ)` and `f (x₂ : ℂ)` lie in DIFFERENT
components of `M`, then `M'.Os.length + 1 = M.Os.length`. -/
theorem rectangle_surgery [ConnectedSpace S] (hS : IsSurface S) (AS : SurfAtlas S)
    {s t : S} (hst : s ≠ t) (M : ProperManifold S s t)
    {f : ℂ → S} {x₁ x₂ d : ℝ} (hx : x₁ < x₂) (hd : 0 < d)
    (hfc : ContinuousOn f (Icc x₁ x₂ ×ℂ Icc (-d) d))
    (hfi : InjOn f (Icc x₁ x₂ ×ℂ Icc (-d) d))
    (hΔint : f '' (Icc x₁ x₂ ×ℂ Icc (-d) d) ⊆ (bd S)ᶜ)
    (hMΔ : M.U ∩ f '' (Icc x₁ x₂ ×ℂ Icc (-d) d) =
      f '' (({x₁} : Set ℝ) ×ℂ Icc (-d) d) ∪ f '' (({x₂} : Set ℝ) ×ℂ Icc (-d) d)) :
    let Δ := f '' (Icc x₁ x₂ ×ℂ Icc (-d) d)
    let T := f '' (Icc x₁ x₂ ×ℂ ({d} : Set ℝ))
    let B := f '' (Icc x₁ x₂ ×ℂ ({-d} : Set ℝ))
    ∃ M' : ProperManifold S s t,
      M'.U \ Δ = M.U \ Δ ∧
      M'.U ∩ Δ = T ∪ B ∧
      M'.w1Total AS = M.w1Total AS ∧
      (∀ ωM ωM', IsCrossingCocycle M.U ωM → IsCrossingCocycle M'.U ωM' → BdCohRel s t ωM' ωM) ∧
      ((¬ (f (x₁ : ℂ) ∈ M.P₀ ∧ f (x₂ : ℂ) ∈ M.P₀) ∧
        ∀ a ∈ M.Os, ¬ (f (x₁ : ℂ) ∈ a.O ∧ f (x₂ : ℂ) ∈ a.O)) → M'.Os.length + 1 = M.Os.length) := by
  have : T2Space S := hS.2.1
  let rg : RectGeom S := ⟨f, x₁, x₂, d, hx, hd, hfc, hfi, hΔint⟩
  have hMΔ' : M.U ∩ rg.Δ = rg.Lset ∪ rg.Rset := hMΔ
  have hflip_MΔ : M.U ∩ rg.flip.Δ = rg.flip.Lset ∪ rg.flip.Rset := by
    rw [rg.flip_Δ, rg.flip_L, rg.flip_R, union_comm, hMΔ']
  have hcoh_of : ∀ M' : ProperManifold S s t, M'.U \ rg.Δ = M.U \ rg.Δ →
      ∀ ωM ωM', IsCrossingCocycle M.U ωM → IsCrossingCocycle M'.U ωM' → BdCohRel s t ωM' ωM := fun M' hagree ωM ωM' hωM hωM' =>
    bdCohRel_of_agree_outside_disc hS M'.isClosed_U rg.isClosedDisc_Δ rg.hΔint M'.U_inter_bd hagree
      (fun z hz => (M'.exists_crossingCocycle hS hst).2 z hz.1) hωM' hωM
  have hseg_comp : ∀ (K : Set S), IsConnected K → K ⊆ M.U → K ⊆ M.P₀ ∨ ∃ a ∈ M.Os, K ⊆ a.O := by
    intro K hKc hKsub
    have hdisjP : Disjoint M.P₀ (ProperManifold.listUnion M.Os) := by
      rw [Set.disjoint_left]; intro x hxP hxO; obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp hxO
      exact Set.disjoint_left.mp (M.hP₀_disj a ha) hxP hxa
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hKc.isPreconnected M.P₀ (ProperManifold.listUnion M.Os)
        M.hP₀l.isCompact.isClosed (ProperManifold.isClosed_listUnion M.Os) hKsub
        (by rw [eq_empty_iff_forall_notMem]; rintro x ⟨-, h1, h2⟩; exact Set.disjoint_left.mp hdisjP h1 h2) with hKP | hKO
    · exact Or.inl hKP
    · right
      obtain ⟨x₀, hx₀⟩ := hKc.nonempty; obtain ⟨a, ha, hx₀a⟩ := mem_iUnion₂.mp (hKO hx₀)
      obtain ⟨l₁, l₂, hOs_eq⟩ := List.mem_iff_append.mp ha
      have hdisja : Disjoint a.O (ProperManifold.listUnion (l₁ ++ l₂)) := by
        have hpw := M.hOs_disj; rw [hOs_eq, List.pairwise_append, List.pairwise_cons] at hpw
        rw [Set.disjoint_left]; intro x hxa hxl; obtain ⟨b, hb, hxb⟩ := mem_iUnion₂.mp hxl
        rcases List.mem_append.mp hb with hb1 | hb2
        · exact Set.disjoint_left.mp (hpw.2.2 b hb1 a (List.mem_cons_self ..)) hxb hxa
        · exact Set.disjoint_left.mp (hpw.2.1.1 b hb2) hxa hxb
      have hUeq : ProperManifold.listUnion M.Os = a.O ∪ ProperManifold.listUnion (l₁ ++ l₂) := by
        rw [hOs_eq, ProperManifold.listUnion_append, ProperManifold.listUnion_cons, ProperManifold.listUnion_append]
        ext x; simp only [mem_union]; tauto
      rcases isPreconnected_iff_subset_of_disjoint_closed.mp hKc.isPreconnected a.O (ProperManifold.listUnion (l₁ ++ l₂))
          a.hO.isCompact.isClosed (ProperManifold.isClosed_listUnion (l₁ ++ l₂)) (hUeq ▸ hKO)
          (by rw [eq_empty_iff_forall_notMem]; rintro x ⟨-, h1, h2⟩; exact Set.disjoint_left.mp hdisja h1 h2) with hKa | hKl
      · exact ⟨a, ha, hKa⟩
      · exact (Set.disjoint_left.mp hdisja hx₀a (hKl hx₀)).elim
  have hLsubU : rg.Lset ⊆ M.U := fun x hx => (hMΔ'.symm ▸ Or.inl hx : x ∈ M.U ∩ rg.Δ).1
  have hRsubU : rg.Rset ⊆ M.U := fun x hx => (hMΔ'.symm ▸ Or.inr hx : x ∈ M.U ∩ rg.Δ).1
  have hmidL : f (x₁ : ℂ) ∈ rg.Lset := ⟨(x₁ : ℂ), Complex.mem_reProdIm.mpr ⟨rfl, by simp only [mem_Icc, ofReal_im]; exact ⟨by linarith, hd.le⟩⟩, rfl⟩
  have hmidR : f (x₂ : ℂ) ∈ rg.Rset := ⟨(x₂ : ℂ), Complex.mem_reProdIm.mpr ⟨rfl, by simp only [mem_Icc, ofReal_im]; exact ⟨by linarith, hd.le⟩⟩, rfl⟩
  rcases hseg_comp rg.Lset rg.isConnected_L hLsubU with hLP | ⟨a, ha, hLa⟩ <;>
  rcases hseg_comp rg.Rset rg.isConnected_R hRsubU with hRP | ⟨b, hb, hRb⟩
  · -- Case A: both in `M.P₀`!
    have hP_oo : ∀ K : Set S, K ⊆ M.P₀ → K ⊆ rg.Δ → K ⊆ M.γ₀ '' Ioo 0 1 := fun K hKP hKΔ z hz => by
      obtain ⟨r, hr, rfl⟩ := M.hγ₀im ▸ hKP hz; have hnb : M.γ₀ r ∉ bd S := rg.hΔint (hKΔ hz)
      exact ⟨r, ⟨lt_of_le_of_ne hr.1 fun h => hnb (by rw [← h, M.hγ₀0]; exact (M.hP₀b.symm ▸ Or.inl rfl : s ∈ M.P₀ ∩ bd S).2),
        lt_of_le_of_ne hr.2 fun h => hnb (by rw [h, M.hγ₀1]; exact (M.hP₀b.symm ▸ Or.inr rfl : t ∈ M.P₀ ∩ bd S).2)⟩, rfl⟩
    obtain ⟨u₁, v₁, hu₁0, huv₁, hv₁1, hLeq, hLends⟩ := subarc_param_interval M.hγ₀c M.hγ₀i rg.hd rg.σL_c rg.σL_i (rg.σL_im ▸ hP_oo rg.Lset hLP rg.L_subΔ)
    obtain ⟨u₂, v₂, hu₂0, huv₂, hv₂1, hReq, hRends⟩ := subarc_param_interval M.hγ₀c M.hγ₀i rg.hd rg.σR_c rg.σR_i (rg.σR_im ▸ hP_oo rg.Rset hRP rg.R_subΔ)
    rw [rg.σL_im] at hLeq; rw [rg.σR_im] at hReq
    have hIcc_disj : Disjoint (Icc u₁ v₁) (Icc u₂ v₂) := by
      rw [Set.disjoint_left]; intro r h1 h2; exact Set.disjoint_left.mp rg.LR_disj (hLeq.subset ⟨r, h1, rfl⟩) (hReq.subset ⟨r, h2, rfl⟩)
    have hord : v₁ < u₂ ∨ v₂ < u₁ := by
      by_cases h : v₁ < u₂; · exact Or.inl h
      right; push Not at h; by_contra h2; push Not at h2
      exact Set.disjoint_left.mp hIcc_disj (show max u₁ u₂ ∈ Icc u₁ v₁ from ⟨le_max_left _ _, max_le huv₁.le h⟩) ⟨le_max_right _ _, max_le h2 huv₂.le⟩
    rcases hord with hv₁u₂ | hv₂u₁
    · obtain ⟨M', h1, h2, h3⟩ := rect_surgery_caseA hS AS M rg hMΔ' hu₁0 huv₁ hv₁u₂ huv₂ hv₂1 hLeq hReq hLends hRends
      exact ⟨M', h1, h2, h3, hcoh_of M' h1, fun hdiff => (hdiff.1 ⟨hLP hmidL, hRP hmidR⟩).elim⟩
    · have hLends' : (M.γ₀ u₂ = rg.flip.σL (-rg.flip.d) ∧ M.γ₀ v₂ = rg.flip.σL rg.flip.d) ∨
          (M.γ₀ u₂ = rg.flip.σL rg.flip.d ∧ M.γ₀ v₂ = rg.flip.σL (-rg.flip.d)) := by
        simpa [RectGeom.flip, RectGeom.σL, RectGeom.σR] using hRends
      have hRends' : (M.γ₀ u₁ = rg.flip.σR (-rg.flip.d) ∧ M.γ₀ v₁ = rg.flip.σR rg.flip.d) ∨
          (M.γ₀ u₁ = rg.flip.σR rg.flip.d ∧ M.γ₀ v₁ = rg.flip.σR (-rg.flip.d)) := by
        simpa [RectGeom.flip, RectGeom.σL, RectGeom.σR] using hLends
      obtain ⟨M', h1, h2, h3⟩ := rect_surgery_caseA hS AS M rg.flip hflip_MΔ hu₂0 huv₂ hv₂u₁ huv₁ hv₁1
        (rg.flip_L.symm ▸ hReq) (rg.flip_R.symm ▸ hLeq) hLends' hRends'
      rw [rg.flip_Δ] at h1 h2; rw [rg.flip_T, rg.flip_B] at h2
      exact ⟨M', h1, h2, h3, hcoh_of M' h1, fun hdiff => (hdiff.1 ⟨hLP hmidL, hRP hmidR⟩).elim⟩
  · -- Case B (`L ⊆ M.P₀`, `R ⊆ b.O`):
    obtain ⟨l₁, l₂, hOs_eq⟩ := List.mem_iff_append.mp hb
    obtain ⟨M', h1, h2, h3, hlen⟩ := rect_surgery_caseB hS AS M rg hMΔ' l₁ l₂ b hOs_eq hLP hRb
    exact ⟨M', h1, h2, h3, hcoh_of M' h1, fun _ => hlen⟩
  · -- Case B flipped (`L ⊆ a.O`, `R ⊆ M.P₀`):
    obtain ⟨l₁, l₂, hOs_eq⟩ := List.mem_iff_append.mp ha
    obtain ⟨M', h1, h2, h3, hlen⟩ := rect_surgery_caseB hS AS M rg.flip hflip_MΔ l₁ l₂ a hOs_eq (rg.flip_L.symm ▸ hRP) (rg.flip_R.symm ▸ hLa)
    rw [rg.flip_Δ] at h1 h2; rw [rg.flip_T, rg.flip_B] at h2
    exact ⟨M', h1, h2, h3, hcoh_of M' h1, fun _ => hlen⟩
  · -- Cases C & D (`L ⊆ a.O`, `R ⊆ b.O`):
    by_cases hab : a.O = b.O
    · -- Case D: same `O`-arc!
      have hRb' : rg.Rset ⊆ a.O := hab ▸ hRb
      obtain ⟨l₁, l₂, hOs_eq⟩ := List.mem_iff_append.mp ha
      have hbase_ex : ∃ c ∈ Ioo (0 : ℝ) 1, a.α c ∉ rg.Lset ∪ rg.Rset := by
        by_contra hnot; push Not at hnot
        have hLc : IsClosed rg.Lset := rg.σL_im ▸ (isCompact_Icc.image_of_continuousOn rg.σL_c).isClosed
        have hRc : IsClosed rg.Rset := rg.σR_im ▸ (isCompact_Icc.image_of_continuousOn rg.σR_c).isClosed
        have hOsub : a.O ⊆ rg.Lset ∪ rg.Rset := by
          rw [← a.hαim]; rintro _ ⟨r, hr, rfl⟩
          have h0m : a.α 0 ∈ rg.Lset ∪ rg.Rset := by
            have hlim : Filter.Tendsto (fun n : ℕ => a.α (1 / ((n : ℝ) + 2))) Filter.atTop (𝓝 (a.α 0)) := by
              refine (a.hαc.continuousWithinAt ⟨le_rfl, zero_le_one⟩).tendsto.comp ?_
              refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ (Filter.Eventually.of_forall fun n => ⟨by positivity, by
                rw [div_le_one (by positivity)]; linarith⟩)
              have ht1 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (Filter.tendsto_add_atTop_nat 1)
              exact ht1.congr fun n => by simp; ring
            exact (hLc.union hRc).mem_of_tendsto hlim (Filter.Eventually.of_forall fun n =>
              hnot _ ⟨by positivity, by rw [div_lt_one (by positivity)]; linarith⟩)
          rcases hr.1.eq_or_lt with rfl | hr0; · exact h0m
          rcases hr.2.eq_or_lt with rfl | hr1; · exact a.hα01 ▸ h0m
          exact hnot r ⟨hr0, hr1⟩
        have ha_conn : IsPreconnected a.O := by rw [← a.hαim]; exact isPreconnected_Icc.image a.α a.hαc
        rcases isPreconnected_iff_subset_of_disjoint_closed.mp ha_conn rg.Lset rg.Rset hLc hRc hOsub
            (by rw [eq_empty_iff_forall_notMem]; rintro x ⟨-, h1, h2⟩; exact Set.disjoint_left.mp rg.LR_disj h1 h2) with h1 | h2
        · exact Set.disjoint_left.mp rg.LR_disj (h1 (hRb' hmidR)) hmidR
        · exact Set.disjoint_left.mp rg.LR_disj hmidL (h2 (hLa hmidL))
      obtain ⟨c, hc, hc_notLR⟩ := hbase_ex
      obtain ⟨hα'c, hα'i, hα'01, hα'0, hα'im, hα'coc⟩ := oArc_rebase a.hαc a.hαi a.hα01 hc.1 hc.2
      let α' := conc2 (subArc a.α c 1) (subArc a.α 0 c)
      obtain ⟨u₁, v₁, hu₁0, huv₁, hv₁1, hLeq, hLends⟩ := subarc_param_interval_loop hα'c hα'i hα'01 rg.hd rg.σL_c rg.σL_i
        (rg.σL_im ▸ hLa.trans (hα'im.trans a.hαim).symm.subset) (rg.σL_im ▸ hα'0.symm ▸ fun h => hc_notLR (Or.inl h))
      obtain ⟨u₂, v₂, hu₂0, huv₂, hv₂1, hReq, hRends⟩ := subarc_param_interval_loop hα'c hα'i hα'01 rg.hd rg.σR_c rg.σR_i
        (rg.σR_im ▸ hRb'.trans (hα'im.trans a.hαim).symm.subset) (rg.σR_im ▸ hα'0.symm ▸ fun h => hc_notLR (Or.inr h))
      rw [rg.σL_im] at hLeq; rw [rg.σR_im] at hReq
      have hIcc_disj : Disjoint (Icc u₁ v₁) (Icc u₂ v₂) := by
        rw [Set.disjoint_left]; intro r h1 h2; exact Set.disjoint_left.mp rg.LR_disj (hLeq.subset ⟨r, h1, rfl⟩) (hReq.subset ⟨r, h2, rfl⟩)
      have hord : v₁ < u₂ ∨ v₂ < u₁ := by
        by_cases h : v₁ < u₂; · exact Or.inl h
        right; push Not at h; by_contra h2; push Not at h2
        exact Set.disjoint_left.mp hIcc_disj (show max u₁ u₂ ∈ Icc u₁ v₁ from ⟨le_max_left _ _, max_le huv₁.le h⟩) ⟨le_max_right _ _, max_le h2 huv₂.le⟩
      rcases hord with hv₁u₂ | hv₂u₁
      · obtain ⟨M', h1, h2, h3⟩ := rect_surgery_caseD hS AS M rg hMΔ' l₁ l₂ a hOs_eq
          hα'c hα'i hα'01 (hα'im.trans a.hαim) (hα'coc (isCoc_w1 hS AS)) hu₁0 huv₁ hv₁u₂ huv₂ hv₂1 hLeq hReq hLends hRends
        exact ⟨M', h1, h2, h3, hcoh_of M' h1, fun hdiff => (hdiff.2 a ha ⟨hLa hmidL, hRb' hmidR⟩).elim⟩
      · have hLends' : (α' u₂ = rg.flip.σL (-rg.flip.d) ∧ α' v₂ = rg.flip.σL rg.flip.d) ∨
            (α' u₂ = rg.flip.σL rg.flip.d ∧ α' v₂ = rg.flip.σL (-rg.flip.d)) := by
          simpa [RectGeom.flip, RectGeom.σL, RectGeom.σR] using hRends
        have hRends' : (α' u₁ = rg.flip.σR (-rg.flip.d) ∧ α' v₁ = rg.flip.σR rg.flip.d) ∨
            (α' u₁ = rg.flip.σR rg.flip.d ∧ α' v₁ = rg.flip.σR (-rg.flip.d)) := by
          simpa [RectGeom.flip, RectGeom.σL, RectGeom.σR] using hLends
        obtain ⟨M', h1, h2, h3⟩ := rect_surgery_caseD hS AS M rg.flip hflip_MΔ l₁ l₂ a hOs_eq
          hα'c hα'i hα'01 (hα'im.trans a.hαim) (hα'coc (isCoc_w1 hS AS)) hu₂0 huv₂ hv₂u₁ huv₁ hv₁1
          (rg.flip_L.symm ▸ hReq) (rg.flip_R.symm ▸ hLeq) hLends' hRends'
        rw [rg.flip_Δ] at h1 h2; rw [rg.flip_T, rg.flip_B] at h2
        exact ⟨M', h1, h2, h3, hcoh_of M' h1, fun hdiff => (hdiff.2 a ha ⟨hLa hmidL, hRb' hmidR⟩).elim⟩
    · -- Case C: two DISTINCT `O`-arcs!
      obtain ⟨l₁, l₂, hOs_eq⟩ := List.mem_iff_append.mp ha
      have hb_in : b ∈ l₁ ∨ b ∈ l₂ := by
        have hb' := hb; rw [hOs_eq] at hb'
        rcases List.mem_append.mp hb' with h1 | h2
        · exact Or.inl h1
        · rcases List.mem_cons.mp h2 with rfl | h2'
          · exact (hab rfl).elim
          · exact Or.inr h2'
      rcases hb_in with hb1 | hb2
      · obtain ⟨p₁, p₂, hl1_eq⟩ := List.mem_iff_append.mp hb1
        have hOs_eq' : M.Os = p₁ ++ b :: (p₂ ++ a :: l₂) := by rw [hOs_eq, hl1_eq]; simp [List.append_assoc]
        obtain ⟨M', h1, h2, h3, hlen⟩ := rect_surgery_caseC hS AS M rg.flip hflip_MΔ p₁ p₂ l₂ b a hOs_eq'
          (rg.flip_L.symm ▸ hRb) (rg.flip_R.symm ▸ hLa)
        rw [rg.flip_Δ] at h1 h2; rw [rg.flip_T, rg.flip_B] at h2
        exact ⟨M', h1, h2, h3, hcoh_of M' h1, fun _ => hlen⟩
      · obtain ⟨m₁, m₂, hl2_eq⟩ := List.mem_iff_append.mp hb2
        have hOs_eq' : M.Os = l₁ ++ a :: (m₁ ++ b :: m₂) := by rw [hOs_eq, hl2_eq]
        obtain ⟨M', h1, h2, h3, hlen⟩ := rect_surgery_caseC hS AS M rg hMΔ' l₁ m₁ m₂ a b hOs_eq' hLa hRb
        exact ⟨M', h1, h2, h3, hcoh_of M' h1, fun _ => hlen⟩

end RectangleSurgery

/-! ### Section 4: Transversality predicate and parity reduction (`parity_surgery`) -/

section ParityReduction

/-- A `ProperManifold` `M` is *transverse* to a `StripBox S Q` with crossing coordinates
`X : Fin m → Finset ℝ` if `M.U` avoids all strip tips and meets each box `sb.box i` in
exact vertical segments `{x} × [-sb.δ, sb.δ]` for `x ∈ X i ⊆ (sb.a i, sb.b i)`. -/
def ProperManifold.IsTransverse {s t : S} (M : ProperManifold S s t)
    {m : ℕ} {Q : Fin m → Set S} (sb : StripBox S Q) (X : Fin m → Finset ℝ) : Prop :=
  (∀ i, Disjoint M.U (sb.tip i)) ∧
  (∀ i, ∀ x ∈ X i, x ∈ Ioo (sb.a i) (sb.b i)) ∧
  (∀ i, M.U ∩ sb.box i = ⋃ x ∈ X i, sb.f i '' (({x} : Set ℝ) ×ℂ Icc (-sb.δ) sb.δ))

/-- For a transverse `ProperManifold`, `M.U ∩ Q i` is in bijection with `X i`. -/
theorem ProperManifold.IsTransverse.inter_Q_eq {s t : S} {M : ProperManifold S s t}
    {m : ℕ} {Q : Fin m → Set S} {sb : StripBox S Q} {X : Fin m → Finset ℝ}
    (htr : M.IsTransverse sb X) (i : Fin m) :
    M.U ∩ Q i = (fun x : ℝ => sb.f i (x : ℂ)) '' (X i : Set ℝ) := by
  ext y; constructor
  · rintro ⟨hyM, hyQ⟩
    have hymid : y ∈ sb.mid i := by
      by_contra hnot; exact Set.disjoint_left.mp (htr.1 i) hyM ⟨hyQ, hnot⟩
    obtain ⟨w, hw, rfl⟩ := hymid
    rw [Complex.mem_reProdIm] at hw
    have hwR : w ∈ sb.rect i := Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self hw.1, by rw [mem_singleton_iff.mp hw.2]; exact ⟨by linarith [sb.hδ], sb.hδ.le⟩⟩
    have hwbox : sb.f i w ∈ M.U ∩ sb.box i := ⟨hyM, w, hwR, rfl⟩
    rw [htr.2.2 i] at hwbox
    obtain ⟨x, hxX, w', hw', hfe⟩ := mem_iUnion₂.mp hwbox
    rw [Complex.mem_reProdIm] at hw'
    have hw'R : w' ∈ sb.rect i := Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hw'.1]; exact Ioo_subset_Icc_self (htr.2.1 i x hxX), hw'.2⟩
    have hww' := sb.hfi i hw'R hwR hfe
    refine ⟨x, hxX, congrArg (sb.f i) (Complex.ext ?_ ?_)⟩
    · rw [ofReal_re, ← mem_singleton_iff.mp hw'.1, hww']
    · rw [ofReal_im, mem_singleton_iff.mp hw.2]
  · rintro ⟨x, hxX, rfl⟩
    have hxin := htr.2.1 i x hxX
    have hxR : (x : ℂ) ∈ sb.rect i := Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self hxin, by simp [sb.hδ.le]⟩
    have hxM : sb.f i (x : ℂ) ∈ M.U ∩ sb.box i := by
      rw [htr.2.2 i]; exact mem_iUnion₂.mpr ⟨x, hxX, (x : ℂ), Complex.mem_reProdIm.mpr ⟨rfl, by simp [sb.hδ.le]⟩, rfl⟩
    exact ⟨hxM.1, (sb.hQ_eq i (x : ℂ) hxR).mpr (by simp)⟩

/-- Any `Finset ℝ` of cardinality ≥ 2 has two consecutive elements `x₁ < x₂`. -/
private theorem exists_consecutive_pair {s : Finset ℝ} (hcard : 2 ≤ s.card) :
    ∃ x₁ ∈ s, ∃ x₂ ∈ s, x₁ < x₂ ∧ ∀ x ∈ s, x ∉ Ioo x₁ x₂ := by
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  let x₁ := s.min' hne
  have hx₁ : x₁ ∈ s := Finset.min'_mem s hne
  have hne2 : (s.erase x₁).Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hx₁]; omega)
  let x₂ := (s.erase x₁).min' hne2
  have hx₂e : x₂ ∈ s.erase x₁ := Finset.min'_mem _ hne2
  have hx₂ : x₂ ∈ s := Finset.mem_of_mem_erase hx₂e
  have hne12 : x₂ ≠ x₁ := Finset.ne_of_mem_erase hx₂e
  have hlt : x₁ < x₂ := lt_of_le_of_ne (Finset.min'_le s x₂ hx₂) hne12.symm
  refine ⟨x₁, hx₁, x₂, hx₂, hlt, fun x hx hxoo => ?_⟩
  have hle : x₂ ≤ x := Finset.min'_le _ x (Finset.mem_erase.mpr ⟨hxoo.1.ne', hx⟩)
  linarith [hxoo.2]

/-- Single parity-surgery step: eliminates two consecutive crossings on `sb.box i`,
shrinking `sb.δ` by a factor of `4` and decreasing `∑ j, (X j).card` by `2`. -/
private theorem parity_surgery_step [ConnectedSpace S] (hS : IsSurface S) (AS : SurfAtlas S)
    {s t : S} (hst : s ≠ t) {m : ℕ} {Q : Fin m → Set S}
    (sb : StripBox S Q) (M : ProperManifold S s t) (X : Fin m → Finset ℝ)
    (htr : M.IsTransverse sb X) (i : Fin m) (hcard : 2 ≤ (X i).card) :
    ∃ (sb' : StripBox S Q) (M' : ProperManifold S s t) (X' : Fin m → Finset ℝ),
      sb'.f = sb.f ∧ sb'.a = sb.a ∧ sb'.b = sb.b ∧ sb'.δ ≤ sb.δ ∧
      M'.IsTransverse sb' X' ∧
      M'.w1Total AS = M.w1Total AS ∧
      (∀ ωM ωM', IsCrossingCocycle M.U ωM → IsCrossingCocycle M'.U ωM' → BdCohRel s t ωM' ωM) ∧
      (∑ j : Fin m, (X' j).card) + 2 = ∑ j : Fin m, (X j).card := by
  classical
  have : T2Space S := hS.2.1
  obtain ⟨x₁, hx₁, x₂, hx₂, hxlt, hconsec⟩ := exists_consecutive_pair hcard
  have hx₁in := htr.2.1 i x₁ hx₁
  have hx₂in := htr.2.1 i x₂ hx₂
  let d : ℝ := sb.δ / 2
  have hd_eq : d = sb.δ / 2 := rfl
  have hd : 0 < d := half_pos sb.hδ
  let R := Icc x₁ x₂ ×ℂ Icc (-d) d
  have hRsub : R ⊆ sb.rect i := fun w hw => by
    simp only [R, StripBox.rect, Complex.mem_reProdIm] at hw ⊢
    exact ⟨⟨by linarith [hw.1.1, hx₁in.1], by linarith [hw.1.2, hx₂in.2]⟩,
      ⟨by linarith [hw.2.1, hd_eq, sb.hδ], by linarith [hw.2.2, hd_eq, sb.hδ]⟩⟩
  let Δ := sb.f i '' R
  have hΔint : Δ ⊆ (bd S)ᶜ := (image_mono hRsub).trans (sb.hint i)
  have hMΔ : M.U ∩ Δ = sb.f i '' (({x₁} : Set ℝ) ×ℂ Icc (-d) d) ∪ sb.f i '' (({x₂} : Set ℝ) ×ℂ Icc (-d) d) := by
    ext y; constructor
    · rintro ⟨hyM, w, hwR, rfl⟩
      have hybox : sb.f i w ∈ M.U ∩ sb.box i := ⟨hyM, w, hRsub hwR, rfl⟩
      rw [htr.2.2 i] at hybox
      obtain ⟨x, hxX, w', hw', hfe⟩ := mem_iUnion₂.mp hybox
      rw [Complex.mem_reProdIm] at hw' hwR
      have hw'R : w' ∈ sb.rect i := Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hw'.1]; exact Ioo_subset_Icc_self (htr.2.1 i x hxX), hw'.2⟩
      have hww' := sb.hfi i hw'R (hRsub (Complex.mem_reProdIm.mpr hwR)) hfe
      have hwx : w.re = x := by rw [← hww', mem_singleton_iff.mp hw'.1]
      rcases hwR.1.1.eq_or_lt with h1 | h1
      · exact Or.inl ⟨w, Complex.mem_reProdIm.mpr ⟨h1.symm, hwR.2⟩, rfl⟩
      · rcases hwR.1.2.eq_or_lt with h2 | h2
        · exact Or.inr ⟨w, Complex.mem_reProdIm.mpr ⟨h2, hwR.2⟩, rfl⟩
        · exact (hconsec x hxX ⟨hwx ▸ h1, hwx ▸ h2⟩).elim
    · rintro (⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩)
      · rw [Complex.mem_reProdIm] at hw
        have hwR : w ∈ R := Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hw.1]; exact ⟨le_rfl, hxlt.le⟩, hw.2⟩
        have hwM : sb.f i w ∈ M.U ∩ sb.box i := by
          rw [htr.2.2 i]
          exact mem_iUnion₂.mpr ⟨x₁, hx₁, w, Complex.mem_reProdIm.mpr ⟨hw.1, ⟨by linarith [hw.2.1, hd_eq, sb.hδ], by linarith [hw.2.2, hd_eq, sb.hδ]⟩⟩, rfl⟩
        exact ⟨hwM.1, w, hwR, rfl⟩
      · rw [Complex.mem_reProdIm] at hw
        have hwR : w ∈ R := Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hw.1]; exact ⟨hxlt.le, le_rfl⟩, hw.2⟩
        have hwM : sb.f i w ∈ M.U ∩ sb.box i := by
          rw [htr.2.2 i]
          exact mem_iUnion₂.mpr ⟨x₂, hx₂, w, Complex.mem_reProdIm.mpr ⟨hw.1, ⟨by linarith [hw.2.1, hd_eq, sb.hδ], by linarith [hw.2.2, hd_eq, sb.hδ]⟩⟩, rfl⟩
        exact ⟨hwM.1, w, hwR, rfl⟩
  obtain ⟨M', hagree, hM'Δ, hw1, hcoh, -⟩ :=
    rectangle_surgery hS AS hst M hxlt hd ((sb.hfc i).mono hRsub) ((sb.hfi i).mono hRsub) hΔint hMΔ
  let d' : ℝ := sb.δ / 4
  have hd' : 0 < d' := div_pos sb.hδ (by norm_num)
  have hd'le : d' ≤ sb.δ := by dsimp only [d']; linarith [sb.hδ]
  let sb' := sb.shrink d' hd' hd'le
  let X' : Fin m → Finset ℝ := Function.update X i ((X i).erase x₁ |>.erase x₂)
  refine ⟨sb', M', X', rfl, rfl, rfl, hd'le, ⟨?_, ?_, ?_⟩, hw1, hcoh, ?_⟩
  · intro k
    have htip_eq : sb'.tip k = sb.tip k := rfl
    rw [htip_eq, Set.disjoint_left]; intro y hyM' hytip
    by_cases hyΔ : y ∈ Δ
    · obtain ⟨w, hwR, rfl⟩ := hyΔ
      by_cases hki : k = i
      · subst hki
        have hwim : w.im = 0 := (sb.hQ_eq k w (hRsub hwR)).mp hytip.1
        rw [Complex.mem_reProdIm] at hwR
        exact hytip.2 ⟨w, Complex.mem_reProdIm.mpr ⟨⟨by linarith [hwR.1.1, hx₁in.1], by linarith [hwR.1.2, hx₂in.2]⟩, hwim⟩, rfl⟩
      · exact Set.disjoint_left.mp (sb.hQ_other i k (Ne.symm hki)) ⟨w, hRsub hwR, rfl⟩ hytip.1
    · exact Set.disjoint_left.mp (htr.1 k) (show y ∈ M.U \ Δ from hagree ▸ ⟨hyM', hyΔ⟩).1 hytip
  · intro k x hxX'
    by_cases hki : k = i
    · subst hki; simp only [X', Function.update_self] at hxX'
      exact htr.2.1 k x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hxX'))
    · simp only [X', Function.update_of_ne hki] at hxX'
      exact htr.2.1 k x hxX'
  · intro k
    by_cases hki : k = i
    · subst hki; simp only [X', Function.update_self]
      ext y; constructor
      · rintro ⟨hyM', w, hw, rfl⟩
        have hw' : w ∈ Icc (sb.a k) (sb.b k) ×ℂ Icc (-d') d' := hw
        rw [Complex.mem_reProdIm] at hw'
        have hwR_big : w ∈ sb.rect k := Complex.mem_reProdIm.mpr ⟨hw'.1, ⟨by dsimp only [d'] at *; linarith [hw'.2.1, sb.hδ], by dsimp only [d'] at *; linarith [hw'.2.2, sb.hδ]⟩⟩
        have hwnotΔ : sb.f k w ∉ Δ := fun hΔw => by
          have hin : sb.f k w ∈ M'.U ∩ Δ := ⟨hyM', hΔw⟩
          rw [hM'Δ] at hin
          rcases hin with ⟨w₁, hw₁, hfe⟩ | ⟨w₁, hw₁, hfe⟩
          · rw [Complex.mem_reProdIm] at hw₁
            have hw₁R : w₁ ∈ R := Complex.mem_reProdIm.mpr ⟨hw₁.1, by rw [mem_singleton_iff.mp hw₁.2]; exact ⟨by linarith, le_rfl⟩⟩
            have h1 := congrArg Complex.im (sb.hfi k (hRsub hw₁R) hwR_big hfe)
            rw [mem_singleton_iff.mp hw₁.2] at h1; dsimp only [d, d'] at *; linarith [hw'.2.2, sb.hδ]
          · rw [Complex.mem_reProdIm] at hw₁
            have hw₁R : w₁ ∈ R := Complex.mem_reProdIm.mpr ⟨hw₁.1, by rw [mem_singleton_iff.mp hw₁.2]; exact ⟨le_rfl, by linarith⟩⟩
            have h1 := congrArg Complex.im (sb.hfi k (hRsub hw₁R) hwR_big hfe)
            rw [mem_singleton_iff.mp hw₁.2] at h1; dsimp only [d, d'] at *; linarith [hw'.2.1, sb.hδ]
        have hyM : sb.f k w ∈ M.U ∩ sb.box k := ⟨(show sb.f k w ∈ M.U \ Δ from hagree ▸ ⟨hyM', hwnotΔ⟩).1, w, hwR_big, rfl⟩
        rw [htr.2.2 k] at hyM
        obtain ⟨x, hxX, w₁, hw₁, hfe⟩ := mem_iUnion₂.mp hyM
        rw [Complex.mem_reProdIm] at hw₁
        have hw₁R : w₁ ∈ sb.rect k := Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hw₁.1]; exact Ioo_subset_Icc_self (htr.2.1 k x hxX), hw₁.2⟩
        have hww₁ := sb.hfi k hw₁R hwR_big hfe
        have hwx : w.re = x := by rw [← hww₁, mem_singleton_iff.mp hw₁.1]
        have hne1 : x ≠ x₁ := fun h => hwnotΔ ⟨w, Complex.mem_reProdIm.mpr ⟨⟨by linarith [hwx, h], by linarith [hwx, h, hxlt]⟩,
          ⟨by dsimp only [d, d'] at *; linarith [hw'.2.1, sb.hδ], by dsimp only [d, d'] at *; linarith [hw'.2.2, sb.hδ]⟩⟩, rfl⟩
        have hne2 : x ≠ x₂ := fun h => hwnotΔ ⟨w, Complex.mem_reProdIm.mpr ⟨⟨by linarith [hwx, h, hxlt], by linarith [hwx, h]⟩,
          ⟨by dsimp only [d, d'] at *; linarith [hw'.2.1, sb.hδ], by dsimp only [d, d'] at *; linarith [hw'.2.2, sb.hδ]⟩⟩, rfl⟩
        exact mem_iUnion₂.mpr ⟨x, Finset.mem_erase.mpr ⟨hne2, Finset.mem_erase.mpr ⟨hne1, hxX⟩⟩,
          w, Complex.mem_reProdIm.mpr ⟨hwx, hw'.2⟩, rfl⟩
      · intro hy
        obtain ⟨x, hxX', w, hw, rfl⟩ := mem_iUnion₂.mp hy
        have hne2 : x ≠ x₂ := Finset.ne_of_mem_erase hxX'
        have hx1e := Finset.mem_of_mem_erase hxX'
        have hne1 : x ≠ x₁ := Finset.ne_of_mem_erase hx1e
        have hxX : x ∈ X k := Finset.mem_of_mem_erase hx1e
        rw [Complex.mem_reProdIm] at hw
        have hwx : w.re = x := mem_singleton_iff.mp hw.1
        have hxin := htr.2.1 k x hxX
        have hw_box' : w ∈ sb'.rect k := Complex.mem_reProdIm.mpr ⟨by rw [hwx]; exact Ioo_subset_Icc_self hxin, hw.2⟩
        have hw_box : w ∈ sb.rect k := Complex.mem_reProdIm.mpr ⟨by rw [hwx]; exact Ioo_subset_Icc_self hxin,
          ⟨by dsimp only [sb', StripBox.shrink, d'] at *; linarith [hw.2.1, sb.hδ],
           by dsimp only [sb', StripBox.shrink, d'] at *; linarith [hw.2.2, sb.hδ]⟩⟩
        have hwnotΔ : sb.f k w ∉ Δ := fun ⟨w₁, hw₁R, hfe⟩ => by
          have h1 := sb.hfi k (hRsub hw₁R) hw_box hfe
          rw [Complex.mem_reProdIm] at hw₁R
          have hx_in : x ∈ Icc x₁ x₂ := hwx ▸ h1 ▸ hw₁R.1
          exact hconsec x hxX ⟨lt_of_le_of_ne hx_in.1 hne1.symm, lt_of_le_of_ne hx_in.2 hne2⟩
        have hyM : sb.f k w ∈ M.U ∩ sb.box k := by
          rw [htr.2.2 k]
          exact mem_iUnion₂.mpr ⟨x, hxX, w, Complex.mem_reProdIm.mpr ⟨hw.1,
            ⟨by dsimp only [sb', StripBox.shrink, d'] at *; linarith [hw.2.1, sb.hδ],
             by dsimp only [sb', StripBox.shrink, d'] at *; linarith [hw.2.2, sb.hδ]⟩⟩, rfl⟩
        exact ⟨(show sb.f k w ∈ M'.U \ Δ from hagree.symm ▸ ⟨hyM.1, hwnotΔ⟩).1, w, hw_box', rfl⟩
    · simp only [X', Function.update_of_ne hki]
      have hbox_disj : Disjoint (sb'.box k) Δ := by
        refine (sb.hdisj hki).mono ?_ (image_mono hRsub)
        rintro _ ⟨w, hw, rfl⟩; simp only [sb', StripBox.shrink, StripBox.rect, Complex.mem_reProdIm] at hw
        exact ⟨w, Complex.mem_reProdIm.mpr ⟨hw.1, ⟨by dsimp only [d'] at *; linarith [hw.2.1, sb.hδ], by dsimp only [d'] at *; linarith [hw.2.2, sb.hδ]⟩⟩, rfl⟩
      ext y; constructor
      · rintro ⟨hyM', hybox'⟩
        have hyM : y ∈ M.U := (show y ∈ M.U \ Δ from hagree ▸ ⟨hyM', Set.disjoint_left.mp hbox_disj hybox'⟩).1
        obtain ⟨w, hw', rfl⟩ := hybox'
        simp only [sb', StripBox.shrink, StripBox.rect, Complex.mem_reProdIm] at hw'
        have hwR : w ∈ sb.rect k := Complex.mem_reProdIm.mpr ⟨hw'.1, ⟨by dsimp only [d'] at *; linarith [hw'.2.1, sb.hδ], by dsimp only [d'] at *; linarith [hw'.2.2, sb.hδ]⟩⟩
        have hy_old : sb.f k w ∈ M.U ∩ sb.box k := ⟨hyM, w, hwR, rfl⟩
        rw [htr.2.2 k] at hy_old
        obtain ⟨x, hxX, w₁, hw₁, hfe⟩ := mem_iUnion₂.mp hy_old
        rw [Complex.mem_reProdIm] at hw₁
        have hw₁R : w₁ ∈ sb.rect k := Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hw₁.1]; exact Ioo_subset_Icc_self (htr.2.1 k x hxX), hw₁.2⟩
        have hww₁ := sb.hfi k hw₁R hwR hfe
        exact mem_iUnion₂.mpr ⟨x, hxX, w, Complex.mem_reProdIm.mpr ⟨hww₁ ▸ hw₁.1, hw'.2⟩, rfl⟩
      · intro hy
        obtain ⟨x, hxX, w, hw, rfl⟩ := mem_iUnion₂.mp hy
        rw [Complex.mem_reProdIm] at hw
        have hxin := htr.2.1 k x hxX
        have hw_box' : w ∈ sb'.rect k := Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hw.1]; exact Ioo_subset_Icc_self hxin, hw.2⟩
        have hyM : sb.f k w ∈ M.U ∩ sb.box k := by
          rw [htr.2.2 k]
          exact mem_iUnion₂.mpr ⟨x, hxX, w, Complex.mem_reProdIm.mpr ⟨hw.1,
            ⟨by dsimp only [sb', StripBox.shrink, d'] at *; linarith [hw.2.1, sb.hδ],
             by dsimp only [sb', StripBox.shrink, d'] at *; linarith [hw.2.2, sb.hδ]⟩⟩, rfl⟩
        exact ⟨(show sb.f k w ∈ M'.U \ Δ from hagree.symm ▸ ⟨hyM.1, Set.disjoint_left.mp hbox_disj ⟨w, hw_box', rfl⟩⟩).1, w, hw_box', rfl⟩
  · have hne12 : x₂ ≠ x₁ := hxlt.ne'
    have hcard_i : (((X i).erase x₁).erase x₂).card + 2 = (X i).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hne12, hx₂⟩), Finset.card_erase_of_mem hx₁]; omega
    have hsum1 : ∑ j : Fin m, (X' j).card = (X' i).card + ∑ j ∈ Finset.univ.erase i, (X' j).card :=
      (Finset.add_sum_erase Finset.univ (fun j => (X' j).card) (Finset.mem_univ i)).symm
    have hsum2 : ∑ j : Fin m, (X j).card = (X i).card + ∑ j ∈ Finset.univ.erase i, (X j).card :=
      (Finset.add_sum_erase Finset.univ (fun j => (X j).card) (Finset.mem_univ i)).symm
    have hrest_eq : ∑ j ∈ Finset.univ.erase i, (X' j).card = ∑ j ∈ Finset.univ.erase i, (X j).card :=
      Finset.sum_congr rfl fun j hj => by simp only [X', Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [hsum1, hsum2, hrest_eq]; simp only [X', Function.update_self]; omega

/-- **Step 1 (Parity Reduction)**: From any transverse `ProperManifold` `(M, sb, X)`,
repeatedly eliminates consecutive crossing pairs to reach a transverse `ProperManifold`
`(M', sb', X')` with `(X' i).card ≤ 1` for EVERY `i : Fin m`, preserving `w1Total AS`
and the crossing-cocycle cohomology class `BdCohRel s t`. -/
theorem parity_surgery [ConnectedSpace S] (hS : IsSurface S) (AS : SurfAtlas S)
    {s t : S} (hst : s ≠ t) {m : ℕ} {Q : Fin m → Set S}
    (sb : StripBox S Q) (M : ProperManifold S s t) (X : Fin m → Finset ℝ)
    (htr : M.IsTransverse sb X) :
    ∃ (sb' : StripBox S Q) (M' : ProperManifold S s t) (X' : Fin m → Finset ℝ),
      M'.IsTransverse sb' X' ∧
      (∀ i, (X' i).card ≤ 1) ∧
      M'.w1Total AS = M.w1Total AS ∧
      (∀ ωM ωM', IsCrossingCocycle M.U ωM → IsCrossingCocycle M'.U ωM' → BdCohRel s t ωM' ωM) := by
  have hind : ∀ (n : ℕ) (sb : StripBox S Q) (M : ProperManifold S s t) (X : Fin m → Finset ℝ),
      M.IsTransverse sb X → ∑ j : Fin m, (X j).card ≤ n →
      ∃ (sb' : StripBox S Q) (M' : ProperManifold S s t) (X' : Fin m → Finset ℝ),
        M'.IsTransverse sb' X' ∧
        (∀ i, (X' i).card ≤ 1) ∧
        M'.w1Total AS = M.w1Total AS ∧
        (∀ ωM ωM', IsCrossingCocycle M.U ωM → IsCrossingCocycle M'.U ωM' → BdCohRel s t ωM' ωM) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro sb M X htr hle
      by_cases hdone : ∀ i, (X i).card ≤ 1
      · refine ⟨sb, M, X, htr, hdone, rfl, fun ωM ωM' h1 h2 => ?_⟩
        have : T2Space S := hS.2.1
        obtain ⟨z₀, hz₀⟩ : ∃ z₀ : S, z₀ ∈ (bd S)ᶜ := by
          refine ⟨M.γ₀ (1 / 2), fun hbd => ?_⟩
          have hmem : M.γ₀ (1 / 2) ∈ M.P₀ ∩ bd S := ⟨M.hγ₀im ▸ ⟨1 / 2, by norm_num, rfl⟩, hbd⟩
          rw [M.hP₀b] at hmem
          rcases hmem with hs | ht
          · have := M.hγ₀i (by norm_num) ⟨le_rfl, zero_le_one⟩ (hs.trans M.hγ₀0.symm); norm_num at this
          · have := M.hγ₀i (by norm_num) ⟨zero_le_one, le_rfl⟩ ((mem_singleton_iff.mp ht).trans M.hγ₀1.symm); norm_num at this
        have hint0 : IsInteriorPoint z₀ := not_not.mp hz₀
        obtain ⟨U, h, g, c, hUsub, -⟩ := hint0.exists_ballChart (isClosed_bd S).isOpen_compl hz₀ (R := 2) (by norm_num)
        have hsub : closedBall (0 : ℂ) 1 ⊆ ball 0 2 := closedBall_subset_ball (by norm_num)
        have hΔ : IsClosedDisc (g '' closedBall (0 : ℂ) 1) :=
          (c.image_disc (isClosedDisc_closedBall_of_pos (0 : ℂ) one_pos).1 hsub).1
        have hΔint : g '' closedBall (0 : ℂ) 1 ⊆ (bd S)ᶜ := by
          rintro _ ⟨w, hw, rfl⟩; exact hUsub (c.gm (hsub hw))
        exact bdCohRel_of_agree_outside_disc hS M.isClosed_U hΔ hΔint M.U_inter_bd rfl
          (fun z hz => (M.exists_crossingCocycle hS hst).2 z hz.1) h2 h1
      · push Not at hdone
        obtain ⟨i, hi⟩ := hdone
        obtain ⟨sb₁, M₁, X₁, -, -, -, -, htr₁, hw1₁, hcoh₁, hsum₁⟩ :=
          parity_surgery_step hS AS hst sb M X htr i (by omega)
        obtain ⟨sb', M', X', htr', hdone', hw1', hcoh'⟩ :=
          ih (∑ j : Fin m, (X₁ j).card) (by omega) sb₁ M₁ X₁ htr₁ le_rfl
        obtain ⟨⟨ω₁, hω₁⟩, -⟩ := M₁.exists_crossingCocycle hS hst
        exact ⟨sb', M', X', htr', hdone', hw1'.trans hw1₁,
          fun ωM ωM' h1 h2 => bdCohRel_trans (hcoh' ω₁ ωM' hω₁ h2) (hcoh₁ ωM ω₁ h1 hω₁)⟩
  exact hind (∑ j : Fin m, (X j).card) sb M X htr le_rfl

end ParityReduction

end GraphMinor.GHR18
