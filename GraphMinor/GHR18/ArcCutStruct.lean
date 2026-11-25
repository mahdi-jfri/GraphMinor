module

public import GraphMinor.GHR18.ArcAlign
public import GraphMinor.Surface.CutIArc

/-!
# Structural Classification of Cutting Along a Non-Separating Proper `I`-Arc

Given a connected surface `S` and a non-separating proper `I`-arc `F` with endpoints `s ≠ t`
cut by `ψ : Y → S` (`ConnectedSpace Y`):
- `connectedSpace_cut_iff`: `ConnectedSpace Y ↔ IsPreconnected (S \ F)`.
- `untouched_cuff_preimage` and `untouched_cuff_image`: 1-to-1 correspondence between untouched
  cuffs of `S` (avoiding `s, t`) and untouched cuffs of `Y` (avoiding `ξ, η`).
- `exists_two_lifts_order`: cyclic ordering of two disjoint arcs `ξ, η` on the same cuff `C` of `Y`.
- `cut_arc_model_diffCuff`, `cut_arc_model_sameCuff_twoSided`, `cut_arc_model_sameCuff_oneSided`:
  exact `(a, b, c)` relations, gap bijections, lift directions, and `cocInt (w1 AS)` values.
- `same_cut_model_of_cocycle_eq`: two non-separating arcs `F, F'` with the same `BdCohRel`
  crossing cocycle and same `cocInt (w1 AS)` have the same cut type (`C_ξ = C_η ↔ C_ξ' = C_η'`)
  and homeomorphic cut surfaces `Y ≃ₜ SurfaceModel a₀ b₀ c₀` and `Y' ≃ₜ SurfaceModel a₀ b₀ c₀`.
-/

@[expose] public section

open Set Function Topology Filter Metric GraphMinor.Surface

namespace GraphMinor.GHR18

universe u

section BasicCut

variable {Y S : Type u} [TopologicalSpace Y] [TopologicalSpace S]

/-- `ψ` restricts to a homeomorphism `ψ ⁻¹' Fᶜ ≃ₜ Fᶜ`. -/
noncomputable def cutComplHomeo [CompactSpace Y] [T2Space S] {ψ : Y → S} {F : Set S}
    (hψ : IsCutting ψ F) (hF : IsClosed F) : (ψ ⁻¹' Fᶜ : Set Y) ≃ₜ (Fᶜ : Set S) := by
  have hq : IsQuotientMap ψ := hψ.1.isClosedMap.isQuotientMap hψ.1 hψ.2.1
  have hqr : IsQuotientMap (Fᶜ.restrictPreimage ψ) := hq.restrictPreimage_isOpen hF.isOpen_compl
  have hbij : Bijective (Fᶜ.restrictPreimage ψ) := by
    refine ⟨fun a b h => Subtype.ext (hψ.2.2.1 a.2 b.2 (congrArg Subtype.val h)), fun ⟨x, hx⟩ => ?_⟩
    obtain ⟨w, rfl⟩ := hψ.2.1 x; exact ⟨⟨w, hx⟩, rfl⟩
  let eEq := Equiv.ofBijective (Fᶜ.restrictPreimage ψ) hbij
  exact {
    toEquiv := eEq
    continuous_toFun := hqr.continuous
    continuous_invFun := by
      rw [hqr.continuous_iff]
      have : eEq.invFun ∘ Fᶜ.restrictPreimage ψ = id := funext fun x => eEq.symm_apply_apply x
      rw [this]; exact continuous_id }

theorem cutComplHomeo_apply [CompactSpace Y] [T2Space S] {ψ : Y → S} {F : Set S}
    (hψ : IsCutting ψ F) (hF : IsClosed F) (y : (ψ ⁻¹' Fᶜ : Set Y)) :
    (cutComplHomeo hψ hF y).1 = ψ y.1 := rfl

theorem cutComplHomeo_symm_psi [CompactSpace Y] [T2Space S] {ψ : Y → S} {F : Set S}
    (hψ : IsCutting ψ F) (hF : IsClosed F) (x : (Fᶜ : Set S)) :
    ψ ((cutComplHomeo hψ hF).symm x).1 = x.1 := by
  have := congrArg Subtype.val ((cutComplHomeo hψ hF).apply_symm_apply x)
  exact this

/-- For a cutting `ψ : Y → S` along a closed set `F`, `ψ ⁻¹' Fᶜ` is dense in `Y` (since `ψ ⁻¹' F ⊆ bd Y`
and every boundary point has interior points arbitrarily close to it). -/
theorem dense_cut_compl (hY : IsSurface Y) {ψ : Y → S} {F : Set S} (hψ : IsCutting ψ F) :
    Dense (ψ ⁻¹' Fᶜ : Set Y) := by
  intro y
  rw [_root_.mem_closure_iff]
  intro U hUo hyU
  obtain ⟨c, hyU'⟩ := exists_surfChart (hY.2.2 y)
  have hW : IsOpen (c.U ∩ U) := c.hU.inter hUo
  have hpre : IsOpen (c.O ∩ {w : ℂ | 0 < w.re} ∩ c.k ⁻¹' (c.U ∩ U)) := by
    have h1 : IsOpen (c.O ∩ {w : ℂ | 0 < w.re}) :=
      c.hO.inter (isOpen_lt (continuous_const (y := (0 : ℝ))) Complex.continuous_re)
    have hsub : c.O ∩ {w : ℂ | 0 < w.re} ⊆ c.O ∩ halfPlane := fun w hw => ⟨hw.1, show 0 ≤ w.re from le_of_lt hw.2⟩
    exact (c.hk.mono hsub).isOpen_inter_preimage h1 hW
  have hO_nhd : c.k ⁻¹' (c.U ∩ U) ∈ 𝓝[c.O ∩ halfPlane] (c.j y) :=
    (c.hk (c.j y) (c.hm hyU')).preimage_mem_nhdsWithin (hW.mem_nhds ⟨by rw [c.hl hyU']; exact hyU', by rw [c.hl hyU']; exact hyU⟩)
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhdsWithin_iff.mp hO_nhd
  obtain ⟨r', hr', hr'O⟩ := Metric.isOpen_iff.mp c.hO (c.j y) (c.hm hyU').1
  set ε := min (r / 2) (r' / 2)
  have hε : 0 < ε := lt_min (half_pos hr) (half_pos hr')
  set w : ℂ := c.j y + (ε : ℂ)
  have hw_re : 0 < w.re := by
    have hre0 : 0 ≤ (c.j y).re := (c.hm hyU').2
    simp only [w, Complex.add_re, Complex.ofReal_re]; linarith
  have hw_O : w ∈ c.O := hr'O (by
    rw [mem_ball, dist_eq_norm, show w - c.j y = (ε : ℂ) by simp [w], Complex.norm_real, Real.norm_of_nonneg hε.le]
    exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hr'))
  have hw_ball : w ∈ ball (c.j y) r := by
    rw [mem_ball, dist_eq_norm, show w - c.j y = (ε : ℂ) by simp [w], Complex.norm_real, Real.norm_of_nonneg hε.le]
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hr)
  have hw_in : c.k w ∈ c.U ∩ U := hrsub ⟨hw_ball, hw_O, hw_re.le⟩
  refine ⟨c.k w, hw_in.2, ?_⟩
  show ψ (c.k w) ∉ F
  intro hFmem
  have hbd : c.k w ∈ bd Y := hψ.2.2.2.2 hFmem
  have hre0 := (c.mem_bd_iff hw_in.1).mp hbd
  rw [c.hr ⟨hw_O, hw_re.le⟩] at hre0
  linarith

/-- Cutting `S` along `F` yields a connected surface `Y` iff `Fᶜ` is preconnected. -/
theorem connectedSpace_cut_iff (hY : IsSurface Y) (hS : IsSurface S) [Nonempty Y]
    {ψ : Y → S} {F : Set S} (hψ : IsCutting ψ F) (hF : IsClosed F) :
    ConnectedSpace Y ↔ IsPreconnected (Fᶜ : Set S) := by
  have : CompactSpace Y := hY.1
  have : T2Space S := hS.2.1
  let eF := cutComplHomeo hψ hF
  have hpre_iff : IsPreconnected (ψ ⁻¹' Fᶜ : Set Y) ↔ IsPreconnected (Fᶜ : Set S) := by
    constructor
    · intro h
      have h1 : IsPreconnected (univ : Set (ψ ⁻¹' Fᶜ : Set Y)) := by
        rw [← IsEmbedding.subtypeVal.isPreconnected_image, image_univ, Subtype.range_coe]; exact h
      have h2 := (h1.image eF eF.continuous.continuousOn).image Subtype.val continuous_subtype_val.continuousOn
      have him : Subtype.val '' (eF '' (univ : Set (ψ ⁻¹' Fᶜ : Set Y))) = Fᶜ := by
        ext x; constructor
        · rintro ⟨⟨w, hw⟩, -, rfl⟩; exact hw
        · intro hx; exact ⟨⟨x, hx⟩, ⟨eF.symm ⟨x, hx⟩, mem_univ _, eF.apply_symm_apply _⟩, rfl⟩
      rwa [him] at h2
    · intro h
      have h1 : IsPreconnected (univ : Set (Fᶜ : Set S)) := by
        rw [← IsEmbedding.subtypeVal.isPreconnected_image, image_univ, Subtype.range_coe]; exact h
      have h2 := (h1.image eF.symm eF.symm.continuous.continuousOn).image Subtype.val continuous_subtype_val.continuousOn
      have him : Subtype.val '' (eF.symm '' (univ : Set (Fᶜ : Set S))) = ψ ⁻¹' Fᶜ := by
        ext y; constructor
        · rintro ⟨⟨w, hw⟩, -, rfl⟩; exact hw
        · intro hy; exact ⟨⟨y, hy⟩, ⟨eF ⟨y, hy⟩, mem_univ _, eF.symm_apply_apply _⟩, rfl⟩
      rwa [him] at h2
  rw [← hpre_iff]
  constructor
  · intro hYc
    have hint_sub : (bd Y)ᶜ ⊆ ψ ⁻¹' Fᶜ := fun y hy hFmem => hy (hψ.2.2.2.2 hFmem)
    have hcl_int : closure (bd Y)ᶜ = (univ : Set Y) := by
      ext y; simp only [mem_univ, iff_true, _root_.mem_closure_iff]
      intro U hUo hyU
      obtain ⟨c, hyU'⟩ := exists_surfChart (hY.2.2 y)
      have hO_nhd : c.k ⁻¹' (c.U ∩ U) ∈ 𝓝[c.O ∩ halfPlane] (c.j y) :=
        (c.hk (c.j y) (c.hm hyU')).preimage_mem_nhdsWithin ((c.hU.inter hUo).mem_nhds ⟨by rw [c.hl hyU']; exact hyU', by rw [c.hl hyU']; exact hyU⟩)
      obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhdsWithin_iff.mp hO_nhd
      obtain ⟨r', hr', hr'O⟩ := Metric.isOpen_iff.mp c.hO (c.j y) (c.hm hyU').1
      set ε := min (r / 2) (r' / 2)
      have hε : 0 < ε := lt_min (half_pos hr) (half_pos hr')
      set w : ℂ := c.j y + (ε : ℂ)
      have hw_re : 0 < w.re := by
        have hre0 : 0 ≤ (c.j y).re := (c.hm hyU').2
        simp only [w, Complex.add_re, Complex.ofReal_re]; linarith
      have hw_O : w ∈ c.O := hr'O (by
        rw [mem_ball, dist_eq_norm, show w - c.j y = (ε : ℂ) by simp [w], Complex.norm_real, Real.norm_of_nonneg hε.le]
        exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hr'))
      have hw_ball : w ∈ ball (c.j y) r := by
        rw [mem_ball, dist_eq_norm, show w - c.j y = (ε : ℂ) by simp [w], Complex.norm_real, Real.norm_of_nonneg hε.le]
        exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hr)
      have hw_in : c.k w ∈ c.U ∩ U := hrsub ⟨hw_ball, hw_O, hw_re.le⟩
      refine ⟨c.k w, hw_in.2, fun hbd => ?_⟩
      have hre0 := (c.mem_bd_iff hw_in.1).mp hbd
      rw [c.hr ⟨hw_O, hw_re.le⟩] at hre0; linarith
    have hint_pre : IsPreconnected (bd Y)ᶜ := by
      intro U V hUo hVo hsub hU hV
      let U₁ : Set Y := {y | ∃ W, IsOpen W ∧ y ∈ W ∧ W ∩ (bd Y)ᶜ ⊆ U}
      let V₁ : Set Y := {y | ∃ W, IsOpen W ∧ y ∈ W ∧ W ∩ (bd Y)ᶜ ⊆ V}
      have hU₁o : IsOpen U₁ := isOpen_iff_forall_mem_open.mpr fun y ⟨W, hWo, hyW, hWU⟩ =>
        ⟨W, fun z hz => ⟨W, hWo, hz, hWU⟩, hWo, hyW⟩
      have hV₁o : IsOpen V₁ := isOpen_iff_forall_mem_open.mpr fun y ⟨W, hWo, hyW, hWV⟩ =>
        ⟨W, fun z hz => ⟨W, hWo, hz, hWV⟩, hWo, hyW⟩
      by_contra hdisj
      have hcov : (univ : Set Y) ⊆ U₁ ∪ V₁ := fun y _ => by
        obtain ⟨c, hyU'⟩ := exists_surfChart (hY.2.2 y)
        obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp c.hO (c.j y) (c.hm hyU').1
        let W : Set Y := c.U ∩ c.j ⁻¹' ball (c.j y) r
        have hWo : IsOpen W := c.hj.isOpen_inter_preimage c.hU isOpen_ball
        have hyW : y ∈ W := ⟨hyU', mem_ball_self hr⟩
        have hW_int : W ∩ (bd Y)ᶜ = c.k '' (ball (c.j y) r ∩ {w : ℂ | 0 < w.re}) := by
          ext z; constructor
          · rintro ⟨⟨hzU, hzB⟩, hzI⟩
            have hre : 0 < (c.j z).re := lt_of_le_of_ne (c.hm hzU).2 (Ne.symm fun h0 => hzI ((c.mem_bd_iff hzU).mpr h0))
            exact ⟨c.j z, ⟨hzB, hre⟩, c.hl hzU⟩
          · rintro ⟨w, ⟨hwB, hwre⟩, rfl⟩
            have hwO : w ∈ c.O ∩ halfPlane := ⟨hrO hwB, show 0 ≤ w.re from le_of_lt hwre⟩
            refine ⟨⟨c.hk' hwO, by show c.j (c.k w) ∈ ball (c.j y) r; rwa [c.hr hwO]⟩, fun hbd => ?_⟩
            have := (c.mem_bd_iff (c.hk' hwO)).mp hbd; rw [c.hr hwO] at this; linarith [show 0 < w.re from hwre]
        have hconv_half : Convex ℝ {w : ℂ | 0 < w.re} := by
          intro x hx y hy a b ha hb hab
          show 0 < (a • x + b • y).re
          simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
          rcases eq_or_lt_of_le ha with rfl | ha'
          · have hb1 : b = 1 := by linarith
            rw [hb1]; simp; exact hy
          · nlinarith [show 0 < x.re from hx, show 0 < y.re from hy]
        have hconv : Convex ℝ (ball (c.j y) r ∩ {w : ℂ | 0 < w.re}) :=
          (convex_ball (c.j y) r).inter hconv_half
        have hW_pre : IsPreconnected (W ∩ (bd Y)ᶜ) := by
          rw [hW_int]
          exact hconv.isPreconnected.image c.k (c.hk.mono fun w hw => ⟨hrO hw.1, show 0 ≤ w.re from le_of_lt hw.2⟩)
        have hW_sub : W ∩ (bd Y)ᶜ ⊆ U ∪ V := fun z hz => hsub hz.2
        have hW_or : W ∩ (bd Y)ᶜ ⊆ U ∨ W ∩ (bd Y)ᶜ ⊆ V := by
          by_contra hnot
          push Not at hnot
          obtain ⟨z₁, hz₁W, hz₁nU⟩ := Set.not_subset.mp hnot.1
          obtain ⟨z₂, hz₂W, hz₂nV⟩ := Set.not_subset.mp hnot.2
          obtain ⟨z, hzW, hzU, hzV⟩ := hW_pre U V hUo hVo hW_sub
            ⟨z₂, hz₂W, (hW_sub hz₂W).resolve_right hz₂nV⟩
            ⟨z₁, hz₁W, (hW_sub hz₁W).resolve_left hz₁nU⟩
          exact hdisj ⟨z, hzW.2, hzU, hzV⟩
        rcases hW_or with hWU | hWV
        · exact .inl ⟨W, hWo, hyW, hWU⟩
        · exact .inr ⟨W, hWo, hyW, hWV⟩
      have hU₁_ne : U₁.Nonempty := by
        obtain ⟨y, hyI, hyU⟩ := hU
        exact ⟨y, U, hUo, hyU, fun z hz => hz.1⟩
      have hV₁_ne : V₁.Nonempty := by
        obtain ⟨y, hyI, hyV⟩ := hV
        exact ⟨y, V, hVo, hyV, fun z hz => hz.1⟩
      obtain ⟨y, -, ⟨W₁, hW₁o, hyW₁, hW₁U⟩, ⟨W₂, hW₂o, hyW₂, hW₂V⟩⟩ :=
        isPreconnected_univ U₁ V₁ hU₁o hV₁o hcov (by obtain ⟨y, hy⟩ := hU₁_ne; exact ⟨y, mem_univ _, hy⟩)
          (by obtain ⟨y, hy⟩ := hV₁_ne; exact ⟨y, mem_univ _, hy⟩)
      obtain ⟨z, ⟨hzW₁, hzW₂⟩, hzI⟩ := _root_.mem_closure_iff.mp (hcl_int.symm ▸ mem_univ y) (W₁ ∩ W₂) (hW₁o.inter hW₂o) ⟨hyW₁, hyW₂⟩
      exact hdisj ⟨z, hzI, hW₁U ⟨hzW₁, hzI⟩, hW₂V ⟨hzW₂, hzI⟩⟩
    exact hint_pre.subset_closure hint_sub (by rw [hcl_int]; exact subset_univ _)
  · intro hpre
    have hcl : closure (ψ ⁻¹' Fᶜ : Set Y) = univ := (dense_cut_compl hY hψ).closure_eq
    exact { isPreconnected_univ := by rw [← hcl]; exact hpre.closure, toNonempty := inferInstance }

/-- Every boundary point of `Y` not mapping into `F` maps to a boundary point of `S`, and vice versa. -/
theorem mem_bd_cut_iff (hY : IsSurface Y) (hS : IsSurface S) [T2Space Y]
    {ψ : Y → S} {F : Set S} (hψ : IsCutting ψ F) (hF : IsClosed F)
    {y : Y} (hyF : ψ y ∉ F) : y ∈ bd Y ↔ ψ y ∈ bd S := by
  have : CompactSpace Y := hY.1
  have : T2Space S := hS.2.1
  constructor
  · intro hybd
    by_contra hnotbd
    let eF := cutComplHomeo hψ hF
    obtain ⟨cS, hcS⟩ := exists_surfChart (hS.2.2 (ψ y))
    have hre_pos : 0 < (cS.j (ψ y)).re :=
      lt_of_le_of_ne (cS.hm hcS).2 (Ne.symm fun h0 => hnotbd ((cS.mem_bd_iff hcS).mpr h0))
    have hO' : IsOpen (cS.O ∩ {w : ℂ | 0 < w.re} ∩ cS.k ⁻¹' Fᶜ) := by
      have h1 : IsOpen (cS.O ∩ {w : ℂ | 0 < w.re}) :=
        cS.hO.inter (isOpen_lt (continuous_const (y := (0 : ℝ))) Complex.continuous_re)
      have hsub : cS.O ∩ {w : ℂ | 0 < w.re} ⊆ cS.O ∩ halfPlane := fun w hw => ⟨hw.1, show 0 ≤ w.re from le_of_lt hw.2⟩
      exact (cS.hk.mono hsub).isOpen_inter_preimage h1 hF.isOpen_compl
    have hmem0 : cS.j (ψ y) ∈ cS.O ∩ {w : ℂ | 0 < w.re} ∩ cS.k ⁻¹' Fᶜ :=
      ⟨⟨(cS.hm hcS).1, hre_pos⟩, by show cS.k (cS.j (ψ y)) ∉ F; rw [cS.hl hcS]; exact hyF⟩
    obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hO' _ hmem0
    have hB_sub : ball (cS.j (ψ y)) r ⊆ cS.O ∩ halfPlane := fun w hw => ⟨(hrsub hw).1.1, show 0 ≤ w.re from le_of_lt (hrsub hw).1.2⟩
    let US : Set S := cS.k '' ball (cS.j (ψ y)) r
    have hUS_eq : US = cS.U ∩ cS.j ⁻¹' ball (cS.j (ψ y)) r := by
      ext x; constructor
      · rintro ⟨w, hw, rfl⟩; exact ⟨cS.hk' (hB_sub hw), by show cS.j (cS.k w) ∈ ball (cS.j (ψ y)) r; rwa [cS.hr (hB_sub hw)]⟩
      · rintro ⟨hxU, hxB⟩; exact ⟨cS.j x, hxB, cS.hl hxU⟩
    have hUS_open : IsOpen US := hUS_eq ▸ cS.hj.isOpen_inter_preimage cS.hU isOpen_ball
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
        left_inv := fun z => Subtype.ext (by dsimp only; exact congrArg Subtype.val (eF.symm_apply_apply ⟨z.1, hUS_subF z.2⟩))
        right_inv := fun z => Subtype.ext (by dsimp only; exact congrArg Subtype.val (eF.apply_symm_apply ⟨z.1, hUS_subF z.2⟩))
        continuous_toFun := continuous_induced_rng.mpr (hψ.1.comp continuous_subtype_val)
        continuous_invFun := by
          rw [continuous_induced_rng]
          show Continuous (fun z : US => (eF.symm ⟨z.1, hUS_subF z.2⟩).1)
          refine continuous_subtype_val.comp (eF.symm.continuous.comp ?_)
          rw [continuous_induced_rng]; exact continuous_subtype_val }
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
        left_inv := fun w => Subtype.ext (by dsimp only; rw [mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hr.ne'), add_sub_cancel])
        right_inv := fun v => Subtype.ext (by dsimp only; rw [add_sub_cancel_left, mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hr.ne')])
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
        left_inv := fun z => Subtype.ext (by apply Complex.ext <;> simp [EuclideanSpace.equiv])
        right_inv := fun p => Subtype.ext (by ext i; fin_cases i <;> simp [EuclideanSpace.equiv])
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
  · intro hψbd; exact bd_lift hψ hF hψbd hyF

/-- An untouched cuff `D ∈ cuffs S` (not containing `s` or `t`) lifts to an untouched cuff
`ψ ⁻¹' D ∈ cuffs Y` (disjoint from `ψ ⁻¹' F`), and `ψ` maps `ψ ⁻¹' D` bijectively onto `D`. -/
theorem untouched_cuff_preimage (hY : IsSurface Y) (hS : IsSurface S) [T2Space Y]
    {ψ : Y → S} {F : Set S} {s t : S} (hψ : IsCutting ψ F) (hF : IsClosed F)
    (hb : F ∩ bd S = {s, t}) {D : Set S} (hD : D ∈ cuffs S)
    (hDs : s ∉ D) (hDt : t ∉ D) :
    ψ ⁻¹' D ∈ cuffs Y ∧ Disjoint (ψ ⁻¹' D) (ψ ⁻¹' F) ∧ ψ '' (ψ ⁻¹' D) = D := by
  have : CompactSpace Y := hY.1
  have : T2Space S := hS.2.1
  have hDbd : D ⊆ bd S := by obtain ⟨z, -, rfl⟩ := hD; exact connectedComponentIn_subset _ _
  have hDF : Disjoint D F := by
    rw [Set.disjoint_left]; intro x hxD hxF
    have hst : x ∈ ({s, t} : Set S) := hb ▸ ⟨hxF, hDbd hxD⟩
    rcases hst with rfl | rfl
    · exact hDs hxD
    · exact hDt hxD
  have hpre_disj : Disjoint (ψ ⁻¹' D) (ψ ⁻¹' F) := hDF.preimage ψ
  have him : ψ '' (ψ ⁻¹' D) = D := image_preimage_eq D hψ.2.1
  have hpre_bd : ψ ⁻¹' D ⊆ bd Y := fun y hy =>
    bd_lift hψ hF (hDbd hy) (Set.disjoint_left.mp hDF hy)
  -- `ψ ⁻¹' D` is connected (homeomorphic to `D` via `cutComplHomeo`!) and nonempty:
  obtain ⟨z₀, hz₀, rfl⟩ := hD
  have hDne : (connectedComponentIn (bd S) z₀).Nonempty := ⟨z₀, mem_connectedComponentIn hz₀⟩
  obtain ⟨y₀, hy₀⟩ := hψ.2.1 z₀
  have hy₀_mem : y₀ ∈ ψ ⁻¹' connectedComponentIn (bd S) z₀ := by
    show ψ y₀ ∈ connectedComponentIn (bd S) z₀; rw [hy₀]; exact mem_connectedComponentIn hz₀
  let eF := cutComplHomeo hψ hF
  have hpre_conn : IsPreconnected (ψ ⁻¹' connectedComponentIn (bd S) z₀) := by
    let D' : Set (Fᶜ : Set S) := Subtype.val ⁻¹' connectedComponentIn (bd S) z₀
    have hD'_eq : Subtype.val '' D' = connectedComponentIn (bd S) z₀ := by
      ext x; constructor
      · rintro ⟨⟨w, _⟩, hw, rfl⟩; exact hw
      · intro hx; exact ⟨⟨x, Set.disjoint_left.mp hDF hx⟩, hx, rfl⟩
    have hD'_pre : IsPreconnected D' := by
      have := isPreconnected_connectedComponentIn (F := bd S) (x := z₀)
      rw [← hD'_eq] at this
      exact (IsEmbedding.subtypeVal.isPreconnected_image).mp this
    have hpre_eq : ψ ⁻¹' connectedComponentIn (bd S) z₀ = Subtype.val '' (eF.symm '' D') := by
      ext y; constructor
      · intro hy
        have hyFc : ψ y ∉ F := Set.disjoint_left.mp hDF hy
        refine ⟨⟨y, hyFc⟩, ⟨⟨ψ y, hyFc⟩, hy, ?_⟩, rfl⟩
        exact eF.symm_apply_apply ⟨y, hyFc⟩
      · rintro ⟨⟨y', hy'⟩, ⟨⟨x, hx⟩, hxD, heq⟩, rfl⟩
        have h1 : ψ y' = x := by
          have := congrArg (fun w => (eF w).1) heq
          rw [eF.apply_symm_apply, cutComplHomeo_apply] at this
          exact this.symm
        show ψ y' ∈ connectedComponentIn (bd S) z₀; rw [h1]; exact hxD
    rw [hpre_eq]
    exact (hD'_pre.image eF.symm eF.symm.continuous.continuousOn).image Subtype.val continuous_subtype_val.continuousOn
  have hsub : ψ ⁻¹' connectedComponentIn (bd S) z₀ ⊆ connectedComponentIn (bd Y) y₀ :=
    hpre_conn.subset_connectedComponentIn hy₀_mem hpre_bd
  have hsup : connectedComponentIn (bd Y) y₀ ⊆ ψ ⁻¹' connectedComponentIn (bd S) z₀ := by
    have hcfS := cuff_statement.{u} S hS
    have hcfY := cuff_statement.{u} Y hY
    have hD_cuff : connectedComponentIn (bd S) z₀ ∈ cuffs S := ⟨z₀, hz₀, rfl⟩
    have hY_cuff : connectedComponentIn (bd Y) y₀ ∈ cuffs Y := ⟨y₀, hpre_bd hy₀_mem, rfl⟩
    obtain ⟨φD⟩ := hcfS.2.2 _ hD_cuff
    obtain ⟨φY⟩ := hcfY.2.2 _ hY_cuff
    have hHomeo : Circle ≃ₜ (ψ ⁻¹' connectedComponentIn (bd S) z₀ : Set Y) := by
      let eD : (connectedComponentIn (bd S) z₀ : Set S) ≃ₜ (ψ ⁻¹' connectedComponentIn (bd S) z₀ : Set Y) := {
        toFun := fun x => ⟨(eF.symm ⟨x.1, Set.disjoint_left.mp hDF x.2⟩).1, by
          show ψ (eF.symm ⟨x.1, Set.disjoint_left.mp hDF x.2⟩).1 ∈ connectedComponentIn (bd S) z₀
          rw [cutComplHomeo_symm_psi hψ hF]; exact x.2⟩
        invFun := fun y => ⟨ψ y.1, y.2⟩
        left_inv := fun x => Subtype.ext (cutComplHomeo_symm_psi hψ hF ⟨x.1, Set.disjoint_left.mp hDF x.2⟩)
        right_inv := fun y => Subtype.ext (by
          dsimp only
          exact congrArg Subtype.val (eF.symm_apply_apply ⟨y.1, Set.disjoint_left.mp hDF y.2⟩))
        continuous_toFun := by
          rw [continuous_induced_rng]
          change Continuous (fun x : (connectedComponentIn (bd S) z₀ : Set S) =>
            (eF.symm ⟨x.1, Set.disjoint_left.mp hDF x.2⟩).1)
          refine continuous_subtype_val.comp (eF.symm.continuous.comp ?_)
          rw [continuous_induced_rng]; exact continuous_subtype_val
        continuous_invFun := continuous_induced_rng.mpr (hψ.1.comp continuous_subtype_val) }
      exact φD.trans eD
    exact (oarc_eq φY ⟨hHomeo⟩ hsub).symm.subset
  have heq : ψ ⁻¹' connectedComponentIn (bd S) z₀ = connectedComponentIn (bd Y) y₀ := subset_antisymm hsub hsup
  exact ⟨heq ▸ ⟨y₀, hpre_bd hy₀_mem, rfl⟩, hpre_disj, him⟩

/-- Conversely, every cuff `E ∈ cuffs Y` disjoint from `ψ ⁻¹' F` projects to an untouched cuff
`ψ '' E ∈ cuffs S` avoiding `{s, t}`, with `ψ ⁻¹' (ψ '' E) = E`. -/
theorem untouched_cuff_image (hY : IsSurface Y) (hS : IsSurface S) [T2Space Y]
    {ψ : Y → S} {F : Set S} {s t : S} (hψ : IsCutting ψ F) (hF : IsClosed F)
    (hb : F ∩ bd S = {s, t}) {E : Set Y} (hE : E ∈ cuffs Y)
    (hEF : Disjoint E (ψ ⁻¹' F)) :
    ψ '' E ∈ cuffs S ∧ s ∉ ψ '' E ∧ t ∉ ψ '' E ∧ ψ ⁻¹' (ψ '' E) = E := by
  have : CompactSpace Y := hY.1
  have : T2Space S := hS.2.1
  obtain ⟨y₀, hy₀, rfl⟩ := hE
  have hy₀E : y₀ ∈ connectedComponentIn (bd Y) y₀ := mem_connectedComponentIn hy₀
  have hEbd : connectedComponentIn (bd Y) y₀ ⊆ bd Y := connectedComponentIn_subset _ _
  have hψy₀_bd : ψ y₀ ∈ bd S := (mem_bd_cut_iff hY hS hψ hF (Set.disjoint_left.mp hEF hy₀E)).mp hy₀
  let D : Set S := connectedComponentIn (bd S) (ψ y₀)
  have hD : D ∈ cuffs S := ⟨ψ y₀, hψy₀_bd, rfl⟩
  have him_sub : ψ '' connectedComponentIn (bd Y) y₀ ⊆ D := by
    have hpre : IsPreconnected (ψ '' connectedComponentIn (bd Y) y₀) :=
      isPreconnected_connectedComponentIn.image ψ hψ.1.continuousOn
    refine hpre.subset_connectedComponentIn ⟨y₀, hy₀E, rfl⟩ ?_
    rintro _ ⟨y, hy, rfl⟩
    exact (mem_bd_cut_iff hY hS hψ hF (Set.disjoint_left.mp hEF hy)).mp (hEbd hy)
  have hcfS := cuff_statement.{u} S hS
  have hcfY := cuff_statement.{u} Y hY
  obtain ⟨φE⟩ := hcfY.2.2 _ ⟨y₀, hy₀, rfl⟩
  obtain ⟨φD⟩ := hcfS.2.2 _ hD
  have hHomeo : Circle ≃ₜ (ψ '' connectedComponentIn (bd Y) y₀ : Set S) := by
    let g : (connectedComponentIn (bd Y) y₀ : Set Y) → (ψ '' connectedComponentIn (bd Y) y₀ : Set S) :=
      fun y => ⟨ψ y.1, ⟨y.1, y.2, rfl⟩⟩
    have hgc : Continuous g := continuous_induced_rng.mpr (hψ.1.comp continuous_subtype_val)
    have hgb : Bijective g := by
      refine ⟨fun a b h => Subtype.ext (hψ.2.2.1 (Set.disjoint_left.mp hEF a.2) (Set.disjoint_left.mp hEF b.2)
        (congrArg Subtype.val h)), fun ⟨x, y, hy, hx⟩ => ⟨⟨y, hy⟩, Subtype.ext hx⟩⟩
    haveI : CompactSpace (connectedComponentIn (bd Y) y₀ : Set Y) :=
      isCompact_iff_compactSpace.mp (hcfY.2.2 _ ⟨y₀, hy₀, rfl⟩).isCompact
    exact φE.trans (hgc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g hgb))
  have heq : ψ '' connectedComponentIn (bd Y) y₀ = D := oarc_eq φD ⟨hHomeo⟩ him_sub
  have hs_not : s ∉ ψ '' connectedComponentIn (bd Y) y₀ := by
    rintro ⟨y, hy, hyS⟩
    have hsF : s ∈ F := (show s ∈ F ∩ bd S from hb ▸ mem_insert _ _).1
    exact Set.disjoint_left.mp hEF hy (show ψ y ∈ F by rw [hyS]; exact hsF)
  have ht_not : t ∉ ψ '' connectedComponentIn (bd Y) y₀ := by
    rintro ⟨y, hy, hyS⟩
    have htF : t ∈ F := (show t ∈ F ∩ bd S from hb ▸ mem_insert_of_mem _ rfl).1
    exact Set.disjoint_left.mp hEF hy (show ψ y ∈ F by rw [hyS]; exact htF)
  have hpre : ψ ⁻¹' (ψ '' connectedComponentIn (bd Y) y₀) = connectedComponentIn (bd Y) y₀ := by
    ext y; constructor
    · rintro ⟨z, hz, hzy⟩
      have hzF : ψ z ∉ F := Set.disjoint_left.mp hEF hz
      exact (hψ.2.2.1 (show ψ y ∉ F by rw [← hzy]; exact hzF) hzF hzy.symm) ▸ hz
    · intro hy; exact ⟨y, hy, rfl⟩
  exact ⟨heq ▸ hD, hs_not, ht_not, hpre⟩

end BasicCut

/-! ### Cyclic order of lifts on a single cuff and gap classification -/

section LiftOrderAndGaps

variable {Y S : Type u} [TopologicalSpace Y] [TopologicalSpace S]

/-- On a cuff `C` parameterized by `φ`, two disjoint embedded arcs `ξ, η` (with lifts `m₁, m₂` where
`m₁` is strictly increasing) can have `m₂` shifted by an integer so that:
- if `m₂` is `StrictMonoOn`, `m₁ 0 < m₁ 1 < m₂ 0 < m₂ 1 < m₁ 0 + 1`;
- if `m₂` is `StrictAntiOn`, `m₁ 0 < m₁ 1 < m₂ 1 < m₂ 0 < m₁ 0 + 1`. -/
theorem exists_two_lifts_order {C : Set Y} (φ : Circle ≃ₜ C) {ξ η : ℝ → Y}
    {m₁ m₂ : ℝ → ℝ}
    (hm₁c : ContinuousOn m₁ (Icc 0 1)) (hm₁m : StrictMonoOn m₁ (Icc 0 1))
    (hm₁e : ∀ u ∈ Icc (0 : ℝ) 1, (φ (ee (m₁ u))).1 = ξ u)
    (hm₂c : ContinuousOn m₂ (Icc 0 1))
    (hm₂_mo : StrictMonoOn m₂ (Icc 0 1) ∨ StrictAntiOn m₂ (Icc 0 1))
    (hm₂e : ∀ u ∈ Icc (0 : ℝ) 1, (φ (ee (m₂ u))).1 = η u)
    (hiξ : InjOn ξ (Icc 0 1)) (hiη : InjOn η (Icc 0 1))
    (hdj : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1, ξ u ≠ η v) :
    ∃ k : ℤ,
      (∀ u ∈ Icc (0 : ℝ) 1, (φ (ee (m₂ u + k))).1 = η u) ∧
      ((StrictMonoOn m₂ (Icc 0 1) ∧ m₁ 0 < m₁ 1 ∧ m₁ 1 < m₂ 0 + k ∧ m₂ 0 + k < m₂ 1 + k ∧ m₂ 1 + k < m₁ 0 + 1) ∨
       (StrictAntiOn m₂ (Icc 0 1) ∧ m₁ 0 < m₁ 1 ∧ m₁ 1 < m₂ 1 + k ∧ m₂ 1 + k < m₂ 0 + k ∧ m₂ 0 + k < m₁ 0 + 1)) := by
  have hlt1 : m₁ 1 < m₁ 0 + 1 := lift_lt_add_one hm₁c hm₁m (inj_of_lift hm₁e hiξ)
  have h01 : m₁ 0 < m₁ 1 := hm₁m ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one
  have hne_ee : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1, ee (m₁ u) ≠ ee (m₂ v) := fun u hu v hv he =>
    hdj u hu v hv (by rw [← hm₁e u hu, ← hm₂e v hv, he])
  have hshift_ee : ∀ (k : ℤ) u, u ∈ Icc (0 : ℝ) 1 → (φ (ee (m₂ u + k))).1 = η u := fun k u hu => by
    have : ee (m₂ u + k) = ee (m₂ u) := ee_eq_iff.mpr ⟨k, rfl⟩
    rw [this]; exact hm₂e u hu
  rcases hm₂_mo with hm₂m | hm₂a
  · -- `m₂` strictly increasing: pick `k : ℤ` so `m₂ 0 + k ∈ Ico (m₁ 0) (m₁ 0 + 1)`!
    let k : ℤ := -⌊m₂ 0 - m₁ 0⌋
    have hk_lo : m₁ 0 ≤ m₂ 0 + k := by
      simp only [k, Int.cast_neg]; linarith [Int.floor_le (m₂ 0 - m₁ 0)]
    have hk_hi : m₂ 0 + k < m₁ 0 + 1 := by
      simp only [k, Int.cast_neg]; linarith [Int.lt_floor_add_one (m₂ 0 - m₁ 0)]
    have hlt2 : m₂ 1 < m₂ 0 + 1 := lift_lt_add_one hm₂c hm₂m (inj_of_lift hm₂e hiη)
    have h201 : m₂ 0 < m₂ 1 := hm₂m ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one
    have h12 : m₁ 1 < m₂ 0 + k := by
      by_contra hle
      have hmem : m₂ 0 + k ∈ Icc (m₁ 0) (m₁ 1) := ⟨hk_lo, not_lt.mp hle⟩
      obtain ⟨u, hu, hueq⟩ := intermediate_value_Icc zero_le_one hm₁c hmem
      have : ee (m₁ u) = ee (m₂ 0) := by rw [hueq]; exact ee_eq_iff.mpr ⟨k, rfl⟩
      exact hne_ee u hu 0 ⟨le_rfl, zero_le_one⟩ this
    have h21 : m₂ 1 + k < m₁ 0 + 1 := by
      by_contra hge
      have hmem : m₁ 0 + 1 ∈ Icc (m₂ 0 + k) (m₂ 1 + k) := ⟨hk_hi.le, not_lt.mp hge⟩
      obtain ⟨v, hv, hveq⟩ := intermediate_value_Icc zero_le_one (hm₂c.add continuousOn_const) hmem
      have : ee (m₁ 0) = ee (m₂ v) := by
        rw [← ee_add_one (m₁ 0), ← hveq]; exact ee_eq_iff.mpr ⟨k, rfl⟩
      exact hne_ee 0 ⟨le_rfl, zero_le_one⟩ v hv this
    exact ⟨k, hshift_ee k, .inl ⟨hm₂m, h01, h12, by linarith, h21⟩⟩
  · -- `m₂` strictly decreasing: pick `k : ℤ` so `m₂ 1 + k ∈ Ico (m₁ 0) (m₁ 0 + 1)`!
    let k : ℤ := -⌊m₂ 1 - m₁ 0⌋
    have hk_lo : m₁ 0 ≤ m₂ 1 + k := by
      simp only [k, Int.cast_neg]; linarith [Int.floor_le (m₂ 1 - m₁ 0)]
    have hk_hi : m₂ 1 + k < m₁ 0 + 1 := by
      simp only [k, Int.cast_neg]; linarith [Int.lt_floor_add_one (m₂ 1 - m₁ 0)]
    have h210 : m₂ 1 < m₂ 0 := hm₂a ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one
    have h12 : m₁ 1 < m₂ 1 + k := by
      by_contra hle
      have hmem : m₂ 1 + k ∈ Icc (m₁ 0) (m₁ 1) := ⟨hk_lo, not_lt.mp hle⟩
      obtain ⟨u, hu, hueq⟩ := intermediate_value_Icc zero_le_one hm₁c hmem
      have : ee (m₁ u) = ee (m₂ 1) := by rw [hueq]; exact ee_eq_iff.mpr ⟨k, rfl⟩
      exact hne_ee u hu 1 ⟨zero_le_one, le_rfl⟩ this
    have h20 : m₂ 0 + k < m₁ 0 + 1 := by
      by_contra hge
      have hmem : m₁ 0 + 1 ∈ Icc (m₂ 1 + k) (m₂ 0 + k) := ⟨hk_hi.le, not_lt.mp hge⟩
      obtain ⟨v, hv, hveq⟩ := intermediate_value_Icc' zero_le_one (hm₂c.add continuousOn_const) hmem
      have : ee (m₁ 0) = ee (m₂ v) := by
        rw [← ee_add_one (m₁ 0), ← hveq]; exact ee_eq_iff.mpr ⟨k, rfl⟩
      exact hne_ee 0 ⟨le_rfl, zero_le_one⟩ v hv this
    exact ⟨k, hshift_ee k, .inr ⟨hm₂a, h01, h12, by linarith, h20⟩⟩

/-- **No-same-endpoint gap lemma**: if an open gap `(p, q)` (with `q - p < 1`) on a cuff `C_Y` of `Y`
avoids `ψ ⁻¹' F` and both endpoints map to the SAME point `x₀ ∈ C_S` on a cuff `C_S` of `S`,
then `ψ '' (φY '' ee '' Icc p q) = C_S` (so `C_S` cannot contain any other point of `F`!). -/
theorem gap_image_eq_cuff_of_same_end (hY : IsSurface Y) (hS : IsSurface S) [T2Space Y]
    {ψ : Y → S} {F : Set S} (hψ : IsCutting ψ F) (hF : IsClosed F)
    {CY : Set Y} (hCY : CY ⊆ bd Y) (φY : Circle ≃ₜ CY)
    {CS : Set S} (hCS : CS ∈ cuffs S)
    {p q : ℝ} (hpq : p < q) (hspan : q - p < 1)
    (hoff : ∀ v ∈ Ioo p q, ψ (φY (ee v)).1 ∉ F)
    (hend : ψ (φY (ee p)).1 = ψ (φY (ee q)).1)
    (hpCS : ψ (φY (ee p)).1 ∈ CS) :
    ψ '' ((fun v => (φY (ee v)).1) '' Icc p q) = CS := by
  have : CompactSpace Y := hY.1
  have : T2Space S := hS.2.1
  have hcfS := cuff_statement.{u} S hS
  obtain ⟨φS⟩ := hcfS.2.2 _ hCS
  let γ : ℝ → S := fun u => ψ (φY (ee (lin p q u))).1
  have hγc : ContinuousOn γ (Icc 0 1) :=
    hψ.1.comp_continuousOn (continuous_subtype_val.comp_continuousOn
      (φY.continuous.comp_continuousOn (continuous_ee.comp_continuousOn (continuousOn_lin p q))))
  have hγ_bd : ∀ u ∈ Icc (0 : ℝ) 1, γ u ∈ bd S := fun u hu => by
    rcases eq_or_lt_of_le hu.1 with rfl | h0
    · obtain ⟨z, -, rfl⟩ := hCS; exact connectedComponentIn_subset _ _ (by simpa [γ, lin_zero] using hpCS)
    · rcases eq_or_lt_of_le hu.2 with rfl | h1
      · obtain ⟨z, -, rfl⟩ := hCS; exact connectedComponentIn_subset _ _ (by simpa [γ, lin_one, ← hend] using hpCS)
      · exact (mem_bd_cut_iff hY hS hψ hF (hoff _ (lin_mem hpq.le ⟨h0, h1⟩ hpq))).mp (hCY (φY _).2)
  have hγ_CS : ∀ u ∈ Icc (0 : ℝ) 1, γ u ∈ CS := by
    obtain ⟨z, hz, rfl⟩ := hCS
    have hpre := isPreconnected_Icc.image γ hγc
    have h0 : γ 0 ∈ connectedComponentIn (bd S) z := by simpa [γ, lin_zero] using hpCS
    have hsub : γ '' Icc 0 1 ⊆ connectedComponentIn (bd S) (γ 0) :=
      hpre.subset_connectedComponentIn ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩ (by rintro _ ⟨u, hu, rfl⟩; exact hγ_bd u hu)
    have hcomp_eq : connectedComponentIn (bd S) (γ 0) = connectedComponentIn (bd S) z :=
      (connectedComponentIn_eq h0).symm
    intro u hu; exact hcomp_eq ▸ hsub ⟨u, hu, rfl⟩
  have hγ01 : γ 0 = γ 1 := by simp only [γ, lin_zero, lin_one]; exact hend
  have hγ_inj : InjOn γ (Ico 0 1) := fun a ha b hb he => by
    rcases eq_or_lt_of_le ha.1 with rfl | ha0
    · rcases eq_or_lt_of_le hb.1 with rfl | hb0
      · rfl
      · exfalso
        have h1 : ψ (φY (ee (lin p q b))).1 ∈ F := by
          -- Wait: what if `ψ (φY (ee p)) ∉ F`? Then `ψ` is injective on `φY (ee p)` and `φY (ee (lin p q b))`, impossible since `q - p < 1`!
          by_contra hnotF
          have hnotF0 : ψ (φY (ee p)).1 ∉ F := by rwa [show ψ (φY (ee p)).1 = γ 0 by simp [γ, lin_zero], he]
          have heY := hψ.2.2.1 hnotF0 hnotF (by simpa [γ, lin_zero] using he)
          have hee := φY.injective (Subtype.ext heY)
          have hlin := lin_mem hpq.le ⟨hb0, hb.2⟩ hpq
          exact ee_ne hlin.1 (by linarith [hlin.2]) hee
        exact hoff _ (lin_mem hpq.le ⟨hb0, hb.2⟩ hpq) h1
    · rcases eq_or_lt_of_le hb.1 with rfl | hb0
      · exfalso
        have h1 : ψ (φY (ee (lin p q a))).1 ∈ F := by
          by_contra hnotF
          have hnotF0 : ψ (φY (ee p)).1 ∉ F := by rwa [show ψ (φY (ee p)).1 = γ 0 by simp [γ, lin_zero], ← he]
          have heY := hψ.2.2.1 hnotF hnotF0 (by simpa [γ, lin_zero] using he)
          have hee := φY.injective (Subtype.ext heY)
          have hlin := lin_mem hpq.le ⟨ha0, ha.2⟩ hpq
          exact ee_ne hlin.1 (by linarith [hlin.2]) hee.symm
        exact hoff _ (lin_mem hpq.le ⟨ha0, ha.2⟩ hpq) h1
      · have h1 := hoff _ (lin_mem hpq.le ⟨ha0, ha.2⟩ hpq)
        have h2 := hoff _ (lin_mem hpq.le ⟨hb0, hb.2⟩ hpq)
        have heY := hψ.2.2.1 h1 h2 he
        have hee := φY.injective (Subtype.ext heY)
        have hlinA := lin_mem hpq.le ⟨ha0, ha.2⟩ hpq
        have hlinB := lin_mem hpq.le ⟨hb0, hb.2⟩ hpq
        obtain ⟨k, hk⟩ := ee_eq_iff.mp hee
        have hklt : |(k : ℝ)| < 1 := by rw [abs_lt]; exact ⟨by linarith [hlinA.1, hlinB.2], by linarith [hlinA.2, hlinB.1]⟩
        have hk0 : k = 0 := by have := abs_lt.mp (show |k| < 1 by exact_mod_cast hklt); omega
        subst hk0; simp only [Int.cast_zero, add_zero] at hk
        exact (strictMonoOn_lin hpq).injOn (Ico_subset_Icc_self ha) (Ico_subset_Icc_self hb) hk
  -- Build `Circle ≃ₜ (γ '' Icc 0 1)` just like `holeParam`, then apply `oarc_eq`!
  have him_eq : ψ '' ((fun v => (φY (ee v)).1) '' Icc p q) = γ '' Icc 0 1 := by
    ext x; constructor
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      refine ⟨(v - p) / (q - p), ⟨div_nonneg (by linarith [hv.1]) (by linarith),
        (div_le_one (by linarith)).mpr (by linarith [hv.2])⟩, ?_⟩
      simp only [γ, lin]; congr 4; field_simp; ring
    · rintro ⟨u, hu, rfl⟩
      exact ⟨(φY (ee (lin p q u))).1, ⟨lin p q u, ⟨by simp only [lin]; nlinarith [hu.1],
        by simp only [lin]; nlinarith [hu.2]⟩, rfl⟩, rfl⟩
  rw [him_eq]
  have hHomeo : Circle ≃ₜ (γ '' Icc 0 1 : Set S) := by
    let g : Circle → (γ '' Icc 0 1 : Set S) := fun z =>
      let u := (exists_param z).choose
      ⟨γ u, ⟨u, Ico_subset_Icc_self (exists_param z).choose_spec.1, rfl⟩⟩
    have hg_ee : ∀ u ∈ Icc (0 : ℝ) 1, (g (ee u)).1 = γ u := fun u hu => by
      dsimp only [g]; set v := (exists_param (ee u)).choose; have hv := (exists_param (ee u)).choose_spec
      rcases eq_or_lt_of_le hu.2 with rfl | hlt
      · obtain ⟨k, hk⟩ := ee_eq_iff.mp (hv.2.trans (show ee 1 = ee 0 by simpa using ee_add_one 0))
        have hklt : |(k : ℝ)| < 1 := by rw [abs_lt]; exact ⟨by linarith [hv.1.1], by linarith [hv.1.2]⟩
        have hk0 : k = 0 := by have := abs_lt.mp (show |k| < 1 by exact_mod_cast hklt); omega
        subst hk0; simp only [Int.cast_zero, add_zero] at hk
        have hv0 : v = 0 := hk
        rw [hv0, hγ01]
      · obtain ⟨k, hk⟩ := ee_eq_iff.mp hv.2
        have hklt : |(k : ℝ)| < 1 := by rw [abs_lt]; exact ⟨by linarith [hv.1.1, hlt], by linarith [hv.1.2, hu.1]⟩
        have hk0 : k = 0 := by have := abs_lt.mp (show |k| < 1 by exact_mod_cast hklt); omega
        subst hk0; simp only [Int.cast_zero, add_zero] at hk
        have hvu : v = u := hk
        rw [hvu]
    have hgc : Continuous g := by
      have hq : IsQuotientMap (fun t : ℝ => ee t) :=
        (Circle.isCoveringMap_exp.isQuotientMap fun z => ⟨_, Circle.exp_arg z⟩).comp
          (Homeomorph.mulLeft₀ (2 * Real.pi) (by positivity)).isQuotientMap
      rw [hq.continuous_iff]
      have hcomp : g ∘ ee = fun t : ℝ =>
          ⟨γ (Int.fract t), ⟨Int.fract t, ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩, rfl⟩⟩ := by
        funext t
        have hfr : ee t = ee (Int.fract t) := ee_eq_iff.mpr ⟨⌊t⌋, by linarith [Int.floor_add_fract t]⟩
        ext; simp only [comp_apply, hfr]; exact hg_ee _ ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
      rw [hcomp]
      exact continuous_induced_rng.mpr (ContinuousOn.comp_fract'' hγc hγ01)
    have hgb : Bijective g := by
      refine ⟨fun z₁ z₂ he => ?_, fun ⟨x, u, hu, hx⟩ => ⟨ee u, Subtype.ext ((hg_ee u hu).trans hx)⟩⟩
      obtain ⟨u₁, hu₁, rfl⟩ := exists_param z₁
      obtain ⟨u₂, hu₂, rfl⟩ := exists_param z₂
      have he' : γ u₁ = γ u₂ := by rw [← hg_ee u₁ (Ico_subset_Icc_self hu₁), ← hg_ee u₂ (Ico_subset_Icc_self hu₂), he]
      rw [hγ_inj hu₁ hu₂ he']
    exact hgc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g hgb)
  exact oarc_eq φS ⟨hHomeo⟩ (by rintro _ ⟨u, hu, rfl⟩; exact hγ_CS u hu)

/-- On a cuff `C_st = connectedComponentIn (bd S) s` containing `s ≠ t`, with `φ_st : Circle ≃ₜ C_st`,
`u_s < u_t < u_s + 1`, `(φ_st (ee u_s)).1 = s`, `(φ_st (ee u_t)).1 = t`, define the two open arcs
`G₁ := (fun v => (φ_st (ee v)).1) '' Ioo u_t (u_s + 1)` and `G₂ := (fun v => (φ_st (ee v)).1) '' Ioo u_s u_t`.
Then `C_st \ {s, t} = G₁ ∪ G₂`, `Disjoint G₁ G₂`, and both `G₁, G₂` are open in `C_st`. -/
theorem same_cuff_gaps_partition {CS : Set S} (φS : Circle ≃ₜ CS) {s t : S}
    {u_s u_t : ℝ} (h1 : u_s < u_t) (h2 : u_t < u_s + 1)
    (hs : (φS (ee u_s)).1 = s) (ht : (φS (ee u_t)).1 = t) :
    let G₁ := (fun v => (φS (ee v)).1) '' Ioo u_t (u_s + 1)
    let G₂ := (fun v => (φS (ee v)).1) '' Ioo u_s u_t
    CS \ {s, t} = G₁ ∪ G₂ ∧ Disjoint G₁ G₂ ∧ IsPreconnected G₁ ∧ IsPreconnected G₂ := by
  intro G₁ G₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext x; constructor
    · rintro ⟨hxC, hxst⟩
      obtain ⟨r, hr, hreq⟩ := exists_param (φS.symm ⟨x, hxC⟩)
      -- Shift `r` into `Ico u_s (u_s + 1)`:
      let v := r + ⌊u_s - r⌋ + 1
      -- Actually `v := u_s + Int.fract (r - u_s)` lies in `Ico u_s (u_s + 1)` and `ee v = ee r`!
      set w := u_s + Int.fract (r - u_s)
      have hw_lo : u_s ≤ w := by simp only [w]; linarith [Int.fract_nonneg (r - u_s)]
      have hw_hi : w < u_s + 1 := by simp only [w]; linarith [Int.fract_lt_one (r - u_s)]
      have hwee : ee w = ee r := ee_eq_iff.mpr ⟨-⌊r - u_s⌋, by simp only [w, Int.cast_neg]; linarith [Int.floor_add_fract (r - u_s)]⟩
      have hwx : (φS (ee w)).1 = x := by rw [hwee, hreq]; simp
      have hne_s : w ≠ u_s := fun he => hxst (Or.inl (by rw [← hwx, he, hs]))
      have hne_t : w ≠ u_t := fun he => hxst (Or.inr (mem_singleton_iff.mpr (by rw [← hwx, he, ht])))
      rcases lt_or_gt_of_ne hne_t with hlt | hgt
      · exact .inr ⟨w, ⟨lt_of_le_of_ne hw_lo (Ne.symm hne_s), hlt⟩, hwx⟩
      · exact .inl ⟨w, ⟨hgt, hw_hi⟩, hwx⟩
    · rintro (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
      · refine ⟨(φS _).2, ?_⟩
        rintro (hxs | hxt)
        · exact ee_ne (by linarith [hv.1]) hv.2 (φS.injective (Subtype.ext (hs.trans hxs.symm)))
        · exact ee_ne hv.1 (by linarith [hv.2]) (φS.injective (Subtype.ext (ht.trans hxt.symm)))
      · refine ⟨(φS _).2, ?_⟩
        rintro (hxs | hxt)
        · exact ee_ne hv.1 (by linarith [hv.2]) (φS.injective (Subtype.ext (hs.trans hxs.symm)))
        · exact ee_ne hv.2 (by linarith [hv.1]) (φS.injective (Subtype.ext ((mem_singleton_iff.mp hxt).trans ht.symm)))
  · rw [Set.disjoint_left]
    rintro _ ⟨v₁, hv₁, rfl⟩ ⟨v₂, hv₂, he⟩
    exact ee_ne (x := v₂) (y := v₁) (by linarith [hv₂.2, hv₁.1]) (by linarith [hv₁.2, hv₂.1])
      (φS.injective (Subtype.ext he))
  · exact isPreconnected_Ioo.image _ (continuous_subtype_val.comp (φS.continuous.comp continuous_ee)).continuousOn
  · exact isPreconnected_Ioo.image _ (continuous_subtype_val.comp (φS.continuous.comp continuous_ee)).continuousOn

end LiftOrderAndGaps

/-! ### Exact classification of `(aY, bY, cY)` vs `(aS, bS, cS)` and `cocInt (w1 AS)` -/

section CutModelClass

variable {Y S : Type u} [TopologicalSpace Y] [TopologicalSpace S]

/-- **Model classification for cutting along a non-separating proper `I`-arc**:
Given connected `S ≃ₜ SurfaceModel aS bS cS` and connected `Y ≃ₜ SurfaceModel aY bY cY`
cutting `S` along `F` (with ends `s ≠ t`, `ArcLift ψ F a ξ η`):
1. If `C_s ≠ C_t`: `C_ξ = C_η`, `cY + 1 = cS`, `2*aY + bY = 2*aS + bS`, `bY = 0 ↔ bS = 0`, and
   `ξ, η` run in OPPOSITE directions on `C_ξ`.
2. If `C_s = C_t` and `C_ξ ≠ C_η`: `cY = cS + 1`, `2*aY + bY + 2 = 2*aS + bS`.
3. If `C_s = C_t` and `C_ξ = C_η`: `cY = cS`, `2*aY + bY + 1 = 2*aS + bS`, and
   `ξ, η` run in the SAME direction on `C_ξ`. -/
theorem cut_arc_model_invariants [ConnectedSpace S] [ConnectedSpace Y] [T2Space Y]
    (hS : IsSurface S) (hY : IsSurface Y)
    {ψ : Y → S} {F : Set S} {s t : S} (hne : s ≠ t) (hψ : IsCutting ψ F)
    (hb : F ∩ bd S = {s, t}) (hl : IsLineWithEnds F s t)
    {X X' : Set Y} (hP : LiftPair ψ F s t X X')
    {a : ℝ → S} {ξ η : ℝ → Y} (L : ArcLift ψ F a ξ η)
    (ha0 : a 0 = s) (ha1 : a 1 = t)
    (himξ : ξ '' Icc 0 1 = X) (himη : η '' Icc 0 1 = X')
    (hiξ : InjOn ξ (Icc 0 1)) (hiη : InjOn η (Icc 0 1))
    {aS bS cS aY bY cY : ℕ}
    (eS : S ≃ₜ SurfaceModel aS bS cS) (eY : Y ≃ₜ SurfaceModel aY bY cY) :
    let C_s := connectedComponentIn (bd S) s
    let C_t := connectedComponentIn (bd S) t
    let C_ξ := connectedComponentIn (bd Y) (ξ 0)
    let C_η := connectedComponentIn (bd Y) (η 0)
    (C_s ≠ C_t → C_ξ = C_η ∧ cY + 1 = cS ∧ 2 * aY + bY = 2 * aS + bS ∧ (bY = 0 ↔ bS = 0)) ∧
    (C_s = C_t → C_ξ ≠ C_η → cY = cS + 1 ∧ 2 * aY + bY + 2 = 2 * aS + bS) ∧
    (C_s = C_t → C_ξ = C_η → cY = cS ∧ 2 * aY + bY + 1 = 2 * aS + bS) := by
  intro C_s C_t C_ξ C_η
  have : CompactSpace Y := hY.1
  have : T2Space S := hS.2.1
  have hFc : IsClosed F := hl.isCompact.isClosed
  obtain ⟨_, _, _, _, _, _, hd, hun, -⟩ := id hP
  have hsb : s ∈ bd S := (show s ∈ F ∩ bd S from hb ▸ mem_insert _ _).2
  have htb : t ∈ bd S := (show t ∈ F ∩ bd S from hb ▸ mem_insert_of_mem _ rfl).2
  have hub : ψ ⁻¹' F = ξ '' Icc 0 1 ∪ η '' Icc 0 1 := by rw [himξ, himη, hun]
  have hXb : X ⊆ bd Y := fun z hz => hψ.2.2.2.2 (hun ▸ Or.inl hz)
  have hXb' : X' ⊆ bd Y := fun z hz => hψ.2.2.2.2 (hun ▸ Or.inr hz)
  have pX : IsPreconnected X := himξ ▸ isPreconnected_Icc.image _ L.cξ
  have pX' : IsPreconnected X' := himη ▸ isPreconnected_Icc.image _ L.cη
  have hx0 : ξ 0 ∈ X := himξ ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  have hy0 : η 0 ∈ X' := himη ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  have hCξ : C_ξ ∈ cuffs Y := ⟨_, hXb hx0, rfl⟩
  have hCη : C_η ∈ cuffs Y := ⟨_, hXb' hy0, rfl⟩
  have hXC : X ⊆ C_ξ := pX.subset_connectedComponentIn hx0 hXb
  have hXC' : X' ⊆ C_η := pX'.subset_connectedComponentIn hy0 hXb'
  have hξm : ∀ u ∈ Icc (0 : ℝ) 1, ξ u ∈ X := fun u hu => himξ ▸ ⟨u, hu, rfl⟩
  have hηm : ∀ u ∈ Icc (0 : ℝ) 1, η u ∈ X' := fun u hu => himη ▸ ⟨u, hu, rfl⟩
  have hdcuff := cuff_statement.{u} Y hY
  have hdc : ∀ {C : Set Y}, C ∈ cuffs Y → C ⊆ bd Y := fun {C} hC => by
    obtain ⟨z, -, rfl⟩ := hC; exact connectedComponentIn_subset _ _
  have hcrit := modelCriterion.2
  have : Nonempty S := ⟨s⟩
  -- Analyze `C_ξ = C_η` vs `C_ξ ≠ C_η`:
  by_cases hCC : C_ξ = C_η
  · -- Single cut cuff `C_ξ = C_η`:
    obtain ⟨i, hi, φ, g, hg, hs⟩ := exists_one_hole eY hCξ
    obtain ⟨a', ξ', η', m, L', ha', hxim, heim, hix, hie, hmc, hmm, hmξ⟩ :=
      orient_lift L φ (fun u hu => hXC (hξm u hu)) hiξ hiη
    obtain ⟨hN, hLf⟩ := erase_facts cY i
    have hξ' : ∀ u ∈ Icc (0 : ℝ) 1, ξ' u ∈ X := fun u hu => by rw [← himξ, ← hxim]; exact ⟨u, hu, rfl⟩
    have hη' : ∀ u ∈ Icc (0 : ℝ) 1, η' u ∈ X' := fun u hu => by rw [← himη, ← heim]; exact ⟨u, hu, rfl⟩
    have hub' : ψ ⁻¹' F = ξ' '' Icc 0 1 ∪ η' '' Icc 0 1 := by rw [hxim, heim, hub]
    obtain ⟨σ, g', hp, -, p, q, hpq, e1, e2, e3⟩ := arc_one_aux hY L' hψ.1 hψ.2.1 hCξ φ hi hLf hg hs hmc hmm hmξ
      (fun u hu => hCC ▸ hXC' (hη' u hu)) hix hie (fun u hu v hv he => Set.disjoint_left.mp hd (hξ' u hu) (he ▸ hη' v hv))
    have hn := nf_blkB (a := aY) (b := bY) (c := cY) hi hN hLf σ
    have hlen := length_erase_range hi
    cases σ with
    | false =>
      obtain ⟨w, h5, h6⟩ := hn.1 rfl
      obtain ⟨e'⟩ := homeo_of_nf hp h5 h6
      rw [hlen, show cY - 1 + 2 = cY + 1 by omega] at e'
      have hinv := (hcrit aY bY (cY + 1) aS bS cS).mp ⟨e'.symm.trans eS⟩
      -- Also show `C_s ≠ C_t`! (Wait: if `C_s = C_t`, then `σ = false` is impossible by `gap_image_eq_cuff_of_same_end`!)
      have hne_st : C_s ≠ C_t := by
        intro hst_eq
        -- `p < q` has `φ (ee p) = ξ' 1`, `φ (ee q) = η' (ofs false 0) = η' 1`, so BOTH map to `a' 1 ∈ {s, t}`!
        have h0 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
        have hb1 : ψ (φ (ee p)).1 = a' 1 := by rw [e1, L'.hξ 1 h0]
        have hb2 : ψ (φ (ee q)).1 = a' 1 := by rw [e2, ofs_false, sub_zero, L'.hη 1 h0]
        have hlt_span : q - p < 1 := by
          -- Wait: `φ (ee p) = ξ' 1` and `φ (ee q) = η' 1`; could `q - p ≥ 1`?
          -- Look at `e3`: for ALL `v ∈ Ioo p q`, `φ (ee v) ≠ ξ' u`! If `q - p ≥ 1`, then `p + 1 ∈ Ioo p q`? Wait if `q - p = 1`, `ee q = ee p`, contradicting `ξ' 1 ≠ η' 1`! And if `q - p > 1`, `p + 1 ∈ Ioo p q` has `φ (ee (p + 1)) = φ (ee p) = ξ' 1`, contradicting `e3`!
          by_contra hge
          rcases eq_or_lt_of_le (not_lt.mp hge) with he | hgt
          · have : ee q = ee p := ee_eq_iff.mpr ⟨1, by push_cast; linarith⟩
            exact Set.disjoint_left.mp hd (hξ' 1 h0) (by rw [← e1, ← this, e2, ofs_false, sub_zero]; exact hη' 1 h0)
          · have hp1 : p + 1 ∈ Ioo p q := ⟨by linarith, by linarith⟩
            exact (e3 (p + 1) hp1 1 h0).1 (by rw [ee_add_one, e1])
        have hoff : ∀ v ∈ Ioo p q, ψ (φ (ee v)).1 ∉ F := fun v hv hF' => by
          have hm' : (φ (ee v)).1 ∈ ψ ⁻¹' F := hF'
          rw [hub'] at hm'
          rcases hm' with ⟨u, hu, hu'⟩ | ⟨u, hu, hu'⟩
          · exact (e3 v hv u hu).1 hu'.symm
          · exact (e3 v hv u hu).2 hu'.symm
        have ha1_in : a' 1 ∈ C_s := by
          rcases ha' with ⟨-, h2⟩ | ⟨-, h2⟩
          · rw [h2, ha1, hst_eq]; exact mem_connectedComponentIn htb
          · rw [h2, ha0]; exact mem_connectedComponentIn hsb
        have hCs_cuff : C_s ∈ cuffs S := ⟨s, hsb, rfl⟩
        have hfull := gap_image_eq_cuff_of_same_end hY hS hψ hFc (hdc hCξ) φ hCs_cuff hpq hlt_span hoff
          (hb1.trans hb2.symm) (hb1.symm ▸ ha1_in)
        -- `a' 0 ∈ C_s` (`≠ a' 1`), so `a' 0 = ψ (φ (ee v))` for some `v ∈ Ioo p q`, contradicting `hoff`!
        have ha0_in : a' 0 ∈ C_s := by
          rcases ha' with ⟨h2, -⟩ | ⟨h2, -⟩
          · rw [h2, ha0]; exact mem_connectedComponentIn hsb
          · rw [h2, ha1, hst_eq]; exact mem_connectedComponentIn htb
        have ha0_ne : a' 0 ≠ a' 1 := by
          rcases ha' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2, ha0, ha1]
          · exact hne
          · exact hne.symm
        obtain ⟨_, ⟨v, hv, rfl⟩, hv_eq⟩ := hfull.symm.subset ha0_in
        have hv_ne_p : v ≠ p := fun he => ha0_ne (by rw [← hv_eq, he, hb1])
        have hv_ne_q : v ≠ q := fun he => ha0_ne (by rw [← hv_eq, he, hb2])
        have ha0_F : a' 0 ∈ F := by
          rcases ha' with ⟨h2, -⟩ | ⟨h2, -⟩
          · rw [h2, ha0]; exact (show s ∈ F ∩ bd S from hb ▸ mem_insert _ _).1
          · rw [h2, ha1]; exact (show t ∈ F ∩ bd S from hb ▸ mem_insert_of_mem _ rfl).1
        exact hoff v ⟨lt_of_le_of_ne hv.1 (Ne.symm hv_ne_p), lt_of_le_of_ne hv.2 hv_ne_q⟩ (hv_eq.symm ▸ ha0_F)
      exact ⟨fun _ => ⟨hCC, hinv.1, hinv.2.1, hinv.2.2⟩,
        fun h => absurd h hne_st,
        fun h _ => absurd h hne_st⟩
    | true =>
      obtain ⟨w, h5, h6⟩ := hn.2 rfl
      obtain ⟨e'⟩ := homeo_of_nf hp h5 h6
      rw [hlen, show cY - 1 + 1 = cY by omega] at e'
      have hinv := (hcrit aY (bY + 1) cY aS bS cS).mp ⟨e'.symm.trans eS⟩
      have h0 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
      have hb1 : ψ (φ (ee p)).1 = a' 1 := by rw [e1, L'.hξ 1 h0]
      have hb2 : ψ (φ (ee q)).1 = a' 0 := by rw [e2, ofs_true, L'.hη 0 ⟨le_rfl, zero_le_one⟩]
      have hends : a' 0 ∈ bd S ∧ a' 1 ∈ bd S := by
        rcases ha' with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> rw [h2, h3, ha0, ha1] <;> exact ⟨by assumption, by assumption⟩
      have key := same_of_gap hψ hFc (hdc hCξ) φ hpq (fun v hv hF' => by
        have hm' : (φ (ee v)).1 ∈ ψ ⁻¹' F := hF'
        rw [hub'] at hm'
        rcases hm' with ⟨u, hu, hu'⟩ | ⟨u, hu, hu'⟩
        · exact (e3 v hv u hu).1 hu'.symm
        · exact (e3 v hv u hu).2 hu'.symm) (hb1 ▸ hends.2) (hb2 ▸ hends.1)
      rw [hb1, hb2] at key
      have hsame : C_s = C_t := by
        rcases ha' with ⟨h2, h3⟩ | ⟨h2, h3⟩
        · rw [h2, h3, ha0, ha1] at key; exact key.symm
        · rw [h2, h3, ha0, ha1] at key; exact key
      exact ⟨fun h => absurd hsame h,
        fun _ h => absurd hCC h,
        fun _ _ => ⟨hinv.1, by omega⟩⟩
  · -- Two distinct cut cuffs `C_ξ ≠ C_η`:
    have hdis := cuffs_disjoint hCξ hCη hCC
    obtain ⟨φ₀⟩ := hdcuff.2.2 _ hCξ
    have hsame : C_s = C_t := by
      have := same_of_cuff hψ hFc L (hdc hCξ) φ₀ (fun u hu => hXC (hξm u hu)) hiξ hiη
        (fun u hu hm => Set.disjoint_left.mp hdis hm (hXC' (hηm u hu))) hub (ha0 ▸ hsb) (ha1 ▸ htb)
      rwa [ha0, ha1] at this
    obtain ⟨i, hi, j, hj, hij, φ, φ', g, hg, hs, hs'⟩ := exists_two_holes eY hCξ hCη hCC
    obtain ⟨a', ξ', η', m, L', ha', hxim, heim, hix, hie, hmc, hmm, hmξ⟩ :=
      orient_lift L φ (fun u hu => hXC (hξm u hu)) hiξ hiη
    obtain ⟨hN, hLf⟩ := erase_erase_facts cY i j
    have hη' : ∀ u ∈ Icc (0 : ℝ) 1, η' u ∈ X' := fun u hu => by rw [← himη, ← heim]; exact ⟨u, hu, rfl⟩
    obtain ⟨σ, g', hp, -⟩ := arc_two_aux hY L' hψ.1 hψ.2.1 hCξ hCη (hdcuff.2.2 _ hCξ).isCompact.isClosed
      (hdcuff.2.2 _ hCη).isCompact.isClosed hdis φ φ' hij hi hj hLf hg hs hs' hmc hmm hmξ (fun u hu => hXC' (hη' u hu)) hix hie
    have hn := nf_blkA (a := aY) (b := bY) (c := cY) hij hi hj hN hLf σ
    have hlen := length_erase_erase hij hi hj
    have hinv_2 : cY = cS + 1 ∧ 2 * aY + bY + 2 = 2 * aS + bS := by
      cases σ with
      | false =>
        obtain ⟨w, h5, h6⟩ := hn.1 rfl
        obtain ⟨e'⟩ := homeo_of_nf hp h5 h6
        rw [hlen] at e'
        have hinv := (hcrit (aY + 1) bY (cY - 2 + 1) aS bS cS).mp ⟨e'.symm.trans eS⟩
        exact ⟨by omega, by omega⟩
      | true =>
        obtain ⟨w, h5, h6⟩ := hn.2 rfl
        obtain ⟨e'⟩ := homeo_of_nf hp h5 h6
        rw [hlen] at e'
        have hinv := (hcrit aY (bY + 2) (cY - 2 + 1) aS bS cS).mp ⟨e'.symm.trans eS⟩
        exact ⟨by omega, by omega⟩
    exact ⟨fun h => absurd hsame h, fun _ _ => hinv_2, fun _ h => absurd h hCC⟩

/-- Direction of `ξ, η` on a single cut cuff `C = C_ξ = C_η`:
- When `C_s ≠ C_t`, `ξ` and `η` run in **OPPOSITE** directions on `C`.
- When `C_s = C_t`, `ξ` and `η` run in the **SAME** direction on `C`. -/
theorem cut_single_cuff_dirs (hY : IsSurface Y) (hS : IsSurface S) [T2Space Y]
    {ψ : Y → S} {F : Set S} {s t : S} (hne : s ≠ t) (hψ : IsCutting ψ F) (hF : IsClosed F)
    (hb : F ∩ bd S = {s, t}) {X X' : Set Y} (hP : LiftPair ψ F s t X X')
    {a : ℝ → S} {ξ η : ℝ → Y} (L : ArcLift ψ F a ξ η)
    (ha0 : a 0 = s) (ha1 : a 1 = t)
    (himξ : ξ '' Icc 0 1 = X) (himη : η '' Icc 0 1 = X')
    (hiξ : InjOn ξ (Icc 0 1)) (hiη : InjOn η (Icc 0 1))
    {C : Set Y} (hC : C ∈ cuffs Y) (φ : Circle ≃ₜ C)
    {m₁ m₂ : ℝ → ℝ}
    (hm₁c : ContinuousOn m₁ (Icc 0 1)) (hm₁m : StrictMonoOn m₁ (Icc 0 1))
    (hm₁e : ∀ u ∈ Icc (0 : ℝ) 1, (φ (ee (m₁ u))).1 = ξ u)
    (hm₂c : ContinuousOn m₂ (Icc 0 1))
    (hm₂e : ∀ u ∈ Icc (0 : ℝ) 1, (φ (ee (m₂ u))).1 = η u) :
    let C_s := connectedComponentIn (bd S) s
    let C_t := connectedComponentIn (bd S) t
    (C_s ≠ C_t → StrictAntiOn m₂ (Icc 0 1)) ∧ (C_s = C_t → StrictMonoOn m₂ (Icc 0 1)) := by
  intro C_s C_t
  have : CompactSpace Y := hY.1
  have : T2Space S := hS.2.1
  obtain ⟨_, _, _, _, _, _, hd, hun, -⟩ := id hP
  have hsb : s ∈ bd S := (show s ∈ F ∩ bd S from hb ▸ mem_insert _ _).2
  have htb : t ∈ bd S := (show t ∈ F ∩ bd S from hb ▸ mem_insert_of_mem _ rfl).2
  have hCbd : C ⊆ bd Y := by obtain ⟨z, -, rfl⟩ := hC; exact connectedComponentIn_subset _ _
  have hmo2 := lift_mono hm₂c (inj_of_lift hm₂e hiη)
  have hdj : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1, ξ u ≠ η v := fun u hu v hv he => by
    have h1 : ξ u ∈ X := himξ ▸ ⟨u, hu, rfl⟩
    have h2 : ξ u ∈ X' := he ▸ (show η v ∈ X' from himη ▸ ⟨v, hv, rfl⟩)
    exact Set.disjoint_left.mp hd h1 h2
  obtain ⟨k, hk_e, hord⟩ := exists_two_lifts_order φ hm₁c hm₁m hm₁e hm₂c hmo2 hm₂e hiξ hiη hdj
  have hub : ψ ⁻¹' F = ξ '' Icc 0 1 ∪ η '' Icc 0 1 := by rw [himξ, himη, hun]
  rcases hord with ⟨hm2m, h01, h12, h23, h34⟩ | ⟨hm2a, h01, h12, h23, h34⟩
  · -- `m₂` is `StrictMonoOn`: the gap `(m₁ 1, m₂ 0 + k)` connects `ξ 1` (over `t`) to `η 0` (over `s`), so `C_s = C_t`!
    have hoff : ∀ v ∈ Ioo (m₁ 1) (m₂ 0 + k), ψ (φ (ee v)).1 ∉ F := fun v hv hF' => by
      have hm' : (φ (ee v)).1 ∈ ψ ⁻¹' F := hF'
      rw [hub] at hm'
      rcases hm' with ⟨u, hu, hu'⟩ | ⟨u, hu, hu'⟩
      · have h1 := φ.injective (Subtype.ext ((hm₁e u hu).trans hu'))
        have hlo := hm₁m.monotoneOn ⟨le_rfl, zero_le_one⟩ hu hu.1
        have hhi := hm₁m.monotoneOn hu ⟨zero_le_one, le_rfl⟩ hu.2
        exact ee_ne (by linarith [hv.1]) (by linarith [hv.2]) h1
      · have h1 := φ.injective (Subtype.ext ((hk_e u hu).trans hu'))
        have hlo := hm2m.monotoneOn ⟨le_rfl, zero_le_one⟩ hu hu.1
        have hhi := hm2m.monotoneOn hu ⟨zero_le_one, le_rfl⟩ hu.2
        exact ee_ne (by linarith [hv.2]) (by linarith [hv.1]) h1.symm
    have hp : ψ (φ (ee (m₁ 1))).1 = t := by rw [hm₁e 1 ⟨zero_le_one, le_rfl⟩, L.hξ 1 ⟨zero_le_one, le_rfl⟩, ha1]
    have hq : ψ (φ (ee (m₂ 0 + k))).1 = s := by rw [hk_e 0 ⟨le_rfl, zero_le_one⟩, L.hη 0 ⟨le_rfl, zero_le_one⟩, ha0]
    have hsame := same_of_gap hψ hF hCbd φ h12 hoff (hp.symm ▸ htb) (hq.symm ▸ hsb)
    rw [hp, hq] at hsame
    exact ⟨fun h => absurd hsame.symm h, fun _ => hm2m⟩
  · -- `m₂` is `StrictAntiOn`: the gap `(m₁ 1, m₂ 1 + k)` connects `ξ 1` (over `t`) to `η 1` (over `t`), so `C_s ≠ C_t`!
    have hoff : ∀ v ∈ Ioo (m₁ 1) (m₂ 1 + k), ψ (φ (ee v)).1 ∉ F := fun v hv hF' => by
      have hm' : (φ (ee v)).1 ∈ ψ ⁻¹' F := hF'
      rw [hub] at hm'
      rcases hm' with ⟨u, hu, hu'⟩ | ⟨u, hu, hu'⟩
      · have h1 := φ.injective (Subtype.ext ((hm₁e u hu).trans hu'))
        have hlo := hm₁m.monotoneOn ⟨le_rfl, zero_le_one⟩ hu hu.1
        have hhi := hm₁m.monotoneOn hu ⟨zero_le_one, le_rfl⟩ hu.2
        exact ee_ne (by linarith [hv.1]) (by linarith [hv.2]) h1
      · have h1 := φ.injective (Subtype.ext ((hk_e u hu).trans hu'))
        have hlo := hm2a.antitoneOn hu ⟨zero_le_one, le_rfl⟩ hu.2
        have hhi := hm2a.antitoneOn ⟨le_rfl, zero_le_one⟩ hu hu.1
        exact ee_ne (by linarith [hv.2]) (by linarith [hv.1]) h1.symm
    have hp : ψ (φ (ee (m₁ 1))).1 = t := by rw [hm₁e 1 ⟨zero_le_one, le_rfl⟩, L.hξ 1 ⟨zero_le_one, le_rfl⟩, ha1]
    have hq : ψ (φ (ee (m₂ 1 + k))).1 = t := by rw [hk_e 1 ⟨zero_le_one, le_rfl⟩, L.hη 1 ⟨zero_le_one, le_rfl⟩, ha1]
    have hne_st : C_s ≠ C_t := by
      intro hst_eq
      have hCt_cuff : C_t ∈ cuffs S := ⟨t, htb, rfl⟩
      have hfull := gap_image_eq_cuff_of_same_end hY hS hψ hF hCbd φ hCt_cuff h12 (by linarith) hoff
        (hp.trans hq.symm) (hp.symm ▸ mem_connectedComponentIn htb)
      have hsCt : s ∈ C_t := hst_eq ▸ mem_connectedComponentIn hsb
      obtain ⟨_, ⟨v, hv, rfl⟩, hv_eq⟩ := hfull.symm.subset hsCt
      have hv_ne1 : v ≠ m₁ 1 := fun he => hne (by rw [← hv_eq, he, hp])
      have hv_ne2 : v ≠ m₂ 1 + k := fun he => hne (by rw [← hv_eq, he, hq])
      have hsF : s ∈ F := (show s ∈ F ∩ bd S from hb ▸ mem_insert _ _).1
      exact hoff v ⟨lt_of_le_of_ne hv.1 (Ne.symm hv_ne1), lt_of_le_of_ne hv.2 hv_ne2⟩ (hv_eq.symm ▸ hsF)
    exact ⟨fun _ => hm2a, fun h => absurd h hne_st⟩

/-- **Same-cuff `w1` parity distinguishes 1-sided vs 2-sided**: when `C_s = C_t = C_st` with gap
path `A₁` from `t` to `s` (avoiding `F` on `(0, 1)`), for a connected cutting `Y` of `F`:
- `C_ξ ≠ C_η` (`F` 2-sided) → `cocInt (w1 AS) (conc2 a A₁) = 0`;
- `C_ξ = C_η` (`F` 1-sided) → `cocInt (w1 AS) (conc2 a A₁) = 1`! -/
theorem cocInt_same_cuff_iff_oneSided [ConnectedSpace Y] [T2Space Y]
    (hY : IsSurface Y) (hS : IsSurface S)
    {ψ : Y → S} {F : Set S} {s t : S} (hne : s ≠ t) (hψ : IsCutting ψ F)
    (hb : F ∩ bd S = {s, t}) (hl : IsLineWithEnds F s t)
    {X X' : Set Y} (hP : LiftPair ψ F s t X X')
    {a : ℝ → S} {ξ η : ℝ → Y} (L : ArcLift ψ F a ξ η)
    (ha0 : a 0 = s) (ha1 : a 1 = t)
    (himξ : ξ '' Icc 0 1 = X) (himη : η '' Icc 0 1 = X')
    (hiξ : InjOn ξ (Icc 0 1)) (hiη : InjOn η (Icc 0 1))
    (AS : SurfAtlas S)
    (hsame : connectedComponentIn (bd S) s = connectedComponentIn (bd S) t)
    {φS : Circle ≃ₜ connectedComponentIn (bd S) s} {u_s u_t : ℝ}
    (hu1 : u_s < u_t) (hu2 : u_t < u_s + 1)
    (hus : (φS (ee u_s)).1 = s) (hut : (φS (ee u_t)).1 = t) :
    let A₁ : ℝ → S := fun u => (φS (ee (lin u_t (u_s + 1) u))).1
    let C_ξ := connectedComponentIn (bd Y) (ξ 0)
    let C_η := connectedComponentIn (bd Y) (η 0)
    (C_ξ ≠ C_η → cocInt (w1 AS) (conc2 a A₁) = 0) ∧
    (C_ξ = C_η → cocInt (w1 AS) (conc2 a A₁) = 1) := by
  intro A₁ C_ξ C_η
  have : CompactSpace Y := hY.1
  have : T2Space S := hS.2.1
  have hF : IsClosed F := hl.isCompact.isClosed
  obtain ⟨AY⟩ := exists_surfAtlas hY
  obtain ⟨_, _, _, _, _, _, hd, hun, -⟩ := id hP
  have hsb : s ∈ bd S := (show s ∈ F ∩ bd S from hb ▸ mem_insert _ _).2
  have hXb : X ⊆ bd Y := fun z hz => hψ.2.2.2.2 (hun ▸ Or.inl hz)
  have hXb' : X' ⊆ bd Y := fun z hz => hψ.2.2.2.2 (hun ▸ Or.inr hz)
  have pX : IsPreconnected X := himξ ▸ isPreconnected_Icc.image _ L.cξ
  have pX' : IsPreconnected X' := himη ▸ isPreconnected_Icc.image _ L.cη
  have hCξ : C_ξ ∈ cuffs Y := ⟨_, hXb (himξ ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩), rfl⟩
  have hCη : C_η ∈ cuffs Y := ⟨_, hXb' (himη ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩), rfl⟩
  have hXC : X ⊆ C_ξ := pX.subset_connectedComponentIn (himξ ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩) hXb
  have hXC' : X' ⊆ C_η := pX'.subset_connectedComponentIn (himη ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩) hXb'
  have hCξ_bd : C_ξ ⊆ bd Y := connectedComponentIn_subset _ _
  have hCη_bd : C_η ⊆ bd Y := connectedComponentIn_subset _ _
  have hA₁_cont : ContinuousOn A₁ (Icc 0 1) :=
    continuous_subtype_val.comp_continuousOn (φS.continuous.comp_continuousOn
      (continuous_ee.comp_continuousOn (continuousOn_lin u_t (u_s + 1))))
  have hA₁0 : A₁ 0 = t := by simp only [A₁, lin_zero]; exact hut
  have hA₁1 : A₁ 1 = s := by simp only [A₁, lin_one, ee_add_one]; exact hus
  have hA₁off : ∀ u ∈ Ioo (0 : ℝ) 1, A₁ u ∉ F := fun u hu hF' => by
    have hv := lin_mem hu2.le hu hu2
    have hbd : A₁ u ∈ bd S := connectedComponentIn_subset _ _ (φS _).2
    have hst : A₁ u ∈ ({s, t} : Set S) := hb ▸ ⟨hF', hbd⟩
    rcases hst with hs' | ht'
    · exact ee_ne (by linarith [hv.1]) hv.2 (φS.injective (Subtype.ext (hus.trans hs'.symm)))
    · exact ee_ne hv.1 (by linarith [hv.2]) (φS.injective (Subtype.ext (hut.trans ht'.symm)))
  -- Lift `A₁` on `(0, 1)` via `cutComplHomeo.symm`, then note its image lies in a unique gap of `C_ξ ∪ C_η`!
  let eF := cutComplHomeo hψ hF
  have hGpart := same_cuff_gaps_partition φS hu1 hu2 hus hut
  have hA₁_in_G₁ : ∀ u ∈ Ioo (0 : ℝ) 1, A₁ u ∈ (fun v => (φS (ee v)).1) '' Ioo u_t (u_s + 1) := fun u hu =>
    ⟨lin u_t (u_s + 1) u, lin_mem hu2.le hu hu2, rfl⟩
  -- For any `x ∈ G₁` (`A₁ (1/2)`), its unique preimage `y₁ ∈ bd Y \ ψ⁻¹(F)` lies in `C_ξ` OR `C_η`!
  have hmid_off : A₁ (1 / 2) ∉ F := hA₁off (1 / 2) ⟨by norm_num, by norm_num⟩
  let y_mid : Y := (eF.symm ⟨A₁ (1 / 2), hmid_off⟩).1
  have hψ_ymid : ψ y_mid = A₁ (1 / 2) := cutComplHomeo_symm_psi hψ hF ⟨A₁ (1 / 2), hmid_off⟩
  have hymid_bd : y_mid ∈ bd Y := bd_lift hψ hF (hψ_ymid.symm ▸ connectedComponentIn_subset _ _ (φS _).2) (hψ_ymid.symm ▸ hmid_off)
  -- Show `y_mid ∈ C_ξ ∪ C_η` (otherwise its cuff `E` would be untouched, so `A₁ (1/2) ∈ ψ '' E` which avoids `s`, contradicting `A₁ (1/2) ∈ C_s`!):
  have hymid_in : y_mid ∈ C_ξ ∨ y_mid ∈ C_η := by
    by_contra hnot
    push Not at hnot
    let E := connectedComponentIn (bd Y) y_mid
    have hE : E ∈ cuffs Y := ⟨y_mid, hymid_bd, rfl⟩
    have hE_ne1 : E ≠ C_ξ := fun he => hnot.1 (he ▸ mem_connectedComponentIn hymid_bd)
    have hE_ne2 : E ≠ C_η := fun he => hnot.2 (he ▸ mem_connectedComponentIn hymid_bd)
    have hEF : Disjoint E (ψ ⁻¹' F) := by
      rw [Set.disjoint_left]; intro z hzE hzF
      rcases (hun.symm ▸ hzF : z ∈ X ∪ X') with hzX | hzX'
      · exact Set.disjoint_left.mp (cuffs_disjoint hE hCξ hE_ne1) hzE (hXC hzX)
      · exact Set.disjoint_left.mp (cuffs_disjoint hE hCη hE_ne2) hzE (hXC' hzX')
    obtain ⟨hψE_cuff, hs_not, -, -⟩ := untouched_cuff_image hY hS hψ hF hb hE hEF
    have hmem : A₁ (1 / 2) ∈ ψ '' E := ⟨y_mid, mem_connectedComponentIn hymid_bd, hψ_ymid⟩
    have hCs_cuff : connectedComponentIn (bd S) s ∈ cuffs S := ⟨s, hsb, rfl⟩
    have heq : ψ '' E = connectedComponentIn (bd S) s := by
      by_contra hne'
      exact Set.disjoint_left.mp (cuffs_disjoint hψE_cuff hCs_cuff hne') hmem (φS _).2
    exact hs_not (heq.symm ▸ mem_connectedComponentIn hsb)
  -- Also note `cocInt (w1 AS) (conc2 a A₁)` is invariant under swapping `(ξ, η)` since `a` is unchanged!
  have hkey_for_cuff : ∀ (ξ₀ η₀ : ℝ → Y) (X₀ X₀' : Set Y) (C₀ C₀' : Set Y),
      LiftPair ψ F s t X₀ X₀' → ArcLift ψ F a ξ₀ η₀ →
      ξ₀ '' Icc 0 1 = X₀ → η₀ '' Icc 0 1 = X₀' → InjOn ξ₀ (Icc 0 1) → InjOn η₀ (Icc 0 1) →
      C₀ = connectedComponentIn (bd Y) (ξ₀ 0) → C₀' = connectedComponentIn (bd Y) (η₀ 0) →
      y_mid ∈ C₀ →
      (C₀ ≠ C₀' → cocInt (w1 AS) (conc2 a A₁) = 0) ∧ (C₀ = C₀' → cocInt (w1 AS) (conc2 a A₁) = 1) := by
    intro ξ₀ η₀ X₀ X₀' C₀ C₀' hP₀ L₀ himξ₀ himη₀ hiξ₀ hiη₀ hC₀eq hC₀'eq hymid₀
    obtain ⟨_, _, _, _, _, _, hd₀, hun₀, -⟩ := id hP₀
    have hX₀b : X₀ ⊆ bd Y := fun z hz => hψ.2.2.2.2 (hun₀ ▸ Or.inl hz)
    have hX₀'b : X₀' ⊆ bd Y := fun z hz => hψ.2.2.2.2 (hun₀ ▸ Or.inr hz)
    have hC₀_cuff : C₀ ∈ cuffs Y := hC₀eq ▸ ⟨_, hX₀b (himξ₀ ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩), rfl⟩
    have hC₀_bd : C₀ ⊆ bd Y := hC₀eq ▸ connectedComponentIn_subset _ _
    have hX₀C : X₀ ⊆ C₀ := hC₀eq ▸ (himξ₀ ▸ isPreconnected_Icc.image _ L₀.cξ).subset_connectedComponentIn
      (himξ₀ ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩) hX₀b
    have hX₀'C : X₀' ⊆ C₀' := hC₀'eq ▸ (himη₀ ▸ isPreconnected_Icc.image _ L₀.cη).subset_connectedComponentIn
      (himη₀ ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩) hX₀'b
    obtain ⟨φ₀⟩ := (cuff_statement.{u} Y hY).2.2 _ hC₀_cuff
    obtain ⟨m₁₀, hm₁₀c, hm₁₀e⟩ := exists_lift φ₀ L₀.cξ (fun u hu => hX₀C (himξ₀ ▸ ⟨u, hu, rfl⟩))
    -- Flip `φ₀` if needed so `m₁₀` is `StrictMonoOn`:
    have hex_pos_φ : ∃ (φ : Circle ≃ₜ C₀) (m₁ : ℝ → ℝ), ContinuousOn m₁ (Icc 0 1) ∧ StrictMonoOn m₁ (Icc 0 1) ∧
        ∀ u ∈ Icc (0 : ℝ) 1, (φ (ee (m₁ u))).1 = ξ₀ u := by
      rcases lift_mono hm₁₀c (inj_of_lift hm₁₀e hiξ₀) with hsm | hsa
      · exact ⟨φ₀, m₁₀, hm₁₀c, hsm, hm₁₀e⟩
      · refine ⟨(Homeomorph.inv Circle).trans φ₀, fun u => -m₁₀ u, hm₁₀c.neg,
          fun a ha b hb h => neg_lt_neg (hsa ha hb h), fun u hu => ?_⟩
        simp only [Homeomorph.trans_apply]
        change (φ₀ (ee (-m₁₀ u))⁻¹).1 = ξ₀ u
        have : (ee (-m₁₀ u))⁻¹ = ee (m₁₀ u) := by
          unfold ee; rw [mul_neg, Circle.exp_neg, inv_inv]
        rw [this]; exact hm₁₀e u hu
    obtain ⟨φ, m₁, hm₁c, hm₁m, hm₁ξ⟩ := hex_pos_φ
    have hlt1 : m₁ 1 < m₁ 0 + 1 := lift_lt_add_one hm₁c hm₁m (inj_of_lift hm₁ξ hiξ₀)
    have h01 : m₁ 0 < m₁ 1 := hm₁m ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one
    -- Helper: for any open gap `(p, q)` with `p < q`, `q - p < 1`, avoiding `ψ ⁻¹' F`, `φ (ee p)` over `t`, `φ (ee q)` over `s`, and containing `y_mid`,
    -- we get `γ_gap : [0, 1] → C₀` lifting `A₁` from `φ (ee p)` to `φ (ee q)`.
    have hgap_lift : ∀ {p q : ℝ}, p < q → q - p < 1 →
        (∀ v ∈ Ioo p q, ψ (φ (ee v)).1 ∉ F) →
        ψ (φ (ee p)).1 = t → ψ (φ (ee q)).1 = s →
        (∃ v_m ∈ Ioo p q, (φ (ee v_m)).1 = y_mid) →
        ∃ γ_gap : ℝ → Y, ContinuousOn γ_gap (Icc 0 1) ∧ (∀ u ∈ Icc (0 : ℝ) 1, γ_gap u ∈ C₀) ∧
          (∀ u ∈ Icc (0 : ℝ) 1, ψ (γ_gap u) = A₁ u) ∧ γ_gap 0 = (φ (ee p)).1 ∧ γ_gap 1 = (φ (ee q)).1 := by
      intro p q hpq hspan hgoff hpt hqs ⟨v_m, hvm_in, hvm_y⟩
      have hgap_c : ContinuousOn (fun v => ψ (φ (ee v)).1) (Icc p q) :=
        hψ.1.comp_continuousOn (continuous_subtype_val.comp (φ.continuous.comp continuous_ee)).continuousOn
      have hgap_CS : ∀ v ∈ Icc p q, ψ (φ (ee v)).1 ∈ connectedComponentIn (bd S) s := fun v hv => by
        rcases eq_or_lt_of_le hv.1 with rfl | h1
        · rw [hpt, hsame]; exact mem_connectedComponentIn (show t ∈ bd S from (show t ∈ F ∩ bd S from hb ▸ mem_insert_of_mem _ rfl).2)
        · rcases eq_or_lt_of_le hv.2 with rfl | h2
          · rw [hqs]; exact mem_connectedComponentIn hsb
          · have hsub := (isPreconnected_Icc.image (fun w => ψ (φ (ee w)).1) hgap_c).subset_connectedComponentIn
              ⟨q, ⟨hpq.le, le_rfl⟩, hqs⟩ (by
                rintro _ ⟨w, hw, rfl⟩
                dsimp only
                rcases eq_or_lt_of_le hw.1 with rfl | h1'
                · rw [hpt]; exact (show t ∈ F ∩ bd S from hb ▸ mem_insert_of_mem _ rfl).2
                · rcases eq_or_lt_of_le hw.2 with rfl | h2'
                  · rw [hqs]; exact hsb
                  · exact (mem_bd_cut_iff hY hS hψ hF (hgoff w ⟨h1', h2'⟩)).mp (hC₀_bd (φ _).2))
            exact hsub ⟨v, hv, rfl⟩
      obtain ⟨l, hlc, hle⟩ := exists_lift φS (hgap_c.comp (continuousOn_lin p q)
        fun w hw => ⟨by simp only [lin]; nlinarith [hw.1, hpq], by simp only [lin]; nlinarith [hw.2, hpq]⟩)
        (fun w hw => hgap_CS _ ⟨by simp only [lin]; nlinarith [hw.1, hpq], by simp only [lin]; nlinarith [hw.2, hpq]⟩)
      let toW : ℝ → ℝ := fun x => (x - p) / (q - p)
      have hlin_toW : ∀ x, lin p q (toW x) = x := fun x => by simp only [lin, toW]; field_simp [show q - p ≠ 0 by linarith]; ring
      have htoW_mem : ∀ x ∈ Ioo p q, toW x ∈ Ioo (0 : ℝ) 1 := fun x hx =>
        ⟨div_pos (by linarith [hx.1]) (by linarith), (div_lt_one (by linarith)).mpr (by linarith [hx.2])⟩
      have hl_no_st : ∀ w ∈ Ioo (0 : ℝ) 1, ee (l w) ≠ ee u_s ∧ ee (l w) ≠ ee u_t := fun w hw => by
        have hlv : (φS (ee (l w))).1 = ψ (φ (ee (lin p q w))).1 := hle w (Ioo_subset_Icc_self hw)
        have hoffw := hgoff _ (lin_mem hpq.le hw hpq)
        refine ⟨fun h => hoffw ?_, fun h => hoffw ?_⟩
        · rw [← hlv, h, hus]; exact (show s ∈ F ∩ bd S from hb ▸ mem_insert _ _).1
        · rw [← hlv, h, hut]; exact (show t ∈ F ∩ bd S from hb ▸ mem_insert_of_mem _ rfl).1
      have hvm_e : ee (l (toW v_m)) = ee (lin u_t (u_s + 1) (1 / 2)) := by
        apply φS.injective; apply Subtype.ext
        have h1 : (φS (ee (l (toW v_m)))).1 = ψ (φ (ee (lin p q (toW v_m)))).1 :=
          hle _ (Ioo_subset_Icc_self (htoW_mem v_m hvm_in))
        rw [h1, hlin_toW, hvm_y, hψ_ymid]
      obtain ⟨k', hk'⟩ := ee_eq_iff.mp hvm_e
      have hlm_in : l (toW v_m) ∈ Ioo (u_t + k') (u_s + 1 + k') := by
        have h12 := lin_mem hu2.le (show (1 / 2 : ℝ) ∈ Ioo 0 1 by norm_num) hu2
        constructor <;> linarith [h12.1, h12.2, hk']
      have hgap_sub_G₁ : ∀ v ∈ Ioo p q, ψ (φ (ee v)).1 ∈ (fun w => (φS (ee w)).1) '' Ioo u_t (u_s + 1) := fun v hv => by
        have hwm := htoW_mem v_m hvm_in
        have hwv := htoW_mem v hv
        have hlv_in : l (toW v) ∈ Ioo (u_t + k') (u_s + 1 + k') := by
          constructor
          · by_contra hle'
            have hmem : u_t + k' ∈ Icc (l (toW v)) (l (toW v_m)) := ⟨not_lt.mp hle', hlm_in.1.le⟩
            rcases le_total (toW v) (toW v_m) with hord | hord
            · obtain ⟨w, hw, hweq⟩ := intermediate_value_Icc hord (hlc.mono fun x hx => ⟨by linarith [hx.1, hwv.1], by linarith [hx.2, hwm.2]⟩) hmem
              exact (hl_no_st w ⟨by linarith [hw.1, hwv.1], by linarith [hw.2, hwm.2]⟩).2 (by rw [hweq]; exact ee_eq_iff.mpr ⟨k', rfl⟩)
            · obtain ⟨w, hw, hweq⟩ := intermediate_value_Icc' hord (hlc.mono fun x hx => ⟨by linarith [hx.1, hwm.1], by linarith [hx.2, hwv.2]⟩) hmem
              exact (hl_no_st w ⟨by linarith [hw.1, hwm.1], by linarith [hw.2, hwv.2]⟩).2 (by rw [hweq]; exact ee_eq_iff.mpr ⟨k', rfl⟩)
          · by_contra hge'
            have hmem : u_s + 1 + k' ∈ Icc (l (toW v_m)) (l (toW v)) := ⟨hlm_in.2.le, not_lt.mp hge'⟩
            rcases le_total (toW v_m) (toW v) with hord | hord
            · obtain ⟨w, hw, hweq⟩ := intermediate_value_Icc hord (hlc.mono fun x hx => ⟨by linarith [hx.1, hwm.1], by linarith [hx.2, hwv.2]⟩) hmem
              exact (hl_no_st w ⟨by linarith [hw.1, hwm.1], by linarith [hw.2, hwv.2]⟩).1 (by rw [hweq]; exact ee_eq_iff.mpr ⟨k' + 1, by push_cast; ring⟩)
            · obtain ⟨w, hw, hweq⟩ := intermediate_value_Icc' hord (hlc.mono fun x hx => ⟨by linarith [hx.1, hwv.1], by linarith [hx.2, hwm.2]⟩) hmem
              exact (hl_no_st w ⟨by linarith [hw.1, hwv.1], by linarith [hw.2, hwm.2]⟩).1 (by rw [hweq]; exact ee_eq_iff.mpr ⟨k' + 1, by push_cast; ring⟩)
        refine ⟨l (toW v) - k', ⟨by linarith [hlv_in.1], by linarith [hlv_in.2]⟩, ?_⟩
        have hee : ee (l (toW v) - k') = ee (l (toW v)) := ee_eq_iff.mpr ⟨-k', by push_cast; ring⟩
        have h1 : (φS (ee (l (toW v)))).1 = ψ (φ (ee (lin p q (toW v)))).1 :=
          hle _ (Ioo_subset_Icc_self (htoW_mem v hv))
        dsimp only; rw [hee, h1, hlin_toW]
      have hgap_inj : InjOn (fun v => ψ (φ (ee v)).1) (Icc p q) := fun v₁ hv₁ v₂ hv₂ he => by
        dsimp only at he
        by_cases h1p : v₁ = p
        · subst v₁; by_cases h2p : v₂ = p
          · exact h2p.symm
          · exfalso; rcases eq_or_lt_of_le hv₂.2 with rfl | h2lt
            · exact hne (hqs.symm.trans (he.symm.trans hpt))
            · exact hgoff v₂ ⟨lt_of_le_of_ne hv₂.1 (Ne.symm h2p), h2lt⟩
                (by rw [← he, hpt]; exact (show t ∈ F ∩ bd S from hb ▸ mem_insert_of_mem _ rfl).1)
        · by_cases h1q : v₁ = q
          · subst v₁; by_cases h2q : v₂ = q
            · exact h2q.symm
            · exfalso; rcases eq_or_lt_of_le hv₂.1 with rfl | h2gt
              · exact hne (hqs.symm.trans (he.trans hpt))
              · exact hgoff v₂ ⟨h2gt, lt_of_le_of_ne hv₂.2 h2q⟩
                  (by rw [← he, hqs]; exact (show s ∈ F ∩ bd S from hb ▸ mem_insert _ _).1)
          · have hv1I : v₁ ∈ Ioo p q := ⟨lt_of_le_of_ne hv₁.1 (Ne.symm h1p), lt_of_le_of_ne hv₁.2 h1q⟩
            have hv2_off : ψ (φ (ee v₂)).1 ∉ F := by rw [← he]; exact hgoff v₁ hv1I
            have heY := hψ.2.2.1 (hgoff v₁ hv1I) hv2_off he
            have hee := φ.injective (Subtype.ext heY)
            obtain ⟨k'', hk''⟩ := ee_eq_iff.mp hee
            have hklt : |(k'' : ℝ)| < 1 := by rw [abs_lt]; exact ⟨by linarith [hv₁.1, hv₂.2], by linarith [hv₁.2, hv₂.1]⟩
            have hk0 : k'' = 0 := by have := abs_lt.mp (show |k''| < 1 by exact_mod_cast hklt); omega
            subst hk0; simp only [Int.cast_zero, add_zero] at hk''; exact hk''
      have him_A₁ : (fun v => ψ (φ (ee v)).1) '' Icc p q = A₁ '' Icc 0 1 := by
        have hsub : (fun v => ψ (φ (ee v)).1) '' Icc p q ⊆ A₁ '' Icc 0 1 := by
          rintro _ ⟨v, hv, rfl⟩
          dsimp only
          rcases eq_or_lt_of_le hv.1 with rfl | h1
          · exact ⟨0, ⟨le_rfl, zero_le_one⟩, hA₁0.trans hpt.symm⟩
          · rcases eq_or_lt_of_le hv.2 with rfl | h2
            · exact ⟨1, ⟨zero_le_one, le_rfl⟩, hA₁1.trans hqs.symm⟩
            · obtain ⟨w, hw, hwe⟩ := hgap_sub_G₁ v ⟨h1, h2⟩
              refine ⟨(w - u_t) / (u_s + 1 - u_t), ⟨div_nonneg (by linarith [hw.1]) (by linarith),
                (div_le_one (by linarith)).mpr (by linarith [hw.2])⟩, ?_⟩
              dsimp only [A₁, lin]
              rw [show u_t + (u_s + 1 - u_t) * ((w - u_t) / (u_s + 1 - u_t)) = w by field_simp [show u_s + 1 - u_t ≠ 0 by linarith]; ring]
              exact hwe
        refine subset_antisymm hsub ?_
        rintro _ ⟨u, hu, rfl⟩
        have hA₁_inj : InjOn A₁ (Icc 0 1) := fun a ha b hb he => by
          have hee := φS.injective (Subtype.ext he)
          obtain ⟨k'', hk''⟩ := ee_eq_iff.mp hee
          have hla : lin u_t (u_s + 1) a ∈ Icc u_t (u_s + 1) := ⟨by simp only [lin]; nlinarith [ha.1, hu2], by simp only [lin]; nlinarith [ha.2, hu2]⟩
          have hlb : lin u_t (u_s + 1) b ∈ Icc u_t (u_s + 1) := ⟨by simp only [lin]; nlinarith [hb.1, hu2], by simp only [lin]; nlinarith [hb.2, hu2]⟩
          have hklt : |(k'' : ℝ)| < 1 := by rw [abs_lt]; exact ⟨by linarith [hla.1, hlb.2, hu1], by linarith [hla.2, hlb.1, hu1]⟩
          have hk0 : k'' = 0 := by have := abs_lt.mp (show |k''| < 1 by exact_mod_cast hklt); omega
          subst hk0; simp only [Int.cast_zero, add_zero] at hk''
          exact (strictMonoOn_lin hu2).injOn ha hb hk''
        obtain ⟨A₁_inv, hA₁i_c, hA₁i_l⟩ := exists_inv_of_compactOn isCompact_Icc hA₁_cont hA₁_inj
        have hcomp_c : ContinuousOn (fun v => A₁_inv (ψ (φ (ee v)).1)) (Icc p q) :=
          hA₁i_c.comp hgap_c fun v hv => hsub ⟨v, hv, rfl⟩
        have h0v : A₁_inv (ψ (φ (ee p)).1) = 0 := by rw [hpt, ← hA₁0]; exact hA₁i_l ⟨le_rfl, zero_le_one⟩
        have h1v : A₁_inv (ψ (φ (ee q)).1) = 1 := by rw [hqs, ← hA₁1]; exact hA₁i_l ⟨zero_le_one, le_rfl⟩
        obtain ⟨v, hv, hveq⟩ := intermediate_value_Icc hpq.le hcomp_c (show u ∈ Icc _ _ by rw [h0v, h1v]; exact hu)
        refine ⟨v, hv, ?_⟩
        obtain ⟨u', hu', hu'eq⟩ := hsub ⟨v, hv, rfl⟩
        dsimp only at hveq hu'eq
        have : u' = u := by rw [← hveq, ← hu'eq, hA₁i_l hu']
        rw [← this, hu'eq]
      obtain ⟨ginv, hginv_c, hginv_l⟩ := exists_inv_of_compactOn isCompact_Icc hgap_c hgap_inj
      let γ_gap : ℝ → Y := fun u => (φ (ee (ginv (A₁ u)))).1
      have hginv_mem : ∀ u ∈ Icc (0 : ℝ) 1, ginv (A₁ u) ∈ Icc p q ∧ ψ (φ (ee (ginv (A₁ u)))).1 = A₁ u := fun u hu => by
        obtain ⟨v, hv, hveq⟩ := him_A₁.symm.subset ⟨u, hu, rfl⟩
        dsimp only at hveq
        exact ⟨by rw [← hveq, hginv_l hv]; exact hv, by rw [← hveq, hginv_l hv, hveq]⟩
      refine ⟨γ_gap, continuous_subtype_val.comp_continuousOn (φ.continuous.comp_continuousOn
        (continuous_ee.comp_continuousOn (hginv_c.comp hA₁_cont fun u hu => him_A₁.symm ▸ ⟨u, hu, rfl⟩))),
        fun _ _ => (φ _).2, fun u hu => (hginv_mem u hu).2, ?_, ?_⟩
      · have h2 := hgap_inj (hginv_mem 0 ⟨le_rfl, zero_le_one⟩).1 ⟨le_rfl, hpq.le⟩ ((hginv_mem 0 ⟨le_rfl, zero_le_one⟩).2.trans (hA₁0.trans hpt.symm))
        simp only [γ_gap, h2]
      · have h2 := hgap_inj (hginv_mem 1 ⟨zero_le_one, le_rfl⟩).1 ⟨hpq.le, le_rfl⟩ ((hginv_mem 1 ⟨zero_le_one, le_rfl⟩).2.trans (hA₁1.trans hqs.symm))
        simp only [γ_gap, h2]
    constructor
    · -- `C₀ ≠ C₀'` (2-sided): `C₀ \ X₀` is the single open gap `(m₁ 1, m₁ 0 + 1)`, which lifts `A₁`!
      intro hneC
      have hdis0 := cuffs_disjoint hC₀_cuff (hC₀'eq ▸ ⟨_, hX₀'b (himη₀ ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩), rfl⟩) hneC
      have hgap_off : ∀ v ∈ Ioo (m₁ 1) (m₁ 0 + 1), ψ (φ (ee v)).1 ∉ F := fun v hv hF' => by
        rcases (hun₀.symm ▸ hF' : (φ (ee v)).1 ∈ X₀ ∪ X₀') with hx | hx'
        · obtain ⟨u, hu, hu'⟩ := himξ₀.symm.subset hx
          have h1 := φ.injective (Subtype.ext ((hm₁ξ u hu).trans hu'))
          have hlo := hm₁m.monotoneOn ⟨le_rfl, zero_le_one⟩ hu hu.1
          have hhi := hm₁m.monotoneOn hu ⟨zero_le_one, le_rfl⟩ hu.2
          exact ee_ne (by linarith [hv.1]) (by linarith [hv.2]) h1
        · exact Set.disjoint_left.mp hdis0 (φ _).2 (hX₀'C hx')
      obtain ⟨r_m, -, hrm_eq⟩ := exists_param (φ.symm ⟨y_mid, hymid₀⟩)
      set v_m := m₁ 0 + Int.fract (r_m - m₁ 0)
      have hvm_ee : ee v_m = ee r_m := ee_eq_iff.mpr ⟨-⌊r_m - m₁ 0⌋, by simp only [v_m, Int.cast_neg]; linarith [Int.floor_add_fract (r_m - m₁ 0)]⟩
      have hvm_y : (φ (ee v_m)).1 = y_mid := by rw [hvm_ee, hrm_eq]; simp
      have hvm_in : v_m ∈ Ioo (m₁ 1) (m₁ 0 + 1) := by
        have hlo : m₁ 0 ≤ v_m := by simp only [v_m]; linarith [Int.fract_nonneg (r_m - m₁ 0)]
        have hhi : v_m < m₁ 0 + 1 := by simp only [v_m]; linarith [Int.fract_lt_one (r_m - m₁ 0)]
        refine ⟨?_, hhi⟩
        by_contra hle
        obtain ⟨u, hu, hueq⟩ := intermediate_value_Icc zero_le_one hm₁c ⟨hlo, not_lt.mp hle⟩
        have : y_mid = ξ₀ u := by rw [← hvm_y, ← hueq, hm₁ξ u hu]
        exact hmid_off (by rw [← hψ_ymid, this]; exact show ξ₀ u ∈ ψ ⁻¹' F from hun₀ ▸ Or.inl (himξ₀ ▸ ⟨u, hu, rfl⟩))
      obtain ⟨γ_gap, hgc, hgC, hgψ, hg0, hg1⟩ := hgap_lift hlt1 (by linarith) hgap_off
        (by rw [hm₁ξ 1 ⟨zero_le_one, le_rfl⟩, L₀.hξ 1 ⟨zero_le_one, le_rfl⟩, ha1])
        (by rw [ee_add_one, hm₁ξ 0 ⟨le_rfl, zero_le_one⟩, L₀.hξ 0 ⟨le_rfl, zero_le_one⟩, ha0])
        ⟨v_m, hvm_in, hvm_y⟩
      rw [hm₁ξ 1 ⟨zero_le_one, le_rfl⟩] at hg0
      rw [ee_add_one, hm₁ξ 0 ⟨le_rfl, zero_le_one⟩] at hg1
      exact (cocInt_loop_same_cuff hY hS hψ hF hb hP₀ L₀ ha0 ha1 himξ₀ himη₀ hiξ₀ hiη₀ AY AS
        hA₁_cont hA₁0 hA₁1 hA₁off hC₀_bd φ hm₁c hm₁ξ hm₁m hgc hgC hgψ hg0).1 hg1
    · -- `C₀ = C₀'` (1-sided): `ξ₀` and `η₀` run in the SAME direction on `C₀`, and one of the two gaps `(m₁ 1, m₂ 0)` or `(m₂ 1, m₁ 0 + 1)` lifts `A₁`!
      intro heqC
      obtain ⟨m₂₀, hm₂₀c, hm₂₀e⟩ := exists_lift φ L₀.cη (fun u hu => heqC ▸ hX₀'C (himη₀ ▸ ⟨u, hu, rfl⟩))
      have hm₂₀m : StrictMonoOn m₂₀ (Icc 0 1) :=
        (cut_single_cuff_dirs hY hS hne hψ hF hb hP₀ L₀ ha0 ha1 himξ₀ himη₀ hiξ₀ hiη₀ hC₀_cuff φ hm₁c hm₁m hm₁ξ hm₂₀c hm₂₀e).2 hsame
      have hdj₀ : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1, ξ₀ u ≠ η₀ v := fun u hu v hv he => by
        have h1 : ξ₀ u ∈ X₀ := himξ₀ ▸ ⟨u, hu, rfl⟩
        have h2 : ξ₀ u ∈ X₀' := he ▸ (show η₀ v ∈ X₀' from himη₀ ▸ ⟨v, hv, rfl⟩)
        exact Set.disjoint_left.mp hd₀ h1 h2
      obtain ⟨k, hk_e, hord⟩ := exists_two_lifts_order φ hm₁c hm₁m hm₁ξ hm₂₀c (.inl hm₂₀m) hm₂₀e hiξ₀ hiη₀ hdj₀
      have hord' : m₁ 0 < m₁ 1 ∧ m₁ 1 < m₂₀ 0 + k ∧ m₂₀ 0 + k < m₂₀ 1 + k ∧ m₂₀ 1 + k < m₁ 0 + 1 := by
        rcases hord with ⟨-, h⟩ | ⟨ha, -⟩
        · exact h
        · exact absurd (ha ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one)
            (not_lt.mpr (hm₂₀m ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one).le)
      let m₂ : ℝ → ℝ := fun u => m₂₀ u + k
      have hm₂c : ContinuousOn m₂ (Icc 0 1) := hm₂₀c.add continuousOn_const
      have hm₂m : StrictMonoOn m₂ (Icc 0 1) := fun a ha b hb h => by dsimp only [m₂]; linarith [hm₂₀m ha hb h]
      have hm₂η : ∀ u ∈ Icc (0 : ℝ) 1, (φ (ee (m₂ u))).1 = η₀ u := hk_e
      -- Find `v_m ∈ Ioo (m₁ 1) (m₂ 0) ∪ Ioo (m₂ 1) (m₁ 0 + 1)` with `(φ (ee v_m)).1 = y_mid`:
      obtain ⟨r_m, -, hrm_eq⟩ := exists_param (φ.symm ⟨y_mid, hymid₀⟩)
      set v_m := m₁ 0 + Int.fract (r_m - m₁ 0)
      have hvm_ee : ee v_m = ee r_m := ee_eq_iff.mpr ⟨-⌊r_m - m₁ 0⌋, by simp only [v_m, Int.cast_neg]; linarith [Int.floor_add_fract (r_m - m₁ 0)]⟩
      have hvm_y : (φ (ee v_m)).1 = y_mid := by rw [hvm_ee, hrm_eq]; simp
      have hvm_lo : m₁ 0 ≤ v_m := by simp only [v_m]; linarith [Int.fract_nonneg (r_m - m₁ 0)]
      have hvm_hi : v_m < m₁ 0 + 1 := by simp only [v_m]; linarith [Int.fract_lt_one (r_m - m₁ 0)]
      have hvm_gt1 : m₁ 1 < v_m := by
        by_contra hle
        obtain ⟨u, hu, hueq⟩ := intermediate_value_Icc zero_le_one hm₁c ⟨hvm_lo, not_lt.mp hle⟩
        have : y_mid = ξ₀ u := by rw [← hvm_y, ← hueq, hm₁ξ u hu]
        exact hmid_off (by rw [← hψ_ymid, this]; exact show ξ₀ u ∈ ψ ⁻¹' F from hun₀ ▸ Or.inl (himξ₀ ▸ ⟨u, hu, rfl⟩))
      have hvm_not2 : v_m ∉ Icc (m₂ 0) (m₂ 1) := fun hmem => by
        obtain ⟨u, hu, hueq⟩ := intermediate_value_Icc zero_le_one hm₂c hmem
        have : y_mid = η₀ u := by rw [← hvm_y, ← hueq, hm₂η u hu]
        exact hmid_off (by rw [← hψ_ymid, this]; exact show η₀ u ∈ ψ ⁻¹' F from hun₀ ▸ Or.inr (himη₀ ▸ ⟨u, hu, rfl⟩))
      by_cases hvm_g1 : v_m < m₂ 0
      · -- Gap 1: `(m₁ 1, m₂ 0)` from `ξ₀ 1` to `η₀ 0`!
        have hgoff : ∀ v ∈ Ioo (m₁ 1) (m₂ 0), ψ (φ (ee v)).1 ∉ F := fun v hv hF' => by
          rcases (hun₀.symm ▸ hF' : (φ (ee v)).1 ∈ X₀ ∪ X₀') with hx | hx'
          · obtain ⟨u, hu, hu'⟩ := himξ₀.symm.subset hx
            have h1 := φ.injective (Subtype.ext ((hm₁ξ u hu).trans hu'))
            exact ee_ne (by linarith [hv.1, hm₁m.monotoneOn hu ⟨zero_le_one, le_rfl⟩ hu.2])
              (by linarith [hv.2, hm₁m.monotoneOn ⟨le_rfl, zero_le_one⟩ hu hu.1, hord'.2.2.1, hord'.2.2.2]) h1
          · obtain ⟨u, hu, hu'⟩ := himη₀.symm.subset hx'
            have h1 := φ.injective (Subtype.ext ((hm₂η u hu).trans hu'))
            exact ee_ne (by linarith [hv.2, hm₂m.monotoneOn ⟨le_rfl, zero_le_one⟩ hu hu.1])
              (by linarith [hv.1, hm₂m.monotoneOn hu ⟨zero_le_one, le_rfl⟩ hu.2, hord'.1, hord'.2.2.2]) h1.symm
        obtain ⟨γ_gap, hgc, hgC, hgψ, hg0, hg1⟩ := hgap_lift hord'.2.1 (by linarith [hord'.1, hord'.2.2.1, hord'.2.2.2])
          hgoff (by rw [hm₁ξ 1 ⟨zero_le_one, le_rfl⟩, L₀.hξ 1 ⟨zero_le_one, le_rfl⟩, ha1])
          (by rw [hm₂η 0 ⟨le_rfl, zero_le_one⟩, L₀.hη 0 ⟨le_rfl, zero_le_one⟩, ha0]) ⟨v_m, ⟨hvm_gt1, hvm_g1⟩, hvm_y⟩
        rw [hm₁ξ 1 ⟨zero_le_one, le_rfl⟩] at hg0
        rw [hm₂η 0 ⟨le_rfl, zero_le_one⟩] at hg1
        exact (cocInt_loop_same_cuff hY hS hψ hF hb hP₀ L₀ ha0 ha1 himξ₀ himη₀ hiξ₀ hiη₀ AY AS
          hA₁_cont hA₁0 hA₁1 hA₁off hC₀_bd φ hm₁c hm₁ξ hm₁m hgc hgC hgψ hg0).2 hg1 ⟨m₂, hm₂c, hm₂m, hm₂η⟩
      · -- Gap 2: `(m₂ 1, m₁ 0 + 1)` from `η₀ 1` to `ξ₀ 0`! Apply `cocInt_loop_same_cuff` with `(η₀, ξ₀)` swapped!
        have hvm_gt2 : m₂ 1 < v_m := lt_of_not_ge fun hle => hvm_not2 ⟨not_lt.mp hvm_g1, hle⟩
        have hgoff : ∀ v ∈ Ioo (m₂ 1) (m₁ 0 + 1), ψ (φ (ee v)).1 ∉ F := fun v hv hF' => by
          rcases (hun₀.symm ▸ hF' : (φ (ee v)).1 ∈ X₀ ∪ X₀') with hx | hx'
          · obtain ⟨u, hu, hu'⟩ := himξ₀.symm.subset hx
            have h1 := φ.injective (Subtype.ext ((hm₁ξ u hu).trans hu'))
            exact ee_ne (by linarith [hv.1, hm₁m.monotoneOn hu ⟨zero_le_one, le_rfl⟩ hu.2, hord'.2.1, hord'.2.2.1])
              (by linarith [hv.2, hm₁m.monotoneOn ⟨le_rfl, zero_le_one⟩ hu hu.1]) h1
          · obtain ⟨u, hu, hu'⟩ := himη₀.symm.subset hx'
            have h1 := φ.injective (Subtype.ext ((hm₂η u hu).trans hu'))
            exact ee_ne (by linarith [hv.1, hm₂m.monotoneOn hu ⟨zero_le_one, le_rfl⟩ hu.2])
              (by linarith [hv.2, hm₂m.monotoneOn ⟨le_rfl, zero_le_one⟩ hu hu.1, hord'.1, hord'.2.1]) h1
        obtain ⟨γ_gap, hgc, hgC, hgψ, hg0, hg1⟩ := hgap_lift hord'.2.2.2 (by linarith [hord'.1, hord'.2.1, hord'.2.2.1])
          hgoff (by rw [hm₂η 1 ⟨zero_le_one, le_rfl⟩, L₀.hη 1 ⟨zero_le_one, le_rfl⟩, ha1])
          (by rw [ee_add_one, hm₁ξ 0 ⟨le_rfl, zero_le_one⟩, L₀.hξ 0 ⟨le_rfl, zero_le_one⟩, ha0]) ⟨v_m, ⟨hvm_gt2, hvm_hi⟩, hvm_y⟩
        rw [hm₂η 1 ⟨zero_le_one, le_rfl⟩] at hg0
        rw [ee_add_one, hm₁ξ 0 ⟨le_rfl, zero_le_one⟩] at hg1
        have hP_sw : LiftPair ψ F s t X₀' X₀ := by
          obtain ⟨x0, x1, y0, y1, l1, l2, hd', hun', b1, b2, h7, h8, h9, h10⟩ := id hP₀
          exact ⟨y0, y1, x0, x1, l2, l1, hd'.symm, by rw [union_comm]; exact hun', b2, b1, h8, h7, h10, h9⟩
        have L_sw : ArcLift ψ F a η₀ ξ₀ :=
          ⟨L₀.cη, L₀.cξ, L₀.hη, L₀.hξ, L₀.img, fun y₁ y₂ h1 h2 => (L₀.fib y₁ y₂ h1 h2).imp fun u ⟨hu, h⟩ =>
            ⟨hu, h.elim (fun ⟨ha, hb⟩ => .inr ⟨hb, ha⟩) (fun ⟨ha, hb⟩ => .inl ⟨hb, ha⟩)⟩⟩
        exact (cocInt_loop_same_cuff hY hS hψ hF hb hP_sw L_sw ha0 ha1 himη₀ himξ₀ hiη₀ hiξ₀ AY AS
          hA₁_cont hA₁0 hA₁1 hA₁off hC₀_bd φ hm₂c hm₂η hm₂m hgc hgC hgψ hg0).2 hg1 ⟨m₁, hm₁c, hm₁m, hm₁ξ⟩
  rcases hymid_in with h1 | h2
  · exact hkey_for_cuff ξ η X X' C_ξ C_η hP L himξ himη hiξ hiη rfl rfl h1
  · have hP_sw : LiftPair ψ F s t X' X := by
      obtain ⟨x0, x1, y0, y1, l1, l2, hd', hun', b1, b2, h7, h8, h9, h10⟩ := id hP
      exact ⟨y0, y1, x0, x1, l2, l1, hd'.symm, by rw [union_comm]; exact hun', b2, b1, h8, h7, h10, h9⟩
    have L_sw : ArcLift ψ F a η ξ :=
      ⟨L.cη, L.cξ, L.hη, L.hξ, L.img, fun y₁ y₂ h1 h2 => (L.fib y₁ y₂ h1 h2).imp fun u ⟨hu, h⟩ =>
        ⟨hu, h.elim (fun ⟨ha, hb⟩ => .inr ⟨hb, ha⟩) (fun ⟨ha, hb⟩ => .inl ⟨hb, ha⟩)⟩⟩
    have hres := hkey_for_cuff η ξ X' X C_η C_ξ hP_sw L_sw himη himξ hiη hiξ rfl rfl h2
    exact ⟨fun h => hres.1 h.symm, fun h => hres.2 h.symm⟩

/-- **Equal cocycles ⇒ same cut type and homeomorphic cut surfaces**:
Given connected `S`, non-separating proper `I`-arc `F` (`ConnectedSpace Y`), and proper `I`-arc `F'`
with the same endpoints `s ≠ t`, `BdCohRel s t (arcCocycle F') (arcCocycle F)`, and
`cocInt (w1 AS) a' = cocInt (w1 AS) a`, then:
1. `ConnectedSpace Y'`;
2. `C_ξ = C_η ↔ C_ξ' = C_η'`;
3. `∃ a₀ b₀ c₀, Nonempty (Y ≃ₜ SurfaceModel a₀ b₀ c₀) ∧ Nonempty (Y' ≃ₜ SurfaceModel a₀ b₀ c₀)`. -/
theorem same_cut_model_of_cocycle_eq [ConnectedSpace S] (hS : IsSurface S)
    {F F' : Set S} {s t : S} (hne : s ≠ t)
    (hb : F ∩ bd S = {s, t}) (hb' : F' ∩ bd S = {s, t})
    (hl : IsLineWithEnds F s t) (hl' : IsLineWithEnds F' s t)
    {Y Y' : Type u} [TopologicalSpace Y] [T2Space Y] [TopologicalSpace Y'] [T2Space Y']
    {ψ : Y → S} {ψ' : Y' → S} (hY : IsSurface Y) (hY' : IsSurface Y')
    (hψ : IsCutting ψ F) (hψ' : IsCutting ψ' F')
    {X X' : Set Y} {X₂ X₂' : Set Y'}
    (hP : LiftPair ψ F s t X X') (hP' : LiftPair ψ' F' s t X₂ X₂')
    {a a' : ℝ → S} {ξ η : ℝ → Y} {ξ' η' : ℝ → Y'}
    (L : ArcLift ψ F a ξ η) (L' : ArcLift ψ' F' a' ξ' η')
    (ha0 : a 0 = s) (ha1 : a 1 = t) (ha'0 : a' 0 = s) (ha'1 : a' 1 = t)
    (himξ : ξ '' Icc 0 1 = X) (himη : η '' Icc 0 1 = X')
    (himξ' : ξ' '' Icc 0 1 = X₂) (himη' : η' '' Icc 0 1 = X₂')
    (hiξ : InjOn ξ (Icc 0 1)) (hiη : InjOn η (Icc 0 1))
    (hiξ' : InjOn ξ' (Icc 0 1)) (hiη' : InjOn η' (Icc 0 1))
    (hconn : ConnectedSpace Y)
    (AS : SurfAtlas S)
    (hrel : BdCohRel s t (arcCocycle hS hne hb' hl') (arcCocycle hS hne hb hl))
    (hw1 : cocInt (w1 AS) a' = cocInt (w1 AS) a) :
    ConnectedSpace Y' ∧
    (connectedComponentIn (bd Y) (ξ 0) = connectedComponentIn (bd Y) (η 0) ↔
      connectedComponentIn (bd Y') (ξ' 0) = connectedComponentIn (bd Y') (η' 0)) ∧
    ∃ a₀ b₀ c₀ : ℕ, Nonempty (Y ≃ₜ SurfaceModel a₀ b₀ c₀) ∧ Nonempty (Y' ≃ₜ SurfaceModel a₀ b₀ c₀) := by
  have hconn' : ConnectedSpace Y' :=
    connected_cut_of_bdCohRel hS hne hb hb' hl hl' hY hY' hψ hψ' hP hP' hconn hrel
  obtain ⟨aS, bS, cS, ⟨eS⟩⟩ := classification.{u} S hS inferInstance
  obtain ⟨aY, bY, cY, ⟨eY⟩⟩ := classification.{u} Y hY hconn
  obtain ⟨aY', bY', cY', ⟨eY'⟩⟩ := classification.{u} Y' hY' hconn'
  obtain ⟨AY⟩ := exists_surfAtlas hY
  obtain ⟨AY'⟩ := exists_surfAtlas hY'
  -- Orientability matches: `bY = 0 ↔ bY' = 0`!
  have hori_eq : bY = 0 ↔ bY' = 0 := by
    rw [← cohRel_w1_zero_iff_of_homeo hY AY eY, ← cohRel_w1_zero_iff_of_homeo hY' AY' eY',
      cut_orientable_iff_cohRel_w1 hS hne hb hl hY hψ hP AY AS,
      cut_orientable_iff_cohRel_w1 hS hne hb' hl' hY' hψ' hP' AY' AS]
    exact or_congr_right ⟨fun h => h.trans hrel.cohRel.symm,
      fun h => h.trans hrel.cohRel⟩
  have hinv := cut_arc_model_invariants hS hY hne hψ hb hl hP L ha0 ha1 himξ himη hiξ hiη eS eY
  have hinv' := cut_arc_model_invariants hS hY' hne hψ' hb' hl' hP' L' ha'0 ha'1 himξ' himη' hiξ' hiη' eS eY'
  have htype_and_nums :
      (connectedComponentIn (bd Y) (ξ 0) = connectedComponentIn (bd Y) (η 0) ↔
        connectedComponentIn (bd Y') (ξ' 0) = connectedComponentIn (bd Y') (η' 0)) ∧
      cY = cY' ∧ 2 * aY + bY = 2 * aY' + bY' := by
    by_cases hst : connectedComponentIn (bd S) s = connectedComponentIn (bd S) t
    · -- Same cuff `C_s = C_t`: compare `cocInt (w1 AS) (conc2 a A₁)` vs `cocInt (w1 AS) (conc2 a' A₁)`!
      have hsb : s ∈ bd S := (show s ∈ F ∩ bd S from hb ▸ mem_insert _ _).2
      have htb : t ∈ bd S := (show t ∈ F ∩ bd S from hb ▸ mem_insert_of_mem _ rfl).2
      obtain ⟨φS⟩ := (cuff_statement.{u} S hS).2.2 _ ⟨s, hsb, rfl⟩
      obtain ⟨u_s, -, hus_e⟩ := exists_param (φS.symm ⟨s, mem_connectedComponentIn hsb⟩)
      obtain ⟨r_t, -, hrt_e⟩ := exists_param (φS.symm ⟨t, hst ▸ mem_connectedComponentIn htb⟩)
      set u_t := u_s + Int.fract (r_t - u_s)
      have hus : (φS (ee u_s)).1 = s := by rw [hus_e]; simp
      have hut : (φS (ee u_t)).1 = t := by
        have hee : ee u_t = ee r_t := ee_eq_iff.mpr ⟨-⌊r_t - u_s⌋, by simp only [u_t, Int.cast_neg]; linarith [Int.floor_add_fract (r_t - u_s)]⟩
        rw [hee, hrt_e]; simp
      have hu1 : u_s < u_t := lt_of_le_of_ne (by simp only [u_t]; linarith [Int.fract_nonneg (r_t - u_s)])
        fun he => hne (by rw [← hus, ← hut, he])
      have hu2 : u_t < u_s + 1 := by simp only [u_t]; linarith [Int.fract_lt_one (r_t - u_s)]
      let A₁ : ℝ → S := fun u => (φS (ee (lin u_t (u_s + 1) u))).1
      have hA₁c : ContinuousOn A₁ (Icc 0 1) :=
        continuous_subtype_val.comp_continuousOn (φS.continuous.comp_continuousOn
          (continuous_ee.comp_continuousOn (continuousOn_lin u_t (u_s + 1))))
      have ha_c : ContinuousOn a (Icc 0 1) := (hψ.1.comp_continuousOn L.cξ).congr fun u hu => (L.hξ u hu).symm
      have ha'_c : ContinuousOn a' (Icc 0 1) := (hψ'.1.comp_continuousOn L'.cξ).congr fun u hu => (L'.hξ u hu).symm
      have hA₁0 : A₁ 0 = t := by simp only [A₁, lin_zero]; exact hut
      have hloop_eq : cocInt (w1 AS) (conc2 a A₁) = cocInt (w1 AS) (conc2 a' A₁) := by
        rw [cocInt_conc2 (isCoc_w1 hS AS) ha_c hA₁c (ha1.trans hA₁0.symm),
            cocInt_conc2 (isCoc_w1 hS AS) ha'_c hA₁c (ha'1.trans hA₁0.symm), hw1]
      have hp1 := cocInt_same_cuff_iff_oneSided hY hS hne hψ hb hl hP L ha0 ha1 himξ himη hiξ hiη AS hst hu1 hu2 hus hut
      have hp2 := cocInt_same_cuff_iff_oneSided hY' hS hne hψ' hb' hl' hP' L' ha'0 ha'1 himξ' himη' hiξ' hiη' AS hst hu1 hu2 hus hut
      by_cases h1 : connectedComponentIn (bd Y) (ξ 0) = connectedComponentIn (bd Y) (η 0)
      · have h2 : connectedComponentIn (bd Y') (ξ' 0) = connectedComponentIn (bd Y') (η' 0) := by
          by_contra hne2
          have e1 := hp1.2 h1
          have e2 := hp2.1 hne2
          rw [e1, e2] at hloop_eq; exact one_ne_zero hloop_eq
        have hn1 := hinv.2.2 hst h1
        have hn2 := hinv'.2.2 hst h2
        exact ⟨iff_of_true h1 h2, hn1.1.trans hn2.1.symm, by omega⟩
      · have h2 : connectedComponentIn (bd Y') (ξ' 0) ≠ connectedComponentIn (bd Y') (η' 0) := by
          intro heq2
          have e1 := hp1.1 h1
          have e2 := hp2.2 heq2
          rw [e1, e2] at hloop_eq; exact zero_ne_one hloop_eq
        have hn1 := hinv.2.1 hst h1
        have hn2 := hinv'.2.1 hst h2
        exact ⟨iff_of_false h1 h2, hn1.1.trans hn2.1.symm, by omega⟩
    · -- Distinct cuffs `C_s ≠ C_t`:
      have hn1 := hinv.1 hst
      have hn2 := hinv'.1 hst
      exact ⟨iff_of_true hn1.1 hn2.1, by omega, by omega⟩
  obtain ⟨htype, hc_eq, h2ab_eq⟩ := htype_and_nums
  have ⟨eM⟩ := (modelCriterion.2 aY' bY' cY' aY bY cY).mpr ⟨hc_eq.symm, h2ab_eq.symm, hori_eq.symm⟩
  exact ⟨hconn', htype, aY, bY, cY, ⟨eY⟩, ⟨eY'.trans eM⟩⟩

end CutModelClass

end GraphMinor.GHR18
