module

public import GraphMinor.GHR18.Theorem26
public import GraphMinor.Surface.CutParallel

/-!
# Geelen–Huynh–Richter (2018), Theorem 1.3

Given a connected compact surface `S`, a non-separating matching `M : Fin n → Set S` of `n`
pairwise disjoint proper `I`-arcs (`(⋃ j, M j)ᶜ` preconnected), and a matching `L : Fin m → Set S`
of `m` pairwise disjoint proper `I`-arcs whose endpoints are disjoint from the endpoints of `M`,
there exists a boundary-fixing homeomorphism `φ : S ≃ₜ S` such that `φ '' M j ∩ L i` is finite for
all `j, i` and
```
  ∑ j : Fin n, ∑ i : Fin m, (φ '' M j ∩ L i).ncard ≤ m * (3 ^ n - 1).
```

## Proof outline (induction on `n`)
- `n = 0`: take `φ = Homeomorph.refl S`.
- `n = k + 1`:
  1. Since `(⋃ j, M j)ᶜ` is preconnected and dense in `S`, `(M 0)ᶜ` is preconnected.
  2. Apply `ghr18_theorem_2_6` to `M 0` and `L` to obtain a boundary-fixing homeomorphism `β` such
     that `P₁ := β '' M 0` meets each `L i` in `d_i ≤ 2` simple crossings.
  3. Cut `S` along `P₁` (`exists_cut_arc`) to obtain a connected compact surface `Y` with cutting
     map `ψ : Y → S`.
  4. Lift `β '' M j.succ` (`j : Fin k`) to a non-separating matching `M'` of size `k` in `Y`.
  5. Split each `L i` at its `d_i ≤ 2` simple crossings with `P₁` into `d_i + 1 ≤ 3` pairwise
     disjoint proper `I`-arcs in `Y`, yielding a matching `L'` of size `m' = ∑ i, (d_i + 1) ≤ 3m`
     whose endpoints are disjoint from the endpoints of `M'`.
  6. Apply the induction hypothesis on `Y` to get a boundary-fixing homeomorphism `G : Y ≃ₜ Y`,
     descend `G` across `ψ` via `exists_descend_cut` to `γ : S ≃ₜ S`, and compose `φ := β.trans γ`.
     Then the crossing count is at most `2 * m + 3 * m * (3 ^ k - 1) = m * (3 ^ (k + 1) - 1)`.
-/

@[expose] public section

namespace GraphMinor.GHR18

open Set Topology Metric Complex Function GraphMinor.Surface

variable {S : Type} [TopologicalSpace S]

/-! ### Section 1: Density of complement and lifting/splitting across a cut -/

section CutLifting

/-- The complement of a finite family of pairwise disjoint proper `I`-arcs on a surface is dense. -/
theorem dense_compl_iUnion_iArcs (hS : IsSurface S) {n : ℕ} {M : Fin n → Set S}
    (hM : ∀ j, ∃ s t, s ≠ t ∧ IsLineWithEnds (M j) s t ∧ M j ∩ bd S = {s, t})
    (hMdisj : Pairwise fun i j => Disjoint (M i) (M j)) :
    closure ((⋃ j : Fin n, M j)ᶜ) = univ := by
  classical
  have : T2Space S := hS.2.1
  choose sM tM _ hMl hMb using hM
  have hMcl : ∀ j, IsClosed (M j) := fun j => (hMl j).isCompact.isClosed
  have hint_mem : ∀ j : Fin n, ∀ p ∈ M j \ bd S, p ∈ closure ((⋃ k : Fin n, M k)ᶜ) := by
    intro j p ⟨hpM, hpint⟩
    let Z : Set S := ⋃ (k : Fin n) (_ : k ≠ j), M k
    have hZcl : IsClosed Z := isClosed_iUnion_of_finite fun k => isClosed_iUnion_of_finite fun _ => hMcl k
    have hpZ : p ∉ Z := fun h => by
      obtain ⟨k, hkj, hpk⟩ := mem_iUnion₂.mp h
      exact Set.disjoint_left.mp (hMdisj hkj) hpk hpM
    obtain ⟨bc, hbc0, hbcW⟩ := exists_box_on_iArc hS (hMb j) (hMl j) hpM hpint
      ((isClosed_bd S).isOpen_compl.sdiff hZcl) ⟨hpint, hpZ⟩ sdiff_subset
    have hL_sub : bc.leftHalf ⊆ (⋃ k : Fin n, M k)ᶜ := fun z hz hU => by
      obtain ⟨k, hzk⟩ := mem_iUnion.mp hU
      by_cases hkj : k = j
      · subst hkj
        exact Set.disjoint_left.mp bc.clLeftHalf_disj_A (bc.leftHalf_subset_clLeft hz) hzk
      · exact (hbcW (bc.clLeftHalf_subset_box (bc.leftHalf_subset_clLeft hz))).2
          (mem_iUnion₂.mpr ⟨k, hkj, hzk⟩)
    exact closure_mono hL_sub (hbc0 ▸ bc.center_mem_closure_leftHalf)
  have hM_mem : ∀ j : Fin n, ∀ p ∈ M j, p ∈ closure ((⋃ k : Fin n, M k)ᶜ) := by
    intro j p hpM
    by_cases hpbd : p ∈ bd S
    · obtain ⟨φ, hφ0, hφ1⟩ := hMl j
      have hp_cl : p ∈ closure (M j \ bd S) := by
        have hφ_int : ∀ r : unitInterval, r.1 ∈ Ioo (0 : ℝ) 1 → (φ r).1 ∈ M j \ bd S := fun r hr => by
          refine ⟨(φ r).2, fun hbd => ?_⟩
          have hm : (φ r).1 ∈ M j ∩ bd S := ⟨(φ r).2, hbd⟩
          rw [hMb j] at hm
          rcases hm with hs | ht
          · have h0 : r.1 = 0 := congrArg Subtype.val (φ.injective (Subtype.ext (hs.trans hφ0.symm)))
            linarith [hr.1]
          · have h1 : r.1 = 1 := congrArg Subtype.val (φ.injective (Subtype.ext ((mem_singleton_iff.mp ht).trans hφ1.symm)))
            linarith [hr.2]
        have hm : p ∈ M j ∩ bd S := ⟨hpM, hpbd⟩
        rw [hMb j] at hm
        rcases hm with rfl | htp
        · let seq : ℕ → unitInterval := fun k => ⟨1 / ((k : ℝ) + 2), by positivity, by rw [div_le_one (by positivity)]; linarith⟩
          have hlim : Filter.Tendsto (fun k => (φ (seq k)).1) Filter.atTop (𝓝 (sM j)) := by
            rw [← hφ0]
            refine (continuous_subtype_val.comp φ.continuous).continuousAt.tendsto.comp ?_
            rw [tendsto_subtype_rng]
            have ht0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (Filter.tendsto_add_atTop_nat 1)
            exact ht0.congr fun k => by simp only [seq, Function.comp_apply, Nat.cast_add, Nat.cast_one]; ring
          exact mem_closure_of_tendsto hlim (Filter.Eventually.of_forall fun k =>
            hφ_int (seq k) ⟨by positivity, (div_lt_one (by positivity)).mpr (by linarith)⟩)
        · rw [mem_singleton_iff.mp htp]
          let seq : ℕ → unitInterval := fun k => ⟨1 - 1 / ((k : ℝ) + 2),
            by have : 1 / ((k : ℝ) + 2) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
               linarith,
            by have : (0 : ℝ) < 1 / ((k : ℝ) + 2) := by positivity
               linarith⟩
          have hlim : Filter.Tendsto (fun k => (φ (seq k)).1) Filter.atTop (𝓝 (tM j)) := by
            rw [← hφ1]
            refine (continuous_subtype_val.comp φ.continuous).continuousAt.tendsto.comp ?_
            rw [tendsto_subtype_rng]
            have ht0 : Filter.Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 2)) Filter.atTop (𝓝 0) :=
              ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (Filter.tendsto_add_atTop_nat 1)).congr fun k => by
                simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]; ring
            simpa [seq] using tendsto_const_nhds.sub ht0
          exact mem_closure_of_tendsto hlim (Filter.Eventually.of_forall fun k =>
            hφ_int (seq k) ⟨by dsimp only [seq]; have : 1 / ((k : ℝ) + 2) < 1 := (div_lt_one (by positivity)).mpr (by linarith); linarith,
              by dsimp only [seq]; have : (0 : ℝ) < 1 / ((k : ℝ) + 2) := (by positivity); linarith⟩)
      exact closure_minimal (hint_mem j) isClosed_closure hp_cl
    · exact hint_mem j p ⟨hpM, hpbd⟩
  ext x; simp only [mem_univ, iff_true]
  by_cases hx : x ∈ ⋃ j : Fin n, M j
  · obtain ⟨j, hxj⟩ := mem_iUnion.mp hx; exact hM_mem j x hxj
  · exact subset_closure hx

/-- Any single arc of a non-separating matching is non-separating. -/
theorem isPreconnected_compl_of_matching (hS : IsSurface S) {n : ℕ} {M : Fin n → Set S}
    (hM : ∀ j, ∃ s t, s ≠ t ∧ IsLineWithEnds (M j) s t ∧ M j ∩ bd S = {s, t})
    (hMdisj : Pairwise fun i j => Disjoint (M i) (M j))
    (hnonsep : IsPreconnected ((⋃ j : Fin n, M j)ᶜ : Set S)) (j₀ : Fin n) :
    IsPreconnected ((M j₀)ᶜ : Set S) := by
  refine hnonsep.subset_closure (fun x hx h0 => hx (mem_iUnion.mpr ⟨j₀, h0⟩)) ?_
  rw [dense_compl_iUnion_iArcs hS hM hMdisj]; exact subset_univ _

/-- Lifting a proper `I`-arc `Q` disjoint from the cut arc `F` across `ψ : Y → S`. -/
theorem lift_disjoint_iArc {Y : Type} [TopologicalSpace Y] [T2Space Y]
    (hY : IsSurface Y) (hS : IsSurface S) {ψ : Y → S} {F : Set S}
    (hψ : IsCutting ψ F) (hF : IsClosed F)
    {Q : Set S} {u v : S} (huv : u ≠ v) (hQl : IsLineWithEnds Q u v) (hQb : Q ∩ bd S = {u, v})
    (hdisj : Disjoint Q F) :
    ∃ u' v' : Y, u' ≠ v' ∧ ψ u' = u ∧ ψ v' = v ∧
      IsLineWithEnds (ψ ⁻¹' Q) u' v' ∧ (ψ ⁻¹' Q) ∩ bd Y = {u', v'} := by
  have : CompactSpace Y := hY.1
  have : T2Space S := hS.2.1
  let eF := cutComplHomeo hψ hF
  have hQsub : Q ⊆ Fᶜ := Set.disjoint_left.mp hdisj
  obtain ⟨φ, hφ0, hφ1⟩ := hQl
  have huQ : u ∈ Q := hφ0 ▸ (φ 0).2
  have hvQ : v ∈ Q := hφ1 ▸ (φ 1).2
  let u' : Y := (eF.symm ⟨u, hQsub huQ⟩).1
  let v' : Y := (eF.symm ⟨v, hQsub hvQ⟩).1
  have hψu : ψ u' = u := by
    have := congrArg Subtype.val (eF.apply_symm_apply ⟨u, hQsub huQ⟩)
    exact this
  have hψv : ψ v' = v := by
    have := congrArg Subtype.val (eF.apply_symm_apply ⟨v, hQsub hvQ⟩)
    exact this
  have huv' : u' ≠ v' := fun h => huv (hψu.symm.trans ((congrArg ψ h).trans hψv))
  let toQ' : Q → (ψ ⁻¹' Q : Set Y) := fun x =>
    ⟨(eF.symm ⟨x.1, hQsub x.2⟩).1, by
      show ψ (eF.symm ⟨x.1, hQsub x.2⟩).1 ∈ Q
      have h : ψ (eF.symm ⟨x.1, hQsub x.2⟩).1 = x.1 :=
        congrArg Subtype.val (eF.apply_symm_apply ⟨x.1, hQsub x.2⟩)
      rw [h]; exact x.2⟩
  let fromQ' : (ψ ⁻¹' Q : Set Y) → Q := fun y => ⟨ψ y.1, y.2⟩
  let hQhomeo : Q ≃ₜ (ψ ⁻¹' Q : Set Y) :=
    { toFun := toQ'
      invFun := fromQ'
      left_inv := fun x => Subtype.ext (show ψ (eF.symm ⟨x.1, hQsub x.2⟩).1 = x.1 from
        congrArg Subtype.val (eF.apply_symm_apply ⟨x.1, hQsub x.2⟩))
      right_inv := fun y => by
        have hyF : ψ y.1 ∉ F := hQsub y.2
        have h := congrArg Subtype.val (eF.symm_apply_apply ⟨y.1, hyF⟩)
        exact Subtype.ext h
      continuous_toFun := Continuous.subtype_mk
        (continuous_subtype_val.comp (eF.symm.continuous.comp (Continuous.subtype_mk continuous_subtype_val fun x => hQsub x.2))) _
      continuous_invFun := Continuous.subtype_mk (hψ.1.comp continuous_subtype_val) _ }
  have hL' : IsLineWithEnds (ψ ⁻¹' Q) u' v' := by
    refine ⟨φ.trans hQhomeo, ?_, ?_⟩
    · change (eF.symm ⟨(φ 0).1, hQsub (φ 0).2⟩).1 = (eF.symm ⟨u, hQsub huQ⟩).1
      congr 2; exact Subtype.ext hφ0
    · change (eF.symm ⟨(φ 1).1, hQsub (φ 1).2⟩).1 = (eF.symm ⟨v, hQsub hvQ⟩).1
      congr 2; exact Subtype.ext hφ1
  have hbd' : (ψ ⁻¹' Q) ∩ bd Y = {u', v'} := by
    have hu'F : ψ u' ∉ F := by rw [hψu]; exact hQsub huQ
    have hv'F : ψ v' ∉ F := by rw [hψv]; exact hQsub hvQ
    ext y; constructor
    · rintro ⟨hyQ, hybd⟩
      have hyF : ψ y ∉ F := hQsub hyQ
      have hψbd : ψ y ∈ Q ∩ bd S := ⟨hyQ, (mem_bd_cut_iff hY hS hψ hF hyF).mp hybd⟩
      rw [hQb] at hψbd
      rcases hψbd with hu | hv
      · left; exact hψ.2.2.1 hyF hu'F (hu.trans hψu.symm)
      · right; exact hψ.2.2.1 hyF hv'F ((mem_singleton_iff.mp hv).trans hψv.symm)
    · rintro (rfl | rfl)
      · refine ⟨by show ψ u' ∈ Q; rw [hψu]; exact huQ, (mem_bd_cut_iff hY hS hψ hF hu'F).mpr ?_⟩
        rw [hψu]; exact (hQb.symm ▸ Or.inl rfl : u ∈ Q ∩ bd S).2
      · refine ⟨by show ψ v' ∈ Q; rw [hψv]; exact hvQ, (mem_bd_cut_iff hY hS hψ hF hv'F).mpr ?_⟩
        rw [hψv]; exact (hQb.symm ▸ Or.inr rfl : v ∈ Q ∩ bd S).2
  exact ⟨u', v', huv', hψu, hψv, hL', hbd'⟩

/-- In a compact surface `Y`, the interior `(bd Y)ᶜ` is dense in `Y`. -/
private theorem dense_compl_bd_surface {Y : Type} [TopologicalSpace Y] (hY : IsSurface Y) :
    closure ((bd Y)ᶜ : Set Y) = univ := by
  ext y; simp only [mem_univ, iff_true, _root_.mem_closure_iff]
  intro U hUo hyU
  obtain ⟨c, hyU'⟩ := exists_surfChart (hY.2.2 y)
  have hO_nhd : c.k ⁻¹' (c.U ∩ U) ∈ 𝓝[c.O ∩ halfPlane] (c.j y) :=
    (c.hk (c.j y) (c.hm hyU')).preimage_mem_nhdsWithin
      ((c.hU.inter hUo).mem_nhds ⟨by rw [c.hl hyU']; exact hyU', by rw [c.hl hyU']; exact hyU⟩)
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhdsWithin_iff.mp hO_nhd
  obtain ⟨r', hr', hr'O⟩ := Metric.isOpen_iff.mp c.hO (c.j y) (c.hm hyU').1
  let ε := min (r / 2) (r' / 2)
  have hε : 0 < ε := lt_min (half_pos hr) (half_pos hr')
  let w : ℂ := c.j y + (ε : ℂ)
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

/-- Local two-sided limit at a simple crossing `p ∈ F ∩ Q` when cutting `S` along `F`:
the lifted open sub-arcs of `Q` approaching `p` from the left and from the right converge in `Y`
to the TWO DISTINCT preimages `yL ≠ yR` of `p` under `ψ`. -/
private theorem exists_crossing_side_limits {Y : Type} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [T2Space S]
    (hY : IsSurface Y) (hS : IsSurface S) {ψ : Y → S} {F Q : Set S}
    (hψ : IsCutting ψ F) (hF : IsClosed F) (hsimple : IsSimpleCrossing F Q)
    (φ : unitInterval ≃ₜ Q) {a t₀ b : ℝ}
    (ha0 : 0 ≤ a) (hat : a < t₀) (htb : t₀ < b) (hb1 : b ≤ 1)
    (htF : (φ ⟨t₀, ⟨ha0.trans hat.le, htb.le.trans hb1⟩⟩).1 ∈ F)
    (hL_off : ∀ t : ℝ, (ht : t ∈ Ioo a t₀) → (φ ⟨t, ⟨ha0.trans ht.1.le, ht.2.le.trans (htb.le.trans hb1)⟩⟩).1 ∉ F)
    (hR_off : ∀ t : ℝ, (ht : t ∈ Ioo t₀ b) → (φ ⟨t, ⟨(ha0.trans hat.le).trans ht.1.le, ht.2.le.trans hb1⟩⟩).1 ∉ F) :
    let eF := cutComplHomeo hψ hF
    let liftL : ℝ → Y := fun t =>
      if ht : t ∈ Ioo a t₀ then (eF.symm ⟨(φ ⟨t, ⟨ha0.trans ht.1.le, ht.2.le.trans (htb.le.trans hb1)⟩⟩).1, hL_off t ht⟩).1
      else Classical.choice ⟨(hψ.2.1 (φ 0).1).choose⟩
    let liftR : ℝ → Y := fun t =>
      if ht : t ∈ Ioo t₀ b then (eF.symm ⟨(φ ⟨t, ⟨(ha0.trans hat.le).trans ht.1.le, ht.2.le.trans hb1⟩⟩).1, hR_off t ht⟩).1
      else Classical.choice ⟨(hψ.2.1 (φ 0).1).choose⟩
    ∃ yL yR : Y, yL ≠ yR ∧
      ψ yL = (φ ⟨t₀, ⟨ha0.trans hat.le, htb.le.trans hb1⟩⟩).1 ∧
      ψ yR = (φ ⟨t₀, ⟨ha0.trans hat.le, htb.le.trans hb1⟩⟩).1 ∧
      Filter.Tendsto liftL (𝓝[<] t₀) (𝓝 yL) ∧
      Filter.Tendsto liftR (𝓝[>] t₀) (𝓝 yR) := by
  classical
  have : CompactSpace Y := hY.1
  have : T2Space S := hS.2.1
  let eF := cutComplHomeo hψ hF
  let p : S := (φ ⟨t₀, ⟨ha0.trans hat.le, htb.le.trans hb1⟩⟩).1
  have hpQ : p ∈ Q := (φ _).2
  obtain ⟨g, ε, hε, hgc, hgi, hVopen, hgint, hg0, hFbox, hQbox⟩ := hsimple p ⟨htF, hpQ⟩
  let Rsq : Set ℂ := Icc (-ε) ε ×ℂ Icc (-ε) ε
  let V : Set S := g '' (Ioo (-ε) ε ×ℂ Ioo (-ε) ε)
  let Hpos : Set S := g '' (Ioo (-ε) ε ×ℂ Ioo 0 ε)
  let Hneg : Set S := g '' (Ioo (-ε) ε ×ℂ Ioo (-ε) 0)
  have hsub_oo : Ioo (-ε) ε ×ℂ Ioo (-ε) ε ⊆ Rsq := fun _ h =>
    Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp h).1,
      Ioo_subset_Icc_self (Complex.mem_reProdIm.mp h).2⟩
  have hsub_pos : Ioo (-ε) ε ×ℂ Ioo 0 ε ⊆ Rsq := fun _ h =>
    Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp h).1,
      ⟨by linarith [(Complex.mem_reProdIm.mp h).2.1], (Complex.mem_reProdIm.mp h).2.2.le⟩⟩
  have hsub_neg : Ioo (-ε) ε ×ℂ Ioo (-ε) 0 ⊆ Rsq := fun _ h =>
    Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp h).1,
      ⟨(Complex.mem_reProdIm.mp h).2.1.le, by linarith [(Complex.mem_reProdIm.mp h).2.2]⟩⟩
  have hHpos_open : IsOpen Hpos := isOpen_image_of_manifold (isOpen_Ioo.reProdIm isOpen_Ioo)
    (hgc.mono hsub_pos) (hgi.mono hsub_pos) (fun _ _ => hS.2.2 _)
  have hHneg_open : IsOpen Hneg := isOpen_image_of_manifold (isOpen_Ioo.reProdIm isOpen_Ioo)
    (hgc.mono hsub_neg) (hgi.mono hsub_neg) (fun _ _ => hS.2.2 _)
  have hH_disj : Disjoint Hpos Hneg := by
    rw [Set.disjoint_left]; rintro _ ⟨w₁, hw₁, rfl⟩ ⟨w₂, hw₂, hfe⟩
    have := hgi (hsub_pos hw₁) (hsub_neg hw₂) hfe.symm
    rw [this] at hw₁
    linarith [(Complex.mem_reProdIm.mp hw₁).2.1, (Complex.mem_reProdIm.mp hw₂).2.2]
  have hVF_eq : V \ F = Hpos ∪ Hneg := by
    ext x; constructor
    · rintro ⟨⟨w, hw, rfl⟩, hnotF⟩
      have hw' := Complex.mem_reProdIm.mp hw
      have him_ne : w.im ≠ 0 := fun h0 => hnotF
        (show g w ∈ F ∩ g '' Rsq by
          rw [hFbox]; exact ⟨w, Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self hw'.1, h0⟩, rfl⟩).1
      rcases lt_or_gt_of_ne him_ne with hlt | hgt
      · exact Or.inr ⟨w, Complex.mem_reProdIm.mpr ⟨hw'.1, ⟨hw'.2.1, hlt⟩⟩, rfl⟩
      · exact Or.inl ⟨w, Complex.mem_reProdIm.mpr ⟨hw'.1, ⟨hgt, hw'.2.2⟩⟩, rfl⟩
    · rintro (⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩)
      · have hw' := Complex.mem_reProdIm.mp hw
        refine ⟨⟨w, Complex.mem_reProdIm.mpr ⟨hw'.1, ⟨by linarith [hw'.2.1], hw'.2.2⟩⟩, rfl⟩, fun hF' => ?_⟩
        have h1 : g w ∈ F ∩ g '' Rsq := ⟨hF', w, hsub_pos hw, rfl⟩
        rw [hFbox] at h1; obtain ⟨u, hu, hfe⟩ := h1; rw [Complex.mem_reProdIm] at hu
        have huR : u ∈ Rsq := Complex.mem_reProdIm.mpr ⟨hu.1, by rw [mem_singleton_iff.mp hu.2]; exact ⟨by linarith, hε.le⟩⟩
        have := congrArg Complex.im (hgi (hsub_pos hw) huR hfe.symm)
        rw [mem_singleton_iff.mp hu.2] at this; linarith [hw'.2.1]
      · have hw' := Complex.mem_reProdIm.mp hw
        refine ⟨⟨w, Complex.mem_reProdIm.mpr ⟨hw'.1, ⟨hw'.2.1, by linarith [hw'.2.2]⟩⟩, rfl⟩, fun hF' => ?_⟩
        have h1 : g w ∈ F ∩ g '' Rsq := ⟨hF', w, hsub_neg hw, rfl⟩
        rw [hFbox] at h1; obtain ⟨u, hu, hfe⟩ := h1; rw [Complex.mem_reProdIm] at hu
        have huR : u ∈ Rsq := Complex.mem_reProdIm.mpr ⟨hu.1, by rw [mem_singleton_iff.mp hu.2]; exact ⟨by linarith, hε.le⟩⟩
        have := congrArg Complex.im (hgi (hsub_neg hw) huR hfe.symm)
        rw [mem_singleton_iff.mp hu.2] at this; linarith [hw'.2.2]
  -- Step 1: Every `y ∈ ψ ⁻¹' {p}` cannot lie in BOTH `closure (ψ ⁻¹' Hpos)` and `closure (ψ ⁻¹' Hneg)`!
  have hnot_both_cl : ∀ y : Y, ψ y = p →
      ¬ (y ∈ closure (ψ ⁻¹' Hpos) ∧ y ∈ closure (ψ ⁻¹' Hneg)) := by
    intro y hψy ⟨hcl1, hcl2⟩
    have hyV : y ∈ ψ ⁻¹' V := by
      show ψ y ∈ V; rw [hψy, ← hg0]
      exact ⟨0, Complex.mem_reProdIm.mpr ⟨by simp [hε], by simp [hε]⟩, rfl⟩
    obtain ⟨c, hyU⟩ := exists_surfChart (hY.2.2 y)
    have hO_nhd : c.k ⁻¹' (c.U ∩ ψ ⁻¹' V) ∈ 𝓝[c.O ∩ halfPlane] (c.j y) :=
      (c.hk (c.j y) (c.hm hyU)).preimage_mem_nhdsWithin
        ((c.hU.inter (hVopen.preimage hψ.1)).mem_nhds ⟨by rw [c.hl hyU]; exact hyU, by rw [c.hl hyU]; exact hyV⟩)
    obtain ⟨r₁, hr₁, hr₁sub⟩ := Metric.mem_nhdsWithin_iff.mp hO_nhd
    obtain ⟨r₂, hr₂, hr₂O⟩ := Metric.isOpen_iff.mp c.hO (c.j y) (c.hm hyU).1
    let r := min r₁ r₂
    have hr : 0 < r := lt_min hr₁ hr₂
    let W : Set Y := c.U ∩ c.j ⁻¹' ball (c.j y) r
    have hWo : IsOpen W := c.hj.isOpen_inter_preimage c.hU isOpen_ball
    have hyW : y ∈ W := ⟨hyU, mem_ball_self hr⟩
    have hW_subV : W ⊆ ψ ⁻¹' V := fun z ⟨hzU, hzB⟩ => by
      have h1 : c.k (c.j z) ∈ c.U ∩ ψ ⁻¹' V := hr₁sub ⟨ball_subset_ball (min_le_left _ _) hzB, c.hm hzU⟩
      rw [c.hl hzU] at h1; exact h1.2
    have hW_int_eq : W ∩ (bd Y)ᶜ = c.k '' (ball (c.j y) r ∩ {w : ℂ | 0 < w.re}) := by
      ext z; constructor
      · rintro ⟨⟨hzU, hzB⟩, hzI⟩
        have hre : 0 < (c.j z).re := lt_of_le_of_ne (c.hm hzU).2 (Ne.symm fun h0 => hzI ((c.mem_bd_iff hzU).mpr h0))
        exact ⟨c.j z, ⟨hzB, hre⟩, c.hl hzU⟩
      · rintro ⟨w, ⟨hwB, hwre⟩, rfl⟩
        have hwO : w ∈ c.O ∩ halfPlane := ⟨hr₂O (ball_subset_ball (min_le_right _ _) hwB), show 0 ≤ w.re from le_of_lt hwre⟩
        refine ⟨⟨c.hk' hwO, by show c.j (c.k w) ∈ ball (c.j y) r; rwa [c.hr hwO]⟩, fun hbd => ?_⟩
        have := (c.mem_bd_iff (c.hk' hwO)).mp hbd; rw [c.hr hwO] at this; linarith [show 0 < w.re from hwre]
    have hW_int_pre : IsPreconnected (W ∩ (bd Y)ᶜ) := by
      rw [hW_int_eq]
      have hconv_half : Convex ℝ {w : ℂ | 0 < w.re} := by
        intro x hx z hz u v hu hv huv
        show 0 < (u • x + v • z).re
        simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        rcases eq_or_lt_of_le hu with rfl | hu'
        · rw [show v = 1 by linarith]; simp; exact hz
        · nlinarith [show 0 < x.re from hx, show 0 < z.re from hz]
      exact ((convex_ball (c.j y) r).inter hconv_half).isPreconnected.image c.k
        (c.hk.mono fun w hw => ⟨hr₂O (ball_subset_ball (min_le_right _ _) hw.1), show 0 ≤ w.re from le_of_lt hw.2⟩)
    have hW_int_cov : W ∩ (bd Y)ᶜ ⊆ ψ ⁻¹' Hpos ∪ ψ ⁻¹' Hneg := fun z ⟨hzW, hzI⟩ => by
      have hzF : ψ z ∉ F := fun h => hzI (hψ.2.2.2.2 h)
      have hmem : ψ z ∈ V \ F := ⟨hW_subV hzW, hzF⟩
      rw [hVF_eq] at hmem; exact hmem
    obtain ⟨u₁, hu₁W, hu₁P⟩ := _root_.mem_closure_iff.mp hcl1 W hWo hyW
    obtain ⟨u₂, hu₂W, hu₂N⟩ := _root_.mem_closure_iff.mp hcl2 W hWo hyW
    obtain ⟨z₁, ⟨hz₁W, hz₁P⟩, hz₁I⟩ := _root_.mem_closure_iff.mp (dense_compl_bd_surface hY ▸ mem_univ u₁)
      (W ∩ ψ ⁻¹' Hpos) (hWo.inter (hHpos_open.preimage hψ.1)) ⟨hu₁W, hu₁P⟩
    obtain ⟨z₂, ⟨hz₂W, hz₂N⟩, hz₂I⟩ := _root_.mem_closure_iff.mp (dense_compl_bd_surface hY ▸ mem_univ u₂)
      (W ∩ ψ ⁻¹' Hneg) (hWo.inter (hHneg_open.preimage hψ.1)) ⟨hu₂W, hu₂N⟩
    obtain ⟨z, -, hzP, hzN⟩ := hW_int_pre (ψ ⁻¹' Hpos) (ψ ⁻¹' Hneg)
      (hHpos_open.preimage hψ.1) (hHneg_open.preimage hψ.1) hW_int_cov
      ⟨z₁, ⟨hz₁W, hz₁I⟩, hz₁P⟩ ⟨z₂, ⟨hz₂W, hz₂I⟩, hz₂N⟩
    exact Set.disjoint_left.mp hH_disj hzP hzN
  -- Step 2: Find `y₊ ∈ ψ ⁻¹' {p} ∩ closure (ψ ⁻¹' Hpos)` and `y₋ ∈ ψ ⁻¹' {p} ∩ closure (ψ ⁻¹' Hneg)`!
  have hex_side : ∀ (σ : ℝ), (σ = 1 ∨ σ = -1) →
      ∃ y : Y, ψ y = p ∧ y ∈ closure (ψ ⁻¹' (if σ = 1 then Hpos else Hneg)) := by
    intro σ hσ
    let Hσ : Set S := if σ = 1 then Hpos else Hneg
    have hHσ_subF : Hσ ⊆ Fᶜ := by
      dsimp only [Hσ]; split_ifs
      · exact fun x hx => (hVF_eq.symm ▸ Or.inl hx : x ∈ V \ F).2
      · exact fun x hx => (hVF_eq.symm ▸ Or.inr hx : x ∈ V \ F).2
    let wseq : ℕ → ℂ := fun n => ((σ * (ε / ((n : ℝ) + 2)) : ℝ) : ℂ) * I
    have hw_in : ∀ n : ℕ, g (wseq n) ∈ Hσ := fun n => by
      have hpos : 0 < ε / ((n : ℝ) + 2) := by positivity
      have hlt : ε / ((n : ℝ) + 2) < ε := (div_lt_iff₀ (by positivity)).mpr (by nlinarith)
      have hwre : (wseq n).re = 0 := by
        dsimp only [wseq]; rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
      have hwim : (wseq n).im = σ * (ε / ((n : ℝ) + 2)) := by
        dsimp only [wseq]; rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
      rcases hσ with rfl | rfl
      · simp only [Hσ, ↓reduceIte]
        refine ⟨wseq n, Complex.mem_reProdIm.mpr ⟨?_, ?_⟩, rfl⟩
        · rw [hwre]; exact ⟨by linarith, hε⟩
        · rw [hwim, one_mul]; exact ⟨hpos, hlt⟩
      · simp only [Hσ, show (-1 : ℝ) ≠ 1 by norm_num, ↓reduceIte]
        refine ⟨wseq n, Complex.mem_reProdIm.mpr ⟨?_, ?_⟩, rfl⟩
        · rw [hwre]; exact ⟨by linarith, hε⟩
        · rw [hwim]; exact ⟨by linarith, by linarith⟩
    let yseq : ℕ → Y := fun n => (eF.symm ⟨g (wseq n), hHσ_subF (hw_in n)⟩).1
    have hψ_yseq : ∀ n, ψ (yseq n) = g (wseq n) := fun n =>
      congrArg Subtype.val (eF.apply_symm_apply ⟨g (wseq n), hHσ_subF (hw_in n)⟩)
    have hyseq_in : ∀ n, yseq n ∈ ψ ⁻¹' Hσ := fun n => by
      show ψ (yseq n) ∈ Hσ; rw [hψ_yseq n]; exact hw_in n
    have : (Filter.map yseq Filter.atTop).NeBot := Filter.map_neBot
    obtain ⟨y, -, hycl⟩ := isCompact_univ.exists_clusterPt (f := Filter.map yseq Filter.atTop) (by simp)
    have hlim_gw : Filter.Tendsto (fun n => g (wseq n)) Filter.atTop (𝓝 p) := by
      rw [← hg0]
      refine (hgc.continuousWithinAt (Complex.mem_reProdIm.mpr ⟨by simp [hε.le], by simp [hε.le]⟩)).tendsto.comp ?_
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ (Filter.Eventually.of_forall fun n => ?_)
      · have ht0 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) Filter.atTop (𝓝 0) :=
          ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (Filter.tendsto_add_atTop_nat 1)).congr fun n => by
            simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]; ring
        have h0 : Filter.Tendsto (fun n : ℕ => σ * (ε / ((n : ℝ) + 2))) Filter.atTop (𝓝 0) := by
          have h1 := (tendsto_const_nhds (x := σ * ε)).mul ht0
          rw [mul_zero] at h1; exact h1.congr fun n => by ring
        simpa [wseq] using (Complex.continuous_ofReal.continuousAt.tendsto.comp h0).mul tendsto_const_nhds
      · have hpos : 0 < ε / ((n : ℝ) + 2) := by positivity
        have hlt : ε / ((n : ℝ) + 2) < ε := (div_lt_iff₀ (by positivity)).mpr (by nlinarith)
        have hwre : (wseq n).re = 0 := by
          dsimp only [wseq]; rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
        have hwim : (wseq n).im = σ * (ε / ((n : ℝ) + 2)) := by
          dsimp only [wseq]; rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
        rw [Complex.mem_reProdIm, hwre, hwim]
        rcases hσ with rfl | rfl
        · exact ⟨⟨by linarith, hε.le⟩, ⟨by linarith, by linarith⟩⟩
        · exact ⟨⟨by linarith, hε.le⟩, ⟨by linarith, by linarith⟩⟩
    have hψy : ψ y = p := by
      have hcl_ψ : ClusterPt (ψ y) (Filter.map (fun n => g (wseq n)) Filter.atTop) := by
        have h1 := hycl.map hψ.1.continuousAt Filter.tendsto_map
        simpa only [Filter.map_map, Function.comp_def, hψ_yseq] using h1
      have hle : Filter.map (fun n => g (wseq n)) Filter.atTop ≤ 𝓝 p := hlim_gw
      exact eq_of_nhds_neBot (hcl_ψ.mono hle)
    have hy_clH : y ∈ closure (ψ ⁻¹' Hσ) := by
      rw [mem_closure_iff_clusterPt]
      exact hycl.mono (Filter.le_principal_iff.mpr (Filter.mem_map.mpr (Filter.Eventually.of_forall hyseq_in)))
    exact ⟨y, hψy, hy_clH⟩
  obtain ⟨yPos, hψPos, hclPos⟩ := hex_side 1 (Or.inl rfl)
  simp only [↓reduceIte] at hclPos
  obtain ⟨yNeg, hψNeg, hclNeg⟩ := hex_side (-1) (Or.inr rfl)
  simp only [show (-1 : ℝ) ≠ 1 by norm_num, ↓reduceIte] at hclNeg
  have hyPN_ne : yPos ≠ yNeg := fun h => hnot_both_cl yPos hψPos ⟨hclPos, h ▸ hclNeg⟩
  have hfib_eq : ψ ⁻¹' {p} = {yPos, yNeg} := by
    have hcard : (ψ ⁻¹' {p}).ncard = 2 := hψ.2.2.2.1 p htF
    obtain ⟨z₁, z₂, hne, hpair⟩ := Set.ncard_eq_two.mp hcard
    have h1 : yPos ∈ ({z₁, z₂} : Set Y) := hpair ▸ hψPos
    have h2 : yNeg ∈ ({z₁, z₂} : Set Y) := hpair ▸ hψNeg
    rw [hpair]; ext z; simp only [mem_insert_iff, mem_singleton_iff]
    rcases h1 with rfl | rfl <;> rcases h2 with h | h
    · exact (hyPN_ne h.symm).elim
    · rw [h]
    · rw [h]; exact or_comm
    · exact (hyPN_ne h.symm).elim
  -- Step 3: Any curve `u` in `ψ ⁻¹' Hpos` (or `Hneg`) with `ψ ∘ u → p` along a filter `l` must tend to `yPos` (or `yNeg`)!
  have htend_of_H : ∀ {l : Filter ℝ} [l.NeBot] (u : ℝ → Y) (H : Set S) (y₀ : Y),
      (H = Hpos ∧ y₀ = yPos ∨ H = Hneg ∧ y₀ = yNeg) →
      (∀ᶠ t in l, u t ∈ ψ ⁻¹' H) →
      Filter.Tendsto (fun t => ψ (u t)) l (𝓝 p) →
      Filter.Tendsto u l (𝓝 y₀) := by
    intro l _ u H y₀ hHy hev hlim
    rw [_root_.tendsto_nhds]
    intro U hUo hy₀U
    by_contra hnot
    have hfreq : ∃ᶠ t in l, u t ∈ ψ ⁻¹' H \ U := by
      rw [Filter.frequently_iff]; intro s hs
      by_contra hall; push Not at hall
      exact hnot (Filter.mem_of_superset (Filter.inter_mem hs hev) fun t ⟨hts, htH⟩ => by
        by_contra hnu; exact hall t hts ⟨htH, hnu⟩)
    -- Use compactness of `Uᶜ` for the filter `l ⊓ 𝓟 {t | u t ∈ ψ ⁻¹' H \ U}`:
    let l' := l ⊓ Filter.principal {t | u t ∈ ψ ⁻¹' H \ U}
    have hl'_ne : l'.NeBot := Filter.inf_principal_neBot_iff.mpr fun s hs => by
      obtain ⟨t, hts, ht⟩ := Filter.frequently_iff.mp hfreq hs; exact ⟨t, hts, ht⟩
    have : (Filter.map u l').NeBot := Filter.map_neBot
    obtain ⟨z, -, hzcl⟩ := isCompact_univ.exists_clusterPt (f := Filter.map u l') (by simp)
    have hz_notU : z ∉ U := fun hzU => by
      have : (𝓝 z ⊓ Filter.map u l').NeBot := hzcl
      have hU_mem : U ∈ 𝓝 z ⊓ Filter.map u l' := Filter.mem_inf_of_left (hUo.mem_nhds hzU)
      have hnotU_mem : Uᶜ ∈ 𝓝 z ⊓ Filter.map u l' :=
        Filter.mem_inf_of_right (Filter.mem_map.mpr (Filter.mem_inf_of_right (Filter.mem_principal.mpr fun _ h => h.2)))
      obtain ⟨w, hwU, hwnU⟩ := Filter.nonempty_of_mem (Filter.inter_mem hU_mem hnotU_mem)
      exact hwnU hwU
    have hz_clH : z ∈ closure (ψ ⁻¹' H) := by
      rw [mem_closure_iff_clusterPt]
      exact hzcl.mono (Filter.le_principal_iff.mpr (Filter.mem_map.mpr
        (Filter.mem_inf_of_right (Filter.mem_principal.mpr fun _ h => h.1))))
    have hψz : ψ z = p := by
      have hcl_ψ : ClusterPt (ψ z) (Filter.map (fun t => ψ (u t)) l') := by
        have h1 := hzcl.map hψ.1.continuousAt Filter.tendsto_map
        simpa only [Filter.map_map, Function.comp_def] using h1
      have hle : Filter.map (fun t => ψ (u t)) l' ≤ 𝓝 p :=
        (Filter.map_mono inf_le_left).trans hlim
      exact eq_of_nhds_neBot (hcl_ψ.mono hle)
    have hz_fib : z ∈ ({yPos, yNeg} : Set Y) := hfib_eq ▸ hψz
    rcases hHy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hz_fib with hz | hz
      · rw [hz] at hz_notU; exact hz_notU hy₀U
      · rw [mem_singleton_iff.mp hz] at hz_clH; exact hnot_both_cl yNeg hψNeg ⟨hz_clH, hclNeg⟩
    · rcases hz_fib with hz | hz
      · rw [hz] at hz_clH; exact hnot_both_cl yPos hψPos ⟨hclPos, hz_clH⟩
      · rw [mem_singleton_iff.mp hz] at hz_notU; exact hz_notU hy₀U
  -- Step 4: Near `t₀`, `Q` enters `p` from one of `Hpos, Hneg` and leaves into the OTHER!
  let ψQ : ℝ → S := fun t => if ht : t ∈ Icc (0 : ℝ) 1 then (φ ⟨t, ht⟩).1 else p
  have hψQc : ContinuousOn ψQ (Icc 0 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp φ.continuous).congr fun r => by simp only [Set.domRestrict, Function.comp, ψQ, dite_eq_left r.2]
  have ht₀_in : t₀ ∈ Icc (0 : ℝ) 1 := ⟨ha0.trans hat.le, htb.le.trans hb1⟩
  have hψQ_t₀ : ψQ t₀ = p := by dsimp only [ψQ]; rw [dite_eq_left ht₀_in]
  have hpreV : ψQ ⁻¹' V ∈ 𝓝[Icc (0 : ℝ) 1] t₀ :=
    hψQc.continuousWithinAt ht₀_in (hVopen.mem_nhds (hψQ_t₀.symm ▸ hg0.symm ▸ ⟨0, Complex.mem_reProdIm.mpr ⟨by simp [hε], by simp [hε]⟩, rfl⟩))
  obtain ⟨δ₀, hδ₀, hδ₀sub⟩ := Metric.mem_nhdsWithin_iff.mp hpreV
  let δ := min (δ₀ / 2) (min (t₀ - a) (b - t₀))
  have hδ : 0 < δ := lt_min (half_pos hδ₀) (lt_min (sub_pos.mpr hat) (sub_pos.mpr htb))
  have hIoo_sub : Ioo (t₀ - δ) (t₀ + δ) ⊆ Ioo a b := fun t ht =>
    ⟨by linarith [ht.1, (min_le_right (δ₀ / 2) _).trans (min_le_left (t₀ - a) (b - t₀))],
     by linarith [ht.2, (min_le_right (δ₀ / 2) _).trans (min_le_right (t₀ - a) (b - t₀))]⟩
  have hIcc_sub : Icc (t₀ - δ / 2) (t₀ + δ / 2) ⊆ Ioo (t₀ - δ) (t₀ + δ) := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hIoo_V : ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ), ψQ t ∈ V := fun t ht =>
    hδ₀sub ⟨by rw [Metric.mem_ball, Real.dist_eq, abs_lt]
               have h1 : δ ≤ δ₀ / 2 := min_le_left _ _
               exact ⟨by linarith [ht.1], by linarith [ht.2]⟩,
      ⟨ha0.trans (hIoo_sub ht).1.le, (hIoo_sub ht).2.le.trans hb1⟩⟩
  -- Left side `(t₀ - δ, t₀)` is connected in `V \ F = Hpos ∪ Hneg`, so lies in ONE half; same for `(t₀, t₀ + δ)`:
  have hside_L : ψQ '' Ioo (t₀ - δ) t₀ ⊆ Hpos ∨ ψQ '' Ioo (t₀ - δ) t₀ ⊆ Hneg := by
    have hpre : IsPreconnected (ψQ '' Ioo (t₀ - δ) t₀) :=
      isPreconnected_Ioo.image ψQ (hψQc.mono fun t ht => ⟨ha0.trans (hIoo_sub ⟨ht.1, ht.2.trans (by linarith)⟩).1.le,
        (hIoo_sub ⟨ht.1, ht.2.trans (by linarith)⟩).2.le.trans hb1⟩)
    have hcov : ψQ '' Ioo (t₀ - δ) t₀ ⊆ Hpos ∪ Hneg := by
      rintro _ ⟨t, ht, rfl⟩
      rw [← hVF_eq]; refine ⟨hIoo_V t ⟨ht.1, ht.2.trans (by linarith)⟩, ?_⟩
      have htab : t ∈ Ioo a t₀ := ⟨(hIoo_sub ⟨ht.1, ht.2.trans (by linarith)⟩).1, ht.2⟩
      have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨ha0.trans htab.1.le, htab.2.le.trans (htb.le.trans hb1)⟩
      dsimp only [ψQ]; rw [dite_eq_left ht01]
      exact hL_off t htab
    by_contra hnot; push Not at hnot
    obtain ⟨x₁, hx₁, hx₁n⟩ := Set.not_subset.mp hnot.1
    obtain ⟨x₂, hx₂, hx₂n⟩ := Set.not_subset.mp hnot.2
    obtain ⟨z, -, hzP, hzN⟩ := hpre Hpos Hneg hHpos_open hHneg_open hcov
      ⟨x₂, hx₂, (hcov hx₂).resolve_right hx₂n⟩ ⟨x₁, hx₁, (hcov hx₁).resolve_left hx₁n⟩
    exact Set.disjoint_left.mp hH_disj hzP hzN
  have hside_R : ψQ '' Ioo t₀ (t₀ + δ) ⊆ Hpos ∨ ψQ '' Ioo t₀ (t₀ + δ) ⊆ Hneg := by
    have hpre : IsPreconnected (ψQ '' Ioo t₀ (t₀ + δ)) :=
      isPreconnected_Ioo.image ψQ (hψQc.mono fun t ht => ⟨ha0.trans (hIoo_sub ⟨(by linarith : t₀ - δ < t₀).trans ht.1, ht.2⟩).1.le,
        (hIoo_sub ⟨(by linarith : t₀ - δ < t₀).trans ht.1, ht.2⟩).2.le.trans hb1⟩)
    have hcov : ψQ '' Ioo t₀ (t₀ + δ) ⊆ Hpos ∪ Hneg := by
      rintro _ ⟨t, ht, rfl⟩
      rw [← hVF_eq]; refine ⟨hIoo_V t ⟨(by linarith : t₀ - δ < t₀).trans ht.1, ht.2⟩, ?_⟩
      have htab : t ∈ Ioo t₀ b := ⟨ht.1, (hIoo_sub ⟨(by linarith : t₀ - δ < t₀).trans ht.1, ht.2⟩).2⟩
      have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨(ha0.trans hat.le).trans htab.1.le, htab.2.le.trans hb1⟩
      dsimp only [ψQ]; rw [dite_eq_left ht01]
      exact hR_off t htab
    by_contra hnot; push Not at hnot
    obtain ⟨x₁, hx₁, hx₁n⟩ := Set.not_subset.mp hnot.1
    obtain ⟨x₂, hx₂, hx₂n⟩ := Set.not_subset.mp hnot.2
    obtain ⟨z, -, hzP, hzN⟩ := hpre Hpos Hneg hHpos_open hHneg_open hcov
      ⟨x₂, hx₂, (hcov hx₂).resolve_right hx₂n⟩ ⟨x₁, hx₁, (hcov hx₁).resolve_left hx₁n⟩
    exact Set.disjoint_left.mp hH_disj hzP hzN
  -- Show `(t₀ - δ, t₀)` and `(t₀, t₀ + δ)` CANNOT lie in the SAME half, by IVT on `im ∘ g⁻¹ ∘ ψQ`!
  have hnot_same : ¬ (ψQ '' Ioo (t₀ - δ) t₀ ⊆ Hpos ∧ ψQ '' Ioo t₀ (t₀ + δ) ⊆ Hpos) ∧
      ¬ (ψQ '' Ioo (t₀ - δ) t₀ ⊆ Hneg ∧ ψQ '' Ioo t₀ (t₀ + δ) ⊆ Hneg) := by
    obtain ⟨ginv, hginvc, hginv_l⟩ := exists_inv_of_compactOn (isCompact_Icc.reProdIm isCompact_Icc) hgc hgi
    let f : ℝ → ℝ := fun t => (ginv (ψQ t)).im
    have hIcc_box : ∀ t ∈ Icc (t₀ - δ / 2) (t₀ + δ / 2), ψQ t ∈ g '' Rsq := fun t ht =>
      (image_mono hsub_oo) (hIoo_V t (hIcc_sub ht))
    have hfc : ContinuousOn f (Icc (t₀ - δ / 2) (t₀ + δ / 2)) :=
      Complex.continuous_im.comp_continuousOn
        (hginvc.comp (hψQc.mono fun t ht => ⟨ha0.trans (hIoo_sub (hIcc_sub ht)).1.le,
          (hIoo_sub (hIcc_sub ht)).2.le.trans hb1⟩) hIcc_box)
    have hfi : InjOn f (Icc (t₀ - δ / 2) (t₀ + δ / 2)) := by
      intro t₁ ht₁ t₂ ht₂ he
      have ht₁01 : t₁ ∈ Icc (0 : ℝ) 1 := ⟨ha0.trans (hIoo_sub (hIcc_sub ht₁)).1.le, (hIoo_sub (hIcc_sub ht₁)).2.le.trans hb1⟩
      have ht₂01 : t₂ ∈ Icc (0 : ℝ) 1 := ⟨ha0.trans (hIoo_sub (hIcc_sub ht₂)).1.le, (hIoo_sub (hIcc_sub ht₂)).2.le.trans hb1⟩
      have hre0 : ∀ t ∈ Icc (t₀ - δ / 2) (t₀ + δ / 2), (ginv (ψQ t)).re = 0 ∧ g (ginv (ψQ t)) = ψQ t := fun t ht => by
        have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨ha0.trans (hIoo_sub (hIcc_sub ht)).1.le, (hIoo_sub (hIcc_sub ht)).2.le.trans hb1⟩
        have htQ : ψQ t ∈ Q := by simp only [ψQ, dite_eq_left ht01]; exact (φ ⟨t, ht01⟩).2
        have h1 : ψQ t ∈ Q ∩ g '' Rsq := ⟨htQ, hIcc_box t ht⟩
        rw [hQbox] at h1; obtain ⟨w, hw, hwe⟩ := h1; rw [Complex.mem_reProdIm] at hw
        have hwR : w ∈ Rsq := Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hw.1]; exact ⟨by linarith, hε.le⟩, hw.2⟩
        have hgw : ginv (ψQ t) = w := by rw [← hwe]; exact hginv_l hwR
        exact ⟨by rw [hgw]; exact mem_singleton_iff.mp hw.1, by rw [hgw, hwe]⟩
      have hge : ginv (ψQ t₁) = ginv (ψQ t₂) := Complex.ext ((hre0 t₁ ht₁).1.trans (hre0 t₂ ht₂).1.symm) he
      have hψe : ψQ t₁ = ψQ t₂ := by rw [← (hre0 t₁ ht₁).2, ← (hre0 t₂ ht₂).2, hge]
      simp only [ψQ, dite_eq_left ht₁01, dite_eq_left ht₂01] at hψe
      exact congrArg Subtype.val (φ.injective (Subtype.ext hψe))
    have hft₀ : f t₀ = 0 := by
      have h0R : (0 : ℂ) ∈ Rsq := Complex.mem_reProdIm.mpr ⟨by simp [hε.le], by simp [hε.le]⟩
      simp only [f, hψQ_t₀, ← hg0, hginv_l h0R, zero_im]
    have hL_pt : t₀ - δ / 2 ∈ Ioo (t₀ - δ) t₀ := ⟨by linarith, by linarith⟩
    have hR_pt : t₀ + δ / 2 ∈ Ioo t₀ (t₀ + δ) := ⟨by linarith, by linarith⟩
    constructor
    · rintro ⟨hLP, hRP⟩
      have hfL : 0 < f (t₀ - δ / 2) := by
        obtain ⟨w, hw, hwe⟩ := hLP ⟨t₀ - δ / 2, hL_pt, rfl⟩
        have : ginv (ψQ (t₀ - δ / 2)) = w := by rw [← hwe]; exact hginv_l (hsub_pos hw)
        simp only [f, this]; exact (Complex.mem_reProdIm.mp hw).2.1
      have hfR : 0 < f (t₀ + δ / 2) := by
        obtain ⟨w, hw, hwe⟩ := hRP ⟨t₀ + δ / 2, hR_pt, rfl⟩
        have : ginv (ψQ (t₀ + δ / 2)) = w := by rw [← hwe]; exact hginv_l (hsub_pos hw)
        simp only [f, this]; exact (Complex.mem_reProdIm.mp hw).2.1
      let m := min (f (t₀ - δ / 2)) (f (t₀ + δ / 2)) / 2
      have hmin_pos : 0 < min (f (t₀ - δ / 2)) (f (t₀ + δ / 2)) := lt_min hfL hfR
      have hm_pos : 0 < m := by dsimp only [m]; linarith
      obtain ⟨s₁, hs₁, hfs₁⟩ := intermediate_value_Icc' (by linarith : t₀ - δ / 2 ≤ t₀)
        (hfc.mono (Icc_subset_Icc_right (by linarith)))
        (show m ∈ Icc (f t₀) (f (t₀ - δ / 2)) from ⟨by rw [hft₀]; exact hm_pos.le, by dsimp only [m]; linarith [min_le_left (f (t₀ - δ / 2)) (f (t₀ + δ / 2))]⟩)
      obtain ⟨s₂, hs₂, hfs₂⟩ := intermediate_value_Icc (by linarith : t₀ ≤ t₀ + δ / 2)
        (hfc.mono (Icc_subset_Icc_left (by linarith)))
        (show m ∈ Icc (f t₀) (f (t₀ + δ / 2)) from ⟨by rw [hft₀]; exact hm_pos.le, by dsimp only [m]; linarith [min_le_right (f (t₀ - δ / 2)) (f (t₀ + δ / 2))]⟩)
      have hs12 := hfi ⟨hs₁.1, hs₁.2.trans (by linarith)⟩ ⟨(by linarith : t₀ - δ / 2 ≤ t₀).trans hs₂.1, hs₂.2⟩ (hfs₁.trans hfs₂.symm)
      have hs1_eq : s₁ = t₀ := le_antisymm hs₁.2 (hs12 ▸ hs₂.1)
      rw [hs1_eq, hft₀] at hfs₁; linarith
    · rintro ⟨hLN, hRN⟩
      have hfL : f (t₀ - δ / 2) < 0 := by
        obtain ⟨w, hw, hwe⟩ := hLN ⟨t₀ - δ / 2, hL_pt, rfl⟩
        have : ginv (ψQ (t₀ - δ / 2)) = w := by rw [← hwe]; exact hginv_l (hsub_neg hw)
        simp only [f, this]; exact (Complex.mem_reProdIm.mp hw).2.2
      have hfR : f (t₀ + δ / 2) < 0 := by
        obtain ⟨w, hw, hwe⟩ := hRN ⟨t₀ + δ / 2, hR_pt, rfl⟩
        have : ginv (ψQ (t₀ + δ / 2)) = w := by rw [← hwe]; exact hginv_l (hsub_neg hw)
        simp only [f, this]; exact (Complex.mem_reProdIm.mp hw).2.2
      let m := max (f (t₀ - δ / 2)) (f (t₀ + δ / 2)) / 2
      have hmax_neg : max (f (t₀ - δ / 2)) (f (t₀ + δ / 2)) < 0 := max_lt hfL hfR
      have hm_neg : m < 0 := by dsimp only [m]; linarith
      obtain ⟨s₁, hs₁, hfs₁⟩ := intermediate_value_Icc (by linarith : t₀ - δ / 2 ≤ t₀)
        (hfc.mono (Icc_subset_Icc_right (by linarith)))
        (show m ∈ Icc (f (t₀ - δ / 2)) (f t₀) from ⟨by dsimp only [m]; linarith [le_max_left (f (t₀ - δ / 2)) (f (t₀ + δ / 2))], by rw [hft₀]; exact hm_neg.le⟩)
      obtain ⟨s₂, hs₂, hfs₂⟩ := intermediate_value_Icc' (by linarith : t₀ ≤ t₀ + δ / 2)
        (hfc.mono (Icc_subset_Icc_left (by linarith)))
        (show m ∈ Icc (f (t₀ + δ / 2)) (f t₀) from ⟨by dsimp only [m]; linarith [le_max_right (f (t₀ - δ / 2)) (f (t₀ + δ / 2))], by rw [hft₀]; exact hm_neg.le⟩)
      have hs12 := hfi ⟨hs₁.1, hs₁.2.trans (by linarith)⟩ ⟨(by linarith : t₀ - δ / 2 ≤ t₀).trans hs₂.1, hs₂.2⟩ (hfs₁.trans hfs₂.symm)
      have hs1_eq : s₁ = t₀ := le_antisymm hs₁.2 (hs12 ▸ hs₂.1)
      rw [hs1_eq, hft₀] at hfs₁; linarith
  -- Step 5: Conclude convergence on `𝓝[<] t₀` and `𝓝[>] t₀` to `{yPos, yNeg}`!
  dsimp only
  let liftL : ℝ → Y := fun t =>
    if ht : t ∈ Ioo a t₀ then (eF.symm ⟨(φ ⟨t, ⟨ha0.trans ht.1.le, ht.2.le.trans (htb.le.trans hb1)⟩⟩).1, hL_off t ht⟩).1
    else Classical.choice ⟨(hψ.2.1 (φ 0).1).choose⟩
  let liftR : ℝ → Y := fun t =>
    if ht : t ∈ Ioo t₀ b then (eF.symm ⟨(φ ⟨t, ⟨(ha0.trans hat.le).trans ht.1.le, ht.2.le.trans hb1⟩⟩).1, hR_off t ht⟩).1
    else Classical.choice ⟨(hψ.2.1 (φ 0).1).choose⟩
  have hψ_liftL : ∀ᶠ t in 𝓝[<] t₀, ψ (liftL t) = ψQ t := by
    filter_upwards [Ioo_mem_nhdsLT (by linarith : t₀ - δ < t₀)] with t ht
    have htab : t ∈ Ioo a t₀ := ⟨(hIoo_sub ⟨ht.1, ht.2.trans (by linarith)⟩).1, ht.2⟩
    have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨ha0.trans htab.1.le, htab.2.le.trans (htb.le.trans hb1)⟩
    simp only [liftL, dite_eq_left htab, ψQ, dite_eq_left ht01]
    exact congrArg Subtype.val (eF.apply_symm_apply ⟨(φ ⟨t, ht01⟩).1, hL_off t htab⟩)
  have hψ_liftR : ∀ᶠ t in 𝓝[>] t₀, ψ (liftR t) = ψQ t := by
    filter_upwards [Ioo_mem_nhdsGT (by linarith : t₀ < t₀ + δ)] with t ht
    have htab : t ∈ Ioo t₀ b := ⟨ht.1, (hIoo_sub ⟨(by linarith : t₀ - δ < t₀).trans ht.1, ht.2⟩).2⟩
    have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨(ha0.trans hat.le).trans htab.1.le, htab.2.le.trans hb1⟩
    simp only [liftR, dite_eq_left htab, ψQ, dite_eq_left ht01]
    exact congrArg Subtype.val (eF.apply_symm_apply ⟨(φ ⟨t, ht01⟩).1, hR_off t htab⟩)
  have hlimL_ψ' : Filter.Tendsto (fun t => ψ (liftL t)) (𝓝[<] t₀) (𝓝 p) := by
    refine Filter.Tendsto.congr' (hψ_liftL.mono fun _ h => h.symm) ?_
    rw [← hψQ_t₀]
    refine (hψQc.continuousWithinAt ht₀_in).tendsto.comp ?_
    exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ nhdsWithin_le_nhds
      (Filter.Eventually.mono (Ioo_mem_nhdsLT (by linarith : t₀ - δ < t₀)) fun t ht =>
        ⟨ha0.trans (hIoo_sub ⟨ht.1, ht.2.trans (by linarith)⟩).1.le,
         (hIoo_sub ⟨ht.1, ht.2.trans (by linarith)⟩).2.le.trans hb1⟩)
  have hlimR_ψ' : Filter.Tendsto (fun t => ψ (liftR t)) (𝓝[>] t₀) (𝓝 p) := by
    refine Filter.Tendsto.congr' (hψ_liftR.mono fun _ h => h.symm) ?_
    rw [← hψQ_t₀]
    refine (hψQc.continuousWithinAt ht₀_in).tendsto.comp ?_
    exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ nhdsWithin_le_nhds
      (Filter.Eventually.mono (Ioo_mem_nhdsGT (by linarith : t₀ < t₀ + δ)) fun t ht =>
        ⟨ha0.trans (hIoo_sub ⟨(by linarith : t₀ - δ < t₀).trans ht.1, ht.2⟩).1.le,
         (hIoo_sub ⟨(by linarith : t₀ - δ < t₀).trans ht.1, ht.2⟩).2.le.trans hb1⟩)
  rcases hside_L with hLP | hLN <;> rcases hside_R with hRP | hRN
  · exact (hnot_same.1 ⟨hLP, hRP⟩).elim
  · refine ⟨yPos, yNeg, hyPN_ne, hψPos, hψNeg, ?_, ?_⟩
    · refine htend_of_H liftL Hpos yPos (Or.inl ⟨rfl, rfl⟩) ?_ hlimL_ψ'
      filter_upwards [Ioo_mem_nhdsLT (by linarith : t₀ - δ < t₀), hψ_liftL] with t ht hψe
      show ψ (liftL t) ∈ Hpos; rw [hψe]; exact hLP ⟨t, ht, rfl⟩
    · refine htend_of_H liftR Hneg yNeg (Or.inr ⟨rfl, rfl⟩) ?_ hlimR_ψ'
      filter_upwards [Ioo_mem_nhdsGT (by linarith : t₀ < t₀ + δ), hψ_liftR] with t ht hψe
      show ψ (liftR t) ∈ Hneg; rw [hψe]; exact hRN ⟨t, ht, rfl⟩
  · refine ⟨yNeg, yPos, hyPN_ne.symm, hψNeg, hψPos, ?_, ?_⟩
    · refine htend_of_H liftL Hneg yNeg (Or.inr ⟨rfl, rfl⟩) ?_ hlimL_ψ'
      filter_upwards [Ioo_mem_nhdsLT (by linarith : t₀ - δ < t₀), hψ_liftL] with t ht hψe
      show ψ (liftL t) ∈ Hneg; rw [hψe]; exact hLN ⟨t, ht, rfl⟩
    · refine htend_of_H liftR Hpos yPos (Or.inl ⟨rfl, rfl⟩) ?_ hlimR_ψ'
      filter_upwards [Ioo_mem_nhdsGT (by linarith : t₀ < t₀ + δ), hψ_liftR] with t ht hψe
      show ψ (liftR t) ∈ Hpos; rw [hψe]; exact hRP ⟨t, ht, rfl⟩
  · exact (hnot_same.2 ⟨hLN, hRN⟩).elim

/-- Split a proper `I`-arc `Q` meeting the cut arc `F` in `d = (F ∩ Q).ncard` simple interior
crossings into `d + 1` pairwise disjoint proper `I`-arcs in the cut surface `Y`. -/
theorem split_transverse_iArc {Y : Type} [TopologicalSpace Y] [T2Space Y]
    (hY : IsSurface Y) (hS : IsSurface S) {ψ : Y → S} {F : Set S}
    (hψ : IsCutting ψ F) (hF : IsClosed F)
    {Q : Set S} {u v : S} (_huv : u ≠ v) (hQl : IsLineWithEnds Q u v) (hQb : Q ∩ bd S = {u, v})
    (huF : u ∉ F) (hvF : v ∉ F)
    (hfin : (F ∩ Q).Finite) (hsimple : IsSimpleCrossing F Q) :
    let d := (F ∩ Q).ncard
    ∃ (pieces : Fin (d + 1) → Set Y),
      (∀ r : Fin (d + 1), ∃ u' v' : Y, u' ≠ v' ∧ IsLineWithEnds (pieces r) u' v' ∧ pieces r ∩ bd Y = {u', v'}) ∧
      (Pairwise fun r₁ r₂ => Disjoint (pieces r₁) (pieces r₂)) ∧
      (∀ r : Fin (d + 1), pieces r ⊆ ψ ⁻¹' Q) ∧
      (ψ ⁻¹' (Q \ F) ⊆ ⋃ r : Fin (d + 1), pieces r) ∧
      (∀ r : Fin (d + 1), pieces r ∩ bd Y ⊆ ψ ⁻¹' (F ∪ {u, v})) := by
  classical
  have : CompactSpace Y := hY.1
  have : T2Space S := hS.2.1
  let d := (F ∩ Q).ncard
  let eF := cutComplHomeo hψ hF
  obtain ⟨φ, hφ0, hφ1⟩ := hQl
  have hφ_int : ∀ r : unitInterval, r.1 ∈ Ioo (0 : ℝ) 1 → (φ r).1 ∈ (bd S)ᶜ := fun r hr hbd => by
    have hm : (φ r).1 ∈ Q ∩ bd S := ⟨(φ r).2, hbd⟩
    rw [hQb] at hm
    rcases hm with hu | hv
    · have h0 : r.1 = 0 := congrArg Subtype.val (φ.injective (Subtype.ext (hu.trans hφ0.symm))); linarith [hr.1]
    · have h1 : r.1 = 1 := congrArg Subtype.val (φ.injective (Subtype.ext ((mem_singleton_iff.mp hv).trans hφ1.symm))); linarith [hr.2]
  -- Crossing parameter set `Tfin ⊆ (0, 1)` of size `d`:
  let toParam : S → ℝ := fun p => if hp : p ∈ Q then (φ.symm ⟨p, hp⟩).1 else 0
  have htoParam_inj : InjOn toParam (F ∩ Q) := fun p₁ hp₁ p₂ hp₂ he => by
    simp only [toParam, dite_eq_left hp₁.2, dite_eq_left hp₂.2] at he
    exact congrArg Subtype.val (φ.symm.injective (Subtype.ext he))
  let Tfin : Finset ℝ := (hfin.image toParam).toFinset
  have hTcard : Tfin.card = d := by
    rw [← Set.ncard_coe_finset, Finite.coe_toFinset]
    exact htoParam_inj.ncard_image
  have hT_oo : ∀ t ∈ Tfin, t ∈ Ioo (0 : ℝ) 1 := fun t ht => by
    obtain ⟨p, ⟨hpF, hpQ⟩, rfl⟩ := (hfin.image toParam).mem_toFinset.mp ht
    simp only [toParam, dite_eq_left hpQ]
    refine ⟨lt_of_le_of_ne (φ.symm ⟨p, hpQ⟩).2.1 fun h0 => huF ?_,
      lt_of_le_of_ne (φ.symm ⟨p, hpQ⟩).2.2 fun h1 => hvF ?_⟩
    · have hp_eq : p = u := by
        have h : (φ (φ.symm ⟨p, hpQ⟩)).1 = p := congrArg Subtype.val (φ.apply_symm_apply ⟨p, hpQ⟩)
        rw [← h, show φ.symm ⟨p, hpQ⟩ = 0 from Subtype.ext h0.symm]; exact hφ0
      exact hp_eq ▸ hpF
    · have hp_eq : p = v := by
        have h : (φ (φ.symm ⟨p, hpQ⟩)).1 = p := congrArg Subtype.val (φ.apply_symm_apply ⟨p, hpQ⟩)
        rw [← h, show φ.symm ⟨p, hpQ⟩ = 1 from Subtype.ext h1]; exact hφ1
      exact hp_eq ▸ hpF
  have hmem_T_iff : ∀ (r : unitInterval), r.1 ∈ Tfin ↔ (φ r).1 ∈ F := fun r => by
    rw [(hfin.image toParam).mem_toFinset]; constructor
    · rintro ⟨p, ⟨hpF, hpQ⟩, hpe⟩
      simp only [toParam, dite_eq_left hpQ] at hpe
      have h1 : φ r = ⟨p, hpQ⟩ := by rw [← Subtype.ext hpe, φ.apply_symm_apply]
      exact (congrArg Subtype.val h1).symm ▸ hpF
    · intro hF'
      refine ⟨(φ r).1, ⟨hF', (φ r).2⟩, ?_⟩
      simp only [toParam, dite_eq_left (φ r).2]
      exact congrArg Subtype.val (φ.symm_apply_apply r)
  -- Sorted endpoints `pts : Fin (d + 2) → ℝ` with `pts 0 = 0`, `pts (last (d + 1)) = 1`:
  let emb : Fin d ↪o ℝ := Tfin.orderEmbOfFin hTcard
  let pts : Fin (d + 2) → ℝ := fun i =>
    if h0 : i.1 = 0 then 0
    else if hd : i.1 = d + 1 then 1
    else emb ⟨i.1 - 1, by omega⟩
  have hpts_0 : pts 0 = 0 := by simp [pts]
  have hpts_last : pts (Fin.last (d + 1)) = 1 := by simp [pts]
  have hpts_mid : ∀ j : Fin d, pts ⟨j.1 + 1, by omega⟩ = emb j := fun j => by
    simp only [pts, Nat.succ_ne_zero, show j.1 + 1 ≠ d + 1 by omega, ↓reduceDIte, Nat.add_sub_cancel, Fin.eta]
  have hpts_mono : StrictMono pts := by
    intro i j hij
    dsimp only [pts]
    by_cases hi0 : i.1 = 0
    · simp only [hi0, ↓reduceDIte]
      have hj0 : j.1 ≠ 0 := by omega
      simp only [hj0, ↓reduceDIte]
      split_ifs with hjd
      · exact zero_lt_one
      · exact (hT_oo _ (Finset.orderEmbOfFin_mem Tfin hTcard _)).1
    · simp only [hi0, ↓reduceDIte]
      have hid : i.1 ≠ d + 1 := by omega
      simp only [hid, ↓reduceDIte]
      have hj0 : j.1 ≠ 0 := by omega
      simp only [hj0, ↓reduceDIte]
      split_ifs with hjd
      · exact (hT_oo _ (Finset.orderEmbOfFin_mem Tfin hTcard _)).2
      · exact emb.strictMono (show (⟨i.1 - 1, by omega⟩ : Fin d) < ⟨j.1 - 1, by omega⟩ by simp [Fin.lt_def]; omega)
  have hpts_01 : ∀ i : Fin (d + 2), pts i ∈ Icc (0 : ℝ) 1 := fun i => by
    constructor
    · rw [← hpts_0]; exact hpts_mono.monotone (Fin.zero_le i)
    · rw [← hpts_last]; exact hpts_mono.monotone (Fin.le_last i)
  have hpts_mid_F : ∀ j : Fin d, (φ ⟨pts ⟨j.1 + 1, by omega⟩, hpts_01 _⟩).1 ∈ F := fun j => by
    rw [← hmem_T_iff]; dsimp only; rw [hpts_mid j]; exact Finset.orderEmbOfFin_mem Tfin hTcard j
  -- Open interval `(pts r.castSucc, pts r.succ)` avoids `F`:
  have hIoo_off : ∀ (r : Fin (d + 1)) (t : ℝ) (ht : t ∈ Ioo (pts r.castSucc) (pts r.succ)),
      (φ ⟨t, ⟨(hpts_01 r.castSucc).1.trans ht.1.le, ht.2.le.trans (hpts_01 r.succ).2⟩⟩).1 ∉ F := by
    intro r t ht hF'
    have htT : t ∈ Tfin := (hmem_T_iff ⟨t, _⟩).mpr hF'
    have hmem_rng : t ∈ range emb := by rw [Finset.range_orderEmbOfFin]; exact htT
    obtain ⟨j, hje⟩ := hmem_rng
    have hj_eq : pts ⟨j.1 + 1, by omega⟩ = t := (hpts_mid j).trans hje
    have h1 : r.castSucc < (⟨j.1 + 1, by omega⟩ : Fin (d + 2)) := hpts_mono.lt_iff_lt.mp (hj_eq.symm ▸ ht.1)
    have h2 : (⟨j.1 + 1, by omega⟩ : Fin (d + 2)) < r.succ := hpts_mono.lt_iff_lt.mp (hj_eq.symm ▸ ht.2)
    simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at h1 h2; omega
  -- Extract left/right limits `yL_mid j ≠ yR_mid j` at each interior crossing `j : Fin d`:
  have hmid_lim_ex : ∀ j : Fin d,
      ∃ yL yR : Y, yL ≠ yR ∧
        ψ yL = (φ ⟨pts ⟨j.1 + 1, by omega⟩, hpts_01 _⟩).1 ∧
        ψ yR = (φ ⟨pts ⟨j.1 + 1, by omega⟩, hpts_01 _⟩).1 ∧
        Filter.Tendsto (fun t =>
          if ht : t ∈ Ioo (pts ⟨j.1, by omega⟩) (pts ⟨j.1 + 1, by omega⟩) then
            (eF.symm ⟨(φ ⟨t, ⟨(hpts_01 _).1.trans ht.1.le, ht.2.le.trans (hpts_01 _).2⟩⟩).1,
              hIoo_off j.castSucc t ht⟩).1
          else Classical.choice ⟨(hψ.2.1 (φ 0).1).choose⟩) (𝓝[<] pts ⟨j.1 + 1, by omega⟩) (𝓝 yL) ∧
        Filter.Tendsto (fun t =>
          if ht : t ∈ Ioo (pts ⟨j.1 + 1, by omega⟩) (pts ⟨j.1 + 2, by omega⟩) then
            (eF.symm ⟨(φ ⟨t, ⟨(hpts_01 _).1.trans ht.1.le, ht.2.le.trans (hpts_01 _).2⟩⟩).1,
              hIoo_off j.succ t ht⟩).1
          else Classical.choice ⟨(hψ.2.1 (φ 0).1).choose⟩) (𝓝[>] pts ⟨j.1 + 1, by omega⟩) (𝓝 yR) := fun j =>
    exists_crossing_side_limits hY hS hψ hF hsimple φ
      (hpts_01 ⟨j.1, by omega⟩).1 (hpts_mono (show (⟨j.1, by omega⟩ : Fin (d + 2)) < ⟨j.1 + 1, by omega⟩ by simp [Fin.lt_def]))
      (hpts_mono (show (⟨j.1 + 1, by omega⟩ : Fin (d + 2)) < ⟨j.1 + 2, by omega⟩ by simp [Fin.lt_def]))
      (hpts_01 ⟨j.1 + 2, by omega⟩).2 (hpts_mid_F j) (hIoo_off j.castSucc) (hIoo_off j.succ)
  choose yL_mid yR_mid hmid_ne hψL_mid hψR_mid htendL_mid htendR_mid using hmid_lim_ex
  -- Outer boundary endpoints `yStart`, `yEnd` in `Y`:
  let yStart : Y := (eF.symm ⟨u, huF⟩).1
  let yEnd : Y := (eF.symm ⟨v, hvF⟩).1
  have hψStart : ψ yStart = u := congrArg Subtype.val (eF.apply_symm_apply ⟨u, huF⟩)
  have hψEnd : ψ yEnd = v := congrArg Subtype.val (eF.apply_symm_apply ⟨v, hvF⟩)
  -- For each `r : Fin (d + 1)`, define endpoints `uY r, vY r` and curve `γY r : ℝ → Y` on `[pts r.castSucc, pts r.succ]`:
  let uY : Fin (d + 1) → Y := fun r => if h0 : r.1 = 0 then yStart else yR_mid ⟨r.1 - 1, by omega⟩
  let vY : Fin (d + 1) → Y := fun r => if hd : r.1 = d then yEnd else yL_mid ⟨r.1, by omega⟩
  have hψ_uY : ∀ r : Fin (d + 1), ψ (uY r) = (φ ⟨pts r.castSucc, hpts_01 _⟩).1 := fun r => by
    dsimp only [uY]; split_ifs with h0
    · rw [hψStart, ← hφ0]
      exact congrArg (fun x => (φ x).1) (Subtype.ext (by simp [show r.castSucc = 0 from Fin.ext h0, hpts_0]))
    · rw [hψR_mid]
      exact congrArg (fun x => (φ x).1) (Subtype.ext (show pts ⟨r.1 - 1 + 1, by omega⟩ = pts r.castSucc from
        congrArg pts (Fin.ext (by simp only [Fin.val_castSucc]; omega))))
  have hψ_vY : ∀ r : Fin (d + 1), ψ (vY r) = (φ ⟨pts r.succ, hpts_01 _⟩).1 := fun r => by
    dsimp only [vY]; split_ifs with hd
    · rw [hψEnd, ← hφ1]
      exact congrArg (fun x => (φ x).1) (Subtype.ext (by simp [show r.succ = Fin.last (d + 1) from Fin.ext (by simp [hd]), hpts_last]))
    · rw [hψL_mid]
      exact congrArg (fun x => (φ x).1) (Subtype.ext (show pts ⟨r.1 + 1, by omega⟩ = pts r.succ from
        congrArg pts (Fin.ext rfl)))
  let γY : Fin (d + 1) → ℝ → Y := fun r t =>
    if ht : t ∈ Ioo (pts r.castSucc) (pts r.succ) then
      (eF.symm ⟨(φ ⟨t, ⟨(hpts_01 r.castSucc).1.trans ht.1.le, ht.2.le.trans (hpts_01 r.succ).2⟩⟩).1, hIoo_off r t ht⟩).1
    else if t ≤ pts r.castSucc then uY r else vY r
  have hγY_left : ∀ r, γY r (pts r.castSucc) = uY r := fun r => by
    simp only [γY, mem_Ioo, lt_self_iff_false, false_and, ↓reduceDIte, le_rfl, ↓reduceIte]
  have hγY_right : ∀ r, γY r (pts r.succ) = vY r := fun r => by
    have hlt : pts r.castSucc < pts r.succ := hpts_mono (Fin.castSucc_lt_succ (i := r))
    simp only [γY, mem_Ioo, lt_self_iff_false, and_false, ↓reduceDIte, not_le.mpr hlt, ↓reduceIte]
  have hψ_γY : ∀ r, ∀ t, (ht : t ∈ Icc (pts r.castSucc) (pts r.succ)) →
      ψ (γY r t) = (φ ⟨t, ⟨(hpts_01 r.castSucc).1.trans ht.1, ht.2.trans (hpts_01 r.succ).2⟩⟩).1 := by
    intro r t ht
    by_cases h1 : t = pts r.castSucc
    · subst h1; rw [hγY_left r, hψ_uY r]
    · by_cases h2 : t = pts r.succ
      · subst h2; rw [hγY_right r, hψ_vY r]
      · have hoo : t ∈ Ioo (pts r.castSucc) (pts r.succ) := ⟨lt_of_le_of_ne ht.1 (Ne.symm h1), lt_of_le_of_ne ht.2 h2⟩
        simp only [γY, dite_eq_left hoo]
        exact congrArg Subtype.val (eF.apply_symm_apply _)
  have hγY_cont : ∀ r : Fin (d + 1), ContinuousOn (γY r) (Icc (pts r.castSucc) (pts r.succ)) := fun r => by
    intro t ht
    have hlt_ab : pts r.castSucc < pts r.succ := hpts_mono (Fin.castSucc_lt_succ (i := r))
    by_cases h1 : t = pts r.castSucc
    · subst h1
      rw [ContinuousWithinAt, hγY_left r]
      have hnhd : 𝓝[Icc (pts r.castSucc) (pts r.succ)] (pts r.castSucc) = 𝓝[≥] (pts r.castSucc) :=
        le_antisymm (nhdsWithin_mono _ Icc_subset_Ici_self)
          (le_inf nhdsWithin_le_nhds (Filter.le_principal_iff.mpr
            (mem_nhdsWithin.mpr ⟨Iio (pts r.succ), isOpen_Iio, hlt_ab, fun x ⟨hx1, hx2⟩ => ⟨hx2, hx1.le⟩⟩)))
      rw [hnhd]
      have h_of_gt : Filter.Tendsto (γY r) (𝓝[>] (pts r.castSucc)) (𝓝 (uY r)) →
          Filter.Tendsto (γY r) (𝓝[≥] (pts r.castSucc)) (𝓝 (uY r)) := fun h => by
        have heq : Ici (pts r.castSucc) = Ioi (pts r.castSucc) ∪ {pts r.castSucc} := by
          ext x; simp [le_iff_lt_or_eq, eq_comm]
        rw [heq, nhdsWithin_union, Filter.tendsto_sup]
        exact ⟨h, by rw [nhdsWithin_singleton, Filter.tendsto_pure_left]; exact fun _ hs => mem_of_mem_nhds (by rwa [hγY_left r])⟩
      refine h_of_gt ?_
      dsimp only [uY]; split_ifs with h0
      · have hr0 : r = 0 := Fin.ext h0; subst hr0
        have h0_eq : pts (0 : Fin (d + 1)).castSucc = 0 := hpts_0
        have hopen_off : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo (pts (0 : Fin (d + 1)).castSucc) (pts (0 : Fin (d + 1)).succ) :=
          Ioo_mem_nhdsGT (h0_eq ▸ hlt_ab)
        rw [h0_eq]
        have hlimS : Filter.Tendsto (fun x : ℝ => (φ ⟨max 0 (min 1 x), le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩).1)
            (𝓝[>] (0 : ℝ)) (𝓝 u) := by
          rw [← hφ0]
          refine ((continuous_subtype_val.comp φ.continuous).continuousAt.tendsto.comp ?_).mono_left nhdsWithin_le_nhds
          have hcont : Continuous (fun x : ℝ => (⟨max 0 (min 1 x), le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩ : unitInterval)) := by fun_prop
          simpa using hcont.continuousAt (x := (0 : ℝ)) |>.tendsto
        have hcont_y : Filter.Tendsto (fun x : ℝ =>
            if hx : (φ ⟨max 0 (min 1 x), ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩⟩).1 ∈ Fᶜ then
              (eF.symm ⟨_, hx⟩).1 else yStart) (𝓝[>] (0 : ℝ)) (𝓝 yStart) := by
          rw [_root_.tendsto_nhds]; intro U hUo hyU
          have hpre : (fun z : (Fᶜ : Set S) => (eF.symm z).1) ⁻¹' U ∈ 𝓝 (⟨u, huF⟩ : (Fᶜ : Set S)) :=
            (continuous_subtype_val.comp eF.symm.continuous).continuousAt (hUo.mem_nhds hyU)
          rw [nhds_subtype_eq_comap, Filter.mem_comap] at hpre
          obtain ⟨W, hW_nhd, hW_sub⟩ := hpre
          filter_upwards [hlimS hW_nhd, hopen_off] with x hxW hxoo
          have hx01 : max 0 (min 1 x) = x := by
            rw [min_eq_right (hxoo.2.le.trans (hpts_01 _).2), max_eq_right (h0_eq ▸ hxoo.1.le)]
          have hsub : (⟨max 0 (min 1 x), ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩⟩ : unitInterval) =
              ⟨x, ⟨(hpts_01 _).1.trans hxoo.1.le, hxoo.2.le.trans (hpts_01 _).2⟩⟩ :=
            Subtype.ext (show max 0 (min 1 x) = x from hx01)
          have hxF : (φ ⟨max 0 (min 1 x), ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩⟩).1 ∈ Fᶜ := by
            rw [hsub]; exact hIoo_off 0 x hxoo
          show (if hx : (φ _).1 ∈ Fᶜ then (eF.symm ⟨_, hx⟩).1 else yStart) ∈ U
          rw [dite_eq_left hxF]; exact hW_sub hxW
        refine hcont_y.congr' (hopen_off.mono fun x hxoo => ?_)
        have hx01 : max 0 (min 1 x) = x := by
          rw [min_eq_right (hxoo.2.le.trans (hpts_01 _).2), max_eq_right (h0_eq ▸ hxoo.1.le)]
        have hsub : (⟨max 0 (min 1 x), ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩⟩ : unitInterval) =
            ⟨x, ⟨(hpts_01 _).1.trans hxoo.1.le, hxoo.2.le.trans (hpts_01 _).2⟩⟩ :=
          Subtype.ext (show max 0 (min 1 x) = x from hx01)
        have hxF : (φ ⟨x, ⟨(hpts_01 _).1.trans hxoo.1.le, hxoo.2.le.trans (hpts_01 _).2⟩⟩).1 ∈ Fᶜ := hIoo_off 0 x hxoo
        dsimp only [γY]; rw [hsub, dite_eq_left hxF, dite_eq_left hxoo]
      · let j : Fin d := ⟨r.1 - 1, by omega⟩
        have hj1 : (⟨j.1 + 1, by omega⟩ : Fin (d + 2)) = r.castSucc := Fin.ext (by simp [j]; omega)
        have hj2 : (⟨j.1 + 2, by omega⟩ : Fin (d + 2)) = r.succ := Fin.ext (by simp [j]; omega)
        have htr := htendR_mid j
        refine (show Filter.Tendsto _ (𝓝[>] pts r.castSucc) (𝓝 (yR_mid ⟨r.1 - 1, by omega⟩)) from by
          simpa only [hj1] using htr).congr' (Filter.Eventually.mono (Ioo_mem_nhdsGT hlt_ab) fun x hx => ?_)
        have hxoo : x ∈ Ioo (pts r.castSucc) (pts r.succ) := hx
        have hx' : x ∈ Ioo (pts r.castSucc) (pts ⟨j.1 + 2, by omega⟩) := by rw [hj2]; exact hxoo
        dsimp only [γY]; rw [dite_eq_left hx', dite_eq_left hxoo]
    · by_cases h2 : t = pts r.succ
      · subst h2
        rw [ContinuousWithinAt, hγY_right r]
        have hnhd : 𝓝[Icc (pts r.castSucc) (pts r.succ)] (pts r.succ) = 𝓝[≤] (pts r.succ) :=
          le_antisymm (nhdsWithin_mono _ Icc_subset_Iic_self)
            (le_inf nhdsWithin_le_nhds (Filter.le_principal_iff.mpr
              (mem_nhdsWithin.mpr ⟨Ioi (pts r.castSucc), isOpen_Ioi, hlt_ab, fun x ⟨hx1, hx2⟩ => ⟨hx1.le, hx2⟩⟩)))
        rw [hnhd]
        have h_of_lt : Filter.Tendsto (γY r) (𝓝[<] (pts r.succ)) (𝓝 (vY r)) →
            Filter.Tendsto (γY r) (𝓝[≤] (pts r.succ)) (𝓝 (vY r)) := fun h => by
          have heq : Iic (pts r.succ) = Iio (pts r.succ) ∪ {pts r.succ} := by
            ext x; simp [le_iff_lt_or_eq]
          rw [heq, nhdsWithin_union, Filter.tendsto_sup]
          exact ⟨h, by rw [nhdsWithin_singleton, Filter.tendsto_pure_left]; exact fun _ hs => mem_of_mem_nhds (by rwa [hγY_right r])⟩
        refine h_of_lt ?_
        dsimp only [vY]; split_ifs with hd
        · have hrd : r = Fin.last d := Fin.ext hd; subst hrd
          have h1_eq : pts (Fin.last d).succ = 1 := hpts_last
          have hopen_off : ∀ᶠ x in 𝓝[<] (1 : ℝ), x ∈ Ioo (pts (Fin.last d).castSucc) (pts (Fin.last d).succ) := by
            rw [h1_eq]; exact Ioo_mem_nhdsLT (h1_eq ▸ hlt_ab)
          rw [h1_eq]
          have hlimS : Filter.Tendsto (fun x : ℝ => (φ ⟨max 0 (min 1 x), ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩⟩).1)
              (𝓝[<] (1 : ℝ)) (𝓝 v) := by
            rw [← hφ1]
            refine ((continuous_subtype_val.comp φ.continuous).continuousAt.tendsto.comp ?_).mono_left nhdsWithin_le_nhds
            have hcont : Continuous (fun x : ℝ => (⟨max 0 (min 1 x), ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩⟩ : unitInterval)) := by fun_prop
            simpa using hcont.continuousAt (x := (1 : ℝ)) |>.tendsto
          have hcont_y : Filter.Tendsto (fun x : ℝ =>
              if hx : (φ ⟨max 0 (min 1 x), ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩⟩).1 ∈ Fᶜ then
                (eF.symm ⟨_, hx⟩).1 else yEnd) (𝓝[<] (1 : ℝ)) (𝓝 yEnd) := by
            rw [_root_.tendsto_nhds]; intro U hUo hyU
            have hpre : (fun z : (Fᶜ : Set S) => (eF.symm z).1) ⁻¹' U ∈ 𝓝 (⟨v, hvF⟩ : (Fᶜ : Set S)) :=
              (continuous_subtype_val.comp eF.symm.continuous).continuousAt (hUo.mem_nhds hyU)
            rw [nhds_subtype_eq_comap, Filter.mem_comap] at hpre
            obtain ⟨W, hW_nhd, hW_sub⟩ := hpre
            filter_upwards [hlimS hW_nhd, hopen_off] with x hxW hxoo
            have hx01 : max 0 (min 1 x) = x := by
              rw [min_eq_right (h1_eq ▸ hxoo.2.le), max_eq_right ((hpts_01 _).1.trans hxoo.1.le)]
            have hsub : (⟨max 0 (min 1 x), ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩⟩ : unitInterval) =
                ⟨x, ⟨(hpts_01 _).1.trans hxoo.1.le, hxoo.2.le.trans (hpts_01 _).2⟩⟩ :=
              Subtype.ext (show max 0 (min 1 x) = x from hx01)
            have hxF : (φ ⟨max 0 (min 1 x), ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩⟩).1 ∈ Fᶜ := by
              rw [hsub]; exact hIoo_off (Fin.last d) x hxoo
            show (if hx : (φ _).1 ∈ Fᶜ then (eF.symm ⟨_, hx⟩).1 else yEnd) ∈ U
            rw [dite_eq_left hxF]; exact hW_sub hxW
          refine hcont_y.congr' (hopen_off.mono fun x hxoo => ?_)
          have hx01 : max 0 (min 1 x) = x := by
            rw [min_eq_right (h1_eq ▸ hxoo.2.le), max_eq_right ((hpts_01 _).1.trans hxoo.1.le)]
          have hsub : (⟨max 0 (min 1 x), ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩⟩ : unitInterval) =
              ⟨x, ⟨(hpts_01 _).1.trans hxoo.1.le, hxoo.2.le.trans (hpts_01 _).2⟩⟩ :=
            Subtype.ext (show max 0 (min 1 x) = x from hx01)
          have hxF : (φ ⟨x, ⟨(hpts_01 _).1.trans hxoo.1.le, hxoo.2.le.trans (hpts_01 _).2⟩⟩).1 ∈ Fᶜ := hIoo_off (Fin.last d) x hxoo
          dsimp only [γY]; rw [hsub, dite_eq_left hxF, dite_eq_left hxoo]
        · let j : Fin d := ⟨r.1, by omega⟩
          have hj0 : (⟨j.1, by omega⟩ : Fin (d + 2)) = r.castSucc := Fin.ext rfl
          have hj1 : (⟨j.1 + 1, by omega⟩ : Fin (d + 2)) = r.succ := Fin.ext rfl
          have htl := htendL_mid j
          refine (show Filter.Tendsto _ (𝓝[<] pts r.succ) (𝓝 (yL_mid ⟨r.1, by omega⟩)) from by
            simpa only [hj1] using htl).congr' (Filter.Eventually.mono (Ioo_mem_nhdsLT hlt_ab) fun x hx => ?_)
          have hxoo : x ∈ Ioo (pts r.castSucc) (pts r.succ) := hx
          have hx' : x ∈ Ioo (pts ⟨j.1, by omega⟩) (pts r.succ) := by rw [hj0]; exact hxoo
          dsimp only [γY]; rw [dite_eq_left hx', dite_eq_left hxoo]
      · -- Interior point `t ∈ Ioo (pts r.castSucc) (pts r.succ)`: continuous via `eF.symm ∘ φ`
        have hoo : t ∈ Ioo (pts r.castSucc) (pts r.succ) := ⟨lt_of_le_of_ne ht.1 (Ne.symm h1), lt_of_le_of_ne ht.2 h2⟩
        have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨(hpts_01 r.castSucc).1.trans ht.1, ht.2.trans (hpts_01 r.succ).2⟩
        have hcont_at : ContinuousAt (γY r) t := by
          rw [ContinuousAt, _root_.tendsto_nhds]; intro U hUo hγU
          let pt : (Fᶜ : Set S) := ⟨(φ ⟨t, ht01⟩).1, hIoo_off r t hoo⟩
          have hγt : γY r t = (eF.symm pt).1 := dite_eq_left hoo
          have hpre : (fun z : (Fᶜ : Set S) => (eF.symm z).1) ⁻¹' U ∈ 𝓝 pt :=
            (continuous_subtype_val.comp eF.symm.continuous).continuousAt
              (hUo.mem_nhds (show (Subtype.val ∘ eF.symm) pt ∈ U by change (eF.symm pt).1 ∈ U; rwa [← hγt]))
          rw [nhds_subtype_eq_comap, Filter.mem_comap] at hpre
          obtain ⟨W, hW_nhd, hW_sub⟩ := hpre
          have hcont_clamp : Continuous (fun x : ℝ => (φ ⟨max 0 (min 1 x), le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩).1) :=
            continuous_subtype_val.comp (φ.continuous.comp (by fun_prop))
          have hclamp_t : (⟨max 0 (min 1 t), ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩⟩ : unitInterval) = ⟨t, ht01⟩ :=
            Subtype.ext (show max 0 (min 1 t) = t by rw [min_eq_right ht01.2, max_eq_right ht01.1])
          have hlimS : Filter.Tendsto (fun x : ℝ => (φ ⟨max 0 (min 1 x), ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩⟩).1)
              (𝓝 t) (𝓝 pt.1) := by
            simpa only [hclamp_t] using hcont_clamp.continuousAt (x := t) |>.tendsto
          filter_upwards [hlimS hW_nhd, isOpen_Ioo.mem_nhds hoo] with x hxW hxoo
          have hx01 : max 0 (min 1 x) = x := by
            rw [min_eq_right (hxoo.2.le.trans (hpts_01 _).2), max_eq_right ((hpts_01 _).1.trans hxoo.1.le)]
          have hsub : (⟨max 0 (min 1 x), ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩⟩ : unitInterval) =
              ⟨x, ⟨(hpts_01 r.castSucc).1.trans hxoo.1.le, hxoo.2.le.trans (hpts_01 r.succ).2⟩⟩ :=
            Subtype.ext (show max 0 (min 1 x) = x from hx01)
          have hγx : γY r x = (eF.symm ⟨(φ ⟨x, ⟨(hpts_01 r.castSucc).1.trans hxoo.1.le, hxoo.2.le.trans (hpts_01 r.succ).2⟩⟩).1,
              hIoo_off r x hxoo⟩).1 := dite_eq_left hxoo
          show γY r x ∈ U; rw [hγx]
          exact hW_sub (by show (φ ⟨x, _⟩).1 ∈ W; rw [← hsub]; exact hxW)
        exact hcont_at.continuousWithinAt
  -- Injectivity of `γY r` on `[pts r.castSucc, pts r.succ]`:
  have hγY_inj : ∀ r : Fin (d + 1), InjOn (γY r) (Icc (pts r.castSucc) (pts r.succ)) := fun r t₁ ht₁ t₂ ht₂ he => by
    have hψe : ψ (γY r t₁) = ψ (γY r t₂) := congrArg ψ he
    rw [hψ_γY r t₁ ht₁, hψ_γY r t₂ ht₂] at hψe
    exact congrArg Subtype.val (φ.injective (Subtype.ext hψe))
  let pieces : Fin (d + 1) → Set Y := fun r => γY r '' Icc (pts r.castSucc) (pts r.succ)
  -- Each `pieces r` is a proper `I`-arc with distinct endpoints `uY r, vY r`:
  have hpieces_arc : ∀ r : Fin (d + 1), ∃ u' v' : Y, u' ≠ v' ∧ IsLineWithEnds (pieces r) u' v' ∧ pieces r ∩ bd Y = {u', v'} := by
    intro r
    have hlt_ab : pts r.castSucc < pts r.succ := hpts_mono (Fin.castSucc_lt_succ (i := r))
    have huv_r : uY r ≠ vY r := fun h => by
      have he : pts r.castSucc = pts r.succ :=
        hγY_inj r (left_mem_Icc.mpr hlt_ab.le) (right_mem_Icc.mpr hlt_ab.le)
          (by rw [hγY_left r, hγY_right r, h])
      linarith
    obtain ⟨inv, hinvc, hinv_l⟩ := exists_inv_of_compactOn isCompact_Icc (hγY_cont r) (hγY_inj r)
    let a := pts r.castSucc
    let b := pts r.succ
    have hba : 0 < b - a := sub_pos.mpr hlt_ab
    let fwd : unitInterval → pieces r := fun s =>
      ⟨γY r ((1 - s.1) * a + s.1 * b),
        ⟨(1 - s.1) * a + s.1 * b, ⟨by nlinarith [s.2.1, s.2.2], by nlinarith [s.2.1, s.2.2]⟩, rfl⟩⟩
    let bwd : pieces r → unitInterval := fun y =>
      ⟨(inv y.1 - a) / (b - a), by
        obtain ⟨t, ht, hty⟩ := y.2
        have hinv_y : inv y.1 = t := hty ▸ hinv_l ht
        rw [hinv_y]
        exact ⟨div_nonneg (sub_nonneg.mpr ht.1) hba.le, (div_le_one hba).mpr (sub_le_sub_right ht.2 a)⟩⟩
    have hline : IsLineWithEnds (pieces r) (uY r) (vY r) := by
      refine ⟨{
        toFun := fwd
        invFun := bwd
        left_inv := fun s => by
          apply Subtype.ext; dsimp only [fwd, bwd]
          have ht : (1 - s.1) * a + s.1 * b ∈ Icc a b := ⟨by nlinarith [s.2.1, s.2.2], by nlinarith [s.2.1, s.2.2]⟩
          rw [hinv_l ht]; field_simp; ring
        right_inv := fun y => by
          apply Subtype.ext; dsimp only [fwd, bwd]
          obtain ⟨t, ht, hty⟩ := y.2
          have hinv_y : inv y.1 = t := hty ▸ hinv_l ht
          rw [hinv_y]
          have heq : (1 - (t - a) / (b - a)) * a + (t - a) / (b - a) * b = t := by field_simp; ring
          rw [heq, hty]
        continuous_toFun := by
          refine Continuous.subtype_mk ?_ _
          exact (hγY_cont r).comp_continuous
            (by fun_prop : Continuous fun s : unitInterval => (1 - s.1) * a + s.1 * b)
            (fun s => ⟨by nlinarith [s.2.1, s.2.2], by nlinarith [s.2.1, s.2.2]⟩)
        continuous_invFun := by
          refine Continuous.subtype_mk ?_ _
          exact (((hinvc.comp_continuous continuous_subtype_val (fun y => y.2)).sub continuous_const).div_const (b - a))
      }, ?_, ?_⟩
      · show γY r ((1 - (0 : ℝ)) * a + 0 * b) = uY r
        simp only [sub_zero, one_mul, zero_mul, add_zero, a]; exact hγY_left r
      · show γY r ((1 - (1 : ℝ)) * a + 1 * b) = vY r
        simp only [sub_self, zero_mul, one_mul, zero_add, b]; exact hγY_right r
    have huY_bd : uY r ∈ bd Y := by
      dsimp only [uY]; split_ifs with h0
      · exact (mem_bd_cut_iff hY hS hψ hF (hψStart.symm ▸ huF)).mpr
          (hψStart.symm ▸ (hQb.symm ▸ Or.inl rfl : u ∈ Q ∩ bd S).2)
      · exact hψ.2.2.2.2 (show ψ (yR_mid ⟨r.1 - 1, by omega⟩) ∈ F by rw [hψR_mid]; exact hpts_mid_F ⟨r.1 - 1, by omega⟩)
    have hvY_bd : vY r ∈ bd Y := by
      dsimp only [vY]; split_ifs with hd
      · exact (mem_bd_cut_iff hY hS hψ hF (hψEnd.symm ▸ hvF)).mpr
          (hψEnd.symm ▸ (hQb.symm ▸ Or.inr rfl : v ∈ Q ∩ bd S).2)
      · exact hψ.2.2.2.2 (show ψ (yL_mid ⟨r.1, by omega⟩) ∈ F by rw [hψL_mid]; exact hpts_mid_F ⟨r.1, by omega⟩)
    have hbd_r : pieces r ∩ bd Y = {uY r, vY r} := by
      ext y; constructor
      · rintro ⟨⟨t, ht, rfl⟩, hybd⟩
        by_cases h1 : t = pts r.castSucc
        · left; rw [h1, hγY_left r]
        · by_cases h2 : t = pts r.succ
          · right; rw [h2, hγY_right r]; rfl
          · exfalso
            have hoo : t ∈ Ioo (pts r.castSucc) (pts r.succ) := ⟨lt_of_le_of_ne ht.1 (Ne.symm h1), lt_of_le_of_ne ht.2 h2⟩
            have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨(hpts_01 r.castSucc).1.trans ht.1, ht.2.trans (hpts_01 r.succ).2⟩
            have hψnotF : ψ (γY r t) ∉ F := by rw [hψ_γY r t ht]; exact hIoo_off r t hoo
            have hψbd : ψ (γY r t) ∈ bd S := (mem_bd_cut_iff hY hS hψ hF hψnotF).mp hybd
            rw [hψ_γY r t ht] at hψbd
            exact hφ_int ⟨t, ht01⟩ ⟨lt_of_le_of_lt (hpts_01 r.castSucc).1 hoo.1, lt_of_lt_of_le hoo.2 (hpts_01 r.succ).2⟩ hψbd
      · rintro (rfl | rfl)
        · exact ⟨⟨pts r.castSucc, left_mem_Icc.mpr hlt_ab.le, hγY_left r⟩, huY_bd⟩
        · exact ⟨⟨pts r.succ, right_mem_Icc.mpr hlt_ab.le, hγY_right r⟩, hvY_bd⟩
    exact ⟨uY r, vY r, huv_r, hline, hbd_r⟩
  -- Pairwise disjointness of `pieces`:
  have hpieces_disj : Pairwise fun r₁ r₂ => Disjoint (pieces r₁) (pieces r₂) := by
    have hlt_disj : ∀ r₁ r₂ : Fin (d + 1), r₁ < r₂ → Disjoint (pieces r₁) (pieces r₂) := by
      intro r₁ r₂ hlt
      rw [Set.disjoint_left]; rintro y ⟨t₁, ht₁, rfl⟩ ⟨t₂, ht₂, hy2⟩
      have hψe : ψ (γY r₁ t₁) = ψ (γY r₂ t₂) := congrArg ψ hy2.symm
      rw [hψ_γY r₁ t₁ ht₁, hψ_γY r₂ t₂ ht₂] at hψe
      have ht12 : t₁ = t₂ := congrArg Subtype.val (φ.injective (Subtype.ext hψe))
      have hle_idx : r₁.succ ≤ r₂.castSucc := by simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; exact Nat.succ_le_of_lt hlt
      have hle_pts : pts r₁.succ ≤ pts r₂.castSucc := hpts_mono.monotone hle_idx
      have hpts_eq : pts r₁.succ = pts r₂.castSucc := le_antisymm hle_pts (ht₂.1.trans (ht12 ▸ ht₁.2))
      have hidx_eq : r₁.succ = r₂.castSucc := hpts_mono.injective hpts_eq
      have hr2_val : r₂.1 = r₁.1 + 1 := (congrArg Fin.val hidx_eq).symm
      have ht1_eq : t₁ = pts r₁.succ := le_antisymm ht₁.2 (hpts_eq.symm ▸ ht12.symm ▸ ht₂.1)
      have ht2_eq : t₂ = pts r₂.castSucc := le_antisymm (hpts_eq ▸ ht12 ▸ ht₁.2) ht₂.1
      rw [ht1_eq, hγY_right r₁, ht2_eq, hγY_left r₂] at hy2
      have hr1_lt : r₁.1 ≠ d := by omega
      have hr2_ne : r₂.1 ≠ 0 := by omega
      have h1 : vY r₁ = yL_mid ⟨r₁.1, by omega⟩ := by dsimp only [vY]; exact dite_eq_right hr1_lt
      have h2 : uY r₂ = yR_mid ⟨r₁.1, by omega⟩ := by
        dsimp only [uY]; rw [dite_eq_right hr2_ne]
        congr 1; exact Fin.ext (by simp [hr2_val])
      rw [h1, h2] at hy2
      exact hmid_ne ⟨r₁.1, by omega⟩ hy2.symm
    intro r₁ r₂ hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hlt_disj r₁ r₂ hlt
    · exact (hlt_disj r₂ r₁ hgt).symm
  -- Remaining 3 properties of `pieces`:
  have hpieces_sub : ∀ r : Fin (d + 1), pieces r ⊆ ψ ⁻¹' Q := by
    rintro r _ ⟨t, ht, rfl⟩
    show ψ (γY r t) ∈ Q; rw [hψ_γY r t ht]; exact (φ _).2
  have hpieces_cov : ψ ⁻¹' (Q \ F) ⊆ ⋃ r : Fin (d + 1), pieces r := by
    intro y ⟨hyQ, hyF⟩
    let s : unitInterval := φ.symm ⟨ψ y, hyQ⟩
    have hφs : (φ s).1 = ψ y := congrArg Subtype.val (φ.apply_symm_apply ⟨ψ y, hyQ⟩)
    by_cases hs0 : s.1 = 0
    · refine mem_iUnion.mpr ⟨0, pts (0 : Fin (d + 1)).castSucc, left_mem_Icc.mpr (hpts_mono (Fin.castSucc_lt_succ (i := 0))).le, ?_⟩
      rw [hγY_left 0]
      have hu_eq : ψ y = u := by rw [← hφs, show s = 0 from Subtype.ext hs0, hφ0]
      have hψu0 : ψ (uY 0) = ψ y := by
        rw [hψ_uY 0, hu_eq, ← hφ0]
        exact congrArg (fun r => (φ r).1) (Subtype.ext hpts_0)
      exact hψ.2.2.1 (show ψ (uY 0) ∉ F by rw [hψu0]; exact hyF) hyF hψu0
    · by_cases hs1 : s.1 = 1
      · refine mem_iUnion.mpr ⟨Fin.last d, pts (Fin.last d).succ, right_mem_Icc.mpr (hpts_mono (Fin.castSucc_lt_succ (i := Fin.last d))).le, ?_⟩
        rw [hγY_right (Fin.last d)]
        have hv_eq : ψ y = v := by rw [← hφs, show s = 1 from Subtype.ext hs1, hφ1]
        have hψv1 : ψ (vY (Fin.last d)) = ψ y := by
          rw [hψ_vY (Fin.last d), hv_eq, ← hφ1]
          exact congrArg (fun r => (φ r).1) (Subtype.ext hpts_last)
        exact hψ.2.2.1 (show ψ (vY (Fin.last d)) ∉ F by rw [hψv1]; exact hyF) hyF hψv1
      · have hs_oo : s.1 ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne s.2.1 (Ne.symm hs0), lt_of_le_of_ne s.2.2 hs1⟩
        have hs_not_pts : ∀ i : Fin (d + 2), pts i ≠ s.1 := fun i hi => by
          by_cases hi0 : i.1 = 0
          · have : i = 0 := Fin.ext hi0; rw [this, hpts_0] at hi; exact hs0 hi.symm
          · by_cases hid : i.1 = d + 1
            · have : i = Fin.last (d + 1) := Fin.ext hid; rw [this, hpts_last] at hi; exact hs1 hi.symm
            · have hj_eq : i = ⟨(i.1 - 1) + 1, by omega⟩ := Fin.ext (by simp; omega)
              have hF' : (φ s).1 ∈ F := by
                have hsub : s = ⟨pts ⟨(i.1 - 1) + 1, by omega⟩, hpts_01 _⟩ := Subtype.ext (by rw [← hj_eq]; exact hi.symm)
                rw [hsub]; exact hpts_mid_F ⟨i.1 - 1, by omega⟩
              exact hyF (hφs ▸ hF')
        let Slt : Finset (Fin (d + 2)) := Finset.univ.filter fun i => pts i < s.1
        have hSlt_ne : Slt.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hpts_0]; exact hs_oo.1⟩⟩
        let i₀ := Slt.max' hSlt_ne
        have hi₀_lt : pts i₀ < s.1 := (Finset.mem_filter.mp (Finset.max'_mem Slt hSlt_ne)).2
        have hi₀_ne_last : i₀.1 < d + 1 := by
          by_contra hge
          have hlt2 : i₀.1 < d + 2 := i₀.2
          have heq : i₀ = Fin.last (d + 1) := Fin.ext (by simp only [Fin.val_last]; omega)
          rw [heq, hpts_last] at hi₀_lt; linarith [hs_oo.2]
        let r : Fin (d + 1) := ⟨i₀.1, hi₀_ne_last⟩
        have hr_cs : r.castSucc = i₀ := Fin.ext rfl
        have hs_lt_succ : s.1 < pts r.succ := by
          by_contra hnot; push Not at hnot
          have hlt' : pts r.succ < s.1 := lt_of_le_of_ne hnot (hs_not_pts r.succ)
          have hle := Finset.le_max' Slt r.succ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt'⟩)
          have : r.1 + 1 ≤ r.1 := hle
          omega
        have hs_Icc : s.1 ∈ Icc (pts r.castSucc) (pts r.succ) := ⟨(hr_cs ▸ hi₀_lt).le, hs_lt_succ.le⟩
        refine mem_iUnion.mpr ⟨r, s.1, hs_Icc, ?_⟩
        have hψe : ψ (γY r s.1) = ψ y := by
          rw [hψ_γY r s.1 hs_Icc, ← hφs]
        exact hψ.2.2.1 (show ψ (γY r s.1) ∉ F by rw [hψe]; exact hyF) hyF hψe
  have hpieces_bd_sub : ∀ r : Fin (d + 1), pieces r ∩ bd Y ⊆ ψ ⁻¹' (F ∪ {u, v}) := by
    intro r y hy
    obtain ⟨u', v', -, -, hbd_r⟩ := hpieces_arc r
    -- Actually prove directly from `hψ_γY` and `hpieces_arc`!
    obtain ⟨⟨t, ht, rfl⟩, hybd⟩ := hy
    show ψ (γY r t) ∈ F ∪ {u, v}
    by_cases h1 : t = pts r.castSucc
    · rw [h1, hγY_left r]; dsimp only [uY]; split_ifs with h0
      · exact Or.inr (Or.inl hψStart)
      · exact Or.inl (by rw [hψR_mid]; exact hpts_mid_F ⟨r.1 - 1, by omega⟩)
    · by_cases h2 : t = pts r.succ
      · rw [h2, hγY_right r]; dsimp only [vY]; split_ifs with hd
        · exact Or.inr (Or.inr hψEnd)
        · exact Or.inl (by rw [hψL_mid]; exact hpts_mid_F ⟨r.1, by omega⟩)
      · exfalso
        have hoo : t ∈ Ioo (pts r.castSucc) (pts r.succ) := ⟨lt_of_le_of_ne ht.1 (Ne.symm h1), lt_of_le_of_ne ht.2 h2⟩
        have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨(hpts_01 r.castSucc).1.trans ht.1, ht.2.trans (hpts_01 r.succ).2⟩
        have hψnotF : ψ (γY r t) ∉ F := by rw [hψ_γY r t ht]; exact hIoo_off r t hoo
        have hψbd : ψ (γY r t) ∈ bd S := (mem_bd_cut_iff hY hS hψ hF hψnotF).mp hybd
        rw [hψ_γY r t ht] at hψbd
        exact hφ_int ⟨t, ht01⟩ ⟨lt_of_le_of_lt (hpts_01 r.castSucc).1 hoo.1, lt_of_lt_of_le hoo.2 (hpts_01 r.succ).2⟩ hψbd
  exact ⟨pieces, hpieces_arc, hpieces_disj, hpieces_sub, hpieces_cov, hpieces_bd_sub⟩

end CutLifting

/-! ### Section 2: Geelen–Huynh–Richter (2018), Theorem 1.3 -/

/-- **Geelen–Huynh–Richter (2018), Theorem 1.3**:
Given a connected compact surface `S`, a non-separating matching `M : Fin n → Set S` of `n`
pairwise disjoint proper `I`-arcs, and a matching `L : Fin m → Set S` of `m` pairwise disjoint
proper `I`-arcs whose endpoints are disjoint from those of `M`, there exists a boundary-fixing
homeomorphism `φ : S ≃ₜ S` such that `φ '' M j ∩ L i` is finite for all `j, i` and
`∑ j, ∑ i, (φ '' M j ∩ L i).ncard ≤ m * (3 ^ n - 1)`. -/
theorem ghr18_theorem_1_3 {n : ℕ} :
    ∀ {S : Type} [TopologicalSpace S] [ConnectedSpace S]
      (_hS : IsSurface S) {m : ℕ}
      {M : Fin n → Set S} {L : Fin m → Set S}
      (_hM : ∀ j, ∃ s t, s ≠ t ∧ IsLineWithEnds (M j) s t ∧ M j ∩ bd S = {s, t})
      (_hMdisj : Pairwise fun j₁ j₂ => Disjoint (M j₁) (M j₂))
      (_hnonsep : IsPreconnected ((⋃ j : Fin n, M j)ᶜ : Set S))
      (_hL : ∀ i, ∃ u v, u ≠ v ∧ IsLineWithEnds (L i) u v ∧ L i ∩ bd S = {u, v})
      (_hLdisj : Pairwise fun i₁ i₂ => Disjoint (L i₁) (L i₂))
      (_hbd_disj : ∀ j i, Disjoint (M j ∩ bd S) (L i ∩ bd S)),
      ∃ φ : S ≃ₜ S, (∀ x ∈ bd S, φ x = x) ∧
        (∀ j i, (φ '' M j ∩ L i).Finite) ∧
        (∀ j i, IsSimpleCrossing (φ '' M j) (L i)) ∧
        (∑ j : Fin n, ∑ i : Fin m, (φ '' M j ∩ L i).ncard) ≤ m * (3 ^ n - 1) := by
  induction n with
  | zero =>
    intro S _ _ _ m M L _ _ _ _ _ _
    exact ⟨Homeomorph.refl S, fun _ _ => rfl, fun j => Fin.elim0 j, fun j => Fin.elim0 j, by simp⟩
  | succ k ih =>
    intro S _ _ hS m M L hM hMdisj hnonsep hL hLdisj hbd_disj
    classical
    have : T2Space S := hS.2.1
    -- Step 1: Apply GHR18 Theorem 2.6 to `M 0` and `L`
    obtain ⟨s₀, t₀, hst₀, hM0l, hM0b⟩ := hM 0
    have hM0_nonsep : IsPreconnected ((M 0)ᶜ : Set S) :=
      isPreconnected_compl_of_matching hS hM hMdisj hnonsep 0
    have hs0L : ∀ i, s₀ ∉ L i := fun i h => by
      have hs0bd : s₀ ∈ M 0 ∩ bd S := hM0b.symm ▸ Or.inl rfl
      exact Set.disjoint_left.mp (hbd_disj 0 i) hs0bd ⟨h, hs0bd.2⟩
    have ht0L : ∀ i, t₀ ∉ L i := fun i h => by
      have ht0bd : t₀ ∈ M 0 ∩ bd S := hM0b.symm ▸ Or.inr rfl
      exact Set.disjoint_left.mp (hbd_disj 0 i) ht0bd ⟨h, ht0bd.2⟩
    obtain ⟨β, hβfix, hβcross⟩ := ghr18_theorem_2_6 hS hst₀ hM0b hM0l hM0_nonsep L hL hLdisj hs0L ht0L
    let P₁ : Set S := β '' M 0
    have himg_line : ∀ {A : Set S} {a b : S}, IsLineWithEnds A a b → IsLineWithEnds (β '' A) (β a) (β b) := by
      intro A a b ⟨f, hf0, hf1⟩
      refine ⟨f.trans (β.image A), ?_, ?_⟩
      · show β (f 0).1 = β a; rw [hf0]
      · show β (f 1).1 = β b; rw [hf1]
    have hP₁l : IsLineWithEnds P₁ s₀ t₀ := by
      have hs0bd : s₀ ∈ bd S := (hM0b.symm ▸ Or.inl rfl : s₀ ∈ M 0 ∩ bd S).2
      have ht0bd : t₀ ∈ bd S := (hM0b.symm ▸ Or.inr rfl : t₀ ∈ M 0 ∩ bd S).2
      rw [← hβfix s₀ hs0bd, ← hβfix t₀ ht0bd]
      exact himg_line hM0l
    have hP₁b : P₁ ∩ bd S = {s₀, t₀} := by
      ext x; constructor
      · rintro ⟨⟨z, hzM, rfl⟩, hxbd⟩
        have hzeq : β z = z := β.injective (hβfix (β z) hxbd)
        have hzbd : z ∈ bd S := hzeq ▸ hxbd
        rw [hzeq]; exact hM0b ▸ ⟨hzM, hzbd⟩
      · rintro (hx | hx)
        · rw [hx]
          have hs0 : s₀ ∈ M 0 ∩ bd S := hM0b.symm ▸ Or.inl rfl
          exact ⟨⟨s₀, hs0.1, hβfix s₀ hs0.2⟩, hs0.2⟩
        · rw [mem_singleton_iff.mp hx]
          have ht0 : t₀ ∈ M 0 ∩ bd S := hM0b.symm ▸ Or.inr rfl
          exact ⟨⟨t₀, ht0.1, hβfix t₀ ht0.2⟩, ht0.2⟩
    have hP₁cl : IsClosed P₁ := hP₁l.isCompact.isClosed
    -- Step 2: Cut `S` along `P₁` to get a connected compact surface `Y`
    obtain ⟨Y, _, _, ψ, hY, hψ, -⟩ := exists_cut_arc hS hst₀ hP₁b hP₁l
    have : CompactSpace Y := hY.1
    have : Nonempty Y := by
      obtain ⟨x⟩ := ‹ConnectedSpace S›.toNonempty
      obtain ⟨y, -⟩ := hψ.2.1 x
      exact ⟨y⟩
    have hP₁_nonsep : IsPreconnected (P₁ᶜ : Set S) := by
      change IsPreconnected ((β '' M 0)ᶜ : Set S)
      rw [← Set.image_compl_eq β.bijective]
      exact hM0_nonsep.image β β.continuous.continuousOn
    have : ConnectedSpace Y := (connectedSpace_cut_iff hY hS hψ hP₁cl).mpr hP₁_nonsep
    -- Step 3: Lift `β '' M j.succ` (`j : Fin k`) to a non-separating matching `M'` in `Y`
    let M' : Fin k → Set Y := fun j => ψ ⁻¹' (β '' M j.succ)
    have hβM_arc : ∀ j : Fin k, ∃ s t, s ≠ t ∧ IsLineWithEnds (β '' M j.succ) s t ∧
        (β '' M j.succ) ∩ bd S = {s, t} ∧ Disjoint (β '' M j.succ) P₁ := by
      intro j
      obtain ⟨s, t, hst, hMl, hMb⟩ := hM j.succ
      have hsbd : s ∈ bd S := (hMb.symm ▸ Or.inl rfl : s ∈ M j.succ ∩ bd S).2
      have htbd : t ∈ bd S := (hMb.symm ▸ Or.inr rfl : t ∈ M j.succ ∩ bd S).2
      refine ⟨s, t, hst, ?_, ?_, ?_⟩
      · rw [← hβfix s hsbd, ← hβfix t htbd]; exact himg_line hMl
      · ext x; constructor
        · rintro ⟨⟨z, hzM, rfl⟩, hxbd⟩
          have hzeq : β z = z := β.injective (hβfix (β z) hxbd)
          have hzbd : z ∈ bd S := hzeq ▸ hxbd
          rw [hzeq]; exact hMb ▸ ⟨hzM, hzbd⟩
        · rintro (hx | hx)
          · rw [hx]; exact ⟨⟨s, (hMb.symm ▸ Or.inl rfl : s ∈ M j.succ ∩ bd S).1, hβfix s hsbd⟩, hsbd⟩
          · rw [mem_singleton_iff.mp hx]; exact ⟨⟨t, (hMb.symm ▸ Or.inr rfl : t ∈ M j.succ ∩ bd S).1, hβfix t htbd⟩, htbd⟩
      · exact Set.disjoint_image_of_injective β.injective (hMdisj (Fin.succ_ne_zero j))
    have hM' : ∀ j : Fin k, ∃ s' t' : Y, s' ≠ t' ∧ IsLineWithEnds (M' j) s' t' ∧ M' j ∩ bd Y = {s', t'} := by
      intro j
      obtain ⟨s, t, hst, hMl, hMb, hdisj⟩ := hβM_arc j
      obtain ⟨s', t', hst', -, -, hL', hbd'⟩ := lift_disjoint_iArc hY hS hψ hP₁cl hst hMl hMb hdisj
      exact ⟨s', t', hst', hL', hbd'⟩
    have hM'disj : Pairwise fun j₁ j₂ : Fin k => Disjoint (M' j₁) (M' j₂) := fun j₁ j₂ hne => by
      have hdisjS : Disjoint (β '' M j₁.succ) (β '' M j₂.succ) :=
        Set.disjoint_image_of_injective β.injective (hMdisj (fun h => hne (Fin.succ_injective k h)))
      exact hdisjS.preimage ψ
    have hM'_nonsep : IsPreconnected ((⋃ j : Fin k, M' j)ᶜ : Set Y) := by
      let U_S : Set S := (⋃ j : Fin (k + 1), β '' M j)ᶜ
      have hU_S_pre : IsPreconnected U_S := by
        have heq : U_S = β '' (⋃ j : Fin (k + 1), M j)ᶜ := by
          rw [Set.image_compl_eq β.bijective, Set.image_iUnion]
        rw [heq]; exact hnonsep.image β β.continuous.continuousOn
      have hU_S_sub : U_S ⊆ P₁ᶜ := fun x hx h0 => hx (mem_iUnion.mpr ⟨0, h0⟩)
      let eF := cutComplHomeo hψ hP₁cl
      let U_Y : Set Y := ψ ⁻¹' U_S
      have hU_Y_pre : IsPreconnected U_Y := by
        let subS : Set (P₁ᶜ : Set S) := Subtype.val ⁻¹' U_S
        have hsubS_pre : IsPreconnected subS := by
          rw [← IsEmbedding.subtypeVal.isPreconnected_image]
          have him : Subtype.val '' subS = U_S := by
            ext x; constructor
            · rintro ⟨⟨w, _⟩, hw, rfl⟩; exact hw
            · intro hx; exact ⟨⟨x, hU_S_sub hx⟩, hx, rfl⟩
          rwa [him]
        have h2 := (hsubS_pre.image eF.symm eF.symm.continuous.continuousOn).image Subtype.val continuous_subtype_val.continuousOn
        have him2 : Subtype.val '' (eF.symm '' subS) = U_Y := by
          ext y; constructor
          · rintro ⟨⟨w, hw⟩, ⟨⟨x, hx⟩, hxU, hwe⟩, rfl⟩
            show ψ w ∈ U_S
            have : ψ w = x := by
              have h := congrArg Subtype.val (eF.apply_symm_apply ⟨x, hx⟩)
              rw [hwe] at h; exact h
            rwa [this]
          · intro hy
            have hyP₁ : ψ y ∉ P₁ := hU_S_sub hy
            refine ⟨⟨y, hyP₁⟩, ⟨⟨ψ y, hyP₁⟩, hy, ?_⟩, rfl⟩
            exact eF.symm_apply_apply ⟨y, hyP₁⟩
        rwa [him2] at h2
      have hU_Y_eq : U_Y = (ψ ⁻¹' P₁ᶜ) ∩ (⋃ j : Fin k, M' j)ᶜ := by
        ext y; simp only [U_Y, U_S, M', mem_preimage, mem_compl_iff, mem_iUnion, mem_inter_iff, not_exists]
        constructor
        · intro h; exact ⟨h 0, fun j => h j.succ⟩
        · rintro ⟨h0, hs⟩ j; refine Fin.cases h0 hs j
      have hopen_compl : IsOpen ((⋃ j : Fin k, M' j)ᶜ : Set Y) :=
        (isClosed_iUnion_of_finite fun j => by
          obtain ⟨_, _, _, hl, _⟩ := hM' j; exact hl.isCompact.isClosed).isOpen_compl
      have hsub_cl : (⋃ j : Fin k, M' j)ᶜ ⊆ closure U_Y := by
        intro y hy
        rw [hU_Y_eq, _root_.mem_closure_iff]
        intro V hVo hyV
        obtain ⟨z, ⟨hzV, hzO⟩, hzD⟩ := _root_.mem_closure_iff.mp (dense_cut_compl hY hψ y)
          (V ∩ (⋃ j : Fin k, M' j)ᶜ) (hVo.inter hopen_compl) ⟨hyV, hy⟩
        exact ⟨z, hzV, hzD, hzO⟩
      exact hU_Y_pre.subset_closure (hU_Y_eq ▸ inter_subset_right) hsub_cl
    -- Step 4: Split each `L i` along `P₁` into `d i + 1 ≤ 3` pairwise disjoint proper `I`-arcs in `Y`
    choose uL vL huvL hLl hLb using hL
    let d : Fin m → ℕ := fun i => (P₁ ∩ L i).ncard
    have hsplit_ex : ∀ i : Fin m,
        ∃ (pieces : Fin (d i + 1) → Set Y),
          (∀ r, ∃ u' v' : Y, u' ≠ v' ∧ IsLineWithEnds (pieces r) u' v' ∧ pieces r ∩ bd Y = {u', v'}) ∧
          (Pairwise fun r₁ r₂ => Disjoint (pieces r₁) (pieces r₂)) ∧
          (∀ r, pieces r ⊆ ψ ⁻¹' L i) ∧
          (ψ ⁻¹' (L i \ P₁) ⊆ ⋃ r, pieces r) ∧
          (∀ r, pieces r ∩ bd Y ⊆ ψ ⁻¹' (P₁ ∪ {uL i, vL i})) := fun i => by
      have huP₁ : uL i ∉ P₁ := fun h => by
        have hubd : uL i ∈ L i ∩ bd S := hLb i ▸ Or.inl rfl
        have h1 : uL i ∈ P₁ ∩ bd S := ⟨h, hubd.2⟩
        rw [hP₁b] at h1
        rcases h1 with rfl | hEq
        · exact hs0L i hubd.1
        · exact ht0L i ((mem_singleton_iff.mp hEq) ▸ hubd.1)
      have hvP₁ : vL i ∉ P₁ := fun h => by
        have hvbd : vL i ∈ L i ∩ bd S := hLb i ▸ Or.inr rfl
        have h1 : vL i ∈ P₁ ∩ bd S := ⟨h, hvbd.2⟩
        rw [hP₁b] at h1
        rcases h1 with rfl | hEq
        · exact hs0L i hvbd.1
        · exact ht0L i ((mem_singleton_iff.mp hEq) ▸ hvbd.1)
      exact split_transverse_iArc hY hS hψ hP₁cl (huvL i) (hLl i) (hLb i) huP₁ hvP₁
        (hβcross i).1 (hβcross i).2.2
    choose pieces hpieces_arc hpieces_disj hpieces_sub hpieces_cov hpieces_bd using hsplit_ex
    let eL : (Σ i : Fin m, Fin (d i + 1)) ≃ Fin (Fintype.card (Σ i : Fin m, Fin (d i + 1))) :=
      Fintype.equivFin (Σ i : Fin m, Fin (d i + 1))
    let m' := Fintype.card (Σ i : Fin m, Fin (d i + 1))
    let L' : Fin m' → Set Y := fun idx => pieces (eL.symm idx).1 (eL.symm idx).2
    have hL' : ∀ idx : Fin m', ∃ u' v' : Y, u' ≠ v' ∧ IsLineWithEnds (L' idx) u' v' ∧ L' idx ∩ bd Y = {u', v'} :=
      fun idx => hpieces_arc (eL.symm idx).1 (eL.symm idx).2
    have hL'disj : Pairwise fun idx₁ idx₂ : Fin m' => Disjoint (L' idx₁) (L' idx₂) := fun idx₁ idx₂ hne => by
      have hne' : eL.symm idx₁ ≠ eL.symm idx₂ := fun h => hne (eL.symm.injective h)
      by_cases hi : (eL.symm idx₁).1 = (eL.symm idx₂).1
      · rcases h1 : eL.symm idx₁ with ⟨i₁, r₁⟩
        rcases h2 : eL.symm idx₂ with ⟨i₂, r₂⟩
        rw [h1, h2] at hi hne'; dsimp only at hi; subst hi
        have hr : r₁ ≠ r₂ := fun h => hne' (by subst h; rfl)
        have hL1 : L' idx₁ = pieces i₁ r₁ := by dsimp only [L']; rw [h1]
        have hL2 : L' idx₂ = pieces i₁ r₂ := by dsimp only [L']; rw [h2]
        dsimp only; rw [hL1, hL2]; exact hpieces_disj i₁ hr
      · exact ((hLdisj hi).preimage ψ).mono (hpieces_sub _ _) (hpieces_sub _ _)
    have hbd'_disj : ∀ j idx, Disjoint (M' j ∩ bd Y) (L' idx ∩ bd Y) := by
      intro j idx
      rw [Set.disjoint_left]; intro y hyM hyL
      have h1 : ψ y ∈ (β '' M j.succ) ∩ bd S := by
        obtain ⟨s, t, -, -, hMb, hdisj⟩ := hβM_arc j
        have hnotP₁ : ψ y ∉ P₁ := Set.disjoint_left.mp hdisj hyM.1
        exact ⟨hyM.1, (mem_bd_cut_iff hY hS hψ hP₁cl hnotP₁).mp hyM.2⟩
      have h1' : ψ y ∈ M j.succ ∩ bd S := by
        obtain ⟨z, hzM, hze⟩ := h1.1
        have hzeq : β z = z := β.injective (hβfix (β z) (hze ▸ h1.2))
        have hzbd : z ∈ bd S := hzeq ▸ hze ▸ h1.2
        rw [← hze, hzeq]; exact ⟨hzM, hzbd⟩
      have h2 : ψ y ∈ P₁ ∪ {uL (eL.symm idx).1, vL (eL.symm idx).1} := hpieces_bd _ _ hyL
      rcases h2 with hP₁m | huv_m
      · obtain ⟨-, -, -, -, -, hdisj⟩ := hβM_arc j
        exact Set.disjoint_left.mp hdisj hyM.1 hP₁m
      · have hLbd : ψ y ∈ L (eL.symm idx).1 ∩ bd S := (hLb (eL.symm idx).1).symm ▸ huv_m
        exact Set.disjoint_left.mp (hbd_disj j.succ (eL.symm idx).1) h1' hLbd
    -- Step 5: Apply IH on `Y`, descend `G` to `γ : S ≃ₜ S`, and compose `φ := β.trans γ`
    obtain ⟨G, hGfix, hGfin, hGsimple, hGsum⟩ := ih hY hM' hM'disj hM'_nonsep hL' hL'disj hbd'_disj
    obtain ⟨γ, hγψ⟩ := exists_descend_cut hψ G fun z hz => hGfix z (hψ.2.2.2.2 hz)
    have hγfix : ∀ x ∈ bd S, γ x = x := fun x hx => by
      obtain ⟨y, rfl⟩ := hψ.2.1 x
      have hybd : y ∈ bd Y := by
        by_cases hF' : ψ y ∈ P₁
        · exact hψ.2.2.2.2 hF'
        · exact (mem_bd_cut_iff hY hS hψ hP₁cl hF').mpr hx
      rw [hγψ y, hGfix y hybd]
    have hγP₁ : ∀ x ∈ P₁, γ x = x := fun x hx => by
      obtain ⟨y, rfl⟩ := hψ.2.1 x
      rw [hγψ y, hGfix y (hψ.2.2.2.2 hx)]
    let φ : S ≃ₜ S := β.trans γ
    have hφfix : ∀ x ∈ bd S, φ x = x := fun x hx => by
      simp only [φ, Homeomorph.trans_apply, hβfix x hx, hγfix x hx]
    have hφM0 : φ '' M 0 = P₁ := by
      change (γ ∘ β) '' M 0 = P₁
      rw [Set.image_comp]
      ext x; constructor
      · rintro ⟨z, hz, rfl⟩; rwa [hγP₁ z hz]
      · intro hx; exact ⟨x, hx, hγP₁ x hx⟩
    have hφMsucc : ∀ j : Fin k, φ '' M j.succ = ψ '' (G '' M' j) := fun j => by
      change (γ ∘ β) '' M j.succ = ψ '' (G '' (ψ ⁻¹' (β '' M j.succ)))
      rw [Set.image_comp, ← Set.image_comp (f := ψ) (g := G)]
      have heq : (ψ ∘ G) '' (ψ ⁻¹' (β '' M j.succ)) = (γ ∘ ψ) '' (ψ ⁻¹' (β '' M j.succ)) := by
        congr 1; funext y; exact (hγψ y).symm
      rw [heq, Set.image_comp, Set.image_preimage_eq _ hψ.2.1]
    have hφMsucc_inter : ∀ (j : Fin k) (i : Fin m),
        φ '' M j.succ ∩ L i = ⋃ r : Fin (d i + 1), ψ '' (G '' M' j ∩ pieces i r) := by
      intro j i
      ext x; constructor
      · rintro ⟨hxM, hxL⟩
        have hxnotP₁ : x ∉ P₁ := by
          obtain ⟨z, hzM, rfl⟩ := hxM
          intro hP₁m
          have h1 : β z ∈ P₁ := by
            have : γ (β z) = γ (γ (β z)) := (hγP₁ _ hP₁m).symm
            have h2 := γ.injective (hγP₁ (γ (β z)) hP₁m)
            exact h2 ▸ hP₁m
          obtain ⟨-, -, -, -, -, hdisj⟩ := hβM_arc j
          exact Set.disjoint_left.mp hdisj ⟨z, hzM, rfl⟩ h1
        rw [hφMsucc j] at hxM
        obtain ⟨y, hyG, rfl⟩ := hxM
        have hy_cov : y ∈ ⋃ r : Fin (d i + 1), pieces i r := hpieces_cov i ⟨hxL, hxnotP₁⟩
        obtain ⟨r, hyr⟩ := mem_iUnion.mp hy_cov
        exact mem_iUnion.mpr ⟨r, y, ⟨hyG, hyr⟩, rfl⟩
      · intro hx
        obtain ⟨r, y, ⟨hyG, hyr⟩, rfl⟩ := mem_iUnion.mp hx
        exact ⟨hφMsucc j ▸ ⟨y, hyG, rfl⟩, hpieces_sub i r hyr⟩
    have hφfin : ∀ j i, (φ '' M j ∩ L i).Finite := by
      intro j i
      refine Fin.cases ?_ (fun j' => ?_) j
      · rw [hφM0]; exact (hβcross i).1
      · rw [hφMsucc_inter j' i]
        exact Set.finite_iUnion fun r => (hGfin j' (eL ⟨i, r⟩)).image ψ |>.subset (by
          dsimp only [L']; rw [Equiv.symm_apply_apply])
    -- Step 6: Crossing count bound
    have hsum_succ : (∑ j' : Fin k, ∑ i : Fin m, (φ '' M j'.succ ∩ L i).ncard) ≤ m' * (3 ^ k - 1) := by
      calc (∑ j' : Fin k, ∑ i : Fin m, (φ '' M j'.succ ∩ L i).ncard)
          ≤ ∑ j' : Fin k, ∑ i : Fin m, ∑ r : Fin (d i + 1), (G '' M' j' ∩ pieces i r).ncard := by
            refine Finset.sum_le_sum fun j' _ => Finset.sum_le_sum fun i _ => ?_
            rw [hφMsucc_inter j' i]
            have h1 : ∀ (s : Finset (Fin (d i + 1))),
                (⋃ r ∈ s, ψ '' (G '' M' j' ∩ pieces i r)).ncard ≤
                  ∑ r ∈ s, (ψ '' (G '' M' j' ∩ pieces i r)).ncard := by
              intro s
              induction s using Finset.induction_on with
              | empty => simp
              | insert a s ha ihs =>
                rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
                exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left ihs _)
            have h2 : (⋃ r : Fin (d i + 1), ψ '' (G '' M' j' ∩ pieces i r)).ncard ≤
                ∑ r : Fin (d i + 1), (ψ '' (G '' M' j' ∩ pieces i r)).ncard := by
              simpa only [Finset.mem_univ, iUnion_true] using h1 Finset.univ
            exact h2.trans (Finset.sum_le_sum fun r _ =>
              Set.ncard_image_le ((hGfin j' (eL ⟨i, r⟩)).subset (by dsimp only [L']; rw [Equiv.symm_apply_apply])))
        _ = ∑ j' : Fin k, ∑ idx : Fin m', (G '' M' j' ∩ L' idx).ncard := by
            refine Finset.sum_congr rfl fun j' _ => ?_
            rw [← Fintype.sum_sigma (fun p : Σ i : Fin m, Fin (d i + 1) => (G '' M' j' ∩ pieces p.1 p.2).ncard)]
            exact Fintype.sum_equiv eL _ _ fun p => by dsimp only [L']; rw [Equiv.symm_apply_apply]
        _ ≤ m' * (3 ^ k - 1) := hGsum
    have hm'_le : m' ≤ 3 * m := by
      have hm'_eq : m' = ∑ i : Fin m, (d i + 1) := by
        simp only [m', Fintype.card_sigma, Fintype.card_fin]
      rw [hm'_eq]
      calc (∑ i : Fin m, (d i + 1)) ≤ ∑ _i : Fin m, 3 :=
            Finset.sum_le_sum fun i _ => by
              change (β '' M 0 ∩ L i).ncard + 1 ≤ 3
              have := (hβcross i).2.1; omega
        _ = 3 * m := by simp [mul_comm]
    have hsum_0 : (∑ i : Fin m, (φ '' M 0 ∩ L i).ncard) ≤ 2 * m := by
      calc (∑ i : Fin m, (φ '' M 0 ∩ L i).ncard)
          = ∑ i : Fin m, d i := Finset.sum_congr rfl fun i _ => by rw [hφM0]
        _ ≤ ∑ _i : Fin m, 2 := Finset.sum_le_sum fun i _ => (hβcross i).2.1
        _ = 2 * m := by simp [mul_comm]
    have htotal : (∑ j : Fin (k + 1), ∑ i : Fin m, (φ '' M j ∩ L i).ncard) ≤ m * (3 ^ (k + 1) - 1) := by
      rw [Fin.sum_univ_succ]
      have hpow : 1 ≤ 3 ^ k := Nat.one_le_pow k 3 (by norm_num)
      have harith : 2 * m + 3 * m * (3 ^ k - 1) = m * (3 ^ (k + 1) - 1) := by
        zify [hpow, show 1 ≤ 3 ^ (k + 1) from Nat.one_le_pow (k + 1) 3 (by norm_num)]
        ring
      calc (∑ i : Fin m, (φ '' M 0 ∩ L i).ncard) +
            (∑ j' : Fin k, ∑ i : Fin m, (φ '' M j'.succ ∩ L i).ncard)
          ≤ 2 * m + m' * (3 ^ k - 1) := Nat.add_le_add hsum_0 hsum_succ
        _ ≤ 2 * m + (3 * m) * (3 ^ k - 1) := Nat.add_le_add_left (Nat.mul_le_mul_right _ hm'_le) _
        _ = m * (3 ^ (k + 1) - 1) := harith
    have hφsimple : ∀ j i, IsSimpleCrossing (φ '' M j) (L i) := by
      intro j i
      refine Fin.cases ?_ (fun j' => ?_) j
      · rw [hφM0]; exact (hβcross i).2.2
      · intro p ⟨hpM, hpL⟩
        have hp_inter : p ∈ ⋃ r : Fin (d i + 1), ψ '' (G '' M' j' ∩ pieces i r) :=
          hφMsucc_inter j' i ▸ ⟨hpM, hpL⟩
        obtain ⟨r, y, ⟨hyG, hyr⟩, rfl⟩ := mem_iUnion.mp hp_inter
        have hynotP₁ : ψ y ∉ P₁ := by
          obtain ⟨z, hzM, hze⟩ := hpM
          intro hP₁m
          have h1 : β z ∈ P₁ := by
            have h2 := γ.injective (hγP₁ (γ (β z)) (hze ▸ hP₁m))
            exact h2 ▸ hze ▸ hP₁m
          obtain ⟨-, -, -, -, -, hdisj⟩ := hβM_arc j'
          exact Set.disjoint_left.mp hdisj ⟨z, hzM, rfl⟩ h1
        have hidx_eq : L' (eL ⟨i, r⟩) = pieces i r := by dsimp only [L']; rw [Equiv.symm_apply_apply]
        obtain ⟨g, ε, hε, hgc, hgi, hVo, hgint, hg0, hMbox, hLbox⟩ :=
          hGsimple j' (eL ⟨i, r⟩) y ⟨hyG, hidx_eq.symm ▸ hyr⟩
        rw [hidx_eq] at hLbox
        -- Shrink `ε` so the box avoids `ψ ⁻¹' P₁` and all other `pieces i r'` (`r' ≠ r`):
        let Z : Set Y := ψ ⁻¹' P₁ ∪ ⋃ (r' : Fin (d i + 1)) (_ : r' ≠ r), pieces i r'
        have hZcl : IsClosed Z := (hP₁cl.preimage hψ.1).union
          (isClosed_iUnion_of_finite fun r' => isClosed_iUnion_of_finite fun _ => by
            obtain ⟨_, _, _, hl, _⟩ := hpieces_arc i r'; exact hl.isCompact.isClosed)
        have hyZ : y ∉ Z := by
          rintro (h1 | h2)
          · exact hynotP₁ h1
          · obtain ⟨r', hne, hyr'⟩ := mem_iUnion₂.mp h2
            exact Set.disjoint_left.mp (hpieces_disj i hne) hyr' hyr
        have h0_nhd : g ⁻¹' Zᶜ ∈ 𝓝[Icc (-ε) ε ×ℂ Icc (-ε) ε] (0 : ℂ) :=
          (hgc 0 (Complex.mem_reProdIm.mpr ⟨by simp [hε.le], by simp [hε.le]⟩)).preimage_mem_nhdsWithin
            (hZcl.isOpen_compl.mem_nhds (hg0.symm ▸ hyZ))
        obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp h0_nhd
        let ε' := min (ε / 2) (δ / 2)
        have hε' : 0 < ε' := lt_min (half_pos hε) (half_pos hδ)
        have hε'_le : ε' ≤ ε := (min_le_left _ _).trans (half_le_self hε.le)
        have hsub_sq : Icc (-ε') ε' ×ℂ Icc (-ε') ε' ⊆ Icc (-ε) ε ×ℂ Icc (-ε) ε := fun w hw => by
          have hw' := Complex.mem_reProdIm.mp hw
          exact Complex.mem_reProdIm.mpr ⟨⟨by linarith [hw'.1.1], by linarith [hw'.1.2]⟩,
            ⟨by linarith [hw'.2.1], by linarith [hw'.2.2]⟩⟩
        have hsub_Z : ∀ w ∈ Icc (-ε') ε' ×ℂ Icc (-ε') ε', g w ∉ Z := fun w hw => by
          have hw' := Complex.mem_reProdIm.mp hw
          have hnorm : ‖w‖ < δ := by
            have h1 : |w.re| ≤ ε' := abs_le.mpr hw'.1
            have h2 : |w.im| ≤ ε' := abs_le.mpr hw'.2
            have h3 : ε' ≤ δ / 2 := min_le_right _ _
            have h4 : ‖w‖ ≤ |w.re| + |w.im| := by
              have := Complex.norm_le_abs_re_add_abs_im w; exact this
            have : |w.re| + |w.im| ≤ 2 * ε' := by linarith
            -- wait: `2 * ε' ≤ δ`, might be equal! Use `ε' = min (ε / 2) (δ / 3)`!
            linarith [show ‖w‖ < δ from by
              have hsq : w.re ^ 2 + w.im ^ 2 ≤ 2 * ε' ^ 2 := by nlinarith [abs_le.mp h1, abs_le.mp h2]
              have hle : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
              nlinarith [norm_nonneg w]]
          exact hδsub ⟨by rwa [mem_ball_zero_iff], hsub_sq hw⟩
        have hψg_inj : InjOn (ψ ∘ g) (Icc (-ε') ε' ×ℂ Icc (-ε') ε') := fun w₁ hw₁ w₂ hw₂ he => by
          have h1 : g w₁ ∉ ψ ⁻¹' P₁ := fun h => hsub_Z w₁ hw₁ (Or.inl h)
          have h2 : g w₂ ∉ ψ ⁻¹' P₁ := fun h => hsub_Z w₂ hw₂ (Or.inl h)
          exact hgi (hsub_sq hw₁) (hsub_sq hw₂) (hψ.2.2.1 h1 h2 he)
        have hψg_cont : ContinuousOn (ψ ∘ g) (Icc (-ε') ε' ×ℂ Icc (-ε') ε') :=
          hψ.1.comp_continuousOn (hgc.mono hsub_sq)
        have hsub_oo' : Ioo (-ε') ε' ×ℂ Ioo (-ε') ε' ⊆ Icc (-ε') ε' ×ℂ Icc (-ε') ε' := fun w hw =>
          Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hw).1,
            Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hw).2⟩
        have hopen' : IsOpen ((ψ ∘ g) '' (Ioo (-ε') ε' ×ℂ Ioo (-ε') ε')) :=
          isOpen_image_of_manifold (isOpen_Ioo.reProdIm isOpen_Ioo) (hψg_cont.mono hsub_oo')
            (hψg_inj.mono hsub_oo') (fun _ _ => hS.2.2 _)
        refine ⟨ψ ∘ g, ε', hε', hψg_cont, hψg_inj, hopen', ?_, by simp [hg0], ?_, ?_⟩
        · rintro _ ⟨w, hw, rfl⟩ hbd
          have hnotP₁ : ψ (g w) ∉ P₁ := fun h => hsub_Z w hw (Or.inl h)
          exact hgint ⟨w, hsub_sq hw, rfl⟩ ((mem_bd_cut_iff hY hS hψ hP₁cl hnotP₁).mpr hbd)
        · ext x; constructor
          · rintro ⟨hxM, w, hw, rfl⟩
            have hnotP₁ : ψ (g w) ∉ P₁ := fun h => hsub_Z w hw (Or.inl h)
            rw [hφMsucc j'] at hxM; obtain ⟨y', hy'G, hy'e⟩ := hxM
            have hy'_eq : y' = g w := hψ.2.2.1 (show ψ y' ∉ P₁ by rw [hy'e]; exact hnotP₁) hnotP₁ hy'e
            have h1 : g w ∈ G '' M' j' ∩ g '' (Icc (-ε) ε ×ℂ Icc (-ε) ε) := ⟨hy'_eq ▸ hy'G, w, hsub_sq hw, rfl⟩
            rw [hMbox] at h1; obtain ⟨u, hu, hue⟩ := h1
            have hu_eq : u = w := hgi (by
              have hu' := Complex.mem_reProdIm.mp hu
              exact Complex.mem_reProdIm.mpr ⟨hu'.1, by rw [mem_singleton_iff.mp hu'.2]; exact ⟨by linarith, hε.le⟩⟩)
              (hsub_sq hw) hue
            rw [hu_eq] at hu
            exact ⟨w, Complex.mem_reProdIm.mpr ⟨(Complex.mem_reProdIm.mp hw).1, (Complex.mem_reProdIm.mp hu).2⟩, rfl⟩
          · rintro ⟨w, hw, rfl⟩
            have hw' := Complex.mem_reProdIm.mp hw
            have hw_sq : w ∈ Icc (-ε') ε' ×ℂ Icc (-ε') ε' :=
              Complex.mem_reProdIm.mpr ⟨hw'.1, by rw [mem_singleton_iff.mp hw'.2]; exact ⟨by linarith, hε'.le⟩⟩
            have hgwG : g w ∈ G '' M' j' := (show g w ∈ G '' M' j' ∩ g '' (Icc (-ε) ε ×ℂ Icc (-ε) ε) by
              rw [hMbox]; exact ⟨w, Complex.mem_reProdIm.mpr ⟨⟨by linarith [hw'.1.1], by linarith [hw'.1.2]⟩, hw'.2⟩, rfl⟩).1
            exact ⟨hφMsucc j' ▸ ⟨g w, hgwG, rfl⟩, w, hw_sq, rfl⟩
        · ext x; constructor
          · rintro ⟨hxL, w, hw, rfl⟩
            have hnotP₁ : ψ (g w) ∉ P₁ := fun h => hsub_Z w hw (Or.inl h)
            have hcov := hpieces_cov i ⟨hxL, hnotP₁⟩
            obtain ⟨r', hgw_r'⟩ := mem_iUnion.mp hcov
            have hr'_eq : r' = r := by
              by_contra hne
              exact hsub_Z w hw (Or.inr (mem_iUnion₂.mpr ⟨r', hne, hgw_r'⟩))
            rw [hr'_eq] at hgw_r'
            have h1 : g w ∈ pieces i r ∩ g '' (Icc (-ε) ε ×ℂ Icc (-ε) ε) := ⟨hgw_r', w, hsub_sq hw, rfl⟩
            rw [hLbox] at h1; obtain ⟨u, hu, hue⟩ := h1
            have hu_eq : u = w := hgi (by
              have hu' := Complex.mem_reProdIm.mp hu
              exact Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hu'.1]; exact ⟨by linarith, hε.le⟩, hu'.2⟩)
              (hsub_sq hw) hue
            rw [hu_eq] at hu
            exact ⟨w, Complex.mem_reProdIm.mpr ⟨(Complex.mem_reProdIm.mp hu).1, (Complex.mem_reProdIm.mp hw).2⟩, rfl⟩
          · rintro ⟨w, hw, rfl⟩
            have hw' := Complex.mem_reProdIm.mp hw
            have hw_sq : w ∈ Icc (-ε') ε' ×ℂ Icc (-ε') ε' :=
              Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hw'.1]; exact ⟨by linarith, hε'.le⟩, hw'.2⟩
            have hgw_r : g w ∈ pieces i r := (show g w ∈ pieces i r ∩ g '' (Icc (-ε) ε ×ℂ Icc (-ε) ε) by
              rw [hLbox]; exact ⟨w, Complex.mem_reProdIm.mpr ⟨hw'.1, ⟨by linarith [hw'.2.1], by linarith [hw'.2.2]⟩⟩, rfl⟩).1
            exact ⟨hpieces_sub i r hgw_r, w, hw_sq, rfl⟩
    exact ⟨φ, hφfix, hφfin, hφsimple, htotal⟩

end GraphMinor.GHR18
