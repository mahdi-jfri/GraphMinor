module

public import GraphMinor.LPPS22.CutToDisc

/-!
# Lokshtanov–Pilipczuk–Pilipczuk–Saurabh (2022), Appendix A, Lemma A.3

Given a connected compact surface `S ≃ₜ SurfaceModel a b c` with `1 ≤ c`, and two matchings
`G : Fin n → Set S` and `L : Fin m → Set S` of pairwise disjoint proper `I`-arcs with disjoint
boundary endpoints, there exists a boundary-fixing homeomorphism `φ : S ≃ₜ S` such that
`φ '' L i ∩ G j` is finite for all `i, j` and
```
  ∑ i : Fin m, ∑ j : Fin n, (φ '' L i ∩ G j).ncard ≤ m * 3 ^ (2 * n + 3 * (2 * a + b) + c).
```

## Proof
1. Apply `exists_disc_cutting_matching` (`CutToDisc.lean`) to extend a subset `G₀ ⊆ G` by new
   arcs `N₁` (disjoint from `G` and avoiding `L ∩ bd S`) to a non-separating matching `N` of size
   `r = 2 * a + b + c - 1`.
2. Apply `ghr18_theorem_1_3` (`Theorem13.lean`) to `N` and `L`, giving a boundary-fixing
   homeomorphism `β` so that `L₁ := β.symm '' L` meets `N` in at most `m * (3 ^ r - 1)` simple
   crossings.
3. Induct on `r` (`descend_disc_matching_over_cut_system`): cut `S` sequentially along `N 0, ...,
   N (r - 1)`, splitting `L₁` at each step via `split_transverse_iArc` into a total of
   `m₁' ≤ m + ∑ k, ∑ i, (N k ∩ L₁ i).ncard ≤ m * 3 ^ r` chords in the resulting closed disc
   `SurfaceModel 0 0 1 ≃ₜ closedBall (0 : ℂ) 1`, while lifting `G_rem := G \ G₀` (`≤ n` arcs)
   into the same closed disc.
4. Apply `lpps22_disc_matching` (`DiscMatching.lean`) in the closed disc, and descend across the
   `r` cuts via `exists_descend_cut` to obtain `γ : S ≃ₜ S` fixing `bd S` and fixing every `N k`
   pointwise.
5. Compose `φ := β.symm.trans γ`. The total crossing count is at most
   `m * (3 ^ r - 1) + m * 3 ^ r * n ≤ m * (n + 1) * 3 ^ r ≤ m * 3 ^ (2 * n + 3 * (2 * a + b) + c)`.
-/

@[expose] public section

namespace GraphMinor.LPPS22

open Set Topology Metric Complex Function GraphMinor.Surface GraphMinor.GHR18

/-! ### Section 1: Transporting `IsSimpleCrossing` across homeomorphisms and cuts -/

/-- `IsSimpleCrossing` is preserved under a homeomorphism of `S`. -/
private theorem isSimpleCrossing_image_homeo {S : Type} [TopologicalSpace S]
    (_hS : IsSurface S) (α : S ≃ₜ S) {A B : Set S} (h : IsSimpleCrossing A B) :
    IsSimpleCrossing (α '' A) (α '' B) := by
  intro p ⟨hpA, hpB⟩
  obtain ⟨q, hqA, hqe⟩ := hpA
  have hqB : q ∈ B := by obtain ⟨q', hq'B, hq'e⟩ := hpB; exact α.injective (hq'e.trans hqe.symm) ▸ hq'B
  obtain ⟨g, ε, hε, hgc, hgi, hVo, hgint, hg0, hAbox, hBbox⟩ := h q ⟨hqA, hqB⟩
  refine ⟨α ∘ g, ε, hε, α.continuous.comp_continuousOn hgc, α.injective.comp_injOn hgi, ?_, ?_,
    by simp [hg0, hqe], ?_, ?_⟩
  · rw [Set.image_comp]; exact α.isOpenMap _ hVo
  · rintro _ ⟨w, hw, rfl⟩ hbd
    have hqbd : g w ∈ bd S := by
      have him := image_bd_homeomorph α.symm
      exact him ▸ ⟨α (g w), hbd, α.symm_apply_apply _⟩
    exact hgint ⟨w, hw, rfl⟩ hqbd
  · rw [Set.image_comp (f := α), Set.image_comp (f := α), ← Set.image_inter α.injective, hAbox]
  · rw [Set.image_comp (f := α), Set.image_comp (f := α), ← Set.image_inter α.injective, hBbox]

/-- Lifting `IsSimpleCrossing` across a cut `ψ : Y → S` along `F` when `A` is disjoint from `F`
and `piece ⊆ ψ ⁻¹' B` is one piece of a disjoint splitting of `B \ F`. -/
private theorem isSimpleCrossing_lift_cut {S Y : Type} [TopologicalSpace S] [TopologicalSpace Y] [T2Space Y]
    (hS : IsSurface S) (hY : IsSurface Y) {ψ : Y → S} {F : Set S}
    (hψ : IsCutting ψ F) (hFcl : IsClosed F)
    {A B : Set S} (hdisj : Disjoint A F) (hsimple : IsSimpleCrossing A B)
    {d : ℕ} {pieces : Fin (d + 1) → Set Y}
    (hpieces_cl : ∀ r, IsClosed (pieces r))
    (hpieces_disj : Pairwise fun r₁ r₂ => Disjoint (pieces r₁) (pieces r₂))
    (hpieces_sub : ∀ r, pieces r ⊆ ψ ⁻¹' B)
    (hpieces_cov : ψ ⁻¹' (B \ F) ⊆ ⋃ r, pieces r)
    (r : Fin (d + 1)) :
    IsSimpleCrossing (ψ ⁻¹' A) (pieces r) := by
  classical
  have : CompactSpace Y := hY.1
  have : T2Space S := hS.2.1
  let eF := cutComplHomeo hψ hFcl
  intro y ⟨hyA, hyr⟩
  have hynotF : ψ y ∉ F := Set.disjoint_left.mp hdisj hyA
  have hyB : ψ y ∈ B := hpieces_sub r hyr
  obtain ⟨g, ε, hε, hgc, hgi, hVo, hgint, hg0, hAbox, hBbox⟩ := hsimple (ψ y) ⟨hyA, hyB⟩
  -- Shrink `ε` so `g '' Rsq' ⊆ Fᶜ` and `(eF.symm ∘ g) '' Rsq'` avoids all other `pieces r'` (`r' ≠ r`):
  have h0_nhdF : g ⁻¹' Fᶜ ∈ 𝓝[Icc (-ε) ε ×ℂ Icc (-ε) ε] (0 : ℂ) :=
    (hgc 0 (Complex.mem_reProdIm.mpr ⟨by simp [hε.le], by simp [hε.le]⟩)).preimage_mem_nhdsWithin
      (hFcl.isOpen_compl.mem_nhds (hg0.symm ▸ hynotF))
  obtain ⟨δ₁, hδ₁, hδ₁sub⟩ := Metric.mem_nhdsWithin_iff.mp h0_nhdF
  let ε₁ := min (ε / 2) (δ₁ / 3)
  have hε₁ : 0 < ε₁ := lt_min (half_pos hε) (by positivity)
  have hsub₁ : Icc (-ε₁) ε₁ ×ℂ Icc (-ε₁) ε₁ ⊆ Icc (-ε) ε ×ℂ Icc (-ε) ε := fun w hw => by
    have hw' := Complex.mem_reProdIm.mp hw
    have hle : ε₁ ≤ ε := (min_le_left _ _).trans (half_le_self hε.le)
    exact Complex.mem_reProdIm.mpr ⟨⟨by linarith [hw'.1.1], by linarith [hw'.1.2]⟩,
      ⟨by linarith [hw'.2.1], by linarith [hw'.2.2]⟩⟩
  have hsub₁_F : ∀ w ∈ Icc (-ε₁) ε₁ ×ℂ Icc (-ε₁) ε₁, g w ∈ Fᶜ := fun w hw => by
    have hw' := Complex.mem_reProdIm.mp hw
    have hnorm : ‖w‖ < δ₁ := by
      have h1 : |w.re| ≤ ε₁ := abs_le.mpr hw'.1
      have h2 : |w.im| ≤ ε₁ := abs_le.mpr hw'.2
      have h3 : ε₁ ≤ δ₁ / 3 := min_le_right _ _
      have h4 : ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
      linarith
    exact hδ₁sub ⟨by rwa [mem_ball_zero_iff], hsub₁ hw⟩
  let gY : ℂ → Y := fun w => if hw : w ∈ Icc (-ε₁) ε₁ ×ℂ Icc (-ε₁) ε₁ then (eF.symm ⟨g w, hsub₁_F w hw⟩).1 else y
  have hgY_cont : ContinuousOn gY (Icc (-ε₁) ε₁ ×ℂ Icc (-ε₁) ε₁) := by
    rw [continuousOn_iff_continuous_domRestrict]
    let g1 : (Icc (-ε₁) ε₁ ×ℂ Icc (-ε₁) ε₁ : Set ℂ) → (Fᶜ : Set S) := fun w => ⟨g w.1, hsub₁_F w.1 w.2⟩
    have hg1c : Continuous g1 := Continuous.subtype_mk
      (continuousOn_iff_continuous_domRestrict.mp (hgc.mono hsub₁)) _
    exact (continuous_subtype_val.comp (eF.symm.continuous.comp hg1c)).congr fun w => by
      simp only [Set.domRestrict, Function.comp, gY, g1, dite_eq_left w.2]
  have hgY_ψ : ∀ w ∈ Icc (-ε₁) ε₁ ×ℂ Icc (-ε₁) ε₁, ψ (gY w) = g w := fun w hw => by
    simp only [gY, dite_eq_left hw]
    exact congrArg Subtype.val (eF.apply_symm_apply ⟨g w, hsub₁_F w hw⟩)
  have hgY_0 : gY 0 = y := by
    have h0m : (0 : ℂ) ∈ Icc (-ε₁) ε₁ ×ℂ Icc (-ε₁) ε₁ := Complex.mem_reProdIm.mpr ⟨by simp [hε₁.le], by simp [hε₁.le]⟩
    have hψe : ψ (gY 0) = ψ y := (hgY_ψ 0 h0m).trans hg0
    exact hψ.2.2.1 (show ψ (gY 0) ∉ F by rw [hψe]; exact hynotF) hynotF hψe
  let Z : Set Y := ⋃ (r' : Fin (d + 1)) (_ : r' ≠ r), pieces r'
  have hZcl : IsClosed Z := isClosed_iUnion_of_finite fun r' => isClosed_iUnion_of_finite fun _ => hpieces_cl r'
  have hyZ : y ∉ Z := fun h => by
    obtain ⟨r', hne, hyr'⟩ := mem_iUnion₂.mp h
    exact Set.disjoint_left.mp (hpieces_disj hne) hyr' hyr
  have h0_nhdZ : gY ⁻¹' Zᶜ ∈ 𝓝[Icc (-ε₁) ε₁ ×ℂ Icc (-ε₁) ε₁] (0 : ℂ) :=
    (hgY_cont 0 (Complex.mem_reProdIm.mpr ⟨by simp [hε₁.le], by simp [hε₁.le]⟩)).preimage_mem_nhdsWithin
      (hZcl.isOpen_compl.mem_nhds (hgY_0.symm ▸ hyZ))
  obtain ⟨δ₂, hδ₂, hδ₂sub⟩ := Metric.mem_nhdsWithin_iff.mp h0_nhdZ
  let ε' := min (ε₁ / 2) (δ₂ / 3)
  have hε' : 0 < ε' := lt_min (half_pos hε₁) (by positivity)
  have hsub₂ : Icc (-ε') ε' ×ℂ Icc (-ε') ε' ⊆ Icc (-ε₁) ε₁ ×ℂ Icc (-ε₁) ε₁ := fun w hw => by
    have hw' := Complex.mem_reProdIm.mp hw
    have hle : ε' ≤ ε₁ := (min_le_left _ _).trans (half_le_self hε₁.le)
    exact Complex.mem_reProdIm.mpr ⟨⟨by linarith [hw'.1.1], by linarith [hw'.1.2]⟩,
      ⟨by linarith [hw'.2.1], by linarith [hw'.2.2]⟩⟩
  have hsub₂_Z : ∀ w ∈ Icc (-ε') ε' ×ℂ Icc (-ε') ε', gY w ∉ Z := fun w hw => by
    have hw' := Complex.mem_reProdIm.mp hw
    have hnorm : ‖w‖ < δ₂ := by
      have h1 : |w.re| ≤ ε' := abs_le.mpr hw'.1
      have h2 : |w.im| ≤ ε' := abs_le.mpr hw'.2
      have h3 : ε' ≤ δ₂ / 3 := min_le_right _ _
      have h4 : ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
      linarith
    exact hδ₂sub ⟨by rwa [mem_ball_zero_iff], hsub₂ hw⟩
  have hgY_inj : InjOn gY (Icc (-ε') ε' ×ℂ Icc (-ε') ε') := fun w₁ hw₁ w₂ hw₂ he => by
    have hψe : g w₁ = g w₂ := by rw [← hgY_ψ w₁ (hsub₂ hw₁), ← hgY_ψ w₂ (hsub₂ hw₂), he]
    exact hgi (hsub₁ (hsub₂ hw₁)) (hsub₁ (hsub₂ hw₂)) hψe
  have hsub_oo' : Ioo (-ε') ε' ×ℂ Ioo (-ε') ε' ⊆ Icc (-ε') ε' ×ℂ Icc (-ε') ε' := fun w hw =>
    Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hw).1,
      Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hw).2⟩
  have hopen' : IsOpen (gY '' (Ioo (-ε') ε' ×ℂ Ioo (-ε') ε')) :=
    isOpen_image_of_manifold (isOpen_Ioo.reProdIm isOpen_Ioo) ((hgY_cont.mono hsub₂).mono hsub_oo')
      (hgY_inj.mono hsub_oo') (fun _ _ => hY.2.2 _)
  refine ⟨gY, ε', hε', hgY_cont.mono hsub₂, hgY_inj, hopen', ?_, hgY_0, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩ hbd
    have hnotF : ψ (gY w) ∉ F := by rw [hgY_ψ w (hsub₂ hw)]; exact hsub₁_F w (hsub₂ hw)
    have hψbd : g w ∈ bd S := hgY_ψ w (hsub₂ hw) ▸ (mem_bd_cut_iff hY hS hψ hFcl hnotF).mp hbd
    exact hgint ⟨w, hsub₁ (hsub₂ hw), rfl⟩ hψbd
  · ext z; constructor
    · rintro ⟨hzA, w, hw, rfl⟩
      have hgwA : g w ∈ A := hgY_ψ w (hsub₂ hw) ▸ hzA
      have h1 : g w ∈ A ∩ g '' (Icc (-ε) ε ×ℂ Icc (-ε) ε) := ⟨hgwA, w, hsub₁ (hsub₂ hw), rfl⟩
      rw [hAbox] at h1; obtain ⟨u, hu, hue⟩ := h1
      have hu_eq : u = w := hgi (by
        have hu' := Complex.mem_reProdIm.mp hu
        exact Complex.mem_reProdIm.mpr ⟨hu'.1, by rw [mem_singleton_iff.mp hu'.2]; exact ⟨by linarith, hε.le⟩⟩)
        (hsub₁ (hsub₂ hw)) hue
      rw [hu_eq] at hu
      exact ⟨w, Complex.mem_reProdIm.mpr ⟨(Complex.mem_reProdIm.mp hw).1, (Complex.mem_reProdIm.mp hu).2⟩, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      have hw' := Complex.mem_reProdIm.mp hw
      have hle : ε' ≤ ε := ((min_le_left _ _).trans (half_le_self hε₁.le)).trans ((min_le_left _ _).trans (half_le_self hε.le))
      have hw_sq : w ∈ Icc (-ε') ε' ×ℂ Icc (-ε') ε' :=
        Complex.mem_reProdIm.mpr ⟨hw'.1, by rw [mem_singleton_iff.mp hw'.2]; exact ⟨by linarith, hε'.le⟩⟩
      have hgwA : g w ∈ A := (show g w ∈ A ∩ g '' (Icc (-ε) ε ×ℂ Icc (-ε) ε) by
        rw [hAbox]; exact ⟨w, Complex.mem_reProdIm.mpr ⟨⟨by linarith [hw'.1.1], by linarith [hw'.1.2]⟩, hw'.2⟩, rfl⟩).1
      exact ⟨show ψ (gY w) ∈ A by rw [hgY_ψ w (hsub₂ hw_sq)]; exact hgwA, w, hw_sq, rfl⟩
  · ext z; constructor
    · rintro ⟨hzr, w, hw, rfl⟩
      have hgwB : g w ∈ B := hgY_ψ w (hsub₂ hw) ▸ hpieces_sub r hzr
      have h1 : g w ∈ B ∩ g '' (Icc (-ε) ε ×ℂ Icc (-ε) ε) := ⟨hgwB, w, hsub₁ (hsub₂ hw), rfl⟩
      rw [hBbox] at h1; obtain ⟨u, hu, hue⟩ := h1
      have hu_eq : u = w := hgi (by
        have hu' := Complex.mem_reProdIm.mp hu
        exact Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hu'.1]; exact ⟨by linarith, hε.le⟩, hu'.2⟩)
        (hsub₁ (hsub₂ hw)) hue
      rw [hu_eq] at hu
      exact ⟨w, Complex.mem_reProdIm.mpr ⟨(Complex.mem_reProdIm.mp hu).1, (Complex.mem_reProdIm.mp hw).2⟩, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      have hw' := Complex.mem_reProdIm.mp hw
      have hle : ε' ≤ ε := ((min_le_left _ _).trans (half_le_self hε₁.le)).trans ((min_le_left _ _).trans (half_le_self hε.le))
      have hw_sq : w ∈ Icc (-ε') ε' ×ℂ Icc (-ε') ε' :=
        Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hw'.1]; exact ⟨by linarith, hε'.le⟩, hw'.2⟩
      have hgwB : g w ∈ B := (show g w ∈ B ∩ g '' (Icc (-ε) ε ×ℂ Icc (-ε) ε) by
        rw [hBbox]; exact ⟨w, Complex.mem_reProdIm.mpr ⟨hw'.1, ⟨by linarith [hw'.2.1], by linarith [hw'.2.2]⟩⟩, rfl⟩).1
      have hcov : gY w ∈ ⋃ r', pieces r' := hpieces_cov ⟨by rw [hgY_ψ w (hsub₂ hw_sq)]; exact hgwB,
        by rw [hgY_ψ w (hsub₂ hw_sq)]; exact hsub₁_F w (hsub₂ hw_sq)⟩
      obtain ⟨r', hr'⟩ := mem_iUnion.mp hcov
      have hr'_eq : r' = r := by
        by_contra hne; exact hsub₂_Z w hw_sq (mem_iUnion₂.mpr ⟨r', hne, hr'⟩)
      exact ⟨hr'_eq ▸ hr', w, hw_sq, rfl⟩

/-! ### Section 2: Descending the disc matching bound across a disc-cutting system -/

/-- Inductively cut `S` along a disc-cutting non-separating matching `N : Fin r → Set S`, apply
`lpps22_disc_matching` in the resulting closed disc, and descend back to a boundary-fixing
homeomorphism `γ : S ≃ₜ S` that fixes every `N k` pointwise. -/
private theorem descend_disc_matching_over_cut_system {r : ℕ} :
    ∀ {S : Type} [TopologicalSpace S] [ConnectedSpace S]
      (_hS : IsSurface S) {a b c n_rem m₁ : ℕ}
      (_eS : S ≃ₜ SurfaceModel a b c) (_hc : 1 ≤ c) (_hr : 2 * a + b + c - 1 = r)
      {N : Fin r → Set S} {G_rem : Fin n_rem → Set S} {L₁ : Fin m₁ → Set S}
      (_hN : ∀ k, ∃ s t, s ≠ t ∧ IsLineWithEnds (N k) s t ∧ N k ∩ bd S = {s, t})
      (_hNdisj : Pairwise fun k₁ k₂ => Disjoint (N k₁) (N k₂))
      (_hNnonsep : IsPreconnected ((⋃ k : Fin r, N k)ᶜ : Set S))
      (_hG : ∀ j, ∃ s t, s ≠ t ∧ IsLineWithEnds (G_rem j) s t ∧ G_rem j ∩ bd S = {s, t})
      (_hGdisj : Pairwise fun j₁ j₂ => Disjoint (G_rem j₁) (G_rem j₂))
      (_hGNdisj : ∀ k j, Disjoint (N k) (G_rem j))
      (_hL : ∀ i, ∃ u v, u ≠ v ∧ IsLineWithEnds (L₁ i) u v ∧ L₁ i ∩ bd S = {u, v})
      (_hLdisj : Pairwise fun i₁ i₂ => Disjoint (L₁ i₁) (L₁ i₂))
      (_hbd_NL : ∀ k i, Disjoint (N k ∩ bd S) (L₁ i ∩ bd S))
      (_hbd_GL : ∀ j i, Disjoint (G_rem j ∩ bd S) (L₁ i ∩ bd S))
      (_hfin : ∀ k i, (N k ∩ L₁ i).Finite)
      (_hsimple : ∀ k i, IsSimpleCrossing (N k) (L₁ i)),
      ∃ γ : S ≃ₜ S, (∀ x ∈ bd S, γ x = x) ∧
        (∀ k, ∀ x ∈ N k, γ x = x) ∧
        (∀ i j, (γ '' L₁ i ∩ G_rem j).Finite) ∧
        (∑ i : Fin m₁, ∑ j : Fin n_rem, (γ '' L₁ i ∩ G_rem j).ncard) ≤
          (m₁ + ∑ k : Fin r, ∑ i : Fin m₁, (N k ∩ L₁ i).ncard) * n_rem := by
  induction r with
  | zero =>
    intro S _ _ hS a b c n_rem m₁ eS hc hr N G_rem L₁ _ _ _ hG hGdisj _ hL hLdisj _ hbd_GL _ _
    have ha0 : a = 0 := by omega
    have hb0 : b = 0 := by omega
    have hc1 : c = 1 := by omega
    subst ha0 hb0 hc1
    obtain ⟨ed⟩ := nonempty_disc_homeo
    obtain ⟨eb⟩ := isClosedDisc_closedBall.1
    let eD : S ≃ₜ closedBall (0 : ℂ) 1 := (eS.trans ed).trans eb
    obtain ⟨γ, hγfix, hγcross⟩ := lpps22_disc_matching eD hL hLdisj hG hGdisj
      (fun i j => (hbd_GL j i).symm)
    refine ⟨γ, hγfix, fun k => Fin.elim0 k, fun i j => (hγcross i j).1, ?_⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    calc (∑ i : Fin m₁, ∑ j : Fin n_rem, (γ '' L₁ i ∩ G_rem j).ncard)
        ≤ ∑ _i : Fin m₁, ∑ _j : Fin n_rem, 1 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => (hγcross i j).2
      _ = m₁ * n_rem := by simp
  | succ r' ih =>
    intro S _ _ hS a b c n_rem m₁ eS hc hr N G_rem L₁ hN hNdisj hNnonsep hG hGdisj hGNdisj
      hL hLdisj hbd_NL hbd_GL hfin hsimple
    classical
    have ht2S : T2Space S := hS.2.1
    -- Cut `S` along `N 0`:
    obtain ⟨s₀, t₀, hst₀, hN0l, hN0b⟩ := hN 0
    have hN0cl : IsClosed (N 0) := hN0l.isCompact.isClosed
    have hN0_nonsep : IsPreconnected ((N 0)ᶜ : Set S) :=
      isPreconnected_compl_of_matching hS hN hNdisj hNnonsep 0
    obtain ⟨Y, tY, t2Y, ψ, hY, hψ, X, X', hP⟩ := exists_cut_arc hS hst₀ hN0b hN0l
    have : CompactSpace Y := hY.1
    have : Nonempty Y := by obtain ⟨x⟩ := ‹ConnectedSpace S›.toNonempty; obtain ⟨y, -⟩ := hψ.2.1 x; exact ⟨y⟩
    have : ConnectedSpace Y := (connectedSpace_cut_iff hY hS hψ hN0cl).mpr hN0_nonsep
    obtain ⟨a', b', c', ⟨eY⟩, hc', heuler⟩ := cut_iArc_euler_connected hS hY eS hst₀ hN0b hN0l hψ hP
    -- Lift `N k.succ` (`k : Fin r'`) and `G_rem j` (`j : Fin n_rem`) to `Y`:
    let N' : Fin r' → Set Y := fun k => ψ ⁻¹' N k.succ
    let G' : Fin n_rem → Set Y := fun j => ψ ⁻¹' G_rem j
    have hN' : ∀ k : Fin r', ∃ s' t' : Y, s' ≠ t' ∧ IsLineWithEnds (N' k) s' t' ∧ N' k ∩ bd Y = {s', t'} := by
      intro k; obtain ⟨s, t, hst, hl, hb⟩ := hN k.succ
      obtain ⟨s', t', hst', -, -, hl', hb'⟩ := lift_disjoint_iArc hY hS hψ hN0cl hst hl hb (hNdisj (Fin.succ_ne_zero k))
      exact ⟨s', t', hst', hl', hb'⟩
    have hN'disj : Pairwise fun k₁ k₂ : Fin r' => Disjoint (N' k₁) (N' k₂) := fun k₁ k₂ hne =>
      (hNdisj (fun h => hne (Fin.succ_injective r' h))).preimage ψ
    have hN'nonsep : IsPreconnected ((⋃ k : Fin r', N' k)ᶜ : Set Y) := by
      let U_S : Set S := (⋃ k : Fin (r' + 1), N k)ᶜ
      have hU_S_sub : U_S ⊆ (N 0)ᶜ := fun x hx h0 => hx (mem_iUnion.mpr ⟨0, h0⟩)
      let eF := cutComplHomeo hψ hN0cl
      let U_Y : Set Y := ψ ⁻¹' U_S
      have hU_Y_pre : IsPreconnected U_Y := by
        let subS : Set ((N 0)ᶜ : Set S) := Subtype.val ⁻¹' U_S
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
          · rintro ⟨⟨w, _⟩, ⟨⟨x, hx⟩, hxU, hwe⟩, rfl⟩
            show ψ w ∈ U_S
            have : ψ w = x := by have h := congrArg Subtype.val (eF.apply_symm_apply ⟨x, hx⟩); rw [hwe] at h; exact h
            rwa [this]
          · intro hy
            have hy0 : ψ y ∉ N 0 := hU_S_sub hy
            exact ⟨⟨y, hy0⟩, ⟨⟨ψ y, hy0⟩, hy, eF.symm_apply_apply ⟨y, hy0⟩⟩, rfl⟩
        rwa [him2] at h2
      have hU_Y_eq : U_Y = (ψ ⁻¹' (N 0)ᶜ) ∩ (⋃ k : Fin r', N' k)ᶜ := by
        ext y; simp only [U_Y, U_S, N', mem_preimage, mem_compl_iff, mem_iUnion, mem_inter_iff, not_exists]
        constructor
        · intro h; exact ⟨h 0, fun k => h k.succ⟩
        · rintro ⟨h0, hs⟩ k; exact Fin.cases h0 hs k
      have hopen : IsOpen ((⋃ k : Fin r', N' k)ᶜ : Set Y) :=
        (isClosed_iUnion_of_finite fun k => by obtain ⟨_, _, _, hl, _⟩ := hN' k; exact hl.isCompact.isClosed).isOpen_compl
      refine hU_Y_pre.subset_closure (hU_Y_eq ▸ inter_subset_right) fun y hy => ?_
      rw [hU_Y_eq, _root_.mem_closure_iff]; intro V hVo hyV
      obtain ⟨z, ⟨hzV, hzO⟩, hzD⟩ := _root_.mem_closure_iff.mp (dense_cut_compl hY hψ y)
        (V ∩ (⋃ k : Fin r', N' k)ᶜ) (hVo.inter hopen) ⟨hyV, hy⟩
      exact ⟨z, hzV, hzD, hzO⟩
    have hG' : ∀ j : Fin n_rem, ∃ s' t' : Y, s' ≠ t' ∧ IsLineWithEnds (G' j) s' t' ∧ G' j ∩ bd Y = {s', t'} := by
      intro j; obtain ⟨s, t, hst, hl, hb⟩ := hG j
      obtain ⟨s', t', hst', -, -, hl', hb'⟩ := lift_disjoint_iArc hY hS hψ hN0cl hst hl hb (hGNdisj 0 j).symm
      exact ⟨s', t', hst', hl', hb'⟩
    have hG'disj : Pairwise fun j₁ j₂ : Fin n_rem => Disjoint (G' j₁) (G' j₂) := fun j₁ j₂ hne =>
      (hGdisj hne).preimage ψ
    have hGN'disj : ∀ k j, Disjoint (N' k) (G' j) := fun k j => (hGNdisj k.succ j).preimage ψ
    -- Split each `L₁ i` along `N 0`:
    choose uL vL huvL hLl hLb using hL
    let d : Fin m₁ → ℕ := fun i => (N 0 ∩ L₁ i).ncard
    have hsplit_ex : ∀ i : Fin m₁,
        ∃ (pieces : Fin (d i + 1) → Set Y),
          (∀ s, ∃ u' v' : Y, u' ≠ v' ∧ IsLineWithEnds (pieces s) u' v' ∧ pieces s ∩ bd Y = {u', v'}) ∧
          (Pairwise fun s₁ s₂ => Disjoint (pieces s₁) (pieces s₂)) ∧
          (∀ s, pieces s ⊆ ψ ⁻¹' L₁ i) ∧
          (ψ ⁻¹' (L₁ i \ N 0) ⊆ ⋃ s, pieces s) ∧
          (∀ s, pieces s ∩ bd Y ⊆ ψ ⁻¹' (N 0 ∪ {uL i, vL i})) := fun i => by
      have hu0 : uL i ∉ N 0 := fun h => by
        have hubd : uL i ∈ L₁ i ∩ bd S := hLb i ▸ Or.inl rfl
        exact Set.disjoint_left.mp (hbd_NL 0 i) ⟨h, hubd.2⟩ hubd
      have hv0 : vL i ∉ N 0 := fun h => by
        have hvbd : vL i ∈ L₁ i ∩ bd S := hLb i ▸ Or.inr rfl
        exact Set.disjoint_left.mp (hbd_NL 0 i) ⟨h, hvbd.2⟩ hvbd
      exact split_transverse_iArc hY hS hψ hN0cl (huvL i) (hLl i) (hLb i) hu0 hv0 (hfin 0 i) (hsimple 0 i)
    choose pieces hpieces_arc hpieces_disj hpieces_sub hpieces_cov hpieces_bd using hsplit_ex
    let eL : (Σ i : Fin m₁, Fin (d i + 1)) ≃ Fin (Fintype.card (Σ i : Fin m₁, Fin (d i + 1))) :=
      Fintype.equivFin (Σ i : Fin m₁, Fin (d i + 1))
    let m₁' := Fintype.card (Σ i : Fin m₁, Fin (d i + 1))
    let L₁' : Fin m₁' → Set Y := fun idx => pieces (eL.symm idx).1 (eL.symm idx).2
    have hL₁' : ∀ idx, ∃ u' v' : Y, u' ≠ v' ∧ IsLineWithEnds (L₁' idx) u' v' ∧ L₁' idx ∩ bd Y = {u', v'} :=
      fun idx => hpieces_arc (eL.symm idx).1 (eL.symm idx).2
    have hL₁'disj : Pairwise fun idx₁ idx₂ : Fin m₁' => Disjoint (L₁' idx₁) (L₁' idx₂) := fun idx₁ idx₂ hne => by
      have hne' : eL.symm idx₁ ≠ eL.symm idx₂ := fun h => hne (eL.symm.injective h)
      by_cases hi : (eL.symm idx₁).1 = (eL.symm idx₂).1
      · rcases h1 : eL.symm idx₁ with ⟨i₁, s₁⟩
        rcases h2 : eL.symm idx₂ with ⟨i₂, s₂⟩
        rw [h1, h2] at hi hne'; dsimp only at hi; subst hi
        have hs : s₁ ≠ s₂ := fun h => hne' (by subst h; rfl)
        have hL1 : L₁' idx₁ = pieces i₁ s₁ := by dsimp only [L₁']; rw [h1]
        have hL2 : L₁' idx₂ = pieces i₁ s₂ := by dsimp only [L₁']; rw [h2]
        dsimp only; rw [hL1, hL2]; exact hpieces_disj i₁ hs
      · exact ((hLdisj hi).preimage ψ).mono (hpieces_sub _ _) (hpieces_sub _ _)
    have hbd'_NL : ∀ k idx, Disjoint (N' k ∩ bd Y) (L₁' idx ∩ bd Y) := fun k idx => by
      rw [Set.disjoint_left]; intro y hyN hyL
      have hnot0 : ψ y ∉ N 0 := Set.disjoint_left.mp (hNdisj (Fin.succ_ne_zero k)) hyN.1
      have h1 : ψ y ∈ N k.succ ∩ bd S := ⟨hyN.1, (mem_bd_cut_iff hY hS hψ hN0cl hnot0).mp hyN.2⟩
      rcases hpieces_bd _ _ hyL with h0 | huv
      · exact hnot0 h0
      · exact Set.disjoint_left.mp (hbd_NL k.succ (eL.symm idx).1) h1 ((hLb _).symm ▸ huv)
    have hbd'_GL : ∀ j idx, Disjoint (G' j ∩ bd Y) (L₁' idx ∩ bd Y) := fun j idx => by
      rw [Set.disjoint_left]; intro y hyG hyL
      have hnot0 : ψ y ∉ N 0 := Set.disjoint_right.mp (hGNdisj 0 j) hyG.1
      have h1 : ψ y ∈ G_rem j ∩ bd S := ⟨hyG.1, (mem_bd_cut_iff hY hS hψ hN0cl hnot0).mp hyG.2⟩
      rcases hpieces_bd _ _ hyL with h0 | huv
      · exact hnot0 h0
      · exact Set.disjoint_left.mp (hbd_GL j (eL.symm idx).1) h1 ((hLb _).symm ▸ huv)
    have hfin' : ∀ k idx, (N' k ∩ L₁' idx).Finite := fun k idx => by
      have hinj : InjOn ψ (N' k ∩ L₁' idx) := fun y₁ hy₁ y₂ hy₂ he =>
        hψ.2.2.1 (Set.disjoint_left.mp (hNdisj (Fin.succ_ne_zero k)) hy₁.1)
          (Set.disjoint_left.mp (hNdisj (Fin.succ_ne_zero k)) hy₂.1) he
      refine ((hfin k.succ (eL.symm idx).1).subset ?_).of_finite_image hinj
      rintro _ ⟨y, ⟨hyN, hyL⟩, rfl⟩
      exact ⟨hyN, hpieces_sub _ _ hyL⟩
    have hsimple' : ∀ k idx, IsSimpleCrossing (N' k) (L₁' idx) := fun k idx =>
      isSimpleCrossing_lift_cut hS hY hψ hN0cl (hNdisj (Fin.succ_ne_zero k)) (hsimple k.succ _)
        (fun s => by obtain ⟨_, _, _, hl, _⟩ := hpieces_arc _ s; exact hl.isCompact.isClosed)
        (hpieces_disj _) (hpieces_sub _) (hpieces_cov _) (eL.symm idx).2
    -- Apply IH on `Y`, descend `G_Y` across `ψ`:
    obtain ⟨G_Y, hGYfix, hGYN', hGYfin, hGYsum⟩ :=
      ih hY eY hc' (by omega) hN' hN'disj hN'nonsep hG' hG'disj hGN'disj hL₁' hL₁'disj hbd'_NL hbd'_GL hfin' hsimple'
    obtain ⟨γ, hγψ⟩ := exists_descend_cut hψ G_Y fun z hz => hGYfix z (hψ.2.2.2.2 hz)
    have hγfix : ∀ x ∈ bd S, γ x = x := fun x hx => by
      obtain ⟨y, rfl⟩ := hψ.2.1 x
      have hybd : y ∈ bd Y := by
        by_cases h0 : ψ y ∈ N 0
        · exact hψ.2.2.2.2 h0
        · exact (mem_bd_cut_iff hY hS hψ hN0cl h0).mpr hx
      rw [hγψ y, hGYfix y hybd]
    have hγN : ∀ k : Fin (r' + 1), ∀ x ∈ N k, γ x = x := fun k x hx => by
      obtain ⟨y, rfl⟩ := hψ.2.1 x
      refine Fin.cases (fun hx => ?_) (fun k' hx => ?_) k hx
      · rw [hγψ y, hGYfix y (hψ.2.2.2.2 hx)]
      · rw [hγψ y, hGYN' k' y hx]
    have hγ_inter : ∀ (i : Fin m₁) (j : Fin n_rem),
        γ '' L₁ i ∩ G_rem j = ⋃ s : Fin (d i + 1), ψ '' (G_Y '' pieces i s ∩ G' j) := by
      intro i j
      ext x; constructor
      · rintro ⟨⟨z, hzL, rfl⟩, hxG⟩
        have hznot0 : z ∉ N 0 := fun h0 =>
          Set.disjoint_left.mp (hGNdisj 0 j) h0 (hγN 0 z h0 ▸ hxG)
        obtain ⟨y, rfl⟩ := hψ.2.1 z
        obtain ⟨s, hys⟩ := mem_iUnion.mp (hpieces_cov i ⟨hzL, hznot0⟩)
        refine mem_iUnion.mpr ⟨s, G_Y y, ⟨⟨y, hys, rfl⟩, ?_⟩, (hγψ y).symm⟩
        show ψ (G_Y y) ∈ G_rem j; rw [← hγψ y]; exact hxG
      · intro hx
        obtain ⟨s, y', ⟨⟨y, hys, rfl⟩, hy'G⟩, rfl⟩ := mem_iUnion.mp hx
        exact ⟨⟨ψ y, hpieces_sub i s hys, hγψ y⟩, hy'G⟩
    have hγfin : ∀ i j, (γ '' L₁ i ∩ G_rem j).Finite := fun i j => by
      rw [hγ_inter i j]
      exact Set.finite_iUnion fun s => ((hGYfin (eL ⟨i, s⟩) j).subset (by dsimp only [L₁']; rw [Equiv.symm_apply_apply])).image ψ
    -- Crossing count: relate `∑ k, ∑ idx, (N' k ∩ L₁' idx).ncard` to `∑ k, ∑ i, (N k.succ ∩ L₁ i).ncard`!
    have hsum_pieces : (∑ k : Fin r', ∑ idx : Fin m₁', (N' k ∩ L₁' idx).ncard) ≤
        ∑ k : Fin r', ∑ i : Fin m₁, (N k.succ ∩ L₁ i).ncard := by
      refine Finset.sum_le_sum fun k _ => ?_
      rw [← Fintype.sum_equiv eL (fun p => (N' k ∩ pieces p.1 p.2).ncard)
          (fun idx => (N' k ∩ L₁' idx).ncard) (fun p => by dsimp only [L₁']; rw [Equiv.symm_apply_apply]),
        Fintype.sum_sigma]
      refine Finset.sum_le_sum fun i _ => ?_
      -- The sets `ψ '' (N' k ∩ pieces i s)` (`s : Fin (d i + 1)`) are pairwise disjoint subsets of `N k.succ ∩ L₁ i`!
      have him_eq : ∀ s : Fin (d i + 1), (N' k ∩ pieces i s).ncard = (ψ '' (N' k ∩ pieces i s)).ncard := fun s => by
        have hinj : InjOn ψ (N' k ∩ pieces i s) := fun y₁ hy₁ y₂ hy₂ he =>
          hψ.2.2.1 (Set.disjoint_left.mp (hNdisj (Fin.succ_ne_zero k)) hy₁.1)
            (Set.disjoint_left.mp (hNdisj (Fin.succ_ne_zero k)) hy₂.1) he
        exact hinj.ncard_image.symm
      have him_disj : Pairwise fun s₁ s₂ : Fin (d i + 1) => Disjoint (ψ '' (N' k ∩ pieces i s₁)) (ψ '' (N' k ∩ pieces i s₂)) := by
        intro s₁ s₂ hne
        rw [Set.disjoint_left]; rintro _ ⟨y₁, hy₁, rfl⟩ ⟨y₂, hy₂, he⟩
        have hy12 := hψ.2.2.1 (Set.disjoint_left.mp (hNdisj (Fin.succ_ne_zero k)) hy₁.1)
          (Set.disjoint_left.mp (hNdisj (Fin.succ_ne_zero k)) hy₂.1) he.symm
        exact Set.disjoint_left.mp (hpieces_disj i hne) hy₁.2 (hy12 ▸ hy₂.2)
      have him_sub : ∀ s : Fin (d i + 1), ψ '' (N' k ∩ pieces i s) ⊆ N k.succ ∩ L₁ i := by
        rintro s _ ⟨y, ⟨hyN, hys⟩, rfl⟩; exact ⟨hyN, hpieces_sub i s hys⟩
      have hsum_disj : ∀ (S : Finset (Fin (d i + 1))),
          ∑ s ∈ S, (ψ '' (N' k ∩ pieces i s)).ncard = (⋃ s ∈ S, ψ '' (N' k ∩ pieces i s)).ncard := by
        intro S
        induction S using Finset.induction_on with
        | empty => simp
        | insert a S ha ihS =>
          have hdisj_a : Disjoint (ψ '' (N' k ∩ pieces i a)) (⋃ s ∈ S, ψ '' (N' k ∩ pieces i s)) := by
            rw [Set.disjoint_iUnion_right]; intro s; rw [Set.disjoint_iUnion_right]; intro hs
            exact him_disj (fun h => ha (h ▸ hs))
          have hfa : (ψ '' (N' k ∩ pieces i a)).Finite := (hfin k.succ i).subset (him_sub a)
          have hfS : (⋃ s ∈ S, ψ '' (N' k ∩ pieces i s)).Finite := (hfin k.succ i).subset (iUnion₂_subset fun s _ => him_sub s)
          rw [Finset.sum_insert ha, Finset.set_biUnion_insert, ihS, ← Set.ncard_union_eq hdisj_a hfa hfS]
      calc (∑ s : Fin (d i + 1), (N' k ∩ pieces i s).ncard)
          = ∑ s : Fin (d i + 1), (ψ '' (N' k ∩ pieces i s)).ncard := Finset.sum_congr rfl fun s _ => him_eq s
        _ = (⋃ s ∈ (Finset.univ : Finset (Fin (d i + 1))), ψ '' (N' k ∩ pieces i s)).ncard := hsum_disj Finset.univ
        _ ≤ (N k.succ ∩ L₁ i).ncard := Set.ncard_le_ncard (iUnion₂_subset fun s _ => him_sub s) (hfin k.succ i)
    have hm₁'_eq : m₁' = m₁ + ∑ i : Fin m₁, (N 0 ∩ L₁ i).ncard := by
      simp only [m₁', Fintype.card_sigma, Fintype.card_fin, d, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, smul_eq_mul, mul_one, add_comm]
    have htotal : (∑ i : Fin m₁, ∑ j : Fin n_rem, (γ '' L₁ i ∩ G_rem j).ncard) ≤
        (m₁ + ∑ k : Fin (r' + 1), ∑ i : Fin m₁, (N k ∩ L₁ i).ncard) * n_rem := by
      calc (∑ i : Fin m₁, ∑ j : Fin n_rem, (γ '' L₁ i ∩ G_rem j).ncard)
          ≤ ∑ i : Fin m₁, ∑ j : Fin n_rem, ∑ s : Fin (d i + 1), (G_Y '' pieces i s ∩ G' j).ncard := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
            rw [hγ_inter i j]
            have h1 : ∀ (S : Finset (Fin (d i + 1))),
                (⋃ s ∈ S, ψ '' (G_Y '' pieces i s ∩ G' j)).ncard ≤
                  ∑ s ∈ S, (ψ '' (G_Y '' pieces i s ∩ G' j)).ncard := by
              intro S; induction S using Finset.induction_on with
              | empty => simp
              | insert a S ha ihS =>
                rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
                exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left ihS _)
            have h2 : (⋃ s : Fin (d i + 1), ψ '' (G_Y '' pieces i s ∩ G' j)).ncard ≤
                ∑ s : Fin (d i + 1), (ψ '' (G_Y '' pieces i s ∩ G' j)).ncard := by
              simpa only [Finset.mem_univ, iUnion_true] using h1 Finset.univ
            exact h2.trans (Finset.sum_le_sum fun s _ =>
              Set.ncard_image_le ((hGYfin (eL ⟨i, s⟩) j).subset (by dsimp only [L₁']; rw [Equiv.symm_apply_apply])))
        _ = ∑ idx : Fin m₁', ∑ j : Fin n_rem, (G_Y '' L₁' idx ∩ G' j).ncard := by
            conv_lhs =>
              arg 2; ext i; rw [Finset.sum_comm]
            rw [← Fintype.sum_sigma (fun p : Σ i : Fin m₁, Fin (d i + 1) => ∑ j : Fin n_rem, (G_Y '' pieces p.1 p.2 ∩ G' j).ncard)]
            exact Fintype.sum_equiv eL _ _ fun p => Finset.sum_congr rfl fun j _ => by dsimp only [L₁']; rw [Equiv.symm_apply_apply]
        _ ≤ (m₁' + ∑ k : Fin r', ∑ idx : Fin m₁', (N' k ∩ L₁' idx).ncard) * n_rem := hGYsum
        _ ≤ (m₁ + ∑ k : Fin (r' + 1), ∑ i : Fin m₁, (N k ∩ L₁ i).ncard) * n_rem := by
            refine Nat.mul_le_mul_right n_rem ?_
            calc m₁' + ∑ k : Fin r', ∑ idx : Fin m₁', (N' k ∩ L₁' idx).ncard
                ≤ m₁' + ∑ k : Fin r', ∑ i : Fin m₁, (N k.succ ∩ L₁ i).ncard := Nat.add_le_add_left hsum_pieces _
              _ = m₁ + ∑ k : Fin (r' + 1), ∑ i : Fin m₁, (N k ∩ L₁ i).ncard := by
                  rw [hm₁'_eq, Fin.sum_univ_succ, add_assoc]
    exact ⟨γ, hγfix, hγN, hγfin, htotal⟩

/-! ### Section 3: LPPS22 Lemma A.3 -/

/-- **Lokshtanov–Pilipczuk–Pilipczuk–Saurabh (2022), Appendix A, Lemma A.3**:
On a connected compact surface `S ≃ₜ SurfaceModel a b c` with `1 ≤ c`, given two matchings
`G : Fin n → Set S` and `L : Fin m → Set S` of pairwise disjoint proper `I`-arcs with disjoint
boundary endpoints, there exists a boundary-fixing homeomorphism `φ : S ≃ₜ S` such that
`φ '' L i ∩ G j` is finite for all `i, j` and
`∑ i, ∑ j, (φ '' L i ∩ G j).ncard ≤ m * 3 ^ (2 * n + 3 * (2 * a + b) + c)`. -/
theorem lpps22_lemma_A_3 {S : Type} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsSurface S) {a b c n m : ℕ} (eS : S ≃ₜ SurfaceModel a b c) (hc : 1 ≤ c)
    {G : Fin n → Set S} {L : Fin m → Set S}
    (hG : ∀ j, ∃ s t, s ≠ t ∧ IsLineWithEnds (G j) s t ∧ G j ∩ bd S = {s, t})
    (hGdisj : Pairwise fun j₁ j₂ => Disjoint (G j₁) (G j₂))
    (hL : ∀ i, ∃ u v, u ≠ v ∧ IsLineWithEnds (L i) u v ∧ L i ∩ bd S = {u, v})
    (hLdisj : Pairwise fun i₁ i₂ => Disjoint (L i₁) (L i₂))
    (hbd_disj : ∀ j i, Disjoint (G j ∩ bd S) (L i ∩ bd S)) :
    ∃ φ : S ≃ₜ S, (∀ x ∈ bd S, φ x = x) ∧
      (∀ i j, (φ '' L i ∩ G j).Finite) ∧
      (∑ i : Fin m, ∑ j : Fin n, (φ '' L i ∩ G j).ncard) ≤ m * 3 ^ (2 * n + 3 * (2 * a + b) + c) := by
  classical
  have ht2S : T2Space S := hS.2.1
  let K : Set S := ⋃ i : Fin m, L i ∩ bd S
  have hKfin : K.Finite := Set.finite_iUnion fun i => by
    obtain ⟨u, v, -, -, hb⟩ := hL i; rw [hb]; exact (Set.finite_singleton v).insert u
  have hKcl : IsClosed K := hKfin.isClosed
  have hKcuff : ∀ C ∈ cuffs S, (C \ K).Nonempty := fun C hC => by
    obtain ⟨φC⟩ := (cuff_statement.{0} S hS).2.2 C hC
    by_contra hnot
    rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hnot
    have hCfin : C.Finite := hKfin.subset hnot
    have : Finite C := hCfin.to_subtype
    have : Finite Circle := Finite.of_equiv C φC.symm.toEquiv
    have hinj : Function.Injective (fun k : ℕ => Circle.exp (1 / ((k : ℝ) + 1))) := by
      intro k₁ k₂ h
      have hval : Complex.exp (((1 / ((k₁ : ℝ) + 1) : ℝ) : ℂ) * I) = Complex.exp (((1 / ((k₂ : ℝ) + 1) : ℝ) : ℂ) * I) := by
        simpa [Circle.coe_exp] using congrArg Subtype.val h
      have h1 : Complex.exp ((((1 / ((k₁ : ℝ) + 1) - 1 / ((k₂ : ℝ) + 1)) : ℝ) : ℂ) * I) = 1 := by
        calc Complex.exp ((((1 / ((k₁ : ℝ) + 1) - 1 / ((k₂ : ℝ) + 1)) : ℝ) : ℂ) * I)
            = Complex.exp (((1 / ((k₁ : ℝ) + 1) : ℝ) : ℂ) * I) * (Complex.exp (((1 / ((k₂ : ℝ) + 1) : ℝ) : ℂ) * I))⁻¹ := by
              rw [← Complex.exp_neg, ← Complex.exp_add]; congr 1; push_cast; ring
          _ = 1 := by rw [hval, mul_inv_cancel₀ (Complex.exp_ne_zero _)]
      obtain ⟨z, hz⟩ := Complex.exp_eq_one_iff.mp h1
      have him : 1 / ((k₁ : ℝ) + 1) - 1 / ((k₂ : ℝ) + 1) = z * (2 * Real.pi) := by
        have := congrArg Complex.im hz
        simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add, sub_zero,
          Complex.intCast_re, Complex.intCast_im, Complex.re_ofNat, Complex.im_ofNat] at this
        linarith
      have hbd : |1 / ((k₁ : ℝ) + 1) - 1 / ((k₂ : ℝ) + 1)| < 2 * Real.pi := by
        have ha : (0 : ℝ) < 1 / ((k₁ : ℝ) + 1) := by positivity
        have hb : (0 : ℝ) < 1 / ((k₂ : ℝ) + 1) := by positivity
        have ha1 : 1 / ((k₁ : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
        have hb1 : 1 / ((k₂ : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
        rw [abs_lt]; constructor <;> linarith [Real.pi_gt_three]
      have hz0 : z = 0 := by
        by_contra hzn
        have h1z : (1 : ℝ) ≤ |(z : ℝ)| := by exact_mod_cast Int.one_le_abs hzn
        have : |1 / ((k₁ : ℝ) + 1) - 1 / ((k₂ : ℝ) + 1)| = |(z : ℝ)| * (2 * Real.pi) := by
          rw [him, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
        nlinarith [Real.pi_pos]
      subst hz0; simp only [Int.cast_zero, zero_mul, sub_eq_zero] at him
      have heq : ((k₁ : ℝ) + 1) = (k₂ : ℝ) + 1 := by
        have h1 : (1 : ℝ) / ((k₁ : ℝ) + 1) = 1 / ((k₂ : ℝ) + 1) := him
        field_simp at h1; linarith
      exact_mod_cast (show (k₁ : ℝ) = k₂ by linarith)
    exact not_finite_iff_infinite.mpr (inferInstance : Infinite ℕ) (Finite.of_injective _ hinj)
  have hGK : ∀ j, Disjoint (G j ∩ bd S) K := fun j =>
    Set.disjoint_iUnion_right.mpr fun i => hbd_disj j i
  -- Step 1: Build disc-cutting non-separating matching `N` of size `r := 2 * a + b + c - 1`
  obtain ⟨I₀, r₁, N₁, hr_eq, hN₁, hN₁disj, hN₁G, hNnonsep_raw⟩ :=
    exists_disc_cutting_matching (n + (2 * a + b + c - 1)) hS eS hc le_rfl hKcl hKcuff hG hGdisj hGK
  let r : ℕ := 2 * a + b + c - 1
  let eI₀ : Fin I₀.card ≃ I₀ := (Fintype.equivFinOfCardEq (Fintype.card_coe I₀)).symm
  let N : Fin r → Set S := fun k =>
    if h : k.1 < I₀.card then G (eI₀ ⟨k.1, h⟩).1 else N₁ ⟨k.1 - I₀.card, by omega⟩
  have hN_union : (⋃ k : Fin r, N k) = (⋃ j ∈ I₀, G j) ∪ ⋃ k : Fin r₁, N₁ k := by
    ext x; simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨k, hxk⟩; dsimp only [N] at hxk; split_ifs at hxk with hk
      · exact Or.inl ⟨(eI₀ ⟨k.1, hk⟩).1, (eI₀ ⟨k.1, hk⟩).2, hxk⟩
      · exact Or.inr ⟨⟨k.1 - I₀.card, by omega⟩, hxk⟩
    · rintro (⟨j, hj, hxj⟩ | ⟨k, hxk⟩)
      · let idx := eI₀.symm ⟨j, hj⟩
        have hidx : (eI₀ idx).1 = j := congrArg Subtype.val (eI₀.apply_symm_apply ⟨j, hj⟩)
        refine ⟨⟨idx.1, by omega⟩, ?_⟩
        simp only [N, idx.2, ↓reduceDIte, Fin.eta, hidx]; exact hxj
      · refine ⟨⟨I₀.card + k.1, by omega⟩, ?_⟩
        simp only [N, show ¬ (I₀.card + k.1 < I₀.card) by omega, ↓reduceDIte, Nat.add_sub_cancel_left]; exact hxk
  have hN : ∀ k : Fin r, ∃ s t, s ≠ t ∧ IsLineWithEnds (N k) s t ∧ N k ∩ bd S = {s, t} := fun k => by
    dsimp only [N]; split_ifs with hk
    · exact hG _
    · obtain ⟨s, t, hst, hl, hb, -, -⟩ := hN₁ ⟨k.1 - I₀.card, by omega⟩; exact ⟨s, t, hst, hl, hb⟩
  have hNdisj : Pairwise fun k₁ k₂ : Fin r => Disjoint (N k₁) (N k₂) := fun k₁ k₂ hne => by
    dsimp only [N]; split_ifs with h1 h2 h2
    · exact hGdisj fun h => hne (Fin.ext (congrArg (Fin.val : Fin I₀.card → ℕ) (eI₀.injective (Subtype.ext h))))
    · exact (hN₁G _ _).symm
    · exact hN₁G _ _
    · exact hN₁disj fun h => hne (Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega))
  have hNnonsep : IsPreconnected ((⋃ k : Fin r, N k)ᶜ : Set S) := hN_union.symm ▸ hNnonsep_raw
  have hbd_NL : ∀ k i, Disjoint (N k ∩ bd S) (L i ∩ bd S) := fun k i => by
    dsimp only [N]; split_ifs with hk
    · exact hbd_disj _ i
    · obtain ⟨s, t, -, -, hb, hsK, htK⟩ := hN₁ ⟨k.1 - I₀.card, by omega⟩
      rw [hb, Set.disjoint_left]
      rintro x (rfl | hx) hxL
      · exact hsK (mem_iUnion.mpr ⟨i, hxL⟩)
      · exact htK (mem_singleton_iff.mp hx ▸ mem_iUnion.mpr ⟨i, hxL⟩)
  -- Step 2: Apply `ghr18_theorem_1_3` to `N` and `L`, and pull `L` back by `β.symm`
  obtain ⟨β, hβfix, hβfin, hβsimple, hβsum⟩ := ghr18_theorem_1_3 hS hN hNdisj hNnonsep hL hLdisj hbd_NL
  let L₁ : Fin m → Set S := fun i => β.symm '' L i
  have hβsymm_fix : ∀ x ∈ bd S, β.symm x = x := fun x hx => β.injective (by rw [β.apply_symm_apply, hβfix x hx])
  have hL₁ : ∀ i, ∃ u v, u ≠ v ∧ IsLineWithEnds (L₁ i) u v ∧ L₁ i ∩ bd S = {u, v} := fun i => by
    obtain ⟨u, v, huv, ⟨f, hf0, hf1⟩, hb⟩ := hL i
    have hubd : u ∈ bd S := (hb.symm ▸ Or.inl rfl : u ∈ L i ∩ bd S).2
    have hvbd : v ∈ bd S := (hb.symm ▸ Or.inr rfl : v ∈ L i ∩ bd S).2
    refine ⟨u, v, huv, ⟨f.trans (β.symm.image (L i)), by show β.symm (f 0).1 = u; rw [hf0, hβsymm_fix u hubd],
      by show β.symm (f 1).1 = v; rw [hf1, hβsymm_fix v hvbd]⟩, ?_⟩
    ext x; constructor
    · rintro ⟨⟨z, hzL, rfl⟩, hxbd⟩
      have hzeq : β.symm z = z := β.symm.injective (hβsymm_fix (β.symm z) hxbd)
      rw [hzeq]; exact hb ▸ ⟨hzL, hzeq ▸ hxbd⟩
    · rintro (hx | hx)
      · rw [hx]; exact ⟨⟨u, (hb.symm ▸ Or.inl rfl : u ∈ L i ∩ bd S).1, hβsymm_fix u hubd⟩, hubd⟩
      · rw [mem_singleton_iff.mp hx]; exact ⟨⟨v, (hb.symm ▸ Or.inr rfl : v ∈ L i ∩ bd S).1, hβsymm_fix v hvbd⟩, hvbd⟩
  have hL₁_bd : ∀ i, L₁ i ∩ bd S = L i ∩ bd S := fun i => by
    ext x; constructor
    · rintro ⟨⟨z, hzL, rfl⟩, hxbd⟩
      have hzeq : β.symm z = z := β.symm.injective (hβsymm_fix (β.symm z) hxbd)
      exact ⟨hzeq.symm ▸ hzL, hxbd⟩
    · rintro ⟨hxL, hxbd⟩
      exact ⟨⟨x, hxL, hβsymm_fix x hxbd⟩, hxbd⟩
  have hL₁disj : Pairwise fun i₁ i₂ => Disjoint (L₁ i₁) (L₁ i₂) := fun i₁ i₂ hne =>
    Set.disjoint_image_of_injective β.symm.injective (hLdisj hne)
  have hNL₁_eq : ∀ k i, N k ∩ L₁ i = β.symm '' (β '' N k ∩ L i) := fun k i => by
    rw [Set.image_inter β.symm.injective, ← Set.image_comp]; simp [L₁]
  have hNL₁_fin : ∀ k i, (N k ∩ L₁ i).Finite := fun k i => hNL₁_eq k i ▸ (hβfin k i).image β.symm
  have hNL₁_simple : ∀ k i, IsSimpleCrossing (N k) (L₁ i) := fun k i => by
    have h1 : β.symm '' (β '' N k) = N k := by rw [← Set.image_comp]; simp
    exact h1 ▸ isSimpleCrossing_image_homeo hS β.symm (hβsimple k i)
  have hNL₁_sum : (∑ k : Fin r, ∑ i : Fin m, (N k ∩ L₁ i).ncard) ≤ m * (3 ^ r - 1) := by
    have heq : (∑ k : Fin r, ∑ i : Fin m, (N k ∩ L₁ i).ncard) = ∑ k : Fin r, ∑ i : Fin m, (β '' N k ∩ L i).ncard :=
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by
        rw [hNL₁_eq k i, Set.ncard_image_of_injective _ β.symm.injective]
    exact heq ▸ hβsum
  -- Step 3: Remaining arcs `G_rem` (`j ∈ I₀ᶜ`) and descend disc matching over `N`
  let Irem : Finset (Fin n) := Finset.univ \ I₀
  let eRem : Fin Irem.card ≃ Irem := (Fintype.equivFinOfCardEq (Fintype.card_coe Irem)).symm
  let G_rem : Fin Irem.card → Set S := fun j => G (eRem j).1
  have hGNrem_disj : ∀ k j, Disjoint (N k) (G_rem j) := fun k j => by
    dsimp only [N, G_rem]; split_ifs with hk
    · refine hGdisj fun h => ?_
      have hm1 : (eRem j).1 ∈ I₀ := h ▸ (eI₀ ⟨k.1, hk⟩).2
      exact (Finset.mem_sdiff.mp (eRem j).2).2 hm1
    · exact hN₁G _ _
  obtain ⟨γ, hγfix, hγN, hγfin_rem, hγsum_rem⟩ :=
    descend_disc_matching_over_cut_system hS eS hc rfl hN hNdisj hNnonsep
      (fun j => hG (eRem j).1)
      (fun j₁ j₂ hne => hGdisj fun h => hne (eRem.injective (Subtype.ext h)))
      hGNrem_disj hL₁ hL₁disj
      (fun k i => hL₁_bd i ▸ hbd_NL k i)
      (fun j i => hL₁_bd i ▸ hbd_disj (eRem j).1 i)
      hNL₁_fin hNL₁_simple
  -- Step 4: Compose `φ := β.symm.trans γ` and bound total crossings!
  let φ : S ≃ₜ S := β.symm.trans γ
  have hφfix : ∀ x ∈ bd S, φ x = x := fun x hx => by
    simp only [φ, Homeomorph.trans_apply, hβsymm_fix x hx, hγfix x hx]
  have hφL : ∀ i, φ '' L i = γ '' L₁ i := fun i => by
    change (γ ∘ β.symm) '' L i = γ '' (β.symm '' L i); rw [Set.image_comp]
  have hγ_on_I0 : ∀ j : Fin n, j ∈ I₀ → ∀ i : Fin m, (γ '' L₁ i ∩ G j).Finite ∧
      (γ '' L₁ i ∩ G j).ncard = (G j ∩ L₁ i).ncard := fun j hj i => by
    let idx := eI₀.symm ⟨j, hj⟩
    have hidx : (eI₀ idx).1 = j := congrArg Subtype.val (eI₀.apply_symm_apply ⟨j, hj⟩)
    have hNk : N ⟨idx.1, by omega⟩ = G j := by simp only [N, idx.2, ↓reduceDIte, Fin.eta, hidx]
    have hγG : γ '' G j = G j := by
      ext x; constructor
      · rintro ⟨z, hz, rfl⟩; rwa [hγN ⟨idx.1, by omega⟩ z (hNk.symm ▸ hz)]
      · intro hx; exact ⟨x, hx, hγN ⟨idx.1, by omega⟩ x (hNk.symm ▸ hx)⟩
    have heq : γ '' L₁ i ∩ G j = γ '' (G j ∩ L₁ i) := by
      rw [Set.image_inter γ.injective, hγG, inter_comm]
    rw [heq]
    exact ⟨(hNk ▸ hNL₁_fin ⟨idx.1, by omega⟩ i).image γ, Set.ncard_image_of_injective _ γ.injective⟩
  have hφfin : ∀ i j, (φ '' L i ∩ G j).Finite := fun i j => by
    rw [hφL i]
    by_cases hj : j ∈ I₀
    · exact (hγ_on_I0 j hj i).1
    · let idx := eRem.symm ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩⟩
      have hidx : G_rem idx = G j := by
        simp only [G_rem, idx]; congr 1; exact congrArg Subtype.val (eRem.apply_symm_apply _)
      exact hidx ▸ hγfin_rem i idx
  -- Split sum over `j : Fin n` into `j ∈ I₀` and `j ∈ Irem`:
  have hsum_I0 : (∑ i : Fin m, ∑ j ∈ I₀, (φ '' L i ∩ G j).ncard) ≤ m * (3 ^ r - 1) := by
    calc (∑ i : Fin m, ∑ j ∈ I₀, (φ '' L i ∩ G j).ncard)
        = ∑ i : Fin m, ∑ j ∈ I₀, (G j ∩ L₁ i).ncard :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => by rw [hφL i, (hγ_on_I0 j hj i).2]
      _ = ∑ j ∈ I₀, ∑ i : Fin m, (G j ∩ L₁ i).ncard := Finset.sum_comm
      _ = ∑ k : Fin I₀.card, ∑ i : Fin m, (N ⟨k.1, by omega⟩ ∩ L₁ i).ncard := by
          rw [← Finset.sum_coe_sort I₀]
          exact (Fintype.sum_equiv eI₀ (fun k => ∑ i : Fin m, (N ⟨k.1, by omega⟩ ∩ L₁ i).ncard)
            (fun j : I₀ => ∑ i : Fin m, (G j.1 ∩ L₁ i).ncard) fun k =>
              Finset.sum_congr rfl fun i _ => by simp only [N, k.2, ↓reduceDIte, Fin.eta]).symm
      _ ≤ ∑ k : Fin r, ∑ i : Fin m, (N k ∩ L₁ i).ncard := by
          let fEmb : Fin I₀.card ↪ Fin r := ⟨fun k => ⟨k.1, by omega⟩, fun _ _ h => Fin.ext (congrArg (Fin.val : Fin r → ℕ) h)⟩
          calc (∑ k : Fin I₀.card, ∑ i : Fin m, (N (fEmb k) ∩ L₁ i).ncard)
              = ∑ k ∈ Finset.univ.map fEmb, ∑ i : Fin m, (N k ∩ L₁ i).ncard :=
                (Finset.sum_map Finset.univ fEmb (fun k : Fin r => ∑ i : Fin m, (N k ∩ L₁ i).ncard)).symm
            _ ≤ ∑ k ∈ Finset.univ, ∑ i : Fin m, (N k ∩ L₁ i).ncard :=
                Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ ≤ m * (3 ^ r - 1) := hNL₁_sum
  have hsum_Irem : (∑ i : Fin m, ∑ j ∈ Irem, (φ '' L i ∩ G j).ncard) ≤ m * 3 ^ r * n := by
    have hcard_rem : Irem.card ≤ n := (Finset.card_le_univ Irem).trans (by simp)
    have hpow : 1 ≤ 3 ^ r := Nat.one_le_pow r 3 (by norm_num)
    have hmul_eq : m + m * (3 ^ r - 1) = m * 3 ^ r := by zify [hpow]; ring
    calc (∑ i : Fin m, ∑ j ∈ Irem, (φ '' L i ∩ G j).ncard)
        = ∑ i : Fin m, ∑ j : Fin Irem.card, (γ '' L₁ i ∩ G_rem j).ncard := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hφL i, ← Finset.sum_coe_sort Irem]
          exact (Fintype.sum_equiv eRem (fun j => (γ '' L₁ i ∩ G_rem j).ncard)
            (fun j : Irem => (γ '' L₁ i ∩ G j.1).ncard) fun _ => rfl).symm
      _ ≤ (m + ∑ k : Fin r, ∑ i : Fin m, (N k ∩ L₁ i).ncard) * Irem.card := hγsum_rem
      _ ≤ (m + m * (3 ^ r - 1)) * n := Nat.mul_le_mul (Nat.add_le_add_left hNL₁_sum m) hcard_rem
      _ = m * 3 ^ r * n := by rw [hmul_eq]
  have htotal : (∑ i : Fin m, ∑ j : Fin n, (φ '' L i ∩ G j).ncard) ≤ m * 3 ^ (2 * n + 3 * (2 * a + b) + c) := by
    have hsplit : ∀ i : Fin m, (∑ j : Fin n, (φ '' L i ∩ G j).ncard) =
        (∑ j ∈ I₀, (φ '' L i ∩ G j).ncard) + (∑ j ∈ Irem, (φ '' L i ∩ G j).ncard) := fun i => by
      have hunion : I₀ ∪ Irem = Finset.univ := Finset.union_sdiff_of_subset (Finset.subset_univ I₀)
      have hdisj : Disjoint I₀ Irem := Finset.disjoint_sdiff
      rw [← Finset.sum_union hdisj, hunion]
    have hpow_n : n + 1 ≤ 3 ^ (2 * n) := by
      have hgen : ∀ k : ℕ, k + 1 ≤ 3 ^ (2 * k) := fun k => by
        induction k with
        | zero => norm_num
        | succ k ih =>
          have h9 : 3 ^ (2 * (k + 1)) = 9 * 3 ^ (2 * k) := by rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]; ring
          omega
      exact hgen n
    have hr_le : r ≤ 3 * (2 * a + b) + c := by omega
    calc (∑ i : Fin m, ∑ j : Fin n, (φ '' L i ∩ G j).ncard)
        = (∑ i : Fin m, ∑ j ∈ I₀, (φ '' L i ∩ G j).ncard) + (∑ i : Fin m, ∑ j ∈ Irem, (φ '' L i ∩ G j).ncard) := by
          rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => hsplit i
      _ ≤ m * (3 ^ r - 1) + m * 3 ^ r * n := Nat.add_le_add hsum_I0 hsum_Irem
      _ ≤ m * 3 ^ r + m * 3 ^ r * n := Nat.add_le_add_right (Nat.mul_le_mul_left m (Nat.sub_le _ _)) _
      _ = m * ((n + 1) * 3 ^ r) := by ring
      _ ≤ m * (3 ^ (2 * n) * 3 ^ (3 * (2 * a + b) + c)) :=
          Nat.mul_le_mul_left m (Nat.mul_le_mul hpow_n (Nat.pow_le_pow_right (by norm_num) hr_le))
      _ = m * 3 ^ (2 * n + 3 * (2 * a + b) + c) := by rw [← pow_add, ← add_assoc]
  exact ⟨φ, hφfix, hφfin, htotal⟩

end GraphMinor.LPPS22
