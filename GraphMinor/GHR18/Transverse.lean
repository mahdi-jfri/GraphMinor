module

public import GraphMinor.GHR18.StripBox
public import GraphMinor.GM07.Section35

/-!
# Transversality and finite crossing for a proper `I`-arc

This file proves Step 0 of the surgery proof of Geelen–Huynh–Richter (2018), Theorem 2.6:

1. `exists_finite_cross_parallel`: given a proper `I`-arc `P` with ends `s ≠ t` and a finite
   family `Q : Fin m → Set S` of pairwise disjoint proper `I`-arcs avoiding `{s, t}`, there exist a
   `StripBox S Q` (`sb`) and a boundary-fixing homeomorphism `α : S ≃ₜ S` such that `P₁ := α '' P`
   avoids all collar tips `sb.tip i` and meets `⋃ i, Q i` in a finite set.
2. `exists_transverse_arc`: given such `P₁` and `sb`, by iteratively straightening one intersection
   point at a time inside tiny interior discs `sb.f i '' closedBall (x₀ : ℂ) ε ⊆ (bd S)ᶜ` (replacing
   bounces by straight chords and crossings by 3-segment polygonal arcs crossing `{im = 0}`
   vertically), we obtain a shrunk strip box `sb'` and a proper `I`-arc `P_tr` with the same
   boundary cohomology class (`BdCohRel s t`) and `w₁` integral as `P₁`, such that `P_tr` meets each
   box `sb'.box i` in a finite union of vertical segments `sb'.f i '' ({x} ×ℂ Icc (-sb'.δ) sb'.δ)`.
-/

@[expose] public section

namespace GraphMinor.GHR18

open Set Topology Metric Complex Function GraphMinor.Surface GraphMinor.GM07

variable {S : Type} [TopologicalSpace S]

/-! ### Section 1: Moving `P` by a boundary-fixing homeomorphism to cross `Q` finitely often -/

section FiniteCross

/-- Move a proper `I`-arc `P` by a boundary-fixing homeomorphism `α : S ≃ₜ S` into a lens disc
around `P` so that `α '' P` avoids all collar tips of a `StripBox S Q` and meets `⋃ i, Q i` in a
finite set. -/
theorem exists_finite_cross_parallel (hS : IsSurface S)
    {P : Set S} {s t : S} (hst : s ≠ t) (hPb : P ∩ bd S = {s, t}) (hPl : IsLineWithEnds P s t)
    {m : ℕ} (Q : Fin m → Set S)
    (hQ : ∀ i, ∃ u v, u ≠ v ∧ IsLineWithEnds (Q i) u v ∧ Q i ∩ bd S = {u, v})
    (hQdisj : Pairwise fun i j => Disjoint (Q i) (Q j))
    (hsQ : ∀ i, s ∉ Q i) (htQ : ∀ i, t ∉ Q i) :
    ∃ (sb : StripBox S Q) (α : S ≃ₜ S),
      (∀ x ∈ bd S, α x = x) ∧
      (∀ i, Disjoint (α '' P) (sb.tip i)) ∧
      ((α '' P) ∩ ⋃ i, Q i).Finite := by
  classical
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have hPc : IsClosed P := hPl.isCompact.isClosed
  have hPbdQ : ∀ i, Disjoint P (Q i ∩ bd S) := fun i => by
    rw [Set.disjoint_left]; rintro x hxP ⟨hxQ, hxbd⟩
    rcases (hPb ▸ ⟨hxP, hxbd⟩ : x ∈ ({s, t} : Set S)) with rfl | h
    · exact hsQ i hxQ
    · rw [mem_singleton_iff.mp h] at hxQ; exact htQ i hxQ
  obtain ⟨sb, hsbP⟩ := exists_stripBox hS Q hQ hQdisj hPc hPbdQ
  obtain ⟨T, _, j, K, hT, hj, hK, hcov, hinter, -⟩ := exists_capAll S hS
  have : T2Space T := hT.2.1
  have hji := hj.injective
  have hman : ∀ x : T, IsManifoldPoint x := fun x => (hT.2.2 x).isManifoldPoint
  -- Build a thin closed lens disc `DT` around `j '' P` avoiding `K ∪ ⋃ i, j '' sb.tip i`:
  let Z_lens : Set T := K ∪ j '' (⋃ i, sb.tip i)
  have hZ_lens_c : IsClosed Z_lens :=
    hK.union (hj.isClosedMap _ (isClosed_iUnion_of_finite fun i => sb.htip_closed i))
  have hPl' : IsLineWithEnds (j '' P) (j s) (j t) := hPl.map_of_embedding hj.isEmbedding
  have hst' : j s ≠ j t := fun h => hst (hji h)
  have hPZ : (j '' P) ∩ Z_lens ⊆ {j s, j t} := by
    rintro _ ⟨⟨x, hxP, rfl⟩, hK' | ⟨y, hy, he⟩⟩
    · have hxbd : x ∈ bd S := by
        have : j x ∈ range j ∩ K := ⟨mem_range_self _, hK'⟩
        rw [hinter] at this; obtain ⟨w, hw, hwe⟩ := this; exact hji hwe ▸ hw
      rcases (hPb ▸ ⟨hxP, hxbd⟩ : x ∈ ({s, t} : Set S)) with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (congrArg j (mem_singleton_iff.mp h))
    · obtain ⟨i, hytip⟩ := mem_iUnion.mp hy
      exact (Set.disjoint_left.mp (hsbP i) hxP (hji he ▸ hytip)).elim
  obtain ⟨DT, _, _, hDT, hPDT, hDTZ, hsDT, htDT, hbdP, -⟩ :=
    exists_edge_lens hT hPl' hst' hZ_lens_c hPZ
  -- Pull `DT` back to a closed disc `D ⊆ S`:
  have hDT_rng : DT ⊆ range j := fun y hy => by
    by_contra hnr
    have hyK : y ∈ K := (hcov ▸ mem_univ y).resolve_left hnr
    rcases hDTZ ⟨hy, Or.inl hyK⟩ with rfl | h
    · exact hnr (mem_range_self s)
    · rw [mem_singleton_iff.mp h] at hnr; exact hnr (mem_range_self t)
  let D : Set S := j ⁻¹' DT
  have hjD : j '' D = DT := image_preimage_eq_iff.mpr hDT_rng
  have : Nonempty S := ⟨s⟩
  have hsPb : s ∈ P ∩ bd S := hPb.symm ▸ Or.inl rfl
  have htPb : t ∈ P ∩ bd S := hPb.symm ▸ Or.inr rfl
  have hD_disc : IsClosedDisc D ∧ discBd D = j ⁻¹' discBd DT := by
    have hj_inv : ∃ g : T → S, ContinuousOn g DT ∧ (∀ y ∈ DT, j (g y) = y) ∧ (∀ x ∈ D, g (j x) = x) := by
      obtain ⟨jinv, hjc, hjl⟩ := exists_inv_of_compactOn isCompact_univ hj.continuous.continuousOn hji.injOn
      refine ⟨jinv, hjc.mono (by rwa [image_univ]), fun y hy => ?_, fun x _ => hjl (mem_univ x)⟩
      obtain ⟨x, rfl⟩ := hDT_rng hy
      rw [hjl (mem_univ x)]
    obtain ⟨g, hgc, hgj, hgx⟩ := hj_inv
    have hgim : g '' DT = D := by
      ext x; constructor
      · rintro ⟨y, hy, rfl⟩; show j (g y) ∈ DT; rw [hgj y hy]; exact hy
      · intro hx; exact ⟨j x, hx, hgx x hx⟩
    have hres := hDT.image hgc hj.continuous.continuousOn (fun y hy => hgj y hy)
    rw [hgim] at hres
    refine ⟨hres.1, ?_⟩
    rw [hres.2]; ext x; constructor
    · rintro ⟨y, hy, rfl⟩; show j (g y) ∈ discBd DT; rw [hgj y (discBd_subset DT hy)]; exact hy
    · intro hx; exact ⟨j x, hx, hgx x (discBd_subset DT hx)⟩
  have hD : IsClosedDisc D := hD_disc.1
  have hPD : P ⊆ D := fun x hx => hPDT ⟨x, hx, rfl⟩
  have hsD : s ∈ discBd D := hD_disc.2 ▸ hsDT
  have htD : t ∈ discBd D := hD_disc.2 ▸ htDT
  have hP_discBd : P ∩ discBd D = {s, t} := by
    ext x; constructor
    · rintro ⟨hxP, hxbd⟩
      have : j x ∈ discBd DT ∩ j '' P := ⟨(Set.ext_iff.mp hD_disc.2 x).mp hxbd, x, hxP, rfl⟩
      rcases hbdP this with h | h
      · exact Or.inl (hji h)
      · exact Or.inr (hji (mem_singleton_iff.mp h))
    · rintro (rfl | h)
      · exact ⟨hsPb.1, hsD⟩
      · rw [mem_singleton_iff.mp h]; exact ⟨htPb.1, htD⟩
  have hD_bd : D ∩ bd S ⊆ {s, t} := by
    rintro x ⟨hxD, hxbd⟩
    have hK' : j x ∈ K := (hinter ▸ mem_image_of_mem j hxbd : j x ∈ range j ∩ K).2
    rcases hDTZ ⟨hxD, Or.inl hK'⟩ with h | h
    · exact Or.inl (hji h)
    · exact Or.inr (hji (mem_singleton_iff.mp h))
  have hD_int_bd : Disjoint (discInt D) (bd S) := by
    rw [Set.disjoint_left]; intro x hxI hxbd
    rcases hD_bd ⟨hxI.1, hxbd⟩ with rfl | h
    · exact hxI.2 hsD
    · rw [mem_singleton_iff.mp h] at hxI; exact hxI.2 htD
  have hD_tips : ∀ i, Disjoint D (sb.tip i) := fun i => by
    rw [Set.disjoint_left]; intro x hxD hxtip
    have hZ : j x ∈ Z_lens := Or.inr ⟨x, mem_iUnion.mpr ⟨i, hxtip⟩, rfl⟩
    rcases hDTZ ⟨hxD, hZ⟩ with h | h
    · exact hsQ i (hji h ▸ hxtip.1)
    · exact htQ i (hji (mem_singleton_iff.mp h) ▸ hxtip.1)
  -- Join `s` and `t` inside `discInt D` with finitely many crossings of `⋃ i, Q i`:
  let QU : Set S := ⋃ i, Q i
  have hQUc : IsClosed QU := isClosed_iUnion_of_finite fun i => by
    obtain ⟨_, _, _, hl, _⟩ := hQ i; exact hl.isCompact.isClosed
  have hsQU : s ∉ QU := fun h => by obtain ⟨i, hi⟩ := mem_iUnion.mp h; exact hsQ i hi
  have htQU : t ∉ QU := fun h => by obtain ⟨i, hi⟩ := mem_iUnion.mp h; exact htQ i hi
  obtain ⟨w₁, K₁, hw₁, hw₁Q, hJ₁, hK₁⟩ := exists_start_off hj.isEmbedding hD hsD hQUc hsQU
  obtain ⟨w₂, K₂, hw₂, hw₂Q, hJ₂, hK₂⟩ := exists_start_off hj.isEmbedding hD htD hQUc htQU
  let O' : Set T := j '' discInt D
  let Z' : Set T := j '' QU
  have hO'eq : O' = discInt DT := by
    show j '' (D \ discBd D) = DT \ discBd DT
    rw [image_sdiff hji, hjD, hD_disc.2, image_preimage_eq_iff.mpr ((discBd_subset DT).trans hDT_rng)]
  have hO'o : IsOpen O' := hO'eq ▸ hDT.isOpen_discInt hman
  have hO'c : IsPreconnected O' := hD.isPreconnected_discInt.image j hj.continuous.continuousOn
  have hZ'c : IsClosed Z' := hj.isClosedMap _ hQUc
  -- Local arc condition for `Z'` inside `O'`:
  have hloc : ∀ z ∈ O' ∩ Z', ∃ (a : unitInterval → T) (W : Set T),
      IsArcMap a ∧ IsOpen W ∧ z ∈ W ∧ z ∈ a '' Ioo 0 1 ∧ range a ⊆ Z' ∧ Z' ∩ W ⊆ range a := by
    rintro _ ⟨⟨x, hxI, rfl⟩, ⟨x', hx'Q, he⟩⟩
    obtain rfl := (hji he).symm
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx'Q
    have hxmid : x ∈ sb.mid i := by
      by_contra hnot
      exact Set.disjoint_left.mp (hD_tips i) hxI.1 ⟨hxi, hnot⟩
    obtain ⟨z₀, hz₀, hfz₀⟩ := hxmid
    rw [Complex.mem_reProdIm] at hz₀
    have hre : z₀.re ∈ Ioo (sb.a i) (sb.b i) := hz₀.1
    have him : z₀.im = 0 := mem_singleton_iff.mp hz₀.2
    let r := min (min (z₀.re - sb.a i) (sb.b i - z₀.re)) sb.δ / 2
    have hr : 0 < r := half_pos (lt_min (lt_min (by linarith [hre.1]) (by linarith [hre.2])) sb.hδ)
    have hr1 : r ≤ (z₀.re - sb.a i) / 2 := div_le_div_of_nonneg_right ((min_le_left _ _).trans (min_le_left _ _)) (by norm_num)
    have hr2 : r ≤ (sb.b i - z₀.re) / 2 := div_le_div_of_nonneg_right ((min_le_left _ _).trans (min_le_right _ _)) (by norm_num)
    have hr3 : r ≤ sb.δ / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    let rect_loc : Set ℂ := Ioo (z₀.re - r) (z₀.re + r) ×ℂ Ioo (-r) r
    have hrect_sub : rect_loc ⊆ sb.openRect i := fun w hw => by
      simp only [rect_loc, StripBox.openRect, Complex.mem_reProdIm] at hw ⊢
      exact ⟨⟨by linarith [hw.1.1, hre.1], by linarith [hw.1.2, hre.2]⟩, ⟨by linarith [hw.2.1, sb.hδ], by linarith [hw.2.2, sb.hδ]⟩⟩
    have hrect_cc : Icc (z₀.re - r) (z₀.re + r) ×ℂ Icc (-r) r ⊆ sb.rect i := fun w hw => by
      simp only [StripBox.rect, Complex.mem_reProdIm] at hw ⊢
      exact ⟨⟨by linarith [hw.1.1, hre.1], by linarith [hw.1.2, hre.2]⟩, ⟨by linarith [hw.2.1, sb.hδ], by linarith [hw.2.2, sb.hδ]⟩⟩
    let U_S : Set S := sb.f i '' rect_loc
    have hU_So : IsOpen U_S := sb.hfo i rect_loc (isOpen_Ioo.reProdIm isOpen_Ioo) hrect_sub
    obtain ⟨W₀, hW₀o, hW₀eq⟩ := hj.isInducing.isOpen_iff.mp hU_So
    let W : Set T := W₀ ∩ Kᶜ
    have hWo : IsOpen W := hW₀o.inter hK.isOpen_compl
    have hxU : x ∈ U_S := ⟨z₀, Complex.mem_reProdIm.mpr ⟨⟨by linarith, by linarith⟩, by rw [him]; exact ⟨by linarith, hr⟩⟩, hfz₀⟩
    have hxK : j x ∉ K := fun hK' => Set.disjoint_left.mp hD_int_bd hxI
      (by have : j x ∈ range j ∩ K := ⟨mem_range_self _, hK'⟩; rw [hinter] at this; obtain ⟨y, hy, he⟩ := this; exact hji he ▸ hy)
    let segC : unitInterval → ℂ := fun u => ((z₀.re - r + 2 * r * u.1 : ℝ) : ℂ)
    have hseg_in : ∀ u : unitInterval, segC u ∈ sb.rect i := fun u =>
      hrect_cc (Complex.mem_reProdIm.mpr
        ⟨⟨by simp only [segC, ofReal_re]; nlinarith [u.2.1, hr], by simp only [segC, ofReal_re]; nlinarith [u.2.2, hr]⟩,
         ⟨by simp only [segC, ofReal_im]; linarith, by simp only [segC, ofReal_im]; exact hr.le⟩⟩)
    let a : unitInterval → T := fun u => j (sb.f i (segC u))
    have ha : IsArcMap a := by
      refine ⟨hj.continuous.comp ((sb.hfc i).comp_continuous (by unfold segC; fun_prop) hseg_in), fun u v huv => ?_⟩
      have h1 := sb.hfi i (hseg_in u) (hseg_in v) (hji huv)
      have h2 := congrArg Complex.re h1
      simp only [segC, ofReal_re] at h2
      exact Subtype.ext (by nlinarith)
    refine ⟨a, W, ha, hWo, ⟨(Set.ext_iff.mp hW₀eq x).mpr hxU, hxK⟩,
      ⟨⟨1 / 2, by norm_num, by norm_num⟩, ⟨by show (0 : ℝ) < 1 / 2; norm_num, by show (1 / 2 : ℝ) < 1; norm_num⟩, ?_⟩, ?_, ?_⟩
    · show j (sb.f i (segC ⟨1 / 2, by norm_num, by norm_num⟩)) = j x
      rw [← hfz₀]; congr 2; apply Complex.ext <;> simp [segC, him]; ring
    · rintro _ ⟨u, rfl⟩
      exact ⟨sb.f i (segC u), mem_iUnion.mpr ⟨i, (sb.hQ_eq i _ (hseg_in u)).mpr (by simp [segC])⟩, rfl⟩
    · rintro _ ⟨⟨y, hyQU, rfl⟩, hyW⟩
      have hyU : y ∈ U_S := (Set.ext_iff.mp hW₀eq y).mp hyW.1
      obtain ⟨w, hw, rfl⟩ := hyU
      have hw_rect : w ∈ sb.rect i := hrect_cc (Complex.mem_reProdIm.mpr
        ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hw).1, Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hw).2⟩)
      obtain ⟨k, hyk⟩ := mem_iUnion.mp hyQU
      have hki : k = i := by
        by_contra hne
        exact Set.disjoint_left.mp (sb.hQ_other i k (Ne.symm hne)) ⟨w, hw_rect, rfl⟩ hyk
      rw [hki] at hyk
      have hwim : w.im = 0 := (sb.hQ_eq i w hw_rect).mp hyk
      have hwre := (Complex.mem_reProdIm.mp hw).1
      let uval : ℝ := (w.re - (z₀.re - r)) / (2 * r)
      have hu0 : 0 ≤ uval := div_nonneg (by linarith [hwre.1]) (by linarith)
      have hu1 : uval ≤ 1 := (div_le_one (by linarith)).mpr (by linarith [hwre.2])
      refine ⟨⟨uval, hu0, hu1⟩, ?_⟩
      show j (sb.f i (segC ⟨uval, hu0, hu1⟩)) = j (sb.f i w)
      congr 2; apply Complex.ext
      · simp only [segC, ofReal_re, uval]; field_simp [hr.ne']; ring
      · simp [segC, hwim]
  have hmemO : ∀ {x}, x ∈ discInt D → x ∉ QU → j x ∈ O' \ Z' := fun {x} h1 h2 =>
    ⟨⟨x, h1, rfl⟩, fun ⟨x', h3, e⟩ => h2 (hji e ▸ h3)⟩
  obtain ⟨K₃, h3O, h3Z, hJ₃⟩ := finReach_of_connected hT hO'o hO'c hZ'c hloc (hmemO hw₁ hw₁Q) (hmemO hw₂ hw₂Q)
  have hJ : JoinedIn (K₁ ∪ K₃ ∪ K₂) (j s) (j t) :=
    ((hJ₁.mono (subset_union_left.trans subset_union_left)).trans
      (hJ₃.mono (subset_union_right.trans subset_union_left))).trans
      (hJ₂.symm.mono subset_union_right)
  obtain ⟨L, hLs, hLl⟩ := ((joinedIn_iff_eq_or_exists_isLineWithEnds hJ.source_mem hJ.target_mem).mp hJ).resolve_left hst'
  have hKr : K₁ ∪ K₃ ∪ K₂ ⊆ range j := by
    rintro z ((hz | hz) | hz)
    · rcases hK₁ hz with rfl | ⟨x, -, rfl⟩ <;> exact mem_range_self _
    · obtain ⟨x, -, rfl⟩ := h3O hz; exact mem_range_self _
    · rcases hK₂ hz with rfl | ⟨x, -, rfl⟩ <;> exact mem_range_self _
  obtain ⟨u', v', e1, e2, hP₁l⟩ := hLl.pull hj.isEmbedding (hLs.trans hKr)
  obtain rfl := hji e1
  obtain rfl := hji e2
  let P₁ : Set S := j ⁻¹' L
  have hinner : ∀ x ∈ P₁, x ≠ u' → x ≠ v' → x ∈ discInt D := fun x hx h1 h2 => by
    rcases hLs hx with (h3 | h3) | h3
    · rcases hK₁ h3 with h4 | ⟨x', h4, e⟩
      · exact (h1 (hji h4)).elim
      · exact hji e ▸ h4.1
    · obtain ⟨x', h4, e⟩ := h3O h3; exact hji e ▸ h4
    · rcases hK₂ h3 with h4 | ⟨x', h4, e⟩
      · exact (h2 (hji h4)).elim
      · exact hji e ▸ h4.1
  have hP₁D : P₁ ⊆ D := fun x hx => by
    by_cases h1 : x = u'; · exact h1 ▸ discBd_subset D hsD
    by_cases h2 : x = v'; · exact h2 ▸ discBd_subset D htD
    exact (hinner x hx h1 h2).1
  have hP₁_discBd : P₁ ∩ discBd D = {u', v'} := by
    ext x; constructor
    · rintro ⟨hxP, hxbd⟩
      by_cases h1 : x = u'; · exact Or.inl h1
      by_cases h2 : x = v'; · exact Or.inr h2
      exact ((hinner x hxP h1 h2).2 hxbd).elim
    · rintro (rfl | h)
      · obtain ⟨f, hf0, -⟩ := hP₁l; exact ⟨hf0 ▸ (f 0).2, hsD⟩
      · rw [mem_singleton_iff.mp h]; obtain ⟨f, -, hf1⟩ := hP₁l; exact ⟨hf1 ▸ (f 1).2, htD⟩
  have hP₁_fin : (P₁ ∩ QU).Finite := by
    have hfin : (({j u', j v'} : Set T) ∪ (K₃ ∩ Z')).Finite :=
      ((finite_singleton _).union (finite_singleton _)).union h3Z
    refine Finite.of_finite_image (hfin.subset ?_) hji.injOn
    rintro _ ⟨x, ⟨hx, hxQ⟩, rfl⟩
    by_cases h1 : x = u'; · exact Or.inl (Or.inl (congrArg j h1))
    by_cases h2 : x = v'; · exact Or.inl (Or.inr (congrArg j h2))
    rcases hLs hx with (h3 | h3) | h3
    · rcases hK₁ h3 with h4 | ⟨x', h4, e⟩
      · exact (h1 (hji h4)).elim
      · exact (h4.2 (hji e ▸ hxQ)).elim
    · exact Or.inr ⟨h3, x, hxQ, rfl⟩
    · rcases hK₂ h3 with h4 | ⟨x', h4, e⟩
      · exact (h2 (hji h4)).elim
      · exact (h4.2 (hji e ▸ hxQ)).elim
  obtain ⟨α, hαP, hαfix⟩ := exists_chord_homeo hS.2.2 hD hPD hP₁D hst hPl hP₁l hP_discBd hP₁_discBd
  refine ⟨sb, α, fun x hx => hαfix x (fun hI => Set.disjoint_left.mp hD_int_bd hI hx),
    fun i => (hD_tips i).mono_left (hαP.symm ▸ hP₁D), hαP.symm ▸ hP₁_fin⟩

end FiniteCross

/-! ### Section 2: Splitting `cocInt` on 3 subintervals and disc-local arc replacement -/

section ArcReplace

/-- Splitting `cocInt φ γ` into three subintervals `[0, u]`, `[u, v]`, `[v, 1]`. -/
theorem cocInt_split_three {A : Type} [AddCommGroup A] {φ : S → S → A} (hφ : IsCoc φ)
    {γ : ℝ → S} (hγc : ContinuousOn γ (Icc 0 1))
    {u v : ℝ} (hu0 : 0 < u) (huv : u < v) (hv1 : v < 1) :
    cocInt φ γ =
      cocInt φ (fun r => γ (lin 0 u r)) +
      (cocInt φ (fun r => γ (lin u v r)) + cocInt φ (fun r => γ (lin v 1 r))) := by
  let γ₁ : ℝ → S := fun r => γ (lin 0 u r)
  let γ₂ : ℝ → S := fun r => γ (lin u v r)
  let γ₃ : ℝ → S := fun r => γ (lin v 1 r)
  have hlin_in : ∀ {a b r : ℝ}, 0 ≤ a → a ≤ b → b ≤ 1 → r ∈ Icc (0 : ℝ) 1 → lin a b r ∈ Icc (0 : ℝ) 1 :=
    fun {a b r} ha hab hb hr => ⟨by simp only [lin]; nlinarith [hr.1, hr.2], by simp only [lin]; nlinarith [hr.1, hr.2]⟩
  have hγ₁c : ContinuousOn γ₁ (Icc 0 1) := hγc.comp (continuousOn_lin 0 u) (fun r hr => hlin_in le_rfl hu0.le (by linarith) hr)
  have hγ₂c : ContinuousOn γ₂ (Icc 0 1) := hγc.comp (continuousOn_lin u v) (fun r hr => hlin_in hu0.le huv.le hv1.le hr)
  have hγ₃c : ContinuousOn γ₃ (Icc 0 1) := hγc.comp (continuousOn_lin v 1) (fun r hr => hlin_in (by linarith) hv1.le le_rfl hr)
  have h23_end : γ₂ 1 = γ₃ 0 := by simp [γ₂, γ₃, lin_one, lin_zero]
  have h23c : ContinuousOn (conc2 γ₂ γ₃) (Icc 0 1) := continuousOn_conc2 hγ₂c hγ₃c h23_end
  have h123_end : γ₁ 1 = conc2 γ₂ γ₃ 0 := by
    simp only [γ₁, conc2, show (0 : ℝ) ≤ 1 / 2 by norm_num, ite_true, mul_zero, γ₂, lin_one, lin_zero]
  have h123c : ContinuousOn (conc2 γ₁ (conc2 γ₂ γ₃)) (Icc 0 1) := continuousOn_conc2 hγ₁c h23c h123_end
  let ρ : ℝ → ℝ := fun r =>
    if r ≤ 1 / 2 then lin 0 u (2 * r)
    else if r ≤ 3 / 4 then lin u v (4 * r - 2)
    else lin v 1 (4 * r - 3)
  have hρc : ContinuousOn ρ (Icc 0 1) := by
    have hcov : Icc (0 : ℝ) 1 = (Icc 0 (1 / 2) ∪ Icc (1 / 2) (3 / 4)) ∪ Icc (3 / 4) 1 := by
      ext r; simp only [mem_Icc, mem_union]; constructor
      · intro hr; by_cases h1 : r ≤ 1 / 2
        · exact Or.inl (Or.inl ⟨hr.1, h1⟩)
        · by_cases h2 : r ≤ 3 / 4
          · exact Or.inl (Or.inr ⟨by linarith, h2⟩)
          · exact Or.inr ⟨by linarith, hr.2⟩
      · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) <;> exact ⟨by linarith, by linarith⟩
    rw [hcov]
    have hc1 : ContinuousOn ρ (Icc 0 (1 / 2)) :=
      ((continuousOn_lin 0 u).comp (show ContinuousOn (fun r : ℝ => 2 * r) (Icc 0 (1 / 2)) by fun_prop)
        (fun r hr => ⟨by linarith [hr.1], by linarith [hr.2]⟩)).congr fun r hr =>
        by dsimp only [ρ, Function.comp]; exact ite_eq_left hr.2
    have hc2 : ContinuousOn ρ (Icc (1 / 2) (3 / 4)) :=
      ((continuousOn_lin u v).comp (show ContinuousOn (fun r : ℝ => 4 * r - 2) (Icc (1 / 2) (3 / 4)) by fun_prop)
        (fun r hr => ⟨by linarith [hr.1], by linarith [hr.2]⟩)).congr fun r hr => by
        dsimp only [ρ, Function.comp]
        by_cases h1 : r ≤ 1 / 2
        · have he : r = 1 / 2 := le_antisymm h1 hr.1; rw [ite_eq_left h1, he]; norm_num [lin]
        · rw [ite_eq_right h1, ite_eq_left hr.2]
    have hc3 : ContinuousOn ρ (Icc (3 / 4) 1) :=
      ((continuousOn_lin v 1).comp (show ContinuousOn (fun r : ℝ => 4 * r - 3) (Icc (3 / 4) 1) by fun_prop)
        (fun r hr => ⟨by linarith [hr.1], by linarith [hr.2]⟩)).congr fun r hr => by
        dsimp only [ρ, Function.comp]
        have h1 : ¬ r ≤ 1 / 2 := by linarith [hr.1]
        rw [ite_eq_right h1]
        by_cases h2 : r ≤ 3 / 4
        · have he : r = 3 / 4 := le_antisymm h2 hr.1; rw [ite_eq_left h2, he]; norm_num [lin]
        · exact ite_eq_right h2
    exact (hc1.union_of_isClosed hc2 isClosed_Icc isClosed_Icc).union_of_isClosed hc3 (isClosed_Icc.union isClosed_Icc) isClosed_Icc
  have hρm : ∀ r ∈ Icc (0 : ℝ) 1, ρ r ∈ Icc (0 : ℝ) 1 := fun r hr => by
    dsimp only [ρ]; split_ifs with h1 h2
    · exact hlin_in le_rfl hu0.le (by linarith) ⟨by linarith [hr.1], by linarith⟩
    · exact hlin_in hu0.le huv.le hv1.le ⟨by linarith, by linarith⟩
    · exact hlin_in (by linarith) hv1.le le_rfl ⟨by linarith, by linarith [hr.2]⟩
  have hρ0 : ρ 0 = 0 := by simp [ρ, lin]
  have hρ1 : ρ 1 = 1 := by
    unfold ρ
    rw [ite_eq_right (by norm_num : ¬ (1 : ℝ) ≤ 1 / 2), ite_eq_right (by norm_num : ¬ (1 : ℝ) ≤ 3 / 4)]
    norm_num [lin]
  have hconc_eq : ∀ r ∈ Icc (0 : ℝ) 1, (γ ∘ ρ) r = conc2 γ₁ (conc2 γ₂ γ₃) r := fun r _ => by
    simp only [Function.comp, ρ, conc2, γ₁, γ₂, γ₃]
    by_cases h1 : r ≤ 1 / 2
    · simp only [ite_eq_left h1]
    · simp only [ite_eq_right h1]
      have h2_iff : 2 * r - 1 ≤ 1 / 2 ↔ r ≤ 3 / 4 := by constructor <;> intro h <;> linarith
      by_cases h2 : r ≤ 3 / 4
      · rw [ite_eq_left h2, ite_eq_left (h2_iff.mpr h2)]
        congr 2; ring
      · rw [ite_eq_right h2, ite_eq_right (mt h2_iff.mp h2)]
        congr 2; ring
  have hrep := cocInt_reparam hφ hγc hρc hρm hρ0 hρ1
  have hcongr : cocInt φ (γ ∘ ρ) = cocInt φ (conc2 γ₁ (conc2 γ₂ γ₃)) :=
    cocInt_congr hφ (hγc.comp hρc hρm) h123c hconc_eq
  rw [← hrep, hcongr, cocInt_conc2 hφ hγ₁c h23c h123_end, cocInt_conc2 hφ hγ₂c hγ₃c h23_end]

/-- Replace an arc `γ : ℝ → S` on `[u, v] ⊆ (0, 1)` by a new arc `β : ℝ → S` inside an interior
closed disc `Δ ⊆ (bd S)ᶜ` containing BOTH `γ '' Icc u v` and `β '' Icc u v`, sharing endpoints
`β u = γ u`, `β v = γ v`, and disjoint on `(u, v)` from `γ '' (Icc 0 u ∪ Icc v 1)`. Preserves
`BdCohRel s t` and `cocInt (w1 AS)`. -/
theorem replace_arc_in_disc [ConnectedSpace S] (hS : IsSurface S) (AS : SurfAtlas S)
    {s t : S} (hst : s ≠ t) {P : Set S} (hPb : P ∩ bd S = {s, t}) (hPl : IsLineWithEnds P s t)
    {γ : ℝ → S} (hγc : ContinuousOn γ (Icc 0 1)) (hγi : InjOn γ (Icc 0 1))
    (hγ0 : γ 0 = s) (hγ1 : γ 1 = t) (hγim : γ '' Icc 0 1 = P)
    {Δ : Set S} (hΔ : IsClosedDisc Δ) (hΔint : Δ ⊆ (bd S)ᶜ)
    {u v : ℝ} (hu0 : 0 < u) (huv : u < v) (hv1 : v < 1)
    (hγΔ : γ '' Icc u v ⊆ Δ)
    {β : ℝ → S} (hβc : ContinuousOn β (Icc u v)) (hβi : InjOn β (Icc u v))
    (hβu : β u = γ u) (hβv : β v = γ v) (hβΔ : β '' Icc u v ⊆ Δ)
    (hβ_hit : ∀ r ∈ Ioo u v, β r ∉ γ '' (Icc 0 u ∪ Icc v 1)) :
    let γ' : ℝ → S := fun r => if r ∈ Icc u v then β r else γ r
    let P' : Set S := γ' '' Icc 0 1
    ∃ (hPb' : P' ∩ bd S = {s, t}) (hPl' : IsLineWithEnds P' s t),
      ContinuousOn γ' (Icc 0 1) ∧ InjOn γ' (Icc 0 1) ∧ γ' 0 = s ∧ γ' 1 = t ∧
      P' \ Δ = P \ Δ ∧
      BdCohRel s t (arcCocycle hS hst hPb' hPl') (arcCocycle hS hst hPb hPl) ∧
      cocInt (w1 AS) γ' = cocInt (w1 AS) γ := by
  classical
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  intro γ' P'
  have hγ'0 : γ' 0 = s := by simp only [γ', ite_eq_right (show ¬ (0 : ℝ) ∈ Icc u v from fun h => by linarith [h.1]), hγ0]
  have hγ'1 : γ' 1 = t := by simp only [γ', ite_eq_right (show ¬ (1 : ℝ) ∈ Icc u v from fun h => by linarith [h.2]), hγ1]
  have hγ'c : ContinuousOn γ' (Icc 0 1) := by
    have hcov : Icc (0 : ℝ) 1 = (Icc 0 u ∪ Icc u v) ∪ Icc v 1 := by
      ext r; simp only [mem_Icc, mem_union]; constructor
      · intro hr; by_cases h1 : r ≤ u
        · exact Or.inl (Or.inl ⟨hr.1, h1⟩)
        · by_cases h2 : r ≤ v
          · exact Or.inl (Or.inr ⟨by linarith, h2⟩)
          · exact Or.inr ⟨by linarith, hr.2⟩
      · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) <;> exact ⟨by linarith, by linarith⟩
    rw [hcov]
    have h1 : ContinuousOn γ' (Icc 0 u) := (hγc.mono (Icc_subset_Icc_right (by linarith))).congr fun r hr => by
      dsimp only [γ']
      by_cases h : r ∈ Icc u v
      · have hru : r = u := le_antisymm hr.2 h.1; rw [ite_eq_left h, hru, hβu]
      · exact ite_eq_right h
    have h2 : ContinuousOn γ' (Icc u v) := hβc.congr fun r hr => ite_eq_left hr
    have h3 : ContinuousOn γ' (Icc v 1) := (hγc.mono (Icc_subset_Icc_left (by linarith))).congr fun r hr => by
      dsimp only [γ']
      by_cases h : r ∈ Icc u v
      · have hrv : r = v := le_antisymm h.2 hr.1; rw [ite_eq_left h, hrv, hβv]
      · exact ite_eq_right h
    exact (h1.union_of_isClosed h2 isClosed_Icc isClosed_Icc).union_of_isClosed h3 (isClosed_Icc.union isClosed_Icc) isClosed_Icc
  have hγ'i : InjOn γ' (Icc 0 1) := by
    intro r₁ hr₁ r₂ hr₂ he
    have hmem_out : ∀ r ∈ Icc (0 : ℝ) 1, r ∉ Icc u v → r ∈ Icc 0 u ∪ Icc v 1 := fun r hr hno => by
      by_cases h : r < u
      · exact Or.inl ⟨hr.1, h.le⟩
      · exact Or.inr ⟨by by_contra hv; exact hno ⟨not_lt.mp h, le_of_not_ge hv⟩, hr.2⟩
    by_cases h1 : r₁ ∈ Icc u v <;> by_cases h2 : r₂ ∈ Icc u v
    · simp only [γ', ite_eq_left h1, ite_eq_left h2] at he; exact hβi h1 h2 he
    · simp only [γ', ite_eq_left h1, ite_eq_right h2] at he
      rcases h1.1.eq_or_lt with rfl | h1a
      · rw [hβu] at he; exact hγi hr₁ hr₂ he
      · rcases h1.2.eq_or_lt with rfl | h1b
        · rw [hβv] at he; exact hγi hr₁ hr₂ he
        · exact (hβ_hit r₁ ⟨h1a, h1b⟩ ⟨r₂, hmem_out r₂ hr₂ h2, he.symm⟩).elim
    · simp only [γ', ite_eq_right h1, ite_eq_left h2] at he
      rcases h2.1.eq_or_lt with rfl | h2a
      · rw [hβu] at he; exact hγi hr₁ hr₂ he
      · rcases h2.2.eq_or_lt with rfl | h2b
        · rw [hβv] at he; exact hγi hr₁ hr₂ he
        · exact (hβ_hit r₂ ⟨h2a, h2b⟩ ⟨r₁, hmem_out r₁ hr₁ h1, he⟩).elim
    · simp only [γ', ite_eq_right h1, ite_eq_right h2] at he; exact hγi hr₁ hr₂ he
  have hPl' : IsLineWithEnds P' s t := by
    let g : unitInterval → P' := fun x => ⟨γ' x.1, x.1, x.2, rfl⟩
    have hgc : Continuous g := Continuous.subtype_mk
      (hγ'c.comp_continuous continuous_subtype_val fun x => x.2) _
    have hgb : Bijective g := ⟨fun x y h => Subtype.ext (hγ'i x.2 y.2 (congrArg Subtype.val h)),
      fun ⟨y, r, hr, hre⟩ => ⟨⟨r, hr⟩, Subtype.ext hre⟩⟩
    exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g hgb) hgc, hγ'0, hγ'1⟩
  have hsPb : s ∈ P ∩ bd S := hPb.symm ▸ Or.inl rfl
  have htPb : t ∈ P ∩ bd S := hPb.symm ▸ Or.inr rfl
  have hPb' : P' ∩ bd S = {s, t} := by
    ext x; constructor
    · rintro ⟨⟨r, hr, rfl⟩, hxbd⟩
      by_cases h1 : r ∈ Icc u v
      · rw [show γ' r = β r from ite_eq_left h1] at hxbd
        exact (hΔint (hβΔ ⟨r, h1, rfl⟩) hxbd).elim
      · rw [show γ' r = γ r from ite_eq_right h1] at hxbd ⊢
        exact hPb ▸ ⟨hγim ▸ ⟨r, hr, rfl⟩, hxbd⟩
    · rintro (rfl | h)
      · exact ⟨⟨0, ⟨le_rfl, zero_le_one⟩, hγ'0⟩, hsPb.2⟩
      · rw [mem_singleton_iff.mp h]
        exact ⟨⟨1, ⟨zero_le_one, le_rfl⟩, hγ'1⟩, htPb.2⟩
  have hagree : P' \ Δ = P \ Δ := by
    ext x; constructor
    · rintro ⟨⟨r, hr, rfl⟩, hxΔ⟩
      have hrn : r ∉ Icc u v := fun h => hxΔ (by rw [show γ' r = β r from ite_eq_left h]; exact hβΔ ⟨r, h, rfl⟩)
      rw [show γ' r = γ r from ite_eq_right hrn] at hxΔ ⊢
      exact ⟨hγim ▸ ⟨r, hr, rfl⟩, hxΔ⟩
    · rintro ⟨hxP, hxΔ⟩
      obtain ⟨r, hr, rfl⟩ := hγim ▸ hxP
      have hrn : r ∉ Icc u v := fun h => hxΔ (hγΔ ⟨r, h, rfl⟩)
      exact ⟨⟨r, hr, ite_eq_right hrn⟩, hxΔ⟩
  have hcoh : BdCohRel s t (arcCocycle hS hst hPb' hPl') (arcCocycle hS hst hPb hPl) := by
    obtain ⟨hc1, htwo1⟩ := arcCocycle_isCrossingCocycle hS hst hPb' hPl'
    obtain ⟨hc2, -⟩ := arcCocycle_isCrossingCocycle hS hst hPb hPl
    exact bdCohRel_of_agree_outside_disc hS hPl'.isCompact.isClosed hΔ hΔint hPb' hagree
      (fun z hz => htwo1 z hz.1) hc1 hc2
  have hw1_eq : cocInt (w1 AS) γ' = cocInt (w1 AS) γ := by
    have hcoc := isCoc_w1 hS AS
    rw [cocInt_split_three hcoc hγ'c hu0 huv hv1, cocInt_split_three hcoc hγc hu0 huv hv1]
    have h1 : cocInt (w1 AS) (fun r => γ' (lin 0 u r)) = cocInt (w1 AS) (fun r => γ (lin 0 u r)) := by
      have hsub0 : MapsTo (lin 0 u) (Icc 0 1) (Icc 0 1) :=
        fun r hr => ⟨by simp [lin]; nlinarith [hr.1], by simp [lin]; nlinarith [hr.1, hr.2]⟩
      refine cocInt_congr hcoc (hγ'c.comp (continuousOn_lin 0 u) hsub0) (hγc.comp (continuousOn_lin 0 u) hsub0)
        fun r hr => ?_
      dsimp only [γ']
      by_cases h : lin 0 u r ∈ Icc u v
      · have hle : lin 0 u r ≤ u := by simp only [lin]; nlinarith [hr.2]
        have heq : lin 0 u r = u := le_antisymm hle h.1
        rw [ite_eq_left h, heq, hβu]
      · exact ite_eq_right h
    have h3 : cocInt (w1 AS) (fun r => γ' (lin v 1 r)) = cocInt (w1 AS) (fun r => γ (lin v 1 r)) := by
      have hsub1 : MapsTo (lin v 1) (Icc 0 1) (Icc 0 1) :=
        fun r hr => ⟨by simp [lin]; nlinarith [hr.1, hr.2], by simp [lin]; nlinarith [hr.1, hr.2]⟩
      refine cocInt_congr hcoc (hγ'c.comp (continuousOn_lin v 1) hsub1) (hγc.comp (continuousOn_lin v 1) hsub1)
        fun r hr => ?_
      dsimp only [γ']
      by_cases h : lin v 1 r ∈ Icc u v
      · have hge : v ≤ lin v 1 r := by simp only [lin]; nlinarith [hr.1]
        have heq : lin v 1 r = v := le_antisymm h.2 hge
        rw [ite_eq_left h, heq, hβv]
      · exact ite_eq_right h
    have h2 : cocInt (w1 AS) (fun r => γ' (lin u v r)) = cocInt (w1 AS) (fun r => γ (lin u v r)) := by
      have hlin_uv : ∀ r ∈ Icc (0 : ℝ) 1, lin u v r ∈ Icc u v := fun r hr =>
        ⟨by simp only [lin]; nlinarith [hr.1], by simp only [lin]; nlinarith [hr.2]⟩
      refine cocInt_eq_of_same_ends_in_disc hS hcoc hΔ hΔint
        (hγ'c.comp (continuousOn_lin u v) fun r hr => ⟨by linarith [(hlin_uv r hr).1], by linarith [(hlin_uv r hr).2]⟩)
        (hγc.comp (continuousOn_lin u v) fun r hr => ⟨by linarith [(hlin_uv r hr).1], by linarith [(hlin_uv r hr).2]⟩)
        ?_ ?_ ?_ ?_
      · rintro _ ⟨r, hr, rfl⟩
        dsimp only
        rw [show γ' (lin u v r) = β (lin u v r) from ite_eq_left (hlin_uv r hr)]
        exact hβΔ ⟨lin u v r, hlin_uv r hr, rfl⟩
      · rintro _ ⟨r, hr, rfl⟩; exact hγΔ ⟨lin u v r, hlin_uv r hr, rfl⟩
      · simp only [lin_zero, γ', ite_eq_left (show u ∈ Icc u v from ⟨le_rfl, huv.le⟩), hβu]
      · simp only [lin_one, γ', ite_eq_left (show v ∈ Icc u v from ⟨huv.le, le_rfl⟩), hβv]
    rw [h1, h2, h3]
  exact ⟨hPb', hPl', hγ'c, hγ'i, hγ'0, hγ'1, hagree, hcoh, hw1_eq⟩

end ArcReplace

/-! ### Section 3: Straightening complex arcs inside a ball (bounce & 3-segment vertical crossing) -/

section BallPolygonal

/-- Given `z_u, z_v ∈ sphere (x₀ : ℂ) ε` (`ε > 0`, `z_u ≠ z_v`) with nonzero imaginary parts,
constructs a continuous injective complex path `α : ℝ → ℂ` on `[0, 1]` from `z_u` to `z_v` staying
in `ball (x₀ : ℂ) ε` on `(0, 1)` such that:
- If `z_u.im` and `z_v.im` have the same sign, `α` avoids `{im = 0}` completely.
- If `z_u.im` and `z_v.im` have opposite signs, `α` crosses `{im = 0}` ONLY at `(x₀ : ℂ)`, and
  inside `closedBall (x₀ : ℂ) r₀` (for some `0 < r₀ < ε`) its image is EXACTLY `{x₀} ×ℂ Icc (-r₀) r₀`. -/
private theorem exists_ball_straightener {x₀ ε : ℝ} (hε : 0 < ε)
    {zu zv : ℂ} (hzu : zu ∈ sphere (x₀ : ℂ) ε) (hzv : zv ∈ sphere (x₀ : ℂ) ε) (huv : zu ≠ zv)
    (hzu_im : zu.im ≠ 0) (hzv_im : zv.im ≠ 0) :
    ∃ (α : ℝ → ℂ),
      ContinuousOn α (Icc 0 1) ∧ InjOn α (Icc 0 1) ∧ α 0 = zu ∧ α 1 = zv ∧
      (∀ r ∈ Ioo (0 : ℝ) 1, α r ∈ ball (x₀ : ℂ) ε) ∧
      ((∀ r ∈ Icc (0 : ℝ) 1, (α r).im ≠ 0) ∨
        ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ < ε ∧
          (∀ r ∈ Icc (0 : ℝ) 1, (α r).im = 0 ↔ α r = (x₀ : ℂ)) ∧
          (α '' Icc 0 1) ∩ closedBall (x₀ : ℂ) r₀ = ({x₀} : Set ℝ) ×ℂ Icc (-r₀) r₀) := by
  -- Helper: strict convexity of `ball`: a strict convex combination of two distinct points of `closedBall` lies in `ball`!
  have hstrict_ball : ∀ {w₁ w₂ : ℂ} {t : ℝ}, w₁ ∈ closedBall (x₀ : ℂ) ε → w₂ ∈ closedBall (x₀ : ℂ) ε →
      w₁ ≠ w₂ → t ∈ Ioo (0 : ℝ) 1 → ((1 - t : ℝ) : ℂ) * w₁ + (t : ℂ) * w₂ ∈ ball (x₀ : ℂ) ε := by
    intro w₁ w₂ t h1 h2 hne ht
    rw [mem_ball, dist_eq_norm]
    have hdiff : ((1 - t : ℝ) : ℂ) * w₁ + (t : ℂ) * w₂ - (x₀ : ℂ) =
        ((1 - t : ℝ) : ℂ) * (w₁ - (x₀ : ℂ)) + (t : ℂ) * (w₂ - (x₀ : ℂ)) := by push_cast; ring
    rw [hdiff]
    have ha : ‖w₁ - (x₀ : ℂ)‖ ≤ ε := by simpa [mem_closedBall, dist_eq_norm] using h1
    have hb : ‖w₂ - (x₀ : ℂ)‖ ≤ ε := by simpa [mem_closedBall, dist_eq_norm] using h2
    have h1t : 0 < 1 - t := sub_pos.mpr ht.2
    have hsq : ‖((1 - t : ℝ) : ℂ) * (w₁ - (x₀ : ℂ)) + (t : ℂ) * (w₂ - (x₀ : ℂ))‖ ^ 2 < ε ^ 2 := by
      have hpar : ∀ a b : ℂ, ‖((1 - t : ℝ) : ℂ) * a + (t : ℂ) * b‖ ^ 2 +
          (1 - t) * t * ‖a - b‖ ^ 2 = (1 - t) * ‖a‖ ^ 2 + t * ‖b‖ ^ 2 := fun a b => by
        simp only [Complex.sq_norm, Complex.normSq_apply]
        simp only [add_re, add_im, sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero]
        ring
      have hne' : ‖(w₁ - (x₀ : ℂ)) - (w₂ - (x₀ : ℂ))‖ > 0 := by
        rw [sub_sub_sub_cancel_right]; exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)
      have ht0 : 0 < t := ht.1
      have hpos : 0 < (1 - t) * t * ‖(w₁ - (x₀ : ℂ)) - (w₂ - (x₀ : ℂ))‖ ^ 2 := by positivity
      have ha2 : ‖w₁ - (x₀ : ℂ)‖ ^ 2 ≤ ε ^ 2 := sq_le_sq' (by linarith [norm_nonneg (w₁ - (x₀ : ℂ))]) ha
      have hb2 : ‖w₂ - (x₀ : ℂ)‖ ^ 2 ≤ ε ^ 2 := sq_le_sq' (by linarith [norm_nonneg (w₂ - (x₀ : ℂ))]) hb
      nlinarith [hpar (w₁ - (x₀ : ℂ)) (w₂ - (x₀ : ℂ)), h1t, ht0, ha2, hb2, hpos]
    nlinarith [norm_nonneg (((1 - t : ℝ) : ℂ) * (w₁ - (x₀ : ℂ)) + (t : ℂ) * (w₂ - (x₀ : ℂ)))]
  -- Case 1: same sign (`0 < zu.im * zv.im`): straight chord!
  by_cases hsame : 0 < zu.im * zv.im
  · let α : ℝ → ℂ := fun r => ((1 - r : ℝ) : ℂ) * zu + (r : ℂ) * zv
    refine ⟨α, by unfold α; fun_prop, fun r₁ _ r₂ _ he => ?_, by simp [α], by simp [α],
      fun r hr => hstrict_ball (sphere_subset_closedBall hzu) (sphere_subset_closedBall hzv) huv hr, Or.inl fun r hr => ?_⟩
    · have h1 : ((r₁ - r₂ : ℝ) : ℂ) * (zv - zu) = 0 := by
        have : α r₁ - α r₂ = ((r₁ - r₂ : ℝ) : ℂ) * (zv - zu) := by simp only [α]; push_cast; ring
        rw [← this, he, sub_self]
      rcases mul_eq_zero.mp h1 with h | h
      · linarith [Complex.ofReal_eq_zero.mp h]
      · exact (huv (sub_eq_zero.mp h).symm).elim
    · have him : (α r).im = (1 - r) * zu.im + r * zv.im := by simp [α]
      rw [him]
      rcases lt_or_gt_of_ne hzu_im with h1 | h1
      · have h2 : zv.im < 0 := by nlinarith
        rcases hr.1.eq_or_lt with rfl | hr0
        · linarith
        · nlinarith [hr.2]
      · have h2 : 0 < zv.im := by nlinarith
        rcases hr.1.eq_or_lt with rfl | hr0
        · linarith
        · nlinarith [hr.2]
  -- Case 2: opposite signs (`zu.im * zv.im < 0`): 3-segment polygonal arc!
  · have hopp : zu.im * zv.im < 0 := lt_of_le_of_ne (not_lt.mp hsame) (mul_ne_zero hzu_im hzv_im)
    let σ : ℝ := if 0 < zu.im then 1 else -1
    have hσ_zu : 0 < σ * zu.im := by
      dsimp only [σ]; split_ifs with h
      · linarith
      · have : zu.im < 0 := lt_of_le_of_ne (not_lt.mp h) hzu_im; linarith
    have hσ_zv : σ * zv.im < 0 := by
      dsimp only [σ]; split_ifs with h
      · nlinarith
      · have : zu.im < 0 := lt_of_le_of_ne (not_lt.mp h) hzu_im; nlinarith
    have hσ_sq : σ ^ 2 = 1 := by dsimp only [σ]; split_ifs <;> norm_num
    let p₁ : ℂ := (x₀ : ℂ) + ((σ * (ε / 2) : ℝ) : ℂ) * I
    let p₂ : ℂ := (x₀ : ℂ) - ((σ * (ε / 2) : ℝ) : ℂ) * I
    have hp₁_ball : p₁ ∈ ball (x₀ : ℂ) ε := by
      rw [mem_ball, dist_eq_norm, show p₁ - (x₀ : ℂ) = ((σ * (ε / 2) : ℝ) : ℂ) * I by simp [p₁],
          norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      dsimp only [σ]; split_ifs <;> simp [abs_of_pos (half_pos hε)] <;> linarith
    have hp₂_ball : p₂ ∈ ball (x₀ : ℂ) ε := by
      rw [mem_ball, dist_eq_norm, show p₂ - (x₀ : ℂ) = -(((σ * (ε / 2) : ℝ) : ℂ) * I) by simp [p₂],
          norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      dsimp only [σ]; split_ifs <;> simp [abs_of_pos (half_pos hε)] <;> linarith
    have hzu_ne_p1 : zu ≠ p₁ := fun h => by
      have : dist zu (x₀ : ℂ) = ε := hzu
      have : dist p₁ (x₀ : ℂ) < ε := hp₁_ball
      rw [h] at *; linarith
    have hzv_ne_p2 : zv ≠ p₂ := fun h => by
      have : dist zv (x₀ : ℂ) = ε := hzv
      have : dist p₂ (x₀ : ℂ) < ε := hp₂_ball
      rw [h] at *; linarith
    let seg1 : ℝ → ℂ := fun t => ((1 - t : ℝ) : ℂ) * zu + (t : ℂ) * p₁
    let seg2 : ℝ → ℂ := fun t => ((1 - t : ℝ) : ℂ) * p₁ + (t : ℂ) * p₂
    let seg3 : ℝ → ℂ := fun t => ((1 - t : ℝ) : ℂ) * p₂ + (t : ℂ) * zv
    let α : ℝ → ℂ := fun r =>
      if r ≤ 1 / 3 then seg1 (3 * r)
      else if r ≤ 2 / 3 then seg2 (3 * r - 1)
      else seg3 (3 * r - 2)
    have hαc : ContinuousOn α (Icc 0 1) := by
      have hcov : Icc (0 : ℝ) 1 = (Icc 0 (1 / 3) ∪ Icc (1 / 3) (2 / 3)) ∪ Icc (2 / 3) 1 := by
        ext r; simp only [mem_Icc, mem_union]; constructor
        · intro hr; by_cases h1 : r ≤ 1 / 3
          · exact Or.inl (Or.inl ⟨hr.1, h1⟩)
          · by_cases h2 : r ≤ 2 / 3
            · exact Or.inl (Or.inr ⟨by linarith, h2⟩)
            · exact Or.inr ⟨by linarith, hr.2⟩
        · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) <;> exact ⟨by linarith, by linarith⟩
      rw [hcov]
      have hc1 : ContinuousOn α (Icc 0 (1 / 3)) :=
        (show Continuous fun r : ℝ => seg1 (3 * r) by unfold seg1; fun_prop).continuousOn.congr fun r hr => ite_eq_left hr.2
      have hc2 : ContinuousOn α (Icc (1 / 3) (2 / 3)) :=
        (show Continuous fun r : ℝ => seg2 (3 * r - 1) by unfold seg2; fun_prop).continuousOn.congr fun r hr => by
          dsimp only [α]
          by_cases h1 : r ≤ 1 / 3
          · have he : r = 1 / 3 := le_antisymm h1 hr.1; rw [ite_eq_left h1, he]; simp [seg1, seg2]
          · rw [ite_eq_right h1, ite_eq_left hr.2]
      have hc3 : ContinuousOn α (Icc (2 / 3) 1) :=
        (show Continuous fun r : ℝ => seg3 (3 * r - 2) by unfold seg3; fun_prop).continuousOn.congr fun r hr => by
          dsimp only [α]
          have h1 : ¬ r ≤ 1 / 3 := by linarith [hr.1]
          rw [ite_eq_right h1]
          by_cases h2 : r ≤ 2 / 3
          · have he : r = 2 / 3 := le_antisymm h2 hr.1; rw [ite_eq_left h2, he]; norm_num [seg2, seg3]
          · exact ite_eq_right h2
      exact (hc1.union_of_isClosed hc2 isClosed_Icc isClosed_Icc).union_of_isClosed hc3 (isClosed_Icc.union isClosed_Icc) isClosed_Icc
    -- Key formulas for `seg1`, `seg2`, `seg3`:
    have hseg1_im : ∀ t ∈ Icc (0 : ℝ) 1, 0 < σ * (seg1 t).im := fun t ht => by
      have him : (seg1 t).im = (1 - t) * zu.im + t * (σ * (ε / 2)) := by simp [seg1, p₁]
      have hcalc : σ * (seg1 t).im = (1 - t) * (σ * zu.im) + t * (ε / 2) := by
        rw [him]; calc σ * ((1 - t) * zu.im + t * (σ * (ε / 2)))
          _ = (1 - t) * (σ * zu.im) + t * σ ^ 2 * (ε / 2) := by ring
          _ = (1 - t) * (σ * zu.im) + t * (ε / 2) := by rw [hσ_sq]; ring
      rw [hcalc]
      rcases ht.1.eq_or_lt with rfl | ht0
      · linarith
      · nlinarith [ht.2]
    have hseg3_im : ∀ t ∈ Icc (0 : ℝ) 1, σ * (seg3 t).im < 0 := fun t ht => by
      have him : (seg3 t).im = (1 - t) * (-(σ * (ε / 2))) + t * zv.im := by simp [seg3, p₂]
      have hcalc : σ * (seg3 t).im = (1 - t) * (-(ε / 2)) + t * (σ * zv.im) := by
        rw [him]; calc σ * ((1 - t) * -(σ * (ε / 2)) + t * zv.im)
          _ = (1 - t) * -(σ ^ 2 * (ε / 2)) + t * (σ * zv.im) := by ring
          _ = (1 - t) * (-(ε / 2)) + t * (σ * zv.im) := by rw [hσ_sq]; ring
      rw [hcalc]
      rcases ht.1.eq_or_lt with rfl | ht0
      · linarith
      · nlinarith [ht.2]
    have hseg2_re : ∀ t : ℝ, (seg2 t).re = x₀ := fun t => by simp [seg2, p₁, p₂]; ring
    have hseg2_im : ∀ t : ℝ, (seg2 t).im = (1 - 2 * t) * (σ * (ε / 2)) := fun t => by simp [seg2, p₁, p₂]; ring
    have hseg1_re : ∀ t : ℝ, (seg1 t).re = (1 - t) * zu.re + t * x₀ := fun t => by simp [seg1, p₁]
    have hseg3_re : ∀ t : ℝ, (seg3 t).re = (1 - t) * x₀ + t * zv.re := fun t => by simp [seg3, p₂]
    -- `seg1 t` (`t < 1`) never meets `seg2 s` (`s ∈ [0, 1]`):
    have h12_disj : ∀ {t s : ℝ}, t ∈ Ico (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → seg1 t ≠ seg2 s := by
      intro t s ht hs he
      by_cases hre : zu.re = x₀
      · -- If `zu.re = x₀`, then `|zu.im| = ε`, so `σ * zu.im = ε > ε / 2`, hence `σ * (seg1 t).im > ε / 2 ≥ σ * (seg2 s).im`!
        have hnorm : |zu.im| = ε := by
          have hd : ‖zu - (x₀ : ℂ)‖ = ε := by simpa [mem_sphere, dist_eq_norm] using hzu
          have hsub : zu - (x₀ : ℂ) = (zu.im : ℂ) * I := Complex.ext (by simp [hre]) (by simp)
          rw [hsub, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at hd
          exact hd
        have hσzu : σ * zu.im = ε := by
          have : |σ * zu.im| = ε := by rw [abs_mul]; dsimp only [σ]; split_ifs <;> simp [hnorm]
          rw [abs_of_pos hσ_zu] at this; exact this
        have h1 : σ * (seg1 t).im = (1 - t) * ε + t * (ε / 2) := by
          have him : (seg1 t).im = (1 - t) * zu.im + t * (σ * (ε / 2)) := by simp [seg1, p₁]
          rw [him]; calc σ * ((1 - t) * zu.im + t * (σ * (ε / 2)))
            _ = (1 - t) * (σ * zu.im) + t * σ ^ 2 * (ε / 2) := by ring
            _ = (1 - t) * ε + t * (ε / 2) := by rw [hσzu, hσ_sq]; ring
        have h2 : σ * (seg2 s).im = (1 - 2 * s) * (ε / 2) := by
          rw [hseg2_im]; calc σ * ((1 - 2 * s) * (σ * (ε / 2)))
            _ = (1 - 2 * s) * (σ ^ 2 * (ε / 2)) := by ring
            _ = (1 - 2 * s) * (ε / 2) := by rw [hσ_sq]; ring
        have hgt : σ * (seg2 s).im < σ * (seg1 t).im := by rw [h1, h2]; nlinarith [ht.2, hs.1]
        rw [he] at hgt; exact lt_irrefl _ hgt
      · have := congrArg Complex.re he
        rw [hseg1_re, hseg2_re] at this
        have : (1 - t) * (zu.re - x₀) = 0 := by linarith
        rcases mul_eq_zero.mp this with h1 | h1
        · linarith [ht.2]
        · exact hre (sub_eq_zero.mp h1)
    -- `seg3 t` (`t > 0`) never meets `seg2 s` (`s ∈ [0, 1]`):
    have h23_disj : ∀ {s t : ℝ}, s ∈ Icc (0 : ℝ) 1 → t ∈ Ioc (0 : ℝ) 1 → seg2 s ≠ seg3 t := by
      intro s t hs ht he
      by_cases hre : zv.re = x₀
      · have hnorm : |zv.im| = ε := by
          have hd : ‖zv - (x₀ : ℂ)‖ = ε := by simpa [mem_sphere, dist_eq_norm] using hzv
          have hsub : zv - (x₀ : ℂ) = (zv.im : ℂ) * I := Complex.ext (by simp [hre]) (by simp)
          rw [hsub, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at hd
          exact hd
        have hσzv : σ * zv.im = -ε := by
          have : |σ * zv.im| = ε := by rw [abs_mul]; dsimp only [σ]; split_ifs <;> simp [hnorm]
          rw [abs_of_neg hσ_zv] at this; linarith
        have h3 : σ * (seg3 t).im = (1 - t) * (-(ε / 2)) + t * (-ε) := by
          have him : (seg3 t).im = (1 - t) * (-(σ * (ε / 2))) + t * zv.im := by simp [seg3, p₂]
          rw [him]; calc σ * ((1 - t) * -(σ * (ε / 2)) + t * zv.im)
            _ = (1 - t) * -(σ ^ 2 * (ε / 2)) + t * (σ * zv.im) := by ring
            _ = (1 - t) * (-(ε / 2)) + t * (-ε) := by rw [hσzv, hσ_sq]; ring
        have h2 : σ * (seg2 s).im = (1 - 2 * s) * (ε / 2) := by
          rw [hseg2_im]; calc σ * ((1 - 2 * s) * (σ * (ε / 2)))
            _ = (1 - 2 * s) * (σ ^ 2 * (ε / 2)) := by ring
            _ = (1 - 2 * s) * (ε / 2) := by rw [hσ_sq]; ring
        have hlt : σ * (seg3 t).im < σ * (seg2 s).im := by rw [h3, h2]; nlinarith [ht.1, hs.2]
        rw [he] at hlt; exact lt_irrefl _ hlt
      · have := congrArg Complex.re he
        rw [hseg2_re, hseg3_re] at this
        have : t * (zv.re - x₀) = 0 := by linarith
        rcases mul_eq_zero.mp this with h1 | h1
        · linarith [ht.1]
        · exact hre (sub_eq_zero.mp h1)
    -- Injectivity of `α` on `[0, 1]`:
    have hαi : InjOn α (Icc 0 1) := by
      intro r₁ hr₁ r₂ hr₂ he
      have hinj_seg : ∀ {w₁ w₂ : ℂ} {t₁ t₂ : ℝ}, w₁ ≠ w₂ →
          ((1 - t₁ : ℝ) : ℂ) * w₁ + (t₁ : ℂ) * w₂ = ((1 - t₂ : ℝ) : ℂ) * w₁ + (t₂ : ℂ) * w₂ → t₁ = t₂ := by
        intro w₁ w₂ t₁ t₂ hne h
        have h1 : ((t₁ - t₂ : ℝ) : ℂ) * (w₂ - w₁) = 0 := by
          have : (((1 - t₁ : ℝ) : ℂ) * w₁ + (t₁ : ℂ) * w₂) - (((1 - t₂ : ℝ) : ℂ) * w₁ + (t₂ : ℂ) * w₂) =
              ((t₁ - t₂ : ℝ) : ℂ) * (w₂ - w₁) := by push_cast; ring
          rw [← this, h, sub_self]
        rcases mul_eq_zero.mp h1 with h2 | h2
        · linarith [Complex.ofReal_eq_zero.mp h2]
        · exact (hne (sub_eq_zero.mp h2).symm).elim
      have hp12 : p₁ ≠ p₂ := fun h => by
        have := congrArg Complex.im h
        simp only [p₁, p₂, add_im, sub_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero, zero_add, add_zero] at this
        have : σ * (ε / 2) = 0 := by linarith
        have hσne : σ ≠ 0 := by dsimp only [σ]; split_ifs <;> norm_num
        exact (mul_ne_zero hσne (half_pos hε).ne') this
      dsimp only [α] at he
      split_ifs at he with h1a h2a h2b h1b h2c h2d h2e h2f
      · linarith [hinj_seg hzu_ne_p1 he]
      · rcases h1a.eq_or_lt with rfl | hlt
        · have he' : seg2 0 = seg2 (3 * r₂ - 1) := by simpa [seg1, seg2] using he
          linarith [hinj_seg hp12 he']
        · exact (h12_disj ⟨by linarith [hr₁.1], by linarith⟩ ⟨by linarith, by linarith⟩ he).elim
      · have h1 := hseg1_im (3 * r₁) ⟨by linarith [hr₁.1], by linarith⟩
        have h3 := hseg3_im (3 * r₂ - 2) ⟨by linarith, by linarith [hr₂.2]⟩
        rw [he] at h1; linarith
      · rcases h2c.eq_or_lt with rfl | hlt
        · have he' : seg2 (3 * r₁ - 1) = seg2 0 := by simpa [seg1, seg2] using he
          linarith [hinj_seg hp12 he']
        · exact (h12_disj ⟨by linarith [hr₂.1], by linarith⟩ ⟨by linarith, by linarith⟩ he.symm).elim
      · linarith [hinj_seg hp12 he]
      · exact (h23_disj ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith [hr₂.2]⟩ he).elim
      · have h1 := hseg1_im (3 * r₂) ⟨by linarith [hr₂.1], by linarith⟩
        have h3 := hseg3_im (3 * r₁ - 2) ⟨by linarith, by linarith [hr₁.2]⟩
        rw [he] at h3; linarith
      · exact (h23_disj ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith [hr₁.2]⟩ he.symm).elim
      · linarith [hinj_seg hzv_ne_p2.symm he]
    -- Choose `r₀` smaller than `ε / 2`, `|zu.im|`, and `|zv.im|`:
    let r₀ : ℝ := min (ε / 2) (min |zu.im| |zv.im|) / 2
    have hr₀_pos : 0 < r₀ := half_pos (lt_min (half_pos hε) (lt_min (abs_pos.mpr hzu_im) (abs_pos.mpr hzv_im)))
    have hr₀_eps2 : r₀ < ε / 2 := (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)).trans_lt (half_lt_self (half_pos hε))
    have hr₀_eps : r₀ < ε := hr₀_eps2.trans (half_lt_self hε)
    have hr₀_zu : r₀ < |zu.im| := (div_le_div_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) (by norm_num)).trans_lt
      (half_lt_self (abs_pos.mpr hzu_im))
    have hr₀_zv : r₀ < |zv.im| := (div_le_div_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) (by norm_num)).trans_lt
      (half_lt_self (abs_pos.mpr hzv_im))
    have hσzu_gt : r₀ < σ * zu.im := by
      have : |σ * zu.im| = |zu.im| := by rw [abs_mul]; dsimp only [σ]; split_ifs <;> simp
      rw [abs_of_pos hσ_zu] at this; linarith
    have hσzv_lt : σ * zv.im < -r₀ := by
      have : |σ * zv.im| = |zv.im| := by rw [abs_mul]; dsimp only [σ]; split_ifs <;> simp
      rw [abs_of_neg hσ_zv] at this; linarith
    refine ⟨α, hαc, hαi, by simp [α, seg1], by
      unfold α; rw [ite_eq_right (by norm_num : ¬ (1 : ℝ) ≤ 1 / 3), ite_eq_right (by norm_num : ¬ (1 : ℝ) ≤ 2 / 3)]
      norm_num [seg3], fun r hr => ?_, Or.inr ⟨r₀, hr₀_pos, hr₀_eps, fun r hr => ?_, ?_⟩⟩
    · dsimp only [α]; split_ifs with h1 h2
      · rcases h1.eq_or_lt with rfl | hlt
        · simpa [seg1] using hp₁_ball
        · exact hstrict_ball (sphere_subset_closedBall hzu) (ball_subset_closedBall hp₁_ball) hzu_ne_p1 ⟨by linarith [hr.1], by linarith⟩
      · have := (convex_ball (x₀ : ℂ) ε) hp₁_ball hp₂_ball (show 0 ≤ 1 - (3 * r - 1) by linarith) (show 0 ≤ 3 * r - 1 by linarith) (by ring)
        simpa [seg2, Complex.real_smul] using this
      · exact hstrict_ball (ball_subset_closedBall hp₂_ball) (sphere_subset_closedBall hzv) hzv_ne_p2.symm ⟨by linarith, by linarith [hr.2]⟩
    · constructor
      · intro him0
        dsimp only [α] at him0 ⊢
        split_ifs at him0 ⊢ with h1 h2
        · have := hseg1_im (3 * r) ⟨by linarith [hr.1], by linarith⟩; rw [him0, mul_zero] at this; linarith
        · apply Complex.ext
          · simp [hseg2_re]
          · simp [him0]
        · have := hseg3_im (3 * r - 2) ⟨by linarith, by linarith [hr.2]⟩; rw [him0, mul_zero] at this; linarith
      · intro he; rw [he]; simp
    · ext w; constructor
      · rintro ⟨⟨r, hr, rfl⟩, hwb⟩
        have hwim_le : |((α r).im)| ≤ r₀ := by
          have := Complex.abs_im_le_norm (α r - (x₀ : ℂ))
          have h1 : ‖α r - (x₀ : ℂ)‖ ≤ r₀ := by simpa [mem_closedBall, dist_eq_norm] using hwb
          simpa using this.trans h1
        dsimp only [α] at hwim_le ⊢
        split_ifs at hwim_le ⊢ with h1 h2
        · exfalso
          have him : σ * (seg1 (3 * r)).im = (1 - 3 * r) * (σ * zu.im) + (3 * r) * (ε / 2) := by
            have h' : (seg1 (3 * r)).im = (1 - 3 * r) * zu.im + (3 * r) * (σ * (ε / 2)) := by simp [seg1, p₁]
            rw [h']; calc σ * ((1 - 3 * r) * zu.im + 3 * r * (σ * (ε / 2)))
              _ = (1 - 3 * r) * (σ * zu.im) + 3 * r * σ ^ 2 * (ε / 2) := by ring
              _ = (1 - 3 * r) * (σ * zu.im) + 3 * r * (ε / 2) := by rw [hσ_sq]; ring
          have hgt : r₀ < σ * (seg1 (3 * r)).im := by
            have h3r0 : 0 ≤ 3 * r := by linarith [hr.1]
            have h3r1 : 3 * r ≤ 1 := by linarith
            rw [him]
            rcases h3r0.eq_or_lt with h0 | hpos
            · rw [← h0]; linarith [hσzu_gt]
            · nlinarith [hpos, h3r1, hσzu_gt, hr₀_eps2]
          have habs : |σ * (seg1 (3 * r)).im| = |(seg1 (3 * r)).im| := by rw [abs_mul]; dsimp only [σ]; split_ifs <;> simp
          rw [abs_of_pos (lt_trans hr₀_pos hgt)] at habs; linarith
        · rw [Complex.mem_reProdIm]
          exact ⟨mem_singleton_iff.mpr (hseg2_re _), abs_le.mp hwim_le⟩
        · exfalso
          have him : σ * (seg3 (3 * r - 2)).im = (1 - (3 * r - 2)) * (-(ε / 2)) + (3 * r - 2) * (σ * zv.im) := by
            have h' : (seg3 (3 * r - 2)).im = (1 - (3 * r - 2)) * (-(σ * (ε / 2))) + (3 * r - 2) * zv.im := by simp [seg3, p₂]
            rw [h']; calc σ * ((1 - (3 * r - 2)) * -(σ * (ε / 2)) + (3 * r - 2) * zv.im)
              _ = (1 - (3 * r - 2)) * -(σ ^ 2 * (ε / 2)) + (3 * r - 2) * (σ * zv.im) := by ring
              _ = (1 - (3 * r - 2)) * (-(ε / 2)) + (3 * r - 2) * (σ * zv.im) := by rw [hσ_sq]; ring
          have hlt : σ * (seg3 (3 * r - 2)).im < -r₀ := by
            have h3r0 : 0 ≤ 3 * r - 2 := by linarith
            have h3r1 : 3 * r - 2 ≤ 1 := by linarith [hr.2]
            rw [him]; nlinarith [h3r0, h3r1, hσzv_lt, hr₀_eps2]
          have habs : |σ * (seg3 (3 * r - 2)).im| = |(seg3 (3 * r - 2)).im| := by rw [abs_mul]; dsimp only [σ]; split_ifs <;> simp
          rw [abs_of_neg (by linarith)] at habs; linarith
      · intro hw
        rw [Complex.mem_reProdIm] at hw
        have hwre : w.re = x₀ := mem_singleton_iff.mp hw.1
        have hwim : |w.im| ≤ r₀ := abs_le.mpr hw.2
        have hw_ball : w ∈ closedBall (x₀ : ℂ) r₀ := by
          rw [mem_closedBall, dist_eq_norm, show w - (x₀ : ℂ) = (w.im : ℂ) * I by apply Complex.ext <;> simp [hwre],
              norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
          exact hwim
        -- Solve `seg2 t = w`: `(1 - 2*t) * (σ * ε / 2) = w.im`, i.e. `t = (1 - σ * w.im / (ε / 2)) / 2 ∈ (0, 1)`!
        let tval : ℝ := (1 - σ * w.im / (ε / 2)) / 2
        have habs_sw : |σ * w.im| ≤ r₀ := by rw [abs_mul]; dsimp only [σ]; split_ifs <;> simpa using hwim
        have hlt_eps : |σ * w.im| < ε / 2 := habs_sw.trans_lt hr₀_eps2
        have hdiv_lt : |σ * w.im / (ε / 2)| < 1 := by
          rw [abs_div, abs_of_pos (half_pos hε), div_lt_one (half_pos hε)]; exact hlt_eps
        have ht0 : 0 < tval := by simp only [tval]; linarith [(abs_lt.mp hdiv_lt).2]
        have ht1 : tval < 1 := by simp only [tval]; linarith [(abs_lt.mp hdiv_lt).1]
        let r : ℝ := (tval + 1) / 3
        refine ⟨⟨r, ⟨by linarith [show r = (tval + 1) / 3 from rfl, ht0], by linarith [show r = (tval + 1) / 3 from rfl, ht1]⟩, ?_⟩, hw_ball⟩
        have hr1 : ¬ r ≤ 1 / 3 := by simp only [r]; linarith
        have hr2 : r ≤ 2 / 3 := by simp only [r]; linarith
        simp only [α, ite_eq_right hr1, ite_eq_left hr2]
        apply Complex.ext
        · rw [hseg2_re, hwre]
        · rw [hseg2_im]
          have h3r : 3 * r - 1 = tval := by simp only [r]; ring
          rw [h3r]
          have h12 : 1 - 2 * tval = σ * w.im / (ε / 2) := by simp only [tval]; ring
          rw [h12]
          have hne2 : ε / 2 ≠ 0 := (half_pos hε).ne'
          field_simp [hne2]
          rw [hσ_sq, one_mul]

end BallPolygonal

/-! ### Section 4: Main transversality theorem `exists_transverse_arc` -/

section TransverseMain

/-- A point `q ∈ P ∩ ⋃ i, Q i` is *good* for `(sb, P)` if inside some ball `closedBall (x₀ : ℂ) r`
in `sb.openRect i`, `P` is the exact vertical diameter `{x₀} × [-r, r]`. -/
def IsGoodAt {m : ℕ} {Q : Fin m → Set S} (sb : StripBox S Q) (P : Set S) (q : S) : Prop :=
  ∃ (i : Fin m) (x₀ r : ℝ), 0 < r ∧ closedBall (x₀ : ℂ) r ⊆ sb.openRect i ∧
    q = sb.f i (x₀ : ℂ) ∧ P ∩ sb.f i '' closedBall (x₀ : ℂ) r = sb.f i '' (({x₀} : Set ℝ) ×ℂ Icc (-r) r)

/-- Single straightening step: given an arc `P` with finitely many crossings `F = P ∩ ⋃ i, Q i`
and a bad crossing `q ∈ F` (`¬ IsGoodAt sb P q`), modify `P` inside a tiny interior ball around
`q` to either eliminate `q` (same-side bounce) or make `q` good (3-segment vertical crossing),
preserving all already-good crossings, `BdCohRel s t`, and `cocInt (w1 AS)`. -/
private theorem straighten_one [ConnectedSpace S] (hS : IsSurface S) (AS : SurfAtlas S)
    {m : ℕ} {Q : Fin m → Set S} (sb : StripBox S Q)
    {s t : S} (hst : s ≠ t) {P : Set S} (hPb : P ∩ bd S = {s, t}) (hPl : IsLineWithEnds P s t)
    {γ : ℝ → S} (hγc : ContinuousOn γ (Icc 0 1)) (hγi : InjOn γ (Icc 0 1))
    (hγ0 : γ 0 = s) (hγ1 : γ 1 = t) (hγim : γ '' Icc 0 1 = P)
    (hPtips : ∀ i, Disjoint P (sb.tip i)) (hPfin : (P ∩ ⋃ i, Q i).Finite)
    {q : S} (hq : q ∈ P ∩ ⋃ i, Q i) (hq_bad : ¬ IsGoodAt sb P q) :
    ∃ (P' : Set S) (γ' : ℝ → S) (hPb' : P' ∩ bd S = {s, t}) (hPl' : IsLineWithEnds P' s t),
      ContinuousOn γ' (Icc 0 1) ∧ InjOn γ' (Icc 0 1) ∧ γ' 0 = s ∧ γ' 1 = t ∧ γ' '' Icc 0 1 = P' ∧
      (∀ i, Disjoint P' (sb.tip i)) ∧
      (P' ∩ ⋃ i, Q i) ⊆ (P ∩ ⋃ i, Q i) ∧
      (∀ g ∈ P ∩ ⋃ i, Q i, IsGoodAt sb P g → g ∈ P' ∧ IsGoodAt sb P' g) ∧
      (q ∉ P' ∨ IsGoodAt sb P' q) ∧
      BdCohRel s t (arcCocycle hS hst hPb' hPl') (arcCocycle hS hst hPb hPl) ∧
      cocInt (w1 AS) γ' = cocInt (w1 AS) γ := by
  classical
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  let F : Set S := P ∩ ⋃ i, Q i
  obtain ⟨i, hqi⟩ := mem_iUnion.mp hq.2
  have hqmid : q ∈ sb.mid i := by
    by_contra hnot; exact Set.disjoint_left.mp (hPtips i) hq.1 ⟨hqi, hnot⟩
  obtain ⟨z₀, hz₀, hfz₀⟩ := hqmid
  rw [Complex.mem_reProdIm] at hz₀
  set x₀ : ℝ := z₀.re
  have hz₀_eq : z₀ = (x₀ : ℂ) := Complex.ext rfl (by simp [mem_singleton_iff.mp hz₀.2])
  have hq_eq : sb.f i (x₀ : ℂ) = q := hz₀_eq ▸ hfz₀
  have hx₀_in : x₀ ∈ Ioo (sb.a i) (sb.b i) := hz₀.1
  have hsPb : s ∈ P ∩ bd S := hPb.symm ▸ Or.inl rfl
  have htPb : t ∈ P ∩ bd S := hPb.symm ▸ Or.inr rfl
  -- Find the unique time `t₀ ∈ Ioo 0 1` with `γ t₀ = q`:
  obtain ⟨t₀, ht₀_cc, ht₀_eq⟩ := hγim ▸ hq.1
  have hq_not_bd : q ∉ bd S := fun hbd => sb.hint i ⟨(x₀ : ℂ), Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self hx₀_in, by simp [sb.hδ.le]⟩, hq_eq⟩ hbd
  have ht₀_oo : t₀ ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨lt_of_le_of_ne ht₀_cc.1 fun h => ?_, lt_of_le_of_ne ht₀_cc.2 fun h => ?_⟩
    · rw [← h, hγ0] at ht₀_eq; exact hq_not_bd (ht₀_eq ▸ hsPb.2)
    · rw [h, hγ1] at ht₀_eq; exact hq_not_bd (ht₀_eq ▸ htPb.2)
  -- For each already-good `g ∈ F`, pick its witnessing radius `r_g` and shrink if needed so `q` is not in its closed ball:
  -- Note `q ∉ sb.f j '' closedBall (x_g : ℂ) r_g` is AUTOMATIC because `P ∩ ball_g` only meets `⋃ Q` at `g`, and `q ≠ g`!
  have hgood_ball : ∀ g ∈ F, IsGoodAt sb P g → ∃ (B : Set S), IsClosed B ∧ g ∈ interior B ∧ q ∉ B ∧
      (∀ P' : Set S, P' ∩ B = P ∩ B → g ∈ P' ∧ IsGoodAt sb P' g) := by
    intro g hg ⟨j, xg, rg, hrg, hrg_sub, hgeq, hPball⟩
    have hqg : q ≠ g := fun h => hq_bad (h ▸ ⟨j, xg, rg, hrg, hrg_sub, hgeq, hPball⟩)
    let B : Set S := sb.f j '' closedBall (xg : ℂ) rg
    have hBsub : closedBall (xg : ℂ) rg ⊆ sb.rect j := hrg_sub.trans fun w hw => by
      simp only [StripBox.openRect, StripBox.rect, Complex.mem_reProdIm] at hw ⊢; exact ⟨Ioo_subset_Icc_self hw.1, Ioo_subset_Icc_self hw.2⟩
    have hBc : IsClosed B := ((isCompact_closedBall (xg : ℂ) rg).image_of_continuousOn ((sb.hfc j).mono hBsub)).isClosed
    have hqnotB : q ∉ B := fun hqB => by
      have : q ∈ P ∩ B := ⟨hq.1, hqB⟩
      rw [hPball] at this
      obtain ⟨w, hw, hwe⟩ := this
      rw [Complex.mem_reProdIm] at hw
      have hw_rect : w ∈ sb.rect j := hBsub (by
        rw [mem_closedBall, dist_eq_norm, show w - (xg : ℂ) = (w.im : ℂ) * I by apply Complex.ext <;> simp [mem_singleton_iff.mp hw.1],
            norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]; exact abs_le.mpr hw.2)
      have hji' : j = i := by
        by_contra hne; exact Set.disjoint_left.mp (sb.hQ_other j i hne) ⟨w, hw_rect, rfl⟩ (hwe ▸ hqi)
      subst hji'
      have hwim : w.im = 0 := (sb.hQ_eq j w hw_rect).mp (hwe ▸ hqi)
      have hw_eq : w = (xg : ℂ) := Complex.ext (mem_singleton_iff.mp hw.1) (by simp [hwim])
      exact hqg (hwe.symm.trans (by rw [hw_eq, hgeq]))
    have hg_int : g ∈ interior B := by
      refine interior_maximal (image_mono ball_subset_closedBall)
        (sb.hfo j _ isOpen_ball (ball_subset_closedBall.trans hrg_sub)) ⟨(xg : ℂ), mem_ball_self hrg, hgeq.symm⟩
    refine ⟨B, hBc, hg_int, hqnotB, fun P' hEq => ⟨?_, j, xg, rg, hrg, hrg_sub, hgeq, ?_⟩⟩
    · have : g ∈ P ∩ B := ⟨hg.1, interior_subset hg_int⟩
      exact (hEq.symm ▸ this).1
    · rw [hEq, hPball]
  -- Let `Avoid : Set S` be the closed set `{s, t} ∪ (F \ {q}) ∪ ⋃_{g good} B_g` avoiding `q`:
  let Ggood : Set S := {g ∈ F | IsGoodAt sb P g}
  have hGfin : Ggood.Finite := hPfin.subset (sep_subset _ _)
  have hBex : ∀ g : Ggood, ∃ B : Set S, IsClosed B ∧ q ∉ B ∧
      (∀ P' : Set S, P' ∩ B = P ∩ B → g.1 ∈ P' ∧ IsGoodAt sb P' g.1) := fun g => by
    obtain ⟨B, hBc, -, hqB, hpres⟩ := hgood_ball g.1 g.2.1 g.2.2
    exact ⟨B, hBc, hqB, hpres⟩
  choose Bg hBg_c hBg_q hBg_pres using hBex
  have : Finite Ggood := hGfin.to_subtype
  let Avoid : Set S := {s, t} ∪ (F \ {q}) ∪ (⋃ g : Ggood, Bg g)
  have hAvoid_c : IsClosed Avoid :=
    (((isClosed_singleton.union isClosed_singleton).union (hPfin.subset sdiff_subset).isClosed)).union
      (isClosed_iUnion_of_finite hBg_c)
  have hq_not_Avoid : q ∉ Avoid := by
    rintro ((h | h) | h)
    · rcases h with rfl | h'
      · exact hq_not_bd hsPb.2
      · rw [mem_singleton_iff.mp h'] at hq_not_bd; exact hq_not_bd htPb.2
    · exact h.2 rfl
    · obtain ⟨g, hqg⟩ := mem_iUnion.mp h; exact hBg_q g hqg
  -- Choose `ε > 0` so `closedBall (x₀ : ℂ) ε ⊆ sb.openRect i` and `sb.f i '' closedBall (x₀ : ℂ) ε` is disjoint from `Avoid`:
  have hpre_o : IsOpen (sb.openRect i ∩ sb.f i ⁻¹' Avoidᶜ) :=
    ((sb.hfc i).mono fun w hw => by simp only [StripBox.openRect, Complex.mem_reProdIm] at hw ⊢; exact ⟨Ioo_subset_Icc_self hw.1, Ioo_subset_Icc_self hw.2⟩).isOpen_inter_preimage
      (isOpen_Ioo.reProdIm isOpen_Ioo) hAvoid_c.isOpen_compl
  have hx₀_mem : (x₀ : ℂ) ∈ sb.openRect i ∩ sb.f i ⁻¹' Avoidᶜ :=
    ⟨Complex.mem_reProdIm.mpr ⟨hx₀_in, by simp [sb.hδ]⟩, by rw [mem_preimage, hq_eq]; exact hq_not_Avoid⟩
  obtain ⟨ε₀, hε₀, hε₀sub⟩ := Metric.isOpen_iff.mp hpre_o (x₀ : ℂ) hx₀_mem
  let ε : ℝ := ε₀ / 2
  have hε : 0 < ε := half_pos hε₀
  have hBbig_sub : closedBall (x₀ : ℂ) ε ⊆ sb.openRect i ∩ sb.f i ⁻¹' Avoidᶜ :=
    (closedBall_subset_ball (half_lt_self hε₀)).trans hε₀sub
  have hBbig_rect : closedBall (x₀ : ℂ) ε ⊆ sb.rect i := fun w hw => by
    have hmem := (hBbig_sub hw).1; simp only [StripBox.openRect, StripBox.rect, Complex.mem_reProdIm] at hmem ⊢; exact ⟨Ioo_subset_Icc_self hmem.1, Ioo_subset_Icc_self hmem.2⟩
  let Δbig : Set S := sb.f i '' closedBall (x₀ : ℂ) ε
  obtain ⟨hΔbig_disc, hΔbig_int⟩ := sb.isClosedDisc_subball i hε hBbig_rect
  have hΔbig_disj : Disjoint Δbig Avoid := by
    rw [Set.disjoint_left]; rintro _ ⟨w, hw, rfl⟩ hA; exact (hBbig_sub hw).2 hA
  -- Step A: choose `η > 0` so `γ '' Icc (t₀ - η) (t₀ + η) ⊆ sb.f i '' ball (x₀ : ℂ) ε ⊆ Δbig`:
  let Ubig : Set S := sb.f i '' ball (x₀ : ℂ) ε
  have hUbig_o : IsOpen Ubig := sb.hfo i _ isOpen_ball (ball_subset_closedBall.trans fun w hw => (hBbig_sub hw).1)
  have ht₀_Ubig : γ t₀ ∈ Ubig := ⟨(x₀ : ℂ), mem_ball_self hε, hq_eq.trans ht₀_eq.symm⟩
  have hγ_pre : Icc (0 : ℝ) 1 ∩ γ ⁻¹' Ubig ∈ 𝓝[Icc 0 1] t₀ := by
    have := (hγc t₀ ht₀_cc).preimage_mem_nhdsWithin (hUbig_o.mem_nhds ht₀_Ubig)
    exact Filter.inter_mem self_mem_nhdsWithin this
  obtain ⟨η₀, hη₀, hη₀sub⟩ := Metric.mem_nhdsWithin_iff.mp hγ_pre
  let η : ℝ := min (η₀ / 2) (min t₀ (1 - t₀) / 2)
  have hη : 0 < η := lt_min (half_pos hη₀) (half_pos (lt_min ht₀_oo.1 (sub_pos.mpr ht₀_oo.2)))
  have hη_t0 : 0 < t₀ - η := by
    have : η ≤ t₀ / 2 := (min_le_right _ _).trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
    linarith [ht₀_oo.1]
  have hη_t1 : t₀ + η < 1 := by
    have : η ≤ (1 - t₀) / 2 := (min_le_right _ _).trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
    linarith [ht₀_oo.2]
  have hγ_near : ∀ r ∈ Icc (t₀ - η) (t₀ + η), γ r ∈ Ubig := fun r hr => by
    have hr_in : r ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hr.1], by linarith [hr.2]⟩
    have hdist : r ∈ ball t₀ η₀ := by
      rw [mem_ball, Real.dist_eq, abs_lt]
      have h1 : η ≤ η₀ / 2 := min_le_left _ _
      exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
    exact (hη₀sub ⟨hdist, hr_in⟩).2
  -- Step B: choose `ε' ∈ (0, ε)` so `γ '' (Icc 0 1 \ Ioo (t₀ - η) (t₀ + η))` is disjoint from `sb.f i '' closedBall (x₀ : ℂ) ε'`:
  let OutT : Set ℝ := Icc 0 (t₀ - η) ∪ Icc (t₀ + η) 1
  have hOutT_cpt : IsCompact OutT := isCompact_Icc.union isCompact_Icc
  have hOutT_sub : OutT ⊆ Icc 0 1 := union_subset (Icc_subset_Icc_right (by linarith)) (Icc_subset_Icc_left (by linarith))
  have hOut_closed : IsClosed (γ '' OutT) := (hOutT_cpt.image_of_continuousOn (hγc.mono hOutT_sub)).isClosed
  have hq_not_Out : q ∉ γ '' OutT := by
    rintro ⟨r, hr, hre⟩
    have hreq : r = t₀ := hγi (hOutT_sub hr) ht₀_cc (hre.trans ht₀_eq.symm)
    rcases hr with h1 | h2
    · linarith [h1.2, hη]
    · linarith [h2.1, hη]
  have hpre_o2 : IsOpen (ball (x₀ : ℂ) ε ∩ sb.f i ⁻¹' (γ '' OutT)ᶜ) :=
    ((sb.hfc i).mono (ball_subset_closedBall.trans hBbig_rect)).isOpen_inter_preimage isOpen_ball hOut_closed.isOpen_compl
  obtain ⟨ε₁, hε₁, hε₁sub⟩ := Metric.isOpen_iff.mp hpre_o2 (x₀ : ℂ) ⟨mem_ball_self hε, by rw [mem_preimage, hq_eq]; exact hq_not_Out⟩
  let ε' : ℝ := min (ε / 2) (ε₁ / 2)
  have hε' : 0 < ε' := lt_min (half_pos hε) (half_pos hε₁)
  have hε'_lt : ε' < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hBsm_sub : closedBall (x₀ : ℂ) ε' ⊆ ball (x₀ : ℂ) ε ∩ sb.f i ⁻¹' (γ '' OutT)ᶜ :=
    (closedBall_subset_ball ((min_le_right _ _).trans_lt (half_lt_self hε₁))).trans hε₁sub
  let Δsm : Set S := sb.f i '' closedBall (x₀ : ℂ) ε'
  have hΔsm_sub : Δsm ⊆ Δbig := image_mono (closedBall_subset_closedBall hε'_lt.le)
  have hΔsm_c : IsClosed Δsm :=
    ((isCompact_closedBall (x₀ : ℂ) ε').image_of_continuousOn
      ((sb.hfc i).mono ((closedBall_subset_closedBall hε'_lt.le).trans hBbig_rect))).isClosed
  have hOut_disj : Disjoint (γ '' OutT) Δsm := by
    rw [Set.disjoint_left]; rintro _ h1 ⟨w, hw, rfl⟩; exact (hBsm_sub hw).2 h1
  -- Define first entry `u` and last exit `v` of `γ` in `Δsm`:
  let Hit : Set ℝ := {r ∈ Icc (0 : ℝ) 1 | γ r ∈ Δsm}
  have hHit_ne : Hit.Nonempty := ⟨t₀, ht₀_cc, (x₀ : ℂ), mem_closedBall_self hε'.le, hq_eq.trans ht₀_eq.symm⟩
  have hHit_sub : Hit ⊆ Ioo (t₀ - η) (t₀ + η) := fun r hr => by
    constructor <;> by_contra h <;> push Not at h
    · exact Set.disjoint_left.mp hOut_disj ⟨r, Or.inl ⟨hr.1.1, h⟩, rfl⟩ hr.2
    · exact Set.disjoint_left.mp hOut_disj ⟨r, Or.inr ⟨h, hr.1.2⟩, rfl⟩ hr.2
  have hHit_c : IsClosed Hit := by
    have : Hit = Icc 0 1 ∩ γ ⁻¹' Δsm := rfl
    exact hγc.preimage_isClosed_of_isClosed isClosed_Icc hΔsm_c
  let u : ℝ := sInf Hit
  let v : ℝ := sSup Hit
  have hu_mem : u ∈ Hit := IsClosed.csInf_mem hHit_c hHit_ne ⟨0, fun _ hr => hr.1.1⟩
  have hv_mem : v ∈ Hit := IsClosed.csSup_mem hHit_c hHit_ne ⟨1, fun _ hr => hr.1.2⟩
  have hu_lt_t0 : u < t₀ := by
    -- `t₀ ∈ interior (γ ⁻¹' sb.f i '' ball (x₀ : ℂ) ε')`, so there is `r < t₀` in `Hit`!
    let Usm : Set S := sb.f i '' ball (x₀ : ℂ) ε'
    have hUsm_o : IsOpen Usm := sb.hfo i _ isOpen_ball
      ((ball_subset_closedBall.trans (closedBall_subset_closedBall hε'_lt.le)).trans fun w hw => (hBbig_sub hw).1)
    have hpre_sm := (hγc t₀ ht₀_cc).preimage_mem_nhdsWithin (hUsm_o.mem_nhds ⟨(x₀ : ℂ), mem_ball_self hε', hq_eq.trans ht₀_eq.symm⟩)
    obtain ⟨δt, hδt, hδtsub⟩ := Metric.mem_nhdsWithin_iff.mp hpre_sm
    let r₁ : ℝ := t₀ - min (δt / 2) (t₀ / 2)
    have hmin1_pos : 0 < min (δt / 2) (t₀ / 2) := lt_min (half_pos hδt) (half_pos ht₀_oo.1)
    have hr₁_in : r₁ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [min_le_right (δt / 2) (t₀ / 2), ht₀_oo.1], by linarith [hmin1_pos, ht₀_oo.2]⟩
    have hr₁_ball : r₁ ∈ ball t₀ δt := by
      rw [mem_ball, Real.dist_eq, abs_lt]
      have h1 : 0 < min (δt / 2) (t₀ / 2) := lt_min (half_pos hδt) (half_pos ht₀_oo.1)
      have h2 : min (δt / 2) (t₀ / 2) ≤ δt / 2 := min_le_left _ _
      exact ⟨by linarith, by linarith⟩
    have hr₁_hit : r₁ ∈ Hit := ⟨hr₁_in, image_mono ball_subset_closedBall (hδtsub ⟨hr₁_ball, hr₁_in⟩)⟩
    have hle : u ≤ r₁ := csInf_le ⟨0, fun _ hr => hr.1.1⟩ hr₁_hit
    have hlt : r₁ < t₀ := by simp only [r₁]; linarith [lt_min (half_pos hδt) (half_pos ht₀_oo.1)]
    linarith
  have ht0_lt_v : t₀ < v := by
    let Usm : Set S := sb.f i '' ball (x₀ : ℂ) ε'
    have hUsm_o : IsOpen Usm := sb.hfo i _ isOpen_ball
      ((ball_subset_closedBall.trans (closedBall_subset_closedBall hε'_lt.le)).trans fun w hw => (hBbig_sub hw).1)
    have hpre_sm := (hγc t₀ ht₀_cc).preimage_mem_nhdsWithin (hUsm_o.mem_nhds ⟨(x₀ : ℂ), mem_ball_self hε', hq_eq.trans ht₀_eq.symm⟩)
    obtain ⟨δt, hδt, hδtsub⟩ := Metric.mem_nhdsWithin_iff.mp hpre_sm
    let r₂ : ℝ := t₀ + min (δt / 2) ((1 - t₀) / 2)
    have hr₂_in : r₂ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [lt_min (half_pos hδt) (half_pos (sub_pos.mpr ht₀_oo.2)), ht₀_oo.1],
      by linarith [min_le_right (δt / 2) ((1 - t₀) / 2), ht₀_oo.2]⟩
    have hr₂_ball : r₂ ∈ ball t₀ δt := by
      rw [mem_ball, Real.dist_eq, abs_lt]
      have h1 : 0 < min (δt / 2) ((1 - t₀) / 2) := lt_min (half_pos hδt) (half_pos (sub_pos.mpr ht₀_oo.2))
      have h2 : min (δt / 2) ((1 - t₀) / 2) ≤ δt / 2 := min_le_left _ _
      exact ⟨by linarith, by linarith⟩
    have hr₂_hit : r₂ ∈ Hit := ⟨hr₂_in, image_mono ball_subset_closedBall (hδtsub ⟨hr₂_ball, hr₂_in⟩)⟩
    have hge : r₂ ≤ v := le_csSup ⟨1, fun _ hr => hr.1.2⟩ hr₂_hit
    have hgt : t₀ < r₂ := by simp only [r₂]; linarith [lt_min (half_pos hδt) (half_pos (sub_pos.mpr ht₀_oo.2))]
    linarith
  have hu0 : 0 < u := by linarith [(hHit_sub hu_mem).1, hη_t0]
  have huv : u < v := hu_lt_t0.trans ht0_lt_v
  have hv1 : v < 1 := by linarith [(hHit_sub hv_mem).2, hη_t1]
  -- Extract coordinates `zu, zv ∈ sphere (x₀ : ℂ) ε'` for `γ u` and `γ v`:
  obtain ⟨zu, hzu_cb, hzu_eq⟩ := hu_mem.2
  obtain ⟨zv, hzv_cb, hzv_eq⟩ := hv_mem.2
  have hzu_sph : zu ∈ sphere (x₀ : ℂ) ε' := by
    refine mem_sphere.mpr (le_antisymm (mem_closedBall.mp hzu_cb) ?_)
    by_contra hlt; push Not at hlt
    let Usm : Set S := sb.f i '' ball (x₀ : ℂ) ε'
    have hUsm_o : IsOpen Usm := sb.hfo i _ isOpen_ball
      ((ball_subset_closedBall.trans (closedBall_subset_closedBall hε'_lt.le)).trans fun w hw => (hBbig_sub hw).1)
    have hpre_sm := (hγc u hu_mem.1).preimage_mem_nhdsWithin (hUsm_o.mem_nhds ⟨zu, hlt, hzu_eq⟩)
    obtain ⟨δt, hδt, hδtsub⟩ := Metric.mem_nhdsWithin_iff.mp hpre_sm
    let r₁ : ℝ := u - min (δt / 2) (u / 2)
    have hr₁_in : r₁ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [min_le_right (δt / 2) (u / 2), hu0], by linarith [lt_min (half_pos hδt) (half_pos hu0), huv, hv1]⟩
    have hr₁_ball : r₁ ∈ ball u δt := by
      rw [mem_ball, Real.dist_eq, abs_lt]
      have h1 : 0 < min (δt / 2) (u / 2) := lt_min (half_pos hδt) (half_pos hu0)
      have h2 : min (δt / 2) (u / 2) ≤ δt / 2 := min_le_left _ _
      exact ⟨by linarith, by linarith⟩
    have hr₁_hit : r₁ ∈ Hit := ⟨hr₁_in, image_mono ball_subset_closedBall (hδtsub ⟨hr₁_ball, hr₁_in⟩)⟩
    linarith [csInf_le ⟨0, fun _ hr => hr.1.1⟩ hr₁_hit, lt_min (half_pos hδt) (half_pos hu0)]
  have hzv_sph : zv ∈ sphere (x₀ : ℂ) ε' := by
    refine mem_sphere.mpr (le_antisymm (mem_closedBall.mp hzv_cb) ?_)
    by_contra hlt; push Not at hlt
    let Usm : Set S := sb.f i '' ball (x₀ : ℂ) ε'
    have hUsm_o : IsOpen Usm := sb.hfo i _ isOpen_ball
      ((ball_subset_closedBall.trans (closedBall_subset_closedBall hε'_lt.le)).trans fun w hw => (hBbig_sub hw).1)
    have hpre_sm := (hγc v hv_mem.1).preimage_mem_nhdsWithin (hUsm_o.mem_nhds ⟨zv, hlt, hzv_eq⟩)
    obtain ⟨δt, hδt, hδtsub⟩ := Metric.mem_nhdsWithin_iff.mp hpre_sm
    let r₂ : ℝ := v + min (δt / 2) ((1 - v) / 2)
    have hr₂_in : r₂ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [lt_min (half_pos hδt) (half_pos (sub_pos.mpr hv1)), hu0, huv],
      by linarith [min_le_right (δt / 2) ((1 - v) / 2), hv1]⟩
    have hr₂_ball : r₂ ∈ ball v δt := by
      rw [mem_ball, Real.dist_eq, abs_lt]
      have h1 : 0 < min (δt / 2) ((1 - v) / 2) := lt_min (half_pos hδt) (half_pos (sub_pos.mpr hv1))
      have h2 : min (δt / 2) ((1 - v) / 2) ≤ δt / 2 := min_le_left _ _
      exact ⟨by linarith, by linarith⟩
    have hr₂_hit : r₂ ∈ Hit := ⟨hr₂_in, image_mono ball_subset_closedBall (hδtsub ⟨hr₂_ball, hr₂_in⟩)⟩
    linarith [le_csSup ⟨1, fun _ hr => hr.1.2⟩ hr₂_hit, lt_min (half_pos hδt) (half_pos (sub_pos.mpr hv1))]
  have hzu_ne_zv : zu ≠ zv := fun h => huv.ne (hγi hu_mem.1 hv_mem.1 (hzu_eq.symm.trans (h ▸ hzv_eq)))
  have hzu_im : zu.im ≠ 0 := fun him0 => by
    have hmemQ : γ u ∈ Q i := hzu_eq ▸ (sb.hQ_eq i zu (hBbig_rect (closedBall_subset_closedBall hε'_lt.le hzu_cb))).mpr him0
    have hmemF : γ u ∈ F := ⟨hγim ▸ ⟨u, hu_mem.1, rfl⟩, mem_iUnion.mpr ⟨i, hmemQ⟩⟩
    have hne_q : γ u ≠ q := fun he => hu_lt_t0.ne (hγi hu_mem.1 ht₀_cc (he.trans ht₀_eq.symm))
    exact Set.disjoint_left.mp hΔbig_disj (hΔsm_sub hu_mem.2) (Or.inl (Or.inr ⟨hmemF, hne_q⟩))
  have hzv_im : zv.im ≠ 0 := fun him0 => by
    have hmemQ : γ v ∈ Q i := hzv_eq ▸ (sb.hQ_eq i zv (hBbig_rect (closedBall_subset_closedBall hε'_lt.le hzv_cb))).mpr him0
    have hmemF : γ v ∈ F := ⟨hγim ▸ ⟨v, hv_mem.1, rfl⟩, mem_iUnion.mpr ⟨i, hmemQ⟩⟩
    have hne_q : γ v ≠ q := fun he => ht0_lt_v.ne' (hγi hv_mem.1 ht₀_cc (he.trans ht₀_eq.symm))
    exact Set.disjoint_left.mp hΔbig_disj (hΔsm_sub hv_mem.2) (Or.inl (Or.inr ⟨hmemF, hne_q⟩))
  -- Build the replacement path `β` on `[u, v]` from `exists_ball_straightener`:
  obtain ⟨α, hαc, hαi, hα0, hα1, hα_ball, hα_cases⟩ :=
    exists_ball_straightener hε' hzu_sph hzv_sph hzu_ne_zv hzu_im hzv_im
  let τ : ℝ → ℝ := fun r => (r - u) / (v - u)
  have hτ_in : ∀ r ∈ Icc u v, τ r ∈ Icc (0 : ℝ) 1 := fun r hr =>
    ⟨div_nonneg (sub_nonneg.mpr hr.1) (sub_pos.mpr huv).le, (div_le_one (sub_pos.mpr huv)).mpr (sub_le_sub_right hr.2 u)⟩
  have hτ_oo : ∀ r ∈ Ioo u v, τ r ∈ Ioo (0 : ℝ) 1 := fun r hr =>
    ⟨div_pos (sub_pos.mpr hr.1) (sub_pos.mpr huv), (div_lt_one (sub_pos.mpr huv)).mpr (sub_lt_sub_right hr.2 u)⟩
  have hα_cb : ∀ r ∈ Icc (0 : ℝ) 1, α r ∈ closedBall (x₀ : ℂ) ε' := fun r hr => by
    rcases hr.1.eq_or_lt with rfl | hr0
    · rw [hα0]; exact hzu_cb
    · rcases hr.2.eq_or_lt with rfl | hr1
      · rw [hα1]; exact hzv_cb
      · exact ball_subset_closedBall (hα_ball r ⟨hr0, hr1⟩)
  let β : ℝ → S := fun r => sb.f i (α (τ r))
  have hβc : ContinuousOn β (Icc u v) :=
    ((sb.hfc i).mono ((closedBall_subset_closedBall hε'_lt.le).trans hBbig_rect)).comp
      (hαc.comp (by unfold τ; fun_prop) hτ_in) (fun r hr => hα_cb _ (hτ_in r hr))
  have hβi : InjOn β (Icc u v) := fun r₁ hr₁ r₂ hr₂ he => by
    have h1 := sb.hfi i (hBbig_rect (closedBall_subset_closedBall hε'_lt.le (hα_cb _ (hτ_in r₁ hr₁))))
      (hBbig_rect (closedBall_subset_closedBall hε'_lt.le (hα_cb _ (hτ_in r₂ hr₂)))) he
    have h2 := hαi (hτ_in r₁ hr₁) (hτ_in r₂ hr₂) h1
    simp only [τ] at h2
    have hne : v - u ≠ 0 := (sub_pos.mpr huv).ne'
    have := mul_right_cancel₀ (inv_ne_zero hne) (by simpa only [div_eq_mul_inv] using h2)
    linarith
  have hβu : β u = γ u := by simp [β, τ, hα0, hzu_eq]
  have hβv : β v = γ v := by
    have : τ v = 1 := div_self (sub_pos.mpr huv).ne'
    simp [β, this, hα1, hzv_eq]
  have hβΔ : β '' Icc u v ⊆ Δbig := by
    rintro _ ⟨r, hr, rfl⟩; exact hΔsm_sub ⟨α (τ r), hα_cb _ (hτ_in r hr), rfl⟩
  have hγΔ : γ '' Icc u v ⊆ Δbig := by
    rintro _ ⟨r, hr, rfl⟩
    exact image_mono ball_subset_closedBall (hγ_near r ⟨by linarith [hr.1, (hHit_sub hu_mem).1], by linarith [hr.2, (hHit_sub hv_mem).2]⟩)
  have hβ_hit : ∀ r ∈ Ioo u v, β r ∉ γ '' (Icc 0 u ∪ Icc v 1) := by
    rintro r hr ⟨r', hr', hre⟩
    have hr'_in : r' ∈ Icc (0 : ℝ) 1 := by
      rcases hr' with h1 | h2
      · exact ⟨h1.1, by linarith [h1.2, huv, hv1]⟩
      · exact ⟨by linarith [h2.1, hu0, huv], h2.2⟩
    have hr'_hit : r' ∈ Hit := ⟨hr'_in, hre ▸ ⟨α (τ r), ball_subset_closedBall (hα_ball _ (hτ_oo r hr)), rfl⟩⟩
    rcases hr' with h1 | h2
    · have hle : u ≤ r' := csInf_le ⟨0, fun _ h => h.1.1⟩ hr'_hit
      have hru : r' = u := le_antisymm h1.2 hle
      rw [hru, ← hzu_eq] at hre
      have h1' := sb.hfi i (hBbig_rect (closedBall_subset_closedBall hε'_lt.le hzu_cb))
        (hBbig_rect (closedBall_subset_closedBall hε'_lt.le (ball_subset_closedBall (hα_ball _ (hτ_oo r hr))))) hre
      exact (mem_ball.mp (hα_ball _ (hτ_oo r hr))).ne (h1' ▸ mem_sphere.mp hzu_sph)
    · have hge : r' ≤ v := le_csSup ⟨1, fun _ h => h.1.2⟩ hr'_hit
      have hrv : r' = v := le_antisymm hge h2.1
      rw [hrv, ← hzv_eq] at hre
      have h1' := sb.hfi i (hBbig_rect (closedBall_subset_closedBall hε'_lt.le hzv_cb))
        (hBbig_rect (closedBall_subset_closedBall hε'_lt.le (ball_subset_closedBall (hα_ball _ (hτ_oo r hr))))) hre
      exact (mem_ball.mp (hα_ball _ (hτ_oo r hr))).ne (h1' ▸ mem_sphere.mp hzv_sph)
  -- Apply `replace_arc_in_disc`!
  obtain ⟨hPb', hPl', hγ'c, hγ'i, hγ'0, hγ'1, hagree, hcoh, hw1_eq⟩ :=
    replace_arc_in_disc hS AS hst hPb hPl hγc hγi hγ0 hγ1 hγim hΔbig_disc hΔbig_int hu0 huv hv1 hγΔ
      hβc hβi hβu hβv hβΔ hβ_hit
  set γ' : ℝ → S := fun r => if r ∈ Icc u v then β r else γ r
  set P' : Set S := γ' '' Icc 0 1
  -- Verify `P' ∩ ⋃ Q ⊆ P ∩ ⋃ Q`, `Disjoint P' (sb.tip k)`, preservation of good points, and improvement at `q`:
  have hP'_in_sm : P' ∩ Δsm = β '' Icc u v := by
    ext x; constructor
    · rintro ⟨⟨r, hr, rfl⟩, hxsm⟩
      by_cases huv_r : r ∈ Icc u v
      · rw [show γ' r = β r from ite_eq_left huv_r]; exact ⟨r, huv_r, rfl⟩
      · exfalso
        have hr_hit : r ∈ Hit := ⟨hr, by rwa [show γ' r = γ r from ite_eq_right huv_r] at hxsm⟩
        exact huv_r ⟨csInf_le ⟨0, fun _ h => h.1.1⟩ hr_hit, le_csSup ⟨1, fun _ h => h.1.2⟩ hr_hit⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨⟨r, ⟨by linarith [hr.1], by linarith [hr.2]⟩, ite_eq_left hr⟩, ⟨α (τ r), hα_cb _ (hτ_in r hr), rfl⟩⟩
  have hP'_tips : ∀ k, Disjoint P' (sb.tip k) := fun k => by
    rw [Set.disjoint_left]; intro x hxP' hxtip
    by_cases hxΔ : x ∈ Δbig
    · obtain ⟨w, hw, rfl⟩ := hxΔ
      by_cases hki : k = i
      · subst hki
        have hwim : w.im = 0 := (sb.hQ_eq k w (hBbig_rect hw)).mp hxtip.1
        exact hxtip.2 ⟨w, Complex.mem_reProdIm.mpr ⟨(Complex.mem_reProdIm.mp (hBbig_sub hw).1).1, hwim⟩, rfl⟩
      · exact Set.disjoint_left.mp (sb.hQ_other i k (Ne.symm hki)) ⟨w, hBbig_rect hw, rfl⟩ hxtip.1
    · exact Set.disjoint_left.mp (hPtips k) (show x ∈ P \ Δbig from hagree ▸ ⟨hxP', hxΔ⟩).1 hxtip
  have hP'_sub_F : P' ∩ ⋃ k, Q k ⊆ F := by
    rintro x ⟨hxP', hxQ⟩
    by_cases hxΔ : x ∈ Δbig
    · -- Any point of `P' ∩ Δbig` is either in `β '' Icc u v` or in `γ '' (Icc 0 1 \ Icc u v)`:
      obtain ⟨r, hr, rfl⟩ := hxP'
      by_cases huv_r : r ∈ Icc u v
      · rw [show γ' r = β r from ite_eq_left huv_r] at hxQ ⊢
        obtain ⟨k, hxk⟩ := mem_iUnion.mp hxQ
        have hki : k = i := by
          by_contra hne
          exact Set.disjoint_left.mp (sb.hQ_other i k (Ne.symm hne))
            ⟨α (τ r), hBbig_rect (closedBall_subset_closedBall hε'_lt.le (hα_cb _ (hτ_in r huv_r))), rfl⟩ hxk
        subst hki
        have him0 : (α (τ r)).im = 0 := (sb.hQ_eq k _ (hBbig_rect (closedBall_subset_closedBall hε'_lt.le (hα_cb _ (hτ_in r huv_r))))).mp hxk
        rcases hα_cases with hno0 | ⟨r₀, -, -, hiff0, -⟩
        · exact (hno0 _ (hτ_in r huv_r) him0).elim
        · have heq : α (τ r) = (x₀ : ℂ) := (hiff0 _ (hτ_in r huv_r)).mp him0
          show sb.f k (α (τ r)) ∈ F; rw [heq, hq_eq]; exact hq
      · rw [show γ' r = γ r from ite_eq_right huv_r] at hxQ ⊢
        exact ⟨hγim ▸ ⟨r, hr, rfl⟩, hxQ⟩
    · exact ⟨(show x ∈ P \ Δbig from hagree ▸ ⟨hxP', hxΔ⟩).1, hxQ⟩
  have hpres_good : ∀ g ∈ F, IsGoodAt sb P g → g ∈ P' ∧ IsGoodAt sb P' g := fun g hg hgood => by
    let gg : Ggood := ⟨g, hg, hgood⟩
    refine hBg_pres gg P' ?_
    ext x; constructor
    · rintro ⟨hxP', hxB⟩
      have hxΔ : x ∉ Δbig := fun h => Set.disjoint_left.mp hΔbig_disj h (Or.inr (mem_iUnion.mpr ⟨gg, hxB⟩))
      exact ⟨(show x ∈ P \ Δbig from hagree ▸ ⟨hxP', hxΔ⟩).1, hxB⟩
    · rintro ⟨hxP, hxB⟩
      have hxΔ : x ∉ Δbig := fun h => Set.disjoint_left.mp hΔbig_disj h (Or.inr (mem_iUnion.mpr ⟨gg, hxB⟩))
      exact ⟨(show x ∈ P' \ Δbig from hagree.symm ▸ ⟨hxP, hxΔ⟩).1, hxB⟩
  have himprove : q ∉ P' ∨ IsGoodAt sb P' q := by
    rcases hα_cases with hno0 | ⟨r₀, hr₀_pos, hr₀_lt, -, hball_eq⟩
    · left; intro hqP'
      have hqsm : q ∈ P' ∩ Δsm := ⟨hqP', (x₀ : ℂ), mem_closedBall_self hε'.le, hq_eq⟩
      rw [hP'_in_sm] at hqsm
      obtain ⟨r, hr, hre⟩ := hqsm
      have h1 := sb.hfi i (hBbig_rect (closedBall_subset_closedBall hε'_lt.le (hα_cb _ (hτ_in r hr))))
        (hBbig_rect (mem_closedBall_self hε.le)) (hre.trans hq_eq.symm)
      exact hno0 _ (hτ_in r hr) (by rw [h1]; simp)
    · right
      refine ⟨i, x₀, r₀, hr₀_pos, (closedBall_subset_closedBall (hr₀_lt.le.trans hε'_lt.le)).trans fun w hw => (hBbig_sub hw).1,
        hq_eq.symm, ?_⟩
      have hsub_sm : sb.f i '' closedBall (x₀ : ℂ) r₀ ⊆ Δsm := image_mono (closedBall_subset_closedBall hr₀_lt.le)
      have hβ_im : β '' Icc u v = sb.f i '' (α '' Icc 0 1) := by
        ext x; constructor
        · rintro ⟨r, hr, rfl⟩; exact ⟨α (τ r), ⟨τ r, hτ_in r hr, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨s', hs', rfl⟩, rfl⟩
          let r := u + s' * (v - u)
          refine ⟨r, ⟨by nlinarith [hs'.1], by nlinarith [hs'.2]⟩, ?_⟩
          have : τ r = s' := by simp only [τ, r]; field_simp [(sub_pos.mpr huv).ne']; ring
          simp only [β, this]
      have h1 : P' ∩ sb.f i '' closedBall (x₀ : ℂ) r₀ = (P' ∩ Δsm) ∩ sb.f i '' closedBall (x₀ : ℂ) r₀ := by
        ext x; exact ⟨fun ⟨h1, h2⟩ => ⟨⟨h1, hsub_sm h2⟩, h2⟩, fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩⟩
      rw [h1, hP'_in_sm, hβ_im]
      have hinj_sub : InjOn (sb.f i) (α '' Icc 0 1 ∪ closedBall (x₀ : ℂ) r₀) :=
        (sb.hfi i).mono (union_subset (by rintro _ ⟨s', hs', rfl⟩; exact hBbig_rect (closedBall_subset_closedBall hε'_lt.le (hα_cb s' hs')))
          ((closedBall_subset_closedBall (hr₀_lt.le.trans hε'_lt.le)).trans hBbig_rect))
      rw [← hinj_sub.image_inter subset_union_left subset_union_right, hball_eq]
  exact ⟨P', γ', hPb', hPl', hγ'c, hγ'i, hγ'0, hγ'1, rfl, hP'_tips, hP'_sub_F, hpres_good, himprove, hcoh, hw1_eq⟩

/-- **Step 0 (Transversality)**: Given a proper `I`-arc `P` with ends `s ≠ t` avoiding `Q : Fin m → Set S`
on the boundary, there exist a boundary-fixing homeomorphism `α : S ≃ₜ S`, a `StripBox S Q` (`sb`),
and a proper `I`-arc `P_tr` with ends `s, t` and parameterization `γ_tr` such that:
- `BdCohRel s t (arcCocycle P_tr) (arcCocycle (α '' P))`
- `cocInt (w1 AS) γ_tr = cocInt (w1 AS) (α ∘ γ)`
- `∀ i, Disjoint P_tr (sb.tip i)`
- For every `i : Fin m`, there is a finite set `X i : Finset ℝ` with `∀ x ∈ X i, x ∈ Ioo (sb.a i) (sb.b i)`
  such that `P_tr ∩ sb.box i = ⋃ x ∈ X i, sb.f i '' (({x} : Set ℝ) ×ℂ Icc (-sb.δ) sb.δ)`. -/
theorem exists_transverse_arc [ConnectedSpace S] (hS : IsSurface S) (AS : SurfAtlas S)
    {s t : S} (hst : s ≠ t) {P : Set S} (hPb : P ∩ bd S = {s, t}) (hPl : IsLineWithEnds P s t)
    {γ : ℝ → S} (hγc : ContinuousOn γ (Icc 0 1)) (hγi : InjOn γ (Icc 0 1))
    (hγ0 : γ 0 = s) (hγ1 : γ 1 = t) (hγim : γ '' Icc 0 1 = P)
    {m : ℕ} (Q : Fin m → Set S)
    (hQ : ∀ i, ∃ u v, u ≠ v ∧ IsLineWithEnds (Q i) u v ∧ Q i ∩ bd S = {u, v})
    (hQdisj : Pairwise fun i j => Disjoint (Q i) (Q j))
    (hsQ : ∀ i, s ∉ Q i) (htQ : ∀ i, t ∉ Q i) :
    ∃ (sb : StripBox S Q) (α : S ≃ₜ S)
      (P_tr : Set S) (γ_tr : ℝ → S)
      (hPb' : P_tr ∩ bd S = {s, t}) (hPl' : IsLineWithEnds P_tr s t)
      (hP₁b : (α '' P) ∩ bd S = {s, t}) (hP₁l : IsLineWithEnds (α '' P) s t),
      (∀ x ∈ bd S, α x = x) ∧
      ContinuousOn γ_tr (Icc 0 1) ∧ InjOn γ_tr (Icc 0 1) ∧
      γ_tr 0 = s ∧ γ_tr 1 = t ∧ γ_tr '' Icc 0 1 = P_tr ∧
      BdCohRel s t (arcCocycle hS hst hPb' hPl') (arcCocycle hS hst hP₁b hP₁l) ∧
      cocInt (w1 AS) γ_tr = cocInt (w1 AS) (α ∘ γ) ∧
      (∀ i, Disjoint P_tr (sb.tip i)) ∧
      (∀ i, ∃ X : Finset ℝ, (∀ x ∈ X, x ∈ Ioo (sb.a i) (sb.b i)) ∧
        P_tr ∩ sb.box i = ⋃ x ∈ X, sb.f i '' (({x} : Set ℝ) ×ℂ Icc (-sb.δ) sb.δ)) := by
  classical
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have hsPb : s ∈ P ∩ bd S := hPb.symm ▸ Or.inl rfl
  have htPb : t ∈ P ∩ bd S := hPb.symm ▸ Or.inr rfl
  obtain ⟨sb₀, α, hαfix, hαtips, hαfin⟩ :=
    exists_finite_cross_parallel hS hst hPb hPl Q hQ hQdisj hsQ htQ
  have hP₁b : (α '' P) ∩ bd S = {s, t} := by
    have hbd_img : α '' bd S = bd S := image_bd_homeomorph α
    rw [← hbd_img, ← image_inter α.injective, hPb]
    ext y; simp only [mem_image, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨x, hx | hx, rfl⟩
      · rw [hx]; exact Or.inl (hαfix s hsPb.2)
      · rw [hx]; exact Or.inr (hαfix t htPb.2)
    · rintro (hy | hy)
      · rw [hy]; exact ⟨s, Or.inl rfl, hαfix s hsPb.2⟩
      · rw [hy]; exact ⟨t, Or.inr rfl, hαfix t htPb.2⟩
  have hP₁l : IsLineWithEnds (α '' P) s t := by
    obtain ⟨f, h0, h1⟩ := hPl
    refine ⟨f.trans (α.image P), ?_, ?_⟩
    · change α (f 0).1 = s; rw [h0, hαfix s hsPb.2]
    · change α (f 1).1 = t; rw [h1, hαfix t htPb.2]
  have hαγc : ContinuousOn (α ∘ γ) (Icc 0 1) := α.continuous.comp_continuousOn hγc
  have hαγi : InjOn (α ∘ γ) (Icc 0 1) := fun r₁ hr₁ r₂ hr₂ h => hγi hr₁ hr₂ (α.injective h)
  have hαγ0 : (α ∘ γ) 0 = s := by simp [hγ0, hαfix s hsPb.2]
  have hαγ1 : (α ∘ γ) 1 = t := by simp [hγ1, hαfix t htPb.2]
  have hαγim : (α ∘ γ) '' Icc 0 1 = α '' P := by rw [image_comp, hγim]
  -- Strong induction on the number of bad crossing points `{q ∈ P ∩ ⋃ Q | ¬ IsGoodAt sb₀ P q}.ncard`:
  have hall_good : ∀ (n : ℕ) (P₁ : Set S) (γ₁ : ℝ → S)
      (h1b : P₁ ∩ bd S = {s, t}) (h1l : IsLineWithEnds P₁ s t),
      ContinuousOn γ₁ (Icc 0 1) → InjOn γ₁ (Icc 0 1) → γ₁ 0 = s → γ₁ 1 = t → γ₁ '' Icc 0 1 = P₁ →
      (∀ i, Disjoint P₁ (sb₀.tip i)) → (P₁ ∩ ⋃ i, Q i).Finite →
      {q ∈ P₁ ∩ ⋃ i, Q i | ¬ IsGoodAt sb₀ P₁ q}.ncard ≤ n →
      ∃ (P₂ : Set S) (γ₂ : ℝ → S) (h2b : P₂ ∩ bd S = {s, t}) (h2l : IsLineWithEnds P₂ s t),
        ContinuousOn γ₂ (Icc 0 1) ∧ InjOn γ₂ (Icc 0 1) ∧ γ₂ 0 = s ∧ γ₂ 1 = t ∧ γ₂ '' Icc 0 1 = P₂ ∧
        (∀ i, Disjoint P₂ (sb₀.tip i)) ∧ (P₂ ∩ ⋃ i, Q i).Finite ∧
        (∀ q ∈ P₂ ∩ ⋃ i, Q i, IsGoodAt sb₀ P₂ q) ∧
        BdCohRel s t (arcCocycle hS hst h2b h2l) (arcCocycle hS hst h1b h1l) ∧
        cocInt (w1 AS) γ₂ = cocInt (w1 AS) γ₁ := by
    intro n
    induction n with
    | zero =>
      intro P₁ γ₁ h1b h1l hc hi h0 h1 him htips hfin hcard
      have hemp : {q ∈ P₁ ∩ ⋃ i, Q i | ¬ IsGoodAt sb₀ P₁ q} = ∅ :=
        (Set.ncard_eq_zero (hfin.subset (sep_subset _ _))).mp (Nat.eq_zero_of_le_zero hcard)
      refine ⟨P₁, γ₁, h1b, h1l, hc, hi, h0, h1, him, htips, hfin, fun q hq => ?_, bdCohRel_refl s t _, rfl⟩
      by_contra hbad
      have : q ∈ ({q ∈ P₁ ∩ ⋃ i, Q i | ¬ IsGoodAt sb₀ P₁ q} : Set S) := ⟨hq, hbad⟩
      rw [hemp] at this; exact this
    | succ n ih =>
      intro P₁ γ₁ h1b h1l hc hi h0 h1 him htips hfin hcard
      let Bad := {q ∈ P₁ ∩ ⋃ i, Q i | ¬ IsGoodAt sb₀ P₁ q}
      by_cases hne : Bad.Nonempty
      · obtain ⟨q, hq, hqbad⟩ := hne
        obtain ⟨P', γ', hPb', hPl', hc', hi', h0', h1', him', htips', hsubF', hpres', himp', hcoh', hw1'⟩ :=
          straighten_one hS AS sb₀ hst h1b h1l hc hi h0 h1 him htips hfin hq hqbad
        let Bad' := {x ∈ P' ∩ ⋃ i, Q i | ¬ IsGoodAt sb₀ P' x}
        have hBad'_ssub : Bad' ⊂ Bad := by
          refine ⟨fun x hx => ⟨hsubF' hx.1, fun hg => hx.2 (hpres' x (hsubF' hx.1) hg).2⟩, fun hsub => ?_⟩
          have hqB' : q ∈ Bad' := hsub ⟨hq, hqbad⟩
          rcases himp' with hnotP | hgood
          · exact hnotP hqB'.1.1
          · exact hqB'.2 hgood
        have hBad'_lt : Bad'.ncard < Bad.ncard := Set.ncard_lt_ncard hBad'_ssub (hfin.subset (sep_subset _ _))
        have hBad_le : Bad.ncard ≤ n + 1 := hcard
        have hBad'_le : {x ∈ P' ∩ ⋃ i, Q i | ¬ IsGoodAt sb₀ P' x}.ncard ≤ n := by
          change Bad'.ncard ≤ n; omega
        obtain ⟨P₂, γ₂, h2b, h2l, hc2, hi2, h02, h12, him2, htips2, hfin2, hgood2, hcoh2, hw12⟩ :=
          ih P' γ' hPb' hPl' hc' hi' h0' h1' him' htips' (hfin.subset hsubF') hBad'_le
        exact ⟨P₂, γ₂, h2b, h2l, hc2, hi2, h02, h12, him2, htips2, hfin2, hgood2, bdCohRel_trans hcoh2 hcoh', hw12.trans hw1'⟩
      · rw [Set.not_nonempty_iff_eq_empty] at hne
        refine ⟨P₁, γ₁, h1b, h1l, hc, hi, h0, h1, him, htips, hfin, fun q hq => ?_, bdCohRel_refl s t _, rfl⟩
        by_contra hbad
        have : q ∈ Bad := ⟨hq, hbad⟩
        rw [hne] at this; exact this
  obtain ⟨P_tr, γ_tr, hPb', hPl', hc', hi', h0', h1', him', htips', hfin', hgood', hcoh', hw1'⟩ :=
    hall_good _ (α '' P) (α ∘ γ) hP₁b hP₁l hαγc hαγi hαγ0 hαγ1 hαγim hαtips hαfin le_rfl
  -- Now every `q ∈ P_tr ∩ ⋃ i, Q i` is good for `(sb₀, P_tr)`! Shrink `sb₀.δ` to `δ'` so `P_tr ∩ sb'.box i` is exact vertical segments:
  let F' : Set S := P_tr ∩ ⋃ i, Q i
  have : Finite F' := hfin'.to_subtype
  have hgood_data : ∀ q : F', ∃ (i : Fin m) (x₀ r : ℝ), 0 < r ∧ closedBall (x₀ : ℂ) r ⊆ sb₀.openRect i ∧
      q.1 = sb₀.f i (x₀ : ℂ) ∧ P_tr ∩ sb₀.f i '' closedBall (x₀ : ℂ) r = sb₀.f i '' (({x₀} : Set ℝ) ×ℂ Icc (-r) r) :=
    fun q => hgood' q.1 q.2
  choose iq xq rq hrq_pos hrq_sub hq_feq hq_ball using hgood_data
  let U_good : Set S := ⋃ q : F', sb₀.f (iq q) '' ball (xq q : ℂ) (rq q)
  have hU_good_o : IsOpen U_good := isOpen_iUnion fun q =>
    sb₀.hfo (iq q) _ isOpen_ball (ball_subset_closedBall.trans (hrq_sub q))
  let C_off : Set S := P_tr \ U_good
  have hC_off_c : IsClosed C_off := hPl'.isCompact.isClosed.sdiff hU_good_o
  have hC_off_disj : ∀ i, Disjoint C_off (Q i) := fun i => by
    rw [Set.disjoint_left]; rintro x ⟨hxP, hxU⟩ hxQ
    let q : F' := ⟨x, hxP, mem_iUnion.mpr ⟨i, hxQ⟩⟩
    exact hxU (mem_iUnion.mpr ⟨q, (xq q : ℂ), mem_ball_self (hrq_pos q), (hq_feq q).symm⟩)
  -- For each `i`, find `δ_i ∈ (0, sb₀.δ]` so `Icc (sb₀.a i) (sb₀.b i) ×ℂ Icc (-δ_i) δ_i` avoids `sb₀.f i ⁻¹' C_off`:
  have hδi_ex : ∀ i : Fin m, ∃ d : ℝ, 0 < d ∧ d ≤ sb₀.δ ∧
      Disjoint (sb₀.f i '' (Icc (sb₀.a i) (sb₀.b i) ×ℂ Icc (-d) d)) C_off := by
    intro i
    let seg : Set ℂ := (fun x : ℝ => (x : ℂ)) '' Icc (sb₀.a i) (sb₀.b i)
    have hseg_cpt : IsCompact seg := isCompact_Icc.image Complex.continuous_ofReal
    -- `C_off ∩ sb₀.box i` is closed, so its preimage in `sb₀.rect i` is compact and disjoint from `seg`:
    let BadC : Set ℂ := sb₀.rect i ∩ sb₀.f i ⁻¹' C_off
    have hBadC_c : IsClosed BadC :=
      (sb₀.hfc i).preimage_isClosed_of_isClosed (isClosed_Icc.reProdIm isClosed_Icc) hC_off_c
    have hseg_sub : seg ⊆ BadCᶜ := by
      rintro _ ⟨x, hx, rfl⟩ ⟨hxR, hxC⟩
      exact Set.disjoint_left.mp (hC_off_disj i) hxC ((sb₀.hQ_eq i (x : ℂ) hxR).mpr (by simp))
    obtain ⟨r, hr, hrsub⟩ := hseg_cpt.exists_thickening_subset_open hBadC_c.isOpen_compl hseg_sub
    let d := min sb₀.δ (r / 2)
    have hd_pos : 0 < d := lt_min sb₀.hδ (half_pos hr)
    refine ⟨d, hd_pos, min_le_left _ _, ?_⟩
    rw [Set.disjoint_left]; rintro _ ⟨w, hw, rfl⟩ hwC
    rw [Complex.mem_reProdIm] at hw
    have hw_in_R : w ∈ sb₀.rect i := Complex.mem_reProdIm.mpr
      ⟨hw.1, ⟨by linarith [hw.2.1, min_le_left sb₀.δ (r / 2)], by linarith [hw.2.2, min_le_left sb₀.δ (r / 2)]⟩⟩
    have hw_th : w ∈ thickening r seg := by
      rw [Metric.mem_thickening_iff]
      refine ⟨(w.re : ℂ), ⟨w.re, hw.1, rfl⟩, ?_⟩
      rw [dist_eq_norm, show w - (w.re : ℂ) = (w.im : ℂ) * I by apply Complex.ext <;> simp,
          norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      have : |w.im| ≤ d := abs_le.mpr hw.2
      linarith [min_le_right sb₀.δ (r / 2), half_lt_self hr]
    exact hrsub hw_th ⟨hw_in_R, hwC⟩
  choose δi hδi_pos hδi_le hδi_disj using hδi_ex
  -- Take `δ' > 0` below `sb₀.δ`, all `δi i`, and all `rq q / 2`:
  have hδ'_ex : ∃ δ' : ℝ, 0 < δ' ∧ δ' ≤ sb₀.δ ∧ (∀ i : Fin m, δ' ≤ δi i) ∧ (∀ q : F', δ' ≤ rq q / 2) := by
    obtain ⟨d1, hd1_pos, hd1_le⟩ : ∃ d1 : ℝ, 0 < d1 ∧ d1 ≤ sb₀.δ ∧ ∀ i : Fin m, d1 ≤ δi i := by
      by_cases hm : m = 0
      · subst hm; exact ⟨sb₀.δ, sb₀.hδ, le_rfl, fun i => Fin.elim0 i⟩
      · have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, Nat.pos_of_ne_zero hm⟩, Finset.mem_univ _⟩
        refine ⟨(Finset.univ : Finset (Fin m)).inf' hne δi, ?_, ?_, fun i => Finset.inf'_le δi (Finset.mem_univ i)⟩
        · rw [Finset.lt_inf'_iff]; exact fun i _ => hδi_pos i
        · exact (Finset.inf'_le δi (Finset.mem_univ ⟨0, Nat.pos_of_ne_zero hm⟩)).trans (hδi_le _)
    have : Fintype F' := Fintype.ofFinite F'
    by_cases hF'e : IsEmpty F'
    · exact ⟨d1, hd1_pos, hd1_le.1, hd1_le.2, fun q => hF'e.elim q⟩
    · rw [not_isEmpty_iff] at hF'e
      have hne : (Finset.univ : Finset F').Nonempty := Finset.univ_nonempty
      let d2 := (Finset.univ : Finset F').inf' hne (fun q => rq q / 2)
      have hd2 : 0 < d2 := by rw [Finset.lt_inf'_iff]; exact fun q _ => half_pos (hrq_pos q)
      exact ⟨min d1 d2, lt_min hd1_pos hd2, (min_le_left _ _).trans hd1_le.1,
        fun i => (min_le_left _ _).trans (hd1_le.2 i),
        fun q => (min_le_right _ _).trans (Finset.inf'_le (fun q => rq q / 2) (Finset.mem_univ q))⟩
  obtain ⟨δ', hδ'_pos, hδ'_le, hδ'_i, hδ'_q⟩ := hδ'_ex
  let sb : StripBox S Q := sb₀.shrink δ' hδ'_pos hδ'_le
  refine ⟨sb, α, P_tr, γ_tr, hPb', hPl', hP₁b, hP₁l, hαfix, hc', hi', h0', h1', him', hcoh', hw1', htips', fun i => ?_⟩
  have : Fintype F' := Fintype.ofFinite F'
  let Xi : Finset ℝ := (Finset.univ.filter fun q : F' => iq q = i).image xq
  refine ⟨Xi, ?_, ?_⟩
  · intro x hx
    obtain ⟨q, hq_filt, rfl⟩ := Finset.mem_image.mp hx
    have hiq : iq q = i := (Finset.mem_filter.mp hq_filt).2
    have hmem : (xq q : ℂ) ∈ sb₀.openRect (iq q) := hrq_sub q (mem_closedBall_self (hrq_pos q).le)
    rw [hiq] at hmem
    exact (Complex.mem_reProdIm.mp hmem).1
  · ext y; constructor
    · rintro ⟨hyP, hybox⟩
      -- `y ∉ C_off` because `δ' ≤ δi i`:
      have hy_notC : y ∉ C_off := by
        refine Set.disjoint_left.mp (hδi_disj i) ?_
        obtain ⟨w, hw, rfl⟩ := hybox
        simp only [sb, StripBox.shrink, StripBox.rect, Complex.mem_reProdIm] at hw
        exact ⟨w, Complex.mem_reProdIm.mpr ⟨hw.1, ⟨by linarith [hw.2.1, hδ'_i i], by linarith [hw.2.2, hδ'_i i]⟩⟩, rfl⟩
      have hyU : y ∈ U_good := by by_contra hnu; exact hy_notC ⟨hyP, hnu⟩
      obtain ⟨q, w, hw_b, hwf⟩ := mem_iUnion.mp hyU
      have hiq : iq q = i := by
        by_contra hne
        have h1 : y ∈ sb₀.box (iq q) := ⟨w, by
          have hro := hrq_sub q (ball_subset_closedBall hw_b)
          simp only [StripBox.openRect, StripBox.rect, Complex.mem_reProdIm] at hro ⊢
          exact ⟨Ioo_subset_Icc_self hro.1, Ioo_subset_Icc_self hro.2⟩, hwf⟩
        obtain ⟨w', hw', hwf'⟩ := hybox
        have h2 : y ∈ sb₀.box i := ⟨w', by
          simp only [sb, StripBox.shrink, StripBox.rect, Complex.mem_reProdIm] at hw' ⊢
          exact ⟨hw'.1, ⟨by linarith [hw'.2.1], by linarith [hw'.2.2]⟩⟩, hwf'⟩
        exact Set.disjoint_left.mp (sb₀.hdisj hne) h1 h2
      have hy_in : y ∈ P_tr ∩ sb₀.f (iq q) '' closedBall (xq q : ℂ) (rq q) :=
        ⟨hyP, w, ball_subset_closedBall hw_b, hwf⟩
      rw [hq_ball q] at hy_in
      obtain ⟨w₁, hw₁, hw₁f⟩ := hy_in
      obtain ⟨w₂, hw₂, hw₂f⟩ := hybox
      have hw₁_rect : w₁ ∈ sb₀.rect i := by
        rw [← hiq]
        have hcb : w₁ ∈ closedBall (xq q : ℂ) (rq q) := by
          rw [Complex.mem_reProdIm] at hw₁
          rw [mem_closedBall, dist_eq_norm, show w₁ - (xq q : ℂ) = (w₁.im : ℂ) * I by apply Complex.ext <;> simp [mem_singleton_iff.mp hw₁.1],
              norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]; exact abs_le.mpr hw₁.2
        have hro := hrq_sub q hcb
        simp only [StripBox.openRect, StripBox.rect, Complex.mem_reProdIm] at hro ⊢
        exact ⟨Ioo_subset_Icc_self hro.1, Ioo_subset_Icc_self hro.2⟩
      have hw₂_rect : w₂ ∈ sb₀.rect i := by
        simp only [sb, StripBox.shrink, StripBox.rect, Complex.mem_reProdIm] at hw₂ ⊢
        exact ⟨hw₂.1, ⟨by linarith [hw₂.2.1], by linarith [hw₂.2.2]⟩⟩
      have hw12 : w₁ = w₂ := sb₀.hfi i hw₁_rect hw₂_rect ((hiq ▸ hw₁f).trans hw₂f.symm)
      rw [mem_iUnion₂]
      refine ⟨xq q, Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ q, hiq⟩, rfl⟩,
        w₂, Complex.mem_reProdIm.mpr ⟨hw12 ▸ (Complex.mem_reProdIm.mp hw₁).1, (Complex.mem_reProdIm.mp hw₂).2⟩, hw₂f⟩
    · intro hy
      obtain ⟨x, hx, w, hw, rfl⟩ := mem_iUnion₂.mp hy
      obtain ⟨q, hq_filt, rfl⟩ := Finset.mem_image.mp hx
      have hiq : iq q = i := (Finset.mem_filter.mp hq_filt).2
      rw [Complex.mem_reProdIm] at hw
      have hw_r : w ∈ ({xq q} : Set ℝ) ×ℂ Icc (-(rq q)) (rq q) := by
        rw [Complex.mem_reProdIm]
        have hδeq : sb.δ = δ' := rfl
        exact ⟨hw.1, ⟨by linarith [hw.2.1, hδ'_q q, hrq_pos q, hδeq], by linarith [hw.2.2, hδ'_q q, hrq_pos q, hδeq]⟩⟩
      have hy_in : sb.f i w ∈ P_tr ∩ sb₀.f (iq q) '' closedBall (xq q : ℂ) (rq q) := by
        rw [hq_ball q]; exact ⟨w, hw_r, by simp only [sb, StripBox.shrink, hiq]⟩
      have hxin : xq q ∈ Ioo (sb.a i) (sb.b i) := by
        have hmem : (xq q : ℂ) ∈ sb₀.openRect (iq q) := hrq_sub q (mem_closedBall_self (hrq_pos q).le)
        rw [hiq] at hmem; exact (Complex.mem_reProdIm.mp hmem).1
      refine ⟨hy_in.1, w, Complex.mem_reProdIm.mpr ⟨?_, hw.2⟩, rfl⟩
      rw [mem_singleton_iff.mp hw.1]; exact Ioo_subset_Icc_self hxin

end TransverseMain

end GraphMinor.GHR18
