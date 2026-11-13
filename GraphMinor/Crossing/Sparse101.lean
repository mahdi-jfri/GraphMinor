module

public import GraphMinor.Crossing.Statements
import GraphMinor.Surface.Lunes
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Nonplanar graphs and five low-degree vertices (Section 10.1 of the note)

This file proves the two claims of Section 10.1 of `docs/crossing/crossing_extractor.tex`:
* `sec101Five_proved` (`Sec101FiveStatement`): a simple nonplanar graph has at least five vertices.
* `sec101Statement` (`Sec101Statement`): a simple nonplanar graph on `N` vertices with at most
  `16N` edges has at least five vertices of degree at most `64`.
-/

public section

namespace GraphMinor.Crossing

open SimpleGraph Set Surface Complex

universe u

variable {V : Type u}

/-! ### Section 10.1: Every graph on at most four vertices has a plane embedding -/

/-- The four points `0`, `3`, `3i`, `1 + i` in `ℂ` used to draw `K₄` with straight segments. -/
noncomputable def tetPt : Fin 4 → ℂ
  | 0 => 0
  | 1 => 3
  | 2 => 3 * I
  | 3 => 1 + I

@[simp] private lemma tetPt_re : ∀ i : Fin 4, (tetPt i).re = match i with
  | 0 => 0 | 1 => 3 | 2 => 0 | 3 => 1 := by
  intro i; fin_cases i <;> simp [tetPt]

@[simp] private lemma tetPt_im : ∀ i : Fin 4, (tetPt i).im = match i with
  | 0 => 0 | 1 => 0 | 2 => 3 | 3 => 1 := by
  intro i; fin_cases i <;> simp [tetPt]

private theorem tetPt_injective : Function.Injective tetPt := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [tetPt, Complex.ext_iff]

private theorem tetPt_coords_aux (i j k l : Fin 4) (hij : i ≠ j) (hkl : k ≠ l)
    (hne : s(i, j) ≠ s(k, l)) {t u : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (h₁ : (tetPt k).re + u * ((tetPt l).re - (tetPt k).re) =
      (tetPt i).re + t * ((tetPt j).re - (tetPt i).re))
    (h₂ : (tetPt k).im + u * ((tetPt l).im - (tetPt k).im) =
      (tetPt i).im + t * ((tetPt j).im - (tetPt i).im)) :
    (t = 0 ∧ (i = k ∨ i = l)) ∨ (t = 1 ∧ (j = k ∨ j = l)) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp at hij hkl hne h₁ h₂ ⊢ <;> linarith

/-- Any two distinct segments between the four points `tetPt` meet only at common endpoints. -/
private theorem tetPt_segment_inter (i j k l : Fin 4) (hij : i ≠ j) (hkl : k ≠ l)
    (hne : s(i, j) ≠ s(k, l)) :
    segment ℝ (tetPt i) (tetPt j) ∩ segment ℝ (tetPt k) (tetPt l) ⊆
      tetPt '' ({i, j} ∩ {k, l}) := by
  rintro z ⟨h1, h2⟩
  rw [segment_eq_image'] at h1 h2
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := h1
  obtain ⟨u, ⟨hu0, hu1⟩, hu⟩ := h2
  have h₁ := congrArg Complex.re hu
  have h₂ := congrArg Complex.im hu
  simp only [Complex.add_re, Complex.sub_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.add_im, Complex.sub_im, Complex.mul_im, add_zero] at h₁ h₂
  rcases tetPt_coords_aux i j k l hij hkl hne ht0 ht1 hu0 hu1 h₁ h₂ with
    ⟨rfl, hik⟩ | ⟨rfl, hjk⟩
  · refine ⟨i, ⟨by simp, by simpa using hik⟩, ?_⟩
    simp
  · refine ⟨j, ⟨by simp, by simpa using hjk⟩, ?_⟩
    simp

/-- No segment between two of the four points `tetPt` passes through a third point. -/
private theorem tetPt_mem_segment (i j k : Fin 4) (hij : i ≠ j)
    (h : tetPt k ∈ segment ℝ (tetPt i) (tetPt j)) :
    k = i ∨ k = j := by
  rw [segment_eq_image'] at h
  obtain ⟨t, ⟨ht0, ht1⟩, ht⟩ := h
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [tetPt] at hij ht ⊢ <;>
  · have h₁ := congrArg Complex.re ht
    have h₂ := congrArg Complex.im ht
    simp at h₁ h₂ <;> linarith

/-- Any graph `K` on a finite vertex set `S` that injects into `Fin 4` has a plane embedding. -/
private noncomputable def planeEmbeddingOfInjOnFin4 (K : SimpleGraph V) {S : Set V}
    (hSfin : S.Finite) {f : V → Fin 4} (hf : InjOn f S) :
    HP25.PlaneEmbedding K S where
  pt v := tetPt (f v)
  line u v := segment ℝ (tetPt (f u)) (tetPt (f v))
  finite := hSfin
  injOn := tetPt_injective.injOn.comp hf (mapsTo_univ _ _)
  line_comm u v := segment_symm ℝ _ _
  isLine u hu v hv h := isLineWithEnds_segment fun he =>
    h.ne (hf hu hv (tetPt_injective he))
  inter u hu v hv u' hu' v' hv' h h' hne := by
    have hne' : s(f u, f v) ≠ s(f u', f v') := by
      intro he
      rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hne (by rw [hf hu hu' h1, hf hv hv' h2])
      · exact hne (by rw [hf hu hv' h1, hf hv hu' h2, Sym2.eq_swap])
    refine (tetPt_segment_inter _ _ _ _ (fun he => h.ne (hf hu hv he))
      (fun he => h'.ne (hf hu' hv' he)) hne').trans ?_
    rintro _ ⟨m, ⟨hm1, hm2⟩, rfl⟩
    simp only [mem_insert_iff, mem_singleton_iff] at hm1 hm2
    rcases hm1 with rfl | rfl
    · refine ⟨u, ⟨by simp, ?_⟩, rfl⟩
      rcases hm2 with h2 | h2
      · simp [hf hu hu' h2]
      · simp [hf hu hv' h2]
    · refine ⟨v, ⟨by simp, ?_⟩, rfl⟩
      rcases hm2 with h2 | h2
      · simp [hf hv hu' h2]
      · simp [hf hv hv' h2]
  avoid u hu v hv h w hw hwl := by
    rcases tetPt_mem_segment _ _ _ (fun he => h.ne (hf hu hv he)) hwl with h1 | h1
    · exact Or.inl (hf hw hu h1)
    · exact Or.inr (hf hw hv h1)

/-- **Nonplanar graphs are not small** (Section 10.1): "A nonplanar graph has at least five
vertices." -/
theorem sec101Five_proved : Sec101FiveStatement := by
  intro V K S hSfin _ hnonplanar
  classical
  by_contra hlt
  rw [not_le] at hlt
  let F : Finset V := hSfin.toFinset
  have hFcard : F.card ≤ 4 := by
    dsimp only [F]
    rw [Set.ncard_eq_toFinset_card S hSfin] at hlt
    omega
  let e : F ≃ Fin F.card := F.equivFin
  let f : V → Fin 4 := fun v =>
    if hv : v ∈ F then ⟨(e ⟨v, hv⟩).val, by have := (e ⟨v, hv⟩).isLt; omega⟩ else 0
  have hf : InjOn f S := by
    intro u hu v hv huv
    have huF : u ∈ F := hSfin.mem_toFinset.mpr hu
    have hvF : v ∈ F := hSfin.mem_toFinset.mpr hv
    simp only [f, huF, hvF, ↓reduceDIte, Fin.mk.injEq] at huv
    have heq : e ⟨u, huF⟩ = e ⟨v, hvF⟩ := Fin.ext huv
    exact congrArg Subtype.val (e.injective heq)
  exact hnonplanar ⟨planeEmbeddingOfInjOnFin4 K hSfin hf⟩

/-! ### Section 10.1: Five low-degree vertices always exist -/

/-- **Five low-degree vertices always exist** (Section 10.1): "For $5\le N\le9$, every vertex has
degree at most eight. For $N\ge10$, the number of vertices of degree at least $65$ is at most
$\frac{2M}{65}\le\frac{32N}{65}<\frac N2$. Thus more than $N/2\ge5$ vertices have degree at most
$64$." In both cases at least five vertices have degree at most `64`. -/
theorem sec101_proved : Sec101Statement := by
  intro V K S hSfin hK hnonplanar hM
  classical
  have hN5 : 5 ≤ S.ncard := sec101Five_proved K S hSfin hK hnonplanar
  let _ : Fintype S := hSfin.fintype
  have hcardS : Fintype.card S = S.ncard :=
    (Set.toFinset_card S).symm.trans (Set.ncard_eq_toFinset_card S hSfin).symm
  let Ks : SimpleGraph S := K.comap Subtype.val
  let _ : DecidableRel Ks.Adj := Classical.decRel _
  have hdeg_le : ∀ y : S, (K.neighborSet y.1).ncard ≤ Ks.degree y := by
    intro y
    have hsub : K.neighborSet y.1 ⊆ Subtype.val '' (Ks.neighborFinset y : Set S) := by
      intro z hz
      have hzS : z ∈ S := hK hz.symm
      refine ⟨⟨z, hzS⟩, ?_, rfl⟩
      rw [Finset.mem_coe, mem_neighborFinset]
      exact hz
    have hfin_im : (Subtype.val '' (Ks.neighborFinset y : Set S)).Finite :=
      (Finset.finite_toSet _).image _
    calc
      (K.neighborSet y.1).ncard ≤ (Subtype.val '' (Ks.neighborFinset y : Set S)).ncard :=
        Set.ncard_le_ncard hsub hfin_im
      _ = ((Ks.neighborFinset y : Set S)).ncard :=
        Set.ncard_image_of_injective _ Subtype.val_injective
      _ = (Ks.neighborFinset y).card := Set.ncard_coe_finset _
      _ = Ks.degree y := rfl
  have hEfin : K.edgeSet.Finite := by
    have hsub : K.edgeSet ⊆ (fun p : V × V => s(p.1, p.2)) '' (S ×ˢ S) := by
      intro e he
      induction e using Sym2.ind with
      | _ u v =>
        rw [mem_edgeSet] at he
        exact ⟨(u, v), ⟨hK he, hK he.symm⟩, rfl⟩
    exact ((hSfin.prod hSfin).image _).subset hsub
  have hedge_le : Ks.edgeFinset.card ≤ K.edgeSet.ncard := by
    have hsub : Sym2.map (Subtype.val : S → V) '' Ks.edgeSet ⊆ K.edgeSet := by
      rintro _ ⟨e, he, rfl⟩
      induction e using Sym2.ind with
      | _ u v => exact he
    calc
      Ks.edgeFinset.card = (Ks.edgeFinset : Set (Sym2 S)).ncard := (Set.ncard_coe_finset _).symm
      _ = Ks.edgeSet.ncard := by rw [coe_edgeFinset]
      _ = (Sym2.map (Subtype.val : S → V) '' Ks.edgeSet).ncard :=
        (Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)).symm
      _ ≤ K.edgeSet.ncard := Set.ncard_le_ncard hsub hEfin
  let Good : Finset S := Finset.univ.filter (fun y : S => (K.neighborSet y.1).ncard ≤ 64)
  let Bad : Finset S := Finset.univ.filter (fun y : S => ¬ (K.neighborSet y.1).ncard ≤ 64)
  have hpart : Good.card + Bad.card = S.ncard := by
    have h1 := Finset.card_filter_add_card_filter_not
      (fun y : S => (K.neighborSet y.1).ncard ≤ 64) (s := Finset.univ)
    rw [Finset.card_univ, hcardS] at h1
    exact h1
  have hGood5 : 5 ≤ Good.card := by
    by_cases hN9 : S.ncard ≤ 9
    · -- For `5 ≤ N ≤ 9`, every vertex has degree at most eight.
      have hBad0 : Bad = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro y hy
        simp only [Bad, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hy
        have hsub : K.neighborSet y.1 ⊆ S := fun z hz => hK hz.symm
        have hleS : (K.neighborSet y.1).ncard ≤ S.ncard := Set.ncard_le_ncard hsub hSfin
        omega
      rw [hBad0, Finset.card_empty, add_zero] at hpart
      omega
    · -- For `N ≥ 10`, at most `2M / 65 ≤ 32N / 65` vertices have degree at least 65.
      have hsum_bad : 65 * Bad.card ≤ ∑ y ∈ Bad, Ks.degree y := by
        calc
          65 * Bad.card = ∑ _ ∈ Bad, 65 := by
            rw [Finset.sum_const, smul_eq_mul, mul_comm]
          _ ≤ ∑ y ∈ Bad, Ks.degree y := by
            refine Finset.sum_le_sum fun y hy => ?_
            simp only [Bad, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hy
            have := hdeg_le y
            omega
      have hsum_univ : ∑ y ∈ Bad, Ks.degree y ≤ ∑ y : S, Ks.degree y :=
        Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
      have hhandshake : ∑ y : S, Ks.degree y = 2 * Ks.edgeFinset.card :=
        Ks.sum_degrees_eq_twice_card_edges
      omega
  let emb : S ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  have hmap_card : 5 ≤ (Good.map emb).card := by
    simpa [Finset.card_map] using hGood5
  obtain ⟨U, hUsub, hUcard⟩ := Finset.exists_subset_card_eq hmap_card
  refine ⟨U, hUcard, ?_, ?_⟩
  · intro y hy
    obtain ⟨yS, _, rfl⟩ := Finset.mem_map.mp (hUsub hy)
    exact yS.2
  · intro y hy
    obtain ⟨yS, hyGood, rfl⟩ := Finset.mem_map.mp (hUsub hy)
    simp only [Good, Finset.mem_filter, Finset.mem_univ, true_and] at hyGood
    exact hyGood

end GraphMinor.Crossing
