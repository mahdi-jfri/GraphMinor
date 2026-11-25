module

public import GraphMinor.LPPS22.LemmaA3
public import GraphMinor.Surface.DiscRemove
public import GraphMinor.Surface.OrientCocycle
public import GraphMinor.GM07.Section2Base

/-!
# LPPS22 Theorem A.2: Disc Excision and Matching-Forest Crossing Bound

This file provides the topological excision lemmas and the star-forest crossing bound
used to reduce Graph Minors VII (3.6) (`WExplicitStatement`) to LPPS22 Lemma A.3
(`GraphMinor.LPPS22.lpps22_lemma_A_3`):

1. `homeo_glue_id`: glues a homeomorphism `φA : A ≃ₜ A` fixing `A ∩ B` with the identity on `B`
   when `A, B` are closed sets covering the space.
2. `remove_disc_model` and `remove_discs_model`: excising `p` pairwise disjoint closed discs
   from the interior of a connected surface `S ≃ₜ SurfaceModel a b c` produces a connected surface
   homeomorphic to `SurfaceModel a b (c + p)`.
3. `cut_off_disc_model` and `cut_off_discs_model`: cutting off `q` pairwise disjoint boundary
   closed discs along separating proper `I`-arcs preserves the surface model type
   `SurfaceModel a b c`.
4. `drawing_matching_to_family`: converts a matching `G` with `G.V.ncard ≤ 2 * n` into a family
   of `n' ≤ n` pairwise disjoint proper `I`-arcs.
5. `lpps22_theorem_A_2`: given `p ≤ k` interior closed discs disjoint from a matching `G` and
   `m ≤ 2 * k` pairwise disjoint proper `I`-arcs in the punctured surface whose boundary ends
   avoid `G.V`, produces a homeomorphism `φ : S ≃ₜ S` fixing `bd S` and every disc pointwise
   with `(G.U ∩ ⋃ i, φ '' L i).ncard ≤ 2 * k * 3 ^ (2 * n + 3 * (2 * a + b) + c + k)`.
-/

@[expose] public section

namespace GraphMinor.LPPS22

open Set Topology Metric Filter
open GraphMinor.Surface GraphMinor.GHR18 GraphMinor.GM07

/-! ### Section 1: Gluing a homeomorphism with the identity on a closed cover -/

/-- Glue a homeomorphism `φA : A ≃ₜ A` that fixes `A ∩ B` pointwise with the identity on `B`,
where `A` and `B` are closed sets covering `S`. -/
noncomputable def homeo_glue_id {S : Type*} [TopologicalSpace S] {A B : Set S}
    (hA : IsClosed A) (hB : IsClosed B) (hAB : A ∪ B = univ)
    (φA : A ≃ₜ A) (hfix : ∀ x : A, x.1 ∈ B → (φA x).1 = x.1) : S ≃ₜ S := by
  classical
  have hfix_symm : ∀ x : A, x.1 ∈ B → (φA.symm x).1 = x.1 := fun x hxB => by
    have h1 : φA x = x := Subtype.ext (hfix x hxB)
    have h2 : φA.symm (φA x) = φA.symm x := congrArg φA.symm h1
    rw [φA.symm_apply_apply] at h2
    exact congrArg Subtype.val h2.symm
  let f : S → S := fun x => if hx : x ∈ A then (φA ⟨x, hx⟩).1 else x
  let g : S → S := fun x => if hx : x ∈ A then (φA.symm ⟨x, hx⟩).1 else x
  have hfA : ∀ (x : S) (hx : x ∈ A), f x = (φA ⟨x, hx⟩).1 := fun x hx => by
    simp only [f, hx, ↓reduceDIte]
  have hfB : ∀ x ∈ B, f x = x := fun x hxB => by
    dsimp only [f]
    split_ifs with hxA
    · exact hfix ⟨x, hxA⟩ hxB
    · rfl
  have hgA : ∀ (x : S) (hx : x ∈ A), g x = (φA.symm ⟨x, hx⟩).1 := fun x hx => by
    simp only [g, hx, ↓reduceDIte]
  have hgB : ∀ x ∈ B, g x = x := fun x hxB => by
    dsimp only [g]
    split_ifs with hxA
    · exact hfix_symm ⟨x, hxA⟩ hxB
    · rfl
  have hcont_of : ∀ (h : S → S),
      ContinuousOn h A → ContinuousOn h B → Continuous h := fun h hcA hcB => by
    rw [← continuousOn_univ, ← hAB]
    exact hcA.union_of_isClosed hcB hA hB
  have hf_contA : ContinuousOn f A := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : A.domRestrict f = Subtype.val ∘ φA := by
      ext ⟨x, hx⟩; exact hfA x hx
    rw [heq]
    exact continuous_subtype_val.comp φA.continuous
  have hf_contB : ContinuousOn f B := continuousOn_id.congr (fun x hx => hfB x hx)
  have hg_contA : ContinuousOn g A := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : A.domRestrict g = Subtype.val ∘ φA.symm := by
      ext ⟨x, hx⟩; exact hgA x hx
    rw [heq]
    exact continuous_subtype_val.comp φA.symm.continuous
  have hg_contB : ContinuousOn g B := continuousOn_id.congr (fun x hx => hgB x hx)
  have hleft : Function.LeftInverse g f := fun x => by
    by_cases hx : x ∈ A
    · have hfxA : f x ∈ A := by rw [hfA x hx]; exact (φA ⟨x, hx⟩).2
      rw [hgA _ hfxA]
      have hsub : (⟨f x, hfxA⟩ : A) = φA ⟨x, hx⟩ := Subtype.ext (hfA x hx)
      rw [hsub, φA.symm_apply_apply]
    · have hxB : x ∈ B := (mem_union _ _ _).mp (hAB.symm ▸ mem_univ x) |>.resolve_left hx
      rw [hfB x hxB, hgB x hxB]
  have hright : Function.RightInverse g f := fun x => by
    by_cases hx : x ∈ A
    · have hgxA : g x ∈ A := by rw [hgA x hx]; exact (φA.symm ⟨x, hx⟩).2
      rw [hfA _ hgxA]
      have hsub : (⟨g x, hgxA⟩ : A) = φA.symm ⟨x, hx⟩ := Subtype.ext (hgA x hx)
      rw [hsub, φA.apply_symm_apply]
    · have hxB : x ∈ B := (mem_union _ _ _).mp (hAB.symm ▸ mem_univ x) |>.resolve_left hx
      rw [hgB x hxB, hfB x hxB]
  exact
    { toFun := f
      invFun := g
      left_inv := hleft
      right_inv := hright
      continuous_toFun := hcont_of f hf_contA hf_contB
      continuous_invFun := hcont_of g hg_contA hg_contB }

theorem homeo_glue_id_apply_mem_left {S : Type*} [TopologicalSpace S] {A B : Set S}
    (hA : IsClosed A) (hB : IsClosed B) (hAB : A ∪ B = univ)
    (φA : A ≃ₜ A) (hfix : ∀ x : A, x.1 ∈ B → (φA x).1 = x.1) {x : S} (hx : x ∈ A) :
    homeo_glue_id hA hB hAB φA hfix x = (φA ⟨x, hx⟩).1 := by
  classical
  change (if hxA : x ∈ A then (φA ⟨x, hxA⟩).1 else x) = (φA ⟨x, hx⟩).1
  simp only [hx, ↓reduceDIte]

theorem homeo_glue_id_apply_mem_right {S : Type*} [TopologicalSpace S] {A B : Set S}
    (hA : IsClosed A) (hB : IsClosed B) (hAB : A ∪ B = univ)
    (φA : A ≃ₜ A) (hfix : ∀ x : A, x.1 ∈ B → (φA x).1 = x.1) {x : S} (hx : x ∈ B) :
    homeo_glue_id hA hB hAB φA hfix x = x := by
  classical
  change (if hxA : x ∈ A then (φA ⟨x, hxA⟩).1 else x) = x
  split_ifs with hxA
  · exact hfix ⟨x, hxA⟩ hx
  · rfl

/-! ### Section 2: Excising interior closed discs (`remove_disc_model`, `remove_discs_model`) -/

/-- Removing the open interior of a single closed disc `E ⊆ (bd S)ᶜ` from a connected surface
`S ≃ₜ SurfaceModel a b c` yields a connected surface homeomorphic to `SurfaceModel a b (c + 1)`. -/
theorem remove_disc_model {S : Type} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsSurface S) {a b c : ℕ} (eS : S ≃ₜ SurfaceModel a b c)
    {E : Set S} (hE : IsClosedDisc E) (hEbd : Disjoint E (bd S)) :
    IsClosed (discInt E)ᶜ ∧ IsSurface ↥(discInt E)ᶜ ∧ ConnectedSpace ↥(discInt E)ᶜ ∧
      bd ↥(discInt E)ᶜ = Subtype.val ⁻¹' (bd S ∪ discBd E) ∧
      Nonempty (↥(discInt E)ᶜ ≃ₜ SurfaceModel a b (c + 1)) := by
  classical
  have ht2S : T2Space S := hS.2.1
  have hcS : CompactSpace S := hS.1
  have hint : ∀ x ∈ discBd E, IsInteriorPoint x := fun x hx => by
    by_contra hni
    exact Set.disjoint_left.mp hEbd (discBd_subset E hx) hni
  obtain ⟨hcl, hsurf, hbd⟩ := remove_disc hS hE hint
  have hce : IsClosedEmbedding (Subtype.val : ↥(discInt E)ᶜ → S) := hcl.isClosedEmbedding_subtypeVal
  -- `K := Subtype.val ⁻¹' discBd E` is nonempty, closed, and connected (homeomorphic to `Circle`).
  let K : Set ↥(discInt E)ᶜ := Subtype.val ⁻¹' discBd E
  obtain ⟨φK⟩ := hE.isOArc_discBd
  have hKsub : discBd E ⊆ (discInt E)ᶜ := fun x hx h => h.2 hx
  let eK : Circle ≃ₜ K :=
    { toFun := fun z => ⟨⟨(φK z).1, hKsub (φK z).2⟩, (φK z).2⟩
      invFun := fun x => φK.symm ⟨x.1.1, x.2⟩
      left_inv := fun z => by simp
      right_inv := fun x => by ext; simp
      continuous_toFun := by
        refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
        exact continuous_subtype_val.comp φK.continuous
      continuous_invFun := φK.symm.continuous.comp
        (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _) }
  have hKne : K.Nonempty := ⟨eK 1, (eK 1).2⟩
  have hKconn : IsPreconnected K := by
    have h1 : IsPreconnected (range (fun z : Circle => (eK z).1)) :=
      isPreconnected_range (continuous_subtype_val.comp eK.continuous)
    have h2 : range (fun z : Circle => (eK z).1) = K := by
      ext x
      constructor
      · rintro ⟨z, rfl⟩; exact (eK z).2
      · intro hx; exact ⟨eK.symm ⟨x, hx⟩, by simp⟩
    rwa [h2] at h1
  have hKcl : IsClosed K := by
    have hbdE_cl : IsClosed (discBd E) := by
      have hc : IsCompact (discBd E) := by
        have : discBd E = range (fun z : Circle => (φK z).1) := by
          ext x
          constructor
          · intro hx; exact ⟨φK.symm ⟨x, hx⟩, by simp⟩
          · rintro ⟨z, rfl⟩; exact (φK z).2
        rw [this]
        exact isCompact_range (continuous_subtype_val.comp φK.continuous)
      exact hc.isClosed
    exact hbdE_cl.preimage continuous_subtype_val
  -- Connectedness of `↥(discInt E)ᶜ`.
  have hne : Nonempty ↥(discInt E)ᶜ := ⟨hKne.some⟩
  have hconn : ConnectedSpace ↥(discInt E)ᶜ := by
    rw [connectedSpace_iff_clopen]
    refine ⟨hne, fun W hW => ?_⟩
    have hW_case : K ⊆ W ∨ K ⊆ Wᶜ := by
      by_cases h1 : (K ∩ W).Nonempty
      · left
        intro x hx
        by_contra hxW
        have h2 : (K ∩ Wᶜ).Nonempty := ⟨x, hx, hxW⟩
        obtain ⟨z, -, hzW, hzWc⟩ := hKconn W Wᶜ hW.isOpen hW.isClosed.isOpen_compl
          (fun _ _ => em _) h1 h2
        exact hzWc hzW
      · right
        intro x hx hxW
        exact h1 ⟨x, hx, hxW⟩
    rcases hW_case with hKW | hKWc
    · right
      let A : Set S := Subtype.val '' W ∪ E
      let B : Set S := Subtype.val '' Wᶜ
      have hAcl : IsClosed A := (hce.isClosedMap _ hW.isClosed).union hE.isClosed
      have hBcl : IsClosed B := hce.isClosedMap _ hW.isOpen.isClosed_compl
      have hAB : univ ⊆ A ∪ B := fun z _ => by
        by_cases hz : z ∈ E
        · exact Or.inl (Or.inr hz)
        · have hz' : z ∈ (discInt E)ᶜ := fun h => hz h.1
          by_cases hzW : (⟨z, hz'⟩ : ↥(discInt E)ᶜ) ∈ W
          · exact Or.inl (Or.inl ⟨⟨z, hz'⟩, hzW, rfl⟩)
          · exact Or.inr ⟨⟨z, hz'⟩, hzW, rfl⟩
      have hABdisj : A ∩ B = ∅ := by
        ext z
        simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
        rintro (⟨w, hwW, rfl⟩ | hzE) ⟨w', hw'Wc, hww'⟩
        · exact hw'Wc ((Subtype.ext hww'.symm) ▸ hwW)
        · have hw'K : w' ∈ K := by
            show w'.1 ∈ discBd E
            by_contra hnb
            exact w'.2 ⟨hww'.symm ▸ hzE, hnb⟩
          exact hw'Wc (hKW hw'K)
      have hAne : (univ ∩ A).Nonempty := by
        obtain ⟨z, hz⟩ := hE.nonempty_discInt
        exact ⟨z, mem_univ z, Or.inr (discInt_subset E hz)⟩
      have hBe : B = ∅ := by
        by_contra hBne
        obtain ⟨z, hzB⟩ := Set.nonempty_iff_ne_empty.mpr hBne
        obtain ⟨w, -, hwA, hwB⟩ := isPreconnected_closed_iff.mp isPreconnected_univ
          A B hAcl hBcl hAB hAne ⟨z, mem_univ z, hzB⟩
        exact (Set.eq_empty_iff_forall_notMem.mp hABdisj w) ⟨hwA, hwB⟩
      ext x
      simp only [mem_univ, iff_true]
      by_contra hxW
      exact (Set.eq_empty_iff_forall_notMem.mp hBe x.1) ⟨x, hxW, rfl⟩
    · left
      let A : Set S := Subtype.val '' Wᶜ ∪ E
      let B : Set S := Subtype.val '' W
      have hAcl : IsClosed A := (hce.isClosedMap _ hW.isOpen.isClosed_compl).union hE.isClosed
      have hBcl : IsClosed B := hce.isClosedMap _ hW.isClosed
      have hAB : univ ⊆ A ∪ B := fun z _ => by
        by_cases hz : z ∈ E
        · exact Or.inl (Or.inr hz)
        · have hz' : z ∈ (discInt E)ᶜ := fun h => hz h.1
          by_cases hzW : (⟨z, hz'⟩ : ↥(discInt E)ᶜ) ∈ W
          · exact Or.inr ⟨⟨z, hz'⟩, hzW, rfl⟩
          · exact Or.inl (Or.inl ⟨⟨z, hz'⟩, hzW, rfl⟩)
      have hABdisj : A ∩ B = ∅ := by
        ext z
        simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
        rintro (⟨w, hwWc, rfl⟩ | hzE) ⟨w', hw'W, hww'⟩
        · exact hwWc ((Subtype.ext hww') ▸ hw'W)
        · have hw'K : w' ∈ K := by
            show w'.1 ∈ discBd E
            by_contra hnb
            exact w'.2 ⟨hww'.symm ▸ hzE, hnb⟩
          exact hKWc hw'K hw'W
      have hAne : (univ ∩ A).Nonempty := by
        obtain ⟨z, hz⟩ := hE.nonempty_discInt
        exact ⟨z, mem_univ z, Or.inr (discInt_subset E hz)⟩
      have hBe : B = ∅ := by
        by_contra hBne
        obtain ⟨z, hzB⟩ := Set.nonempty_iff_ne_empty.mpr hBne
        obtain ⟨w, -, hwA, hwB⟩ := isPreconnected_closed_iff.mp isPreconnected_univ
          A B hAcl hBcl hAB hAne ⟨z, mem_univ z, hzB⟩
        exact (Set.eq_empty_iff_forall_notMem.mp hABdisj w) ⟨hwA, hwB⟩
      ext x
      simp only [mem_empty_iff_false, iff_false]
      intro hxW
      exact (Set.eq_empty_iff_forall_notMem.mp hBe x.1) ⟨x, hxW, rfl⟩
  -- `K` is a cuff of `↥(discInt E)ᶜ`.
  have hKcuff : IsCuff K := by
    obtain ⟨x₀, hx₀K⟩ := hKne
    refine ⟨x₀, by rw [hbd]; exact Or.inr hx₀K, ?_⟩
    apply Subset.antisymm
    · set C₀ := connectedComponentIn (bd ↥(discInt E)ᶜ) x₀
      have hC₀sub : C₀ ⊆ K ∪ (Subtype.val ⁻¹' bd S) := fun z hz => by
        have hzb : z ∈ bd ↥(discInt E)ᶜ := connectedComponentIn_subset _ _ hz
        rw [hbd] at hzb
        exact hzb.symm
      have hbd_pre_cl : IsClosed (Subtype.val ⁻¹' bd S : Set ↥(discInt E)ᶜ) :=
        (isClosed_bd S).preimage continuous_subtype_val
      have hdisj : Disjoint K (Subtype.val ⁻¹' bd S) :=
        Set.disjoint_left.mpr fun z hzK hzbd =>
          Set.disjoint_left.mp hEbd (discBd_subset E hzK) hzbd
      intro z hzC₀
      by_contra hzK
      have hzbd : z ∈ (Subtype.val ⁻¹' bd S : Set ↥(discInt E)ᶜ) :=
        (hC₀sub hzC₀).resolve_left hzK
      obtain ⟨w, -, hwK, hwbd⟩ := isPreconnected_closed_iff.mp isPreconnected_connectedComponentIn
        K (Subtype.val ⁻¹' bd S) hKcl hbd_pre_cl hC₀sub
        ⟨x₀, mem_connectedComponentIn (by rw [hbd]; exact Or.inr hx₀K), hx₀K⟩
        ⟨z, hzC₀, hzbd⟩
      exact Set.disjoint_left.mp hdisj hwK hwbd
    · exact hKconn.subset_connectedComponentIn hx₀K fun z hz => by rw [hbd]; exact Or.inr hz
  -- Classification + `paste_model` + `modelCriterion`.
  obtain ⟨a', b', c', ⟨e'⟩⟩ := classification.{0} ↥(discInt E)ᶜ hsurf hconn
  have hu : range (Subtype.val : ↥(discInt E)ᶜ → S) ∪ E = univ := by
    ext z
    simp only [mem_union, Subtype.range_val, mem_univ, iff_true]
    by_cases hz : z ∈ E
    · exact Or.inr hz
    · exact Or.inl fun h => hz h.1
  have hKval : Subtype.val '' K = discBd E := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩; exact hw
    · intro hz; exact ⟨⟨z, hKsub hz⟩, hz, rfl⟩
  have hm : range (Subtype.val : ↥(discInt E)ᶜ → S) ∩ E = Subtype.val '' K := by
    rw [hKval]
    ext z
    simp only [mem_inter_iff, Subtype.range_val, mem_compl_iff, discInt, Set.mem_sdiff, not_and,
      not_not]
    exact ⟨fun ⟨h1, h2⟩ => h1 h2, fun h => ⟨fun _ => h, discBd_subset E h⟩⟩
  obtain ⟨hc'_pos, ⟨eS'⟩⟩ := paste_model hsurf hKcuff hS hce hE hu hm hKval.symm e'
  obtain ⟨hc_eq, h2ab_eq, hb_iff⟩ :=
    (modelCriterion.2 a' b' (c' - 1) a b c).mp ⟨eS'.symm.trans eS⟩
  have hc'_eq : c' = c + 1 := by omega
  obtain ⟨em⟩ := (modelCriterion.2 a' b' c' a b (c + 1)).mpr ⟨hc'_eq, h2ab_eq, hb_iff⟩
  exact ⟨hcl, hsurf, hconn, hbd, ⟨e'.trans em⟩⟩

/-- Removing the open interiors of `p` pairwise disjoint closed discs `Δ : Fin p → Set S` in the
interior of a connected surface `S ≃ₜ SurfaceModel a b c` produces a connected surface homeomorphic
to `SurfaceModel a b (c + p)`. -/
theorem remove_discs_model {S : Type} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsSurface S) {a b c : ℕ} (eS : S ≃ₜ SurfaceModel a b c)
    {p : ℕ} {Δ : Fin p → Set S}
    (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hΔbd : ∀ i, Disjoint (Δ i) (bd S))
    (hΔdisj : Pairwise fun i j => Disjoint (Δ i) (Δ j)) :
    IsClosed (⋃ i : Fin p, discInt (Δ i))ᶜ ∧
      IsSurface ↥(⋃ i : Fin p, discInt (Δ i))ᶜ ∧
      ConnectedSpace ↥(⋃ i : Fin p, discInt (Δ i))ᶜ ∧
      bd ↥(⋃ i : Fin p, discInt (Δ i))ᶜ = Subtype.val ⁻¹' (bd S ∪ ⋃ i : Fin p, discBd (Δ i)) ∧
      Nonempty (↥(⋃ i : Fin p, discInt (Δ i))ᶜ ≃ₜ SurfaceModel a b (c + p)) := by
  induction p with
  | zero =>
    have hun : (⋃ i : Fin 0, discInt (Δ i))ᶜ = (univ : Set S) := by simp
    let eU : ↥(⋃ i : Fin 0, discInt (Δ i))ᶜ ≃ₜ S :=
      (Homeomorph.setCongr hun).trans (Homeomorph.Set.univ S)
    have hsurf : IsSurface ↥(⋃ i : Fin 0, discInt (Δ i))ᶜ := isSurface_of_homeo eU.symm hS
    have hconn : ConnectedSpace ↥(⋃ i : Fin 0, discInt (Δ i))ᶜ :=
      eU.symm.surjective.connectedSpace eU.symm.continuous
    have hbd : bd ↥(⋃ i : Fin 0, discInt (Δ i))ᶜ =
        Subtype.val ⁻¹' (bd S ∪ ⋃ i : Fin 0, discBd (Δ i)) := by
      ext x
      have h1 : x ∈ bd ↥(⋃ i : Fin 0, discInt (Δ i))ᶜ ↔ eU x ∈ bd S := by
        rw [← image_bd_homeomorph eU]
        exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, he⟩ => eU.injective he ▸ hy⟩
      have hval : eU x = x.1 := rfl
      simp [h1, hval]
    exact ⟨hun ▸ isClosed_univ, hsurf, hconn, hbd, ⟨eU.trans eS⟩⟩
  | succ p ih =>
    have ht2S : T2Space S := hS.2.1
    let Δ' : Fin p → Set S := fun i => Δ i.castSucc
    obtain ⟨hcl₁, hsurf₁, hconn₁, hbd₁, ⟨e₁⟩⟩ := ih
      (fun i => hΔ i.castSucc)
      (fun i => hΔbd i.castSucc)
      (fun i j hij => hΔdisj (Fin.castSucc_injective p |>.ne hij))
    let S₁ := ↥(⋃ i : Fin p, discInt (Δ' i))ᶜ
    have hce₁ : IsClosedEmbedding (Subtype.val : S₁ → S) := hcl₁.isClosedEmbedding_subtypeVal
    have hcS₁ : CompactSpace S₁ := hsurf₁.1
    have ht2S₁ : T2Space S₁ := hsurf₁.2.1
    have hneS₁ : Nonempty S₁ := hconn₁.toNonempty
    have hlast_sub : Δ (Fin.last p) ⊆ range (Subtype.val : S₁ → S) := by
      rw [Subtype.range_val]
      intro z hz hmem
      obtain ⟨i, hi⟩ := mem_iUnion.mp hmem
      exact Set.disjoint_left.mp (hΔdisj (Fin.castSucc_ne_last i)) (discInt_subset _ hi) hz
    obtain ⟨hE₁, hE₁bd⟩ := isClosedDisc_preimage hce₁ (hΔ (Fin.last p)) hlast_sub
    let E₁ : Set S₁ := Subtype.val ⁻¹' Δ (Fin.last p)
    have hE₁disj : Disjoint E₁ (bd S₁) := by
      rw [hbd₁, Set.disjoint_left]
      intro x hxE hxbd
      rcases hxbd with hxbdS | hxU
      · exact Set.disjoint_left.mp (hΔbd (Fin.last p)) hxE hxbdS
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hxU
        exact Set.disjoint_left.mp (hΔdisj (Fin.castSucc_ne_last i)) (discBd_subset _ hi) hxE
    obtain ⟨hcl₂, hsurf₂, hconn₂, hbd₂, ⟨e₂⟩⟩ := remove_disc_model hsurf₁ e₁ hE₁ hE₁disj
    have hE₁int : discInt E₁ = Subtype.val ⁻¹' discInt (Δ (Fin.last p)) := by
      change E₁ \ discBd E₁ = Subtype.val ⁻¹' (Δ (Fin.last p) \ discBd (Δ (Fin.last p)))
      rw [hE₁bd]
      rfl
    have hcov_eq : ∀ z : S,
        z ∈ (⋃ i : Fin (p + 1), discInt (Δ i))ᶜ ↔
          ∃ h : z ∈ (⋃ i : Fin p, discInt (Δ' i))ᶜ, (⟨z, h⟩ : S₁) ∈ (discInt E₁)ᶜ := by
      intro z
      simp only [mem_compl_iff, mem_iUnion, not_exists, hE₁int, mem_preimage]
      constructor
      · intro hz
        exact ⟨fun i => hz i.castSucc, hz (Fin.last p)⟩
      · rintro ⟨h1, h2⟩ i
        exact Fin.lastCases h2 h1 i
    let e_iso : ↥(discInt E₁)ᶜ ≃ₜ ↥(⋃ i : Fin (p + 1), discInt (Δ i))ᶜ :=
      { toFun := fun x => ⟨x.1.1, (hcov_eq x.1.1).mpr ⟨x.1.2, x.2⟩⟩
        invFun := fun y => ⟨⟨y.1, ((hcov_eq y.1).mp y.2).1⟩, ((hcov_eq y.1).mp y.2).2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        continuous_toFun := Continuous.subtype_mk
          (continuous_subtype_val.comp continuous_subtype_val) _
        continuous_invFun := Continuous.subtype_mk
          (Continuous.subtype_mk continuous_subtype_val _) _ }
    have hcl_fin : IsClosed (⋃ i : Fin (p + 1), discInt (Δ i))ᶜ := by
      rw [isClosed_compl_iff]
      exact isOpen_iUnion fun i => (hΔ i).isOpen_discInt hS.2.2
    have hsurf_fin : IsSurface ↥(⋃ i : Fin (p + 1), discInt (Δ i))ᶜ :=
      isSurface_of_homeo e_iso hsurf₂
    have hconn_fin : ConnectedSpace ↥(⋃ i : Fin (p + 1), discInt (Δ i))ᶜ :=
      e_iso.surjective.connectedSpace e_iso.continuous
    have hbd_fin : bd ↥(⋃ i : Fin (p + 1), discInt (Δ i))ᶜ =
        Subtype.val ⁻¹' (bd S ∪ ⋃ i : Fin (p + 1), discBd (Δ i)) := by
      ext y
      have h1 : y ∈ bd ↥(⋃ i : Fin (p + 1), discInt (Δ i))ᶜ ↔ e_iso.symm y ∈ bd ↥(discInt E₁)ᶜ := by
        rw [← image_bd_homeomorph e_iso.symm]
        exact ⟨fun hy => ⟨y, hy, rfl⟩, fun ⟨z, hz, he⟩ => e_iso.symm.injective he ▸ hz⟩
      rw [h1, hbd₂, mem_preimage, mem_union, hbd₁, hE₁bd]
      change (y.1 ∈ bd S ∪ ⋃ i : Fin p, discBd (Δ' i)) ∨ y.1 ∈ discBd (Δ (Fin.last p)) ↔
        y.1 ∈ bd S ∪ ⋃ i : Fin (p + 1), discBd (Δ i)
      simp only [mem_union, mem_iUnion]
      constructor
      · rintro ((h | ⟨i, hi⟩) | hlast)
        · exact Or.inl h
        · exact Or.inr ⟨i.castSucc, hi⟩
        · exact Or.inr ⟨Fin.last p, hlast⟩
      · rintro (h | ⟨i, hi⟩)
        · exact Or.inl (Or.inl h)
        · exact Fin.lastCases (motive := fun i => y.1 ∈ discBd (Δ i) → _)
            (fun h => Or.inr h) (fun j h => Or.inl (Or.inr ⟨j, h⟩)) i hi
    have hmod_eq : c + (p + 1) = c + p + 1 := by omega
    rw [hmod_eq]
    exact ⟨hcl_fin, hsurf_fin, hconn_fin, hbd_fin, ⟨e_iso.symm.trans e₂⟩⟩

/-! ### Section 3: Cutting off boundary closed discs (`cut_off_disc_model`, `cut_off_discs_model`) -/

/-- Every point `z` of a surface `Y` has an open neighbourhood `V` such that `V \ bd Y` is
preconnected and `V ⊆ closure (V \ bd Y)`. -/
private theorem exists_open_nhd_connected_int {Y : Type} [TopologicalSpace Y]
    (hY : IsSurface Y) (z : Y) :
    ∃ V : Set Y, IsOpen V ∧ z ∈ V ∧ IsPreconnected (V \ bd Y) ∧ V ⊆ closure (V \ bd Y) := by
  obtain ⟨ch, hzU⟩ := exists_surfChart (hY.2.2 z)
  obtain ⟨r, hr0, hball⟩ := Metric.isOpen_iff.mp ch.hO (ch.j z) (ch.hm hzU).1
  let B : Set ℂ := Metric.ball (ch.j z) r ∩ halfPlane
  let B_int : Set ℂ := Metric.ball (ch.j z) r ∩ {w : ℂ | 0 < w.re}
  let V : Set Y := ch.U ∩ ch.j ⁻¹' Metric.ball (ch.j z) r
  have hV_open : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hca : ContinuousAt ch.j x := ch.hj.continuousAt (ch.hU.mem_nhds hx.1)
    exact Filter.inter_mem (ch.hU.mem_nhds hx.1) (hca (Metric.isOpen_ball.mem_nhds hx.2))
  have hzV : z ∈ V := ⟨hzU, Metric.mem_ball_self hr0⟩
  have hB_sub : B ⊆ ch.O ∩ halfPlane := fun w hw => ⟨hball hw.1, hw.2⟩
  have hVint_eq : V \ bd Y = ch.k '' B_int := by
    ext x
    constructor
    · rintro ⟨hxV, hxnb⟩
      refine ⟨ch.j x, ⟨hxV.2, (ch.not_mem_bd_iff hxV.1).mp hxnb⟩, ch.hl hxV.1⟩
    · rintro ⟨w, hw, rfl⟩
      have hwB : w ∈ B := ⟨hw.1, show (0 : ℝ) ≤ w.re from le_of_lt hw.2⟩
      have hkU : ch.k w ∈ ch.U := ch.hk' (hB_sub hwB)
      refine ⟨⟨hkU, ?_⟩, ?_⟩
      · show ch.j (ch.k w) ∈ Metric.ball (ch.j z) r
        rw [ch.hr (hB_sub hwB)]; exact hw.1
      · rw [ch.not_mem_bd_iff hkU, ch.hr (hB_sub hwB)]; exact hw.2
  have hBint_conv : Convex ℝ B_int := by
    intro a ha b hb s t hs ht hst
    refine ⟨(convex_ball (ch.j z) r) ha.1 hb.1 hs ht hst, ?_⟩
    show 0 < (s • a + t • b).re
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    have ha' : 0 < a.re := ha.2
    have hb' : 0 < b.re := hb.2
    rcases eq_or_lt_of_le hs with rfl | hs'
    · nlinarith
    · nlinarith
  have hVint_conn : IsPreconnected (V \ bd Y) := by
    rw [hVint_eq]
    exact hBint_conv.isPreconnected.image ch.k
      (ch.hk.mono fun w hw => hB_sub ⟨hw.1, show (0 : ℝ) ≤ w.re from le_of_lt hw.2⟩)
  have hV_sub_cl : V ⊆ closure (V \ bd Y) := by
    intro x hxV
    rw [hVint_eq]
    have hxB : ch.j x ∈ B := ⟨hxV.2, (ch.hm hxV.1).2⟩
    have hcont_at : ContinuousWithinAt ch.k (ch.O ∩ halfPlane) (ch.j x) :=
      ch.hk (ch.j x) (hB_sub hxB)
    rw [← ch.hl hxV.1]
    have hclB : ch.j x ∈ closure B_int := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      let δ : ℝ := min (ε / 2) ((r - dist (ch.j x) (ch.j z)) / 2)
      have hdist_lt : dist (ch.j x) (ch.j z) < r := Metric.mem_ball.mp hxB.1
      have hδ_pos : 0 < δ := lt_min (by linarith) (by linarith)
      refine ⟨ch.j x + (δ : ℂ), ⟨?_, ?_⟩, ?_⟩
      · rw [Metric.mem_ball]
        calc dist (ch.j x + (δ : ℂ)) (ch.j z)
            ≤ dist (ch.j x + (δ : ℂ)) (ch.j x) + dist (ch.j x) (ch.j z) := dist_triangle _ _ _
          _ = δ + dist (ch.j x) (ch.j z) := by
              rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg hδ_pos.le]
          _ < r := by linarith [min_le_right (ε / 2) ((r - dist (ch.j x) (ch.j z)) / 2)]
      · show 0 < (ch.j x + (δ : ℂ)).re
        have hre : 0 ≤ (ch.j x).re := hxB.2
        simp only [Complex.add_re, Complex.ofReal_re]
        linarith
      · rw [dist_eq_norm, sub_add_cancel_left, norm_neg, Complex.norm_real, Real.norm_of_nonneg hδ_pos.le]
        linarith [min_le_left (ε / 2) ((r - dist (ch.j x) (ch.j z)) / 2)]
    rw [_root_.mem_closure_iff]
    intro U hU hkxU
    have hnhd : ch.k ⁻¹' U ∈ 𝓝[ch.O ∩ halfPlane] (ch.j x) :=
      hcont_at (hU.mem_nhds hkxU)
    rw [Metric.mem_nhdsWithin_iff] at hnhd
    obtain ⟨δ, hδ_pos, hδ_sub⟩ := hnhd
    obtain ⟨w, hw_int, hw_dist⟩ := Metric.mem_closure_iff.mp hclB δ hδ_pos
    have hw_mem : w ∈ ch.O ∩ halfPlane := hB_sub ⟨hw_int.1, show (0 : ℝ) ≤ w.re from le_of_lt hw_int.2⟩
    have hw_ball : w ∈ Metric.ball (ch.j x) δ := by rwa [Metric.mem_ball, dist_comm]
    exact ⟨ch.k w, hδ_sub ⟨hw_ball, hw_mem⟩, ⟨w, hw_int, rfl⟩⟩
  exact ⟨V, hV_open, hzV, hVint_conn, hV_sub_cl⟩

/-- Cutting a connected surface `S ≃ₜ SurfaceModel a b c` along a proper `I`-arc `A` that cuts
off a closed disc `D` (`A ⊆ discBd D`, `IsOpen (D \ A)`) leaves a connected surface
`↥(D \ A)ᶜ` homeomorphic to the same model `SurfaceModel a b c`. -/
theorem cut_off_disc_model {S : Type} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsSurface S) {a b c : ℕ} (eS : S ≃ₜ SurfaceModel a b c)
    {D A : Set S} {s t : S}
    (hD : IsClosedDisc D) (hA_sub : A ⊆ discBd D)
    (hst : s ≠ t) (hAb : A ∩ bd S = {s, t}) (hAl : IsLineWithEnds A s t)
    (hopen : IsOpen (D \ A)) :
    IsClosed (D \ A)ᶜ ∧ IsSurface ↥(D \ A)ᶜ ∧ ConnectedSpace ↥(D \ A)ᶜ ∧
      bd ↥(D \ A)ᶜ = Subtype.val ⁻¹' (bd S ∪ A) ∧
      Nonempty (↥(D \ A)ᶜ ≃ₜ SurfaceModel a b c) := by
  classical
  have ht2S : T2Space S := hS.2.1
  have hcS : CompactSpace S := hS.1
  have hcl : IsClosed (D \ A)ᶜ := hopen.isClosed_compl
  -- Step 1: `A ⊆ closure Dᶜ` and `Dᶜ.Nonempty` (since `A \ {s, t}` is nonempty and disjoint from `bd S`).
  have hA_diff_cl : A \ {s, t} ⊆ closure Dᶜ := fun p hp => by
    by_contra hnot
    have hD_nhd : D ∈ 𝓝 p := by
      have hopen' : IsOpen (closure Dᶜ)ᶜ := isClosed_closure.isOpen_compl
      refine mem_of_superset (hopen'.mem_nhds hnot) fun z hz => ?_
      by_contra hzD
      exact hz (subset_closure hzD)
    have hp_bd : p ∈ bd S := mem_bd_of_disc hD_nhd (hA_sub hp.1)
    have hp_st : p ∈ ({s, t} : Set S) := hAb ▸ ⟨hp.1, hp_bd⟩
    exact hp.2 hp_st
  have hA_cl_Dc : A ⊆ closure Dᶜ := by
    have h1 := hAl.subset_closure_diff
    calc A ⊆ closure (A \ {s, t}) := h1
      _ ⊆ closure (closure Dᶜ) := closure_mono hA_diff_cl
      _ = closure Dᶜ := closure_closure
  have hcl_Dc_eq : closure Dᶜ = (D \ A)ᶜ := by
    apply Subset.antisymm
    · exact closure_minimal (fun z hz h => hz h.1) hcl
    · intro z hz
      by_cases hzD : z ∈ D
      · exact hA_cl_Dc (by_contra fun hzA => hz ⟨hzD, hzA⟩)
      · exact subset_closure hzD
  have hA_mid : (A \ {s, t}).Nonempty := by
    obtain ⟨f, hf0, hf1⟩ := hAl
    have hmem : (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval) ≠ 0 ∧
        (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval) ≠ 1 := by
      constructor <;> intro h <;> have := congrArg Subtype.val h <;> norm_num at this
    refine ⟨(f ⟨1 / 2, by norm_num, by norm_num⟩).1, (f _).2, ?_⟩
    rintro (h | h)
    · exact hmem.1 (f.injective (Subtype.ext (h.trans hf0.symm)))
    · exact hmem.2 (f.injective (Subtype.ext (h.trans hf1.symm)))
  have hDc_ne : Dᶜ.Nonempty := by
    obtain ⟨p, hp⟩ := hA_mid
    have hpcl : p ∈ closure Dᶜ := hA_diff_cl hp
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, closure_empty] at hpcl
    exact hpcl
  have hDA_ne : (D \ A).Nonempty := by
    obtain ⟨p, hp⟩ := hD.nonempty_discInt
    exact ⟨p, hp.1, fun hpA => hp.2 (hA_sub hpA)⟩
  have hcl_DA_eq : closure (D \ A) = D := by
    apply Subset.antisymm
    · exact closure_minimal sdiff_subset hD.isClosed
    · calc D ⊆ closure (discInt D) := hD.subset_closure_discInt
        _ ⊆ closure (D \ A) := closure_mono fun z hz => ⟨hz.1, fun hzA => hz.2 (hA_sub hzA)⟩
  -- Step 2: Cut `S` along `A`.
  obtain ⟨Y, _, _, ψ, hY, hψ, X, X', hP⟩ := exists_cut_arc hS hst hAb hAl
  have ht2Y : T2Space Y := hY.2.1
  have hcY : CompactSpace Y := hY.1
  obtain ⟨a₀, ξ, η, L, -, -, himξ, himη, hiξ, hiη⟩ := exists_arcLift hP hψ
  obtain ⟨x0, x1, y0, y1, l1, l2, hXX', hun, hbx, hbx', hψx0, hψy0, -, -⟩ := hP
  -- Define the two open pieces `U₁ = ψ ⁻¹' (D \ A)` and `U₂ = ψ ⁻¹' Dᶜ`.
  let U₁ : Set Y := ψ ⁻¹' (D \ A)
  let U₂ : Set Y := ψ ⁻¹' Dᶜ
  have hU₁_open : IsOpen U₁ := hopen.preimage hψ.1
  have hU₂_open : IsOpen U₂ := hD.isClosed.isOpen_compl.preimage hψ.1
  have hU₁₂_disj : Disjoint U₁ U₂ := Set.disjoint_left.mpr fun z h1 h2 => h2 h1.1
  have hU₁₂_cov : (bd Y)ᶜ ⊆ U₁ ∪ U₂ := fun z hz => by
    have hzA : ψ z ∉ A := fun h => hz (hψ.2.2.2.2 h)
    by_cases hzD : ψ z ∈ D
    · exact Or.inl ⟨hzD, hzA⟩
    · exact Or.inr hzD
  -- Every point `z : Y` belongs to exactly one of `closure U₁` and `closure U₂`.
  have hpart_cl : ∀ z : Y, (z ∈ closure U₁ ∧ z ∉ closure U₂) ∨ (z ∈ closure U₂ ∧ z ∉ closure U₁) := by
    intro z
    obtain ⟨V, hVopen, hzV, hVconn, hVcl⟩ := exists_open_nhd_connected_int hY z
    have hVsub : V \ bd Y ⊆ U₁ ∪ U₂ := fun w hw => hU₁₂_cov hw.2
    have hcase : V \ bd Y ⊆ U₁ ∨ V \ bd Y ⊆ U₂ := by
      by_cases h1 : ((V \ bd Y) ∩ U₁).Nonempty
      · left
        intro w hw
        by_contra hw1
        have hw2 : w ∈ U₂ := (hVsub hw).resolve_left hw1
        obtain ⟨u, -, hu1, hu2⟩ := hVconn U₁ U₂ hU₁_open hU₂_open hVsub h1 ⟨w, hw, hw2⟩
        exact Set.disjoint_left.mp hU₁₂_disj hu1 hu2
      · right
        intro w hw
        exact (hVsub hw).resolve_left fun hw1 => h1 ⟨w, hw, hw1⟩
    rcases hcase with hV1 | hV2
    · left
      refine ⟨closure_mono hV1 (hVcl hzV), fun hz2 => ?_⟩
      obtain ⟨w, hwV, hwU2⟩ := _root_.mem_closure_iff.mp hz2 V hVopen hzV
      have hw_cl1 : w ∈ closure U₁ := closure_mono hV1 (hVcl hwV)
      obtain ⟨u, huU2, huU1⟩ := _root_.mem_closure_iff.mp hw_cl1 U₂ hU₂_open hwU2
      exact Set.disjoint_left.mp hU₁₂_disj huU1 huU2
    · right
      refine ⟨closure_mono hV2 (hVcl hzV), fun hz1 => ?_⟩
      obtain ⟨w, hwV, hwU1⟩ := _root_.mem_closure_iff.mp hz1 V hVopen hzV
      have hw_cl2 : w ∈ closure U₂ := closure_mono hV2 (hVcl hwV)
      obtain ⟨u, huU1, huU2⟩ := _root_.mem_closure_iff.mp hw_cl2 U₁ hU₁_open hwU1
      exact Set.disjoint_left.mp hU₁₂_disj huU1 huU2
  let Z₁ : Set Y := closure U₁
  let Z₂ : Set Y := closure U₂
  have hZ₁₂_disj : Disjoint Z₁ Z₂ := Set.disjoint_left.mpr fun z h1 h2 => by
    rcases hpart_cl z with ⟨-, h⟩ | ⟨-, h⟩
    · exact h h2
    · exact h h1
  have hZ₁₂_union : Z₁ ∪ Z₂ = univ := by
    ext z; simp only [mem_union, mem_univ, iff_true]
    rcases hpart_cl z with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hZ₁_clopen : IsClopen Z₁ :=
    ⟨isClosed_closure, by
      have : Z₁ = Z₂ᶜ := by
        ext z; simp only [mem_compl_iff]
        rcases hpart_cl z with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨fun _ => h2, fun _ => h1⟩
        · exact ⟨fun h => (h2 h).elim, fun h => (h h1).elim⟩
      rw [this]; exact isClosed_closure.isOpen_compl⟩
  have hZ₂_clopen : IsClopen Z₂ :=
    ⟨isClosed_closure, by
      have : Z₂ = Z₁ᶜ := by
        ext z; simp only [mem_compl_iff]
        rcases hpart_cl z with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨fun h => (h2 h).elim, fun h => (h h1).elim⟩
        · exact ⟨fun _ => h2, fun _ => h1⟩
      rw [this]; exact isClosed_closure.isOpen_compl⟩
  have hZ₁_ne : Z₁.Nonempty := by
    obtain ⟨p, hp⟩ := hDA_ne
    obtain ⟨z, rfl⟩ := hψ.2.1 p
    exact ⟨z, subset_closure hp⟩
  have hZ₂_ne : Z₂.Nonempty := by
    obtain ⟨p, hp⟩ := hDc_ne
    obtain ⟨z, rfl⟩ := hψ.2.1 p
    exact ⟨z, subset_closure hp⟩
  have hnotc : ¬ ConnectedSpace Y := fun hcY' => by
    rcases (connectedSpace_iff_clopen.mp hcY').2 Z₁ hZ₁_clopen with h0 | h1
    · exact hZ₁_ne.ne_empty h0
    · obtain ⟨z, hz⟩ := hZ₂_ne
      exact Set.disjoint_left.mp hZ₁₂_disj (h1.symm ▸ mem_univ z) hz
  -- Images of `Z₁` and `Z₂` under `ψ`.
  have hψZ₁ : ψ '' Z₁ = D := by
    apply Subset.antisymm
    · calc ψ '' Z₁ ⊆ closure (ψ '' U₁) := image_closure_subset_closure_image hψ.1
        _ = closure (D \ A) := by rw [image_preimage_eq _ hψ.2.1]
        _ = D := hcl_DA_eq
    · rw [← hcl_DA_eq]
      refine closure_minimal ?_ (hZ₁_clopen.isClosed.isCompact.image hψ.1).isClosed
      rw [← image_preimage_eq (D \ A) hψ.2.1]
      exact image_mono subset_closure
  have hψZ₂ : ψ '' Z₂ = (D \ A)ᶜ := by
    apply Subset.antisymm
    · calc ψ '' Z₂ ⊆ closure (ψ '' U₂) := image_closure_subset_closure_image hψ.1
        _ = closure Dᶜ := by rw [image_preimage_eq _ hψ.2.1]
        _ = (D \ A)ᶜ := hcl_Dc_eq
    · rw [← hcl_Dc_eq]
      refine closure_minimal ?_ (hZ₂_clopen.isClosed.isCompact.image hψ.1).isClosed
      rw [← image_preimage_eq Dᶜ hψ.2.1]
      exact image_mono subset_closure
  -- Step 3: Call `cut_comps` + `arc_comps_aux` to identify `W₁, W₂` and their models!
  have hXb : X ⊆ bd Y := fun z hz => hψ.2.2.2.2 (hun ▸ Or.inl hz)
  have hXb' : X' ⊆ bd Y := fun z hz => hψ.2.2.2.2 (hun ▸ Or.inr hz)
  have pX : IsPreconnected X := himξ ▸ isPreconnected_Icc.image _ L.cξ
  have pX' : IsPreconnected X' := himη ▸ isPreconnected_Icc.image _ L.cη
  have hex : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have hx : ξ 0 ∈ X := himξ ▸ ⟨0, hex, rfl⟩
  have hy : η 0 ∈ X' := himη ▸ ⟨0, hex, rfl⟩
  rcases cut_comps hψ hY pX pX' hun hx hy with hYc | ⟨W₁, W₂, -, -, hX₁, hX₂, hW₁, hW₂, hWU, hdW, hc₁, hc₂⟩
  · exact absurd hYc hnotc
  -- Since `X ⊆ W₁`, `X' ⊆ W₂` and `W₁, W₂` are connected while `Z₁, Z₂` are clopen,
  -- each `Wᵢ` lies in `Z₁` or `Z₂`, and since both `Z₁, Z₂` are nonempty, `{W₁, W₂} = {Z₁, Z₂}`!
  have hW_in_Z : ∀ W : Set Y, ConnectedSpace W → W ⊆ Z₁ ∨ W ⊆ Z₂ := fun W hWc => by
    have hWp : IsPreconnected W := (isConnected_iff_connectedSpace.mpr hWc).isPreconnected
    by_cases h1 : (W ∩ Z₁).Nonempty
    · left
      intro w hw
      by_contra hw1
      have hw2 : w ∈ Z₂ := ((mem_union _ _ _).mp (hZ₁₂_union.symm ▸ mem_univ w)).resolve_left hw1
      obtain ⟨u, -, hu1, hu2⟩ := hWp Z₁ Z₂ hZ₁_clopen.isOpen hZ₂_clopen.isOpen
        (fun _ _ => hZ₁₂_union.symm ▸ mem_univ _) h1 ⟨w, hw, hw2⟩
      exact Set.disjoint_left.mp hZ₁₂_disj hu1 hu2
    · right
      intro w hw
      exact ((mem_union _ _ _).mp (hZ₁₂_union.symm ▸ mem_univ w)).resolve_left fun hw1 =>
        h1 ⟨w, hw, hw1⟩
  -- Moreover `Z₁` and `Z₂` each contain exactly one of `X, X'`, hence `ψ` is injective on `Z₁` and `Z₂`!
  have hX_split : (W₁ = Z₁ ∧ W₂ = Z₂) ∨ (W₁ = Z₂ ∧ W₂ = Z₁) := by
    rcases hW_in_Z W₁ hc₁ with h11 | h12 <;> rcases hW_in_Z W₂ hc₂ with h21 | h22
    · -- Both in `Z₁`: impossible since `W₁ ∪ W₂ = univ` and `Z₂.Nonempty`
      obtain ⟨z, hz⟩ := hZ₂_ne
      have hz1 : z ∈ Z₁ := by
        rcases (mem_union _ _ _).mp (hWU.symm ▸ mem_univ z) with h | h
        · exact h11 h
        · exact h21 h
      exact (Set.disjoint_left.mp hZ₁₂_disj hz1 hz).elim
    · left
      refine ⟨Subset.antisymm h11 fun z hz => ?_, Subset.antisymm h22 fun z hz => ?_⟩
      · exact ((mem_union _ _ _).mp (hWU.symm ▸ mem_univ z)).resolve_right fun h =>
          Set.disjoint_left.mp hZ₁₂_disj hz (h22 h)
      · exact ((mem_union _ _ _).mp (hWU.symm ▸ mem_univ z)).resolve_left fun h =>
          Set.disjoint_left.mp hZ₁₂_disj (h11 h) hz
    · right
      refine ⟨Subset.antisymm h12 fun z hz => ?_, Subset.antisymm h21 fun z hz => ?_⟩
      · exact ((mem_union _ _ _).mp (hWU.symm ▸ mem_univ z)).resolve_right fun h =>
          Set.disjoint_left.mp hZ₁₂_disj (h21 h) hz
      · exact ((mem_union _ _ _).mp (hWU.symm ▸ mem_univ z)).resolve_left fun h =>
          Set.disjoint_left.mp hZ₁₂_disj hz (h12 h)
    · obtain ⟨z, hz⟩ := hZ₁_ne
      have hz2 : z ∈ Z₂ := by
        rcases (mem_union _ _ _).mp (hWU.symm ▸ mem_univ z) with h | h
        · exact h12 h
        · exact h22 h
      exact (Set.disjoint_left.mp hZ₁₂_disj hz hz2).elim
  -- Helper: `ψ` is injective on `W₁` and `W₂` (since `W₁ ∩ (X ∪ X') = X` and `W₂ ∩ (X ∪ X') = X'`).
  have hinj_W₁ : InjOn ψ W₁ := fun u hu v hv huv => by
    by_cases huA : ψ u ∈ A
    · have hvA : ψ v ∈ A := huv ▸ huA
      have hu_pre : u ∈ X ∪ X' := hun ▸ huA
      have hv_pre : v ∈ X ∪ X' := hun ▸ hvA
      have huX : u ∈ X := hu_pre.resolve_right fun h => Set.disjoint_left.mp hdW hu (hX₂ h)
      have hvX : v ∈ X := hv_pre.resolve_right fun h => Set.disjoint_left.mp hdW hv (hX₂ h)
      exact hbx.2.1 huX hvX huv
    · have hvA : ψ v ∉ A := fun h => huA (huv.symm ▸ h)
      exact hψ.2.2.1 huA hvA huv
  have hinj_W₂ : InjOn ψ W₂ := fun u hu v hv huv => by
    by_cases huA : ψ u ∈ A
    · have hvA : ψ v ∈ A := huv ▸ huA
      have hu_pre : u ∈ X ∪ X' := hun ▸ huA
      have hv_pre : v ∈ X ∪ X' := hun ▸ hvA
      have huX : u ∈ X' := hu_pre.resolve_left fun h => Set.disjoint_left.mp hdW (hX₁ h) hu
      have hvX : v ∈ X' := hv_pre.resolve_left fun h => Set.disjoint_left.mp hdW (hX₁ h) hv
      exact hbx'.2.1 huX hvX huv
    · have hvA : ψ v ∉ A := fun h => huA (huv.symm ▸ h)
      exact hψ.2.2.1 huA hvA huv
  -- Classify `W₁` and `W₂` and apply `arc_comps_aux` + `homeo_of_two_arc` + `modelCriterion`.
  obtain ⟨a₁, b₁, c₁, ⟨e₁⟩⟩ := classification.{0} W₁ (isSurface_sub hY hW₁) hc₁
  obtain ⟨a₂, b₂, c₂, ⟨e₂⟩⟩ := classification.{0} W₂ (isSurface_sub hY hW₂) hc₂
  obtain ⟨i, j, σ, a', f, hi, hj, -, -, hf, -⟩ := arc_comps_aux hY L hψ.1 hψ.2.1 hW₁ hW₂ hdW hWU e₁ e₂
    (by rw [himξ]; exact hX₁) (by rw [himη]; exact hX₂) (by rw [himξ]; exact hXb) (by rw [himη]; exact hXb') hiξ hiη
  have : Nonempty S := ⟨s⟩
  obtain ⟨hN₁, hL₁⟩ := erase_facts c₁ i
  obtain ⟨hN₂, hL₂⟩ := erase_facts c₂ j
  obtain ⟨e_glue⟩ := homeo_of_two_arc hi hj hN₁ hN₂ hL₁ hL₂ hf
  have hlen₁ := length_erase_range hi
  have hlen₂ := length_erase_range hj
  obtain ⟨hc_eq, h2ab_eq, hb_iff⟩ :=
    (modelCriterion.2 (a₂ + a₁) (b₂ + b₁)
      (((List.range' 0 c₂).erase j).length + ((List.range' 0 c₁).erase i).length + 1) a b c).mp
      ⟨e_glue.symm.trans eS⟩
  -- Build a helper that builds a homeomorphism `W ≃ₜ T` from `InjOn ψ W` and `ψ '' W = T`.
  have mkHomeo : ∀ (W : Set Y) (T : Set S), IsClosed W → InjOn ψ W → ψ '' W = T →
      Nonempty (W ≃ₜ T) := fun W T hWcl hinj himg => by
    have : CompactSpace W := isCompact_iff_compactSpace.mp hWcl.isCompact
    let g : W → T := fun w => ⟨ψ w.1, himg ▸ mem_image_of_mem ψ w.2⟩
    have hg_cont : Continuous g := Continuous.subtype_mk (hψ.1.comp continuous_subtype_val) _
    have hg_bij : Function.Bijective g := by
      refine ⟨fun w₁ w₂ h => Subtype.ext (hinj w₁.2 w₂.2 (congrArg Subtype.val h)), fun y => ?_⟩
      have hy : y.1 ∈ ψ '' W := himg.symm ▸ y.2
      obtain ⟨w, hwW, hwy⟩ := hy
      exact ⟨⟨w, hwW⟩, Subtype.ext hwy⟩
    exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g hg_bij) hg_cont⟩
  -- Obtain `Z₁ ≃ₜ D` and `Z₂ ≃ₜ ↥(D \ A)ᶜ`, and compute `bd ↥(D \ A)ᶜ` and model type!
  obtain ⟨hZ₁_homeo, hZ₂_homeo, hsurf_Z₂, hconn_Z₂, hZ₂_model⟩ :
      Nonempty (Z₁ ≃ₜ D) ∧ Nonempty (Z₂ ≃ₜ ↥(D \ A)ᶜ) ∧
        IsSurface Z₂ ∧ ConnectedSpace Z₂ ∧ Nonempty (Z₂ ≃ₜ SurfaceModel a b c) := by
    obtain ⟨φD⟩ := id hD
    obtain ⟨eDisc⟩ := nonempty_disc_homeo
    have hD_model : Nonempty (D ≃ₜ SurfaceModel 0 0 1) := ⟨φD.symm.trans eDisc.symm⟩
    rcases hX_split with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1; subst h2
      obtain ⟨eD⟩ := mkHomeo Z₁ D hW₁.isClosed hinj_W₁ hψZ₁
      obtain ⟨eSub⟩ := mkHomeo Z₂ (D \ A)ᶜ hW₂.isClosed hinj_W₂ hψZ₂
      obtain ⟨eD0⟩ := hD_model
      obtain ⟨hc1, h2ab1, hb1⟩ := (modelCriterion.2 a₁ b₁ c₁ 0 0 1).mp ⟨e₁.symm.trans (eD.trans eD0)⟩
      have hb1_zero : b₁ = 0 := hb1.mpr rfl
      have ha1_zero : a₁ = 0 := by omega
      have hc2_eq : c₂ = c := by omega
      have h2ab2_eq : 2 * a₂ + b₂ = 2 * a + b := by omega
      have hb2_iff : b₂ = 0 ↔ b = 0 := by
        have : b₂ + b₁ = 0 ↔ b₂ = 0 := by omega
        exact this.symm.trans hb_iff
      obtain ⟨em₂⟩ := (modelCriterion.2 a₂ b₂ c₂ a b c).mpr ⟨hc2_eq, h2ab2_eq, hb2_iff⟩
      exact ⟨⟨eD⟩, ⟨eSub⟩, isSurface_sub hY hW₂, hc₂, ⟨e₂.trans em₂⟩⟩
    · subst h1; subst h2
      obtain ⟨eD⟩ := mkHomeo Z₁ D hW₂.isClosed hinj_W₂ hψZ₁
      obtain ⟨eSub⟩ := mkHomeo Z₂ (D \ A)ᶜ hW₁.isClosed hinj_W₁ hψZ₂
      obtain ⟨eD0⟩ := hD_model
      obtain ⟨hc2, h2ab2, hb2⟩ := (modelCriterion.2 a₂ b₂ c₂ 0 0 1).mp ⟨e₂.symm.trans (eD.trans eD0)⟩
      have hb2_zero : b₂ = 0 := hb2.mpr rfl
      have ha2_zero : a₂ = 0 := by omega
      have hc1_eq : c₁ = c := by omega
      have h2ab1_eq : 2 * a₁ + b₁ = 2 * a + b := by omega
      have hb1_iff : b₁ = 0 ↔ b = 0 := by
        have : b₂ + b₁ = 0 ↔ b₁ = 0 := by omega
        exact this.symm.trans hb_iff
      obtain ⟨em₁⟩ := (modelCriterion.2 a₁ b₁ c₁ a b c).mpr ⟨hc1_eq, h2ab1_eq, hb1_iff⟩
      exact ⟨⟨eD⟩, ⟨eSub⟩, isSurface_sub hY hW₁, hc₁, ⟨e₁.trans em₁⟩⟩
  -- Transport surface, connectedness, and model across `eSub : Z₂ ≃ₜ ↥(D \ A)ᶜ`.
  obtain ⟨eSub⟩ := hZ₂_homeo
  obtain ⟨eZ₂m⟩ := hZ₂_model
  have hsurf_sub : IsSurface ↥(D \ A)ᶜ := isSurface_of_homeo eSub hsurf_Z₂
  have hconn_sub : ConnectedSpace ↥(D \ A)ᶜ := eSub.surjective.connectedSpace eSub.continuous
  -- Compute `bd ↥(D \ A)ᶜ = Subtype.val ⁻¹' (bd S ∪ A)`.
  have hbd_sub : bd ↥(D \ A)ᶜ = Subtype.val ⁻¹' (bd S ∪ A) := by
    -- Build the explicit homeomorphism `gSub : Z₂ ≃ₜ ↥(D \ A)ᶜ` given by `ψ`.
    have hinj_Z₂ : InjOn ψ Z₂ := by
      rcases hX_split with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact h2 ▸ hinj_W₂
      · exact h1 ▸ hinj_W₁
    have : CompactSpace Z₂ := isCompact_iff_compactSpace.mp hZ₂_clopen.isClosed.isCompact
    let g_fn : Z₂ → ↥(D \ A)ᶜ := fun w => ⟨ψ w.1, hψZ₂ ▸ mem_image_of_mem ψ w.2⟩
    have hg_bij : Function.Bijective g_fn := by
      refine ⟨fun w₁ w₂ h => Subtype.ext (hinj_Z₂ w₁.2 w₂.2 (congrArg Subtype.val h)), fun y => ?_⟩
      have hy : y.1 ∈ ψ '' Z₂ := hψZ₂.symm ▸ y.2
      obtain ⟨w, hwZ, hwy⟩ := hy
      exact ⟨⟨w, hwZ⟩, Subtype.ext hwy⟩
    let gSub : Z₂ ≃ₜ ↥(D \ A)ᶜ :=
      Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g_fn hg_bij)
        (Continuous.subtype_mk (hψ.1.comp continuous_subtype_val) _)
    ext x
    by_cases hxA : x.1 ∈ A
    · refine ⟨fun _ => Or.inr hxA, fun _ => ?_⟩
      let w : Z₂ := gSub.symm x
      have hψw : ψ w.1 = x.1 := congrArg Subtype.val (gSub.apply_symm_apply x)
      have hwA : ψ w.1 ∈ A := hψw.symm ▸ hxA
      have hw_bdY : w.1 ∈ bd Y := hψ.2.2.2.2 hwA
      have hw_bdZ₂ : w ∈ bd Z₂ := fun hint =>
        hw_bdY ((isInteriorPoint_sub hZ₂_clopen.isOpen (x := w)).mp hint)
      rw [← image_bd_homeomorph gSub]
      exact ⟨w, hw_bdZ₂, gSub.apply_symm_apply x⟩
    · have hxDc : x.1 ∈ Dᶜ := fun hxD => x.2 ⟨hxD, hxA⟩
      have hDc_sub : Dᶜ ⊆ (D \ A)ᶜ := fun z hz h => hz h.1
      have hloc := (sub_open_iff hD.isClosed.isOpen_compl hDc_sub hxDc).1
      constructor
      · intro hxbd
        exact Or.inl fun hint => hxbd (hloc.mpr hint)
      · rintro (hxbdS | h)
        · exact fun hint => hxbdS (hloc.mp hint)
        · exact absurd h hxA
  exact ⟨hcl, hsurf_sub, hconn_sub, hbd_sub, ⟨eSub.symm.trans eZ₂m⟩⟩

/-- Cutting off `q` pairwise disjoint boundary closed discs `D : Fin q → Set S` along proper
`I`-arcs `A : Fin q → Set S` preserves the model type `SurfaceModel a b c`. -/
theorem cut_off_discs_model {S : Type} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsSurface S) {a b c : ℕ} (eS : S ≃ₜ SurfaceModel a b c)
    {q : ℕ} {D A : Fin q → Set S} {s t : Fin q → S}
    (hD : ∀ i, IsClosedDisc (D i))
    (hDdisj : Pairwise fun i j => Disjoint (D i) (D j))
    (hA_sub : ∀ i, A i ⊆ discBd (D i))
    (hst : ∀ i, s i ≠ t i)
    (hAb : ∀ i, A i ∩ bd S = {s i, t i})
    (hAl : ∀ i, IsLineWithEnds (A i) (s i) (t i))
    (hopen : ∀ i, IsOpen (D i \ A i)) :
    IsClosed (⋃ i : Fin q, D i \ A i)ᶜ ∧
      IsSurface ↥(⋃ i : Fin q, D i \ A i)ᶜ ∧
      ConnectedSpace ↥(⋃ i : Fin q, D i \ A i)ᶜ ∧
      bd ↥(⋃ i : Fin q, D i \ A i)ᶜ = Subtype.val ⁻¹' (bd S ∪ ⋃ i : Fin q, A i) ∧
      Nonempty (↥(⋃ i : Fin q, D i \ A i)ᶜ ≃ₜ SurfaceModel a b c) := by
  induction q with
  | zero =>
    have hun : (⋃ i : Fin 0, D i \ A i)ᶜ = (univ : Set S) := by simp
    let eU : ↥(⋃ i : Fin 0, D i \ A i)ᶜ ≃ₜ S :=
      (Homeomorph.setCongr hun).trans (Homeomorph.Set.univ S)
    have hsurf : IsSurface ↥(⋃ i : Fin 0, D i \ A i)ᶜ := isSurface_of_homeo eU.symm hS
    have hconn : ConnectedSpace ↥(⋃ i : Fin 0, D i \ A i)ᶜ :=
      eU.symm.surjective.connectedSpace eU.symm.continuous
    have hbd : bd ↥(⋃ i : Fin 0, D i \ A i)ᶜ =
        Subtype.val ⁻¹' (bd S ∪ ⋃ i : Fin 0, A i) := by
      ext x
      have h1 : x ∈ bd ↥(⋃ i : Fin 0, D i \ A i)ᶜ ↔ eU x ∈ bd S := by
        rw [← image_bd_homeomorph eU]
        exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, he⟩ => eU.injective he ▸ hy⟩
      have hval : eU x = x.1 := rfl
      simp [h1, hval]
    exact ⟨hun ▸ isClosed_univ, hsurf, hconn, hbd, ⟨eU.trans eS⟩⟩
  | succ q ih =>
    have ht2S : T2Space S := hS.2.1
    obtain ⟨hcl₁, hsurf₁, hconn₁, hbd₁, ⟨e₁⟩⟩ := ih
      (fun i => hD i.castSucc)
      (fun i j hij => hDdisj (Fin.castSucc_injective q |>.ne hij))
      (fun i => hA_sub i.castSucc)
      (fun i => hst i.castSucc)
      (fun i => hAb i.castSucc)
      (fun i => hAl i.castSucc)
      (fun i => hopen i.castSucc)
    let S₁ := ↥(⋃ i : Fin q, D i.castSucc \ A i.castSucc)ᶜ
    have hce₁ : IsClosedEmbedding (Subtype.val : S₁ → S) := hcl₁.isClosedEmbedding_subtypeVal
    have hcS₁ : CompactSpace S₁ := hsurf₁.1
    have ht2S₁ : T2Space S₁ := hsurf₁.2.1
    have hneS₁ : Nonempty S₁ := hconn₁.toNonempty
    have hlast_sub : D (Fin.last q) ⊆ range (Subtype.val : S₁ → S) := by
      rw [Subtype.range_val]
      intro z hz hmem
      obtain ⟨i, hi⟩ := mem_iUnion.mp hmem
      exact Set.disjoint_left.mp (hDdisj (Fin.castSucc_ne_last i)) hi.1 hz
    obtain ⟨hD₁, hD₁bd⟩ := isClosedDisc_preimage hce₁ (hD (Fin.last q)) hlast_sub
    let D₁ : Set S₁ := Subtype.val ⁻¹' D (Fin.last q)
    let A₁ : Set S₁ := Subtype.val ⁻¹' A (Fin.last q)
    have hA_in_D : A (Fin.last q) ⊆ D (Fin.last q) := (hA_sub (Fin.last q)).trans (discBd_subset _)
    have hs_mem : s (Fin.last q) ∈ (⋃ i : Fin q, D i.castSucc \ A i.castSucc)ᶜ := by
      have hsA : s (Fin.last q) ∈ A (Fin.last q) := by
        have : s (Fin.last q) ∈ ({s (Fin.last q), t (Fin.last q)} : Set S) := Or.inl rfl
        rw [← hAb (Fin.last q)] at this
        exact this.1
      exact Subtype.range_val (s := (⋃ i : Fin q, D i.castSucc \ A i.castSucc)ᶜ) ▸
        hlast_sub (hA_in_D hsA)
    have ht_mem : t (Fin.last q) ∈ (⋃ i : Fin q, D i.castSucc \ A i.castSucc)ᶜ := by
      have htA : t (Fin.last q) ∈ A (Fin.last q) := by
        have : t (Fin.last q) ∈ ({s (Fin.last q), t (Fin.last q)} : Set S) := Or.inr rfl
        rw [← hAb (Fin.last q)] at this
        exact this.1
      exact Subtype.range_val (s := (⋃ i : Fin q, D i.castSucc \ A i.castSucc)ᶜ) ▸
        hlast_sub (hA_in_D htA)
    let s₁ : S₁ := ⟨s (Fin.last q), hs_mem⟩
    let t₁ : S₁ := ⟨t (Fin.last q), ht_mem⟩
    have hst₁ : s₁ ≠ t₁ := fun h => hst (Fin.last q) (congrArg Subtype.val h)
    have hA₁_sub : A₁ ⊆ discBd D₁ := by
      rw [hD₁bd]; exact preimage_mono (hA_sub (Fin.last q))
    have hA₁b : A₁ ∩ bd S₁ = {s₁, t₁} := by
      rw [hbd₁]
      ext x
      simp only [A₁, mem_inter_iff, mem_preimage, mem_union, mem_iUnion, mem_insert_iff,
        mem_singleton_iff]
      constructor
      · rintro ⟨hxA, hxbd | ⟨i, hxi⟩⟩
        · have hst' : x.1 ∈ ({s (Fin.last q), t (Fin.last q)} : Set S) := by
            rw [← hAb (Fin.last q)]; exact ⟨hxA, hxbd⟩
          rcases hst' with h | h
          · exact Or.inl (Subtype.ext h)
          · exact Or.inr (Subtype.ext h)
        · exact (Set.disjoint_left.mp (hDdisj (Fin.castSucc_ne_last i))
            ((hA_sub i.castSucc).trans (discBd_subset _) hxi) (hA_in_D hxA)).elim
      · intro h
        have hst' : x.1 ∈ ({s (Fin.last q), t (Fin.last q)} : Set S) := by
          rcases h with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
        rw [← hAb (Fin.last q)] at hst'
        exact ⟨hst'.1, Or.inl hst'.2⟩
    have hA₁l : IsLineWithEnds A₁ s₁ t₁ := by
      obtain ⟨f, hf0, hf1⟩ := hAl (Fin.last q)
      have hf_in : ∀ u : unitInterval, (f u).1 ∈ (⋃ i : Fin q, D i.castSucc \ A i.castSucc)ᶜ :=
        fun u => Subtype.range_val (s := (⋃ i : Fin q, D i.castSucc \ A i.castSucc)ᶜ) ▸
          hlast_sub (hA_in_D (f u).2)
      let g : unitInterval ≃ₜ A₁ :=
        { toFun := fun u => ⟨⟨(f u).1, hf_in u⟩, (f u).2⟩
          invFun := fun x => f.symm ⟨x.1.1, x.2⟩
          left_inv := fun u => by simp
          right_inv := fun x => by ext; simp
          continuous_toFun := Continuous.subtype_mk
            (Continuous.subtype_mk (continuous_subtype_val.comp f.continuous) _) _
          continuous_invFun := f.symm.continuous.comp
            (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _) }
      exact ⟨g, Subtype.ext hf0, Subtype.ext hf1⟩
    have hopen₁ : IsOpen (D₁ \ A₁) := by
      have : D₁ \ A₁ = Subtype.val ⁻¹' (D (Fin.last q) \ A (Fin.last q)) := rfl
      rw [this]
      exact (hopen (Fin.last q)).preimage continuous_subtype_val
    obtain ⟨hcl₂, hsurf₂, hconn₂, hbd₂, ⟨e₂⟩⟩ :=
      cut_off_disc_model hsurf₁ e₁ hD₁ hA₁_sub hst₁ hA₁b hA₁l hopen₁
    have hcov_eq : ∀ z : S,
        z ∈ (⋃ i : Fin (q + 1), D i \ A i)ᶜ ↔
          ∃ h : z ∈ (⋃ i : Fin q, D i.castSucc \ A i.castSucc)ᶜ, (⟨z, h⟩ : S₁) ∈ (D₁ \ A₁)ᶜ := by
      intro z
      simp only [mem_compl_iff, mem_iUnion, not_exists, D₁, A₁, Set.mem_sdiff, mem_preimage]
      constructor
      · intro hz
        exact ⟨fun i => hz i.castSucc, hz (Fin.last q)⟩
      · rintro ⟨h1, h2⟩ i
        exact Fin.lastCases h2 h1 i
    let e_iso : ↥(D₁ \ A₁)ᶜ ≃ₜ ↥(⋃ i : Fin (q + 1), D i \ A i)ᶜ :=
      { toFun := fun x => ⟨x.1.1, (hcov_eq x.1.1).mpr ⟨x.1.2, x.2⟩⟩
        invFun := fun y => ⟨⟨y.1, ((hcov_eq y.1).mp y.2).1⟩, ((hcov_eq y.1).mp y.2).2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        continuous_toFun := Continuous.subtype_mk
          (continuous_subtype_val.comp continuous_subtype_val) _
        continuous_invFun := Continuous.subtype_mk
          (Continuous.subtype_mk continuous_subtype_val _) _ }
    have hcl_fin : IsClosed (⋃ i : Fin (q + 1), D i \ A i)ᶜ := by
      rw [isClosed_compl_iff]
      exact isOpen_iUnion hopen
    have hsurf_fin : IsSurface ↥(⋃ i : Fin (q + 1), D i \ A i)ᶜ :=
      isSurface_of_homeo e_iso hsurf₂
    have hconn_fin : ConnectedSpace ↥(⋃ i : Fin (q + 1), D i \ A i)ᶜ :=
      e_iso.surjective.connectedSpace e_iso.continuous
    have hbd_fin : bd ↥(⋃ i : Fin (q + 1), D i \ A i)ᶜ =
        Subtype.val ⁻¹' (bd S ∪ ⋃ i : Fin (q + 1), A i) := by
      ext y
      have h1 : y ∈ bd ↥(⋃ i : Fin (q + 1), D i \ A i)ᶜ ↔ e_iso.symm y ∈ bd ↥(D₁ \ A₁)ᶜ := by
        rw [← image_bd_homeomorph e_iso.symm]
        exact ⟨fun hy => ⟨y, hy, rfl⟩, fun ⟨z, hz, he⟩ => e_iso.symm.injective he ▸ hz⟩
      rw [h1, hbd₂, mem_preimage, mem_union, hbd₁]
      change (y.1 ∈ bd S ∪ ⋃ i : Fin q, A i.castSucc) ∨ y.1 ∈ A (Fin.last q) ↔
        y.1 ∈ bd S ∪ ⋃ i : Fin (q + 1), A i
      simp only [mem_union, mem_iUnion]
      constructor
      · rintro ((h | ⟨i, hi⟩) | hlast)
        · exact Or.inl h
        · exact Or.inr ⟨i.castSucc, hi⟩
        · exact Or.inr ⟨Fin.last q, hlast⟩
      · rintro (h | ⟨i, hi⟩)
        · exact Or.inl (Or.inl h)
        · exact Fin.lastCases (motive := fun i => y.1 ∈ A i → _)
            (fun h => Or.inr h) (fun j h => Or.inl (Or.inr ⟨j, h⟩)) i hi
    exact ⟨hcl_fin, hsurf_fin, hconn_fin, hbd_fin, ⟨e_iso.symm.trans e₂⟩⟩

/-! ### Section 4: Converting a matching drawing to a family of proper `I`-arcs -/

/-- A matching `G` with `G.V.ncard ≤ 2 * n` decomposes into `n' ≤ n` pairwise disjoint proper
`I`-arcs `G_arc : Fin n' → Set S` whose union is `G.U` and whose boundary endpoints form `G.V`. -/
theorem drawing_matching_to_family {S : Type} [TopologicalSpace S] (hS : IsSurface S)
    {n : ℕ} {G : Drawing S} (hG : IsMatching G) (hGcard : G.V.ncard ≤ 2 * n) :
    ∃ (n' : ℕ) (_ : n' ≤ n) (G_arc : Fin n' → Set S),
      (∀ j, ∃ s t, s ≠ t ∧ IsLineWithEnds (G_arc j) s t ∧ G_arc j ∩ bd S = {s, t}) ∧
      (Pairwise fun j₁ j₂ => Disjoint (G_arc j₁) (G_arc j₂)) ∧
      G.U = ⋃ j, G_arc j ∧
      G.V = ⋃ j, (G_arc j ∩ bd S) := by
  classical
  have ht2S : T2Space S := hS.2.1
  rcases hG with ⟨hprop, hV_bd, hval⟩
  -- Handshaking: `G.V.ncard = 2 * G.E.ncard`, so `G.E.ncard ≤ n`.
  have hsum := sum_vertexValency_eq_two_mul_ncard_E G
  have hsum_V : ∑ v ∈ G.finite_V.toFinset, vertexValency G v = G.V.ncard := by
    calc ∑ v ∈ G.finite_V.toFinset, vertexValency G v
        = ∑ v ∈ G.finite_V.toFinset, 1 := Finset.sum_congr rfl fun v hv =>
            hval v (G.finite_V.mem_toFinset.mp hv)
      _ = G.finite_V.toFinset.card := by simp
      _ = G.V.ncard := by
            rw [← ncard_coe_finset]
            congr 1; ext v; exact G.finite_V.mem_toFinset
  have hn' : G.E.ncard ≤ n := by omega
  let E_fin := G.finite_edges.toFinset
  have hE_card : E_fin.card = G.E.ncard := by
    rw [← ncard_coe_finset]; congr 1; ext e; exact G.finite_edges.mem_toFinset
  let eFin : Fin G.E.ncard ≃ E_fin := (finCongr hE_card.symm).trans (Finset.equivFin E_fin).symm
  let G_arc : Fin G.E.ncard → Set S := fun j => closure (eFin j).1
  have hmemE : ∀ j, (eFin j).1 ∈ G.E := fun j => G.finite_edges.mem_toFinset.mp (eFin j).2
  -- No edge is a loop, since every vertex has valency `1 < 2`.
  have hno_loop : ∀ e ∈ G.E, (tilde e).ncard = 2 := fun e he => by
    rcases ncard_tilde_of_mem_E G he with h2 | h1
    · exact h2
    · exfalso
      have htilde_eq := tilde_eq_closure_inter_V G he
      obtain ⟨u, hu⟩ : (tilde e).Nonempty := by
        by_contra hemp
        rw [Set.not_nonempty_iff_eq_empty] at hemp
        rw [hemp, ncard_empty] at h1
        omega
      have huV : u ∈ G.V := (htilde_eq ▸ hu).2
      have hinc : G.VertexIncident u e := (vertexIncident_iff_mem_tilde G huV he).mpr hu
      have hfin1 : {e' ∈ G.E | G.VertexIncident u e' ∧ (tilde e').ncard = 1}.Finite :=
        G.finite_edges.subset fun e' h => h.1
      have hpos1 : 1 ≤ {e' ∈ G.E | G.VertexIncident u e' ∧ (tilde e').ncard = 1}.ncard :=
        Set.ncard_pos hfin1 |>.mpr ⟨e, he, hinc, h1⟩
      have hv1 := hval u huV
      unfold vertexValency at hv1
      omega
  -- Every vertex `v ∈ G.V` has a unique incident edge `e ∈ G.E`.
  have hinc_uniq : ∀ v ∈ G.V, ∀ e₁ ∈ G.E, ∀ e₂ ∈ G.E,
      v ∈ closure e₁ → v ∈ closure e₂ → e₁ = e₂ := fun v hv e₁ he₁ e₂ he₂ hv1 hv2 => by
    by_contra hne
    have hfin2 : {e' ∈ G.E | G.VertexIncident v e' ∧ (tilde e').ncard = 2}.Finite :=
      G.finite_edges.subset fun e' h => h.1
    have hsub2 : ({e₁, e₂} : Set (Set S)) ⊆ {e' ∈ G.E | G.VertexIncident v e' ∧ (tilde e').ncard = 2} := by
      rintro e (rfl | rfl)
      · exact ⟨he₁, ⟨hv, Or.inl he₁, hv1⟩, hno_loop e he₁⟩
      · exact ⟨he₂, ⟨hv, Or.inl he₂, hv2⟩, hno_loop e he₂⟩
    have hcard2 : 2 ≤ {e' ∈ G.E | G.VertexIncident v e' ∧ (tilde e').ncard = 2}.ncard :=
      calc 2 = ({e₁, e₂} : Set (Set S)).ncard := (ncard_pair hne).symm
        _ ≤ {e' ∈ G.E | G.VertexIncident v e' ∧ (tilde e').ncard = 2}.ncard :=
          Set.ncard_le_ncard hsub2 hfin2
    have hv1 := hval v hv
    unfold vertexValency at hv1
    omega
  have hex_inc : ∀ v ∈ G.V, ∃ e ∈ G.E, v ∈ closure e := fun v hv => by
    have hv1 := hval v hv
    unfold vertexValency at hv1
    have hpos : 0 < {e' ∈ G.E | G.VertexIncident v e' ∧ (tilde e').ncard = 2}.ncard := by
      by_contra h0
      have hz : {e' ∈ G.E | G.VertexIncident v e' ∧ (tilde e').ncard = 2}.ncard = 0 := by omega
      omega
    have hfin2 : {e' ∈ G.E | G.VertexIncident v e' ∧ (tilde e').ncard = 2}.Finite :=
      G.finite_edges.subset fun e' h => h.1
    obtain ⟨e, he, hinc, -⟩ := (Set.ncard_pos hfin2).mp hpos
    exact ⟨e, he, hinc.2.2⟩
  -- Each `G_arc j` is a proper `I`-arc with `G_arc j ∩ bd S = G_arc j ∩ G.V = {s, t}`.
  have hG_arc : ∀ j, ∃ s t, s ≠ t ∧ IsLineWithEnds (G_arc j) s t ∧
      G_arc j ∩ G.V = {s, t} ∧ G_arc j ∩ bd S = {s, t} := fun j => by
    have he := hmemE j
    rcases G.edge_cond _ he with ⟨s, t, hst, hcap, hline⟩ | ⟨u, hcap, -⟩
    · refine ⟨s, t, hst, hline, hcap, ?_⟩
      apply Subset.antisymm
      · intro x ⟨hxcl, hxbd⟩
        have hxU : x ∈ G.U :=
          closure_minimal (fun z hz => (he.2.1 hz).1) G.isClosed_U hxcl
        have hxV : x ∈ G.V := hprop ⟨hxbd, hxU⟩
        exact hcap ▸ ⟨hxcl, hxV⟩
      · rw [← hcap]
        exact inter_subset_inter_right _ hV_bd
    · exfalso
      have h1 := hno_loop _ he
      rw [tilde_eq_closure_inter_V G he, hcap, ncard_singleton] at h1
      omega
  -- For each `e ∈ G.E`, `closure e \ G.V = e`.
  have hcl_diff_V : ∀ j, G_arc j \ G.V = (eFin j).1 := fun j => by
    have he := hmemE j
    obtain ⟨s, t, hst, hline, hcap, -⟩ := hG_arc j
    have he_sub_cl : (eFin j).1 ⊆ G_arc j \ G.V := fun z hz =>
      ⟨subset_closure hz, (he.2.1 hz).2⟩
    have hdiff_eq : G_arc j \ G.V = G_arc j \ {s, t} := by
      ext z; simp only [Set.mem_sdiff]; constructor
      · rintro ⟨hz, hzV⟩; exact ⟨hz, fun h => hzV (hcap ▸ h).2⟩
      · rintro ⟨hz, hzs⟩; exact ⟨hz, fun hzV => hzs (hcap ▸ ⟨hz, hzV⟩)⟩
    have hdiff_sub : G_arc j \ G.V ⊆ G.U \ G.V := fun z ⟨hzcl, hzV⟩ =>
      ⟨closure_minimal (fun w hw => (he.2.1 hw).1) G.isClosed_U hzcl, hzV⟩
    have hdiff_pc : IsPathConnected (G_arc j \ G.V) := by
      rw [hdiff_eq]
      obtain ⟨f, hf0, hf1⟩ := hline
      let J : Set unitInterval := {u : unitInterval | 0 < (u : ℝ) ∧ (u : ℝ) < 1}
      have hJ_pc : IsPathConnected J := by
        refine ⟨⟨1 / 2, by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, fun u hu => ?_⟩
        refine ⟨⟨⟨fun τ => ⟨(1 - (τ : ℝ)) * (1 / 2) + (τ : ℝ) * (u : ℝ),
          by nlinarith [τ.2.1, τ.2.2, u.2.1, u.2.2], by nlinarith [τ.2.1, τ.2.2, u.2.1, u.2.2]⟩,
          Continuous.subtype_mk (by fun_prop) _⟩,
          by ext; simp, by ext; simp⟩, fun τ => ?_⟩
        show 0 < (1 - (τ : ℝ)) * (1 / 2) + (τ : ℝ) * (u : ℝ) ∧
          (1 - (τ : ℝ)) * (1 / 2) + (τ : ℝ) * (u : ℝ) < 1
        have hτ0 : 0 ≤ (τ : ℝ) := τ.2.1
        have hτ1 : (τ : ℝ) ≤ 1 := τ.2.2
        have hu1 : 0 < (u : ℝ) := hu.1
        have hu2 : (u : ℝ) < 1 := hu.2
        rcases eq_or_lt_of_le hτ0 with h0 | h0
        · rw [← h0]; norm_num
        · exact ⟨by nlinarith, by nlinarith⟩
      have himg : (fun u : unitInterval => (f u).1) '' J = G_arc j \ {s, t} := by
        ext z
        constructor
        · rintro ⟨u, hu, rfl⟩
          refine ⟨(f u).2, ?_⟩
          rintro (h | h)
          · have := congrArg Subtype.val (f.injective (Subtype.ext (h.trans hf0.symm)))
            exact hu.1.ne' this
          · have := congrArg Subtype.val (f.injective (Subtype.ext (h.trans hf1.symm)))
            exact hu.2.ne this
        · rintro ⟨hz, hzst⟩
          let u := f.symm ⟨z, hz⟩
          have hu0 : u ≠ 0 := fun h => hzst (Or.inl (by
            have : f u = f 0 := congrArg f h
            simpa [u, hf0] using congrArg Subtype.val this))
          have hu1 : u ≠ 1 := fun h => hzst (Or.inr (by
            have : f u = f 1 := congrArg f h
            simpa [u, hf1] using congrArg Subtype.val this))
          refine ⟨u, ⟨lt_of_le_of_ne u.2.1 fun h => hu0 (Subtype.ext h.symm),
            lt_of_le_of_ne u.2.2 fun h => hu1 (Subtype.ext h)⟩, ?_⟩
          exact congrArg Subtype.val (f.apply_symm_apply ⟨z, hz⟩)
      rw [← himg]
      exact hJ_pc.image (continuous_subtype_val.comp f.continuous)
    exact he.2.2.2 (G_arc j \ G.V) hdiff_sub hdiff_pc he_sub_cl
  -- Pairwise disjointness of `G_arc`.
  have hdisj : Pairwise fun j₁ j₂ => Disjoint (G_arc j₁) (G_arc j₂) := by
    intro j₁ j₂ hne
    rw [Set.disjoint_left]
    intro x hx1 hx2
    by_cases hxV : x ∈ G.V
    · have heq := hinc_uniq x hxV _ (hmemE j₁) _ (hmemE j₂) hx1 hx2
      exact hne (eFin.injective (Subtype.ext heq))
    · have hx1' : x ∈ (eFin j₁).1 := hcl_diff_V j₁ ▸ ⟨hx1, hxV⟩
      have hx2' : x ∈ (eFin j₂).1 := hcl_diff_V j₂ ▸ ⟨hx2, hxV⟩
      have hpc12 : IsPathConnected ((eFin j₁).1 ∪ (eFin j₂).1) := by
        refine ⟨x, Or.inl hx1', fun y hy => ?_⟩
        rcases hy with hy1 | hy2
        · exact ((hmemE j₁).2.2.1.joinedIn _ hx1' _ hy1).mono subset_union_left
        · exact ((hmemE j₂).2.2.1.joinedIn _ hx2' _ hy2).mono subset_union_right
      have hsub12 : (eFin j₁).1 ∪ (eFin j₂).1 ⊆ G.U \ G.V :=
        union_subset (hmemE j₁).2.1 (hmemE j₂).2.1
      have h1 : (eFin j₁).1 ∪ (eFin j₂).1 = (eFin j₁).1 :=
        (hmemE j₁).2.2.2 _ hsub12 hpc12 subset_union_left
      have h2 : (eFin j₁).1 ∪ (eFin j₂).1 = (eFin j₂).1 :=
        (hmemE j₂).2.2.2 _ hsub12 hpc12 subset_union_right
      exact hne (eFin.injective (Subtype.ext (h1.symm.trans h2)))
  -- `G.U = ⋃ j, G_arc j`.
  have hU_eq : G.U = ⋃ j, G_arc j := by
    apply Subset.antisymm
    · intro x hxU
      by_cases hxV : x ∈ G.V
      · obtain ⟨e, he, hxe⟩ := hex_inc x hxV
        let j : Fin G.E.ncard := eFin.symm ⟨e, G.finite_edges.mem_toFinset.mpr he⟩
        refine mem_iUnion.mpr ⟨j, ?_⟩
        simpa [G_arc, j] using hxe
      · have he : pathComponentIn (G.U \ G.V) x ∈ G.E :=
          pathComponentIn_mem_arcComponentsIn (⟨hxU, hxV⟩ : x ∈ G.U \ G.V)
        have hxe : x ∈ pathComponentIn (G.U \ G.V) x := mem_pathComponentIn_self ⟨hxU, hxV⟩
        let j : Fin G.E.ncard := eFin.symm ⟨_, G.finite_edges.mem_toFinset.mpr he⟩
        refine mem_iUnion.mpr ⟨j, ?_⟩
        have hsub : pathComponentIn (G.U \ G.V) x ⊆ closure (pathComponentIn (G.U \ G.V) x) :=
          subset_closure
        simpa [G_arc, j] using hsub hxe
    · exact iUnion_subset fun j =>
        closure_minimal (fun z hz => ((hmemE j).2.1 hz).1) G.isClosed_U
  -- `G.V = ⋃ j, (G_arc j ∩ bd S)`.
  have hV_eq : G.V = ⋃ j, (G_arc j ∩ bd S) := by
    apply Subset.antisymm
    · intro v hv
      obtain ⟨e, he, hve⟩ := hex_inc v hv
      let j : Fin G.E.ncard := eFin.symm ⟨e, G.finite_edges.mem_toFinset.mpr he⟩
      refine mem_iUnion.mpr ⟨j, ?_, hV_bd hv⟩
      simpa [G_arc, j] using hve
    · exact iUnion_subset fun j x ⟨hxcl, hxbd⟩ => by
        obtain ⟨s, t, -, -, hcapV, hcapB⟩ := hG_arc j
        have : x ∈ G_arc j ∩ G.V := by rw [hcapV, ← hcapB]; exact ⟨hxcl, hxbd⟩
        exact this.2
  exact ⟨G.E.ncard, hn', G_arc, fun j => by
    obtain ⟨s, t, hst, hl, -, hb⟩ := hG_arc j
    exact ⟨s, t, hst, hl, hb⟩, hdisj, hU_eq, hV_eq⟩

/-! ### Section 5: LPPS22 Theorem A.2 (star-forest crossing bound with excised hub discs) -/

/-- **Lokshtanov–Pilipczuk–Pilipczuk–Saurabh (2022), Appendix A, Theorem A.2** (excised-disc form):
On a connected surface `S ≃ₜ SurfaceModel a b c` with `1 ≤ c`, given a matching `G` with
`G.V.ncard ≤ 2 * n`, `p ≤ k` pairwise disjoint closed discs `Δ : Fin p → Set S` in `S \ (bd S ∪ G.U)`,
and `m ≤ 2 * k` pairwise disjoint proper `I`-arcs `L : Fin m → Set S` in `(⋃ l, discInt (Δ l))ᶜ`
whose boundary endpoints avoid `G.V`, there exists a homeomorphism `φ : S ≃ₜ S` fixing `bd S` and
every `Δ l` pointwise such that `G.U ∩ ⋃ i, φ '' L i` is finite and has cardinality at most
`2 * k * 3 ^ (2 * n + 3 * (2 * a + b) + c + k)`. -/
theorem lpps22_theorem_A_2 {S : Type} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsSurface S) {a b c k n p m : ℕ} (eS : S ≃ₜ SurfaceModel a b c)
    (hc : 1 ≤ c) (hp : p ≤ k) (hm : m ≤ 2 * k)
    {G : Drawing S} (hG : IsMatching G) (hGcard : G.V.ncard ≤ 2 * n)
    {Δ : Fin p → Set S}
    (hΔ : ∀ l, IsClosedDisc (Δ l))
    (hΔbd : ∀ l, Disjoint (Δ l) (bd S))
    (hΔdisj : Pairwise fun l₁ l₂ => Disjoint (Δ l₁) (Δ l₂))
    (hΔG : ∀ l, Disjoint (Δ l) G.U)
    {L : Fin m → Set S}
    (hL : ∀ i, ∃ u v, u ≠ v ∧ IsLineWithEnds (L i) u v ∧
      L i ∩ (bd S ∪ ⋃ l, discBd (Δ l)) = {u, v})
    (hLsub : ∀ i, L i ⊆ (⋃ l, discInt (Δ l))ᶜ)
    (hLdisj : Pairwise fun i₁ i₂ => Disjoint (L i₁) (L i₂))
    (hL_G : ∀ i, Disjoint (L i ∩ bd S) G.V) :
    ∃ φ : S ≃ₜ S,
      (∀ x ∈ bd S, φ x = x) ∧
      (∀ l, ∀ x ∈ Δ l, φ x = x) ∧
      (G.U ∩ ⋃ i, φ '' L i).Finite ∧
      (G.U ∩ ⋃ i, φ '' L i).ncard ≤ 2 * k * 3 ^ (2 * n + 3 * (2 * a + b) + c + k) := by
  classical
  have ht2S : T2Space S := hS.2.1
  -- Step 1: Excise the `p` interior discs `Δ`.
  obtain ⟨hcl_cut, hsurf_cut, hconn_cut, hbd_cut, ⟨e_cut⟩⟩ :=
    remove_discs_model hS eS hΔ hΔbd hΔdisj
  let S_cut := ↥(⋃ l : Fin p, discInt (Δ l))ᶜ
  -- Step 2: Convert `G` into `n' ≤ n` pairwise disjoint proper `I`-arcs and lift to `S_cut`.
  obtain ⟨n', hn', G_arc, hG_arc, hG_disj, hGU_eq, hGV_eq⟩ :=
    drawing_matching_to_family hS hG hGcard
  have hG_sub_cut : ∀ j, G_arc j ⊆ (⋃ l : Fin p, discInt (Δ l))ᶜ := fun j x hx hmem => by
    obtain ⟨l, hl⟩ := mem_iUnion.mp hmem
    exact Set.disjoint_left.mp (hΔG l) (discInt_subset _ hl) (hGU_eq.symm ▸ mem_iUnion.mpr ⟨j, hx⟩)
  let G_cut : Fin n' → Set S_cut := fun j => Subtype.val ⁻¹' G_arc j
  let L_cut : Fin m → Set S_cut := fun i => Subtype.val ⁻¹' L i
  -- Lift `IsLineWithEnds` from `S` to `S_cut` for any subset `A ⊆ (⋃ l, discInt (Δ l))ᶜ`.
  have lift_line : ∀ {A : Set S} {s t : S}, A ⊆ (⋃ l : Fin p, discInt (Δ l))ᶜ →
      s ≠ t → IsLineWithEnds A s t →
      ∃ hs ht, (⟨s, hs⟩ : S_cut) ≠ ⟨t, ht⟩ ∧
        IsLineWithEnds (Subtype.val ⁻¹' A : Set S_cut) ⟨s, hs⟩ ⟨t, ht⟩ := by
    intro A s t hAsub hst ⟨f, hf0, hf1⟩
    have hs : s ∈ (⋃ l : Fin p, discInt (Δ l))ᶜ := hAsub (hf0 ▸ (f 0).2)
    have ht : t ∈ (⋃ l : Fin p, discInt (Δ l))ᶜ := hAsub (hf1 ▸ (f 1).2)
    refine ⟨hs, ht, fun h => hst (congrArg Subtype.val h), ?_⟩
    let g : unitInterval ≃ₜ (Subtype.val ⁻¹' A : Set S_cut) :=
      { toFun := fun u => ⟨⟨(f u).1, hAsub (f u).2⟩, (f u).2⟩
        invFun := fun x => f.symm ⟨x.1.1, x.2⟩
        left_inv := fun u => by simp
        right_inv := fun x => by ext; simp
        continuous_toFun := Continuous.subtype_mk
          (Continuous.subtype_mk (continuous_subtype_val.comp f.continuous) _) _
        continuous_invFun := f.symm.continuous.comp
          (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _) }
    exact ⟨g, Subtype.ext hf0, Subtype.ext hf1⟩
  have hG_cut : ∀ j, ∃ s t : S_cut, s ≠ t ∧ IsLineWithEnds (G_cut j) s t ∧
      G_cut j ∩ bd S_cut = {s, t} := fun j => by
    obtain ⟨s, t, hst, hl, hbd⟩ := hG_arc j
    obtain ⟨hs, ht, hst', hl'⟩ := lift_line (hG_sub_cut j) hst hl
    refine ⟨⟨s, hs⟩, ⟨t, ht⟩, hst', hl', ?_⟩
    rw [hbd_cut]
    ext x
    simp only [G_cut, mem_inter_iff, mem_preimage, mem_union, mem_iUnion, mem_insert_iff,
      mem_singleton_iff]
    constructor
    · rintro ⟨hxG, hxbd | ⟨l, hxl⟩⟩
      · have hst' : x.1 ∈ ({s, t} : Set S) := hbd ▸ ⟨hxG, hxbd⟩
        rcases hst' with h | h
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Subtype.ext h)
      · exact (Set.disjoint_left.mp (hΔG l) (discBd_subset _ hxl)
          (hGU_eq.symm ▸ mem_iUnion.mpr ⟨j, hxG⟩)).elim
    · intro h
      have hst' : x.1 ∈ ({s, t} : Set S) := by
        rcases h with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      have hGbd : x.1 ∈ G_arc j ∩ bd S := hbd.symm ▸ hst'
      exact ⟨hGbd.1, Or.inl hGbd.2⟩
  have hG_cut_disj : Pairwise fun j₁ j₂ => Disjoint (G_cut j₁) (G_cut j₂) :=
    fun j₁ j₂ hne => (hG_disj hne).preimage Subtype.val
  have hL_cut : ∀ i, ∃ u v : S_cut, u ≠ v ∧ IsLineWithEnds (L_cut i) u v ∧
      L_cut i ∩ bd S_cut = {u, v} := fun i => by
    obtain ⟨u, v, huv, hl, hbd⟩ := hL i
    obtain ⟨hu, hv, huv', hl'⟩ := lift_line (hLsub i) huv hl
    refine ⟨⟨u, hu⟩, ⟨v, hv⟩, huv', hl', ?_⟩
    rw [hbd_cut]
    ext x
    simp only [L_cut, mem_inter_iff, mem_preimage, mem_insert_iff, mem_singleton_iff]
    constructor
    · intro h
      have huv' : x.1 ∈ ({u, v} : Set S) := hbd ▸ h
      rcases huv' with h' | h'
      · exact Or.inl (Subtype.ext h')
      · exact Or.inr (Subtype.ext h')
    · intro h
      have huv' : x.1 ∈ ({u, v} : Set S) := by
        rcases h with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      have hmem : x.1 ∈ L i ∩ (bd S ∪ ⋃ l, discBd (Δ l)) := hbd.symm ▸ huv'
      exact hmem
  have hL_cut_disj : Pairwise fun i₁ i₂ => Disjoint (L_cut i₁) (L_cut i₂) :=
    fun i₁ i₂ hne => (hLdisj hne).preimage Subtype.val
  have hbd_cut_disj : ∀ j i, Disjoint (G_cut j ∩ bd S_cut) (L_cut i ∩ bd S_cut) := fun j i => by
    rw [Set.disjoint_left]
    intro x ⟨hxG, hxbd⟩ ⟨hxL, _⟩
    rw [hbd_cut] at hxbd
    rcases hxbd with hxbdS | hxl
    · have hxGV : x.1 ∈ G.V := hGV_eq.symm ▸ mem_iUnion.mpr ⟨j, hxG, hxbdS⟩
      exact Set.disjoint_left.mp (hL_G i) ⟨hxL, hxbdS⟩ hxGV
    · obtain ⟨l, hxl⟩ := mem_iUnion.mp hxl
      exact Set.disjoint_left.mp (hΔG l) (discBd_subset _ hxl)
        (hGU_eq.symm ▸ mem_iUnion.mpr ⟨j, hxG⟩)
  -- Step 3: Apply LPPS22 Lemma A.3 in `S_cut ≃ₜ SurfaceModel a b (c + p)`.
  obtain ⟨φ_cut, hφ_fix, hφ_fin, hφ_sum⟩ :=
    lpps22_lemma_A_3 hsurf_cut e_cut (by omega : 1 ≤ c + p)
      hG_cut hG_cut_disj hL_cut hL_cut_disj hbd_cut_disj
  -- Step 4: Glue `φ_cut` on `S_cut` with `id` on `B := ⋃ l, Δ l`.
  let A : Set S := (⋃ l : Fin p, discInt (Δ l))ᶜ
  let B : Set S := ⋃ l : Fin p, Δ l
  have hBcl : IsClosed B := isClosed_iUnion_of_finite fun l => (hΔ l).isClosed
  have hAB : A ∪ B = univ := by
    ext x
    simp only [A, B, mem_union, mem_compl_iff, mem_iUnion, mem_univ, iff_true]
    by_cases h : ∃ l, x ∈ discInt (Δ l)
    · obtain ⟨l, hl⟩ := h
      exact Or.inr ⟨l, discInt_subset _ hl⟩
    · exact Or.inl h
  have hfix_AB : ∀ x : S_cut, x.1 ∈ B → (φ_cut x).1 = x.1 := fun x hxB => by
    obtain ⟨l, hxl⟩ := mem_iUnion.mp hxB
    have hxl_bd : x.1 ∈ discBd (Δ l) := by
      by_contra hnb
      exact x.2 (mem_iUnion.mpr ⟨l, hxl, hnb⟩)
    have hx_bd_cut : x ∈ bd S_cut := by
      rw [hbd_cut]; exact Or.inr (mem_iUnion.mpr ⟨l, hxl_bd⟩)
    exact congrArg Subtype.val (hφ_fix x hx_bd_cut)
  let φ : S ≃ₜ S := homeo_glue_id hcl_cut hBcl hAB φ_cut hfix_AB
  have hφ_bd : ∀ x ∈ bd S, φ x = x := fun x hxbd => by
    have hxA : x ∈ A := fun hmem => by
      obtain ⟨l, hl⟩ := mem_iUnion.mp hmem
      exact Set.disjoint_left.mp (hΔbd l) (discInt_subset _ hl) hxbd
    rw [homeo_glue_id_apply_mem_left hcl_cut hBcl hAB φ_cut hfix_AB hxA]
    have hx_bd_cut : (⟨x, hxA⟩ : S_cut) ∈ bd S_cut := by
      rw [hbd_cut]; exact Or.inl hxbd
    exact congrArg Subtype.val (hφ_fix ⟨x, hxA⟩ hx_bd_cut)
  have hφ_Δ : ∀ l, ∀ x ∈ Δ l, φ x = x := fun l x hxl =>
    homeo_glue_id_apply_mem_right hcl_cut hBcl hAB φ_cut hfix_AB (mem_iUnion.mpr ⟨l, hxl⟩)
  -- Step 5: Relate `φ '' L i ∩ G_arc j` to `φ_cut '' L_cut i ∩ G_cut j` and sum!
  have himg_eq : ∀ i j,
      φ '' L i ∩ G_arc j = Subtype.val '' (φ_cut '' L_cut i ∩ G_cut j) := fun i j => by
    ext z
    constructor
    · rintro ⟨⟨x, hxL, rfl⟩, hzG⟩
      have hxA : x ∈ A := hLsub i hxL
      have hφx : φ x = (φ_cut ⟨x, hxA⟩).1 :=
        homeo_glue_id_apply_mem_left hcl_cut hBcl hAB φ_cut hfix_AB hxA
      refine ⟨φ_cut ⟨x, hxA⟩, ⟨⟨⟨x, hxA⟩, hxL, rfl⟩, ?_⟩, hφx.symm⟩
      show (φ_cut ⟨x, hxA⟩).1 ∈ G_arc j
      rwa [← hφx]
    · rintro ⟨y, ⟨⟨x, hxL, rfl⟩, hyG⟩, rfl⟩
      have hφx : φ x.1 = (φ_cut x).1 :=
        homeo_glue_id_apply_mem_left hcl_cut hBcl hAB φ_cut hfix_AB x.2
      exact ⟨⟨x.1, hxL, hφx⟩, hyG⟩
  have hdecomp : G.U ∩ ⋃ i, φ '' L i = ⋃ i : Fin m, ⋃ j : Fin n', (φ '' L i ∩ G_arc j) := by
    rw [hGU_eq]
    ext z
    simp only [mem_inter_iff, mem_iUnion]
    exact ⟨fun ⟨⟨j, hj⟩, ⟨i, hi⟩⟩ => ⟨i, j, hi, hj⟩, fun ⟨i, j, hi, hj⟩ => ⟨⟨j, hj⟩, ⟨i, hi⟩⟩⟩
  have hpair_fin : ∀ i j, (φ '' L i ∩ G_arc j).Finite := fun i j => by
    rw [himg_eq i j]
    exact (hφ_fin i j).image Subtype.val
  have hfin_tot : (G.U ∩ ⋃ i, φ '' L i).Finite := by
    rw [hdecomp]
    exact Set.finite_iUnion fun i => Set.finite_iUnion fun j => hpair_fin i j
  have hcard_pair : ∀ i j, (φ '' L i ∩ G_arc j).ncard = (φ_cut '' L_cut i ∩ G_cut j).ncard :=
    fun i j => by
      rw [himg_eq i j, Set.ncard_image_of_injective _ Subtype.val_injective]
  have ncard_iUnion_fin_le : ∀ {r : ℕ} (F : Fin r → Set S),
      (⋃ i : Fin r, F i).ncard ≤ ∑ i : Fin r, (F i).ncard := by
    intro r
    induction r with
    | zero => intro _; simp
    | succ r ih =>
      intro F
      have hun : (⋃ i : Fin (r + 1), F i) = F 0 ∪ ⋃ i : Fin r, F i.succ := by
        ext z; simp only [mem_iUnion, mem_union]
        constructor
        · rintro ⟨i, hi⟩
          exact Fin.cases (motive := fun i => z ∈ F i → _) (fun h => Or.inl h)
            (fun j h => Or.inr ⟨j, h⟩) i hi
        · rintro (h | ⟨j, hj⟩)
          · exact ⟨0, h⟩
          · exact ⟨j.succ, hj⟩
      rw [hun, Fin.sum_univ_succ]
      exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left (ih (fun j => F j.succ)) _)
  have hcard_tot : (G.U ∩ ⋃ i, φ '' L i).ncard ≤
      ∑ i : Fin m, ∑ j : Fin n', (φ_cut '' L_cut i ∩ G_cut j).ncard := by
    rw [hdecomp]
    calc (⋃ i : Fin m, ⋃ j : Fin n', (φ '' L i ∩ G_arc j)).ncard
        ≤ ∑ i : Fin m, (⋃ j : Fin n', (φ '' L i ∩ G_arc j)).ncard :=
          ncard_iUnion_fin_le _
      _ ≤ ∑ i : Fin m, ∑ j : Fin n', (φ '' L i ∩ G_arc j).ncard :=
          Finset.sum_le_sum fun i _ => ncard_iUnion_fin_le _
      _ = ∑ i : Fin m, ∑ j : Fin n', (φ_cut '' L_cut i ∩ G_cut j).ncard :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hcard_pair i j
  have hbound : (G.U ∩ ⋃ i, φ '' L i).ncard ≤
      2 * k * 3 ^ (2 * n + 3 * (2 * a + b) + c + k) := by
    calc (G.U ∩ ⋃ i, φ '' L i).ncard
        ≤ ∑ i : Fin m, ∑ j : Fin n', (φ_cut '' L_cut i ∩ G_cut j).ncard := hcard_tot
      _ ≤ m * 3 ^ (2 * n' + 3 * (2 * a + b) + (c + p)) := hφ_sum
      _ ≤ (2 * k) * 3 ^ (2 * n + 3 * (2 * a + b) + c + k) := by
          refine Nat.mul_le_mul hm ?_
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  exact ⟨φ, hφ_bd, hφ_Δ, hfin_tot, hbound⟩

end GraphMinor.LPPS22
